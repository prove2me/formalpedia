-- Prove2me | solution 1 for InfoLossLAR.WorstCase.NativeDyadicSchedule.native_dyadic_program
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:28:20.607692+00:00
-- url     : https://prove2.me/submissions/ca54923b-42a6-4556-a7c2-fa71c067b3b0

import Definitions.Def_RegevDyadicSchedule

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeFiniteDraw
@[local fun_prop] theorem naturalBitsLocal_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩
@[local fun_prop] theorem rationalNumeratorLocal_poly : Poly (fun value : ℚ => value.num) := ⟨PolyProgram.ratNum⟩
@[local fun_prop] theorem rationalDenominatorLocal_poly : Poly (fun value : ℚ => value.den) := ⟨PolyProgram.ratDen⟩
@[local fun_prop] theorem signedAbsoluteLocal_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩
@[local fun_prop] theorem takeTicks_poly : Poly (fun x : List Unit × ℕ => x.1.take x.2) := ⟨PolyProgram.listTake Automatic.enc ()⟩

@[local fun_prop] theorem ratOfNat_poly : Poly (fun n : ℕ => (n : ℚ)) := ⟨PolyProgram.ratOfNat⟩

/-- A genuinely unary loop bound made from the *binary lengths* of the
positive initial numerator and requested-width denominator. -/
@[fun_prop] theorem ticks_poly : Poly ticks := by unfold ticks; fun_prop

theorem ticks_length (x : Input) :
    (ticks x).length = Nat.size x.1.1.num.natAbs + Nat.size x.1.2.den := by
  simp [ticks, Nat.size_eq_bits_len]

/-- Produce a dyadic rational using at most the computed bit-length ticks,
even on malformed or oversized input indices. -/
@[fun_prop] theorem widthDenominator_poly :
    Poly (fun x : Input × ℕ => (dyadicPower ((ticks x.1).take x.2) : ℚ)) := by
  have ht : Poly (fun x : Input × ℕ => (ticks x.1).take x.2) :=
    Poly.comp (f:=fun p : List Unit × ℕ => p.1.take p.2)
      (g:=fun x : Input × ℕ => (ticks x.1,x.2)) takeTicks_poly (by fun_prop)
  exact Poly.comp ratOfNat_poly (Poly.comp dyadicPower_poly ht)
@[fun_prop] theorem width_poly : Poly width := by unfold width; fun_prop

theorem width_eq (x : Input) (j : ℕ) (hj : j ≤ (ticks x).length) :
    width (x,j) = x.1.1 / (2 : ℚ)^j := by
  simp [width, dyadicPower, List.length_take, Nat.min_eq_left hj]

/-- Test the terminal crossing without computing an irrational square root. -/
@[fun_prop] theorem crossingTest_poly : Poly crossingTest := by
  unfold crossingTest
  simp only [pow_two]
  fun_prop

theorem crossingTest_correct (x : Input) (j : ℕ)
    (hn : 0 < x.2) (hW : 0 < x.1.1) (hr : 0 < x.1.2)
    (hj : j ≤ (ticks x).length) :
    crossingTest (x,j) = true ↔
      (width (x,j) : ℝ) ≤ (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2) := by
  have hnR : (0 : ℝ) < x.2 := by exact_mod_cast hn
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hnroot : 0 < Real.sqrt (x.2 : ℝ) := Real.sqrt_pos.mpr hnR
  have hu : (0 : ℝ) ≤ width (x,j) := by
    rw [width_eq x j hj]
    have h : 0 < x.1.1 / (2 : ℚ)^j := by positivity
    exact_mod_cast h.le
  have hrR : (0 : ℝ) < x.1.2 := by exact_mod_cast hr
  have hw : (0 : ℝ) ≤ (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2) := by positivity
  have hsq : ((x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2))^2 =
      (x.1.2 : ℝ)^2*((x.2 : ℝ)+2)^2/(2*(x.2 : ℝ)) := by
    simp only [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt hnR.le]
  have hcast : ((2 : ℚ)*(x.2 : ℚ)*width (x,j)^2 ≤
      x.1.2^2*((x.2 : ℚ)+2)^2) ↔
      (2 : ℝ)*(x.2 : ℝ)*(width (x,j) : ℝ)^2 ≤
        (x.1.2 : ℝ)^2*((x.2 : ℝ)+2)^2 := by exact_mod_cast Iff.rfl
  simp only [crossingTest, decide_eq_true_eq]
  change ((2 : ℚ)*(x.2 : ℚ)*width (x,j)^2 ≤ x.1.2^2*((x.2 : ℚ)+2)^2) ↔ _
  rw [hcast, ←sq_le_sq₀ hu hw, hsq, le_div_iff₀ (by positivity : (0 : ℝ) < 2*(x.2 : ℝ))]
  constructor <;> intro h <;> nlinarith


/-- A bit-length cap for a positive rational width ratio. The dependence is
on numerator and denominator bit lengths, not on their magnitudes. -/
private theorem rational_width_cap (start target : ℚ) (hstart : 0 < start) (htarget : 0 < target) :
    let K := Nat.size start.num.natAbs + Nat.size target.den
    (start : ℝ) ≤ (2 : ℝ)^K*(target : ℝ) := by
  have hstartNum : 0 < start.num := Rat.num_pos.mpr hstart
  have htargetNum : 0 < target.num := Rat.num_pos.mpr htarget
  have hstartDen : (0 : ℝ) < start.den := by exact_mod_cast start.den_pos
  have htargetDen : (0 : ℝ) < target.den := by exact_mod_cast target.den_pos
  have hstartNumR : (0 : ℝ) < start.num := by exact_mod_cast hstartNum
  have htargetNumR : (1 : ℝ) ≤ target.num := by exact_mod_cast htargetNum
  have hstartDenR : (1 : ℝ) ≤ start.den := by exact_mod_cast start.den_pos
  have hstartId : (start : ℝ) = (start.num : ℝ)/(start.den : ℝ) := by
    exact_mod_cast start.num_div_den.symm
  have htargetId : (target : ℝ) = (target.num : ℝ)/(target.den : ℝ) := by
    exact_mod_cast target.num_div_den.symm
  have hstartBound : (start : ℝ) ≤ (start.num.natAbs : ℝ) := by
    rw [hstartId]
    have hcast : (start.num.natAbs : ℝ) = (start.num : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, abs_of_nonneg hstartNumR.le]
    rw [hcast]
    exact (div_le_self hstartNumR.le hstartDenR)
  have htargetBound : 1 ≤ (target : ℝ)*(target.den : ℝ) := by
    rw [htargetId]
    field_simp
    exact htargetNumR
  have hsize1 : (start.num.natAbs : ℝ) ≤ (2 : ℝ)^Nat.size start.num.natAbs := by
    exact_mod_cast (Nat.lt_size_self start.num.natAbs).le
  have hsize2 : (target.den : ℝ) ≤ (2 : ℝ)^Nat.size target.den := by
    exact_mod_cast (Nat.lt_size_self target.den).le
  have ht : (0 : ℝ) < target := by exact_mod_cast htarget
  have hNatPos : (0 : ℝ) ≤ start.num.natAbs := by positivity
  dsimp only
  rw [pow_add]
  have hm := mul_le_mul hsize1 hsize2 (by positivity : 0 ≤ (target.den : ℝ))
    (by positivity : 0 ≤ (2 : ℝ)^Nat.size start.num.natAbs)
  nlinarith [mul_nonneg hNatPos (sub_nonneg.mpr htargetBound),
    mul_nonneg ht.le (sub_nonneg.mpr hm)]

/-- The fixed Gaussian width sigma=n+2 makes the terminal input scale at
least the positive requested output width. -/
private theorem fixed_terminal_ge_requested (n : ℕ) (target : ℝ)
    (hn : 0 < n) (htarget : 0 < target) :
    target ≤ target*((n : ℝ)+2)/(Real.sqrt 2*Real.sqrt n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs2Sq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsnSq : (Real.sqrt (n : ℝ))^2=n := Real.sq_sqrt (by positivity)
  have hsum : Real.sqrt 2*Real.sqrt n ≤ (n : ℝ)+2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,hs2Sq,hsnSq]
    nlinarith [sq_nonneg ((n : ℝ)+1)]
  apply (le_div_iff₀ (mul_pos hs2 hsn)).mpr
  exact mul_le_mul_of_nonneg_left hsum htarget.le


@[fun_prop] theorem crossingIndex_poly : Poly crossingIndex := by
  unfold crossingIndex
  apply Poly.list_findIdx crossingTest_poly
  have h := Poly.comp (f:=fun xs : List Unit => List.range xs.length)
    (g:=fun x : Input => ticks x ++ [()]) Poly.list_indices (by fun_prop)
  simpa only [List.length_append,List.length_singleton] using h

@[fun_prop] theorem selectedWidth_poly : Poly selectedWidth := by unfold selectedWidth; fun_prop

/-- The executable scan finds the actual first crossing within the bit-length
bound; no real square root is evaluated in the program. -/
theorem selectedWidth_spec (x : Input)
    (hn : 0 < x.2) (hW : 0 < x.1.1) (hr : 0 < x.1.2)
    (hinit : (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2) ≤ (x.1.1 : ℝ)) :
    let w := (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2)
    crossingIndex x ≤ (ticks x).length ∧
      w/2 ≤ (selectedWidth x : ℝ) ∧ (selectedWidth x : ℝ) ≤ w ∧
      ∀ j < crossingIndex x, w < (width (x,j) : ℝ) := by
  let w := (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2)
  let K := (ticks x).length
  have hrR : (0 : ℝ) < x.1.2 := by exact_mod_cast hr
  have hW_R : (0 : ℝ) < x.1.1 := by exact_mod_cast hW
  have hwrange : (x.1.2 : ℝ) ≤ w := by
    exact fixed_terminal_ge_requested x.2 (x.1.2 : ℝ) hn hrR
  have hcap₀ := rational_width_cap x.1.1 x.1.2 hW hr
  have hcap : (x.1.1 : ℝ) ≤ (2 : ℝ)^K*w := by
    have hK : K = Nat.size x.1.1.num.natAbs + Nat.size x.1.2.den := ticks_length x
    rw [hK]
    exact hcap₀.trans (mul_le_mul_of_nonneg_left hwrange (by positivity))
  have hlast : (width (x,K) : ℝ) ≤ w := by
    rw [width_eq x K (le_refl _)]
    push_cast
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^K)).mpr
    simpa [mul_comm] using hcap
  have hlastTest : crossingTest (x,K) = true :=
    (crossingTest_correct x K hn hW hr (le_refl _)).mpr hlast
  have hlt : crossingIndex x < K+1 := by
    have h := List.findIdx_lt_length_of_exists (xs:=List.range (K+1))
      (p:=fun j => crossingTest (x,j)) ⟨K, List.mem_range.mpr (by omega), hlastTest⟩
    simpa only [List.length_range, crossingIndex] using h
  have hle : crossingIndex x ≤ K := by omega
  have htest : crossingTest (x,crossingIndex x) = true := by
    have h := List.findIdx_getElem (xs:=List.range (K+1))
      (p:=fun j => crossingTest (x,j)) (w:=by simpa [crossingIndex] using hlt)
    simpa only [List.getElem_range, crossingIndex] using h
  have hupper : (selectedWidth x : ℝ) ≤ w := by
    exact (crossingTest_correct x (crossingIndex x) hn hW hr hle).mp htest
  have hprior : ∀ j < crossingIndex x, w < (width (x,j) : ℝ) := by
    intro j hj
    have hjK : j ≤ K := by omega
    have ht := List.not_of_lt_findIdx (xs:=List.range (K+1))
      (p:=fun i => crossingTest (x,i)) (by simpa only [crossingIndex] using hj)
    have hfalse : crossingTest (x,j) ≠ true := by
      have hfalse' : crossingTest (x,j) = false := by simpa only [List.getElem_range] using ht
      simp [hfalse']
    exact lt_of_not_ge (fun h => hfalse ((crossingTest_correct x j hn hW hr hjK).mpr h))
  have hlower : w/2 ≤ (selectedWidth x : ℝ) := by
    by_cases hz : crossingIndex x = 0
    · simp only [selectedWidth, hz, width_eq x 0 (by omega : 0 ≤ (ticks x).length), pow_zero, div_one]
      linarith
    · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hprior' := hprior j (by omega)
      have hjK : j ≤ K := by omega
      have hj1K : j+1 ≤ K := by omega
      rw [width_eq x j hjK] at hprior'
      simp only [selectedWidth,hj, width_eq x (j+1) hj1K]
      push_cast at hprior' ⊢
      rw [pow_succ]
      have heq : (x.1.1 : ℝ)/((2 : ℝ)^j*2) = ((x.1.1 : ℝ)/(2 : ℝ)^j)/2 := by ring
      rw [heq]
      linarith
  exact ⟨hle,hlower,hupper,hprior⟩

/-- The output of the executable crossing scan meets the source smoothing
and terminal BDD-radius constraints of the fixed-family width plan. -/
theorem selected_schedule_sound (x : Input) (q eta : ℝ)
    (hn : 0 < x.2) (hW : 0 < x.1.1) (hr : 0 < x.1.2)
    (hq : 0 < q) (heta : 0 < eta)
    (hthreshold : (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta ≤ (x.1.2 : ℝ))
    (hinit : (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2) ≤ (x.1.1 : ℝ)) :
    crossingIndex x ≤ (ticks x).length ∧
      (∀ j < crossingIndex x, Real.sqrt 2*q*eta < (width (x,j) : ℝ)) ∧
      Real.sqrt 2*q*eta < (selectedWidth x : ℝ) ∧
      Real.sqrt x.2/(Real.sqrt 2*(x.1.2 : ℝ)) ≤
        ((x.2 : ℝ)+2)/(2*(selectedWidth x : ℝ)) ∧
      1/(Real.sqrt 2*(1/(Real.sqrt 2*(x.1.2 : ℝ)))) = (x.1.2 : ℝ) := by
  let w := (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2)
  have hnR : (0 : ℝ) < x.2 := by exact_mod_cast hn
  have hsigma : (0 : ℝ) < (x.2 : ℝ)+2 := by positivity
  have hrR : (0 : ℝ) < x.1.2 := by exact_mod_cast hr
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hrootn : 0 < Real.sqrt (x.2 : ℝ) := Real.sqrt_pos.mpr hnR
  have htwoSq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hbound : 16*q*Real.sqrt x.2*eta ≤ (x.1.2 : ℝ)*((x.2 : ℝ)+2) := by
    apply (div_le_iff₀ hsigma).mp
    calc
      (16*q*Real.sqrt x.2*eta)/((x.2 : ℝ)+2) =
          (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta := by ring
      _ ≤ x.1.2 := hthreshold
  have hslack : 8*Real.sqrt 2*q*eta ≤ w := by
    dsimp [w]
    apply (le_div_iff₀ (mul_pos htwo hrootn)).mpr
    calc
      8*Real.sqrt 2*q*eta*(Real.sqrt 2*Real.sqrt x.2) =
          (8*(Real.sqrt (2 : ℝ))^2)*q*Real.sqrt x.2*eta := by ring
      _ = 16*q*Real.sqrt x.2*eta := by rw [htwoSq]; norm_num
      _ ≤ _ := hbound
  obtain ⟨hle,hlow,hup,hprior⟩ := selectedWidth_spec x hn hW hr hinit
  have hqe : 0 < Real.sqrt 2*q*eta := by positivity
  have hsmall : Real.sqrt 2*q*eta < w/2 := by nlinarith
  have hu : 0 < (selectedWidth x : ℝ) := hsmall.trans_le hlow |>.trans' (by positivity)
  refine ⟨hle,?_,hsmall.trans_le hlow,?_,?_⟩
  · intro j hj
    exact (by nlinarith : Real.sqrt 2*q*eta < w).trans (hprior j hj)
  · have hup' : (selectedWidth x : ℝ)*(Real.sqrt 2*Real.sqrt x.2) ≤
        (x.1.2 : ℝ)*((x.2 : ℝ)+2) := by
      apply (le_div_iff₀ (mul_pos htwo hrootn)).mp
      simpa [w] using hup
    apply (div_le_div_iff₀ (mul_pos htwo hrR) (by positivity : 0 < 2*(selectedWidth x : ℝ))).mpr
    calc
      Real.sqrt x.2*(2*(selectedWidth x : ℝ)) =
          Real.sqrt 2*((selectedWidth x : ℝ)*(Real.sqrt 2*Real.sqrt x.2)) := by
            calc
              _ = (2 : ℝ)*(selectedWidth x : ℝ)*Real.sqrt x.2 := by ring
              _ = (Real.sqrt (2 : ℝ))^2*(selectedWidth x : ℝ)*Real.sqrt x.2 := by rw [htwoSq]
              _ = _ := by ring
      _ ≤ Real.sqrt 2*((x.1.2 : ℝ)*((x.2 : ℝ)+2)) := mul_le_mul_of_nonneg_left hup' htwo.le
      _ = ((x.2 : ℝ)+2)*(Real.sqrt 2*(x.1.2 : ℝ)) := by ring
  · field_simp

noncomputable def selectedWidthProgram : PolyProgram Automatic.enc Automatic.enc selectedWidth :=
  selectedWidth_poly.program

theorem selectedWidth_TM2 : Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc selectedWidth) :=
  ⟨selectedWidthProgram.stock⟩

@[fun_prop] theorem result_poly : Poly result := by unfold result; fun_prop

noncomputable def resultProgram : PolyProgram Automatic.enc Automatic.enc result := result_poly.program

theorem result_TM2 : Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc result) :=
  ⟨resultProgram.stock⟩

end InfoLossLAR.WorstCase.NativeDyadicSchedule

open InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem solution :
    Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc result) ∧
      ∀ (x : Input) (q eta : ℝ),
        0 < x.2 → 0 < x.1.1 → 0 < x.1.2 → 0 < q → 0 < eta →
        (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta ≤ (x.1.2 : ℝ) →
        (x.1.2 : ℝ)*((x.2 : ℝ)+2)/(Real.sqrt 2*Real.sqrt x.2) ≤ (x.1.1 : ℝ) →
        crossingIndex x ≤ (ticks x).length ∧
          (∀ j < crossingIndex x, Real.sqrt 2*q*eta < (width (x,j) : ℝ)) ∧
          Real.sqrt 2*q*eta < (selectedWidth x : ℝ) ∧
          Real.sqrt x.2/(Real.sqrt 2*(x.1.2 : ℝ)) ≤
            ((x.2 : ℝ)+2)/(2*(selectedWidth x : ℝ)) ∧
          1/(Real.sqrt 2*(1/(Real.sqrt 2*(x.1.2 : ℝ)))) = (x.1.2 : ℝ) := by
  exact ⟨result_TM2, fun x q eta hn hW hr hq heta hthreshold hinit =>
    selected_schedule_sound x q eta hn hW hr hq heta hthreshold hinit⟩

#print axioms solution

