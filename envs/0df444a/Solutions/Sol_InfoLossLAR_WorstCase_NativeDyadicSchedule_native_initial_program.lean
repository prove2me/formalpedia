-- Prove2me | solution 1 for InfoLossLAR.WorstCase.NativeDyadicSchedule.native_initial_program
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:37:48.204546+00:00
-- url     : https://prove2.me/submissions/6f4560d9-c30c-4084-9fad-c1ea59d45539

import Definitions.Def_RegevInitialSelection
import Theorems.Thm_InfoLossLAR_WorstCase_NativeDyadicSchedule_native_dyadic_program

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeGaussian
open Integration9_9.TM2NativeFiniteDraw

@[local fun_prop] private theorem initialNatBits_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩
@[local fun_prop] private theorem initialRatNumerator_poly : Poly (fun value : ℚ => value.num) := ⟨PolyProgram.ratNum⟩
@[local fun_prop] private theorem initialRatDenominator_poly : Poly (fun value : ℚ => value.den) := ⟨PolyProgram.ratDen⟩
@[local fun_prop] private theorem initialSignedAbs_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩
@[local fun_prop] theorem takeTicksLocal_poly : Poly (fun x : List Unit × ℕ => x.1.take x.2) :=
  ⟨PolyProgram.listTake Automatic.enc ()⟩
@[local fun_prop] theorem ratOfNatLocal_poly : Poly (fun n : ℕ => (n : ℚ)) := ⟨PolyProgram.ratOfNat⟩

@[local fun_prop] theorem ticksLocal_poly : Poly ticks := by unfold ticks; fun_prop

@[local fun_prop] theorem widthDenominatorLocal_poly :
    Poly (fun x : Input × ℕ => (dyadicPower ((ticks x.1).take x.2) : ℚ)) := by
  have ht : Poly (fun x : Input × ℕ => (ticks x.1).take x.2) :=
    Poly.comp (f:=fun p : List Unit × ℕ => p.1.take p.2)
      (g:=fun x : Input × ℕ => (ticks x.1,x.2)) takeTicksLocal_poly (by fun_prop)
  exact Poly.comp ratOfNatLocal_poly (Poly.comp dyadicPower_poly ht)

@[local fun_prop] theorem widthLocal_poly : Poly width := by unfold width; fun_prop

@[local fun_prop] theorem crossingTestLocal_poly : Poly crossingTest := by
  unfold crossingTest
  simp only [pow_two]
  fun_prop

@[local fun_prop] theorem crossingIndexLocal_poly : Poly crossingIndex := by
  unfold crossingIndex
  apply Poly.list_findIdx crossingTestLocal_poly
  have h := Poly.comp (f:=fun xs : List Unit => List.range xs.length)
    (g:=fun x : Input => ticks x ++ [()]) Poly.list_indices (by fun_prop)
  simpa only [List.length_append,List.length_singleton] using h

@[local fun_prop] theorem selectedWidthLocal_poly : Poly selectedWidth := by unfold selectedWidth; fun_prop

@[fun_prop] theorem initialRowMass_poly : Poly initialRowMass := by
  unfold initialRowMass
  fun_prop

@[fun_prop] theorem initialEntryMass_poly : Poly initialEntryMass := by
  unfold initialEntryMass
  fun_prop

@[fun_prop] theorem initialBase_poly : Poly (fun x : ℚ × ℕ => initialBase x.1 x.2) := by
  unfold initialBase
  fun_prop

@[fun_prop] theorem initialWidth_poly : Poly (fun x : List (List ℤ) × ℕ => initialWidth x.1 x.2) := by
  unfold initialWidth
  fun_prop

@[fun_prop] theorem initialRequest_poly : Poly initialRequest := by
  unfold initialRequest
  fun_prop

@[fun_prop] theorem initialSelection_poly : Poly initialSelection := by
  unfold initialSelection
  fun_prop

noncomputable def initialSelectionProgram : PolyProgram Automatic.enc Automatic.enc initialSelection :=
  initialSelection_poly.program

theorem initialSelection_TM2 : Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc initialSelection) :=
  ⟨initialSelectionProgram.stock⟩

theorem initialBase_lower (r : ℚ) (n : ℕ) :
    2 ≤ initialBase r n ∧ n ≤ initialBase r n ∧
      r*((n+2 : ℕ) : ℚ) ≤ (initialBase r n : ℚ) := by
  refine ⟨?_,?_,?_⟩
  · unfold initialBase; omega
  · unfold initialBase; omega
  · calc
      _ ≤ (⌈r*((n+2 : ℕ) : ℚ)⌉₊ : ℚ) := Nat.le_ceil _
      _ ≤ (initialBase r n : ℚ) := by exact_mod_cast (Nat.le_add_left _ _)

theorem initialEntryMass_nonneg (rows : List (List ℤ)) : 0 ≤ initialEntryMass rows := by
  unfold initialEntryMass initialRowMass
  apply List.sum_nonneg
  intro row hrow
  obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hrow
  apply List.sum_nonneg
  intro value hvalue
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hvalue
  positivity

theorem initialWidth_lower (rows : List (List ℤ)) (base : ℕ) :
    (base : ℚ) ≤ initialWidth rows base := by
  unfold initialWidth
  have hmass := initialEntryMass_nonneg rows
  have hb : (0 : ℚ) ≤ base := by positivity
  nlinarith

theorem initialWidth_pos (rows : List (List ℤ)) (base : ℕ) (hb : 0 < base) :
    0 < initialWidth rows base := by
  unfold initialWidth
  have hmass := initialEntryMass_nonneg rows
  have hbQ : (0 : ℚ) < base := by exact_mod_cast hb
  positivity

/-- The native request always supplies a broad rational source width. -/
theorem initialRequest_sound (x : InitialInput)
    (hn : 0 < x.2) (hr : 0 < x.1.2) :
    2 ≤ initialBase x.1.2 x.2 ∧ x.2 ≤ initialBase x.1.2 x.2 ∧
      (x.1.2 : ℝ)*((x.2 : ℝ)+2) ≤ initialBase x.1.2 x.2 ∧
      0 < (initialRequest x).1.1 ∧
      ((initialRequest x).1.2 : ℝ)*(((initialRequest x).2 : ℝ)+2)/
        (Real.sqrt 2*Real.sqrt (initialRequest x).2) ≤ ((initialRequest x).1.1 : ℝ) := by
  obtain ⟨h2,hdim,hwidth⟩ := initialBase_lower x.1.2 x.2
  have hbpos : 0 < initialBase x.1.2 x.2 := by omega
  have hWpos := initialWidth_pos x.1.1 (initialBase x.1.2 x.2) hbpos
  have hWbase := initialWidth_lower x.1.1 (initialBase x.1.2 x.2)
  have hWbaseR : (initialBase x.1.2 x.2 : ℝ) ≤ initialWidth x.1.1 (initialBase x.1.2 x.2) := by exact_mod_cast hWbase
  have hlarge : (x.1.2 : ℝ)*((x.2 : ℝ)+2) ≤ initialBase x.1.2 x.2 := by exact_mod_cast hwidth
  have hnroot : (1 : ℝ) ≤ Real.sqrt x.2 := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have h2root : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
  have hden : (1 : ℝ) ≤ Real.sqrt 2*Real.sqrt x.2 := one_le_mul_of_one_le_of_one_le h2root hnroot
  have hnum : (0 : ℝ) ≤ (x.1.2 : ℝ)*((x.2 : ℝ)+2) := by positivity
  refine ⟨h2,hdim,hlarge,?_,?_⟩
  · simpa [initialRequest] using hWpos
  · simpa [initialRequest] using (div_le_self hnum hden).trans (hlarge.trans hWbaseR)

/-- Combining the actual binary base constructor with the previously
verified dyadic scan discharges the broad-initial-width hypothesis. -/
theorem initialSelection_sound (x : InitialInput) (q eta : ℝ)
    (hn : 0 < x.2) (hr : 0 < x.1.2) (hq : 0 < q) (heta : 0 < eta)
    (hthreshold : (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta ≤ (x.1.2 : ℝ)) :
    2 ≤ initialBase x.1.2 x.2 ∧ x.2 ≤ initialBase x.1.2 x.2 ∧
      (x.1.2 : ℝ)*((x.2 : ℝ)+2) ≤ initialBase x.1.2 x.2 ∧
      0 < (initialRequest x).1.1 ∧
      crossingIndex (initialRequest x) ≤
        Nat.size ((initialRequest x).1.1).num.natAbs + Nat.size x.1.2.den ∧
      (∀ j < crossingIndex (initialRequest x),
        Real.sqrt 2*q*eta < (width (initialRequest x,j) : ℝ)) ∧
      Real.sqrt 2*q*eta < (selectedWidth (initialRequest x) : ℝ) ∧
      Real.sqrt x.2/(Real.sqrt 2*(x.1.2 : ℝ)) ≤
        ((x.2 : ℝ)+2)/(2*(selectedWidth (initialRequest x) : ℝ)) := by
  obtain ⟨hbase, hdim, hlarge, hW, hinit⟩ := initialRequest_sound x hn hr
  have hs := native_dyadic_program.2 (initialRequest x) q eta
    (by simpa [initialRequest] using hn) hW (by simpa [initialRequest] using hr) hq heta
    (by simpa [initialRequest] using hthreshold) hinit
  obtain ⟨hbound, hprior, hterminal, hbdd, hout⟩ := hs
  have hticks : (ticks (initialRequest x)).length =
      Nat.size ((initialRequest x).1.1).num.natAbs + Nat.size x.1.2.den := by
    simp [ticks,initialRequest,Nat.size_eq_bits_len]
  refine ⟨hbase, hdim, hlarge, hW, ?_, hprior, hterminal, ?_⟩
  · simpa only [hticks] using hbound
  · simpa only [initialRequest] using hbdd

end InfoLossLAR.WorstCase.NativeDyadicSchedule


open InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem solution :
    Nonempty (Turing.TM2ComputableInPolyTime Automatic.enc Automatic.enc initialSelection) ∧
      ∀ (x : InitialInput) (q eta : ℝ),
        0 < x.2 → 0 < x.1.2 → 0 < q → 0 < eta →
        (16*q*Real.sqrt x.2/((x.2 : ℝ)+2))*eta ≤ (x.1.2 : ℝ) →
        2 ≤ initialBase x.1.2 x.2 ∧ x.2 ≤ initialBase x.1.2 x.2 ∧
          (x.1.2 : ℝ)*((x.2 : ℝ)+2) ≤ initialBase x.1.2 x.2 ∧
          0 < (initialRequest x).1.1 ∧
          crossingIndex (initialRequest x) ≤
            Nat.size ((initialRequest x).1.1).num.natAbs + Nat.size x.1.2.den ∧
          (∀ j < crossingIndex (initialRequest x),
            Real.sqrt 2*q*eta < (width (initialRequest x,j) : ℝ)) ∧
          Real.sqrt 2*q*eta < (selectedWidth (initialRequest x) : ℝ) ∧
          Real.sqrt x.2/(Real.sqrt 2*(x.1.2 : ℝ)) ≤
            ((x.2 : ℝ)+2)/(2*(selectedWidth (initialRequest x) : ℝ)) := by
  exact ⟨initialSelection_TM2, fun x q eta hn hr hq heta hthreshold =>
    initialSelection_sound x q eta hn hr hq heta hthreshold⟩

#print axioms solution
