-- Prove2me | solution 1 for OAI.LaughlinFock.thm_fock
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:19:24.05641+00:00
-- url     : https://prove2.me/submissions/aa05c776-99c0-42dc-95c0-02a7fa012aea

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L015
import Definitions.Def_OAIQ084L017
import Definitions.Def_OAIQ084L023
import Theorems.Thm_OAI_LaughlinFock_certificate_four
import Theorems.Thm_OAI_LaughlinFock_fockInequality_eventual_of_certificates

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Model
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model. -/
noncomputable section

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder


theorem hamiltonian_posSemidef (Q : ℕ) : (hamiltonian Q).PosSemidef := by
  unfold hamiltonian
  exact Matrix.posSemidef_sum _ (fun p _ => Matrix.posSemidef_conjTranspose_mul_self _)



theorem final_margin_arithmetic :
    (1 : ℝ) - 93527408868499 / 10 ^ 14 - 61 / 4096 -
      1222 * (3 / 10 ^ 6) = gammaStar := by
  norm_num [gammaStar]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SpinTails
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Tails. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology


theorem fallingRatio_nonneg (Q z : ℕ) : 0 ≤ fallingRatio Q z := by
  unfold fallingRatio
  positivity

theorem fallingRatio_succ {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q (z + 1) =
      ((Q : ℝ) - z) / (2 * Q - 2 - z) * fallingRatio Q z := by
  unfold fallingRatio
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm,
    Nat.cast_sub hz, Nat.cast_sub (show z ≤ 2*Q-2 by omega),
    Nat.cast_sub (show 2 ≤ 2*Q by omega)]
  push_cast
  rfl

 
theorem fallingRatio_le_geometric {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q z ≤ (2 / 3 : ℝ)^z := by
  induction z with
  | zero => simp [fallingRatio]
  | succ z ih =>
    rw [fallingRatio_succ (by omega) (by omega), pow_succ']
    have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hzR : (z : ℝ) + 1 ≤ Q := by exact_mod_cast hz
    have hd : 0 < 2 * (Q : ℝ) - 2 - z := by linarith
    have hf : ((Q : ℝ)-z) / (2*Q-2-z) ≤ 2/3 := by
      rw [div_le_iff₀ hd]
      have : (0 : ℝ) ≤ z := Nat.cast_nonneg z
      linarith
    exact mul_le_mul hf (ih (by omega)) (fallingRatio_nonneg Q z) (by norm_num)

private theorem affineRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => ((Q : ℝ)-z)/(2*Q-2-z)) atTop (𝓝 (1/2)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (z : ℝ)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 + (z : ℝ))
  have hh : Tendsto (fun Q : ℕ => (1 - (z : ℝ)/Q)/(2 - (2+z)/Q))
      atTop (𝓝 (1/2)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2)
      (show (2:ℝ)-0 ≠ 0 by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (z+2)] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hzr : (z : ℝ) + 2 ≤ Q := by exact_mod_cast hQ
  have hd : 2 * (Q:ℝ) - 2 - z ≠ 0 := by have := Nat.cast_nonneg (α:=ℝ) z; linarith
  have hd' : 2 - (2 + (z:ℝ)) / Q ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hn]
    linarith
  field_simp [hn, hd, hd']
  ring

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1/2 : ℝ)^z)) := by
  induction z with
  | zero => simp [fallingRatio]
  | succ z ih =>
    have h := (affineRatio_tendsto z).mul ih
    simp only [← pow_succ'] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (z+2)] with Q hQ
    exact (fallingRatio_succ (by omega) (by omega)).symm

 
theorem gramShift_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => gramShift Q z) atTop
      (𝓝 ((3 * (z : ℝ) - 1) * (-1/2)^z)) := by
  have h := ((fallingRatio_tendsto z).const_mul ((-1:ℝ)^z)).mul
    ((tendsto_const_nhds (x := (3*(z:ℝ)-1))).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((z:ℝ)*(z+1))))
  convert h using 1
  · simp [gramShift]
  · simp only [sub_zero]
    rw [mul_assoc, mul_comm ((3*(z:ℝ)-1)), ← mul_assoc, ← mul_pow]
    congr 1
    norm_num


theorem spinRatio_bounds {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    0 ≤ spinRatio Q z ∧ spinRatio Q z ≤ 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hzR : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hd : 0 < 2 * (Q : ℝ) - 1 := by linarith
  constructor
  · exact div_nonneg (by linarith) hd.le
  · rw [spinRatio, div_le_iff₀ hd]
    linarith

private theorem gramBracket_bounds {Q z : ℕ} (hQ : 1 ≤ Q)
    (hz1 : 1 ≤ z) (hzQ : z ≤ Q) :
    0 ≤ 3 * (z : ℝ) - 1 - z * (z + 1) / Q ∧
      3 * (z : ℝ) - 1 - z * (z + 1) / Q ≤ 3 * z := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have hzQR : (z : ℝ) ≤ Q := by exact_mod_cast hzQ
  have hd : (z : ℝ) * (z + 1) / Q ≤ z + 1 := by
    rw [div_le_iff₀ hQR]
    nlinarith
  have hn : (0 : ℝ) ≤ (z : ℝ) * (z + 1) / Q := by positivity
  constructor <;> linarith

 
theorem gramShift_abs_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz1 : 1 ≤ z) (hzQ : z ≤ Q) :
    |gramShift Q z| ≤ 3 * (z : ℝ) * (2/3)^z := by
  obtain ⟨hb0, hb⟩ := gramBracket_bounds (by omega : 1 ≤ Q) hz1 hzQ
  rw [gramShift, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (fallingRatio_nonneg Q z), abs_of_nonneg hb0]
  calc
    _ ≤ (2/3 : ℝ)^z * (3*z) :=
      mul_le_mul (fallingRatio_le_geometric hQ hzQ) hb hb0 (by positivity)
    _ = _ := mul_comm _ _

theorem spinRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => spinRatio Q z) atTop (𝓝 (3/2)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1+2*(z:ℝ))
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have hh : Tendsto (fun Q : ℕ => (3 - (1+2*(z:ℝ))/Q)/(2 - 1/(Q:ℝ)))
      atTop (𝓝 (3/2)) := by
    convert ((tendsto_const_nhds (x := (3:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2) (show (2:ℝ)-0 ≠ 0 by norm_num)
      using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hqr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : 2*(Q:ℝ)-1 ≠ 0 := by linarith
  have hd' : 2 - 1/(Q:ℝ) ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hn]
    linarith
  unfold spinRatio
  field_simp [hn, hd, hd']
  ring



theorem tailTerm_bound {Q : ℕ} (hQ : 4 ≤ Q) (m : ℕ) :
    ‖tailTerm Q m‖ ≤
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m) := by
  dsimp [tailTerm]
  split_ifs with hm
  · rw [abs_of_nonneg (by
      exact mul_nonneg (mul_nonneg (spinRatio_bounds (by omega) hm).1 (abs_nonneg _))
        (by positivity))]
    calc
      _ ≤ 2 * (3 * ((17+2*m : ℕ):ℝ) * (2/3)^(17+2*m)) * ((17+2*m : ℕ)+1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (spinRatio_bounds (by omega) hm).2
            (gramShift_abs_le hQ (by omega) hm) (abs_nonneg _) (by norm_num)) (by positivity)
      _ = _ := by ring
  · simp only [abs_zero]
    positivity

private theorem tailBound_summable :
    Summable (fun m : ℕ =>
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m)) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(2/3 : ℝ)‖ < 1 by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (show ‖(2/3 : ℝ)‖ < 1 by norm_num)
  have h : Summable (fun z : ℕ => 6*(z:ℝ)*(z+1)*(2/3)^z) := by
    apply ((h2.mul_left 6).add (h1.mul_left 6)).congr
    intro z
    ring
  exact h.comp_injective (fun i j hij => by omega)

 
theorem tailTerm_tendsto (m : ℕ) :
    Tendsto (fun Q : ℕ => tailTerm Q m) atTop
      (𝓝 ((3/2 : ℝ)*(3*((17+2*m : ℕ):ℝ)-1)*
        (1/2 : ℝ)^(17+2*m)*((17+2*m : ℕ)+1))) := by
  let z := 17+2*m
  have hb : 0 ≤ 3*(z:ℝ)-1 := by dsimp [z]; push_cast; have := Nat.cast_nonneg (α:=ℝ) m; linarith
  have h := ((spinRatio_tendsto z).mul (gramShift_tendsto z).abs).mul_const ((z:ℝ)+1)
  have ha : |(-1/2 : ℝ)| = 1/2 := by norm_num
  rw [abs_mul, abs_pow, abs_of_nonneg hb, ha] at h
  have hh : (3/2 : ℝ)*((3*(z:ℝ)-1)*(1/2)^z)*((z:ℝ)+1) =
      (3/2 : ℝ)*(3*(z:ℝ)-1)*(1/2)^z*((z:ℝ)+1) := by ring
  rw [hh] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop z] with Q hQ
  simp [tailTerm, z, hQ]

 
theorem limit_tail_hasSum :
    HasSum (fun m : ℕ => (3/2 : ℝ)*(3*((17+2*m : ℕ):ℝ)-1)*
      (1/2 : ℝ)^(17+2*m)*((17+2*m : ℕ)+1)) (61/4096) := by
  have hr : ‖(1/4 : ℝ)‖ < 1 := by norm_num
  have h0 : HasSum (fun m : ℕ => (1/4 : ℝ)^m) (4/3) := by
    convert hasSum_geometric_of_lt_one (r := (1/4 : ℝ)) (by norm_num) (by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have h1 : HasSum (fun m : ℕ => (m:ℝ)*(1/4 : ℝ)^m) (4/9) := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one hr using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | norm_num
  have h2 : HasSum (fun m : ℕ => ((m+2).choose 2 : ℝ)*(1/4 : ℝ)^m) (64/27) := by
    convert hasSum_choose_mul_geometric_of_norm_lt_one 2 hr using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | norm_num
  have h := (((h2.mul_left 24).add (h1.mul_left 172)).add (h0.mul_left 876)).mul_left
    ((3/2 : ℝ)*(1/2)^17)
  norm_num only [show (3/2 : ℝ)*(1/2)^17 * (24*(64/27)+172*(4/9)+876*(4/3)) =
    61/4096 by norm_num] at h
  apply h.congr_fun
  intro m
  rw [Nat.cast_choose_two]
  push_cast
  rw [pow_add, pow_mul]
  norm_num
  ring

 
theorem tailCoefficient_eq_tsum (Q : ℕ) : tailCoefficient Q = ∑' m, tailTerm Q m := by
  symm
  apply tsum_eq_sum
  intro m hm
  have hm' : Q+1 ≤ m := by simpa only [Finset.mem_range, not_lt] using hm
  have h : ¬ 17+2*m ≤ Q := by omega
  simp [tailTerm, h]

 

theorem tailCoefficient_tendsto :
    Tendsto tailCoefficient atTop (𝓝 (61/4096 : ℝ)) := by
  have h := tendsto_tsum_of_dominated_convergence tailBound_summable tailTerm_tendsto
    (show ∀ᶠ Q in atTop, ∀ m, ‖tailTerm Q m‖ ≤
      6 * ((17+2*m : ℕ) : ℝ) * ((17+2*m : ℕ)+1) * (2/3 : ℝ)^(17+2*m) from
      (eventually_ge_atTop 4).mono (fun _ hQ m => tailTerm_bound hQ m))
  rw [limit_tail_hasSum.tsum_eq] at h
  exact h.congr' (Filter.Eventually.of_forall (fun Q => (tailCoefficient_eq_tsum Q).symm))


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Polynomial


theorem couplingPolynomial_rescale (c u v : ℝ) (_hu : u ≠ 0) (hv : v ≠ 0)
    (hc : c*u^2 = v^2) (z k : ℕ) :
    couplingPolynomial u v z k =
      C (v^z*u^k) * (((X-1)^z*(C c*X+1)^k).comp (C (u/v)*X)) := by
  have h1 : (C v : Polynomial ℝ) * (C (u/v)*X-1) = C u*X-C v := by
    simp only [mul_sub, mul_one, ← mul_assoc, ← C_mul]
    congr 2
    field_simp
  have h2 : (C u : Polynomial ℝ) * (C c*(C (u/v)*X)+1) = C v*X+C u := by
    simp only [mul_add, mul_one, ← mul_assoc, ← C_mul]
    congr 2
    congr 1
    field_simp
    nlinarith only [hc]
  simp only [couplingPolynomial, mul_comp, pow_comp, sub_comp, add_comp, X_comp,
    one_comp, C_comp]
  rw [show C (v^z*u^k) = (C v)^z*(C u)^k by simp, mul_mul_mul_comm,
    ← mul_pow, ← mul_pow, h1, h2]

theorem polynomialCouplingCoefficient_rescale (c u v : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hc : c*u^2=v^2) (z k p : ℕ) :
    polynomialCouplingCoefficient u v z k p =
      (((X-1)^z*(C c*X+1)^k : Polynomial ℝ).coeff p) *
      (monomialWeight (z+k) p / Real.sqrt ((z.factorial : ℝ)*k.factorial) *
        (v^z*u^k*(u/v)^p)) := by
  simp only [polynomialCouplingCoefficient, monomialCoefficient,
    couplingPolynomial_rescale c u v hu hv hc, coeff_C_mul, comp_C_mul_X_coeff]
  ring

theorem rationalCoupling_real (c : ℚ) (z k p : ℕ) :
    (((X-1)^z * (C (c : ℝ)*X+1)^k) : Polynomial ℝ).coeff p =
      (rationalCoupling c z k p : ℝ) := by
  have h : (((X-1)^z * (C c*X+1)^k) : Polynomial ℚ).map (algebraMap ℚ ℝ) =
      ((X-1)^z*(C (c:ℝ)*X+1)^k) := by simp
  rw [← h, Polynomial.coeff_map]
  rfl

 

theorem polynomialCouplingCoefficient_rational (c : ℚ) (hc : 0 < c)
    (z k p : ℕ) :
    polynomialCouplingCoefficient (Real.sqrt (1/(1+(c:ℝ))))
      (Real.sqrt ((c:ℝ)/(1+(c:ℝ)))) z k p =
      (rationalCoupling c z k p : ℝ) * Real.sqrt (rationalCouplingWeight c z k p : ℝ) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hC : (0:ℝ) < 1+(c:ℝ) := by linarith
  let u := Real.sqrt (1/(1+(c:ℝ)))
  let v := Real.sqrt ((c:ℝ)/(1+(c:ℝ)))
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos zero_lt_one hC)
  have hv : 0 < v := Real.sqrt_pos.mpr (div_pos hcR hC)
  have hu2 : u^2 = 1/(1+(c:ℝ)) := Real.sq_sqrt (by positivity)
  have hv2 : v^2 = (c:ℝ)/(1+(c:ℝ)) := Real.sq_sqrt (by positivity)
  have huv2 : (u/v)^2 = 1/(c:ℝ) := by
    rw [div_pow, hu2, hv2]
    field_simp
  rw [polynomialCouplingCoefficient_rescale (c:ℝ) u v hu.ne' hv.ne'
    (by rw [hu2, hv2]; ring), rationalCoupling_real]
  congr 1
  let f : ℝ := monomialWeight (z+k) p / Real.sqrt ((z.factorial : ℝ)*k.factorial) *
      (v^z*u^k*(u/v)^p)
  have hf : 0 ≤ f := by dsimp [f, monomialWeight]; positivity
  have hs : f^2 = (rationalCouplingWeight c z k p : ℝ) := by
    dsimp [f, monomialWeight, rationalCouplingWeight]
    push_cast
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      mul_pow, mul_pow, ← pow_mul, mul_comm z 2, pow_mul, hv2,
      ← pow_mul, mul_comm k 2, pow_mul, hu2,
      ← pow_mul, mul_comm p 2, pow_mul, huv2]
    simp only [div_pow, one_pow, pow_add]
    field_simp
  rw [← hs, Real.sqrt_sq hf]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalThree
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Three. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


theorem rationalAlphaWeight_pos (t : ℕ) (b : RowEntry t) :
    0 < rationalAlphaWeight t b := by
  unfold rationalAlphaWeight
  positivity

theorem rationalCouplingWeight_pos {c : ℚ} (hc : 0 < c) (z k p : ℕ) :
    0 < rationalCouplingWeight c z k p := by
  unfold rationalCouplingWeight
  positivity



theorem planarThreeCoefficient_rational (z T p : ℕ) (hz : z ≤ T) :
    planarThreeCoefficient z T p = (rationalCoupling 2 z (T-z) p : ℝ) *
      Real.sqrt (rationalCouplingWeight 2 z (T-z) p : ℝ) := by
  rw [planarThreeCoefficient, ite_eq_left hz]
  simpa only [Rat.cast_ofNat, show (1:ℝ)+2=3 by norm_num] using
    polynomialCouplingCoefficient_rational 2 (by norm_num) z (T-z) p

theorem rationalAlphaWeight_cancellation {t T z : ℕ} (b : RowEntry t)
    (hz : z ≤ T) (hb : rowP b+rowJ b=T) :
    rationalAlphaWeight t b * rationalCouplingWeight 2 z (T-z) (rowP b) =
      rationalCouplingWeight 2 z (T-z) t := by
  have hi : T-t = rowI b := by simp [rowI, hb]
  have hj : T-rowP b = rowJ b := by omega
  unfold rationalAlphaWeight rationalCouplingWeight
  rw [Nat.add_sub_of_le hz, hi, hj]
  field_simp

theorem alpha_mul_planarThree {t T z : ℕ} (a : RowEntry t → ℚ)
    (b : RowEntry t) (hz : z ≤ T) (hb : rowP b+rowJ b=T) :
    ((a b : ℝ) * Real.sqrt (rationalAlphaWeight t b : ℝ)) *
      planarThreeCoefficient z T (rowP b) =
      ((a b * rationalCoupling 2 z (T-z) (rowP b) : ℚ) : ℝ) *
        Real.sqrt (rationalCouplingWeight 2 z (T-z) t : ℝ) := by
  rw [planarThreeCoefficient_rational z T (rowP b) hz, Rat.cast_mul]
  rw [mul_mul_mul_comm, ← Real.sqrt_mul (by exact_mod_cast (rationalAlphaWeight_pos t b).le)]
  have he : (rationalAlphaWeight t b : ℝ) * (rationalCouplingWeight 2 z (T-z) (rowP b) : ℝ) =
      (rationalCouplingWeight 2 z (T-z) t : ℝ) := by
    exact_mod_cast rationalAlphaWeight_cancellation b hz hb
  rw [he]


theorem planarRowThreeTrace_rational (z : ℕ) (t : Fin 8)
    (ell : ℚ) (a : RowEntry t.val → ℚ) :
    planarRowThreeTrace z t.val (rationalComparisonRow t ell a).ell
      (rationalComparisonRow t ell a).alpha = (rationalThreeTrace z t.val ell a : ℝ) := by
  classical
  unfold planarRowThreeTrace rationalThreeTrace
  push_cast
  apply Finset.sum_congr rfl
  intro T _
  split_ifs with ht
  · let X : ℚ := ∑ b : RowEntry t.val, if rowP b+rowJ b=T then
        a b*rationalCoupling 2 z (T-z) (rowP b) else 0
    have hX : (∑ b : RowEntry t.val, if rowP b+rowJ b=T then
        (rationalComparisonRow t ell a).alpha b*planarThreeCoefficient z T (rowP b) else 0) =
        (X : ℝ) * Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ) := by
      dsimp [X]
      rw [Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with hb
      · exact alpha_mul_planarThree a b ht.1 hb
      · simp
    rw [hX, planarThreeCoefficient_rational z T t.val ht.1]
    change 2*(ell:ℝ)*((rationalCoupling 2 z (T-z) t.val : ℝ)*
        Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))*
        ((X:ℝ)*Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))+
        ((X:ℝ)*Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))^2 = _
    have hn : 0 ≤ (rationalCouplingWeight 2 z (T-z) t.val : ℝ) := by
      exact_mod_cast (rationalCouplingWeight_pos (by norm_num : (0:ℚ)<2) z (T-z) t.val).le
    have hs := Real.sq_sqrt hn
    calc
      _ = (Real.sqrt (rationalCouplingWeight 2 z (T-z) t.val : ℝ))^2 *
        (X:ℝ)*((X:ℝ)+2*(ell:ℝ)*(rationalCoupling 2 z (T-z) t.val : ℝ)) := by ring
      _ = _ := by rw [hs]; simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]; rfl
  · simp

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CertificateRows
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate Rows. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem certificateEta : rowsEta certificateRows = 932999265582865863 / 10^18 := by
  norm_num [rowsEta, certificateRows, rationalComparisonRow,
    certificateEll, certificateEllData, Fin.sum_univ_succ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SquareSplitting
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Splitting. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem FockInequality.mono {Q : ℕ} {a b : ℝ} (h : FockInequality Q b)
    (hab : a ≤ b) : FockInequality Q a := by
  have h' := h.add ((hamiltonian_posSemidef Q).smul (sub_nonneg.mpr hab))
  unfold FockInequality at *
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sub_smul]
  abel



theorem uniform_integer_threshold_of_eventual_bound (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 gammaStar))
    (hbound : ∀ᶠ Q in atTop, FockInequality Q (a Q))
    (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  have he : ∀ᶠ Q in atTop, γ < a Q := ha.eventually (eventually_gt_nhds hγ)
  obtain ⟨q, hq⟩ := eventually_atTop.mp (hbound.and he)
  refine ⟨(max 1 q : ℕ), ?_, ?_⟩
  · exact_mod_cast (le_max_left 1 q)
  · intro Q hQ
    have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
    have hqn : max 1 q ≤ Q.toNat := by exact_mod_cast (show (max 1 q : ℤ) ≤ (Q.toNat : ℤ) by simpa [Int.toNat_of_nonneg hQ0] using hQ)
    exact (hq Q.toNat (le_trans (le_max_right 1 q) hqn)).1.mono
      (hq Q.toNat (le_trans (le_max_right 1 q) hqn)).2.le



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology

 

theorem integer_threshold_of_certificates_le {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hEta : rowsEta rows ≤ 93527408868499 / 10^14)
    (hThree : ∀ z : ComparedThreeBlock,
      planarRowsThreeTrace rows z.val.val <
        (3/2 : ℝ)*(3*(z.val.val : ℝ)-1)*(-1/2)^z.val.val)
    (hFour : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows (3/10^6) D * planarFourGram D).PosSemidef)
    (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  obtain ⟨e, _, helim, hb⟩ :=
    fockInequality_eventual_of_certificates rows (3/10^6) (by norm_num) hThree hFour
  have hl : Tendsto (fun Q => 1-(93527408868499 / 10^14 : ℝ)-
      tailCoefficient Q-1222*(3/10^6)-e Q) atTop (𝓝 gammaStar) := by
    have h := (((tendsto_const_nhds (x := 1-(93527408868499 / 10^14 : ℝ))).sub
      tailCoefficient_tendsto).sub_const (1222*(3/10^6))).sub helim
    simpa only [sub_zero, final_margin_arithmetic] using h
  apply uniform_integer_threshold_of_eventual_bound _ hl _ γ hγ
  filter_upwards [hb] with Q hQ
  exact hQ.mono (by linarith only [hEta])

theorem certificateEta_le : rowsEta certificateRows ≤ 93527408868499 / 10^14 := by
  rw [certificateEta]
  norm_num

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Polynomial


theorem rationalCoupling_integer (c : ℤ) (z k p : ℕ) :
    rationalCoupling (c:ℚ) z k p = (integerCoupling c z k p : ℚ) := by
  have h1 : ((X-1)^z : Polynomial ℚ).coeff = fun h =>
      (-1)^(z-h) * (z.choose h : ℚ) := by
    funext h
    rw [show (X-1:Polynomial ℚ) = X+C (-1) by simp [sub_eq_add_neg]]
    exact coeff_X_add_C_pow (-1) z h
  have h2 : ((C (c:ℚ)*X+1)^k : Polynomial ℚ).coeff = fun h =>
      (k.choose h : ℚ) * (c:ℚ)^h := by
    funext h
    rw [show ((C (c:ℚ)*X+1)^k : Polynomial ℚ) = ((X+1)^k).comp (C (c:ℚ)*X) by simp]
    rw [comp_C_mul_X_coeff, coeff_X_add_one_pow]
  unfold rationalCoupling integerCoupling
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [h1, h2, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro h _
  ring

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeCertificate
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Certificate. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

theorem rationalThreeTrace_integer (z t : ℕ) (ell : ℚ) (a : RowEntry t → ℚ) :
    rationalThreeTrace z t ell a = integerThreeTrace z t ell a := by
  simp only [rationalThreeTrace, integerThreeTrace, ← rationalCoupling_integer, Int.cast_ofNat]

theorem planarRowsThreeTrace_integer (z : ℕ) :
    planarRowsThreeTrace certificateRows z = (integerRowsThreeTrace z : ℝ) := by
  unfold planarRowsThreeTrace integerRowsThreeTrace
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (planarRowThreeTrace_rational z t (certificateEll t) (certificateAlpha t)).trans
    (congrArg (fun q:ℚ => (q:ℝ)) (rationalThreeTrace_integer z t.val _ _))

theorem certificate_three_2 : integerRowsThreeTrace 2 <
    (3/2 : ℚ)*(3*(2:ℚ)-1)*(-1/2)^(2:ℕ) := by
  decide +kernel

theorem certificate_three_4 : integerRowsThreeTrace 4 <
    (3/2 : ℚ)*(3*(4:ℚ)-1)*(-1/2)^(4:ℕ) := by
  decide +kernel

theorem certificate_three_5 : integerRowsThreeTrace 5 <
    (3/2 : ℚ)*(3*(5:ℚ)-1)*(-1/2)^(5:ℕ) := by
  decide +kernel

theorem certificate_three_6 : integerRowsThreeTrace 6 <
    (3/2 : ℚ)*(3*(6:ℚ)-1)*(-1/2)^(6:ℕ) := by
  decide +kernel

theorem certificate_three_7 : integerRowsThreeTrace 7 <
    (3/2 : ℚ)*(3*(7:ℚ)-1)*(-1/2)^(7:ℕ) := by
  decide +kernel

theorem certificate_three_8 : integerRowsThreeTrace 8 <
    (3/2 : ℚ)*(3*(8:ℚ)-1)*(-1/2)^(8:ℕ) := by
  decide +kernel

theorem certificate_three_9 : integerRowsThreeTrace 9 <
    (3/2 : ℚ)*(3*(9:ℚ)-1)*(-1/2)^(9:ℕ) := by
  decide +kernel

theorem certificate_three_10 : integerRowsThreeTrace 10 <
    (3/2 : ℚ)*(3*(10:ℚ)-1)*(-1/2)^(10:ℕ) := by
  decide +kernel

theorem certificate_three_11 : integerRowsThreeTrace 11 <
    (3/2 : ℚ)*(3*(11:ℚ)-1)*(-1/2)^(11:ℕ) := by
  decide +kernel

theorem certificate_three_12 : integerRowsThreeTrace 12 <
    (3/2 : ℚ)*(3*(12:ℚ)-1)*(-1/2)^(12:ℕ) := by
  decide +kernel

theorem certificate_three_13 : integerRowsThreeTrace 13 <
    (3/2 : ℚ)*(3*(13:ℚ)-1)*(-1/2)^(13:ℕ) := by
  decide +kernel

theorem certificate_three_14 : integerRowsThreeTrace 14 <
    (3/2 : ℚ)*(3*(14:ℚ)-1)*(-1/2)^(14:ℕ) := by
  decide +kernel

theorem certificate_three_15 : integerRowsThreeTrace 15 <
    (3/2 : ℚ)*(3*(15:ℚ)-1)*(-1/2)^(15:ℕ) := by
  decide +kernel

theorem certificate_three (z : ComparedThreeBlock) :
    planarRowsThreeTrace certificateRows z.val.val <
      (3/2 : ℝ)*(3*(z.val.val:ℝ)-1)*(-1/2)^z.val.val := by
  rw [planarRowsThreeTrace_integer]
  have h (n : ℕ) (hn : n=2 ∨ 4≤n) (hn' : n<16) : integerRowsThreeTrace n <
      (3/2 : ℚ)*(3*(n:ℚ)-1)*(-1/2)^n := by
    interval_cases n
    · omega
    · omega
    · exact certificate_three_2
    · omega
    · exact certificate_three_4
    · exact certificate_three_5
    · exact certificate_three_6
    · exact certificate_three_7
    · exact certificate_three_8
    · exact certificate_three_9
    · exact certificate_three_10
    · exact certificate_three_11
    · exact certificate_three_12
    · exact certificate_three_13
    · exact certificate_three_14
    · exact certificate_three_15
  have hl := (Rat.cast_lt (K:=ℝ)).mpr (h z.val.val z.property z.val.isLt)
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_sub, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using hl

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem thm_fock_oai (γ : ℝ) (_hγ : 0 < γ) (hγStar : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  exact integer_threshold_of_certificates_le certificateRows certificateEta_le
    certificate_three certificate_four γ hγStar

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.thm_fock_oai := @OAI.LaughlinFock.thm_fock_oai
