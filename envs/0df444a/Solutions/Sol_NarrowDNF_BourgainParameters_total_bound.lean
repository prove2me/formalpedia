-- Prove2me | solution 1 for NarrowDNF.BourgainParameters.total_bound
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:18:55.044471+00:00
-- url     : https://prove2.me/submissions/53036879-e8ae-4610-a164-226a698c68c4

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainParameters
import Theorems.Thm_NarrowDNF_BourgainParameters_first_term_le

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters

section


/-! Explicit numerical choices for the reconstructed Bourgain small-component
estimate. The Fourier threshold eta retains the paper's constants. -/

noncomputable section
namespace NarrowDNF.BourgainParameters






private theorem cutoff_lower (k : ℕ) (e : ℝ) : realCutoff k e ≤ (cutoff k e : ℝ) :=
  Nat.le_ceil _





private theorem three_pow_ge_eight_sq {k : ℕ} (hk : 5 ≤ k) : 8*k^2 ≤ 3^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 3 k]
    nlinarith

private theorem tau_rpow (k : ℕ) {e : ℝ} (he0 : 0 ≤ e) :
    (tau k e) ^ (2/3 : ℝ) = e^2 / (3:ℝ)^(4*k) := by
  unfold tau
  rw [Real.div_rpow (pow_nonneg he0 _) (by positivity),
    ← Real.rpow_natCast_mul he0,
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 3)]
  have h2 : ((6*k : ℕ) : ℝ) * (2/3:ℝ) = ((4*k : ℕ) : ℝ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat]
  rw [h2, Real.rpow_natCast]
  norm_num



private theorem middle_term_le {k : ℕ} {e C : ℝ} (he0 : 0 ≤ e)
    (_hC0 : 0 ≤ C) (hC : C ≤ k) :
    2*C*(3:ℝ)^(2*k)*(tau k e)^(2/3:ℝ) ≤
      2*(k:ℝ)*e^2/(3:ℝ)^k := by
  calc
    _ = 2*C*e^2/(3:ℝ)^(2*k) := by
      rw [tau_rpow k he0, show 4*k = 2*k+2*k by omega, pow_add]
      field_simp
    _ ≤ 2*(k:ℝ)*e^2/(3:ℝ)^(2*k) := by gcongr
    _ ≤ 2*(k:ℝ)*e^2/(3:ℝ)^k :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))

private theorem sqrt_cutoff_lower (k : ℕ) {e : ℝ} (he0 : 0 < e) :
    (3:ℝ)^(9*k)/e^5 ≤ Real.sqrt (cutoff k e : ℝ) := by
  apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
  calc
    _ = realCutoff k e := by
      unfold realCutoff
      simp only [div_pow, ← pow_mul]
      congr 1
      congr 1
      ring
    _ ≤ _ := cutoff_lower k e

private theorem cutoff_denominator_lower (k : ℕ) {e : ℝ} (he0 : 0 < e) :
    (3:ℝ)^(3*k)/e^2 ≤ Real.sqrt (cutoff k e : ℝ) * tau k e := by
  have hid : ((3:ℝ)^(9*k)/e^5) * tau k e = (3:ℝ)^(3*k)/e^2 := by
    unfold tau
    rw [show 9*k = 6*k+3*k by omega, pow_add, pow_add e 3 2]
    field_simp
  rw [← hid]
  exact mul_le_mul_of_nonneg_right (sqrt_cutoff_lower k he0) (by
    unfold tau
    positivity)

private theorem third_term_le {k : ℕ} (hk : 1 ≤ k) {e C : ℝ}
    (he0 : 0 < e) (hC : C ≤ k) :
    (3:ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (cutoff k e : ℝ)*tau k e) ≤
      (k:ℝ)*e^2/(3:ℝ)^k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hroot : Real.sqrt C ≤ k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((k:ℝ)-1)]
  calc
    _ ≤ (3:ℝ)^(2*k)*Real.sqrt C / ((3:ℝ)^(3*k)/e^2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (cutoff_denominator_lower k he0)
    _ = Real.sqrt C * e^2/(3:ℝ)^k := by
      rw [show 3*k = 2*k+k by omega, pow_add]
      field_simp
    _ ≤ (k:ℝ)*e^2/(3:ℝ)^k := by gcongr



end NarrowDNF.BourgainParameters

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.BourgainParameters
/-- The explicit Bourgain error budget, with integer M and the unchanged
paper threshold eta. The stronger denominator permits later floor-cutoff use. -/
theorem solution {k : ℕ} (hk : 5 ≤ k) {e C : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ k) :
    (cutoff k e : ℝ)^k * (eta k e)^2 +
      2*C*(3:ℝ)^(2*k)*(tau k e)^(2/3:ℝ) +
      (3:ℝ)^(2*k)*Real.sqrt C/(Real.sqrt (cutoff k e : ℝ)*tau k e) ≤
        e^2/(2*(k:ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hexp : 8*(k:ℝ)^2 ≤ (3:ℝ)^k := by exact_mod_cast three_pow_ge_eight_sq hk
  have hpoly : 2*(k:ℝ)*(1+3*(k:ℝ)) ≤ (3:ℝ)^k := by
    nlinarith [sq_nonneg ((k:ℝ)-1)]
  calc
    _ ≤ e^2/(3:ℝ)^k + 2*(k:ℝ)*e^2/(3:ℝ)^k + (k:ℝ)*e^2/(3:ℝ)^k :=
      add_le_add (add_le_add (first_term_le hk1 he0 he1) (middle_term_le he0.le hC0 hC))
        (third_term_le hk1 he0 hC)
    _ = ((1+3*(k:ℝ))*e^2)/(3:ℝ)^k := by ring
    _ ≤ e^2/(2*(k:ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_right hpoly (sq_nonneg e)
      nlinarith
