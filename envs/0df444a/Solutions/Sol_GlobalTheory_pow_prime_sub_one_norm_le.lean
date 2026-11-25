-- Prove2me | solution 1 for GlobalTheory.pow_prime_sub_one_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:45.175808+00:00
-- url     : https://prove2.me/submissions/ee6c646c-30a0-4bdb-8a93-0df61fc53c45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowPrimeSubOneNormLe
import Theorems.Thm_GlobalTheory_T_norm_one_add_pow_sub_one_sub_smul_le_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  intro l _ n _ _ X k hX i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with ht
  have t0 : 0 ≤ t := by positivity
  have tl : t ≤ (l : ℝ)⁻¹ := by
    rw [ht, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have t1 : t ≤ 1 := tl.trans (inv_le_one_of_one_le₀ hl1.le)
  have hrhs : (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = t * (l : ℝ)⁻¹ := by
    rw [ht, show -(((k + 1 : ℕ) : ℤ) + 2) = -((k : ℤ) + 2) + (-1) by push_cast; ring,
      zpow_add₀ hl0, zpow_neg_one]
  rw [hrhs]
  set Y := X - 1 with hY
  have hXY : X = 1 + Y := by rw [hY]; abel
  have hR := GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hX l i j
  have hsplit : (X ^ l - 1) i j = ((1 + Y) ^ l - 1 - ((l : ℕ) : ℚ_[l]) • Y) i j + (((l : ℕ) : ℚ_[l]) • Y) i j := by
    rw [hXY]; simp
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · calc _ ≤ t ^ 2 := hR
      _ = t * t := sq t
      _ ≤ t * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_left tl t0
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p, mul_comm]
    exact mul_le_mul_of_nonneg_right (hX i j) (by positivity)
end GlobalTheory
