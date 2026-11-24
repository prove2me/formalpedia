-- Prove2me | solution 1 for MomentComparison.finite_fourth_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:02.192748+00:00
-- url     : https://prove2.me/submissions/23d438e7-22be-4a13-a1ff-470da61c1f56

module
public import Definitions.Def_MomentComparison_Counting
public import Definitions.Def_MomentComparison_Walsh
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_FiniteFourth
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_walshLayer_fourth
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_pair_count_ge
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open MomentComparison
namespace MomentComparison
theorem _root_.solution (n m k : ℕ) (hkm : k ≤ m) :
    (n.choose (2 * k) : ℝ) * ((2 * k).choose k : ℝ) ^ 2 *
      ((n - 2 * k).choose (m - k) : ℝ) ^ 2 ≤
      cubeAverage (fun x => walshLayer n m x ^ 4) := by
  let supports := (univ : Finset (Fin n)).powersetCard (2 * k)
  let pairs := ((2 * k).choose k : ℝ) * ((n - 2 * k).choose (m - k) : ℝ)
  rw [cubeAverage_walshLayer_fourth]
  calc
    _ = ∑ _T ∈ supports, pairs ^ 2 := by
      simp only [sum_const, nsmul_eq_mul, supports, card_powersetCard, card_univ,
        Fintype.card_fin, pairs, mul_pow, mul_assoc]
    _ ≤ ∑ T ∈ supports, (walshPairCount n m T : ℝ) ^ 2 := by
      apply sum_le_sum
      intro T hT
      have hsize := (mem_powersetCard.mp hT).2
      have hcount := pair_count_ge m k hkm T hsize
      rw [Fintype.card_fin] at hcount
      apply pow_le_pow_left₀ (by dsimp [pairs]; positivity) _ 2
      change pairs ≤ (walshPairCount n m T : ℝ)
      dsimp [pairs, walshPairCount]
      exact_mod_cast hcount
    _ ≤ ∑ T : Finset (Fin n), (walshPairCount n m T : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ supports) (fun _ _ _ => sq_nonneg _)
end MomentComparison
