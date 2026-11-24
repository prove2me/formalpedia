-- Prove2me | solution 1 for GlobalTheory.congruenceSubgroups_GL_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:16.446292+00:00
-- url     : https://prove2.me/submissions/d40ca54d-ad91-4507-9ca8-3ea929be1146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CongruenceSubgroupsGLPadic
import Theorems.Thm_GlobalTheory_norm_mul_sub_one_le_of_norm_sub_one_le
import Theorems.Thm_GlobalTheory_T_ultrametric_matrix_inv_near_one


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n],
    ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔
      ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l _ n _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1 := by
    intro k
    refine ⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩
  refine ⟨fun k => {
    carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))}
    one_mem' := by
      intro i j
      simpa using (ht k).1
    mul_mem' := by
      intro X Y hX hY
      simp only [Set.mem_setOf_eq, Units.val_mul] at *
      exact norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY
    inv_mem' := by
      intro X hX
      simp only [Set.mem_setOf_eq] at *
      exact GlobalTheory.T.ultrametric_matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _
        (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩
end GlobalTheory
