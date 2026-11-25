-- Prove2me | solution 1 for GlobalTheory.PMonE.LangOnto.lang_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:49.936124+00:00
-- url     : https://prove2.me/submissions/6bd8af94-765c-428e-8b3e-fef5cf16afd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_exists_sol
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE
namespace GlobalTheory.PMonE.LangOnto
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F,
    (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  intro F _ _ _ p _ _ m _ _ e he A hA b hb
  obtain ⟨x, hx⟩ := exists_sol p he A b
  refine ⟨x, ?_, hx⟩
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  intro i₀
  by_contra hlt
  push Not at hlt
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun j => ‖x j‖) ⟨i₀, mem_univ _⟩
  have hR : 1 < ‖x i‖ := hlt.trans_le (hi i₀ (mem_univ _))
  have h1 : ‖A.mulVec x i‖ ≤ ‖x i‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun j _ => ?_)
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
      _ ≤ ‖x i‖ := by rw [one_mul]; exact hi j (mem_univ _)
  have h2 : x i ^ p ^ e = b i + A.mulVec x i := by rw [← hx i]; ring
  have h3 : ‖x i‖ ^ p ^ e ≤ ‖x i‖ := by
    rw [← norm_pow, h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb i).trans hR.le) h1)
  have h4 : ‖x i‖ ^ 1 < ‖x i‖ ^ p ^ e := pow_lt_pow_right₀ hR (by omega)
  rw [pow_one] at h4
  linarith
end GlobalTheory.PMonE.LangOnto
