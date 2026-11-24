-- Prove2me | solution 1 for GlobalTheory.SmoothForms.bicomm_permMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:18:22.859023+00:00
-- url     : https://prove2.me/submissions/dcd8844a-87aa-4049-8990-0ff0ff546bb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
import Theorems.Thm_GlobalTheory_SmoothForms_bicomm_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  intro n d M hM
  refine bicomm_mem_span (permMat n d) ?_ ?_ M hM
  · ext I K
    simp [permMat, Matrix.one_apply]
  · intro g h
    ext I K
    simp only [permMat, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (K ∘ h)]
    · rw [if_pos rfl, mul_one]
      rfl
    · intro J _ hJ
      simp [hJ]
    · simp
end GlobalTheory.SmoothForms
