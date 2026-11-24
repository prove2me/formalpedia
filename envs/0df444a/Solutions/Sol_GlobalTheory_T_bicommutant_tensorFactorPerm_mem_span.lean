-- Prove2me | solution 1 for GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:18.475274+00:00
-- url     : https://prove2.me/submissions/646c0563-e0bf-4528-912c-bfe6e8db9248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
import Theorems.Thm_GlobalTheory_SmoothForms_bicomm_permMat


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  first | exact @GlobalTheory.SmoothForms.bicomm_permMat | exact GlobalTheory.SmoothForms.bicomm_permMat | (intros; apply GlobalTheory.SmoothForms.bicomm_permMat <;> assumption)
end _root_.GlobalTheory.T
