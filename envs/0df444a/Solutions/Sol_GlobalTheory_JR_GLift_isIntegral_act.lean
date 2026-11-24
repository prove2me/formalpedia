-- Prove2me | solution 1 for GlobalTheory.JR.GLift.isIntegral_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:56.841611+00:00
-- url     : https://prove2.me/submissions/2fe11ba3-6cad-4ec1-b14e-1dcdf9a33ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockGlBorderedConjugationActionI
import Theorems.Thm_GlobalTheory_JR_GLift_norm_mulVec_apply_le_one
import Theorems.Thm_GlobalTheory_JR_GLift_norm_vecMul_apply_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ glO n F) {Y : Gl n F} (hY : IsIntegral Y) : IsIntegral (act k Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hY
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, h4⟩
  · exact norm_mul_apply_le_one _ _
      (fun i j => norm_mul_apply_le_one _ _ (fun i j => (hk i j).1) h1 i j) (fun i j => (hk i j).2) i j
  · exact norm_mulVec_apply_le_one _ _ (fun i j => (hk i j).1) h2 i
  · exact norm_vecMul_apply_le_one _ _ h3 (fun i j => (hk i j).2) i
end GlobalTheory.JR.GLift
