-- Prove2me | solution 1 for GlobalTheory.LineCos.lintegral_fsDensity_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:20.772489+00:00
-- url     : https://prove2.me/submissions/041835be-eb08-4e05-9cf4-ac3ad7ae11e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
import Theorems.Thm_GlobalTheory_LineCos_measurable_cosSq
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_cosSq
import Theorems.Thm_GlobalTheory_T_cosine_square_pushforward_uniform


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ x, (cosSq s G ⁻¹' A).indicator (fun x => ENNReal.ofReal (fsDensity s G x)) x =
      volume.restrict (Icc (0 : ℝ) 1) A := by
  rw [← GlobalTheory.T.cosine_square_pushforward_uniform G s hG, Measure.map_apply (measurable_cosSq s G) hA,
    withDensity_apply _ (measurable_cosSq s G hA), lintegral_indicator (measurable_cosSq s G hA)]
  rfl
end GlobalTheory.LineCos
