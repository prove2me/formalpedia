-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.lintegral_eq_lintegral_parabolic_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:42.189358+00:00
-- url     : https://prove2.me/submissions/62bc1fb2-2c8d-44fd-8253-0734e654cc8f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_lintegral_parabolic_integralGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] {β : Fin n → α}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (hβ : Monotone β)
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β))
    [μP.IsHaarMeasure] (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure]
    (hG : μG (GLnLocal.integralGL F n) = 1)
    (hP : μP (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) = 1)
    (hK : μK univ = 1) {f : GL (Fin n) F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂μG = ∫⁻ p, ∫⁻ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP := by
  have h := lintegral_parabolic_integralGL F n hβ μG μP μK hf
  rw [hG, hP, hK, one_mul, one_mul, one_mul] at h
  exact h.symm
end GroundTheory.Automorphic.Measures
