-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.integral_eq_integral_parabolic_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:40.658485+00:00
-- url     : https://prove2.me/submissions/7058337f-4ab7-4601-9d37-3d69b7c6c093

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_integral_parabolic_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply



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
    (hK : μK univ = 1) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : GL (Fin n) F → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG = ∫ p, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP := by
  have h := integral_parabolic_integralGL F n hβ μG μP μK hf
  simp only [Measure.real, hG, hP, hK, ENNReal.toReal_one, one_mul, one_smul] at h
  exact h.symm
end GroundTheory.Automorphic.Measures
