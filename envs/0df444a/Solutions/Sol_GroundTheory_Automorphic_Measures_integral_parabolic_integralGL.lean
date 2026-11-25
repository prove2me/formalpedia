-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.integral_parabolic_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:08.852929+00:00
-- url     : https://prove2.me/submissions/205cbfc2-201c-46b6-b0e4-b4a373bb09ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_integral_mul_prod_eq
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_blockUpper_mul_integralGL


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
theorem _root_.solution (hβ : Monotone β) (μG : Measure (GL (Fin n) F))
    [μG.IsHaarMeasure] (μP : Measure (Iwasawa.blockUpper F n β)) [μP.IsHaarMeasure]
    (μK : Measure (GLnLocal.integralGL F n)) [μK.IsHaarMeasure] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : GL (Fin n) F → E}
    (hf : Integrable f μG) :
    μG.real (GLnLocal.integralGL F n) • ∫ p, ∫ k, f ((p : GL (Fin n) F) * k) ∂μK ∂μP =
      (μP.real (Subtype.val ⁻¹' (GLnLocal.integralGL F n : Set (GL (Fin n) F))) * μK.real univ) •
        ∫ g, f g ∂μG :=
  integral_mul_prod_eq _ _ (isClosed_blockUpper F n β) (GLnLocal.isOpen_integralGL F n)
    (GLnLocal.isCompact_integralGL F n) (Iwasawa.exists_blockUpper_mul_integralGL F n hβ)
    μG μP μK hf
end GroundTheory.Automorphic.Measures
