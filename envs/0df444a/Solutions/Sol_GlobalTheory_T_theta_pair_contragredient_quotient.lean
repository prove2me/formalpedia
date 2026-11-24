-- Prove2me | solution 1 for GlobalTheory.T.theta_pair_contragredient_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:30.0351+00:00
-- url     : https://prove2.me/submissions/be7a9b17-9dcf-453f-b697-019c156bc94d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotientStatement
import Theorems.Thm_GlobalTheory_ThetaGL_omQuot_contra_of_thetaPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsSmoothChar μ → IsAdmissible π → ThetaPair μ σ π → OmQuot μ σ (contra π) := by
  first | exact @GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair | exact GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair | (intros; apply GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair <;> assumption)
end _root_.GlobalTheory.T
