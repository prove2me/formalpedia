-- Prove2me | solution 1 for GlobalTheory.T.det_commutator_map_eq_charpoly_resultant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:44.039261+00:00
-- url     : https://prove2.me/submissions/3a2eaf73-69e4-4d52-920f-ffab90c619c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultantStatement
import Theorems.Thm_GlobalTheory_DetAdResultant_det_ad_eq_resultant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂), LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) = resultant f₁.charpoly f₂.charpoly := by
  first | exact @GlobalTheory.DetAdResultant.det_ad_eq_resultant | exact GlobalTheory.DetAdResultant.det_ad_eq_resultant | (intros; apply GlobalTheory.DetAdResultant.det_ad_eq_resultant <;> assumption)
end _root_.GlobalTheory.T
