-- Prove2me | solution 1 for GlobalTheory.SmGL.ContraTrace.smoothOp_contra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:27.177643+00:00
-- url     : https://prove2.me/submissions/06c9eb68-ca89-4be3-b2ba-f61199c339dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_contra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.ContraTrace
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.SmGL.ContraTrace
theorem _root_.solution [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by
  have h1 := (isSmooth_contra π).map_smoothOp (μ := μ) hf hc
    (Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype) l
  have h2 := hπ.map_smoothOp (μ := μ) (f := fun g => f g⁻¹) (hf.comp_continuous continuous_inv)
    (hc.comp_homeomorph (Homeomorph.inv G)) (l : Module.Dual ℂ V) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun g => ?_)
  show f g⁻¹ • (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = f g⁻¹ • (l : Module.Dual ℂ V) (π g v)
  rw [inv_inv]
end GlobalTheory.SmGL.ContraTrace
