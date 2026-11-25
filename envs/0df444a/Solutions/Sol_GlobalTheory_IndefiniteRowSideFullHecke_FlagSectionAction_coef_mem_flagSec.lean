-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.coef_mem_flagSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:43.936459+00:00
-- url     : https://prove2.me/submissions/ff974dfa-289d-40ae-8e58-cf17ac25dc93

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_CoefMemFlagSec
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlagSectionAction_isFlagSec_coefFn
import Theorems.Thm_Formalism_L2_Pj_FJ_coefL_apply
import Theorems.Thm_Formalism_L2_Pj_dom_rmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) (X : Data E r) (la : Wt X.Ψ r) (cu : FJ.CuspFD X ρ)
    (hd : ∀ t, ∀ x ∈ X.dom, zAct X cu t x ∈ X.dom) (ph : Fin (nZ X ρ) → ℝ) (P : OrbInt (zAct X cu) X.dom)
    (hP : IsFlagSec X la P) :
    (show FnVia σ (Frame X.Ψ r) from coefL (zAct X cu) X.dom ph P) ∈ flagSec σ X la := by
  have h := isFlagSec_coefFn X la cu hd ph hP
  refine ⟨⟨h.1.congr fun x hx => coefL_apply _ _ _ _ hx, fun x hx b hb => ?_⟩, fun x hx => ?_⟩
  · change coefL (zAct X cu) X.dom ph P (rmul x b) = bchar la b * coefL (zAct X cu) X.dom ph P x
    rw [coefL_apply _ _ _ _ hx, coefL_apply _ _ _ _ (dom_rmul X hx hb)]
    exact h.2 x hx b hb
  · change coefL (zAct X cu) X.dom ph P x = 0
    simp [coefL, hx]
end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
