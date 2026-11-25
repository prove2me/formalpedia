-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.isFlagSec_coefFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:52.782163+00:00
-- url     : https://prove2.me/submissions/42c5cb5c-0024-44ae-994b-fe72fc012dc1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_CoefMemFlagSec
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlagSectionAction_zAct_rmul
import Theorems.Thm_GlobalTheory_differentiableOn_setIntegral_of_holomorphic_of_continuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_isOpen_dom


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
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (cu : FJ.CuspFD X ρ)
    (hd : ∀ t, ∀ x ∈ X.dom, zAct X cu t x ∈ X.dom) (ph : Fin (nZ X ρ) → ℝ) {P : Frame X.Ψ r → ℂ}
    (hP : IsFlagSec X la P) : IsFlagSec X la (coefFn (zAct X cu) ph P) := by
  constructor
  · have hj : Continuous fun p : (Fin (nZ X ρ) → ℝ) × Frame X.Ψ r => zAct X cu p.1 p.2 := by
      unfold zAct zMatC mat
      fun_prop
    have hc : Continuous (chr ph) := by unfold chr; fun_prop
    refine (GlobalTheory.differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume)
      (F := fun t x => integrand (zAct X cu) ph P x t) (FourierCoefficientDomain.isOpen_dom X) (S := cube _) (K := cube _)
      isCompact_Icc subset_rfl measurableSet_Icc (isCompact_Icc.measure_lt_top.ne) ?_ ?_).1
    · refine ContinuousOn.mul (hP.1.continuousOn.comp hj.continuousOn fun p hp => hd p.1 p.2 hp.2) ?_
      exact (hc.comp continuous_fst).continuousOn
    · intro t _
      refine DifferentiableOn.mul_const (hP.1.comp ?_ fun x hx => hd t x hx) _
      refine Differentiable.differentiableOn ?_
      refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun k => ?_
      simp only [zAct, Matrix.mul_apply, mat, Matrix.of_apply]
      fun_prop
  · intro x hx b hb
    unfold coefFn integrand
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [zAct_rmul, hP.2 _ (hd t x hx) b hb, mul_assoc]
end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
