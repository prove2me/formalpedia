-- Prove2me | solution 1 for GlobalTheory.AnVal.AnPt.chart_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:35.388908+00:00
-- url     : https://prove2.me/submissions/7deaabd9-ce10-4ce9-98f4-1639c839d43c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameExponentialJetsIsChart
import Theorems.Thm_GlobalTheory_AnVal_AnPt_chart_jx_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolFam_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetSubstP_anAct


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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)
namespace GlobalTheory.AnVal
namespace AnPt
theorem _root_.solution (m : ℕ) (a : 𝓞 E) :
    Φ.jx m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ Φ.jx m := by
  ext1
  rw [Over.comp_left, Over.comp_left, Φ.chart_jx_left]
  have hlin : ∀ z, (Φ.e z).left ≫ (Xo.univ.t.act.act a).left = (Φ.e (fun k => ty k (a : E) * z k)).left := by
    intro z
    rw [← Over.comp_left, ← Φ.lin a z]
    rfl
  have hol' := isHolFam_comp (fun z => (Φ.e z).left) Φ.hol (Xo.univ.t.act.act a).left
  rw [jetPt_comp (fun z => (Φ.e z).left) Φ.hol _ _ hol' (fun z => rfl)]
  haveI : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m)
      (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2))))
      (fun _ => sub_const_mem_orig _)
  symm
  refine jetPt_precomp (fun z => (Φ.e z).left) _ Φ.hol hol' ?_ m _ ?_
  · show (Φ.e 0).left ≫ _ = (Φ.e 0).left
    rw [hlin]; congr 2; funext k; simp
  · intro U hU f
    change jetSubstP m _ (jetOf m _) = _
    rw [jetSubstP_anAct, ← jetOf_scale m _ (contDiffAt_val _ Φ.hol hU f)]
    congr 1
    funext z
    show valAt' (Φ.e _).left U f = valAt' ((Φ.e z).left ≫ _) U f
    rw [hlin]
end AnPt
end GlobalTheory.AnVal
