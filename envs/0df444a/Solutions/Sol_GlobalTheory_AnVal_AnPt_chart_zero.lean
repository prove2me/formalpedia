-- Prove2me | solution 1 for GlobalTheory.AnVal.AnPt.chart_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:11:04.884925+00:00
-- url     : https://prove2.me/submissions/5fe47016-0276-4f62-95b8-3b5e4c9d021f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameExponentialJetsIsChart
import Theorems.Thm_GlobalTheory_AnVal_AnPt_chart_jx_left
import Theorems.Thm_GlobalTheory_AnVal_AnPt_chart_e_zero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_aug


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
theorem _root_.solution (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ Φ.jx m = 1 := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, one_left'']
  have h1 := jetPt_aug (fun z => (Φ.e z).left) Φ.hol m
  refine h1.trans ?_
  show (Φ.e 0).left = _
  rw [Φ.chart_e_zero, one_left'']
  show y.x ≫ _ = (spMap (algebraMap ℂ ℂ) ≫ y.x) ≫ _
  rw [Algebra.algebraMap_self, spMap]
  simp
end AnPt
end GlobalTheory.AnVal
