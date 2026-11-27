-- Prove2me | solution 1 for GlobalTheory.AnVal.AnPt.chart_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:10:59.556333+00:00
-- url     : https://prove2.me/submissions/73309c05-203c-44be-b473-8c7e2850af2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameExponentialJetsIsChart
import Theorems.Thm_GlobalTheory_AnVal_AnPt_chart_jx_left
import Theorems.Thm_GlobalTheory_AnVal_AnPt_chart_e_zero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_epsMul_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_tan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_spMap_epsMul_zero_jetTan


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
theorem _root_.solution (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (fun z => (Φ.e z).left) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        Φ.jx (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  classical
  let v : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j =>
    homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ Φ.jx (0 + 1)
  let u : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j => epsHom y.x (if j = j0 then 1 else 0) ≫ v j
  refine ⟨u, fun j => by simp [u, v, epsHom], ?_⟩
  have hone : ∀ j, j ≠ j0 → u j = 1 := by
    intro j hj
    ext1
    simp only [u, v, if_neg hj, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left]
    rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug, one_left'']
    show spMap _ ≫ (Φ.e 0).left = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y.x) ≫ _
    rw [Φ.chart_e_zero, one_left'', Category.assoc]
    rfl
  have hprod : (List.ofFn u).prod = u j0 := by
    rw [List.prod_ofFn, Finset.prod_eq_single j0 (fun j _ hj => hone j hj) (by simp)]
  rw [hprod]
  simp only [u, v, if_pos rfl, ite_true, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left,
    epsMul_one]
  rw [show spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ from by simp [spMap]]
  exact (Category.id_comp _).trans (jetPt_tan (fun z => (Φ.e z).left) Φ.hol ((0 : Fin 1), j0) vt hd)
end AnPt
end GlobalTheory.AnVal
