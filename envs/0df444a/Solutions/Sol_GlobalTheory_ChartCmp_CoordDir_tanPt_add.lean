-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordDir.tanPt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:06.425771+00:00
-- url     : https://prove2.me/submissions/81d0de8e-86f8-4498-bc9a-6f1b2d360562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_lin_F
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_fin_one_pair_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordDir
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}
variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
namespace GlobalTheory.ChartCmp.CoordDir
theorem _root_.solution (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) (g g' : Fin 1 × Fin d → V) :
    tanPt x (g + g') = tanPt x g * tanPt x g' := by
  let T : Jet V (Fin 2 × Fin d) (0 + 1) →ₐ[V] DualNumber V :=
    tp (fun p : Fin 2 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2)
  have hT : T = tp (fun p : Fin 2 × Fin d =>
    (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2) := rfl
  have hc : ∀ i : Fin 2, T.comp (jetCopy d (0 + 1) i) =
      tp (fun q : Fin 1 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) i q.2) := by
    intro i
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, hT, tp_mk, tp_mk]
  have h0 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 0 q.2) = tp g := by
    congr 1
    funext q
    simp only [Matrix.cons_val_zero, fin_one_pair_eq]
  have h1 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 1 q.2) = tp g' := by
    congr 1
    funext q
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, fin_one_pair_eq]
  have hF : T.comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) = tp (g + g') := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => G.F p.2) (fun p => G.const p.2),
      hT, tp_psJet, tp_mk, G.const, TrivSqZeroExt.inl_zero, zero_add, lin_F]
    simp only [Pi.add_apply, fin_one_pair_eq]
  have hl : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) ≫ x 1 =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (0 : Fin 2)) ≫ x 1) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (1 : Fin 2)) ≫ x 1) :=
    hx.law 1
  have e := congrArg (fun f => Formalism.L2.Pj.homAt (𝟙 (Sp V)) T ≫ f) hl
  simp only [MonObj.comp_mul, ← Category.assoc, GermD.homAt_comp, hc, hF, h0, h1] at e
  exact e
end GlobalTheory.ChartCmp.CoordDir
