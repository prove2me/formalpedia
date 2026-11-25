-- Prove2me | solution 1 for GlobalTheory.ChartCmp.PushAd.subst_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:38.433477+00:00
-- url     : https://prove2.me/submissions/2a325589-d4cc-41a1-8aad-134e500d96e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.PushAd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
namespace GlobalTheory.ChartCmp.PushAd
theorem _root_.solution (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
    {n n' : ℕ} (m : ℕ) (f : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (α : t.G ⟶ t.G)
    (hα : x m ≫ α = Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)) ≫ x m)
    (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = psIn d m ![k] (f j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k ≫ α := by
  rw [jptG, jptG, Category.assoc, hα, ← Category.assoc, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp,
    Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp]
  congr 2
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  have e : (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.X ∘ fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin n') p.1, p.2) := by
    funext p
    simp
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X, h, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [e, ← MvPolynomial.rename_eq_aeval]
end GlobalTheory.ChartCmp.PushAd
