-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Coord.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:23:36.08659+00:00
-- url     : https://prove2.me/submissions/a4f0e490-192e-4da8-a434-7903d3382a48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.Coord
theorem _root_.solution {G : Over (Sp V)} [GrpObj G] {κ : Type} {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A : Type} [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    {ψ₁ ψ₂ : Jet V κ m →ₐ[V] A} (h1 : aug.comp ψ₁ = jetAug) (h2 : aug.comp ψ₂ = jetAug)
    (e : Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₂ ≫ x m) : ψ₁ = ψ₂ := by
  have hy : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m) = 1 := by
    rw [← Category.assoc, GermD.homAt_comp, h1, hx.2.1]
  exact (hx.2.2 A aug m hk _ hy).unique ⟨h1, rfl⟩ ⟨h2, e⟩
end GlobalTheory.ChartCmp.Coord
