-- Prove2me | solution 1 for GlobalTheory.LinkLaw.read_match
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:10.400281+00:00
-- url     : https://prove2.me/submissions/fd84e9a5-c251-41da-938d-78c17ce72758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkLaw
variable {V : Type} [CommRing V]
namespace GlobalTheory.LinkLaw
theorem _root_.solution {G : Over (Sp V)} {κ : Type} {N m : ℕ} (z : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (x : Chart.sp (R₀ := V) (Chart.JetR V (Fin N) m) ⟶ G) (e : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m)
    (he : z.left = Geo.Tor.spMap (e : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ x.left)
    {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (S : Jet V κ m →ₐ[V] B) (Φ : B →ₐ[V] A) :
    (toAt A ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) Φ) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) S ≫ z =
      Chart.spMap (Φ.comp (S.comp (e : Chart.JetR V (Fin N) m →ₐ[V] Jet V κ m))) ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, he, Chart.spMap_left, toAt, Formalism.L2.Pj.homAt, Over.homMk_left, Category.id_comp,
    ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp]
  rfl
end GlobalTheory.LinkLaw
