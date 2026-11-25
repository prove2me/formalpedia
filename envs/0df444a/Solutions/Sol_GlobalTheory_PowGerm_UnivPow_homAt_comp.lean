-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivPow.homAt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:16:21.133117+00:00
-- url     : https://prove2.me/submissions/df5e5238-b654-44c6-9a79-21776c3b73c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsPowerProduct
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
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivPow
variable {V : Type} [CommRing V]
namespace GlobalTheory.PowGerm.UnivPow
theorem _root_.solution {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
    Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[V] C) : A →+* C))
  rw [← Spec.map_comp]
  rfl
end GlobalTheory.PowGerm.UnivPow
