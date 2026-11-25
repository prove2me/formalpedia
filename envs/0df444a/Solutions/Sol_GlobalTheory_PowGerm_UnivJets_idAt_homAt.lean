-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.idAt_homAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:10.3468+00:00
-- url     : https://prove2.me/submissions/d4935a8d-69c8-4638-b8ae-5588de75102b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivJets
variable {V : Type} [CommRing V] {G : Over (Sp V)}
namespace GlobalTheory.PowGerm.UnivJets
theorem _root_.solution {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (y : overAt (𝟙 (Sp V)) A ⟶ G) :
    idAt B ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f ≫ y = Chart.spMap f ≫ idAt A ≫ y := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, idAt, Over.homMk_left, Category.id_comp]
  rfl
end GlobalTheory.PowGerm.UnivJets
