-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:39.105848+00:00
-- url     : https://prove2.me/submissions/423cb97d-7290-46f3-af8b-5559a10c7db1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Theorems.Thm_GlobalTheory_SS_ArcInf_algOverHom_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]
namespace GlobalTheory.SS.ArcInf
theorem _root_.solution {G : Over (Sp k)} {j : algOver k A ⟶ G} (hj : IsOpenImmersion j.left) {a b : A →ₐ[k] B}
    (h : algOverHom a ≫ j = algOverHom b ≫ j) : a = b := by
  apply algOverHom_injective
  ext1
  have := congrArg (fun x => x.left) h
  simp only [Over.comp_left] at this
  exact (cancel_mono j.left).1 this
end GlobalTheory.SS.ArcInf
