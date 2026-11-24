-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.IsChart.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:46.098183+00:00
-- url     : https://prove2.me/submissions/abe30294-4dfa-4bd5-ad27-25d6a64a0a0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective

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
variable {k : Type} [Field k]
namespace GlobalTheory.SS.ArcInf
namespace IsChart
theorem _root_.solution {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A} (hc : IsChart G j ε f) {B : Type} [CommRing B] [Algebra k B]
    {a b : A →ₐ[k] B} (h : ∀ i, a (f i) = b (f i)) : a = b :=
  AlgHom.ext_of_adjoin_eq_top hc.2.2.1 (by rintro _ ⟨i, rfl⟩; exact h i)
end IsChart
end GlobalTheory.SS.ArcInf
