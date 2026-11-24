-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.TwoVarSetup.exists_liftAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:48.992053+00:00
-- url     : https://prove2.me/submissions/356b1a97-adbd-4163-a98b-cbd02788693e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasicOpenFactorFieldPointAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsArcQuotientTwoVariableCoords

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
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf GlobalTheory.SS.ArcInf.TwoVarSetup
namespace GlobalTheory.SS.ArcInf.TwoVarSetup
theorem _root_.solution {k R F : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing F] [Algebra k F]
    (x : R) (τ : R →ₐ[k] F) (h : IsUnit (τ x)) :
    ∃ τ' : Localization.Away x →ₐ[k] F, ∀ y, τ' (algebraMap R _ y) = τ y := by
  have hu : ∀ y : Submonoid.powers x, IsUnit (τ y) := by
    rintro ⟨y, n, rfl⟩
    show IsUnit (τ (x ^ n))
    rw [map_pow]; exact h.pow n
  exact ⟨IsLocalization.liftAlgHom (S := Localization.Away x) hu, fun x => by simp⟩
end GlobalTheory.SS.ArcInf.TwoVarSetup
