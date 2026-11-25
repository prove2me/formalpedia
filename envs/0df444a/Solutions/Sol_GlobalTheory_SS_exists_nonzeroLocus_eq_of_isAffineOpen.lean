-- Prove2me | solution 1 for GlobalTheory.SS.exists_nonzeroLocus_eq_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:35.079365+00:00
-- url     : https://prove2.me/submissions/befc2ca7-895b-4c8d-b0b6-8b83564bd876

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsNonzeroLocusEqOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AffineComplement_exists_nonzeroLocus_eq


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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ W : X.Opens, IsAffineOpen W → (W : Set X).Nonempty → ∃ (L : LB X) (s : LB.Sec L), L.IsLB ∧ Out.nonzeroLocus s = W :=
  fun X _ _ _ _ h W hW hne => GlobalTheory.AffineComplement.exists_nonzeroLocus_eq X W hW hne h
end GlobalTheory.SS
