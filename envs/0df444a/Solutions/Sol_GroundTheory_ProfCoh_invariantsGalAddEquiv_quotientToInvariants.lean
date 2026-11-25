-- Prove2me | solution 1 for GroundTheory.ProfCoh.invariantsGalAddEquiv_quotientToInvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:38.795171+00:00
-- url     : https://prove2.me/submissions/d75288ec-0d77-4d10-b246-5b9cc731bd41

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open IntermediateField InfiniteGalois
universe u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] (U : OpenNormalSubgroup Gal(L/K))
namespace GroundTheory.ProfCoh
theorem _root_.solution (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (x : Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsGalAddEquiv U (((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q x) =
      quotientEquivGal U q (invariantsGalAddEquiv U x) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply Subtype.ext
    rw [quotientEquivGal_mk_apply]
    rfl
end GroundTheory.ProfCoh
