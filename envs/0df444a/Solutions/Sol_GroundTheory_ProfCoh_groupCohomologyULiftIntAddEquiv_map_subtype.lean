-- Prove2me | solution 1 for GroundTheory.ProfCoh.groupCohomologyULiftIntAddEquiv_map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:50.904309+00:00
-- url     : https://prove2.me/submissions/25a60f69-27a8-40f2-a0d0-f80ef13fc554

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_FiniteVanishing_IntScalars
import Theorems.Thm_P2M_GroundTheory_ProfCoh_forget__homologyMap_comp_forget_HomologyIso_83a1bdaab274

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
variable {Γ : Type} [Group Γ]
namespace GroundTheory.ProfCoh
theorem _root_.solution (M : Rep.{0} (ULift.{0} ℤ) Γ) (S : Subgroup Γ)
    (n : ℕ) (x : groupCohomology M n) :
    groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) n
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) n).hom x) =
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) n).hom
        (groupCohomologyULiftIntAddEquiv M n x) := by
  have key := forget₂_homologyMap_comp_forget₂HomologyIso
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (cochainsMap S.subtype (𝟙 (Rep.res S.subtype M))))
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (cochainsMap S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M)))))
    (cochainsScULiftIntIso M n) (cochainsScULiftIntIso (Rep.res S.subtype M) n) (by
      ext x <;> rfl)
  exact congrArg (fun f => f.hom x) key
end GroundTheory.ProfCoh
