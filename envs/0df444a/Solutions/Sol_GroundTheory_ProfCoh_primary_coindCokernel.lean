-- Prove2me | solution 1 for GroundTheory.ProfCoh.primary_coindCokernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:18.785891+00:00
-- url     : https://prove2.me/submissions/066ccf8c-1e97-47a4-bdc1-e53d8d4cfd75

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_primary_discreteCoind
import Theorems.Thm_GroundTheory_ProfCoh_coindShortComplex_shortExact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A]
    {p : ℕ} (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (x : coindCokernel A) :
    ∃ k : ℕ, p ^ k • x = 0 := by
  have hepi : Epi (coindCokernelπ A) := (coindShortComplex_shortExact A).epi_g
  obtain ⟨f, rfl⟩ := (Rep.epi_iff_surjective (coindCokernelπ A)).1 hepi x
  obtain ⟨k, hk⟩ := primary_discreteCoind A hA f
  exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
end GroundTheory.ProfCoh
