-- Prove2me | solution 1 for GroundTheory.ProfCoh.cdp_le_iff_forall_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:04.433168+00:00
-- url     : https://prove2.me/submissions/fc174db6-a50e-4fb6-8ddc-6c40596635a3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cdp_le_of_forall_primary
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_cdp_le
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_finite_of_simple
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_primary_of_finite
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_add_of_primary

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
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (hp : p.Prime) (n : ℕ) :
    cdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      IsSimpleOrder (Subrepresentation A.ρ) → (∀ a : A, p • a = 0) →
        Subsingleton (cohomology A (n + 1)) := by
  refine ⟨fun h A _ _ hA => subsingleton_cohomology_of_cdp_le hp h A hA (Nat.lt_succ_self n),
    fun h => cdp_le_of_forall_primary hp ?_⟩
  intro A _ hA q hq
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hq
  have := subsingleton_cohomology_add_of_primary
    (fun B _ hB => subsingleton_cohomology_of_primary_of_finite hp.pos
      (fun C _ _ hC => subsingleton_cohomology_of_finite_of_simple h C hC) B hB) j A hA
  rwa [show n + 1 + j = n + j + 1 by omega] at this
end GroundTheory.ProfCoh
