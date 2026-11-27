-- Prove2me | solution 1 for GroundTheory.ProfCoh.cdp_le_iff_forall_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:06.752806+00:00
-- url     : https://prove2.me/submissions/2a85bc71-0d0d-418d-b8dd-3c09446e68ee

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
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → ∀ q : ℕ, n < q → Subsingleton (cohomology A q) := by
  refine ⟨fun h => ?_, cdp_le_of_forall_primary hp⟩
  have hsimple : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      IsSimpleOrder (Subrepresentation A.ρ) → (∀ a : A, p • a = 0) →
        Subsingleton (cohomology A (n + 1)) :=
    fun A _ _ hA => subsingleton_cohomology_of_cdp_le hp h A hA (Nat.lt_succ_self n)
  have hprim : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Subsingleton (cohomology A (n + 1)) :=
    fun A _ hA => subsingleton_cohomology_of_primary_of_finite hp.pos
      (fun B _ _ hB => subsingleton_cohomology_of_finite_of_simple hsimple B hB) A hA
  intro A _ hA q hq
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hq
  have := subsingleton_cohomology_add_of_primary hprim j A hA
  rwa [show n + 1 + j = n + j + 1 by omega] at this
end GroundTheory.ProfCoh
