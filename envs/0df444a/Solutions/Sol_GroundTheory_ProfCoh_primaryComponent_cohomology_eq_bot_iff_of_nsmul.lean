-- Prove2me | solution 1 for GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_iff_of_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:07.509053+00:00
-- url     : https://prove2.me/submissions/30a54b18-5e05-4b8a-9c8e-7e6cd6e538ce

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_nsmul_cohomology_eq_zero
import Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_eq_bot_iff

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
theorem _root_.solution (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hA : ∀ a : A, p • a = 0) (n : ℕ) :
    AddCommGroup.primaryComponent (cohomology A n) p = ⊥ ↔ Subsingleton (cohomology A n) := by
  rw [primaryComponent_eq_bot_iff]
  have h1 : ∀ x : cohomology A n, ∃ k : ℕ, p ^ k • x = 0 := fun x =>
    ⟨1, by rw [pow_one]; exact nsmul_cohomology_eq_zero A hA n x⟩
  exact ⟨fun h => ⟨fun x y => by rw [h x (h1 x), h y (h1 y)]⟩,
    fun h x _ => Subsingleton.elim _ _⟩
end GroundTheory.ProfCoh
