-- Prove2me | solution 1 for GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:48.083662+00:00
-- url     : https://prove2.me/submissions/f87280c6-c5af-4eca-9a7a-142179830827

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_nsmul_id_apply
import Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_eq_bot_iff
import Theorems.Thm_GroundTheory_ProfCoh_eq_zero_of_pow_nsmul_eq_zero
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_comp


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
    [IsDiscreteRep A] {p : ℕ} (hp : Function.Bijective fun a : A => p • a) (n : ℕ) :
    AddCommGroup.primaryComponent (cohomology A n) p = ⊥ := by
  have hmono : Mono (p • 𝟙 A) := (Rep.mono_iff_injective _).2 hp.1
  have hepi : Epi (p • 𝟙 A) := (Rep.epi_iff_surjective _).2 hp.2
  have : IsIso (p • 𝟙 A) := isIso_of_mono_of_epi _
  have key : ∀ z : cohomology A n, (cohomologyMap (inv (p • 𝟙 A)) n).hom (p • z) = z := by
    intro z
    rw [← cohomologyMap_nsmul_id_apply]
    change (cohomologyMap (p • 𝟙 A) n ≫ cohomologyMap (inv (p • 𝟙 A)) n).hom z = z
    rw [← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id]
    rfl
  rw [primaryComponent_eq_bot_iff]
  rintro x ⟨k, hk⟩
  refine eq_zero_of_pow_nsmul_eq_zero (fun y hy => ?_) k x hk
  rw [← key y, hy, map_zero]
end GroundTheory.ProfCoh
