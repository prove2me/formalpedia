-- Prove2me | solution 1 for GroundTheory.ProfCoh.eq_zero_of_pow_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:28.148394+00:00
-- url     : https://prove2.me/submissions/8f158181-4ce5-4987-8c03-e02a0fd1b41e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {M : Type*} [AddCommMonoid M] {p : ℕ}
    (hp : ∀ x : M, p • x = 0 → x = 0) (k : ℕ) (x : M) (hx : p ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih =>
    apply hp
    apply ih
    rw [← mul_smul, ← pow_succ]
    exact hx
end GroundTheory.ProfCoh
