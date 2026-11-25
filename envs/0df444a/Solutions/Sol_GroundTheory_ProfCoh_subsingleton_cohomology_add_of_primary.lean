-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_cohomology_add_of_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:06.186833+00:00
-- url     : https://prove2.me/submissions/16625bde-85df-40f3-bed7-40d96af5348b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_primary_coindCokernel

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
theorem _root_.solution [CompactSpace G] {p : ℕ} {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      Subsingleton (cohomology A (m + 1))) (j : ℕ) :
    ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      Subsingleton (cohomology A (m + 1 + j)) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro A _ hA
    have h' := ih (coindCokernel A) (primary_coindCokernel A hA)
    rw [show m + 1 + j = m + j + 1 by omega] at h'
    rw [show m + 1 + (j + 1) = m + j + 2 by omega]
    exact (cohomologyCoindCokernelIso A (m + j)).toLinearEquiv.symm.toEquiv.subsingleton
end GroundTheory.ProfCoh
