-- Prove2me | solution 1 for GroundTheory.ProfCoh.primary_discreteCoind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:23.914392+00:00
-- url     : https://prove2.me/submissions/e0e01bc4-a22f-418e-9fef-ece41dc083d2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_pow_nsmul_eq_zero_of_le

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
    {p : ℕ} (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (f : discreteCoind (ULift.{u} ℤ) G A) :
    ∃ k : ℕ, p ^ k • f = 0 := by
  let f' : LocallyConstant G A := f
  have : Finite (Set.range f') := f'.range_finite.to_subtype
  choose kk hkk using fun v : Set.range f' => hA v
  obtain ⟨K, hK⟩ := (Set.finite_range kk).bddAbove
  refine ⟨K, LocallyConstant.ext fun x => ?_⟩
  show p ^ K • f' x = 0
  exact pow_nsmul_eq_zero_of_le (hK ⟨⟨f' x, x, rfl⟩, rfl⟩) (hkk ⟨f' x, x, rfl⟩)
end GroundTheory.ProfCoh
