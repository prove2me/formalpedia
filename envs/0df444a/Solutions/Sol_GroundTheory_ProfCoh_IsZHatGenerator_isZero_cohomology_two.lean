-- Prove2me | solution 1 for GroundTheory.ProfCoh.IsZHatGenerator.isZero_cohomology_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:04.875825+00:00
-- url     : https://prove2.me/submissions/6b0e9f13-3229-4423-b85f-d2c7c02f4fba

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_Procyclic
import Theorems.Thm_GroundTheory_ProfCoh_mem_range_sub_one_discreteCoind

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
open CategoryTheory Limits groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {σ : G}
namespace GroundTheory.ProfCoh
namespace IsZHatGenerator
theorem _root_.solution (hσ : IsZHatGenerator σ) (A : Rep.{u} k G)
    [IsDiscreteRep A] (hA : IsAddTorsion A) : IsZero (cohomology A 2) := by
  refine IsZero.of_iso ?_ (cohomologyCoindCokernelIso A 0).symm
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  apply H1Eval_injective (coindCokernel A) hσ.dense
  refine Subsingleton.elim (h := ⟨fun q q' => ?_⟩) _ _
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨q', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
  rw [Submodule.Quotient.eq]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (q - q')
  rw [← hc]
  obtain ⟨d, hd⟩ := mem_range_sub_one_discreteCoind hσ A hA c
  refine ⟨(coindCokernelπ A).hom d, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, ← Rep.hom_comm_apply, ← map_sub]
  rw [← hd]
  rfl
end IsZHatGenerator
end GroundTheory.ProfCoh
