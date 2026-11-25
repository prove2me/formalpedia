-- Prove2me | solution 1 for GroundTheory.ProfCoh.isAddTorsion_discreteCoind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:15.317948+00:00
-- url     : https://prove2.me/submissions/bcaca41b-7b64-4388-8bed-391ff0ebe482

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_Procyclic
import Theorems.Thm_GroundTheory_ProfCoh_H1Iso_hom
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


attribute [local simp] GroundTheory.ProfCoh.H1Iso_hom

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (X : Type u) [AddCommGroup X] [Module k X]
    (hX : IsAddTorsion X) : IsAddTorsion (discreteCoind k G X) := by
  intro f
  classical
  have hfin := (f : LocallyConstant G X).range_finite
  set s := hfin.toFinset
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨∏ v ∈ s, addOrderOf v, Finset.prod_pos fun v _ => (hX v).addOrderOf_pos, ?_⟩
  change (∏ v ∈ s, addOrderOf v) • (f : LocallyConstant G X) = 0
  ext x
  rw [LocallyConstant.coe_smul, Pi.smul_apply, LocallyConstant.coe_zero, Pi.zero_apply,
    ← addOrderOf_dvd_iff_nsmul_eq_zero]
  exact Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 ⟨x, rfl⟩)
end GroundTheory.ProfCoh
