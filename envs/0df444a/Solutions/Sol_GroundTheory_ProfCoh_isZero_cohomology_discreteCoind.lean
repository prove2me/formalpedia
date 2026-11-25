-- Prove2me | solution 1 for GroundTheory.ProfCoh.isZero_cohomology_discreteCoind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:22.980921+00:00
-- url     : https://prove2.me/submissions/c651e89c-fdfa-41df-bcf1-71e3fffcf8ba

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Theorems.Thm_GroundTheory_ProfCoh_coindHomotopy_identity
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology Filter Topology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {X : Type u} [AddCommGroup X] [Module k X]
variable (k G X)
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) :
    Limits.IsZero (cohomology (discreteCoind k G X) (n + 1)) := by
  rw [cohomology, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f hf
  let f' : locallyConstantCochains (discreteCoind k G X) (n + 1) := f
  have hf' : (dLocallyConstant (discreteCoind k G X) (n + 1)).hom f' = 0 := by
    change ((cochainsComplex (discreteCoind k G X)).d (n + 1) (n + 2)).hom f = 0 at hf
    rw [cochainsComplex_d] at hf
    exact hf
  refine ⟨coindHomotopy k X n f', ?_⟩
  have := coindHomotopy_identity n f'
  rw [hf', map_zero, add_zero] at this
  change ((cochainsComplex (discreteCoind k G X)).d n (n + 1)).hom (coindHomotopy k X n f') = f
  rw [cochainsComplex_d]
  exact this
end GroundTheory.ProfCoh
