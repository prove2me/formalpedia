-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_bound_infinite_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:31.804751+00:00
-- url     : https://prove2.me/submissions/0ea245e8-c756-4acf-b98e-e85bcfcc6784

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_infiniteComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {S : Set (IdeleGroup K)} (hS : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ S, ∀ w : InfinitePlace K, ‖(s : 𝔸[K]).1 w‖ ≤ M := by
  have hc : Continuous fun s : IdeleGroup K => ∑ w : InfinitePlace K, ‖(s : 𝔸[K]).1 w‖ :=
    continuous_finsetSum _ fun w _ => (continuous_infiniteComponent w).norm
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s hs w => ?_⟩
  have h := (Real.le_norm_self _).trans (hM s hs)
  exact ((Finset.single_le_sum (f := fun w : InfinitePlace K => ‖(s : 𝔸[K]).1 w‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ w)).trans h).trans (le_max_left _ _)
end GroundTheory.Automorphic.Reduction
