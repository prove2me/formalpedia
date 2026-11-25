-- Prove2me | solution 1 for GroundTheory.Global.discreteTopology_principalSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:27.728967+00:00
-- url     : https://prove2.me/submissions/fbd8c36a-1d36-4db2-91a6-5f2c56ba744a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Theorems.Thm_GroundTheory_Global_exists_eq_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_discreteTopology_of_isOpen_of_forall_mem
import Theorems.Thm_GroundTheory_Global_eq_zero_of_forall_infinitePlace_lt_one
import Theorems.Thm_GroundTheory_Global_isOpen_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_norm_algebraMap_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  refine discreteTopology_of_isOpen_of_forall_mem _
    ({x : K∞ | ∀ w, ‖x w‖ < 1} ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))
    ?_ ⟨fun w => by
      show ‖(0 : K∞) w‖ < 1
      rw [show (0 : K∞) w = 0 from rfl, norm_zero]; exact one_pos,
      Subring.zero_mem _⟩ ?_
  · refine IsOpen.prod ?_ isOpen_integralFiniteAdeles
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_apply (A := fun w : InfinitePlace K => w.Completion) w).norm
        continuous_const
  · rintro _ ⟨k, rfl⟩ ⟨hinf, hf⟩
    obtain ⟨z, rfl⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K k hf
    have hz : ∀ w : InfinitePlace K, w z < 1 := fun w => by
      have := hinf w
      rwa [show (algebraMap K 𝔸[K] (z : K)).1 = algebraMap K K∞ (z : K) from rfl,
        norm_algebraMap_apply] at this
    rw [eq_zero_of_forall_infinitePlace_lt_one K z hz]
    simp
end GroundTheory.Global
