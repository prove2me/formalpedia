-- Prove2me | solution 1 for GroundTheory.Global.exists_isCompact_forall_exists_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:32.580838+00:00
-- url     : https://prove2.me/submissions/f000e56a-832f-4a68-921b-86db7e291b62

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Theorems.Thm_GroundTheory_Global_existsUnique_sub_mem_fundamentalSet
import Theorems.Thm_GroundTheory_Global_isCompact_closure_fundamentalSetInfinite


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
    ∃ C : Set K∞, IsCompact C ∧ ∀ x : 𝔸[K], ∃ k : K, x - algebraMap K 𝔸[K] k ∈
      C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine ⟨closure (fundamentalSetInfinite K), isCompact_closure_fundamentalSetInfinite K,
    fun x => ?_⟩
  obtain ⟨k, ⟨hinf, hf⟩, -⟩ := existsUnique_sub_mem_fundamentalSet K x
  exact ⟨k, subset_closure hinf, hf⟩
end GroundTheory.Global
