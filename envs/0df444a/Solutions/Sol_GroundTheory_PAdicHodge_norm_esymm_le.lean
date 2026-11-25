-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_esymm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:29:32.346033+00:00
-- url     : https://prove2.me/submissions/785f7209-6114-4fd1-a61c-31c1a1753a55

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_sum_le_of_forall_le
import Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_prod_le_pow_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {s : Multiset E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ a ∈ s, ‖a‖ ≤ C) (j : ℕ) :
    ‖s.esymm j‖ ≤ C ^ j := by
  rw [Multiset.esymm]
  refine norm_multiset_sum_le_of_forall_le (pow_nonneg hC j) fun a ha => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 ha
  rw [Multiset.mem_powersetCard] at ht
  rw [← ht.2]
  exact norm_multiset_prod_le_pow_card fun b hb => h b (Multiset.subset_of_le ht.1 hb)
end GroundTheory.PAdicHodge
