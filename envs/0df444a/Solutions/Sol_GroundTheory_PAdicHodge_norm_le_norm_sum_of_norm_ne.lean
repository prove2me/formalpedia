-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_le_norm_sum_of_norm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:06.88537+00:00
-- url     : https://prove2.me/submissions/359d1f48-8795-4536-b9b5-5716bdb0f7fb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {R : Type*} [NormedField R] [IsUltrametricDist R]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) :
    ∀ i ∈ s, ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by
  classical
  intro i hi
  obtain ⟨m, hm, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) ⟨i, hi⟩
  refine (hmax i hi).trans ?_
  rcases eq_or_ne (f m) 0 with h0 | h0
  · rw [h0, norm_zero]; exact norm_nonneg _
  rw [← Finset.add_sum_erase s f hm]
  have hlt : ‖∑ j ∈ s.erase m, f j‖ < ‖f m‖ := by
    rcases (s.erase m).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact norm_pos_iff.2 h0
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      refine hle.trans_lt (lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj)) fun heq => ?_)
      by_cases hj0 : f j = 0
      · rw [hj0, norm_zero] at heq; exact h0 (norm_eq_zero.1 heq.symm)
      · exact (Finset.ne_of_mem_erase hj) (hf j (Finset.mem_of_mem_erase hj) m hm hj0 heq)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
  exact le_max_left _ _
end GroundTheory.PAdicHodge
