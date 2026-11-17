-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_prefix_surjective__p2m_8e730630_f726_4c62_b7a1_a47217416d93_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:55:42.317171+00:00
-- url     : https://prove2.me/submissions/46fb4a72-859e-42b2-aa46-041cbd06c022

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_labelF_block_cover__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
import Theorems.Thm_KnodelPrimeCordial_labelF_range_blocks__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1

theorem solution (q y : ℕ) (hy : y ∈ Set.Icc 1 (12 * q)) :
    ∃ i : ℕ, i < 12 * q ∧ KnodelPrimeCordial.labelF i = y := by
  obtain ⟨k, t, hk, ht, hyt⟩ :=
    KnodelPrimeCordial.labelF_range_blocks__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
      q y hy
  obtain ⟨r, hr, hlabel⟩ :=
    KnodelPrimeCordial.labelF_block_cover__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
      k t ht
  refine ⟨12 * k + r, ?_, ?_⟩
  · omega
  · rw [hlabel]
    omega
