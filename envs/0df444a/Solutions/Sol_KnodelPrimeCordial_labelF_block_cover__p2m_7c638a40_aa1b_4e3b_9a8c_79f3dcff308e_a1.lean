-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_block_cover__p2m_7c638a40_aa1b_4e3b_9a8c_79f3dcff308e_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:14:47.298838+00:00
-- url     : https://prove2.me/submissions/e64f2b92-b807-4bfa-9457-b4117ea75c88

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution (k t : ℕ) (ht : t ∈ Set.Icc 1 12) :
    ∃ r : ℕ, r < 12 ∧ KnodelPrimeCordial.labelF (12 * k + r) = 12 * k + t := by
  change 1 ≤ t ∧ t ≤ 12 at ht
  have htlo : 1 ≤ t := ht.1
  have hthi : t ≤ 12 := ht.2
  interval_cases t
  · refine ⟨3, by omega, ?_⟩
    have hm : (12 * k + 3) % 12 = 3 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨0, by omega, ?_⟩
    have hm : (12 * k + 0) % 12 = 0 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨4, by omega, ?_⟩
    have hm : (12 * k + 4) % 12 = 4 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨1, by omega, ?_⟩
    have hm : (12 * k + 1) % 12 = 1 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨2, by omega, ?_⟩
    have hm : (12 * k + 2) % 12 = 2 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨5, by omega, ?_⟩
    have hm : (12 * k + 5) % 12 = 5 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨8, by omega, ?_⟩
    have hm : (12 * k + 8) % 12 = 8 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨6, by omega, ?_⟩
    have hm : (12 * k + 6) % 12 = 6 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨9, by omega, ?_⟩
    have hm : (12 * k + 9) % 12 = 9 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨11, by omega, ?_⟩
    have hm : (12 * k + 11) % 12 = 11 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨7, by omega, ?_⟩
    have hm : (12 * k + 7) % 12 = 7 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
  · refine ⟨10, by omega, ?_⟩
    have hm : (12 * k + 10) % 12 = 10 := by omega
    simp [KnodelPrimeCordial.labelF, hm]
