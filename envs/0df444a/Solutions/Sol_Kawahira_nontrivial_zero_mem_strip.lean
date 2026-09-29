-- Prove2me | solution 1 for Kawahira.nontrivial_zero_mem_strip
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:31:35.402775+00:00
-- url     : https://prove2.me/submissions/3ff048d9-1869-45fd-925d-f1750cd66e95

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_riemannZeta_neg_odd_ne_zero

open Complex Topology

theorem solution (s : ℂ) (hz : riemannZeta s = 0)
    (htrivial : ∀ n : ℕ, s ≠ -2 * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hpos
    have hre : s.re ≤ 0 := le_of_not_gt hpos
    by_cases hnat : ∀ n : ℕ, s ≠ -(n : ℂ)
    · have hs1 : s ≠ 1 := by
        intro hs
        subst s
        norm_num at hre
      have hfe := riemannZeta_one_sub hnat hs1
      have hzero : riemannZeta (1 - s) = 0 := by
        rw [hfe, hz, mul_zero]
      exact riemannZeta_ne_zero_of_one_le_re (s := 1 - s) (by
        simp only [sub_re, one_re]
        linarith) hzero
    · push_neg at hnat
      obtain ⟨n, hn⟩ := hnat
      rcases Nat.even_or_odd n with heven | hodd
      · obtain ⟨k, rfl⟩ := heven
        rcases k.eq_zero_or_pos with rfl | hk
        · have : s = 0 := by simpa using hn
          subst s
          simpa [riemannZeta_zero] using hz
        · apply htrivial (k - 1)
          rw [hn]
          have hkcast : ((k - 1 : ℕ) : ℂ) + 1 = (k : ℂ) := by
            exact_mod_cast Nat.sub_add_cancel hk
          rw [hkcast]
          push_cast
          ring
      · exact (riemannZeta_neg_odd_ne_zero n hodd) (by simpa [hn] using hz)
  · exact lt_of_not_ge fun hge => riemannZeta_ne_zero_of_one_le_re hge hz
