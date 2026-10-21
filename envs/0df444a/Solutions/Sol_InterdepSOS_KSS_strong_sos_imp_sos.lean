-- Prove2me | solution 1 for InterdepSOS.KSS.strong_sos_imp_sos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:59:09.845775+00:00
-- url     : https://prove2.me/submissions/aa36b82f-ba7b-49f8-9d79-88af7e6d52c6

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
set_option autoImplicit false
open InterdepSOS.KSS

theorem solution {n : ℕ} (k : ℕ) (w : InterdepSOS.KHL.Signal n → ℝ) (h : IsStrongSOS k w) :
    InterdepSOS.KHL.IsSOS k w := by
  intro j x δ s s' hs hs' hxδ hle
  have hxk : x < k := by omega
  have hgrid : ∀ t : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid k t →
      InterdepSOS.KHL.InGrid k (Function.update t j x) := by
    intro t ht i
    by_cases hi : i = j
    · subst hi; simpa using hxk
    · simpa [Function.update_of_ne hi] using ht i
  have hle' : Function.update s' j x ≤ Function.update s j x := by
    intro i
    by_cases hi : i = j
    · subst hi; simp
    · simpa [Function.update_of_ne hi] using hle i hi
  have := h j δ (Function.update s j x) (Function.update s' j x) (hgrid s hs) (hgrid s' hs') hle'
    (by simpa using hxδ)
  simpa using this
