-- Prove2me | solution 1 for GlobalTheory.shiftDiffPoly_coeff_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:46.539934+00:00
-- url     : https://prove2.me/submissions/f726ce63-787e-4ef3-97fb-a60100852940

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
import Theorems.Thm_GlobalTheory_shiftDiffPoly_coeff_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    (f.comp (X + 1) - f).coeff n = 0 := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have : b < n := by simp at hb; omega
    simp [Nat.choose_eq_zero_of_lt this]
  · intro hn'
    have : f.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by simp at hn'; omega)
    simp [this]
end GlobalTheory
