-- Prove2me | solution 1 for GlobalTheory.JacobiClassSum.exists_jacobiSym_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:09.532327+00:00
-- url     : https://prove2.me/submissions/c19aca4a-c5d3-4cde-85f7-9ac3837e0ad0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsJacobiSymEqNegOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.JacobiClassSum
namespace GlobalTheory.JacobiClassSum
theorem _root_.solution {s : ℕ} (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∃ c : ℕ, jacobiSym (c : ℤ) s = -1 := by
  obtain ⟨p, hp, t, rfl⟩ := Nat.exists_prime_and_dvd (ne_of_gt h1)
  have hcop : Nat.Coprime p t := Nat.coprime_of_squarefree_mul hsq
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_odd_iff_even.mpr (even_two_mul t)) hodd
  have ht : t ≠ 0 := by
    rintro rfl
    simp at h1
  haveI : NeZero t := ⟨ht⟩
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop n.val 1
  refine ⟨c, ?_⟩
  have e1 : jacobiSym (c : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : (((c : ℤ) : ZMod p)) = n := by
      rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc1, ZMod.natCast_zmod_val]
    rwa [this]
  have e2 : jacobiSym (c : ℤ) t = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast (Int.natCast_modEq_iff.mpr hc2)),
      jacobiSym.one_left]
  rw [jacobiSym.mul_right, e1, e2]
  norm_num
end GlobalTheory.JacobiClassSum
