-- Prove2me | solution 1 for GlobalTheory.JacobiClassSum.sum_zmod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:01:21.116322+00:00
-- url     : https://prove2.me/submissions/85e3837e-d924-4426-8401-2a32dc9d8ad3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsJacobiSymEqNegOne
import Theorems.Thm_GlobalTheory_JacobiClassSum_exists_jacobiSym_eq_neg_one
import Theorems.Thm_GlobalTheory_JacobiClassSum_jacobiSym_val_natCast

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
theorem _root_.solution {s : ℕ} [NeZero s] (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∑ x : ZMod s, jacobiSym ((x.val : ℕ) : ℤ) s = 0 := by
  obtain ⟨c, hc⟩ := exists_jacobiSym_eq_neg_one h1 hodd hsq
  have hcop : Nat.Coprime c s := by
    by_contra h
    have : jacobiSym (c : ℤ) s = 0 :=
      jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Int.gcd_natCast_natCast] using h)
    rw [this] at hc
    norm_num at hc
  have key : ∀ x : ZMod s, jacobiSym ((((c : ZMod s) * x).val : ℕ) : ℤ) s
      = - jacobiSym ((x.val : ℕ) : ℤ) s := by
    intro x
    have : (c : ZMod s) * x = ((c * x.val : ℕ) : ZMod s) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [this, jacobiSym_val_natCast, Nat.cast_mul, jacobiSym.mul_left, hc]
    ring
  have h := Equiv.sum_comp (Units.mulLeft (ZMod.unitOfCoprime c hcop))
    (fun x : ZMod s => jacobiSym ((x.val : ℕ) : ℤ) s)
  simp only [Units.mulLeft_apply, ZMod.coe_unitOfCoprime, key, Finset.sum_neg_distrib] at h
  linarith
end GlobalTheory.JacobiClassSum
