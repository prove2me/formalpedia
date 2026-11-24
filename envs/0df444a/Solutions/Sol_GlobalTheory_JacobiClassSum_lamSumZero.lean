-- Prove2me | solution 1 for GlobalTheory.JacobiClassSum.lamSumZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:07.746252+00:00
-- url     : https://prove2.me/submissions/d6004490-b9f8-4d52-ba86-3b2aa7023ab7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsJacobiSymEqNegOne
import Theorems.Thm_GlobalTheory_JacobiClassSum_jacobiSym_val_natCast
import Theorems.Thm_GlobalTheory_JacobiClassSum_sum_zmod_eq_zero

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
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.LamSumZero := by
  intro m₀ s a₀ hm h1 hodd hsq hcop
  haveI : NeZero s := ⟨by omega⟩
  rw [← sum_zmod_eq_zero h1 hodd hsq]
  refine Finset.sum_bij (fun b _ => (b : ZMod s)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro b hb b' hb' h
    simp only [Finset.mem_filter, Finset.mem_range] at hb hb'
    have h2 : b ≡ b' [MOD s] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    have h3 : b ≡ b' [MOD m₀] := hb.2.trans hb'.2.symm
    have h4 : b ≡ b' [MOD m₀ * s] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨h3, h2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h4 hb.1 hb'.1
  · intro x _
    have hlt := Nat.chineseRemainder_lt_mul hcop.symm a₀ x.val hm.ne' (NeZero.ne s)
    have hpr := (Nat.chineseRemainder hcop.symm a₀ x.val).2
    refine ⟨(Nat.chineseRemainder hcop.symm a₀ x.val : ℕ), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, hpr.1⟩
    · show ((Nat.chineseRemainder hcop.symm a₀ x.val : ℕ) : ZMod s) = x
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hpr.2, ZMod.natCast_zmod_val]
  · intro b _
    exact (jacobiSym_val_natCast b).symm
end GlobalTheory.JacobiClassSum
