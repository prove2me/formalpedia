-- Prove2me | solution 1 for GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:58.673602+00:00
-- url     : https://prove2.me/submissions/32f598c8-5749-4a68-9deb-ece39ab5eda0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe
import Theorems.Thm_GlobalTheory_BadShare_TwoRoots_card_le_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots
namespace GlobalTheory.BadShare.TwoRoots
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by
  intro g _ N d l hd hN hl hb
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have h1 := card_le_nat g d l hd hl
  have h2 : (l ^ padicValNat l (g ^ d - 1)) ^ 4 ≤ g ^ d := by
    by_contra hc
    exact hb (bb_iff.2 (Or.inr ⟨hl, d, by omega, hN, by rw [mul_comm, pow_mul]; omega⟩))
  have h3 : ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    rw [← Real.rpow_natCast ((g : ℝ) ^ ((d : ℝ) / 4)), ← Real.rpow_mul (by positivity)]
    have : (d : ℝ) / 4 * (4 : ℕ) = d := by push_cast; ring
    rw [this, Real.rpow_natCast]
    exact_mod_cast h2
  have h4 : ((g ^ (d / 2) : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by exact_mod_cast Nat.cast_div_le (α := ℝ) (m := d) (n := 2))
  calc _ ≤ ((l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (g : ℝ) ^ ((d : ℝ) / 4) * (g : ℝ) ^ ((d : ℝ) / 2) := by
      rw [Nat.cast_mul]; exact mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
end GlobalTheory.BadShare.TwoRoots
