-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.balanced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:34.723531+00:00
-- url     : https://prove2.me/submissions/233c454b-a0a5-4773-9c93-25f4a7aecc49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable
import Theorems.Thm_GlobalTheory_FlowProgramme_cyclic_nonneg
import Theorems.Thm_GlobalTheory_FlowProgramme_cyclic_solvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hd : 2 ≤ d)
    (hX : ∀ a b, X a ≤ l * X b) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧
      ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨y, hy⟩ := cyclic_solvable l d X hl'
  have hpos := cyclic_nonneg l d X y hl' hX hy
  have h1 : 1 ∈ Finset.range d := Finset.mem_range.2 (by omega)
  refine ⟨fun a i => if i = 1 then y a else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a i
    dsimp only
    split_ifs
    · exact hpos a
    · exact le_rfl
  · intro a i h
    dsimp only at h
    split_ifs at h with hi
    · subst hi
      exact ⟨odd_one, by omega⟩
    · exact absurd rfl h
  · intro a
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', h1, if_true, pow_one, Nat.cast_one]
    exact (hy a).le
  · simp only [Finset.sum_ite_eq', h1, if_true]
    have : ∑ a, y (a - 1) = ∑ a, y a := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [← Finset.sum_congr rfl fun a _ => hy a, Finset.sum_add_distrib, this, ← Finset.mul_sum]
    ring
end GlobalTheory.FlowProgramme
