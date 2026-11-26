-- Prove2me | solution 1 for N4Code.hammingWeight_swapBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:45.197573+00:00
-- url     : https://prove2.me/submissions/d737c489-4bf2-487c-b798-c77048002582

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (t₁ t' : Fin n) (z : Word n) :
    hammingWeight (swapBits t₁ t' z) = hammingWeight z := by
  unfold hammingWeight
  have hfun : swapBits t₁ t' z = fun u : Fin n => z ((Equiv.swap t₁ t') u) := by
    funext u
    by_cases hut : u = t'
    · subst u
      by_cases ht₁ : t' = t₁
      · subst t₁
        simp [swapBits]
      · simp [swapBits, Equiv.swap_apply_right, ht₁]
    · by_cases hu₁ : u = t₁
      · subst u
        simp [swapBits, Equiv.swap_apply_left]
      · simp [swapBits, hu₁, hut, Equiv.swap_apply_of_ne_of_ne hu₁ hut]
  rw [hfun]
  apply Finset.sum_bij (fun u _ => (Equiv.swap t₁ t') u)
  · intro u _
    simp
  · intro a _ b _ hab
    exact (Equiv.swap t₁ t').injective hab
  · intro b _
    exact ⟨(Equiv.swap t₁ t').symm b, by simp, by simp⟩
  · intro u _
    simp
end N4Code
