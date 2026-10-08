-- Prove2me | solution 1 for OAI.PiExponent.finite_rat_den_le_abs_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:01:01.18431+00:00
-- url     : https://prove2.me/submissions/95d4a1e2-60f7-472b-8f94-bc49712a2040

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions


namespace OAI

namespace PiExponent

 













end PiExponent

end OAI

open OAI.PiExponent in
theorem solution (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1}.Finite := by
  classical
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hp.1, hp.2]
  let t : Set (ℤ × ℕ) := ⋃ (q : ℕ) (_ : q ∈ Set.Icc 1 N),
    Set.Icc ⌈(x - 1) * q⌉ ⌊(x + 1) * q⌋ ×ˢ {q}
  have ht : t.Finite :=
    Set.Finite.biUnion (Set.finite_Icc _ _) fun q _ =>
      Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_singleton _)
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1} ⊆ t := by
    rintro _ ⟨r, ⟨hrN, hr⟩, rfl⟩
    have hrden : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
    have hrlow : x - 1 < (r : ℝ) := by linarith [(abs_lt.mp hr).2]
    have hrhigh : (r : ℝ) < x + 1 := by linarith [(abs_lt.mp hr).1]
    have hnlow : (x - 1) * r.den ≤ (r.num : ℝ) := by
      rw [Rat.cast_def] at hrlow
      exact ((lt_div_iff₀ hrden).mp hrlow).le
    have hnhigh : (r.num : ℝ) ≤ (x + 1) * r.den := by
      rw [Rat.cast_def] at hrhigh
      exact ((div_lt_iff₀ hrden).mp hrhigh).le
    simp only [t, Set.mem_iUnion]
    refine ⟨r.den, ⟨r.pos, hrN⟩, ?_⟩
    exact ⟨⟨Int.ceil_le.mpr hnlow, Int.le_floor.mpr hnhigh⟩, rfl⟩
  exact (ht.subset hsub).of_finite_image hinj.injOn
