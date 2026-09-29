-- Prove2me | solution 1 for MarkovMixing.rayleigh_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T16:34:19.637652+00:00
-- url     : https://prove2.me/submissions/c150e7ed-4f29-4e8a-b9ee-22fa7d63c4ec

import Theorems.Thm_MarkovMixing_thomson_principle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c c' : V → V → ℝ) (hc : IsConductance c) (hc' : IsConductance c')
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hpos' : ∀ x : V, 0 < vertexConductance c' x)
    (hirr : MarkovMixing.Irreducible (networkWalk c))
    (hirr' : MarkovMixing.Irreducible (networkWalk c'))
    (hle : ∀ x y : V, c' x y ≤ c x y) (a z : V) (haz : a ≠ z) :
    effectiveResistance c a z ≤ effectiveResistance c' a z := by
  classical
  obtain ⟨-, θ, hflow', hstr, hE'⟩ :=
    MarkovMixing.thomson_principle c' hc' hpos' hirr' a z haz
  obtain ⟨hinf, -⟩ := MarkovMixing.thomson_principle c hc hpos hirr a z haz
  -- a flow for the smaller conductances is a flow for the larger ones
  have hflowc : IsFlow c θ a z :=
    ⟨hflow'.1,
     fun x y hxy => hflow'.2.1 x y (le_antisymm (by rw [← hxy]; exact hle x y) (hc'.1 x y)),
     hflow'.2.2⟩
  have hmem : flowEnergy c θ ∈ {r : ℝ | ∃ θ : V → V → ℝ,
      IsFlow c θ a z ∧ flowStrength θ a = 1 ∧ r = flowEnergy c θ} :=
    ⟨θ, hflowc, hstr, rfl⟩
  have hbdd : BddBelow {r : ℝ | ∃ θ : V → V → ℝ,
      IsFlow c θ a z ∧ flowStrength θ a = 1 ∧ r = flowEnergy c θ} := by
    refine ⟨0, ?_⟩
    rintro r ⟨σ, -, -, rfl⟩
    unfold flowEnergy
    have hnn : (0 : ℝ) ≤ ∑ x, ∑ y, σ x y ^ 2 / c x y :=
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
        div_nonneg (sq_nonneg _) (hc.1 x y)
    linarith
  have h1 : effectiveResistance c a z ≤ flowEnergy c θ := by
    rw [hinf]
    exact csInf_le hbdd hmem
  have h2 : flowEnergy c θ ≤ flowEnergy c' θ := by
    unfold flowEnergy
    have hsum : ∑ x, ∑ y, θ x y ^ 2 / c x y ≤ ∑ x, ∑ y, θ x y ^ 2 / c' x y := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      by_cases h : c' x y = 0
      · rw [h, hflow'.2.1 x y h]
        simp
      · have hc'pos : 0 < c' x y := lt_of_le_of_ne (hc'.1 x y) (Ne.symm h)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hc'pos (hle x y)
    linarith
  linarith [h1, h2, hE']
