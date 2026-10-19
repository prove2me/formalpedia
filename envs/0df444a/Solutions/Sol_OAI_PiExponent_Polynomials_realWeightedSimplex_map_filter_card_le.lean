-- Prove2me | solution 1 for OAI.PiExponent.Polynomials.realWeightedSimplex_map_filter_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:25:14.778997+00:00
-- url     : https://prove2.me/submissions/38b1e013-697d-4b13-8ba4-4645e7f52fc4

import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators
open OAI.PiExponent

theorem solution {m : ℕ} (w : Fin m → ℝ) (H T : ℝ)
    (hw : ∀ i, 0 < w i) :
    (((Finset.univ : Finset ((OAI.PiExponent.realWeightedSimplex w H).map
      Finsupp.equivFunOnFinite.symm.toEmbedding)).filter
      (fun a => ∑ i : Fin m, w i * (a.1 i : ℝ) ≤ T)).card : ℝ) ≤
        (OAI.PiExponent.realWeightedSimplex w T).card := by
  classical
  let s := (realWeightedSimplex w H).map
    Finsupp.equivFunOnFinite.symm.toEmbedding
  let domain : Finset s := Finset.univ.filter
    (fun a => ∑ i : Fin m, w i * (a.1 i : ℝ) ≤ T)

  have hmem (x : Fin m → ℕ)
      (hx : ∑ i : Fin m, w i * (x i : ℝ) ≤ T) :
      x ∈ realWeightedSimplex w T := by
    have hcoord (i : Fin m) : (x i : ℝ) ≤ T / w i := by
      have hterm : w i * (x i : ℝ) ≤
          ∑ j : Fin m, w j * (x j : ℝ) := by
        exact Finset.single_le_sum
          (s := Finset.univ) (f := fun j : Fin m => w j * (x j : ℝ))
          (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg (x j)))
          (Finset.mem_univ i)
      apply (le_div_iff₀ (hw i)).2
      simpa only [mul_comm] using hterm.trans hx
    rw [realWeightedSimplex]
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro i
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.le_floor (hcoord i))
    · exact hx

  let f : (↥domain) → ↥(realWeightedSimplex w T) := fun a =>
    ⟨a.1.1, hmem a.1.1 (Finset.mem_filter.mp a.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg (fun c : ↥(realWeightedSimplex w T) => c.1 i) hab
  have hcard : domain.card ≤ (realWeightedSimplex w T).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  change (domain.card : ℝ) ≤ (realWeightedSimplex w T).card
  exact_mod_cast hcard
