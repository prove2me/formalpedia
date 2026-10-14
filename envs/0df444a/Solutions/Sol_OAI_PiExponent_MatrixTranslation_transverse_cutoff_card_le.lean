-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslation.transverse_cutoff_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T10:14:59.68918+00:00
-- url     : https://prove2.me/submissions/33bfa9f1-3170-496c-a039-c5ce66b1fba9

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators

theorem solution {m : ℕ}
    (w : Fin m → ℝ) (H B : ℝ) (hw : ∀ i, 0 < w i) :
    ((Finset.univ : Finset (↥(OAI.PiExponent.MatrixTranslation.transverseIndices w H))).filter
      (fun a => ∑ i, w i * (a.1 i : ℝ) ≤ B)).card ≤
      (OAI.PiExponent.realWeightedSimplex w B).card := by
  classical
  let T := OAI.PiExponent.MatrixTranslation.transverseIndices w H
  let S := OAI.PiExponent.realWeightedSimplex w B
  let f : {a : ↥T // ∑ i, w i * (a.1 i : ℝ) ≤ B} → ↥S := fun a =>
    ⟨(Finsupp.equivFunOnFinite a.1.1 : Fin m → ℕ), by
      let x : Fin m → ℕ := Finsupp.equivFunOnFinite a.1.1
      have hsum : ∑ i, w i * (x i : ℝ) ≤ B := by
        simpa [x] using a.2
      change x ∈ OAI.PiExponent.realWeightedSimplex w B
      simp only [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter,
        Fintype.mem_piFinset, Finset.mem_range]
      constructor
      · intro i
        have hterm : w i * (x i : ℝ) ≤ B := by
          have hnonneg : ∀ j, 0 ≤ w j * (x j : ℝ) := by
            intro j
            exact mul_nonneg (le_of_lt (hw j)) (Nat.cast_nonneg _)
          calc
            w i * (x i : ℝ) ≤ ∑ j, w j * (x j : ℝ) := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
            _ ≤ B := hsum
        have hdiv : (x i : ℝ) ≤ B / w i := (le_div_iff₀ (hw i)).2 (by nlinarith)
        have hn : x i ≤ Nat.floor (B / w i) := Nat.le_floor hdiv
        omega
      · exact hsum⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.injective (congrArg Subtype.val h)
  have hcard : Fintype.card {a : ↥T // ∑ i, w i * (a.1 i : ℝ) ≤ B} ≤ Fintype.card ↥S :=
    Fintype.card_le_of_injective f hf
  have hEq : Fintype.card {a : ↥T // ∑ i, w i * (a.1 i : ℝ) ≤ B} =
      ((Finset.univ : Finset ↥T).filter (fun a => ∑ i, w i * (a.1 i : ℝ) ≤ B)).card := by
    apply Fintype.card_of_subtype
    intro a
    simp
  rw [hEq] at hcard
  simpa [T, S] using hcard
