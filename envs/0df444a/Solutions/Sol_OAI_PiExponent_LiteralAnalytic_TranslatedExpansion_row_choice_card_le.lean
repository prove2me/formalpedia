-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.row_choice_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:30:16.282804+00:00
-- url     : https://prove2.me/submissions/68da71d1-eb9c-46fb-8c0f-f6bb5c3c2af2

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

private theorem simplex_coordinate_bound {n : ℕ} (w : Fin n → ℝ) (H : ℝ)
    {a : Fin n → ℕ} (ha : a ∈ realWeightedSimplex w H) (i : Fin n) :
    a i ≤ ⌊H / w i⌋₊ := by
  classical
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at ha
  exact Nat.le_of_lt_succ (ha.1 i)

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) (r : Row d H) :
    Fintype.card (RowChoice d H r) ≤ translationTermCount d.m d.v0 H := by
  classical
  let w : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteDenominators d)
  have hw (i : Fin d.m) : 1 ≤ w i := by
    change (1 : ℝ) ≤ (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log i.val]
    exact d.x_one_le (i.val + 1)
  have hb (a : Fin d.m → ℕ) (ha : a ∈ realWeightedSimplex w H)
      (i : Fin d.m) : a i ≤ ⌊H⌋₊ :=
    (simplex_coordinate_bound w H ha i).trans
      (Nat.floor_le_floor (div_le_self hH.le (hw i)))
  have hindices : Fintype.card (indices d H) ≤ (⌊H⌋₊ + 1) ^ d.m := by
    rw [Fintype.card_coe, indices, Finset.card_map]
    change (realWeightedSimplex w H).card ≤ (⌊H⌋₊ + 1) ^ d.m
    calc
      (realWeightedSimplex w H).card ≤
          (Fintype.piFinset (fun _ : Fin d.m => Finset.range (⌊H⌋₊ + 1))).card := by
        apply Finset.card_le_card
        intro a ha
        apply Fintype.mem_piFinset.mpr
        intro i
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hb a ha i))
      _ = (⌊H⌋₊ + 1) ^ d.m := by simp
  have ha_bound (a : indices d H) (i : Fin d.m) : a.1 i ≤ ⌊H⌋₊ := by
    have ha : a.1 ∈ (realWeightedSimplex w H).map
        Finsupp.equivFunOnFinite.symm.toEmbedding := a.property
    rcases Finset.mem_map.mp ha with ⟨b, hbmem, heq⟩
    have hi : b i = a.1 i := congrArg (fun z : Fin d.m →₀ ℕ => z i) heq
    rw [← hi]
    exact hb b hbmem i
  have hr : r.2.1 0 ≤ ⌊H / d.v0⌋₊ := by
    have hmem : r.2.1 ∈ strictWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H := r.2.property
    have hreal : r.2.1 ∈ realWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H :=
      (Finset.mem_filter.mp hmem).1
    simpa [InterpolationMatrix.rowWeights] using
      simplex_coordinate_bound
        (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H hreal 0
  have hfiber (a : indices d H) :
      Fintype.card ((∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
        Fin (r.2.1 0 + 1)) ≤
      (⌊H⌋₊ + 1) ^ d.m * (⌊H / d.v0⌋₊ + 1) := by
    simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
    refine Nat.mul_le_mul ?_ (Nat.add_le_add_right hr 1)
    calc
      (∏ i : Fin d.m, (a.1 i - r.2.1 i.succ + 1)) ≤
          ∏ _i : Fin d.m, (⌊H⌋₊ + 1) := by
        apply Finset.prod_le_prod'
        intro i _
        exact Nat.add_le_add_right
          ((Nat.sub_le (a.1 i) (r.2.1 i.succ)).trans (ha_bound a i)) 1
      _ = (⌊H⌋₊ + 1) ^ d.m := by simp
  change Fintype.card (Σ a : indices d H,
      (∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
        Fin (r.2.1 0 + 1)) ≤ _
  rw [Fintype.card_sigma]
  calc
    (∑ a : indices d H,
        Fintype.card ((∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
          Fin (r.2.1 0 + 1))) ≤
        ∑ _a : indices d H, (⌊H⌋₊ + 1) ^ d.m * (⌊H / d.v0⌋₊ + 1) :=
      Finset.sum_le_sum (fun a _ => hfiber a)
    _ = Fintype.card (indices d H) *
        ((⌊H⌋₊ + 1) ^ d.m * (⌊H / d.v0⌋₊ + 1)) := by simp
    _ ≤ (⌊H⌋₊ + 1) ^ d.m *
        ((⌊H⌋₊ + 1) ^ d.m * (⌊H / d.v0⌋₊ + 1)) :=
      Nat.mul_le_mul_right _ hindices
    _ = translationTermCount d.m d.v0 H := by
      simp only [translationTermCount, two_mul, pow_add, Nat.mul_assoc]
