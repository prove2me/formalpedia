-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedStrictSimplex_box_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:50:47.340409+00:00
-- url     : https://prove2.me/submissions/72da55a5-d217-4036-984e-03325b8d4cdc

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators

/-- The number of lattice points of the strict weighted simplex is bounded by the number of
points of a coordinate box, whose side lengths are given by the ceilings of `H / w i`. -/
theorem solution {m : ℕ} (w : Fin (m + 1) → ℝ)
    (hw : ∀ i, 0 < w i) (H : ℝ) :
    (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) ≤
      ∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ) := by
  classical
  have hcard : (Fintype.card {a // a ∈ OAI.PiExponent.strictWeightedSimplex w H} : ℝ) =
      ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) := by
    simp
  rw [hcard]
  have hsub : OAI.PiExponent.strictWeightedSimplex w H ⊆
      Fintype.piFinset (fun i : Fin (m + 1) => Finset.range (⌈H / w i⌉₊ + 1)) := by
    intro a ha
    simp only [OAI.PiExponent.strictWeightedSimplex, OAI.PiExponent.realWeightedSimplex,
      Finset.mem_filter] at ha
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hsum : ∑ j, w j * (a j : ℝ) < H := ha.2
    have hterm : w i * (a i : ℝ) ≤ ∑ j, w j * (a j : ℝ) :=
      Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
        (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    have hlt : (a i : ℝ) < H / w i := by
      rw [lt_div_iff₀ (hw i)]
      calc (a i : ℝ) * w i = w i * (a i : ℝ) := by ring
        _ ≤ ∑ j, w j * (a j : ℝ) := hterm
        _ < H := hsum
    have hle : a i ≤ ⌈H / w i⌉₊ := by
      exact_mod_cast hlt.le.trans (Nat.le_ceil (H / w i))
    exact Nat.lt_succ_of_le hle
  have hcardle : (OAI.PiExponent.strictWeightedSimplex w H).card ≤
      (Fintype.piFinset (fun i : Fin (m + 1) =>
        Finset.range (⌈H / w i⌉₊ + 1))).card :=
    Finset.card_le_card hsub
  have hprod : (Fintype.piFinset (fun i : Fin (m + 1) =>
        Finset.range (⌈H / w i⌉₊ + 1))).card =
      ∏ i : Fin (m + 1), (⌈H / w i⌉₊ + 1) := by
    rw [Fintype.card_piFinset]
    simp
  calc ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ)
      ≤ ((Fintype.piFinset (fun i : Fin (m + 1) =>
          Finset.range (⌈H / w i⌉₊ + 1))).card : ℝ) := by exact_mod_cast hcardle
    _ = ∏ i : Fin (m + 1), ((⌈H / w i⌉₊ + 1 : ℕ) : ℝ) := by
        rw [hprod]
        push_cast
        rfl
