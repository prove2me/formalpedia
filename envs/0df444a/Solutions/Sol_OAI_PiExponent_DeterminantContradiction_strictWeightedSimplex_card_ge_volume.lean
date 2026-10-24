-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:12:04.713717+00:00
-- url     : https://prove2.me/submissions/e1a1527a-d1f8-4d60-8835-be0bd645af5a

import Mathlib
import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open OAI.PiExponent
open scoped BigOperators

namespace PXUB

lemma box_eq {m : ℕ} (a : Fin m → ℕ) :
    {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}
      = Set.univ.pi (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)) := by
  ext x; simp [Set.mem_pi]

lemma box_vol {m : ℕ} (a : Fin m → ℕ) :
    MeasureTheory.volume {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1} = 1 := by
  rw [box_eq, Real.volume_pi_Ico]
  simp

lemma box_meas {m : ℕ} (a : Fin m → ℕ) :
    MeasurableSet {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1} := by
  rw [box_eq]; exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)

lemma box_disj {m : ℕ} (s : Finset (Fin m → ℕ)) :
    (s : Set (Fin m → ℕ)).PairwiseDisjoint
      (fun a => {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) := by
  intro a _ b _ hab
  rw [Function.onFun, Set.disjoint_left]
  intro x hxa hxb
  apply hab
  funext i
  have h1 := hxa i; have h2 := hxb i

  have : (a i : ℝ) < b i + 1 := by linarith [h1.1, h2.2]
  have : (b i : ℝ) < a i + 1 := by linarith [h2.1, h1.2]
  have e1 : a i < b i + 1 := by exact_mod_cast ‹(a i : ℝ) < b i + 1›
  have e2 : b i < a i + 1 := by exact_mod_cast ‹(b i : ℝ) < a i + 1›
  omega

lemma union_vol {m : ℕ} (s : Finset (Fin m → ℕ)) :
    MeasureTheory.volume
      (⋃ a ∈ s, {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) = s.card := by
  rw [MeasureTheory.measure_biUnion_finset (box_disj s) (fun a _ => box_meas a)]
  simp [box_vol]

end PXUB

open OAI.PiExponent.DeterminantContradiction in
theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T}
      ≤ (strictWeightedSimplex w T).card := by
  classical
  rw [← PXUB.union_vol]
  apply MeasureTheory.measure_mono
  rintro x ⟨h0, hs⟩
  set a : Fin n → ℕ := fun i => ⌊x i⌋₊ with ha
  have hax : ∀ i, (a i : ℝ) ≤ x i := fun i => Nat.floor_le (h0 i)
  have hsa : ∑ i, w i * (a i : ℝ) ≤ ∑ i, w i * x i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hax i) (hw i).le)
  have hmem : a ∈ strictWeightedSimplex w T := by
    unfold strictWeightedSimplex realWeightedSimplex
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨⟨fun i => ?_, by linarith⟩, by linarith⟩
    have hle : w i * x i ≤ ∑ j, w j * x j :=
      Finset.single_le_sum (f := fun j => w j * x j) (fun j _ => mul_nonneg (hw j).le (h0 j))
        (Finset.mem_univ i)
    have hxi : x i ≤ T / w i := by
      rw [le_div_iff₀ (hw i)]; linarith
    have : a i ≤ ⌊T / w i⌋₊ := Nat.floor_le_floor hxi
    omega
  simp only [Set.mem_iUnion]
  exact ⟨a, hmem, fun i => ⟨hax i, Nat.lt_floor_add_one (x i)⟩⟩
