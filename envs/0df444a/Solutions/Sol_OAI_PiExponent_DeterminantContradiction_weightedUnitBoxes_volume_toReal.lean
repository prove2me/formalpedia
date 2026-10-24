-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedUnitBoxes_volume_toReal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:09:21.232537+00:00
-- url     : https://prove2.me/submissions/5ac16f02-feae-4de9-b530-25565600336f

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

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

theorem solution {m : Nat} (w : Fin m → Real) (B : Real) :
    (MeasureTheory.volume
      (⋃ a ∈ OAI.PiExponent.realWeightedSimplex w B,
        {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1})).toReal =
      ((OAI.PiExponent.realWeightedSimplex w B).card : Real) := by
  rw [PXUB.union_vol]; simp
