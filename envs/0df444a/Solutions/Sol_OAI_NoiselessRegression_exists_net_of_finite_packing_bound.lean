-- Prove2me | solution 1 for OAI.NoiselessRegression.exists_net_of_finite_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:17:15.792077+00:00
-- url     : https://prove2.me/submissions/a2d18f9b-32bc-4cd1-b4a7-aa62486a3fc9

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {E : Type*} [PseudoMetricSpace E]
theorem solution (A : Set E) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hcard : ∀ s : Finset E, (∀ x ∈ s, x ∈ A) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) ∧
      ∀ x ∈ A, ∃ y ∈ s, dist x y ≤ r := by
  classical
  let Sep : Finset E → Prop := fun s => (∀ x ∈ s, x ∈ A) ∧ (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y)
  let P : ℕ → Prop := fun n => ∃ s : Finset E, Sep s ∧ s.card = n
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  have hn0 : P (Nat.findGreatest P N) := Nat.findGreatest_spec (P := P) (Nat.zero_le N) hP0
  obtain ⟨s, ⟨hsA, hsep⟩, hcs⟩ := hn0
  refine ⟨s, hsA, hsep, ?_⟩
  intro x hx
  by_contra hcon
  push_neg at hcon
  have hxs : x ∉ s := by
    intro hxs; have := hcon x hxs; rw [dist_self] at this; linarith
  have hsep' : Sep (insert x s) := by
    refine ⟨?_, ?_⟩
    · intro z hz; rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx
      · exact hsA z hz
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with ha' | ha'
      · rcases Finset.mem_insert.1 hb with hb' | hb'
        · exact absurd (ha'.trans hb'.symm) hab
        · rw [ha']; exact hcon b hb'
      · rcases Finset.mem_insert.1 hb with hb' | hb'
        · rw [hb', dist_comm]; exact hcon a ha'
        · exact hsep a ha' b hb' hab
  have hc : (insert x s).card = Nat.findGreatest P N + 1 := by
    rw [Finset.card_insert_of_notMem hxs, hcs]
  have hle : (insert x s).card ≤ N := hcard _ hsep'.1 hsep'.2
  have := Nat.le_findGreatest (P := P) hle ⟨insert x s, hsep', rfl⟩
  omega
