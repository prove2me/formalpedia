-- Prove2me | solution 1 for NatureSLT.Consistency.key_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:04:51.99603+00:00
-- url     : https://prove2.me/submissions/80969ec6-6460-49f3-bea7-60a9ef62ab17

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk
import Definitions.Def_NatureSLT_Consistency_nontriviallyConsistent
import Definitions.Def_NatureSLT_Consistency_uniformConvergence
import Theorems.Thm_NatureSLT_Consistency_finite_class_lln

open MeasureTheory Filter Topology NatureSLT.Consistency

lemma keyT_bdd {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) (Q : Λ → Z → ℝ) (c : ℝ) :
    BddBelow (Set.range fun α : levelSet F Q c => risk F Q α) := by
  refine ⟨c, ?_⟩
  rintro _ ⟨α, rfl⟩
  exact le_of_lt α.2

lemma keyT_le_risk {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) (Q : Λ → Z → ℝ) (c : ℝ)
    (α : Λ) (hα : α ∈ levelSet F Q c) : infRiskLevel F Q c ≤ risk F Q α :=
  ciInf_le (keyT_bdd F Q c) ⟨α, hα⟩

lemma keyT_c_le {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) (Q : Λ → Z → ℝ) (c : ℝ)
    (hne : (levelSet F Q c).Nonempty) : c ≤ infRiskLevel F Q c := by
  haveI : Nonempty (levelSet F Q c) := hne.to_subtype
  exact le_ciInf fun α => le_of_lt α.2

lemma keyT_backward {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hint : ∀ α, Integrable (Q α) F)
    (hU : UniformOneSidedConvergence F Q) : NontriviallyConsistent F Q := by
  intro c hne ε hε
  set I := infRiskLevel F Q c with hI
  haveI : Nonempty (levelSet F Q c) := hne.to_subtype
  obtain ⟨αs, hαs⟩ : ∃ α : levelSet F Q c, risk F Q α < I + ε / 2 :=
    exists_lt_of_ciInf_lt (by rw [hI] at *; unfold infRiskLevel; linarith)
  have hL := finite_class_lln F (fun (_ : Unit) => Q αs) (Set.finite_range _)
    (fun _ => hint αs) (ε / 2) (by linarith)
  have hA := hU ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hA.add hL) (fun ℓ => zero_le') (fun ℓ => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  rcases hz with h | h
  · left
    simp only [Set.mem_ofPred_eq]
    unfold infEmpiricalRisk at h
    obtain ⟨α, h⟩ := iInf_lt_iff.1 h
    obtain ⟨hα, h⟩ := iInf_lt_iff.1 h
    have h' := EReal.coe_lt_coe_iff.1 h
    have := keyT_le_risk F Q c α hα
    unfold supOneSidedDeviation
    refine lt_of_lt_of_le ?_ (le_iSup _ α)
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  · right
    simp only [Set.mem_ofPred_eq]
    have hle : infEmpiricalRisk Q (levelSet F Q c) z ≤ ((empiricalRisk Q z αs : ℝ) : EReal) := by
      unfold infEmpiricalRisk
      exact iInf₂_le (αs : Λ) αs.2
    have h' := EReal.coe_lt_coe_iff.1 (lt_of_lt_of_le h hle)
    unfold supTwoSidedDeviation
    refine lt_of_lt_of_le ?_ (le_iSup _ ())
    refine EReal.coe_lt_coe_iff.2 ?_
    unfold risk empiricalRisk at *
    rw [abs_sub_comm]
    refine lt_of_lt_of_le ?_ (le_abs_self _)
    linarith

lemma keyT_forward {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (A B : ℝ) (hAB : ∀ α, A ≤ risk F Q α ∧ risk F Q α ≤ B)
    (hC : NontriviallyConsistent F Q) : UniformOneSidedConvergence F Q := by
  intro ε hε
  set s := ε / 4 with hs
  have hs0 : 0 < s := by positivity
  let c : ℕ → ℝ := fun j => A + ((j : ℝ) - 1) * s
  let N := ⌊(B - A) / s⌋₊ + 1
  classical
  let E : (j : ℕ) → (ℓ : ℕ) → Set (Fin ℓ → Z) := fun j ℓ =>
    if (levelSet F Q (c j)).Nonempty then
      {z : Fin ℓ → Z | infEmpiricalRisk Q (levelSet F Q (c j)) z
            < ((infRiskLevel F Q (c j) - ε / 2 : ℝ) : EReal) ∨
          ((infRiskLevel F Q (c j) + ε / 2 : ℝ) : EReal) <
            infEmpiricalRisk Q (levelSet F Q (c j)) z}
    else ∅
  have hE : ∀ j, Tendsto (fun ℓ : ℕ => Measure.pi (fun _ : Fin ℓ => F) (E j ℓ)) atTop (𝓝 0) := by
    intro j
    by_cases hj : (levelSet F Q (c j)).Nonempty
    · simpa [E, hj] using hC (c j) hj (ε / 2) (by linarith)
    · simp [E, hj]
  have hsum := tendsto_finset_sum (Finset.range N) fun j _ => hE j
  simp only [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun ℓ => zero_le') (fun ℓ => ?_)
  refine (measure_mono ?_).trans (measure_biUnion_finset_le (Finset.range N) _)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  unfold supOneSidedDeviation at hz
  obtain ⟨α, hα⟩ := lt_iSup_iff.1 hz
  have hα' := EReal.coe_lt_coe_iff.1 hα
  obtain ⟨hA, hB⟩ := hAB α
  set j := ⌊(risk F Q α - A) / s⌋₊ with hj
  have hx0 : 0 ≤ (risk F Q α - A) / s := div_nonneg (by linarith) hs0.le
  have hfl := Nat.floor_le hx0
  have hlt := Nat.lt_floor_add_one ((risk F Q α - A) / s)
  rw [← hj] at hfl hlt
  have h1 : (j : ℝ) * s ≤ risk F Q α - A := by rwa [le_div_iff₀ hs0] at hfl
  have h2 : risk F Q α - A < ((j : ℝ) + 1) * s := by rwa [div_lt_iff₀ hs0] at hlt
  have hmem : α ∈ levelSet F Q (c j) := by
    show c j < risk F Q α
    simp only [c]; nlinarith
  have hjN : j ∈ Finset.range N := by
    rw [Finset.mem_range]
    have : j ≤ ⌊(B - A) / s⌋₊ :=
      Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs0.le)
    omega
  simp only [Set.mem_iUnion]
  refine ⟨j, hjN, ?_⟩
  have hne : (levelSet F Q (c j)).Nonempty := ⟨α, hmem⟩
  simp only [E, if_pos hne, Set.mem_ofPred_eq]
  left
  have hcI := keyT_c_le F Q (c j) hne
  have hle : infEmpiricalRisk Q (levelSet F Q (c j)) z ≤ ((empiricalRisk Q z α : ℝ) : EReal) := by
    unfold infEmpiricalRisk
    exact iInf₂_le α hmem
  refine lt_of_le_of_lt hle (EReal.coe_lt_coe_iff.2 ?_)
  have : risk F Q α - c j < ε / 2 := by simp only [c]; nlinarith
  linarith

theorem solution {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hint : ∀ α, Integrable (Q α) F) (A B : ℝ)
    (hAB : ∀ α, A ≤ risk F Q α ∧ risk F Q α ≤ B)
    (hsup : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => supOneSidedDeviation F Q z))
    (hinf : ∀ (c : ℝ) (ℓ : ℕ),
      Measurable (fun z : Fin ℓ → Z => infEmpiricalRisk Q (levelSet F Q c) z)) :
    NontriviallyConsistent F Q ↔ UniformOneSidedConvergence F Q :=
  ⟨keyT_forward F Q A B hAB, keyT_backward F Q hint⟩
