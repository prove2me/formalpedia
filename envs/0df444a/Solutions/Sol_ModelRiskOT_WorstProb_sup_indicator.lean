-- Prove2me | solution 1 for ModelRiskOT.WorstProb.sup_indicator
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:10:34.802984+00:00
-- url     : https://prove2.me/submissions/b9a748f5-938e-4ee4-9b4c-d87edcfc4a0b

import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb
set_option autoImplicit false
open MeasureTheory
namespace WorstProbCodex
open ModelRiskOT.WorstProb ModelRiskOT.Duality

lemma costToSet_nonneg {S : Type*} (c : S → S → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (A : Set S) (hA : A.Nonempty) (x : S) : 0 ≤ costToSet c A x := by
  let : Nonempty A := hA.to_subtype
  exact le_ciInf fun y ↦ hc x y

lemma costToSet_le {S : Type*} (c : S → S → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (A : Set S) (x : S) (y : A) : costToSet c A x ≤ c x y := by
  exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact hc x z⟩ y

noncomputable def eventPayoff {S : Type*} (A : Set S) (y : S) : ℝ :=
  A.indicator (fun _ ↦ 1) y

lemma eventPayoff_bounds {S : Type*} (A : Set S) (y : S) :
    0 ≤ eventPayoff A y ∧ eventPayoff A y ≤ 1 := by
  classical
  by_cases h : y ∈ A <;> simp [eventPayoff, h]

lemma event_score_upper {S : Type*} (c : S → S → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (A : Set S) (lam : ℝ) (hlam : 0 ≤ lam) (x y : S) :
    eventPayoff A y - lam * c x y ≤ max 0 (1 - lam * costToSet c A x) := by
  classical
  by_cases h : y ∈ A
  · have hi := costToSet_le c hc A x ⟨y,h⟩
    simp only [eventPayoff, Set.indicator_of_mem h]
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hi hlam) 1).trans (le_max_right _ _)
  · simp only [eventPayoff, Set.indicator_of_notMem h]
    exact (by nlinarith [hc x y] : 0 - lam * c x y ≤ 0).trans (le_max_left _ _)

lemma event_envelope_le_of_upper {S : Type*} (c : S → S → ℝ)
    (_hc : ∀ x y, 0 ≤ c x y) (hdiag : ∀ x, c x x = 0)
    (A : Set S) (hA : A.Nonempty) (lam : ℝ) (hlam : 0 ≤ lam) (x : S) (b : ℝ)
    (hb : ∀ y, eventPayoff A y - lam * c x y ≤ b) :
    max 0 (1 - lam * costToSet c A x) ≤ b := by
  classical
  have hb0 : 0 ≤ b := by
    have h := hb x
    rw [hdiag, mul_zero, sub_zero] at h
    exact (eventPayoff_bounds A x).1.trans h
  refine max_le hb0 ?_
  by_cases hz : lam = 0
  · obtain ⟨y,hy⟩ := hA
    have h := hb y
    simpa [hz, eventPayoff, hy] using h
  · have hp : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hz)
    let : Nonempty A := hA.to_subtype
    have hi : (1 - b) / lam ≤ costToSet c A x := by
      apply le_ciInf
      intro y
      have h := hb y
      simp only [eventPayoff, Set.indicator_of_mem y.property] at h
      apply (div_le_iff₀ hp).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hi hlam
    rw [mul_div_cancel₀ _ hz] at hm
    linarith

end WorstProbCodex
#print axioms WorstProbCodex.costToSet_nonneg
#print axioms WorstProbCodex.costToSet_le
#print axioms WorstProbCodex.eventPayoff_bounds
#print axioms WorstProbCodex.event_score_upper
#print axioms WorstProbCodex.event_envelope_le_of_upper

set_option autoImplicit false
open ModelRiskOT.WorstProb
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c)
    (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty) (lam : ℝ) (hlam : 0 ≤ lam) (x : S) :
    ⨆ y : S, (A.indicator (fun _ => (1 : ℝ)) y - lam * c x y) =
      max (1 - lam * costToSet c A x) 0 := by
  let : Nonempty S := ⟨hAne.choose⟩
  have hu : BddAbove (Set.range (fun y : S ↦ A.indicator (fun _ ↦ (1 : ℝ)) y - lam * c x y)) :=
    ⟨max 0 (1 - lam * costToSet c A x), by
      rintro _ ⟨y,rfl⟩
      exact WorstProbCodex.event_score_upper c hc.nonneg A lam hlam x y⟩
  rw [max_comm]
  apply le_antisymm
  · apply ciSup_le
    intro y
    exact WorstProbCodex.event_score_upper c hc.nonneg A lam hlam x y
  · apply WorstProbCodex.event_envelope_le_of_upper c hc.nonneg
      (fun z ↦ (hc.eq_zero_iff z z).mpr rfl) A hAne lam hlam x
    intro y
    exact le_ciSup hu y
#print axioms solution
