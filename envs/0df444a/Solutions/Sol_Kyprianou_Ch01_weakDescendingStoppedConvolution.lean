-- Prove2me | solution 1 for Kyprianou.Ch01.weakDescendingStoppedConvolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:16:19.531392+00:00
-- url     : https://prove2.me/submissions/84aa2458-eb60-46af-8419-5cfb3993d647

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Theorems.Thm_Kyprianou_Ch01_weakDescendingStoppedJointProduct
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hLaw : ∀ n : ℕ, HasLaw (increment n) mu P)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    P {ω | S (n + 1) ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} =
      ∫⁻ y : ℝ, mu ((fun z : ℝ => y + z) ⁻¹' B) ∂
        (Measure.map (S n)
          (P.restrict {ω | ∀ j : ℕ,
              1 ≤ j → j ≤ n → 0 < S j ω})) := by
  intro S
  let H : Set Ω :=
    {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
  let f : Ω → ℝ × ℝ := fun ω => (S n ω, increment n ω)
  let D : Set (ℝ × ℝ) := {p | p.1 + p.2 ∈ B}
  have hSn (ω : Ω) :
      S (n + 1) ω = S n ω + increment n ω := by
    simp [S, Finset.sum_range_succ]
  have hSnmeas : Measurable (S n) := by
    change Measurable (fun ω => ∑ i ∈ Finset.range n, increment i ω)
    fun_prop
  have hf : Measurable f := hSnmeas.prodMk (hmeas n)
  have hD : MeasurableSet D :=
    hB.preimage (measurable_fst.add measurable_snd)
  have hE : MeasurableSet (f ⁻¹' D) := hD.preimage hf
  have hevent :
      {ω | S (n + 1) ω ∈ B ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω} =
      (f ⁻¹' D) ∩ H := by
    ext ω
    dsimp [f, D, H]
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff]
    rw [hSn ω]
  have hprod :
      Measure.map f (P.restrict H) =
      (Measure.map (S n) (P.restrict H)).prod mu := by
    exact Kyprianou.Ch01.weakDescendingStoppedJointProduct
      P increment hmeas hindep mu hLaw n
  calc
    P {ω | S (n + 1) ω ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
      = P ((f ⁻¹' D) ∩ H) := congrArg P hevent
    _ = (P.restrict H) (f ⁻¹' D) := (Measure.restrict_apply hE).symm
    _ = (Measure.map f (P.restrict H)) D :=
      (Measure.map_apply hf hD).symm
    _ = ((Measure.map (S n) (P.restrict H)).prod mu) D := by
      rw [hprod]
    _ = ∫⁻ y : ℝ, mu ((fun z : ℝ => y + z) ⁻¹' B) ∂
          (Measure.map (S n) (P.restrict H)) := by
      rw [Measure.prod_apply hD]
      congr 1
