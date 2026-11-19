-- Prove2me | solution 1 for Kyprianou.Ch01.weakDescendingStoppedJointProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:36:12.578212+00:00
-- url     : https://prove2.me/submissions/cfa6e412-10ec-483a-b022-e056f49a1624

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_Kyprianou_Ch01_mapRestrictedIndependentProduct
import Theorems.Thm_Kyprianou_Ch01_finitePrefixIndependentOfNext
import Theorems.Thm_Kyprianou_Ch01_weakPrefixVectorRepresentation
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
    (n : ℕ) :
    let S : ℕ → Ω → ℝ :=
      fun k ω => ∑ i ∈ Finset.range k, increment i ω
    let H : Set Ω :=
      {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
    Measure.map (fun ω => (S n ω, increment n ω))
      (P.restrict H) =
        (Measure.map (S n) (P.restrict H)).prod mu := by
  intro S H
  let V : Ω → (Finset.range n → ℝ) :=
    fun ω i => increment i.1 ω
  obtain ⟨g, A, hmg, hA, hS, hH⟩ :=
    Kyprianou.Ch01.weakPrefixVectorRepresentation increment hmeas n
  have hmV : Measurable V := by
    apply measurable_pi_lambda
    intro i
    exact hmeas i.1
  have hi : IndepFun V (increment n) P := by
    simpa only [V] using
      (Kyprianou.Ch01.finitePrefixIndependentOfNext P increment hmeas hindep n)
  have hf : Measurable (fun ω => (V ω, increment n ω)) :=
    hmV.prodMk (hmeas n)
  have hp :
      (P.restrict H).map (fun ω => (V ω, increment n ω)) =
      ((P.restrict H).map V).prod mu := by
    have h := Kyprianou.Ch01.mapRestrictedIndependentProduct
      P V (increment n) hmV (hmeas n) hi A hA
    rw [← hH, (hLaw n).map_eq] at h
    exact h
  have hmgp : Measurable (Prod.map g (id : ℝ → ℝ)) :=
    hmg.prodMap measurable_id
  calc
    (P.restrict H).map (fun ω => (S n ω, increment n ω))
      = ((P.restrict H).map (fun ω => (V ω, increment n ω))).map
          (Prod.map g (id : ℝ → ℝ)) := by
            rw [Measure.map_map hmgp hf]
            apply Measure.map_congr
            filter_upwards [] with ω
            exact congrArg (fun y : ℝ => (y, increment n ω)) (hS ω)
    _ = (((P.restrict H).map V).prod mu).map
          (Prod.map g (id : ℝ → ℝ)) := by rw [hp]
    _ = (((P.restrict H).map V).map g).prod mu := by
          rw [← Measure.map_prod_map _ _ hmg measurable_id]
          simp
    _ = ((P.restrict H).map (S n)).prod mu := by
          have hmap : ((P.restrict H).map V).map g =
              (P.restrict H).map (S n) := by
            rw [Measure.map_map hmg hmV]
            apply Measure.map_congr
            filter_upwards [] with ω
            exact (hS ω).symm
          exact congrArg (fun ν : Measure ℝ => ν.prod mu) hmap
