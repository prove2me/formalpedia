-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ZeroTimeObstruction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:58:34.302697+00:00
-- url     : https://prove2.me/submissions/5f8ea499-c1c1-4eb4-b456-03f562dac808

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2

import Theorems.Thm_Kyprianou_Ch04_exercise45DriftFirstCell
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every nonempty set has outer probability one in the trivial sigma algebra. -/
private theorem trivialOuterProb {Ω : Type} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m = ⊥)
    {s : Set Ω} (hs : s.Nonempty) : P s = 1 := by
  subst m
  letI : MeasurableSpace Ω := ⊥
  have hmeas : MeasurableSet (toMeasurable P s) :=
    measurableSet_toMeasurable P s
  rcases MeasurableSpace.measurableSet_bot_iff.mp hmeas with h | h
  · obtain ⟨w, hw⟩ := hs
    have hmem := subset_toMeasurable P s hw
    rw [h] at hmem
    exact False.elim (by simpa using hmem)
  · calc
      P s = P (toMeasurable P s) := (measure_toMeasurable s).symm
      _ = 1 := by rw [h, measure_univ]

/-- The exact physical UCP predicate fails for an unbounded arbitrary zero-time weight. -/
theorem solution {Ω : Type} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m = ⊥)
    (a : Ω → ℝ) (ha : ∀ n : ℕ, ∃ w, a w = (n : ℝ))
    (I : NNReal → Ω → ℝ)
    (hI : ∀ᵐ w ∂P, ∀ t : NNReal, I t w = (t : ℝ)^2) :
    ¬ Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P
      (fun t _ => (t : ℝ))
      (fun s w => 2 * (if s = 0 then a w else (s : ℝ))) I := by
  classical
  intro h
  have hIall : ∀ w t, I t w = (t : ℝ)^2 := by
    have hz := ae_iff.mp hI
    intro w t
    by_contra hne
    have hs : {w | ¬ ∀ t : NNReal, I t w = (t : ℝ)^2}.Nonempty :=
      ⟨w, fun hw => hne (hw t)⟩
    rw [trivialOuterProb P hm hs] at hz
    exact one_ne_zero hz
  let E (n : ℕ) : Set Ω := {w | ∃ t : NNReal, t ≤ 1 ∧
      1 ≤ |(∑ k ∈ Finset.range n,
        let u : NNReal := (1 : NNReal) * (k : NNReal) / (n : NNReal)
        let v : NNReal := (1 : NNReal) * ((k + 1 : ℕ) : NNReal) / (n : NNReal)
        (2 * (if u = 0 then a w else (u : ℝ))) *
          (((min t v : NNReal) : ℝ) - ((min t u : NNReal) : ℝ))) - I t w|}
  have hlim := h 1 1 zero_lt_one
  change Tendsto (fun n => (P (E n)).toReal) atTop (nhds 0) at hlim
  have he : ∀ᶠ n : ℕ in atTop, (P (E n)).toReal = 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := hn
    obtain ⟨w, hw⟩ := ha n
    let q : NNReal := 1 / (n : NNReal)
    have hn1 : (1 : NNReal) ≤ (n : NNReal) := by exact_mod_cast hn
    have hq : q ≤ 1 := (div_le_one (by positivity)).2 hn1
    have hqr : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    have hqn : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hsum := Kyprianou.Ch04.exercise45DriftFirstCell n hnpos (a w)
    rw [hw] at hsum
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have htwo : 2 * (n : ℝ) / (n : ℝ) = 2 := by field_simp
    rw [htwo] at hsum
    have hs : (E n).Nonempty := by
      refine ⟨w, q, hq, ?_⟩
      rw [hw, hsum, hIall w q]
      apply le_trans ?_ (le_abs_self _)
      nlinarith [mul_nonneg hqn (sub_nonneg.mpr hqr)]
    rw [trivialOuterProb P hm hs, ENNReal.toReal_one]
  have heq : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] (fun n => (P (E n)).toReal) := by
    filter_upwards [he] with n h
    exact h.symm
  have hlim1 : Tendsto (fun n => (P (E n)).toReal) atTop (nhds (1 : ℝ)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).congr' heq
  exact zero_ne_one (tendsto_nhds_unique hlim hlim1)
