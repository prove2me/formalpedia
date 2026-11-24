-- Prove2me | solution 1 for Kyprianou.Ch03.stableHighGridExpectationTendstoZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:19.684294+00:00
-- url     : https://prove2.me/submissions/1955bcd4-5b87-49b4-8811-4d17b8f80e3c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyUniformGridExponentialAbsoluteSumExpectationV1
import Theorems.Thm_Kyprianou_Ch03_stableExpAbsoluteDeficitBoundV1
import Theorems.Thm_Kyprianou_Ch03_stableGridRpowExpDecayV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (α : ℝ) (hα : 1 < α) (hne : ¬ X 1 =ᵐ[P] 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun w => scale ^ (1 / α) * X t w)) :
    Tendsto (fun n : ℕ => ∫ w, Real.exp (-(∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : NNReal) * (((n : NNReal) + 1)⁻¹)) w -
           X ((i.val : NNReal) * (((n : NNReal) + 1)⁻¹)) w|)) ∂P)
      atTop (𝓝 0) := by
  have hm (t : NNReal) : AEMeasurable (X t) P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  obtain ⟨c, hc, hbound⟩ := Kyprianou.Ch03.stableExpAbsoluteDeficitBoundV1 P (X 1) (hm 1) hne
  let G (n : ℕ) : ℝ := ∫ w, Real.exp (-(∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : NNReal) * (((n : NNReal) + 1)⁻¹)) w -
           X ((i.val : NNReal) * (((n : NNReal) + 1)⁻¹)) w|)) ∂P
  have hle (n : ℕ) : G n ≤ Real.exp (-c * ((n : ℝ) + 1) ^ (1 - 1 / α)) := by
    let t : NNReal := ((n : NNReal) + 1)⁻¹
    let s : ℝ := (t : ℝ) ^ (1 / α)
    have ht : 0 < t := by dsimp [t]; positivity
    have hs : 0 ≤ s := Real.rpow_nonneg t.coe_nonneg _
    have ht1 : (t : ℝ) ≤ 1 := by
      dsimp [t]
      push_cast
      apply inv_le_one_of_one_le₀
      have hn : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hα0 : 0 < α := by linarith
    have hs1 : s ≤ 1 := Real.rpow_le_one t.coe_nonneg ht1 (div_nonneg zero_le_one hα0.le)
    have hscale : P.map (X t) = P.map (fun w => s * X 1 w) := by
      simpa [s] using hStable 1 (t : ℝ) (by exact_mod_cast ht)
    let f : ℝ → ℝ := fun x => Real.exp (-|x|)
    have hf : Measurable f := by dsimp [f]; fun_prop
    have hmap : (∫ w, Real.exp (-|X t w|) ∂P) =
        ∫ w, Real.exp (-s * |X 1 w|) ∂P := by
      calc
        _ = ∫ x, f x ∂(P.map (X t)) :=
          (integral_map (hm t) hf.aestronglyMeasurable).symm
        _ = ∫ x, f x ∂(P.map (fun w => s * X 1 w)) := by rw [hscale]
        _ = _ := by
          have hsm : AEMeasurable (fun w => s * X 1 w) P := aemeasurable_const.mul (hm 1)
          rw [integral_map hsm hf.aestronglyMeasurable]
          simp only [f, abs_mul, abs_of_nonneg hs, neg_mul]
    have hq : 0 ≤ ∫ w, Real.exp (-|X t w|) ∂P := integral_nonneg fun w => (Real.exp_pos _).le
    have hqle := hmap.le.trans (hbound s hs hs1)
    dsimp [G]
    rw [Kyprianou.Ch02.levyUniformGridExponentialAbsoluteSumExpectationV1 P X hX n]
    change (∫ w, Real.exp (-|X t w|) ∂P) ^ (n + 1) ≤ _
    calc
      _ ≤ Real.exp (-c * s) ^ (n + 1) := pow_le_pow_left₀ hq hqle _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        have hb : 0 < (n : ℝ) + 1 := by positivity
        have he : ((n : ℝ) + 1) ^ (1 - 1 / α) = ((n : ℝ) + 1) * s := by
          rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_one, Real.rpow_neg hb.le]
          dsimp [s, t]
          push_cast
          rw [Real.inv_rpow hb.le]
        rw [he]
        push_cast
        ring
  change Tendsto G atTop (𝓝 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (Kyprianou.Ch03.stableGridRpowExpDecayV1 α c hα hc)
    (fun n => integral_nonneg fun w => (Real.exp_pos _).le) hle
