-- Prove2me | solution 1 for Kyprianou.Ch02.levyGridLinearGrowthV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:22:32.141915+00:00
-- url     : https://prove2.me/submissions/9e7aceda-0b84-4408-b6ab-689b25f94a63

import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyGridLaplaceDeficitV1
import Theorems.Thm_Kyprianou_Ch02_levyLaplaceCharDefectV1
import Theorems.Thm_Kyprianou_Ch02_levyGridCharDefectLinearV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ,
        c ≤ (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1)) →
    ∃ K : ℝ, ∀ ξ : ℝ,
      -(Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ).re ≤ K * (1 + |ξ|) := by
  intro h
  let q : ℕ → ℝ := fun n => ∫ ω, Real.exp (-|X (((n : ℝ≥0)+1)⁻¹) ω|) ∂P
  have hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1 := by
    intro n
    refine ⟨integral_nonneg (fun _ => Real.exp_nonneg _), ?_⟩
    calc
      q n ≤ ∫ _ : Ω, (1 : ℝ) ∂P := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (fun _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _)))
      _ = 1 := by simp
  obtain ⟨C,hC,hbound⟩ := Kyprianou.Ch02.levyGridLaplaceDeficitV1 q hq h
  refine ⟨4*C, ?_⟩
  intro ξ
  apply Kyprianou.Ch02.levyGridCharDefectLinearV1
  intro n
  have hm := Kyprianou.Ch02.levyLaplaceCharDefectV1 P
    (X (((n : ℝ≥0)+1)⁻¹)) (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX _) ξ
  rw [hchar] at hm
  push_cast at hm
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (n : ℝ)+1 by positivity)
  change _ ≤ ((n : ℝ)+1) * (4*(1+|ξ|)*(1-q n)) at hh
  calc
    _ ≤ ((n : ℝ)+1) * (4*(1+|ξ|)*(1-q n)) := hh
    _ = (4*(1+|ξ|))*(((n : ℝ)+1)*(1-q n)) := by ring
    _ ≤ (4*(1+|ξ|))*C := mul_le_mul_of_nonneg_left (hbound n) (by positivity)
    _ = _ := by ring
