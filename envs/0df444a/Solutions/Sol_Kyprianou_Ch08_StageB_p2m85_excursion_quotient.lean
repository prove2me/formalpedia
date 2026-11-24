-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_excursion_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:15:26.354907+00:00
-- url     : https://prove2.me/submissions/54cae305-2113-4bee-a4c1-cf773996cc73

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_excursion_integral_split
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem solution
    (ψ : ℝ → ℝ) (V : ℝ → ℝ) (n : Measure ℝ)
    (hr : HasQExcursionScaleRepresentation ψ 0 V n)
    (a x : ℝ) (hA : 0 < a) (hB : 0 < a-x) :
    Real.exp (-Phi ψ 0*x - ∫ t in (a-x)..a, (n (Ici t)).toReal) =
      V (a-x) / V a := by
  rcases lt_trichotomy 0 x with hx | hx | hx
  · obtain ⟨_, h⟩ := hr.2 (a-x) a hB (by linarith)
    rw [p2m85_excursion_integral_split ψ V n hr _ _ hB (by linarith), show a-(a-x)=x by ring] at h
    rw [h, mul_div_cancel_left₀ _ (hr.1 _ hA).ne']
    congr 1 <;> ring
  · subst x
    simp [div_self (hr.1 _ hA).ne']
  · obtain ⟨_, h⟩ := hr.2 a (a-x) hA (by linarith)
    rw [p2m85_excursion_integral_split ψ V n hr _ _ hA (by linarith), show a-x-a = -x by ring] at h
    rw [intervalIntegral.integral_symm a (a-x), h,
      div_mul_eq_div_div, div_self (hr.1 _ hB).ne']
    rw [one_div, ← Real.exp_neg]
    congr 1 <;> ring
