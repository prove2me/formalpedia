-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_two_cell_charfun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:06:48.501478+00:00
-- url     : https://prove2.me/submissions/b6521e29-c284-4e4a-8cdf-193b885a35d7

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two disjoint Poisson count integrands have additive characteristic exponents. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b ξ : ℝ) :
    charFun (P.map (fun ω =>
      a * (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal +
      b * (ProbabilityTheory.poissonRandomMeasure K Y ω B).toReal)) ξ =
      Complex.exp ((((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) +
        (((m B).toReal : ℂ) *
        (Complex.exp ((((b * ξ : ℝ) : ℂ)) * Complex.I) - 1))) := by
  let ZA : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω A).toReal
  let ZB : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω B).toReal
  have hmA : Measurable ZA :=
    ENNReal.measurable_toReal.comp
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA)
  have hmB : Measurable ZB :=
    ENNReal.measurable_toReal.comp
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hB)
  have hInd0 : IndepFun ZA ZB P :=
    (indepFun_poissonRandomMeasure_apply hd hA hB hfinA hfinB hAB).comp
      ENNReal.measurable_toReal ENNReal.measurable_toReal
  have hInd : IndepFun (fun ω => a * ZA ω) (fun ω => b * ZB ω) P := by
    exact hInd0.comp
      (φ := fun z : ℝ => a * z) (ψ := fun z : ℝ => b * z)
      (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)
  have ha : Measurable (fun ω => a * ZA ω) := measurable_const.mul hmA
  have hb : Measurable (fun ω => b * ZB ω) := measurable_const.mul hmB
  have hφA : charFun (P.map (fun ω => a * ZA ω)) ξ =
      Complex.exp (((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) := by
    calc
      charFun (P.map (fun ω => a * ZA ω)) ξ =
        charFun (P.map ZA) (a * ξ) :=
        charFun_map_mul_comp hmA.aemeasurable a ξ
      _ = _ := charFun_natCast_poissonRandomMeasure_apply hd hA hfinA (a * ξ)
  have hφB : charFun (P.map (fun ω => b * ZB ω)) ξ =
      Complex.exp (((m B).toReal : ℂ) *
        (Complex.exp ((((b * ξ : ℝ) : ℂ)) * Complex.I) - 1)) := by
    calc
      charFun (P.map (fun ω => b * ZB ω)) ξ =
        charFun (P.map ZB) (b * ξ) :=
        charFun_map_mul_comp hmB.aemeasurable b ξ
      _ = _ := charFun_natCast_poissonRandomMeasure_apply hd hB hfinB (b * ξ)
  change charFun (P.map (fun ω => a * ZA ω + b * ZB ω)) ξ = _
  calc
    charFun (P.map (fun ω => a * ZA ω + b * ZB ω)) ξ =
        charFun (P.map (fun ω => a * ZA ω)) ξ *
          charFun (P.map (fun ω => b * ZB ω)) ξ :=
      congrArg (fun φ : ℝ → ℂ => φ ξ)
        (IndepFun.charFun_map_fun_add_eq_mul ha.aemeasurable hb.aemeasurable hInd)
    _ = _ := by rw [hφA, hφB, ← Complex.exp_add]
