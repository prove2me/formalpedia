-- Prove2me | solution 1 for Kyprianou.Ch01.riskSurplus_isCadlag_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:01:39.561189+00:00
-- url     : https://prove2.me/submissions/973e1dc7-ecfa-4c98-b58b-9adbf7ff322d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_ProbabilityTheory_compoundPoisson_ae_isCadlag
import Theorems.Thm_isCadlag_comp_nnrealCoe
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
import Theorems.Thm_Continuous_isCadlag
import Theorems.Thm_Kyprianou_Ch01_cadlag_nnreal_neg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hr : 0 < rate) (premium x : ℝ) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => riskSurplus arrival claims premium x t ω) := by
  filter_upwards [ProbabilityTheory.compoundPoisson_ae_isCadlag (b := 0) hd hr]
    with ω hω
  have hcp : ProbabilityTheory.IsCadlag
      (fun s : ℝ≥0 => ProbabilityTheory.compoundPoisson 0 arrival claims (s : ℝ) ω) :=
    isCadlag_comp_nnrealCoe hω
  have hneg := cadlag_nnreal_neg _ hcp
  have hcont : Continuous (fun s : ℝ≥0 => x + premium * (s : ℝ)) := by fun_prop
  have hp : ProbabilityTheory.IsCadlag (fun s : ℝ≥0 => x + premium * (s : ℝ)) :=
    Continuous.isCadlag hcont
  have hsum := ProbabilityTheory.IsCadlag.add hp hneg
  simpa [riskSurplus, aggregateClaims, sub_eq_add_neg] using hsum
