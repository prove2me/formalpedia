-- Prove2me | solution 1 for GittinsUCB.Patient.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:21:50.47633+00:00
-- url     : https://prove2.me/submissions/e7670535-964a-4447-aaac-dbcb0417dcab

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
import Theorems.Thm_GittinsUCB_Patient_standardization
import Theorems.Thm_GittinsUCB_Patient_lemma_3
import Theorems.Thm_GittinsUCB_Patient_lemma_5
import Theorems.Thm_GittinsUCB_Patient_lemma_6
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2)
    (μ : ℝ) (σ2 : ℝ≥0) (hσ : 0 < σ2) :
    Tendsto (fun γ : ℝ => gittinsIndex σW2 γ μ σ2 -
      (μ + stdQuantile γ * Real.sqrt (σ2 : ℝ)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  set F := nhdsWithin (1 : ℝ) (Set.Iio 1) with hF
  have hW' : 0 < σW2 / σ2 := div_pos hW hσ
  set a : ℝ → ℝ := fun γ => Real.sqrt (2 * Real.log (1 / (1 - γ))) with ha
  -- the standardized index is within o(1) of `a`
  have hg : Tendsto (fun γ => gittinsIndex (σW2 / σ2) γ 0 1 - a γ) F (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h5 := lemma_5 (σW2 / σ2) hW' (ε / 2) (half_pos hε)
    have h6 := lemma_6 (σW2 / σ2) hW' (ε / 2) (half_pos hε)
    filter_upwards [h5, h6] with γ h5 h6
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith
  have hq : Tendsto (fun γ => stdQuantile γ - a γ) F (nhds 0) := lemma_3
  have hlim : Tendsto (fun γ => Real.sqrt (σ2 : ℝ) * (gittinsIndex (σW2 / σ2) γ 0 1 - a γ)
      - Real.sqrt (σ2 : ℝ) * (stdQuantile γ - a γ)) F (nhds 0) := by
    have := (hg.const_mul (Real.sqrt (σ2 : ℝ))).sub (hq.const_mul (Real.sqrt (σ2 : ℝ)))
    simpa using this
  have hev : ∀ᶠ γ in F, γ ∈ Set.Ioo (0 : ℝ) 1 := by
    have : Set.Ioo (0 : ℝ) 1 ∈ F := by
      rw [hF]
      exact Ioo_mem_nhdsLT (by norm_num)
    exact this
  refine hlim.congr' ?_
  filter_upwards [hev] with γ hγ
  rw [standardization σW2 hW γ μ hγ.1 hγ.2 σ2 hσ]
  ring
