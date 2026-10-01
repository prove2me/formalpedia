-- Prove2me | solution 1 for MilnorDynamics.isHolomorphicOn_smul_gl_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T10:11:26.689228+00:00
-- url     : https://prove2.me/submissions/a8f19cdc-d6dc-4d0b-aee6-5f824be33cd5

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_gl_action_continuous

open scoped OnePoint Topology
open Bornology
open Filter Set
open MilnorDynamics

/-- Finite chart of `g • u` in terms of the finite chart of `u`, for `u ≠ ∞`. -/
private lemma chartFinite_smul_of_ne_infty (g : GL (Fin 2) ℂ) {u : OnePoint ℂ} (hu : u ≠ ∞) :
    chartFinite (g • u) = (g 0 0 * chartFinite u + g 0 1) / (g 1 0 * chartFinite u + g 1 1) := by
  cases u with
  | infty => exact absurd rfl hu
  | coe v =>
      rw [OnePoint.smul_some_eq_ite]
      by_cases h : g 1 0 * v + g 1 1 = 0
      · simp [chartFinite, h]
      · simp [chartFinite, h]

/-- Reciprocal chart of `g • u` in terms of the finite chart of `u`, for `u ≠ ∞`. -/
private lemma chartInfinite_smul_of_ne_infty (g : GL (Fin 2) ℂ) {u : OnePoint ℂ}
    (hu : u ≠ ∞) :
    chartInfinite (g • u) = (g 1 0 * chartFinite u + g 1 1) / (g 0 0 * chartFinite u + g 0 1) := by
  cases u with
  | infty => exact absurd rfl hu
  | coe v =>
      rw [OnePoint.smul_some_eq_ite]
      by_cases h : g 1 0 * v + g 1 1 = 0
      · simp [chartFinite, chartInfinite, h]
      · simp [chartFinite, chartInfinite, h, inv_div]

/-- Finite chart of `g • u` in terms of the reciprocal chart of `u`, for `u ≠ 0`. -/
private lemma chartFinite_smul_of_ne_zero (g : GL (Fin 2) ℂ) {u : OnePoint ℂ}
    (hu : u ≠ ((0 : ℂ) : OnePoint ℂ)) :
    chartFinite (g • u) = (g 0 0 + g 0 1 * chartInfinite u) / (g 1 0 + g 1 1 * chartInfinite u) := by
  cases u with
  | infty =>
      rw [OnePoint.smul_infty_eq_ite]
      by_cases h : g 1 0 = 0
      · simp [chartFinite, chartInfinite, h]
      · simp [chartFinite, chartInfinite, h]
  | coe v =>
      have hv : v ≠ 0 := fun hv0 => hu (by simp [hv0])
      rw [OnePoint.smul_some_eq_ite]
      by_cases h : g 1 0 * v + g 1 1 = 0
      · have h2 : g 1 0 + g 1 1 * v⁻¹ = 0 := by
          field_simp
          linear_combination h
        simp [chartFinite, chartInfinite, h, h2]
      · by_cases h3 : g 0 0 * v + g 0 1 = 0
        · have h4 : g 0 0 + g 0 1 * v⁻¹ = 0 := by
            field_simp
            linear_combination h3
          simp [chartFinite, chartInfinite, h, h3, h4]
        · have h4 : g 0 0 + g 0 1 * v⁻¹ ≠ 0 := by
            intro h4
            refine h3 ?_
            field_simp at h4
            linear_combination h4
          have h5 : g 1 0 + g 1 1 * v⁻¹ ≠ 0 := by
            intro h5
            refine h ?_
            field_simp at h5
            linear_combination h5
          rw [if_neg h]
          simp only [chartFinite, chartInfinite]
          first | (field_simp; ring) | field_simp

/-- Reciprocal chart of `g • u` in terms of the reciprocal chart of `u`, for `u ≠ 0`. -/
private lemma chartInfinite_smul_of_ne_zero (g : GL (Fin 2) ℂ) {u : OnePoint ℂ}
    (hu : u ≠ ((0 : ℂ) : OnePoint ℂ)) :
    chartInfinite (g • u) = (g 1 0 + g 1 1 * chartInfinite u) / (g 0 0 + g 0 1 * chartInfinite u) := by
  cases u with
  | infty =>
      rw [OnePoint.smul_infty_eq_ite]
      by_cases h : g 1 0 = 0
      · simp [chartFinite, chartInfinite, h]
      · simp [chartFinite, chartInfinite, h, inv_div]
  | coe v =>
      have hv : v ≠ 0 := fun hv0 => hu (by simp [hv0])
      rw [OnePoint.smul_some_eq_ite]
      by_cases h : g 1 0 * v + g 1 1 = 0
      · have h2 : g 1 0 + g 1 1 * v⁻¹ = 0 := by
          field_simp
          linear_combination h
        simp [chartFinite, chartInfinite, h, h2]
      · by_cases h3 : g 0 0 * v + g 0 1 = 0
        · have h4 : g 0 0 + g 0 1 * v⁻¹ = 0 := by
            field_simp
            linear_combination h3
          simp [chartFinite, chartInfinite, h, h3, h4]
        · have h4 : g 0 0 + g 0 1 * v⁻¹ ≠ 0 := by
            intro h4
            refine h3 ?_
            field_simp at h4
            linear_combination h4
          have h5 : g 1 0 + g 1 1 * v⁻¹ ≠ 0 := by
            intro h5
            refine h ?_
            field_simp at h5
            linear_combination h5
          rw [if_neg h]
          simp only [chartInfinite]
          rw [inv_div]
          first | (field_simp; ring) | field_simp

theorem solution (g : GL (Fin 2) ℂ) (U : Set ℂ) (hU : IsOpen U) (f : ℂ → OnePoint ℂ)
    (hf : IsHolomorphicOn U f) : IsHolomorphicOn U (fun z => g • f z) := by
  obtain ⟨hcont, hfin, hinf⟩ := hf
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    simpa [Matrix.det_fin_two] using g.det_ne_zero
  refine ⟨(gl_action_continuous g).1.comp_continuousOn hcont, ?_, ?_⟩
  · intro z hzU hz
    have hcat : ContinuousAt f z := hcont.continuousAt (hU.mem_nhds hzU)
    have hz' : g • f z ≠ ∞ := by simpa using hz
    by_cases hfz : f z = ∞
    · have hz0 : f z ≠ ((0 : ℂ) : OnePoint ℂ) := by
        rw [hfz]; exact OnePoint.infty_ne_coe 0
      have hr : g 1 0 ≠ 0 := by
        intro h
        exact hz' (by rw [hfz, OnePoint.smul_infty_eq_ite, if_pos h])
      have ht : DifferentiableAt ℂ (fun w => chartInfinite (f w)) z := hinf z hzU hz0
      have hev : (fun w => chartFinite (g • f w)) =ᶠ[𝓝 z]
          fun w => (g 0 0 + g 0 1 * chartInfinite (f w)) /
            (g 1 0 + g 1 1 * chartInfinite (f w)) := by
        filter_upwards [hcat.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hz0)]
          with w hw
        exact chartFinite_smul_of_ne_zero g hw
      have hnum : DifferentiableAt ℂ (fun w => g 0 0 + g 0 1 * chartInfinite (f w)) z :=
        (ht.const_mul (g 0 1)).const_add (g 0 0)
      have hden : DifferentiableAt ℂ (fun w => g 1 0 + g 1 1 * chartInfinite (f w)) z :=
        (ht.const_mul (g 1 1)).const_add (g 1 0)
      have hden0 : g 1 0 + g 1 1 * chartInfinite (f z) ≠ 0 := by
        simpa [hfz, chartInfinite] using hr
      exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr (hnum.div hden hden0)
    · have ht : DifferentiableAt ℂ (fun w => chartFinite (f w)) z := hfin z hzU hfz
      have hge : f z = ((chartFinite (f z) : ℂ) : OnePoint ℂ) := by
        cases h : f z with
        | infty => exact absurd h hfz
        | coe v => simp [chartFinite]
      have hev : (fun w => chartFinite (g • f w)) =ᶠ[𝓝 z]
          fun w => (g 0 0 * chartFinite (f w) + g 0 1) /
            (g 1 0 * chartFinite (f w) + g 1 1) := by
        filter_upwards [hcat.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hfz)]
          with w hw
        exact chartFinite_smul_of_ne_infty g hw
      have hnum : DifferentiableAt ℂ (fun w => g 0 0 * chartFinite (f w) + g 0 1) z :=
        (ht.const_mul (g 0 0)).add_const (g 0 1)
      have hden : DifferentiableAt ℂ (fun w => g 1 0 * chartFinite (f w) + g 1 1) z :=
        (ht.const_mul (g 1 0)).add_const (g 1 1)
      have hden0 : g 1 0 * chartFinite (f z) + g 1 1 ≠ 0 := by
        intro h
        exact hz' (by rw [hge, OnePoint.smul_some_eq_ite, if_pos h])
      exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr (hnum.div hden hden0)
  · intro z hzU hz
    have hcat : ContinuousAt f z := hcont.continuousAt (hU.mem_nhds hzU)
    have hz' : g • f z ≠ ((0 : ℂ) : OnePoint ℂ) := by simpa using hz
    by_cases hfz : f z = ∞
    · have hz0 : f z ≠ ((0 : ℂ) : OnePoint ℂ) := by
        rw [hfz]; exact OnePoint.infty_ne_coe 0
      have hp : g 0 0 ≠ 0 := by
        by_cases hr : g 1 0 = 0
        · intro hp0
          exact hdet (by rw [hr, hp0]; ring)
        · intro hp0
          exact hz' (by rw [hfz, OnePoint.smul_infty_eq_ite, if_neg hr, hp0, zero_div])
      have ht : DifferentiableAt ℂ (fun w => chartInfinite (f w)) z := hinf z hzU hz0
      have hev : (fun w => chartInfinite (g • f w)) =ᶠ[𝓝 z]
          fun w => (g 1 0 + g 1 1 * chartInfinite (f w)) /
            (g 0 0 + g 0 1 * chartInfinite (f w)) := by
        filter_upwards [hcat.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hz0)]
          with w hw
        exact chartInfinite_smul_of_ne_zero g hw
      have hnum : DifferentiableAt ℂ (fun w => g 1 0 + g 1 1 * chartInfinite (f w)) z :=
        (ht.const_mul (g 1 1)).const_add (g 1 0)
      have hden : DifferentiableAt ℂ (fun w => g 0 0 + g 0 1 * chartInfinite (f w)) z :=
        (ht.const_mul (g 0 1)).const_add (g 0 0)
      have hden0 : g 0 0 + g 0 1 * chartInfinite (f z) ≠ 0 := by
        simpa [hfz, chartInfinite] using hp
      exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr (hnum.div hden hden0)
    · have hge : f z = ((chartFinite (f z) : ℂ) : OnePoint ℂ) := by
        cases h : f z with
        | infty => exact absurd h hfz
        | coe v => simp [chartFinite]
      have ht : DifferentiableAt ℂ (fun w => chartFinite (f w)) z := hfin z hzU hfz
      have hden0 : g 0 0 * chartFinite (f z) + g 0 1 ≠ 0 := by
        by_cases hd : g 1 0 * chartFinite (f z) + g 1 1 = 0
        · intro h0
          have h11 : g 1 1 = -(g 1 0 * chartFinite (f z)) := by linear_combination hd
          have h01 : g 0 1 = -(g 0 0 * chartFinite (f z)) := by linear_combination h0
          exact hdet (by rw [h11, h01]; ring)
        · intro h0
          exact hz' (by rw [hge, OnePoint.smul_some_eq_ite, if_neg hd, h0, zero_div])
      have hev : (fun w => chartInfinite (g • f w)) =ᶠ[𝓝 z]
          fun w => (g 1 0 * chartFinite (f w) + g 1 1) /
            (g 0 0 * chartFinite (f w) + g 0 1) := by
        filter_upwards [hcat.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hfz)]
          with w hw
        exact chartInfinite_smul_of_ne_infty g hw
      have hnum : DifferentiableAt ℂ (fun w => g 1 0 * chartFinite (f w) + g 1 1) z :=
        (ht.const_mul (g 1 0)).add_const (g 1 1)
      have hden : DifferentiableAt ℂ (fun w => g 0 0 * chartFinite (f w) + g 0 1) z :=
        (ht.const_mul (g 0 0)).add_const (g 0 1)
      exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr (hnum.div hden hden0)
