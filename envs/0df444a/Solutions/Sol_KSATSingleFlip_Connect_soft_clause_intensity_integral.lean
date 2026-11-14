-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_clause_intensity_integral
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:40:42.316231+00:00
-- url     : https://prove2.me/submissions/02d6bd42-8cd9-4a8d-be70-45d801ab700b

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClauseIntensity
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect Set
open scoped ENNReal

theorem solution (ν : Measure ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    (∫ s, (Icc 0 1).indicator f s ∂(softClauseIntensity ν)) =
      4*pairing (fun q => f (1-q)) ν := by
  classical
  let g : ℝ → ℝ := (Icc 0 1).indicator f
  let T : ℝ → ℝ := fun z => 1-qOf z
  have hg : Measurable g := by
    have hh := hf.measurable_piecewise (continuousOn_const : ContinuousOn (fun _ : ℝ => (0:ℝ)) (Icc 0 1)ᶜ) measurableSet_Icc
    have heq : g = (Icc 0 1).piecewise f (fun _ => 0) := by
      funext s
      by_cases hs : s ∈ Icc (0:ℝ) 1 <;> simp [g, Set.indicator_apply, hs]
    rw [heq]
    exact hh
  have hT : Measurable T := by dsimp [T, qOf]; fun_prop
  have hw : Measurable (fun z : ℝ => ENNReal.ofReal (Real.cosh z)) := by fun_prop
  have hwt : ∀ᵐ z ∂ν, ENNReal.ofReal (Real.cosh z) < ∞ := Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top)
  have hmem (z : ℝ) : T z ∈ Icc 0 1 := by
    obtain ⟨h0,h1,_⟩ := soft_field_mass_identity z
    dsimp [T]
    constructor <;> linarith
  change (∫ s, g s ∂(softClauseIntensity ν)) = 4*pairing (fun q => f (1-q)) ν
  unfold softClauseIntensity
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_map hT.aemeasurable hg.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hw hwt]
  unfold pairing
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ENNReal.toReal_ofReal (le_of_lt (Real.cosh_pos z)), smul_eq_mul]
  dsimp [g]
  rw [Set.indicator_of_mem (hmem z)]
