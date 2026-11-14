-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_order_mass_potential_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:25:57.059769+00:00
-- url     : https://prove2.me/submissions/fe3d848d-4f1b-40fe-9172-44ca77cdb3b9

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_g_concave
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_difference_concave
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_bounds
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_identity
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect Set

private theorem gap_pairing (ν : Measure ℝ) [IsFiniteMeasure ν] :
    pairing (fun q => fW q-gW q) ν = (massM ν).toReal-hPot ν := by
  have hf : (fun z : ℝ => Real.cosh z*fW (qOf z)) = fun _ => (1:ℝ) := by
    funext z
    exact (soft_field_mass_identity z).2.2
  have hfi : Integrable (fun z => Real.cosh z*fW (qOf z)) ν := by rw [hf]; exact integrable_const 1
  have hgi := (soft_field_potential_bounds ν).1
  have hfun : (fun z : ℝ => Real.cosh z*(fW (qOf z)-gW (qOf z))) =
      fun z => Real.cosh z*fW (qOf z) - Real.cosh z*gW (qOf z) := by
    funext z; ring
  unfold pairing hPot
  rw [hfun, integral_sub hfi hgi, hf]
  simp [pairing, massM, measureReal_def]

theorem solution (ν' ν : Measure ℝ) [IsFiniteMeasure ν'] [IsFiniteMeasure ν]
    (hord : softFieldLE ν' ν) :
    0 ≤ hPot ν-hPot ν' ∧
      hPot ν-hPot ν' ≤ (massM ν).toReal-(massM ν').toReal := by
  have hgcont : ContinuousOn gW (Icc 0 1) := by
    have hh : Continuous gW := by unfold gW; fun_prop
    exact hh.continuousOn
  have hdiffcont : ContinuousOn (fun q => fW q-gW q) (Icc 0 1) := by
    have hh : Continuous (fun q => fW q-gW q) := by unfold fW gW; fun_prop
    exact hh.continuousOn
  have h1 := hord gW hgcont soft_field_g_concave.1 soft_field_g_concave.2.1 soft_field_g_concave.2.2
  have h2 := hord (fun q => fW q-gW q) hdiffcont soft_field_difference_concave.1
    soft_field_difference_concave.2.1 soft_field_difference_concave.2.2
  change hPot ν' ≤ hPot ν at h1
  rw [gap_pairing, gap_pairing] at h2
  constructor <;> linarith
