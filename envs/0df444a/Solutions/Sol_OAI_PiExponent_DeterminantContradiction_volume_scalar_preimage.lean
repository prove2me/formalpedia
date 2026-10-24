-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_scalar_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:18:32.275781+00:00
-- url     : https://prove2.me/submissions/85e3deed-1611-4858-9934-b71315551cec

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

noncomputable section

theorem solution
    (n : Nat) (r : Real) (hpos : 0 < r) (s : Set (Fin n → Real)) :
    MeasureTheory.volume ((fun y : Fin n → Real => r⁻¹ • y) ⁻¹' s) =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume s := by
  let e : (Fin n → Real) ≃ₗ[Real] (Fin n → Real) :=
    LinearEquiv.smulOfNeZero Real (Fin n → Real) r⁻¹ (inv_ne_zero hpos.ne')
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' e).ne_zero
  have hmatrix : LinearMap.toMatrix' e.toLinearMap =
      Matrix.diagonal (fun _ : Fin n => r⁻¹) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [e, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit,
        Matrix.diagonal, Pi.single_apply]
    · simp [e, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit,
        Matrix.diagonal, Pi.single_apply, hij]
  have hdetval : LinearMap.det e.toLinearMap = (r⁻¹) ^ n := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    simp
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := e.toLinearMap) hdet
  calc
    MeasureTheory.volume ((fun y : Fin n → Real => r⁻¹ • y) ⁻¹' s) =
        (MeasureTheory.volume.map
          e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv) s := by
      symm
      exact e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply s
    _ = ENNReal.ofReal (r ^ n) * MeasureTheory.volume s := by
      change (MeasureTheory.Measure.map (e.toLinearMap) MeasureTheory.volume) s = _
      rw [hmap, MeasureTheory.Measure.smul_apply, hdetval]
      have hpow : 0 < (r⁻¹) ^ n := pow_pos (inv_pos.mpr hpos) n
      have hfactor : |((r⁻¹) ^ n)⁻¹| = r ^ n := by
        rw [abs_of_pos (inv_pos.mpr hpow), inv_pow]
        simp
      rw [hfactor]
      simpa only [smul_eq_mul]