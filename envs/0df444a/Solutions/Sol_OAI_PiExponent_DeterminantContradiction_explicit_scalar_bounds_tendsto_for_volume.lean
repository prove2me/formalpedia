-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.explicit_scalar_bounds_tendsto_for_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:46:29.576871+00:00
-- url     : https://prove2.me/submissions/99004256-9b4d-4c20-8aef-982bf7e43acb

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : Real => (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds (A ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i)) ∧
    Tendsto (fun H : Real => (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds (A ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i)) := by
  have hinv : Tendsto (fun H : Real => H⁻¹) atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero
  have hminus :
      Tendsto (fun H : Real => A - (∑ i : Fin m, w i) / H) atTop (nhds A) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv))
  have hplus :
      Tendsto (fun H : Real => A + (∑ i : Fin m, w i) / H) atTop (nhds A) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
  constructor
  · simpa using (((hminus.pow m).div_const ((Nat.factorial m : Nat) : Real)).div_const
      (∏ i : Fin m, w i))
  · simpa using (((hplus.pow m).div_const ((Nat.factorial m : Nat) : Real)).div_const
      (∏ i : Fin m, w i))