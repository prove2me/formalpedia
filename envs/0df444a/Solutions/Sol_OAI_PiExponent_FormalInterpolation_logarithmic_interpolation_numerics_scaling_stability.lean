-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_interpolation_numerics_scaling_stability
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:38:29.143869+00:00
-- url     : https://prove2.me/submissions/24454c7e-9fe4-4ddd-afc1-14041c1b9e73

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaling_headroom
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaling_transfer

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (m K : Nat) (sigma : Rat) (w v : Fin (m + 1) -> Rat)
    (hN : OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics m K w v sigma) :
    exists t : Real, 1 < t /\
      exists w' v' : Fin (m + 1) -> Rat,
        (forall i, (w' i : Real) = t * (w i : Real)) /\
        (forall i, (v' i : Real) = (v i : Real)) /\
        OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics
          m K w' v' sigma := by
  let A : Real :=
    (K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
      (Finset.prod Finset.univ fun i => (w i : Real)) /
        (Finset.prod Finset.univ fun i => (v i : Real))
  let B : Real :=
    (K : Real) * (1 + 3 * (sigma : Real)) ^ m *
      (Finset.prod Finset.univ fun i : Fin m => (w i.succ : Real)) /
        (Finset.prod Finset.univ fun i : Fin m => (v i.succ : Real))
  let c : Fin m -> Real := fun i => (1 + (sigma : Real)) * (w i.succ : Real)
  let d : Fin m -> Real := fun i => (v i.succ : Real)
  have hA : A < 1 := by simpa [A] using hN.volume
  have hB : B < 1 := by simpa [B] using hN.fibre_volume
  have hcd : forall i, c i < d i := by simpa [c, d] using hN.coordinate_ratio
  obtain ⟨q, hq, hvol, hfibre, hcoord⟩ :=
    OAI.PiExponent.FormalInterpolation.scaling_headroom m A B c d hA hB hcd
  refine ⟨(q : Real), ?_, ?_⟩
  · exact_mod_cast hq
  · refine ⟨fun i => q * w i, v, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro i
      rfl
    · apply OAI.PiExponent.FormalInterpolation.scaling_transfer m K sigma w v hN q hq
      · simpa [A] using hvol
      · simpa [B] using hfibre
      · simpa [c, d] using hcoord