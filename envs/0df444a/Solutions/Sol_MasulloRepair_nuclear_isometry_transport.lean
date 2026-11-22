-- Prove2me | solution 1 for MasulloRepair.nuclear_isometry_transport
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T19:29:50.273328+00:00
-- url     : https://prove2.me/submissions/e2608497-f2ec-47d5-b598-600514a3bc89

import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

open MasulloGRH ContinuousLinearMap
open scoped InnerProductSpace

theorem solution {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsNuclearOperator
      (U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint) ∧
    operatorTrace (U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint) =
      operatorTrace T := by
  obtain ⟨x, y, hs, hxy⟩ := hT
  have hsU : Summable (fun n => ‖U (x n)‖ * ‖U (y n)‖) := by
    simpa only [U.norm_map] using hs
  have hxyU : ∀ v : K, HasSum (fun n => inner ℂ (U (x n)) v • U (y n))
      ((U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint) v) := by
    intro v
    have h := (hxy (U.toContinuousLinearMap.adjoint v)).mapL U.toContinuousLinearMap
    simpa only [map_smul, ContinuousLinearMap.adjoint_inner_right,
      LinearIsometry.coe_toContinuousLinearMap, ContinuousLinearMap.comp_apply] using h
  refine ⟨⟨fun n => U (x n), fun n => U (y n), hsU, hxyU⟩, ?_⟩
  rw [operatorTrace_of_nuclear_series _ _ _ hsU hxyU,
    operatorTrace_of_nuclear_series T x y hs hxy]
  exact tsum_congr fun n => U.inner_map_map (x n) (y n)

#print axioms solution
