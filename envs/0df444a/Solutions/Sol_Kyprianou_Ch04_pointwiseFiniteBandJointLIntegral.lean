-- Prove2me | solution 1 for Kyprianou.Ch04.pointwiseFiniteBandJointLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:52:05.593804+00:00
-- url     : https://prove2.me/submissions/78419065-77b0-4a02-9d6a-f188850bbc7d

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteKernelJointLIntegral
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

/-- Restrict to increasing finite bands, where the finite-kernel joint measurability theorem applies. -/
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (R : Omega → Measure E) (U : Set E) (hU : MeasurableSet U)
    (B : Nat → Set E) (hB : ∀ n, MeasurableSet (B n))
    (hm : Monotone B) (hc : (⋃ n, B n) = U)
    (hR : ∀ S : Set E, MeasurableSet S → S ⊆ U → Measurable (fun w => R w S))
    (hFin : ∀ n w, R w (B n) ≠ ⊤)
    (f : Omega × E → ENNReal) (hf : Measurable f) :
    Measurable (fun w => ∫⁻ z in U, f (w,z) ∂(R w)) := by
  have hsub (n : Nat) : B n ⊆ U := by
    rw [← hc]
    exact Set.subset_iUnion B n
  have h (n : Nat) : Measurable (fun w => ∫⁻ z in B n, f (w,z) ∂(R w)) := by
    apply pointwiseFiniteKernelJointLIntegral
    · intro S hS
      simp_rw [Measure.restrict_apply hS]
      exact hR (S ∩ B n) (hS.inter (hB n)) (Set.inter_subset_right.trans (hsub n))
    · intro w
      exact isFiniteMeasure_restrict.mpr (hFin n w)
    · exact hf
  rw [← hc]
  have hd : Directed (· ⊆ ·) B :=
    fun i j => ⟨max i j, hm (le_max_left _ _), hm (le_max_right _ _)⟩
  simp_rw [setLIntegral_iUnion_of_directed _ hd]
  exact Measurable.iSup h
