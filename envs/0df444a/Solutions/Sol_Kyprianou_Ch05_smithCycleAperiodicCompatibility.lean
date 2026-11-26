-- Prove2me | solution 1 for Kyprianou.Ch05.smithCycleAperiodicCompatibility
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:58:07.835556+00:00
-- url     : https://prove2.me/submissions/0f3b60a1-13d7-4b9d-9b1e-ded697c6aee9

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- A Chapter 5 nonlattice probability law supported on the nonnegative half-line with positive mean satisfies Smith's cycle-law and aperiodicity predicates. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F)
    (hnl : NonLatticeMeasure F) :
    SmithRegenerative.Equilibrium.IsCycleLaw F ∧
      SmithRegenerative.Equilibrium.IsAperiodic F := by
  constructor
  · refine ⟨inferInstance, hSupport, ?_⟩
    intro h
    rw [h] at hPositiveMean
    simp at hPositiveMean
  · rintro ⟨d, hd, hmass⟩
    apply hnl d hd
    let S : Set Real := {x | ∃ n : Nat, x = (n : Real) * d}
    have hs : S = Set.range (fun n : Nat => (n : Real) * d) := by
      ext x
      simp [S, eq_comm]
    have hsm : MeasurableSet S := by
      rw [hs]
      exact (Set.countable_range _).measurableSet
    have hc : F Sᶜ = 0 := by
      rw [measure_compl hsm (measure_ne_top F S), show F S = 1 from hmass]
      simp
    apply measure_mono_null _ hc
    intro x hx hn
    obtain ⟨n, hn⟩ := hn
    exact hx (n : Int) (by simpa using hn)
