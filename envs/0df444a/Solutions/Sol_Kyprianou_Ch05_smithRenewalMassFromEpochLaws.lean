-- Prove2me | solution 1 for Kyprianou.Ch05.smithRenewalMassFromEpochLaws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:05:59.332948+00:00
-- url     : https://prove2.me/submissions/236b4cc2-68bc-4da9-b4b9-89af220244c2

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

/-- The renewal measure on [0,t] equals one plus Smith's expected number of positive-index renewal epochs. Infinite counts are included. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Nat → Omega → Real) (F : Measure Real)
    (hX : IsRenewalProcess P X)
    (hLaw : ∀ n, Measure.map (S X n) P = renewalConvolutionPower F n)
    (t : Real) (ht : 0 ≤ t) :
    renewalMeasure F (Set.Icc 0 t) = 1 + H X P t := by
  classical
  have hm (i : Nat) : Measurable (S X i) := by
    unfold S
    exact Finset.measurable_sum _ fun j _ => hX.measurable j
  let I : Nat → Omega → ENNReal := fun i w => if S X i w ≤ t then 1 else 0
  have hI (i : Nat) : Measurable (I i) :=
    Measurable.ite (measurableSet_le (hm i) measurable_const)
      measurable_const measurable_const
  have hmass (i : Nat) : renewalConvolutionPower F i (Set.Icc 0 t) =
      ∫⁻ w, I i w ∂P := by
    rw [← hLaw i, Measure.map_apply (hm i) measurableSet_Icc]
    have he : (S X i) ⁻¹' Set.Icc 0 t = {w | S X i w ≤ t} := by
      ext w
      have hn : 0 ≤ S X i w := Finset.sum_nonneg fun j _ => hX.nonneg j w
      simp [hn]
    rw [he]
    have hmeas : MeasurableSet {w | S X i w ≤ t} :=
      measurableSet_le (hm i) measurable_const
    have he' : I i = ({w | S X i w ≤ t} : Set Omega).indicator (fun _ => 1) := by
      funext w
      simp [I, Set.indicator]
    rw [he', lintegral_indicator hmeas]
    simp
  have hocc (w : Omega) : (∑' i, I i w) = 1 + (N X t w : ENNReal) := by
    have hs : {i : Nat | S X i w ≤ t} =
        insert 0 {i : Nat | 1 ≤ i ∧ S X i w ≤ t} := by
      ext i
      by_cases hi : i = 0
      · subst i; simp [S, ht]
      · simp [hi, Nat.one_le_iff_ne_zero.mpr hi]
    have hc : (∑' i, I i w) = ({i : Nat | S X i w ≤ t}.encard : ENNReal) := by
      rw [← ENNReal.tsum_set_one]
      have hh := tsum_subtype {i : Nat | S X i w ≤ t} (fun _ : Nat => (1 : ENNReal))
      exact hh.symm
    rw [hc, hs, Set.encard_insert_of_notMem (by simp)]
    simp [N, add_comm]
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Icc]
  simp_rw [hmass]
  rw [← lintegral_tsum (fun i => (hI i).aemeasurable)]
  simp_rw [hocc]
  rw [lintegral_add_left measurable_const]
  simp [H]
