-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing_general
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:21:18.583849+00:00
-- url     : https://prove2.me/submissions/5daaea67-e470-49bc-a5e9-90f5c6cdd405

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

open scoped BigOperators Topology ENNReal
open MeasureTheory

theorem solution (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ R}) =
    ∫ t in (0 : ℝ)..R, ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ R - t}) := by
  -- The simplex after separating its first coordinate.
  let P : Set (ℝ × (Fin n → ℝ)) :=
    {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + ∑ i, p.2 i ≤ R}
  have hsum : Continuous (fun p : ℝ × (Fin n → ℝ) => ∑ i, p.2 i) :=
    continuous_finsetSum Finset.univ
      (fun i _ => (continuous_apply i).comp continuous_snd)
  have hnonneg : MeasurableSet
      {p : ℝ × (Fin n → ℝ) | ∀ i, 0 ≤ p.2 i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
  have hP : MeasurableSet P :=
    (measurableSet_le measurable_const measurable_fst).inter
      (hnonneg.inter
        (measurableSet_le (continuous_fst.add hsum).measurable measurable_const))
  -- All coordinates lie in [0,R], so this measurable set has finite volume.
  have hbound : P ⊆ Set.Icc ((0 : ℝ), (0 : Fin n → ℝ))
      (R, fun _ => R) := by
    intro p hp
    rcases hp with ⟨ht, hx, hs⟩
    have hsum0 : 0 ≤ ∑ i, p.2 i := Finset.sum_nonneg fun i _ => hx i
    refine ⟨⟨ht, hx⟩, ⟨?_, ?_⟩⟩
    · linarith
    · intro i
      have hi : p.2 i ≤ ∑ j, p.2 j :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      linarith
  have hfinite : volume P ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono hbound) isCompact_Icc.measure_lt_top).ne
  let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have heS : e ⁻¹' P =
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R} := by
    ext x
    change (0 ≤ x 0 ∧ (∀ i : Fin n, 0 ≤ x i.succ) ∧
        x 0 + ∑ i : Fin n, x i.succ ≤ R) ↔
      ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R)
    simp only [Fin.forall_fin_succ, Fin.sum_univ_succ, and_assoc]
  have hvol : volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R} = volume P := by
    rw [← heS]
    exact he.measure_preimage_equiv P
  -- Tonelli for sets, followed by conversion from extended to real integrals.
  have hslice : (volume P).toReal =
      ∫ t : ℝ, (volume (Prod.mk t ⁻¹' P)).toReal := by
    calc
      (volume P).toReal =
          (∫⁻ t : ℝ, volume (Prod.mk t ⁻¹' P)).toReal :=
        congrArg ENNReal.toReal (Measure.prod_apply hP)
      _ = ∫ t : ℝ, (volume (Prod.mk t ⁻¹' P)).toReal :=
        (integral_toReal (measurable_measure_prodMk_left hP).aemeasurable
          (Measure.ae_measure_lt_top hP hfinite)).symm
  have hsupport : ∀ t : ℝ, t ∉ Set.Icc 0 R →
      (volume (Prod.mk t ⁻¹' P)).toReal = 0 := by
    intro t ht
    have hempty : Prod.mk t ⁻¹' P = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases hx with ⟨ht0, hx0, hs⟩
      apply ht
      refine ⟨ht0, ?_⟩
      have hsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx0 i
      linarith
    rw [hempty]
    simp
  have hsection (t : ℝ) (ht : t ∈ Set.Icc 0 R) :
      Prod.mk t ⁻¹' P =
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R - t} := by
    ext x
    change (0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ t + ∑ i, x i ≤ R) ↔
      ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R - t)
    constructor
    · rintro ⟨_, hx, hs⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hs⟩
      exact ⟨ht.1, hx, by linarith⟩
  calc
    (volume {x : Fin (n + 1) → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R}).toReal = (volume P).toReal :=
      congrArg ENNReal.toReal hvol
    _ = ∫ t : ℝ, (volume (Prod.mk t ⁻¹' P)).toReal := hslice
    _ = ∫ t in Set.Icc 0 R, (volume (Prod.mk t ⁻¹' P)).toReal :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
    _ = ∫ t in Set.Icc 0 R, (volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R - t}).toReal := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact congrArg (fun s : Set (Fin n → ℝ) => (volume s).toReal) (hsection t ht)
    _ = ∫ t in (0 : ℝ)..R, (volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ R - t}).toReal := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hR]
