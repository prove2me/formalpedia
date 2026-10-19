-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:30:56.137156+00:00
-- url     : https://prove2.me/submissions/a4d71dac-1ec8-415f-ab4e-58fc1100ec0b

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact

open scoped BigOperators ENNReal
open MeasureTheory

/-- Split the first coordinate, apply Tonelli, and restrict the section integral
    to the interval on which the sections can be nonempty. -/
theorem solution (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ r}).toReal =
      ∫ t in (0 : ℝ)..r,
        (MeasureTheory.volume
          {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ r - t}).toReal := by
  classical
  let S : Set (ℝ × (Fin m → ℝ)) :=
    {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + ∑ i, p.2 i ≤ r}
  have hsum : Measurable (fun p : ℝ × (Fin m → ℝ) => ∑ i : Fin m, p.2 i) :=
    Finset.measurable_sum Finset.univ
      (fun i _ => (measurable_pi_apply i).comp measurable_snd)
  have hnonneg : MeasurableSet
      {p : ℝ × (Fin m → ℝ) | ∀ i, 0 ≤ p.2 i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_fst).inter
      (hnonneg.inter (measurableSet_le (measurable_fst.add hsum) measurable_const))
  have hbounded : S ⊆ Set.Icc (0 : ℝ × (Fin m → ℝ)) (r, fun _ => r) := by
    rintro p ⟨ht, hy, hs⟩
    have hsum0 : 0 ≤ ∑ i : Fin m, p.2 i :=
      Finset.sum_nonneg fun i _ => hy i
    change (0 ≤ p.1 ∧ ∀ i, 0 ≤ p.2 i) ∧ (p.1 ≤ r ∧ ∀ i, p.2 i ≤ r)
    refine ⟨⟨ht, hy⟩, (le_add_of_nonneg_right hsum0).trans hs, ?_⟩
    intro i
    have hi : p.2 i ≤ ∑ j : Fin m, p.2 j :=
      Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i)
    exact hi.trans ((le_add_of_nonneg_left ht).trans hs)
  have hbox : volume (Set.Icc (0 : ℝ × (Fin m → ℝ)) (r, fun _ => r)) < ∞ :=
    isCompact_Icc.measure_lt_top
  have hfinite : volume S ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono hbounded) hbox).ne
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hpre : e ⁻¹' S =
      {x : Fin (m + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ r} := by
    ext x
    change (0 ≤ x 0 ∧ (∀ i : Fin m, 0 ≤ x i.succ) ∧
      x 0 + ∑ i : Fin m, x i.succ ≤ r) ↔
        ((∀ i : Fin (m + 1), 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ r)
    simp only [Fin.sum_univ_succ x, Fin.forall_fin_succ, and_assoc]
  have hvolume :
      volume {x : Fin (m + 1) → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ r} = volume S := by
    rw [← hpre]
    exact he.measure_preimage_equiv S
  have hfubini : (volume S).toReal =
      ∫ t : ℝ, (volume (Prod.mk t ⁻¹' S)).toReal := by
    calc
      (volume S).toReal =
          (∫⁻ t : ℝ, volume (Prod.mk t ⁻¹' S)).toReal := by
        congr 1
        exact Measure.prod_apply hS
      _ = ∫ t : ℝ, (volume (Prod.mk t ⁻¹' S)).toReal :=
        (integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
          (Measure.ae_measure_lt_top hS hfinite)).symm
  have hsupport : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) r →
      (volume (Prod.mk t ⁻¹' S)).toReal = 0 := by
    intro t ht
    have hempty : Prod.mk t ⁻¹' S = ∅ := by
      ext y
      constructor
      · rintro ⟨ht0, hy, hs⟩
        apply False.elim
        apply ht
        exact ⟨ht0, (le_add_of_nonneg_right
          (Finset.sum_nonneg fun i _ => hy i)).trans hs⟩
      · intro hy
        exact False.elim hy
    simp only [hempty, measure_empty, ENNReal.toReal_zero]
  have hsection (t : ℝ) (ht : 0 ≤ t) :
      Prod.mk t ⁻¹' S =
        {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ r - t} := by
    ext y
    change (0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ t + ∑ i, y i ≤ r) ↔
      ((∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ r - t)
    constructor
    · rintro ⟨_, hy, hs⟩
      refine ⟨hy, (le_sub_iff_add_le).2 ?_⟩
      simpa only [add_comm] using hs
    · rintro ⟨hy, hs⟩
      refine ⟨ht, hy, ?_⟩
      simpa only [add_comm] using (le_sub_iff_add_le).1 hs
  calc
    (volume {x : Fin (m + 1) → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ r}).toReal =
        (volume S).toReal := congrArg ENNReal.toReal hvolume
    _ = ∫ t : ℝ, (volume (Prod.mk t ⁻¹' S)).toReal := hfubini
    _ = ∫ t in Set.Icc (0 : ℝ) r, (volume (Prod.mk t ⁻¹' S)).toReal :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
    _ = ∫ t in (0 : ℝ)..r, (volume (Prod.mk t ⁻¹' S)).toReal := by
      rw [intervalIntegral.integral_of_le hr, integral_Icc_eq_integral_Ioc]
    _ = ∫ t in (0 : ℝ)..r,
        (volume {y : Fin m → ℝ |
          (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ r - t}).toReal := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) r := by
        simpa only [Set.uIcc_of_le hr] using ht
      exact congrArg (fun A : Set (Fin m → ℝ) => (volume A).toReal)
        (hsection t ht'.1)