-- Prove2me | solution 1 for HardyLittlewoodMaximal.weakType_one_one_real
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:16:10.609075+00:00
-- url     : https://prove2.me/submissions/eff5744e-b292-490c-83c5-6c5e3a28425c

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

theorem solution (f : ℝ → ℂ) (hf : Integrable f volume) (α : ℝ) (hα : 0 < α) :
    volume {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)} ≤
      ENNReal.ofReal (3 / α) * ∫⁻ x, ‖f x‖ₑ := by
  classical
  -- The measure `ν = |f| dx`; its total mass is the `L¹` norm of `f`.
  let ν : Measure ℝ := (volume : Measure ℝ).withDensity (fun x ↦ ‖f x‖ₑ)
  have hνapply : ∀ s : Set ℝ, MeasurableSet s → ν s = ∫⁻ y in s, ‖f y‖ₑ := fun s hs ↦
    withDensity_apply _ hs
  have hnorm : ν Set.univ = ∫⁻ x, ‖f x‖ₑ := by
    rw [hνapply _ MeasurableSet.univ, setLIntegral_univ]
  have htotal : ν Set.univ ≠ ∞ := by
    rw [hnorm]
    exact hf.hasFiniteIntegral.ne
  -- Intervals are indexed by (centre, radius).
  let interval : ℝ × ℝ → Set ℝ := fun p ↦ Set.Ioo (p.1 - p.2) (p.1 + p.2)
  let enlarged : ℝ × ℝ → Set ℝ := fun p ↦ Set.Icc (p.1 - 3 * p.2) (p.1 + 3 * p.2)
  -- The intervals on which the average of `|f|` exceeds `α`.
  let good : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ ENNReal.ofReal (α * (2 * p.2)) < ν (interval p)}
  -- Their radii are bounded, because `ν` is a finite measure.
  have hbounded : ∀ p ∈ good, p.2 ≤ (ν Set.univ).toReal / α := by
    intro p hp
    have hpos : 0 < p.2 := hp.1
    have hle := ENNReal.toReal_mono htotal (hp.2.le.trans (measure_mono (Set.subset_univ _)))
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ α * (2 * p.2))] at hle
    rw [le_div_iff₀ hα]
    nlinarith [mul_nonneg hα.le hpos.le]
  -- Vitali selection: a disjoint subfamily such that every good interval meets a selected
  -- interval of at least half its radius.
  obtain ⟨u, hug, hdisjoint, hintersects⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement interval good Prod.snd 2
      one_lt_two (fun p hp ↦ hp.1.le) ((ν Set.univ).toReal / α) hbounded
      (fun p hp ↦ ⟨p.1, by
        change p.1 - p.2 < p.1 ∧ p.1 < p.1 + p.2
        have := hp.1
        constructor <;> linarith⟩)
  have hcount : u.Countable := hdisjoint.countable_of_isOpen (fun p _ ↦ isOpen_Ioo)
    (fun p hp ↦ by
      change (Set.Ioo (p.1 - p.2) (p.1 + p.2)).Nonempty
      exact Set.nonempty_Ioo.mpr (by linarith [(hug hp).1]))
  have : Countable u := hcount.to_subtype
  -- The superlevel set is covered by the threefold enlargements of the selected intervals.
  have hcover : {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)} ⊆
      ⋃ p : u, enlarged p.val := by
    intro x hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp (show ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r) from hx)
    obtain ⟨hr0, hr⟩ := lt_iSup_iff.mp hr
    have hgood : (x, r) ∈ good := by
      refine ⟨hr0, ?_⟩
      change ENNReal.ofReal (α * (2 * r)) < ν (Set.Ioo (x - r) (x + r))
      rw [hνapply _ measurableSet_Ioo, ENNReal.ofReal_mul hα.le]
      exact ENNReal.mul_lt_of_lt_div hr
    obtain ⟨p, hp, ⟨y, hy₁, hy₂⟩, hrad⟩ := hintersects (x, r) hgood
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    change x - r < y ∧ y < x + r at hy₁
    change p.1 - p.2 < y ∧ y < p.1 + p.2 at hy₂
    change r ≤ 2 * p.2 at hrad
    change p.1 - 3 * p.2 ≤ x ∧ x ≤ p.1 + 3 * p.2
    constructor <;> linarith [hy₁.1, hy₁.2, hy₂.1, hy₂.2]
  -- Each enlargement has length `6 r = (3/α) · (α · 2r) ≤ (3/α) ν(interval)`.
  have henlarged : ∀ p : u, volume (enlarged p.val) ≤
      ENNReal.ofReal (3 / α) * ν (interval p.val) := by
    intro p
    have hlength : p.val.1 + 3 * p.val.2 - (p.val.1 - 3 * p.val.2) =
        (3 / α) * (α * (2 * p.val.2)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hα.ne']
      ring
    change volume (Set.Icc (p.val.1 - 3 * p.val.2) (p.val.1 + 3 * p.val.2)) ≤ _
    rw [Real.volume_Icc, hlength, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl (hug p.property).2.le
  -- Disjointness: the selected intervals carry total `ν`-mass at most `ν(ℝ)`.
  have hsum : (∑' p : u, ν (interval p.val)) ≤ ν Set.univ := by
    rw [← measure_iUnion (hdisjoint.on_injective Subtype.val_injective Subtype.property)
      (fun _ ↦ measurableSet_Ioo)]
    exact measure_mono (Set.subset_univ _)
  calc
    volume {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)}
        ≤ volume (⋃ p : u, enlarged p.val) := measure_mono hcover
    _ ≤ ∑' p : u, volume (enlarged p.val) := measure_iUnion_le _
    _ ≤ ∑' p : u, ENNReal.ofReal (3 / α) * ν (interval p.val) :=
        ENNReal.tsum_le_tsum henlarged
    _ = ENNReal.ofReal (3 / α) * ∑' p : u, ν (interval p.val) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (3 / α) * ν Set.univ := mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (3 / α) * ∫⁻ x, ‖f x‖ₑ := by rw [hnorm]
