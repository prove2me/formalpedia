-- Prove2me | solution 1 for HardyLittlewoodMaximal.weakType_one_one_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:21:17.300637+00:00
-- url     : https://prove2.me/submissions/f95fab4e-ed8c-42ef-a358-2e7a51979f65

import Mathlib
import Definitions.Def_DbarRegularity_Setting

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hf : Integrable f volume) (α : ℝ) (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < DbarRegularity.maximalFunction f x} ≤
      ENNReal.ofReal (3 ^ d / α) * ∫⁻ x, ‖f x‖ₑ := by
  classical
  -- The measure `ν = |f| dx`; its total mass is the `L¹` norm of `f`.
  let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity (fun x ↦ ‖f x‖ₑ)
  have hνapply : ∀ s : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet s →
      ν s = ∫⁻ y in s, ‖f y‖ₑ := fun s hs ↦ withDensity_apply _ hs
  have hnorm : ν Set.univ = ∫⁻ x, ‖f x‖ₑ := by
    rw [hνapply _ MeasurableSet.univ, setLIntegral_univ]
  have htotal : ν Set.univ ≠ ∞ := by
    rw [hnorm]
    exact hf.hasFiniteIntegral.ne
  -- Balls are indexed by (centre, radius); the good balls are those on which the average of
  -- `|f|` exceeds `α`.
  let good : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
    {p | 0 < p.2 ∧ ENNReal.ofReal α * volume (ball p.1 p.2) < ν (ball p.1 p.2)}
  -- Every point of the superlevel set is the centre of a good ball.
  have hgood : ∀ x, ENNReal.ofReal α < DbarRegularity.maximalFunction f x →
      ∃ r, (x, r) ∈ good := by
    intro x hx
    unfold DbarRegularity.maximalFunction at hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hx
    obtain ⟨hr0, hr⟩ := lt_iSup_iff.mp hr
    refine ⟨r, hr0, ?_⟩
    change ENNReal.ofReal α * volume (ball x r) < ν (ball x r)
    rw [hνapply _ measurableSet_ball]
    rw [mul_comm, ← div_eq_mul_inv] at hr
    exact ENNReal.mul_lt_of_lt_div hr
  -- The threefold enlargement of a good ball has volume at most `(3^d/α) ν(ball)`.
  have henlarged : ∀ p ∈ good, volume (ball p.1 (3 * p.2)) ≤
      ENNReal.ofReal (3 ^ d / α) * ν (ball p.1 p.2) := by
    intro p hp
    have h1 : volume (ball p.1 (3 * p.2)) = ENNReal.ofReal (3 ^ d) * volume (ball p.1 p.2) := by
      rw [Measure.addHaar_ball_mul_of_pos volume p.1 (by norm_num : (0 : ℝ) < 3) p.2,
        finrank_euclideanSpace_fin, Measure.addHaar_ball_center volume p.1 p.2]
    have h2 : ENNReal.ofReal (3 ^ d) = ENNReal.ofReal (3 ^ d / α) * ENNReal.ofReal α := by
      rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hα.ne']
    rw [h1, h2, mul_assoc]
    exact mul_le_mul' le_rfl hp.2.le
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: the space is a point, and any good ball is the whole space.
    by_cases hS : {x | ENNReal.ofReal α < DbarRegularity.maximalFunction f x} = ∅
    · rw [hS, measure_empty]
      exact bot_le
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS
      obtain ⟨r, hr⟩ := hgood x hx
      have hsub : {x | ENNReal.ofReal α < DbarRegularity.maximalFunction f x} ⊆
          ball x (3 * r) := by
        intro y _
        have hyx : y = x := by
          ext i
          exact absurd i.2 (by omega)
        rw [hyx]
        exact mem_ball_self (mul_pos (by norm_num) hr.1)
      calc
        volume {x | ENNReal.ofReal α < DbarRegularity.maximalFunction f x}
            ≤ volume (ball x (3 * r)) := measure_mono hsub
        _ ≤ ENNReal.ofReal (3 ^ d / α) * ν (ball x r) := henlarged (x, r) hr
        _ ≤ ENNReal.ofReal (3 ^ d / α) * ν Set.univ :=
            mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
        _ = ENNReal.ofReal (3 ^ d / α) * ∫⁻ x, ‖f x‖ₑ := by rw [hnorm]
  · -- `d ≥ 1`: the radii of the good balls are bounded, because `ν` is a finite measure.
    have hv1pos : 0 < volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      measure_ball_pos _ _ one_pos
    have hv1top : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ∞ := measure_ball_lt_top.ne
    have hv1r : 0 < (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
      ENNReal.toReal_pos hv1pos.ne' hv1top
    have hbounded : ∀ p ∈ good, p.2 ≤ max 1 ((ν Set.univ).toReal /
        (α * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) := by
      intro p hp
      have hpos : 0 < p.2 := hp.1
      by_cases h1 : p.2 ≤ 1
      · exact h1.trans (le_max_left _ _)
      · have h1 : 1 < p.2 := not_le.mp h1
        refine le_trans ?_ (le_max_right _ _)
        have hvol : volume (ball p.1 p.2) =
            ENNReal.ofReal (p.2 ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
          rw [Measure.addHaar_ball_of_pos volume p.1 hpos, finrank_euclideanSpace_fin]
        have hle := ENNReal.toReal_mono htotal
          (hp.2.le.trans (measure_mono (Set.subset_univ _)))
        rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le,
          ENNReal.toReal_ofReal (by positivity)] at hle
        rw [le_div_iff₀ (by positivity)]
        have hpow : p.2 ≤ p.2 ^ d := le_self_pow₀ h1.le hd.ne'
        calc
          p.2 * (α * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
              ≤ p.2 ^ d * (α * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal) :=
                mul_le_mul_of_nonneg_right hpow (by positivity)
          _ = α * (p.2 ^ d * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal) := by ring
          _ ≤ (ν Set.univ).toReal := hle
    -- Vitali selection: a disjoint subfamily such that every good ball meets a selected
    -- ball of at least half its radius.
    obtain ⟨u, hug, hdisjoint, hintersects⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement
        (fun p : EuclideanSpace ℝ (Fin d) × ℝ ↦ ball p.1 p.2) good Prod.snd 2
        one_lt_two (fun p hp ↦ hp.1.le) _ hbounded
        (fun p hp ↦ ⟨p.1, mem_ball_self hp.1⟩)
    have hcount : u.Countable := hdisjoint.countable_of_isOpen (fun p _ ↦ isOpen_ball)
      (fun p hp ↦ ⟨p.1, mem_ball_self (hug hp).1⟩)
    have : Countable u := hcount.to_subtype
    -- The superlevel set is covered by the threefold enlargements of the selected balls.
    have hcover : {x | ENNReal.ofReal α < DbarRegularity.maximalFunction f x} ⊆
        ⋃ p : u, ball p.val.1 (3 * p.val.2) := by
      intro x hx
      obtain ⟨r, hr⟩ := hgood x hx
      obtain ⟨p, hp, ⟨y, hy₁, hy₂⟩, hrad⟩ := hintersects (x, r) hr
      refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
      have hy₁' : dist y x < r := hy₁
      have hy₂' : dist y p.1 < p.2 := hy₂
      have hrad' : r ≤ 2 * p.2 := hrad
      rw [mem_ball]
      calc
        dist x p.1 ≤ dist x y + dist y p.1 := dist_triangle _ _ _
        _ < r + p.2 := by
            rw [dist_comm x y]
            exact add_lt_add hy₁' hy₂'
        _ ≤ 3 * p.2 := by linarith
    -- Disjointness: the selected balls carry total `ν`-mass at most `ν(ℝ^d)`.
    have hsum : (∑' p : u, ν (ball p.val.1 p.val.2)) ≤ ν Set.univ := by
      rw [← measure_iUnion (hdisjoint.on_injective Subtype.val_injective Subtype.property)
        (fun _ ↦ measurableSet_ball)]
      exact measure_mono (Set.subset_univ _)
    calc
      volume {x | ENNReal.ofReal α < DbarRegularity.maximalFunction f x}
          ≤ volume (⋃ p : u, ball p.val.1 (3 * p.val.2)) := measure_mono hcover
      _ ≤ ∑' p : u, volume (ball p.val.1 (3 * p.val.2)) := measure_iUnion_le _
      _ ≤ ∑' p : u, ENNReal.ofReal (3 ^ d / α) * ν (ball p.val.1 p.val.2) :=
          ENNReal.tsum_le_tsum (fun p ↦ henlarged p.val (hug p.property))
      _ = ENNReal.ofReal (3 ^ d / α) * ∑' p : u, ν (ball p.val.1 p.val.2) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (3 ^ d / α) * ν Set.univ := mul_le_mul' le_rfl hsum
      _ = ENNReal.ofReal (3 ^ d / α) * ∫⁻ x, ‖f x‖ₑ := by rw [hnorm]
