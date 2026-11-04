-- Prove2me | solution 1 for Grothendieck.integrable_kernel_subst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:51:03.414619+00:00
-- url     : https://prove2.me/submissions/f3872d66-2fdb-454e-a217-8be6e9674172

import Mathlib
import Definitions.Def_Grothendieck_Fubini

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped Real Topology ENNReal

namespace Grothendieck

noncomputable section

/-- **One-dimensional majorant.** `x ↦ (1 + x²)^{-M}` is integrable on `(0,∞)` for `M > 1/2`.

Compared with `x^{-2M}` on `(1,∞)` and bounded by `1` on `(0,1]`. -/
theorem integrableOn_one_add_sq_rpow_neg {M : ℝ} (hM : 1 / 2 < M) :
    IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (0 : ℝ)) := by
  have hMpos : (0:ℝ) < M := lt_trans (by norm_num) hM
  have hcont : ContinuousOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (0 : ℝ)) :=
    (by fun_prop : ContinuousOn (fun x : ℝ => 1 + x ^ 2) (Set.Ioi (0:ℝ))).rpow_const
      (fun x _ => Or.inl (by nlinarith))
  have hcontIoc : ContinuousOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioc (0:ℝ) 1) :=
    hcont.mono (fun x hx => hx.1)
  have hcontIoi : ContinuousOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (1:ℝ)) :=
    hcont.mono (fun x hx => lt_trans (by norm_num : (0:ℝ) < 1) hx)
  have hleft : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioc (0:ℝ) 1) := by
    have hmeas : Measurable fun x : ℝ => (1 + x ^ 2) ^ (-M) := by fun_prop
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : (0:ℝ) ≤ x := le_of_lt hx.1
    have hone : (1:ℝ) ≤ 1 + x ^ 2 := by nlinarith
    have hnonneg : (0:ℝ) < 1 + x ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnonneg _)]
    have := Real.rpow_le_one_of_one_le_of_nonpos hone (neg_nonpos.mpr (le_of_lt hMpos))
    simpa using this
  have hright : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioi (1:ℝ)) := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ (-(2 * M))) (Set.Ioi (1:ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono_nonneg hbase ?_ ?_ ?_
    · exact hcontIoi.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
      exact le_of_lt (Real.rpow_pos_of_pos hpos _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := by linarith
      have hx2 : (0:ℝ) < x ^ 2 := by positivity
      have hle : x ^ 2 ≤ 1 + x ^ 2 := by linarith
      have hstep : (1 + x ^ 2) ^ (-M) ≤ (x ^ 2) ^ (-M) :=
        Real.rpow_le_rpow_of_nonpos hx2 hle (neg_nonpos.mpr hMpos.le)
      rw [← Real.rpow_natCast_mul (le_of_lt hx0) 2 (-M),
        show ((2:ℕ) : ℝ) * -M = -(2 * M) by push_cast; ring] at hstep
      exact hstep
  have hunion : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ)) :=
    hleft.union hright
  have hset : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext x
    constructor
    · rintro (⟨h0, _⟩ | h1)
      · exact h0
      · exact lt_trans (by norm_num : (0:ℝ) < 1) h1
    · intro hx
      rcases le_or_gt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  rwa [hset] at hunion

/-- **Separable domination for the substituted kernel.** For `M > 1/2` and `0 ≤ σ < 1` the
substituted Laplace kernel `((1+u²)(1+v²) - σ u²v²)^{-M}` is integrable on the open quadrant.

The pointwise estimate behind it is
`(1+u²)(1+v²) - σ u² v² = (1-σ)(1+u²)(1+v²) + σ(1+u²+v²) ≥ (1-σ)(1+u²)(1+v²)`,
so the kernel is dominated by `(1-σ)^{-M} g(u) g(v)` with `g(x) = (1+x²)^{-M}`. -/
theorem integrable_plane_kernel_subst_gen {M σ : ℝ} (hM : 1 / 2 < M) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Integrable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)) planeMeasure := by
  have hMpos : (0 : ℝ) < M := lt_trans (by norm_num) hM
  have ht2 : (0 : ℝ) < 1 - σ := by linarith
  -- the one-dimensional majorant is integrable, hence so is the product majorant
  have hg : Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-M)) (volume.restrict (Set.Ioi (0:ℝ))) :=
    integrableOn_one_add_sq_rpow_neg hM
  have hB : Integrable (fun p : ℝ × ℝ => (1 - σ) ^ (-M) *
      ((1 + p.1 ^ 2) ^ (-M) * (1 + p.2 ^ 2) ^ (-M))) planeMeasure := by
    have h := (hg.mul_prod hg).const_mul ((1 - σ) ^ (-M))
    simpa [planeMeasure] using h
  -- almost every point of `planeMeasure` lies in the open quadrant
  have hae : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
    rw [planeMeasure, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact hp
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)) planeMeasure := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  refine Integrable.mono' hB hmeas ?_
  filter_upwards [hae] with p hp
  have hp1 : (0:ℝ) < p.1 := hp.1
  have hp2 : (0:ℝ) < p.2 := hp.2
  have ha : (0:ℝ) ≤ p.1 ^ 2 := sq_nonneg p.1
  have hb : (0:ℝ) ≤ p.2 ^ 2 := sq_nonneg p.2
  have h1a : (0:ℝ) < 1 + p.1 ^ 2 := by linarith
  have h1b : (0:ℝ) < 1 + p.2 ^ 2 := by linarith
  have hkey : (1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2
      = (1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2) + σ * (1 + p.1 ^ 2 + p.2 ^ 2) := by
    ring
  have hKge : (1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2) ≤
      (1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2 := by
    rw [hkey]
    nlinarith
  have hApos : (0:ℝ) < (1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2) :=
    mul_pos (mul_pos ht2 h1a) h1b
  have hKpos : (0:ℝ) < (1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2 :=
    lt_of_lt_of_le hApos hKge
  have hpow_le : ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M) ≤
      ((1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2)) ^ (-M) :=
    Real.rpow_le_rpow_of_nonpos hApos hKge (neg_nonpos.mpr hMpos.le)
  have hpow_split : ((1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2)) ^ (-M)
      = (1 - σ) ^ (-M) * ((1 + p.1 ^ 2) ^ (-M) * (1 + p.2 ^ 2) ^ (-M)) := by
    rw [Real.mul_rpow (le_of_lt (mul_pos ht2 h1a)) (le_of_lt h1b),
      Real.mul_rpow (le_of_lt ht2) (le_of_lt h1a)]
    ring
  have hnorm : ‖((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)‖
      = ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hKpos _)]
  rw [hnorm]
  calc ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - σ * p.1 ^ 2 * p.2 ^ 2) ^ (-M)
      ≤ ((1 - σ) * (1 + p.1 ^ 2) * (1 + p.2 ^ 2)) ^ (-M) := hpow_le
    _ = (1 - σ) ^ (-M) * ((1 + p.1 ^ 2) ^ (-M) * (1 + p.2 ^ 2) ^ (-M)) := hpow_split

/-- **The target.** The substituted Laplace kernel of Lemma 2.1 is integrable on the open
quadrant: for `r ≥ 2` and `τ² < 1`,

`p ↦ ((1 + p.1²)(1 + p.2²) - τ² p.1² p.2²) ^ (-((r+2)/2))`

is integrable for `Grothendieck.planeMeasure`. -/
theorem integrable_kernel_subst_proof (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hM : (1 : ℝ) / 2 < ((r : ℝ) + 2) / 2 := by linarith
  exact integrable_plane_kernel_subst_gen (M := ((r : ℝ) + 2) / 2) (σ := τ ^ 2) hM
    (sq_nonneg τ) hτ

end

end Grothendieck


open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    Integrable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure :=
  integrable_kernel_subst_proof r hr hτ
