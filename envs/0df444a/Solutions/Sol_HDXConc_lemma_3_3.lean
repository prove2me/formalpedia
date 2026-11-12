-- Prove2me | solution 1 for HDXConc.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:08.558226+00:00
-- url     : https://prove2.me/submissions/e0202b69-02e6-4c15-b160-f7da9ee8aeab

import Mathlib
import Definitions.Def_HDXConc_SecondEigLE

section
set_option autoImplicit false
namespace HDXConc.Dev.L33
open HDXConc

variable {V : Type*}

lemma sym_col (W : Finset V) (w : V → V → ℝ) (hsymm : ∀ u ∈ W, ∀ v ∈ W, w u v = w v u)
    (v : V) (hv : v ∈ W) : ∑ u ∈ W, w u v = weightedDeg W w v := by
  unfold weightedDeg
  exact Finset.sum_congr rfl (fun u hu => hsymm u hu v hv)

lemma quad_le (W : Finset V) (w : V → V → ℝ) (hsymm : ∀ u ∈ W, ∀ v ∈ W, w u v = w v u)
    (hnonneg : ∀ u ∈ W, ∀ v ∈ W, 0 ≤ w u v) (k : V → ℝ) :
    ∑ u ∈ W, ∑ v ∈ W, w u v * k u * k v ≤ ∑ v ∈ W, weightedDeg W w v * (k v) ^ 2 := by
  have h1 : ∑ u ∈ W, ∑ v ∈ W, w u v * k u * k v ≤
      ∑ u ∈ W, ∑ v ∈ W, (w u v * k u ^ 2 + w u v * k v ^ 2) / 2 := by
    apply Finset.sum_le_sum; intro u hu
    apply Finset.sum_le_sum; intro v hv
    have := hnonneg u hu v hv
    nlinarith [mul_nonneg this (sq_nonneg (k u - k v))]
  have h2 : ∑ u ∈ W, ∑ v ∈ W, (w u v * k u ^ 2 + w u v * k v ^ 2) / 2 =
      (∑ u ∈ W, weightedDeg W w u * k u ^ 2 + ∑ v ∈ W, weightedDeg W w v * k v ^ 2) / 2 := by
    have e1 : ∑ u ∈ W, ∑ v ∈ W, w u v * k u ^ 2 = ∑ u ∈ W, weightedDeg W w u * k u ^ 2 := by
      apply Finset.sum_congr rfl; intro u _
      unfold weightedDeg; rw [Finset.sum_mul]
    have e2 : ∑ u ∈ W, ∑ v ∈ W, w u v * k v ^ 2 = ∑ v ∈ W, weightedDeg W w v * k v ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro v hv
      rw [← sym_col W w hsymm v hv, Finset.sum_mul]
    simp only [← Finset.sum_div, Finset.sum_add_distrib, e1, e2]
  rw [h2] at h1; linarith

lemma shift_quad (W : Finset V) (w : V → V → ℝ) (hsymm : ∀ u ∈ W, ∀ v ∈ W, w u v = w v u)
    (h : V → ℝ) (s : ℝ) :
    ∑ u ∈ W, ∑ v ∈ W, w u v * (h u + s) * (h v + s) =
      ∑ u ∈ W, ∑ v ∈ W, w u v * h u * h v + 2 * s * ∑ v ∈ W, weightedDeg W w v * h v
        + s ^ 2 * ∑ v ∈ W, weightedDeg W w v := by
  have a1 : ∑ u ∈ W, ∑ v ∈ W, w u v * h u = ∑ v ∈ W, weightedDeg W w v * h v := by
    apply Finset.sum_congr rfl; intro u _
    unfold weightedDeg; rw [Finset.sum_mul]
  have a2 : ∑ u ∈ W, ∑ v ∈ W, w u v * h v = ∑ v ∈ W, weightedDeg W w v * h v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v hv
    rw [← sym_col W w hsymm v hv, Finset.sum_mul]
  have a3 : ∑ u ∈ W, ∑ v ∈ W, w u v = ∑ v ∈ W, weightedDeg W w v := rfl
  have : ∀ u v, w u v * (h u + s) * (h v + s) =
      w u v * h u * h v + s * (w u v * h u) + s * (w u v * h v) + s ^ 2 * w u v := by
    intro u v; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, a1, a2, a3]
  ring

lemma shift_sq (W : Finset V) (w : V → V → ℝ)
    (h : V → ℝ) (s : ℝ) :
    ∑ v ∈ W, weightedDeg W w v * (h v + s) ^ 2 =
      ∑ v ∈ W, weightedDeg W w v * (h v) ^ 2 + 2 * s * ∑ v ∈ W, weightedDeg W w v * h v
        + s ^ 2 * ∑ v ∈ W, weightedDeg W w v := by
  have : ∀ v, weightedDeg W w v * (h v + s) ^ 2 =
      weightedDeg W w v * (h v) ^ 2 + 2 * s * (weightedDeg W w v * h v)
        + s ^ 2 * weightedDeg W w v := by
    intro v; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma deg_g (W : Finset V) (hW : W.Nonempty) (w : V → V → ℝ)
    (hnonneg : ∀ u ∈ W, ∀ v ∈ W, 0 ≤ w u v) (g : V → ℝ) (hg : ∀ v ∈ W, 0 < g v)
    (v : V) (hv : v ∈ W) :
    weightedDeg W w v * g v ^ 2 ≤
      (W.sup' hW g / W.inf' hW g) * weightedDeg W (fun u v => w u v * g u * g v) v := by
  have hmn : 0 < W.inf' hW g := by
    rw [Finset.lt_inf'_iff]; exact hg
  have hM : g v ≤ W.sup' hW g := Finset.le_sup' g hv
  have hm : W.inf' hW g * weightedDeg W w v ≤ ∑ u ∈ W, w v u * g u := by
    unfold weightedDeg; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro u hu
    have := Finset.inf'_le g hu
    have := hnonneg v hv u hu
    nlinarith
  have hd : weightedDeg W (fun u v => w u v * g u * g v) v = g v * ∑ u ∈ W, w v u * g u := by
    unfold weightedDeg; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _; ring
  rw [hd]
  have hdeg0 : 0 ≤ weightedDeg W w v := Finset.sum_nonneg (fun u hu => hnonneg v hv u hu)
  have hgv := hg v hv
  have e : (W.sup' hW g / W.inf' hW g) * W.inf' hW g = W.sup' hW g := by field_simp
  have hr : 0 ≤ W.sup' hW g / W.inf' hW g := by
    have : 0 < W.sup' hW g := lt_of_lt_of_le hgv hM
    positivity
  calc weightedDeg W w v * g v ^ 2 ≤ weightedDeg W w v * g v * W.sup' hW g := by
        have := mul_nonneg hdeg0 hgv.le
        nlinarith
    _ = (W.sup' hW g / W.inf' hW g) * (g v * (W.inf' hW g * weightedDeg W w v)) := by
        linear_combination (-(weightedDeg W w v * g v)) * e
    _ ≤ (W.sup' hW g / W.inf' hW g) * (g v * ∑ u ∈ W, w v u * g u) := by
        apply mul_le_mul_of_nonneg_left _ hr
        exact mul_le_mul_of_nonneg_left hm hgv.le

lemma main (W : Finset V) (hW : W.Nonempty) (w : V → V → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hsymm : ∀ u ∈ W, ∀ v ∈ W, w u v = w v u)
    (hnonneg : ∀ u ∈ W, ∀ v ∈ W, 0 ≤ w u v)
    (hdeg : ∀ v ∈ W, 0 < weightedDeg W w v)
    (g : V → ℝ) (hg : ∀ v ∈ W, 0 < g v)
    (hS : SecondEigLE W w lam) :
    SecondEigLE W (fun u v => w u v * g u * g v) ((W.sup' hW g / W.inf' hW g) * lam) := by
  intro h hh
  set w' : V → V → ℝ := fun u v => w u v * g u * g v with hw'
  set r := W.sup' hW g / W.inf' hW g with hr
  have hsymm' : ∀ u ∈ W, ∀ v ∈ W, w' u v = w' v u := by
    intro u hu v hv; simp only [hw']; rw [hsymm u hu v hv]; ring
  have hnonneg' : ∀ u ∈ W, ∀ v ∈ W, 0 ≤ w' u v := by
    intro u hu v hv; simp only [hw']
    have := hg u hu; have := hg v hv; have := hnonneg u hu v hv
    positivity
  have hD' : 0 ≤ ∑ v ∈ W, weightedDeg W w' v :=
    Finset.sum_nonneg (fun v hv => Finset.sum_nonneg (fun u hu => hnonneg' v hv u hu))
  have hS0 : 0 ≤ ∑ v ∈ W, weightedDeg W w' v * (h v) ^ 2 :=
    Finset.sum_nonneg (fun v hv => mul_nonneg
      (Finset.sum_nonneg (fun u hu => hnonneg' v hv u hu)) (sq_nonneg _))
  by_cases hL : 1 ≤ r * lam
  · have := quad_le W w' hsymm' hnonneg' h
    nlinarith
  · push Not at hL
    have hB : 0 < ∑ v ∈ W, weightedDeg W w v * g v :=
      Finset.sum_pos (fun v hv => mul_pos (hdeg v hv) (hg v hv)) hW
    set A := ∑ v ∈ W, weightedDeg W w v * (g v * h v) with hA
    set B := ∑ v ∈ W, weightedDeg W w v * g v with hB'
    set s := -A / B with hs
    have hk : ∑ v ∈ W, weightedDeg W w v * (g v * (h v + s)) = 0 := by
      have : ∀ v, weightedDeg W w v * (g v * (h v + s)) =
          weightedDeg W w v * (g v * h v) + s * (weightedDeg W w v * g v) := by
        intro v; ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← hA, ← hB', hs]; field_simp; ring
    have h1 := hS (fun v => g v * (h v + s)) hk
    have h2 : ∑ v ∈ W, weightedDeg W w v * (g v * (h v + s)) ^ 2 ≤
        r * ∑ v ∈ W, weightedDeg W w' v * (h v + s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro v hv
      have := deg_g W hW w hnonneg g hg v hv
      have e : weightedDeg W w v * (g v * (h v + s)) ^ 2 =
          (weightedDeg W w v * g v ^ 2) * (h v + s) ^ 2 := by ring
      rw [e, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hq : ∑ u ∈ W, ∑ v ∈ W, w u v * (g u * (h u + s)) * (g v * (h v + s)) =
        ∑ u ∈ W, ∑ v ∈ W, w' u v * (h u + s) * (h v + s) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      simp only [hw']; ring
    have hT : ∑ v ∈ W, weightedDeg W w' v * h v = 0 := hh
    rw [hq] at h1
    rw [shift_quad W w' hsymm' h s, hT] at h1
    have h2' := h2
    rw [shift_sq W w' h s, hT] at h2'
    have hpos : 0 ≤ (1 - r * lam) * (s ^ 2 * ∑ v ∈ W, weightedDeg W w' v) :=
      mul_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hD')
    have h3 : lam * ∑ v ∈ W, weightedDeg W w v * (g v * (h v + s)) ^ 2 ≤
        lam * (r * (∑ v ∈ W, weightedDeg W w' v * (h v) ^ 2 + 2 * s * 0
          + s ^ 2 * ∑ v ∈ W, weightedDeg W w' v)) :=
      mul_le_mul_of_nonneg_left h2' hlam
    nlinarith
end HDXConc.Dev.L33

namespace HDXConc
open HDXConc.Dev.L33 in
theorem chk_lemma_3_3 {V : Type*} (W : Finset V) (hW : W.Nonempty) (w : V → V → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hsymm : ∀ u ∈ W, ∀ v ∈ W, w u v = w v u)
    (hnonneg : ∀ u ∈ W, ∀ v ∈ W, 0 ≤ w u v)
    (hdeg : ∀ v ∈ W, 0 < weightedDeg W w v)
    (g : V → ℝ) (hg : ∀ v ∈ W, 0 < g v)
    (hS : SecondEigLE W w lam) :
    SecondEigLE W (fun u v => w u v * g u * g v) ((W.sup' hW g / W.inf' hW g) * lam) :=
  main W hW w lam hlam hsymm hnonneg hdeg g hg hS
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_lemma_3_3 := @HDXConc.chk_lemma_3_3
