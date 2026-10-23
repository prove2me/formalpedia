-- Prove2me | solution 1 for NelderMeadLD.Conv1D.lemma_4_2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:41:33.297831+00:00
-- url     : https://prove2.me/submissions/89073230-438c-4195-800b-d845c052455e

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology


namespace NelderMeadLD.Conv1D

lemma g55_run_succ (f : ℝ → ℝ) (ρ χ γ σ : ℝ) (p0 : ℝ × ℝ) (k : ℕ) :
    run f ρ χ γ σ p0 (k+1) = step f ρ χ γ σ (run f ρ χ γ σ p0 k) := by
  simp only [run]; rw [Function.iterate_succ_apply']

lemma g55_H1 {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (x z t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t * (z - x)) ≤ (1 - t) * f x + t * f z := by
  have := hf.2 (Set.mem_univ x) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at this
  have e : x + t * (z - x) = (1 - t) * x + t * z := by ring
  rw [e]; exact this

lemma g55_H2 {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) (x z t : ℝ) (hxz : x ≠ z)
    (ht0 : 0 < t) (ht1 : t < 1) :
    f (x + t * (z - x)) < (1 - t) * f x + t * f z := by
  have := hf.2 (Set.mem_univ x) (Set.mem_univ z) hxz (by linarith : (0:ℝ) < 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at this
  have e : x + t * (z - x) = (1 - t) * x + t * z := by ring
  rw [e]; exact this

section moves
variable {f : ℝ → ℝ} {ρ χ γ σ : ℝ} {p : ℝ × ℝ}

lemma g55_mv_R (h : move f ρ χ γ p = Move.reflect) :
    f (xr ρ p) < f p.1 ∧ ¬ f (xe ρ χ p) < f (xr ρ p) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g55_mv_E (h : move f ρ χ γ p = Move.expand) :
    f (xr ρ p) < f p.1 ∧ f (xe ρ χ p) < f (xr ρ p) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g55_mv_O (h : move f ρ χ γ p = Move.outside) :
    ¬ f (xr ρ p) < f p.1 ∧ f (xr ρ p) < f p.2 ∧ f (xc ρ γ p) ≤ f (xr ρ p) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g55_mv_I (h : move f ρ χ γ p = Move.inside) :
    ¬ f (xr ρ p) < f p.1 ∧ ¬ f (xr ρ p) < f p.2 ∧ f (xcc γ p) < f p.2 := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g55_mv_S (h : move f ρ χ γ p = Move.shrink) :
    (¬ f (xr ρ p) < f p.1 ∧ f (xr ρ p) < f p.2 ∧ ¬ f (xc ρ γ p) ≤ f (xr ρ p)) ∨
    (¬ f (xr ρ p) < f p.1 ∧ ¬ f (xr ρ p) < f p.2 ∧ ¬ f (xcc γ p) < f p.2) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g55_step_R (h : move f ρ χ γ p = Move.reflect) :
    step f ρ χ γ σ p = (xr ρ p, p.1) := by
  have h' := g55_mv_R h
  show place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) = _
  rw [h]; simp [acceptedPoint, place, h'.1]

lemma g55_step_E (h : move f ρ χ γ p = Move.expand) :
    step f ρ χ γ σ p = (xe ρ χ p, p.1) := by
  have h' := g55_mv_E h
  show place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) = _
  rw [h]; simp [acceptedPoint, place, h'.2.trans h'.1]

lemma g55_step_O (h : move f ρ χ γ p = Move.outside) :
    step f ρ χ γ σ p = place f p.1 (xc ρ γ p) := by
  show place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) = _
  rw [h]; simp [acceptedPoint]

lemma g55_step_I (h : move f ρ χ γ p = Move.inside) :
    step f ρ χ γ σ p = place f p.1 (xcc γ p) := by
  show place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) = _
  rw [h]; simp [acceptedPoint]

end moves

section inv
variable {f : ℝ → ℝ} {ρ χ γ σ : ℝ} {p0 : ℝ × ℝ}

lemma g55_acc_ne (hpar : ParamsOK ρ χ γ σ) (p : ℝ × ℝ) (hp : p.1 ≠ p.2) (mv : Move) :
    acceptedPoint ρ χ γ σ p mv ≠ p.1 := by
  obtain ⟨hρ, hχ, -, hγ, -, hσ, -⟩ := hpar
  have hd : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hd' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hp.symm
  cases mv <;> simp only [acceptedPoint, xr, xe, xc, xcc, xsh] <;> intro h
  · apply mul_ne_zero (show ρ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show ρ * χ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show ρ * γ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show γ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show σ ≠ 0 by positivity) hd'; linarith

lemma g55_place_inv (x1 v : ℝ) (h : v ≠ x1) :
    (place f x1 v).1 ≠ (place f x1 v).2 ∧ f (place f x1 v).1 ≤ f (place f x1 v).2 := by
  unfold place; split_ifs with hh
  · exact ⟨h, hh.le⟩
  · exact ⟨Ne.symm h, not_lt.1 hh⟩

lemma g55_inv (hpar : ParamsOK ρ χ γ σ) (h0 : IsStart f p0) (k : ℕ) :
    (run f ρ χ γ σ p0 k).1 ≠ (run f ρ χ γ σ p0 k).2 ∧
      f (run f ρ χ γ σ p0 k).1 ≤ f (run f ρ χ γ σ p0 k).2 := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [g55_run_succ]
    exact g55_place_inv _ _ (g55_acc_ne hpar _ ih.1 _)

lemma g55_noS_state (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK ρ χ γ σ) (p : ℝ × ℝ)
    (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) : move f ρ χ γ p ≠ Move.shrink := by
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  intro h
  rcases g55_mv_S h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · apply h3
    have := g55_H1 hf.convexOn p.1 (xr ρ p) γ hγ.le hγ1.le
    have e : xc ρ γ p = p.1 + γ * (xr ρ p - p.1) := by simp only [xc, xr]; ring
    rw [e]; push_neg at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - γ)]
  · apply h3
    have := g55_H2 hf p.1 p.2 γ hp hγ hγ1
    have e : xcc γ p = p.1 + γ * (p.2 - p.1) := by simp only [xcc]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hle (by linarith : (0:ℝ) ≤ 1 - γ)]

theorem lemma_3_5_one_dim_core (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∀ k : ℕ, move f ρ χ γ (run f ρ χ γ σ p0 k) ≠ Move.shrink := fun k =>
  g55_noS_state hf hpar _ (g55_inv hpar h0 k).1 (g55_inv hpar h0 k).2

end inv

namespace G55Cex

noncomputable def fc (t : ℝ) : ℝ := t ^ 2 + max (t / 20) (-t)

lemma fc_neg {t : ℝ} (h : t ≤ 0) : fc t = t ^ 2 - t := by
  unfold fc; rw [max_eq_right (by linarith)]; ring

lemma fc_pos {t : ℝ} (h : 0 ≤ t) : fc t = t ^ 2 + t / 20 := by
  unfold fc; rw [max_eq_left (by linarith)]

lemma fc_sc : StrictConvexOn ℝ Set.univ fc := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  simp only [smul_eq_mul, fc]
  have hsq : (a * x + b * y) ^ 2 < a * x ^ 2 + b * y ^ 2 := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    have : 0 < (x - y) ^ 2 := by have := sub_ne_zero.mpr hxy; positivity
    nlinarith [mul_pos ha hb]
  have hmax : max ((a * x + b * y) / 20) (-(a * x + b * y)) ≤
      a * max (x / 20) (-x) + b * max (y / 20) (-y) := by
    apply max_le
    · nlinarith [le_max_left (x/20) (-x), le_max_left (y/20) (-y)]
    · nlinarith [le_max_right (x/20) (-x), le_max_right (y/20) (-y)]
  nlinarith

lemma fc_nonneg (t : ℝ) : 0 ≤ max (t / 20) (-t) := by
  rcases le_total 0 t with h | h
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)

lemma fc_lev (μ : ℝ) : Bornology.IsBounded {x | fc x ≤ μ} := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨|μ| + 1, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, fc] at hx
  have := fc_nonneg x
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra hc; push_neg at hc
  have h1 : 1 ≤ |x| := by linarith [abs_nonneg μ]
  have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith [le_abs_self μ]

lemma fc_min (y : ℝ) : fc 0 ≤ fc y := by
  have := fc_nonneg y
  simp only [fc]; norm_num; nlinarith [sq_nonneg y]

lemma fc_par : ParamsOK (1/10) 10 (1/2) (1/2) := by
  unfold ParamsOK; norm_num

lemma fc_state (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    move fc (1/10) 10 (1/2) (-s, -(10 * s)) = Move.reflect ∧
    step fc (1/10) 10 (1/2) (1/2) (-s, -(10 * s)) = (-(s/10), -(10 * (s / 10))) ∧
    ¬ Bracketed (1/10) 10 fc (-s, -(10 * s)) := by
  have exr : xr (1/10) (-s, -(10 * s)) = -(s/10) := by simp only [xr]; ring
  have exe : xe (1/10) 10 (-s, -(10 * s)) = 8 * s := by simp only [xe]; ring
  have f1 : fc (-s) = s ^ 2 + s := by rw [fc_neg (by linarith)]; ring
  have f2 : fc (-(10 * s)) = 100 * s ^ 2 + 10 * s := by rw [fc_neg (by linarith)]; ring
  have fr : fc (-(s/10)) = s ^ 2 / 100 + s / 10 := by rw [fc_neg (by linarith)]; ring
  have fe : fc (8 * s) = 64 * s ^ 2 + 2 * s / 5 := by rw [fc_pos (by linarith)]; ring
  have hmv : move fc (1/10) 10 (1/2) (-s, -(10 * s)) = Move.reflect := by
    have c1 : fc (xr (1/10) (-s, -(10 * s))) < fc (-s, -(10 * s)).1 := by
      rw [exr]; simp only; rw [fr, f1]; nlinarith
    have c2 : ¬ fc (xe (1/10) 10 (-s, -(10 * s))) < fc (xr (1/10) (-s, -(10 * s))) := by
      rw [exe, exr, fe, fr]; nlinarith
    unfold move
    rw [if_pos c1, if_neg c2]
  refine ⟨hmv, ?_, ?_⟩
  · rw [g55_step_R hmv, exr]; show (-(s/10), -s) = _; congr 1; ring
  · unfold Bracketed; rw [exe]; simp only; rw [f1, fe]; intro h; nlinarith [h.2]

lemma fc_run (k : ℕ) : ∃ s : ℝ, 0 < s ∧ s ≤ 1/1000 ∧
    run fc (1/10) 10 (1/2) (1/2) (-(1/1000), -(10 * (1/1000))) k = (-s, -(10 * s)) := by
  induction k with
  | zero => exact ⟨1/1000, by norm_num, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨s, hs, hs1, he⟩ := ih
    refine ⟨s / 10, by positivity, by linarith, ?_⟩
    rw [g55_run_succ, he, (fc_state s hs hs1).2.1]

end G55Cex

open G55Cex in
theorem lemma_4_2_false : ¬ (∀ (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ),
    ∃ K : ℕ, Bracketed ρ χ f (run f ρ χ γ σ p0 K) ∧
      (∀ j < K, ¬ Bracketed ρ χ f (run f ρ χ γ σ p0 j)) ∧
      min (run f ρ χ γ σ p0 K).2 (xe ρ χ (run f ρ χ γ σ p0 K)) < xmin ∧
      xmin < max (run f ρ χ γ σ p0 K).2 (xe ρ χ (run f ρ χ γ σ p0 K))) := by
  intro H
  have h0 : IsStart fc (-(1/1000), -(10 * (1/1000))) := by
    refine ⟨by norm_num, ?_⟩
    simp only; rw [fc_neg (by norm_num), fc_neg (by norm_num)]; norm_num
  obtain ⟨K, hK, -⟩ := H fc fc_sc fc_lev 0 fc_min (1/10) 10 (1/2) (1/2) fc_par _ h0 (by norm_num)
  obtain ⟨s, hs, hs1, he⟩ := fc_run K
  rw [he] at hK
  exact (fc_state s hs hs1).2.2 hK

end NelderMeadLD.Conv1D

open NelderMeadLD.Conv1D


theorem solution : ¬ (∀ (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ),
    ∃ K : ℕ, Bracketed ρ χ f (run f ρ χ γ σ p0 K) ∧
      (∀ j < K, ¬ Bracketed ρ χ f (run f ρ χ γ σ p0 j)) ∧
      min (run f ρ χ γ σ p0 K).2 (xe ρ χ (run f ρ χ γ σ p0 K)) < xmin ∧
      xmin < max (run f ρ χ γ σ p0 K).2 (xe ρ χ (run f ρ χ γ σ p0 K))) := by
  exact lemma_4_2_false
