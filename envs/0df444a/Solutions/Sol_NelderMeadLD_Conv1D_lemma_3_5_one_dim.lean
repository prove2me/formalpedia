-- Prove2me | solution 1 for NelderMeadLD.Conv1D.lemma_3_5_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:37:30.363832+00:00
-- url     : https://prove2.me/submissions/9e3112e8-a020-4f39-8ea9-8b37b758323b

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

end NelderMeadLD.Conv1D

open NelderMeadLD.Conv1D


theorem solution (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∀ k : ℕ, move f ρ χ γ (run f ρ χ γ σ p0 k) ≠ Move.shrink := by
  exact lemma_3_5_one_dim_core f hf ρ χ γ σ hpar p0 h0
