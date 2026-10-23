-- Prove2me | solution 1 for NelderMeadLD.Rate1D.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:22:11.401586+00:00
-- url     : https://prove2.me/submissions/9a265080-d080-4eb5-9c2f-e01da2b82269

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm
import Definitions.Def_NelderMeadLD_Rate1D_Algorithm



namespace NelderMeadLD.Rate1D

open NelderMeadLD.Conv1D

lemma g54_run_succ (f : ℝ → ℝ) (χ γ σ : ℝ) (p0 : ℝ × ℝ) (k : ℕ) :
    run f 1 χ γ σ p0 (k+1) = step f 1 χ γ σ (run f 1 χ γ σ p0 k) := by
  simp only [run]; rw [Function.iterate_succ_apply']

lemma g54_H1 {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (x z t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t * (z - x)) ≤ (1 - t) * f x + t * f z := by
  have := hf.2 (Set.mem_univ x) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at this
  have e : x + t * (z - x) = (1 - t) * x + t * z := by ring
  rw [e]; exact this

lemma g54_H2 {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) (x z t : ℝ) (hxz : x ≠ z)
    (ht0 : 0 < t) (ht1 : t < 1) :
    f (x + t * (z - x)) < (1 - t) * f x + t * f z := by
  have := hf.2 (Set.mem_univ x) (Set.mem_univ z) hxz (by linarith : (0:ℝ) < 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at this
  have e : x + t * (z - x) = (1 - t) * x + t * z := by ring
  rw [e]; exact this

section moves
variable {f : ℝ → ℝ} {χ γ σ : ℝ} {p : ℝ × ℝ}

lemma g54_mv_R (h : move f 1 χ γ p = Move.reflect) :
    f (xr 1 p) < f p.1 ∧ ¬ f (xe 1 χ p) < f (xr 1 p) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g54_mv_E (h : move f 1 χ γ p = Move.expand) :
    f (xr 1 p) < f p.1 ∧ f (xe 1 χ p) < f (xr 1 p) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g54_mv_O (h : move f 1 χ γ p = Move.outside) :
    ¬ f (xr 1 p) < f p.1 ∧ f (xr 1 p) < f p.2 ∧ f (xc 1 γ p) ≤ f (xr 1 p) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g54_mv_I (h : move f 1 χ γ p = Move.inside) :
    ¬ f (xr 1 p) < f p.1 ∧ ¬ f (xr 1 p) < f p.2 ∧ f (xcc γ p) < f p.2 := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g54_mv_S (h : move f 1 χ γ p = Move.shrink) :
    (¬ f (xr 1 p) < f p.1 ∧ f (xr 1 p) < f p.2 ∧ ¬ f (xc 1 γ p) ≤ f (xr 1 p)) ∨
    (¬ f (xr 1 p) < f p.1 ∧ ¬ f (xr 1 p) < f p.2 ∧ ¬ f (xcc γ p) < f p.2) := by
  unfold move at h; split_ifs at h <;> simp_all

lemma g54_step_R (h : move f 1 χ γ p = Move.reflect) :
    step f 1 χ γ σ p = (p.1 + (p.1 - p.2), p.1) := by
  have h' := g54_mv_R h
  show place f p.1 (acceptedPoint 1 χ γ σ p (move f 1 χ γ p)) = _
  rw [h]; simp only [acceptedPoint, place]; split_ifs with hh
  · simp only [xr, one_mul] at hh ⊢; simp [hh]
  · exact absurd h'.1 hh

lemma g54_step_E (h : move f 1 χ γ p = Move.expand) :
    step f 1 χ γ σ p = (p.1 + χ * (p.1 - p.2), p.1) := by
  have h' := g54_mv_E h
  show place f p.1 (acceptedPoint 1 χ γ σ p (move f 1 χ γ p)) = _
  rw [h]; simp only [acceptedPoint, place]; split_ifs with hh
  · simp only [xe, one_mul] at hh ⊢; simp [hh]
  · exact absurd (h'.2.trans h'.1) hh

lemma g54_step_O (h : move f 1 χ γ p = Move.outside) :
    step f 1 χ γ σ p = place f p.1 (p.1 + γ * (p.1 - p.2)) := by
  show place f p.1 (acceptedPoint 1 χ γ σ p (move f 1 χ γ p)) = _
  rw [h]; simp [acceptedPoint, xc]

lemma g54_step_I (h : move f 1 χ γ p = Move.inside) :
    step f 1 χ γ σ p = place f p.1 (p.1 - γ * (p.1 - p.2)) := by
  show place f p.1 (acceptedPoint 1 χ γ σ p (move f 1 χ γ p)) = _
  rw [h]; simp [acceptedPoint, xcc]

lemma g54_diam_place (x1 v : ℝ) : diam (place f x1 v) = |v - x1| := by
  unfold place; split_ifs <;> simp [diam, abs_sub_comm]

end moves


section inv
variable {f : ℝ → ℝ} {χ γ σ : ℝ} {p0 : ℝ × ℝ}

lemma g54_acc_ne (hpar : ParamsOK 1 χ γ σ) (p : ℝ × ℝ) (hp : p.1 ≠ p.2) (mv : Move) :
    acceptedPoint 1 χ γ σ p mv ≠ p.1 := by
  obtain ⟨-, hχ, -, hγ, -, hσ, -⟩ := hpar
  have hd : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hd' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hp.symm
  cases mv <;> simp only [acceptedPoint, xr, xe, xc, xcc, xsh] <;> intro h
  · apply hd; linarith
  · apply mul_ne_zero (show (1:ℝ) * χ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show (1:ℝ) * γ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show γ ≠ 0 by positivity) hd; linarith
  · apply mul_ne_zero (show σ ≠ 0 by positivity) hd'; linarith

lemma g54_place_inv (x1 v : ℝ) (h : v ≠ x1) :
    (place f x1 v).1 ≠ (place f x1 v).2 ∧ f (place f x1 v).1 ≤ f (place f x1 v).2 := by
  unfold place; split_ifs with hh
  · exact ⟨h, hh.le⟩
  · exact ⟨Ne.symm h, not_lt.1 hh⟩

lemma g54_inv (hpar : ParamsOK 1 χ γ σ) (h0 : IsStart f p0) (k : ℕ) :
    (run f 1 χ γ σ p0 k).1 ≠ (run f 1 χ γ σ p0 k).2 ∧
      f (run f 1 χ γ σ p0 k).1 ≤ f (run f 1 χ γ σ p0 k).2 := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [g54_run_succ]
    exact g54_place_inv _ _ (g54_acc_ne hpar _ ih.1 _)

lemma g54_noS_state (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ) (p : ℝ × ℝ)
    (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) : move f 1 χ γ p ≠ Move.shrink := by
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  intro h
  rcases g54_mv_S h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · apply h3
    have := g54_H1 hf.convexOn p.1 (xr 1 p) γ hγ.le hγ1.le
    have e : xc 1 γ p = p.1 + γ * (xr 1 p - p.1) := by simp only [xc, xr]; ring
    rw [e]; push_neg at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - γ)]
  · apply h3
    have := g54_H2 hf p.1 p.2 γ hp hγ hγ1
    have e : xcc γ p = p.1 + γ * (p.2 - p.1) := by simp only [xcc]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hle (by linarith : (0:ℝ) ≤ 1 - γ)]

lemma g54_noS (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ) (h0 : IsStart f p0)
    (k : ℕ) : moveAt f χ γ σ p0 k ≠ Move.shrink :=
  g54_noS_state hf hpar _ (g54_inv hpar h0 k).1 (g54_inv hpar h0 k).2

lemma g54_runR {k : ℕ} (h : moveAt f χ γ σ p0 k = Move.reflect) :
    run f 1 χ γ σ p0 (k+1) = ((run f 1 χ γ σ p0 k).1 + ((run f 1 χ γ σ p0 k).1 -
      (run f 1 χ γ σ p0 k).2), (run f 1 χ γ σ p0 k).1) := by
  rw [g54_run_succ]; exact g54_step_R h

lemma g54_runE {k : ℕ} (h : moveAt f χ γ σ p0 k = Move.expand) :
    run f 1 χ γ σ p0 (k+1) = ((run f 1 χ γ σ p0 k).1 + χ * ((run f 1 χ γ σ p0 k).1 -
      (run f 1 χ γ σ p0 k).2), (run f 1 χ γ σ p0 k).1) := by
  rw [g54_run_succ]; exact g54_step_E h

lemma g54_diamR {k : ℕ} (h : moveAt f χ γ σ p0 k = Move.reflect) :
    diam (run f 1 χ γ σ p0 (k+1)) = diam (run f 1 χ γ σ p0 k) := by
  rw [g54_runR h]; simp only [diam]; ring_nf

lemma g54_diamE (hχ : 1 < χ) {k : ℕ} (h : moveAt f χ γ σ p0 k = Move.expand) :
    diam (run f 1 χ γ σ p0 (k+1)) = χ * diam (run f 1 χ γ σ p0 k) := by
  rw [g54_runE h]; simp only [diam]
  rw [show (run f 1 χ γ σ p0 k).1 + χ * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2) -
    (run f 1 χ γ σ p0 k).1 = χ * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2) by ring,
    abs_mul, abs_of_pos (by linarith : (0:ℝ) < χ)]

lemma g54_diamC (hγ : 0 < γ) {k : ℕ} (h : IsContraction (moveAt f χ γ σ p0 k)) :
    diam (run f 1 χ γ σ p0 (k+1)) = γ * diam (run f 1 χ γ σ p0 k) := by
  rw [g54_run_succ]
  rcases h with h | h
  · rw [g54_step_O h, g54_diam_place]; simp only [diam]
    rw [show (run f 1 χ γ σ p0 k).1 + γ * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2) -
      (run f 1 χ γ σ p0 k).1 = γ * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2) by ring,
      abs_mul, abs_of_pos hγ]
  · rw [g54_step_I h, g54_diam_place]; simp only [diam]
    rw [show (run f 1 χ γ σ p0 k).1 - γ * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2) -
      (run f 1 χ γ σ p0 k).1 = -(γ * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2)) by ring,
      abs_neg, abs_mul, abs_of_pos hγ]

end inv

section l46
variable {f : ℝ → ℝ} {χ γ σ : ℝ} {p0 : ℝ × ℝ}

lemma g54_Rrun (k n : ℕ) (h : ∀ i < n, moveAt f χ γ σ p0 (k + i) = Move.reflect) :
    ∀ i ≤ n, (run f 1 χ γ σ p0 (k+i)).1 = (run f 1 χ γ σ p0 k).1 +
        (i:ℝ) * ((run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2) ∧
      (run f 1 χ γ σ p0 (k+i)).1 - (run f 1 χ γ σ p0 (k+i)).2 =
        (run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2 := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [← add_assoc, g54_runR (h i (by omega))]
    simp only
    constructor
    · rw [ih2, ih1]; push_cast; ring
    · rw [ih2]; ring

lemma g54_l46a (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ) (k : ℕ) :
    ¬ ∀ i < rStar χ + 1, moveAt f χ γ σ p0 (k + i) = Move.reflect := by
  intro h
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  set r := rStar χ with hr
  have hr1 : (χ - 1) ≤ (r:ℝ) := Nat.le_ceil _
  have hrpos : 1 ≤ r := by
    have : 0 < r := Nat.ceil_pos.2 (by linarith)
    omega
  have hRR := g54_Rrun (f := f) (χ := χ) (γ := γ) (σ := σ) (p0 := p0) k (r+1) h
  set a := (run f 1 χ γ σ p0 k).1 with ha
  set d := (run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2 with hd
  -- reflection at k: f (a + χ d) ≥ f (a + d)
  have h0 := g54_mv_R (h 0 (by omega))
  simp only [add_zero, xr, xe, one_mul] at h0
  have hk1 : ¬ f (a + χ * d) < f (a + d) := h0.2
  -- descent
  have hstep : ∀ i ≤ r, f (a + ((i:ℝ) + 1) * d) < f (a + (i:ℝ) * d) := by
    intro i hi
    have hm := g54_mv_R (h i (by omega))
    obtain ⟨e1, e2⟩ := hRR i (by omega)
    simp only [xr, one_mul] at hm
    rw [e2, e1] at hm
    have : a + (i:ℝ) * d + d = a + ((i:ℝ) + 1) * d := by ring
    rw [this] at hm; exact hm.1
  have hchain : ∀ i, 1 ≤ i → i ≤ r → f (a + ((i:ℝ) + 1) * d) < f (a + d) := by
    intro i h1 h2
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        have := hstep 1 (by omega); push_cast at this ⊢
        simpa [one_mul] using this
      · have := hstep (i+1) h2
        have := ih h0 (by omega)
        push_cast at *
        linarith
  have hlast := hchain r hrpos le_rfl
  have hrpos' : (0:ℝ) < r := by exact_mod_cast hrpos
  have hH := g54_H1 hf.convexOn (a + d) (a + ((r:ℝ) + 1) * d) ((χ - 1) / r)
    (div_nonneg (by linarith) hrpos'.le) ((div_le_one hrpos').2 hr1)
  have e : a + d + (χ - 1) / r * (a + ((r:ℝ) + 1) * d - (a + d)) = a + χ * d := by
    field_simp; ring
  rw [e] at hH
  have ht : 0 < (χ - 1) / r := div_pos (by linarith) hrpos'
  apply hk1
  nlinarith [mul_lt_mul_of_pos_left hlast ht]

lemma g54_l46b (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ) (k : ℕ)
    (h : moveAt f χ γ σ p0 k = Move.reflect) : moveAt f χ γ σ p0 (k + 1) ≠ Move.expand := by
  intro h'
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  have h0 := g54_mv_R h
  have h1 := g54_mv_E h'
  have hrun := g54_runR h
  unfold moveAt at h1
  rw [hrun] at h1
  set a := (run f 1 χ γ σ p0 k).1 with ha
  set d := (run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2 with hd
  simp only [xr, xe, one_mul] at h0 h1
  have e1 : a + d + χ * (a + d - a) = a + d + χ * d := by ring
  have e2 : a + d + (a + d - a) = a + d + d := by ring
  rw [e1, e2] at h1
  have hz : f (a + d + χ * d) < f (a + d) := h1.2.trans h1.1
  have hχ0 : (0:ℝ) < χ := by linarith
  have hH := g54_H1 hf.convexOn (a + d) (a + d + χ * d) ((χ - 1) / χ)
    (div_nonneg (by linarith) hχ0.le) ((div_le_one hχ0).2 (by linarith))
  have e : a + d + (χ - 1) / χ * (a + d + χ * d - (a + d)) = a + χ * d := by
    field_simp; ring
  rw [e] at hH
  have ht : 0 < (χ - 1) / χ := div_pos (by linarith) hχ0
  apply h0.2
  nlinarith [mul_lt_mul_of_pos_left hz ht]

end l46


theorem lemma_4_6_core (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (p0 : ℝ × ℝ) :
    (∀ k : ℕ, ¬ ∀ i < rStar χ + 1, moveAt f χ γ σ p0 (k + i) = Move.reflect) ∧
    (∀ k : ℕ, moveAt f χ γ σ p0 k = Move.reflect →
      moveAt f χ γ σ p0 (k + 1) ≠ Move.expand) :=
  ⟨fun k => g54_l46a hf hpar k, fun k h => g54_l46b hf hpar k h⟩

end NelderMeadLD.Rate1D

open NelderMeadLD.Rate1D
open NelderMeadLD.Conv1D

theorem solution (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    (∀ k : ℕ, ¬ ∀ i < rStar χ + 1, moveAt f χ γ σ p0 (k + i) = Move.reflect) ∧
    (∀ k : ℕ, moveAt f χ γ σ p0 k = Move.reflect →
      moveAt f χ γ σ p0 (k + 1) ≠ Move.expand) := by
  exact lemma_4_6_core χ γ σ hpar f hf p0
