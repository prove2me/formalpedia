-- Prove2me | solution 1 for NelderMeadLD.Rate1D.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:27:19.358177+00:00
-- url     : https://prove2.me/submissions/ae6ad7ad-f3a7-4cc0-b25c-16aba862ad77

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


section c41
variable {f : ℝ → ℝ} {χ γ σ : ℝ} {p0 : ℝ × ℝ}

lemma g54_br_noE {p : ℝ × ℝ} (hb : Bracketed 1 χ f p) : move f 1 χ γ p ≠ Move.expand := by
  intro h
  have := g54_mv_E h
  have := hb.2
  linarith [this]

lemma g54_br_R (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ) {k : ℕ}
    (hb : Bracketed 1 χ f (run f 1 χ γ σ p0 k)) (h : moveAt f χ γ σ p0 k = Move.reflect) :
    Bracketed 1 χ f (run f 1 χ γ σ p0 (k+1)) := by
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  have h0 := g54_mv_R h
  rw [g54_runR h]
  set a := (run f 1 χ γ σ p0 k).1 with ha
  set d := (run f 1 χ γ σ p0 k).1 - (run f 1 χ γ σ p0 k).2 with hd
  obtain ⟨hb1, hb2⟩ := hb
  simp only [Bracketed, xr, xe, one_mul] at h0 hb2 ⊢
  rw [← hd] at hb2
  have e1 : a + d + χ * (a + d - a) = a + d + χ * d := by ring
  rw [e1]
  refine ⟨h0.1.le, ?_⟩
  by_contra hz
  push_neg at hz
  have hχ0 : (0:ℝ) < χ := by linarith
  have hH := g54_H1 hf.convexOn (a + d) (a + d + χ * d) ((χ - 1) / χ)
    (div_nonneg (by linarith) hχ0.le) ((div_le_one hχ0).2 (by linarith))
  have e : a + d + (χ - 1) / χ * (a + d + χ * d - (a + d)) = a + χ * d := by
    field_simp; ring
  rw [e] at hH
  have ht : 0 < (χ - 1) / χ := div_pos (by linarith) hχ0
  nlinarith [mul_lt_mul_of_pos_left hz ht, h0.1]

theorem corollary_4_1_core (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (K : ℕ) (hK : FirstBracket f χ γ σ p0 K) :
    ∃ k : ℕ, K ≤ k ∧ k ≤ K + rStar χ ∧ IsContraction (moveAt f χ γ σ p0 k) := by
  by_contra hc
  push_neg at hc
  have claim : ∀ i ≤ rStar χ + 1, Bracketed 1 χ f (run f 1 χ γ σ p0 (K + i)) ∧
      ∀ j < i, moveAt f χ γ σ p0 (K + j) = Move.reflect := by
    intro i hi
    induction i with
    | zero => exact ⟨by simpa using hK.1, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ i ih =>
      obtain ⟨hb, hR⟩ := ih (by omega)
      have hmv : moveAt f χ γ σ p0 (K + i) = Move.reflect := by
        cases hm : moveAt f χ γ σ p0 (K + i) with
        | reflect => rfl
        | expand => exact absurd hm (g54_br_noE hb)
        | outside => exact absurd (Or.inl hm) (hc (K + i) (by omega) (by omega))
        | inside => exact absurd (Or.inr hm) (hc (K + i) (by omega) (by omega))
        | shrink => exact absurd hm (g54_noS hf hpar h0 _)
      refine ⟨?_, ?_⟩
      · rw [← add_assoc]; exact g54_br_R hf hpar hb hmv
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hR j hj
        · subst hj; exact hmv
  exact g54_l46a hf hpar K (claim _ le_rfl).2

end c41


section l47
variable {f : ℝ → ℝ} {χ γ σ : ℝ} {p0 : ℝ × ℝ}

lemma g54_barrier (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ) (h0 : IsStart f p0)
    {c : ℕ} (hc : IsContraction (moveAt f χ γ σ p0 c)) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 / γ ∧
      f (run f 1 χ γ σ p0 (c+1)).1 ≤ f ((run f 1 χ γ σ p0 (c+1)).1 +
        β * ((run f 1 χ γ σ p0 (c+1)).1 - (run f 1 χ γ σ p0 (c+1)).2)) := by
  have hinv := (g54_inv hpar h0 c).2
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  have hb1 : 0 < (1 - γ) / γ := div_pos (by linarith) hγ
  have hb2 : (1 - γ) / γ ≤ 1 / γ := div_le_div_of_nonneg_right (by linarith) hγ.le
  have hb3 : 0 < 1 / γ := by positivity
  rw [g54_run_succ]
  set p := run f 1 χ γ σ p0 c with hp
  rcases hc with h | h
  · have hm := g54_mv_O h
    rw [g54_step_O h]
    simp only [xr, one_mul] at hm
    unfold place
    split_ifs with hv
    · refine ⟨(1 - γ) / γ, hb1, hb2, ?_⟩
      have e : p.1 + γ * (p.1 - p.2) + (1 - γ) / γ * (p.1 + γ * (p.1 - p.2) - p.1) =
          p.1 + (p.1 - p.2) := by field_simp; ring
      simp only; rw [e]; linarith [hm.1]
    · refine ⟨1 / γ, hb3, le_rfl, ?_⟩
      have e : p.1 + 1 / γ * (p.1 - (p.1 + γ * (p.1 - p.2))) = p.2 := by field_simp; ring
      simp only; rw [e]; linarith [hm.1, hm.2.1]
  · have hm := g54_mv_I h
    rw [g54_step_I h]
    simp only [xr, one_mul] at hm
    unfold place
    split_ifs with hv
    · refine ⟨(1 - γ) / γ, hb1, hb2, ?_⟩
      have e : p.1 - γ * (p.1 - p.2) + (1 - γ) / γ * (p.1 - γ * (p.1 - p.2) - p.1) =
          p.2 := by field_simp; ring
      simp only; rw [e]; linarith
    · refine ⟨1 / γ, hb3, le_rfl, ?_⟩
      have e : p.1 + 1 / γ * (p.1 - (p.1 - γ * (p.1 - p.2))) = p.1 + (p.1 - p.2) := by
        field_simp; ring
      simp only; rw [e]; linarith [hm.1, hm.2.1]

lemma g54_Erun (m L : ℕ) (h : ∀ i < L, moveAt f χ γ σ p0 (m + i) = Move.expand) :
    ∀ j ≤ L, (run f 1 χ γ σ p0 (m+j)).1 = (run f 1 χ γ σ p0 m).1 +
        (∑ i ∈ Finset.range j, χ ^ (i+1)) * ((run f 1 χ γ σ p0 m).1 - (run f 1 χ γ σ p0 m).2) ∧
      (run f 1 χ γ σ p0 (m+j)).1 - (run f 1 χ γ σ p0 (m+j)).2 =
        χ ^ j * ((run f 1 χ γ σ p0 m).1 - (run f 1 χ γ σ p0 m).2) ∧
      f (run f 1 χ γ σ p0 (m+j)).1 ≤ f (run f 1 χ γ σ p0 m).1 ∧
      (0 < j → f (run f 1 χ γ σ p0 (m+j)).1 < f (run f 1 χ γ σ p0 m).1) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨ih1, ih2, ih3, -⟩ := ih (by omega)
    have hE := h j (by omega)
    have hmv := g54_mv_E hE
    simp only [xr, xe, one_mul] at hmv
    rw [← add_assoc, g54_runE hE]
    simp only
    have hlt : f ((run f 1 χ γ σ p0 (m + j)).1 + χ * ((run f 1 χ γ σ p0 (m + j)).1 -
        (run f 1 χ γ σ p0 (m + j)).2)) < f (run f 1 χ γ σ p0 m).1 :=
      lt_of_lt_of_le (hmv.2.trans hmv.1) ih3
    refine ⟨?_, ?_, hlt.le, fun _ => hlt⟩
    · rw [ih2, ih1, Finset.sum_range_succ]; ring
    · rw [ih2]; ring

lemma g54_l47_base (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ)
    (h0 : IsStart f p0) {c : ℕ} (hc : IsContraction (moveAt f χ γ σ p0 c)) (L : ℕ)
    (hL : ∀ i < L, moveAt f χ γ σ p0 (c + 1 + i) = Move.expand) : L ≤ jStar χ γ := by
  have hχ : 1 < χ := hpar.2.1
  have hγ : 0 < γ := hpar.2.2.2.1
  rcases Nat.eq_zero_or_pos L with hL0 | hL0
  · subst hL0; exact Nat.zero_le _
  obtain ⟨β, hβ0, hβ1, hβ⟩ := g54_barrier hf hpar h0 hc
  obtain ⟨e1, -, -, e4⟩ := g54_Erun (c+1) L hL L le_rfl
  have e4 := e4 hL0
  set a := (run f 1 χ γ σ p0 (c+1)).1 with ha
  set d := (run f 1 χ γ σ p0 (c+1)).1 - (run f 1 χ γ σ p0 (c+1)).2 with hd
  set S := ∑ i ∈ Finset.range L, χ ^ (i+1) with hS
  have hLS : (L:ℝ) ≤ S := by
    have := Finset.sum_le_sum (fun i _ => one_le_pow₀ hχ.le :
      ∀ i ∈ Finset.range L, (1:ℝ) ≤ χ ^ (i+1))
    simpa using this
  have hSβ : S < β := by
    by_contra hcon
    push_neg at hcon
    have hSpos : 0 < S := lt_of_lt_of_le hβ0 hcon
    rw [e1] at e4
    have hH := g54_H1 hf.convexOn a (a + S * d) (β / S) (div_nonneg hβ0.le hSpos.le)
      ((div_le_one hSpos).2 hcon)
    have e : a + β / S * (a + S * d - a) = a + β * d := by field_simp; ring
    rw [e] at hH
    have ht : 0 < β / S := div_pos hβ0 hSpos
    nlinarith [mul_lt_mul_of_pos_left e4 ht]
  have hN : (L:ℝ) < NNM1 χ γ := by
    unfold NNM1
    linarith [le_max_right χ (1 / γ)]
  have hLc : L ≤ ⌈NNM1 χ γ⌉₊ := by
    have := hN.trans_le (Nat.le_ceil (NNM1 χ γ))
    exact_mod_cast this.le
  unfold jStar
  convert Nat.le_findGreatest hLc (P := fun j => ∑ i ∈ Finset.range j, χ ^ (i + 1) < NNM1 χ γ)
    (by
      show S < NNM1 χ γ
      unfold NNM1
      linarith [le_max_right χ (1 / γ)])

theorem lemma_4_7_core (χ γ σ : ℝ) (hpar : ParamsOK 1 χ γ σ)
    (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (k : ℕ) (hk : IsContraction (moveAt f χ γ σ p0 k)) :
    ∀ m : ℕ, k < m → ∀ L : ℕ,
      (∀ i < L, moveAt f χ γ σ p0 (m + i) = Move.expand) → L ≤ jStar χ γ := by
  have key : ∀ n L, (∀ i < L, moveAt f χ γ σ p0 (k + 1 + n + i) = Move.expand) →
      L ≤ jStar χ γ := by
    intro n
    induction n with
    | zero => intro L hL; exact g54_l47_base hf hpar h0 hk L (by simpa using hL)
    | succ n ih =>
      intro L hL
      rcases Nat.eq_zero_or_pos L with hL0 | hL0
      · subst hL0; exact Nat.zero_le _
      have hm1 := hL 0 (by omega)
      cases hm : moveAt f χ γ σ p0 (k + 1 + n) with
      | reflect =>
        exact absurd (by simpa [Nat.add_assoc] using hm1) (g54_l46b hf hpar _ hm)
      | expand =>
        have := ih (L+1) (by
          intro i hi
          rcases i with _ | i
          · simpa using hm
          · have := hL i (by omega)
            rw [← this]; congr 1; omega)
        omega
      | outside =>
        exact g54_l47_base hf hpar h0 (c := k + 1 + n) (Or.inl hm) L
          (fun i hi => by rw [← hL i hi]; congr 1)
      | inside =>
        exact g54_l47_base hf hpar h0 (c := k + 1 + n) (Or.inr hm) L
          (fun i hi => by rw [← hL i hi]; congr 1)
      | shrink => exact absurd hm (g54_noS hf hpar h0 _)
  intro m hm L hL
  obtain ⟨n, rfl⟩ : ∃ n, m = k + 1 + n := ⟨m - k - 1, by omega⟩
  exact key n L hL

end l47


section seg
variable {f : ℝ → ℝ} {χ γ σ : ℝ} {p0 : ℝ × ℝ}

lemma g54_jStar_eq (χ γ : ℝ) : jStar χ γ =
    Nat.findGreatest (fun j => ∑ i ∈ Finset.range j, χ ^ (i + 1) < NNM1 χ γ) ⌈NNM1 χ γ⌉₊ := by
  unfold jStar; congr

lemma g54_phi_lt (hχ : 1 < χ) (hγ : 0 < γ) (hγ1 : γ < 1) : γ * χ ^ (jStar χ γ) < 1 := by
  rcases Nat.eq_zero_or_pos (jStar χ γ) with hJ | hJ
  · rw [hJ]; simpa using hγ1
  have hN0 : (0:ℝ) < NNM1 χ γ := by unfold NNM1; exact lt_max_of_lt_left (by linarith)
  have hP := Nat.findGreatest_spec (P := fun j => ∑ i ∈ Finset.range j, χ ^ (i + 1) < NNM1 χ γ)
    (n := ⌈NNM1 χ γ⌉₊) (m := 0) (Nat.zero_le _) (by simpa using hN0)
  rw [← g54_jStar_eq] at hP
  
  have hsingle : χ ^ (jStar χ γ - 1 + 1) ≤ ∑ i ∈ Finset.range (jStar χ γ), χ ^ (i + 1) :=
    Finset.single_le_sum (f := fun i => χ ^ (i + 1)) (fun i _ => by positivity)
      (Finset.mem_range.2 (by omega))
  rw [Nat.sub_add_cancel hJ] at hsingle
  have h1 : χ ^ (jStar χ γ) < max χ (1 / γ) := lt_of_le_of_lt hsingle hP
  have h2 : χ ≤ χ ^ (jStar χ γ) := le_self_pow₀ hχ.le (by omega)
  rcases lt_max_iff.1 h1 with h | h
  · linarith
  · have := (lt_div_iff₀ hγ).1 h
    linarith

lemma g54_segment (hf : StrictConvexOn ℝ Set.univ f) (hpar : ParamsOK 1 χ γ σ)
    (h0 : IsStart f p0) (k n : ℕ)
    (hE : ∀ L, (∀ i < L, moveAt f χ γ σ p0 (k + i) = Move.expand) → L ≤ jStar χ γ)
    (hnc : ∀ i < n, ¬ IsContraction (moveAt f χ γ σ p0 (k + i))) :
    diam (run f 1 χ γ σ p0 (k + n)) ≤ χ ^ (jStar χ γ) * diam (run f 1 χ γ σ p0 k) ∧
      n ≤ jStar χ γ + rStar χ := by
  have hχ : 1 < χ := hpar.2.1
  have claim : ∀ i ≤ n, ∃ a ≤ i, (∀ j < a, moveAt f χ γ σ p0 (k + j) = Move.expand) ∧
      (∀ j, a ≤ j → j < i → moveAt f χ γ σ p0 (k + j) = Move.reflect) ∧
      diam (run f 1 χ γ σ p0 (k + i)) = χ ^ a * diam (run f 1 χ γ σ p0 k) := by
    intro i hi
    induction i with
    | zero => exact ⟨0, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j h1 h2 => absurd h2 (Nat.not_lt_zero _), by simp⟩
    | succ i ih =>
      obtain ⟨a, hai, hEa, hRa, hd⟩ := ih (by omega)
      cases hm : moveAt f χ γ σ p0 (k + i) with
      | reflect =>
        refine ⟨a, by omega, hEa, ?_, ?_⟩
        · intro j h1 h2
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
          · exact hRa j h1 h2
          · subst h2; exact hm
        · rw [← add_assoc, g54_diamR hm, hd]
      | expand =>
        rcases Nat.lt_or_ge a i with hlt | hge
        · exfalso
          have hR := hRa (i - 1) (by omega) (by omega)
          have := g54_l46b hf hpar _ hR
          rw [show k + (i - 1) + 1 = k + i by omega] at this
          exact this hm
        · have hai' : a = i := le_antisymm hai hge
          subst hai'
          refine ⟨a + 1, le_rfl, ?_, fun j h1 h2 => absurd h2 (by omega), ?_⟩
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
            · exact hEa j hj
            · subst hj; exact hm
          · rw [← add_assoc, g54_diamE hχ hm, hd, pow_succ]; ring
      | outside => exact absurd (Or.inl hm) (hnc i (by omega))
      | inside => exact absurd (Or.inr hm) (hnc i (by omega))
      | shrink => exact absurd hm (g54_noS hf hpar h0 _)
  obtain ⟨a, han, hEa, hRa, hd⟩ := claim n le_rfl
  have haJ := hE a hEa
  refine ⟨?_, ?_⟩
  · rw [hd]
    apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hχ.le haJ)
    simp only [diam]; exact abs_nonneg _
  · by_contra hcon
    apply g54_l46a hf hpar (p0 := p0) (k + a)
    intro i hi
    rw [add_assoc]
    exact hRa (a + i) (by omega) (by omega)

theorem lemma_4_8_core :
    ∀ χ γ : ℝ, 1 < χ → 0 < γ → γ < 1 →
      ∃ φ : ℝ, φ < 1 ∧
        ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∀ f : ℝ → ℝ, StrictConvexOn ℝ Set.univ f →
        (∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) →
        ∀ p0 : ℝ × ℝ, IsStart f p0 →
        ∀ k k' : ℕ, k < k' →
          IsContraction (moveAt f χ γ σ p0 k) →
          IsContraction (moveAt f χ γ σ p0 k') →
          (∀ i : ℕ, k < i → i < k' → ¬ IsContraction (moveAt f χ γ σ p0 i)) →
          diam (run f 1 χ γ σ p0 (k' + 1)) ≤ φ * diam (run f 1 χ γ σ p0 (k + 1)) := by
  intro χ γ hχ hγ hγ1
  refine ⟨γ * χ ^ (jStar χ γ), g54_phi_lt hχ hγ hγ1, ?_⟩
  intro σ hσ hσ1 f hf _ p0 h0 k k' hkk hk hk' hbetween
  have hpar : ParamsOK 1 χ γ σ := ⟨one_pos, hχ, hχ, hγ, hγ1, hσ, hσ1⟩
  obtain ⟨n, rfl⟩ : ∃ n, k' = k + 1 + n := ⟨k' - k - 1, by omega⟩
  have hseg := g54_segment hf hpar h0 (k + 1) n
    (fun L hL => lemma_4_7_core χ γ σ hpar f hf p0 h0 k hk (k + 1) (by omega) L hL)
    (fun i hi => hbetween (k + 1 + i) (by omega) (by omega))
  rw [g54_diamC hγ hk']
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hseg.1 hγ.le

end seg

end NelderMeadLD.Rate1D

open NelderMeadLD.Rate1D
open NelderMeadLD.Conv1D

theorem solution :
    ∀ χ γ : ℝ, 1 < χ → 0 < γ → γ < 1 →
      ∃ φ : ℝ, φ < 1 ∧
        ∀ σ : ℝ, 0 < σ → σ < 1 →
        ∀ f : ℝ → ℝ, StrictConvexOn ℝ Set.univ f →
        (∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) →
        ∀ p0 : ℝ × ℝ, IsStart f p0 →
        ∀ k k' : ℕ, k < k' →
          IsContraction (moveAt f χ γ σ p0 k) →
          IsContraction (moveAt f χ γ σ p0 k') →
          (∀ i : ℕ, k < i → i < k' → ¬ IsContraction (moveAt f χ γ σ p0 i)) →
          diam (run f 1 χ γ σ p0 (k' + 1)) ≤ φ * diam (run f 1 χ γ σ p0 (k + 1)) := by
  exact lemma_4_8_core
