-- Prove2me | solution 1 for NelderMeadLD.Conv1D.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:38:48.846689+00:00
-- url     : https://prove2.me/submissions/6b3d4018-ab7c-4e31-a73c-a981b83bf248

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

section l41
variable {f : ℝ → ℝ}

lemma g55_minlt (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ} (hmin : ∀ y, f xmin ≤ f y)
    {w : ℝ} (hw : w ≠ xmin) : f xmin < f w := by
  have := g55_H2 hf xmin w (1/2) (Ne.symm hw) (by norm_num) (by norm_num)
  have := hmin (xmin + 1/2 * (w - xmin))
  linarith

lemma g55_M (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ} (hmin : ∀ y, f xmin ≤ f y)
    {u w : ℝ} (h : (xmin ≤ u ∧ u < w) ∨ (w < u ∧ u ≤ xmin)) : f u < f w := by
  have hw : w ≠ xmin := by rcases h with h | h <;> intro e <;> subst e <;> linarith
  have h1 := g55_minlt hf hmin hw
  have hne : w - xmin ≠ 0 := sub_ne_zero.mpr hw
  set t := (u - xmin) / (w - xmin) with ht
  have hu : u = xmin + t * (w - xmin) := by rw [ht]; field_simp; ring
  have ht0 : 0 ≤ t := by
    rcases h with h | h
    · exact div_nonneg (by linarith) (by linarith)
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
  have ht1 : t < 1 := by
    rcases h with h | h
    · rw [div_lt_one (by linarith)]; linarith
    · rw [div_lt_one_of_neg (by linarith)]; linarith
  have := g55_H1 hf.convexOn xmin w t ht0 ht1.le
  rw [hu]; nlinarith

theorem lemma_4_1_core (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y) :
    (∀ y1 y2 y3 : ℝ, y1 ≠ y2 → y2 ≠ y3 → y1 ≠ y3 →
        min y1 y3 < y2 → y2 < max y1 y3 → f y2 ≤ f y1 → f y2 ≤ f y3 →
        min y1 y3 < xmin ∧ xmin < max y1 y3) ∧
    (∀ y1 y2 : ℝ, y1 ≠ y2 → xmin ∈ Set.uIcc y1 y2 →
        ∀ ξ1 ξ2 : ℝ, 1 ≤ ξ1 → ξ1 < ξ2 →
          f (y2 + ξ1 * (y1 - y2)) < f (y2 + ξ2 * (y1 - y2))) ∧
    Continuous f := by
  refine ⟨?_, ?_, ?_⟩
  · intro y1 y2 y3 h12 h23 h13 hlo hhi hf1 hf3
    rcases lt_or_gt_of_ne h13 with h | h
    · rw [min_eq_left h.le] at hlo ⊢; rw [max_eq_right h.le] at hhi ⊢
      constructor
      · by_contra hc; push_neg at hc
        have := g55_M hf hmin (u := y1) (w := y2) (Or.inl ⟨hc, hlo⟩); linarith
      · by_contra hc; push_neg at hc
        have := g55_M hf hmin (u := y3) (w := y2) (Or.inr ⟨hhi, hc⟩); linarith
    · rw [min_eq_right h.le] at hlo ⊢; rw [max_eq_left h.le] at hhi ⊢
      constructor
      · by_contra hc; push_neg at hc
        have := g55_M hf hmin (u := y3) (w := y2) (Or.inl ⟨hc, hlo⟩); linarith
      · by_contra hc; push_neg at hc
        have := g55_M hf hmin (u := y1) (w := y2) (Or.inr ⟨hhi, hc⟩); linarith
  · intro y1 y2 h12 hx ξ1 ξ2 hξ1 hξ
    apply g55_M hf hmin
    rw [Set.mem_uIcc] at hx
    rcases lt_or_gt_of_ne h12 with h | h
    · right
      have hx' : xmin ≥ y1 := by rcases hx with hx | hx <;> linarith
      constructor <;> nlinarith
    · left
      have hx' : xmin ≤ y1 := by rcases hx with hx | hx <;> linarith
      constructor <;> nlinarith
  · exact continuousOn_univ.mp (hf.convexOn.continuousOn isOpen_univ)

end l41

end NelderMeadLD.Conv1D

open NelderMeadLD.Conv1D


theorem solution (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y) :
    (∀ y1 y2 y3 : ℝ, y1 ≠ y2 → y2 ≠ y3 → y1 ≠ y3 →
        min y1 y3 < y2 → y2 < max y1 y3 → f y2 ≤ f y1 → f y2 ≤ f y3 →
        min y1 y3 < xmin ∧ xmin < max y1 y3) ∧
    (∀ y1 y2 : ℝ, y1 ≠ y2 → xmin ∈ Set.uIcc y1 y2 →
        ∀ ξ1 ξ2 : ℝ, 1 ≤ ξ1 → ξ1 < ξ2 →
          f (y2 + ξ1 * (y1 - y2)) < f (y2 + ξ2 * (y1 - y2))) ∧
    Continuous f := by
  exact lemma_4_1_core f hf xmin hmin
