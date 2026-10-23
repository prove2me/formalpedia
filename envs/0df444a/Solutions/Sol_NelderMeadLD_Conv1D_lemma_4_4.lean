-- Prove2me | solution 1 for NelderMeadLD.Conv1D.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:48:11.163869+00:00
-- url     : https://prove2.me/submissions/2d01a4e9-9b6a-4291-8a42-b043e6362246

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

section l43
variable {f : ℝ → ℝ}

lemma g55_Ml (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ} (hmin : ∀ y, f xmin ≤ f y)
    {c d l : ℝ} (hd : d ≠ 0) (hx : xmin = c + l * d) {α β : ℝ}
    (h : (l ≤ α ∧ α < β) ∨ (β < α ∧ α ≤ l)) : f (c + α * d) < f (c + β * d) := by
  apply g55_M hf hmin
  subst hx
  rcases lt_or_gt_of_ne hd with hd | hd
  · rcases h with h | h
    · right; constructor <;> nlinarith
    · left; constructor <;> nlinarith
  · rcases h with h | h
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith

lemma g55_ioc {c d l a b : ℝ} (hd : d ≠ 0) (hab : a ≠ b) :
    inIoc' (c + a * d) (c + b * d) (c + l * d) ↔ (a < l ∧ l ≤ b) ∨ (b ≤ l ∧ l < a) := by
  unfold inIoc'
  have hne : c + a * d ≠ c + b * d := by
    intro h; apply hab; have := mul_right_cancel₀ hd (by linarith : a * d = b * d); exact this
  have key : ∀ l' : ℝ, c + l * d = c + l' * d ↔ l = l' := by
    intro l'; constructor
    · intro h; exact mul_right_cancel₀ hd (by linarith)
    · intro h; rw [h]
  rw [key b]
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne hab with h | h
  · have h' : c + b * d ≤ c + a * d := by nlinarith
    rw [min_eq_right h', max_eq_left h']
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left; constructor
        · by_contra hc; push_neg at hc; nlinarith
        · by_contra hc; push_neg at hc; nlinarith
      · left; subst h1; exact ⟨h, le_rfl⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rcases eq_or_lt_of_le h2 with e | e
        · right; exact ⟨e, hne⟩
        · left; constructor <;> nlinarith
      · exfalso; linarith
  · have h' : c + a * d ≤ c + b * d := by nlinarith
    rw [min_eq_left h', max_eq_right h']
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · right; constructor
        · by_contra hc; push_neg at hc; nlinarith
        · by_contra hc; push_neg at hc; nlinarith
      · right; subst h1; exact ⟨le_rfl, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exfalso; linarith
      · rcases eq_or_lt_of_le h1 with e | e
        · right; exact ⟨e.symm, hne⟩
        · left; constructor <;> nlinarith
  · have h' : c + a * d ≤ c + b * d := by nlinarith
    rw [min_eq_left h', max_eq_right h']
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left; constructor
        · by_contra hc; push_neg at hc; nlinarith
        · by_contra hc; push_neg at hc; nlinarith
      · left; subst h1; exact ⟨h, le_rfl⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rcases eq_or_lt_of_le h2 with e | e
        · right; exact ⟨e, hne⟩
        · left; constructor <;> nlinarith
      · exfalso; linarith
  · have h' : c + b * d ≤ c + a * d := by nlinarith
    rw [min_eq_right h', max_eq_left h']
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · right; constructor
        · by_contra hc; push_neg at hc; nlinarith
        · by_contra hc; push_neg at hc; nlinarith
      · right; subst h1; exact ⟨le_rfl, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exfalso; linarith
      · rcases eq_or_lt_of_le h1 with e | e
        · right; exact ⟨e.symm, hne⟩
        · left; constructor <;> nlinarith

lemma g55_NNM_facts {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ) :
    1 ≤ NNM ρ χ γ * (ρ * γ) ∧ ρ ≤ NNM ρ χ γ * γ ∧ ρ * χ ≤ NNM ρ χ γ ∧ χ - 1 ≤ NNM ρ χ γ ∧
      1 ≤ NNM ρ χ γ * γ ∧ 1 ≤ NNM ρ χ γ := by
  obtain ⟨hρ, hχ, -, hγ, hγ1, -, -⟩ := hpar
  have a1 : 1 / (ρ * γ) ≤ NNM ρ χ γ := le_trans (le_max_left _ _) (le_max_left _ _)
  have a2 : ρ / γ ≤ NNM ρ χ γ := le_trans (le_max_right _ _) (le_max_left _ _)
  have a3 : ρ * χ ≤ NNM ρ χ γ := le_trans (le_max_left _ _) (le_max_right _ _)
  have a4 : χ - 1 ≤ NNM ρ χ γ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hργ : 0 < ρ * γ := by positivity
  have b1 : 1 ≤ NNM ρ χ γ * (ρ * γ) := by
    rw [div_le_iff₀ hργ] at a1; linarith
  have b2 : ρ ≤ NNM ρ χ γ * γ := by rw [div_le_iff₀ hγ] at a2; linarith
  have b5 : 1 ≤ NNM ρ χ γ * γ := by
    rcases le_or_gt 1 ρ with h | h
    · linarith
    · nlinarith
  refine ⟨b1, b2, a3, a4, b5, ?_⟩
  nlinarith

lemma g55_prox_coef {ρ χ γ σ xmin : ℝ} (hpar : ParamsOK ρ χ γ σ) {c d l : ℝ} (hd : d ≠ 0)
    (hx : xmin = c + l * d) {α β : ℝ} (hab : α ≠ β) :
    Proximity ρ χ γ xmin (c + α * d, c + β * d) ↔
      (β < l ∧ l ≤ α + NNM ρ χ γ * (α - β)) ∨ (α + NNM ρ χ γ * (α - β) ≤ l ∧ l < β) := by
  have hN := (g55_NNM_facts hpar).2.2.2.2.2
  unfold Proximity
  have e : c + α * d + NNM ρ χ γ * (c + α * d - (c + β * d)) =
      c + (α + NNM ρ χ γ * (α - β)) * d := by ring
  simp only; rw [e, hx]
  apply g55_ioc hd
  intro h
  have : (α - β) * (1 + NNM ρ χ γ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hab (by linarith)
  · linarith

lemma g55_prox_step (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ} (hmin : ∀ y, f xmin ≤ f y)
    {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ) (hρχ : 1 ≤ ρ * χ) (p : ℝ × ℝ)
    (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) (hprox : Proximity ρ χ γ xmin p) :
    Proximity ρ χ γ xmin (step f ρ χ γ σ p) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := g55_NNM_facts hpar
  have hpar' := hpar
  obtain ⟨hρ, hχ, -, hγ, hγ1, -, -⟩ := hpar'
  set N := NNM ρ χ γ with hNdef
  obtain ⟨c, x2⟩ := p
  simp only at hp hle
  set d := c - x2 with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr hp
  set l := (xmin - c) / d with hl
  have hx : xmin = c + l * d := by rw [hl]; field_simp; ring
  have ep : ((c, x2) : ℝ × ℝ) = (c + 0 * d, c + (-1) * d) := by
    rw [hd_def]; ext <;> simp only <;> ring
  rw [ep, g55_prox_coef hpar hd hx (by norm_num)] at hprox
  have hl1 : -1 < l ∧ l ≤ N := by
    rcases hprox with h | h
    · constructor <;> linarith [h.1, h.2]
    · exfalso; linarith [h.1, h.2]
  have exr : xr ρ (c, x2) = c + ρ * d := by simp only [xr, hd_def]
  have exe : xe ρ χ (c, x2) = c + (ρ * χ) * d := by simp only [xe, hd_def]
  have exc : xc ρ γ (c, x2) = c + (ρ * γ) * d := by simp only [xc, hd_def]
  have excc : xcc γ (c, x2) = c + (-γ) * d := by simp only [xcc, hd_def]; ring
  have e0 : c = c + 0 * d := by ring
  have e2 : x2 = c + (-1) * d := by rw [hd_def]; ring
  have M := fun α β (h : (l ≤ α ∧ α < β) ∨ (β < α ∧ α ≤ l)) => g55_Ml hf hmin hd hx h
  have hns := g55_noS_state hf hpar (c, x2) hp hle
  rcases hm : move f ρ χ γ (c, x2) with _ | _ | _ | _ | _
  · -- reflect
    have hh := g55_mv_R hm
    have h1 : f (c + ρ * d) < f (c + 0 * d) := by rw [← e0, ← exr]; exact hh.1
    have h2 : ¬ f (c + (ρ * χ) * d) < f (c + ρ * d) := by rw [← exr, ← exe]; exact hh.2
    rw [g55_step_R hm, exr]
    rw [show (c + ρ * d, c) = (c + ρ * d, c + 0 * d) by simp,
      g55_prox_coef hpar hd hx (by intro h; linarith)]
    left; constructor
    · by_contra hc; push_neg at hc
      exact absurd (M 0 ρ (Or.inl ⟨hc, hρ⟩)) (not_lt.2 h1.le)
    · by_contra hc; push_neg at hc
      apply h2; apply M; right; constructor <;> nlinarith
  · -- expand
    have hh := g55_mv_E hm
    have h1 : f (c + ρ * d) < f (c + 0 * d) := by rw [← e0, ← exr]; exact hh.1
    rw [g55_step_E hm, exe]
    rw [show (c + ρ * χ * d, c) = (c + (ρ * χ) * d, c + 0 * d) by simp,
      g55_prox_coef hpar hd hx (by intro h; nlinarith)]
    left; constructor
    · by_contra hc; push_neg at hc
      exact absurd (M 0 ρ (Or.inl ⟨hc, hρ⟩)) (not_lt.2 h1.le)
    · nlinarith
  · -- outside
    have hh := g55_mv_O hm
    rw [g55_step_O hm, exr, exc] at *
    have hlr : l < ρ := by
      by_contra hc; push_neg at hc
      apply hh.1; simp only; nth_rewrite 2 [e0]; exact M ρ 0 (Or.inr ⟨hρ, hc⟩)
    unfold place
    split_ifs with hc1
    · rw [show (c + ρ * γ * d, c) = (c + (ρ * γ) * d, c + 0 * d) by simp,
        g55_prox_coef hpar hd hx (by intro h; nlinarith)]
      left; constructor
      · by_contra hc; push_neg at hc
        have := M 0 (ρ * γ) (Or.inl ⟨hc, by positivity⟩)
        rw [← e0] at this; linarith
      · nlinarith
    · rw [show (c, c + ρ * γ * d) = (c + 0 * d, c + (ρ * γ) * d) by simp,
        g55_prox_coef hpar hd hx (by intro h; nlinarith)]
      right; constructor
      · nlinarith
      · by_contra hc; push_neg at hc
        apply hc1
        have := M (ρ * γ) 0 (Or.inr ⟨by positivity, hc⟩)
        rw [← e0] at this; exact this
  · -- inside
    have hh := g55_mv_I hm
    rw [g55_step_I hm, exr, excc] at *
    have hlr : l < ρ := by
      by_contra hc; push_neg at hc
      apply hh.2.1; simp only
      have := M ρ 0 (Or.inr ⟨hρ, hc⟩); rw [← e0] at this; linarith
    unfold place
    split_ifs with hc1
    · rw [show (c + -γ * d, c) = (c + (-γ) * d, c + 0 * d) by simp,
        g55_prox_coef hpar hd hx (by intro h; linarith)]
      right; constructor
      · nlinarith
      · by_contra hc; push_neg at hc
        have := M 0 (-γ) (Or.inr ⟨by linarith, hc⟩)
        rw [← e0] at this; linarith
    · rw [show (c, c + -γ * d) = (c + 0 * d, c + (-γ) * d) by simp,
        g55_prox_coef hpar hd hx (by intro h; linarith)]
      left; constructor
      · by_contra hc; push_neg at hc
        apply hc1
        have := M (-γ) 0 (Or.inl ⟨hc, by linarith⟩)
        rw [← e0] at this; exact this
      · nlinarith
  · exact absurd hm hns

theorem lemma_4_3_core (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ) :
    ∀ k : ℕ, Proximity ρ χ γ xmin (run f ρ χ γ σ p0 k) →
      Proximity ρ χ γ xmin (run f ρ χ γ σ p0 (k + 1)) := by
  intro k hk
  rw [g55_run_succ]
  exact g55_prox_step hf hmin hpar hρχ _ (g55_inv hpar h0 k).1 (g55_inv hpar h0 k).2 hk

end l43

section l44
variable {f : ℝ → ℝ}

lemma g55_acc_bd (hf : StrictConvexOn ℝ Set.univ f) {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ)
    (p : ℝ × ℝ) (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) :
    f (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) ≤ (1 - γ) * f p.1 + γ * f p.2 := by
  have hns := g55_noS_state hf hpar p hp hle
  obtain ⟨-, hχ, -, hγ, hγ1, hσ, -⟩ := hpar
  have base : f p.1 ≤ (1 - γ) * f p.1 + γ * f p.2 := by nlinarith
  rcases hm : move f ρ χ γ p with _ | _ | _ | _ | _
  · have := g55_mv_R hm; simp only [acceptedPoint]; linarith
  · have := g55_mv_E hm; simp only [acceptedPoint]; linarith
  · have h := g55_mv_O hm; simp only [acceptedPoint]
    have := g55_H1 hf.convexOn p.1 (xr ρ p) γ hγ.le hγ1.le
    have e : xc ρ γ p = p.1 + γ * (xr ρ p - p.1) := by simp only [xc, xr]; ring
    rw [e]; nlinarith
  · simp only [acceptedPoint]
    have := g55_H1 hf.convexOn p.1 p.2 γ hγ.le hγ1.le
    have e : xcc γ p = p.1 + γ * (p.2 - p.1) := by simp only [xcc]; ring
    rw [e]; linarith
  · exact absurd hm hns

lemma g55_place_bd (x1 v B : ℝ) (h1 : f x1 ≤ B) (h2 : f v ≤ B) :
    f (place f x1 v).1 ≤ f x1 ∧ f (place f x1 v).2 ≤ B := by
  unfold place; split_ifs with h
  · exact ⟨h.le, h1⟩
  · exact ⟨le_rfl, h2⟩

lemma g55_step_bd (hf : StrictConvexOn ℝ Set.univ f) {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ)
    (p : ℝ × ℝ) (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) :
    f (step f ρ χ γ σ p).1 ≤ f p.1 ∧ f (step f ρ χ γ σ p).2 ≤ (1 - γ) * f p.1 + γ * f p.2 := by
  have hγ := hpar.2.2.2.1; have hγ1 := hpar.2.2.2.2.1
  exact g55_place_bd _ _ _ (by nlinarith) (g55_acc_bd hf hpar p hp hle)

theorem lemma_4_4_core (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∃ L : ℝ, Tendsto (fun k => f (run f ρ χ γ σ p0 k).1) atTop (𝓝 L) ∧
      Tendsto (fun k => f (run f ρ χ γ σ p0 k).2) atTop (𝓝 L) := by
  have hγ := hpar.2.2.2.1; have hγ1 := hpar.2.2.2.2.1
  set F1 := fun k => f (run f ρ χ γ σ p0 k).1 with hF1
  set F2 := fun k => f (run f ρ χ γ σ p0 k).2 with hF2
  have hinv := g55_inv hpar h0
  have hst : ∀ k, F1 (k+1) ≤ F1 k ∧ F2 (k+1) ≤ (1 - γ) * F1 k + γ * F2 k := by
    intro k; simp only [hF1, hF2]; rw [g55_run_succ]
    exact g55_step_bd hf hpar _ (hinv k).1 (hinv k).2
  have h12 : ∀ k, F1 k ≤ F2 k := fun k => (hinv k).2
  have hA1 : Antitone F1 := antitone_nat_of_succ_le (fun k => (hst k).1)
  have hA2 : Antitone F2 := antitone_nat_of_succ_le (fun k => by
    have := (hst k).2; have := h12 k; nlinarith)
  have hb1 : BddBelow (Set.range F1) := ⟨f xmin, by rintro _ ⟨k, rfl⟩; exact hmin _⟩
  have hb2 : BddBelow (Set.range F2) := ⟨f xmin, by rintro _ ⟨k, rfl⟩; exact hmin _⟩
  have t1 := tendsto_atTop_ciInf hA1 hb1
  have t2 := tendsto_atTop_ciInf hA2 hb2
  set L1 := ⨅ i, F1 i
  set L2 := ⨅ i, F2 i
  have t2' : Tendsto (fun k => F2 (k+1)) atTop (𝓝 L2) := t2.comp (tendsto_add_atTop_nat 1)
  have hle1 : L1 ≤ L2 := le_of_tendsto_of_tendsto' t1 t2 h12
  have hle2 : L2 ≤ (1 - γ) * L1 + γ * L2 :=
    le_of_tendsto_of_tendsto' t2' ((t1.const_mul (1 - γ)).add (t2.const_mul γ)) (fun k => (hst k).2)
  have : L1 = L2 := by nlinarith
  exact ⟨L1, t1, this ▸ t2⟩

end l44

end NelderMeadLD.Conv1D

open NelderMeadLD.Conv1D


theorem solution (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∃ L : ℝ, Tendsto (fun k => f (run f ρ χ γ σ p0 k).1) atTop (𝓝 L) ∧
      Tendsto (fun k => f (run f ρ χ γ σ p0 k).2) atTop (𝓝 L) := by
  exact lemma_4_4_core f hf xmin hmin ρ χ γ σ hpar p0 h0
