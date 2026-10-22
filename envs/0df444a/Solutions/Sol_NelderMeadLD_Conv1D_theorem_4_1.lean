-- Prove2me | solution 1 for NelderMeadLD.Conv1D.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T19:36:06.826374+00:00
-- url     : https://prove2.me/submissions/06bf1117-99d5-4bb9-b22c-cbe2779496a8

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

set_option autoImplicit false

open Filter Topology

namespace NM1DProof

open NelderMeadLD.Conv1D

lemma mono_right {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {a b : ℝ} (ha : xmin ≤ a) (hab : a < b) : f a < f b := by
  rcases eq_or_lt_of_le ha with h | h
  · have hab' : xmin < b := by rw [h]; exact hab
    rw [← h]
    have key := hf.2 (Set.mem_univ xmin) (Set.mem_univ b) (ne_of_lt hab')
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have h2 := hmin ((1/2:ℝ) • xmin + (1/2:ℝ) • b)
    simp only [smul_eq_mul] at key h2
    linarith
  · have hba : 0 < b - xmin := by linarith
    have hne : b - xmin ≠ 0 := hba.ne'
    have key := hf.2 (Set.mem_univ xmin) (Set.mem_univ b) (ne_of_lt (lt_trans h hab))
      (div_pos (by linarith : (0:ℝ) < b - a) hba) (div_pos (by linarith : (0:ℝ) < a - xmin) hba)
      (by rw [← add_div]; exact (div_eq_one_iff_eq hne).mpr (by ring))
    have e : ((b - a) / (b - xmin)) • xmin + ((a - xmin) / (b - xmin)) • b = a := by
      simp only [smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
    rw [e] at key
    simp only [smul_eq_mul] at key
    have hc : (b - a) / (b - xmin) * f xmin ≤ (b - a) / (b - xmin) * f b :=
      mul_le_mul_of_nonneg_left (hmin b) (div_pos (by linarith) hba).le
    have hsum : (b - a) / (b - xmin) * f b + (a - xmin) / (b - xmin) * f b = f b := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
    linarith

lemma mono_left {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {a b : ℝ} (hab : a < b) (hb : b ≤ xmin) : f b < f a := by
  rcases eq_or_lt_of_le hb with h | h
  · have hab' : a < xmin := by rw [← h]; exact hab
    rw [h]
    have key := hf.2 (Set.mem_univ a) (Set.mem_univ xmin) (ne_of_lt hab')
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have h2 := hmin ((1/2:ℝ) • a + (1/2:ℝ) • xmin)
    simp only [smul_eq_mul] at key h2
    linarith
  · have hba : 0 < xmin - a := by linarith
    have hne : xmin - a ≠ 0 := hba.ne'
    have key := hf.2 (Set.mem_univ a) (Set.mem_univ xmin) (ne_of_lt (lt_trans hab h))
      (div_pos (by linarith : (0:ℝ) < xmin - b) hba) (div_pos (by linarith : (0:ℝ) < b - a) hba)
      (by rw [← add_div]; exact (div_eq_one_iff_eq hne).mpr (by ring))
    have e : ((xmin - b) / (xmin - a)) • a + ((b - a) / (xmin - a)) • xmin = b := by
      simp only [smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
    rw [e] at key
    simp only [smul_eq_mul] at key
    have hc : (b - a) / (xmin - a) * f xmin ≤ (b - a) / (xmin - a) * f a :=
      mul_le_mul_of_nonneg_left (hmin a) (div_pos (by linarith) hba).le
    have hsum : (xmin - b) / (xmin - a) * f a + (b - a) / (xmin - a) * f a = f a := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
    linarith

lemma mono_right_le {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {a b : ℝ} (ha : xmin ≤ a) (hab : a ≤ b) : f a ≤ f b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact (mono_right hf hmin ha h).le

lemma mono_left_le {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ xmin) : f b ≤ f a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact (mono_left hf hmin h hb).le

lemma place_cases (f : ℝ → ℝ) (x v : ℝ) :
    (place f x v = (v, x) ∧ f v < f x) ∨ (place f x v = (x, v) ∧ f x ≤ f v) := by
  unfold place
  by_cases h : f v < f x
  · left; rw [if_pos h]; exact ⟨rfl, h⟩
  · right; rw [if_neg h]; exact ⟨rfl, not_lt.mp h⟩

lemma step_spec {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {ρ χ γ σ : ℝ}
    (hpar : ParamsOK ρ χ γ σ) {p : ℝ × ℝ} (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) :
    (f (xr ρ p) < f p.1 ∧ f (xe ρ χ p) < f (xr ρ p) ∧ step f ρ χ γ σ p = (xe ρ χ p, p.1)) ∨
    (f (xr ρ p) < f p.1 ∧ f (xr ρ p) ≤ f (xe ρ χ p) ∧ step f ρ χ γ σ p = (xr ρ p, p.1)) ∨
    (f p.1 ≤ f (xr ρ p) ∧ f (xr ρ p) < f p.2 ∧ f (xc ρ γ p) < f p.2 ∧
      step f ρ χ γ σ p = place f p.1 (xc ρ γ p)) ∨
    (f p.2 ≤ f (xr ρ p) ∧ f (xcc γ p) < f p.2 ∧
      step f ρ χ γ σ p = place f p.1 (xcc γ p)) := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hd : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hstep : step f ρ χ γ σ p =
      place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) := rfl
  by_cases h1 : f (xr ρ p) < f p.1
  · by_cases h2 : f (xe ρ χ p) < f (xr ρ p)
    · left
      have hm : move f ρ χ γ p = Move.expand := by unfold move; rw [if_pos h1, if_pos h2]
      refine ⟨h1, h2, ?_⟩
      rw [hstep, hm]
      show place f p.1 (xe ρ χ p) = _
      unfold place; rw [if_pos (lt_trans h2 h1)]
    · right; left
      have hm : move f ρ χ γ p = Move.reflect := by unfold move; rw [if_pos h1, if_neg h2]
      refine ⟨h1, not_lt.mp h2, ?_⟩
      rw [hstep, hm]
      show place f p.1 (xr ρ p) = _
      unfold place; rw [if_pos h1]
  · have h1' : f p.1 ≤ f (xr ρ p) := not_lt.mp h1
    by_cases h3 : f (xr ρ p) < f p.2
    · right; right; left
      have hne : p.1 ≠ xr ρ p := by
        intro h; apply hd
        have : ρ * (p.1 - p.2) = 0 := by unfold xr at h; linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hρ.ne'
        · exact h'
      have hcv := hf.2 (Set.mem_univ p.1) (Set.mem_univ (xr ρ p)) hne
        (by linarith : (0:ℝ) < 1 - γ) hγ0 (by ring)
      simp only [smul_eq_mul] at hcv
      have e : (1 - γ) * p.1 + γ * xr ρ p = xc ρ γ p := by unfold xr xc; ring
      rw [e] at hcv
      have hm1 := mul_le_mul_of_nonneg_left h1' (by linarith : (0:ℝ) ≤ 1 - γ)
      have hc : f (xc ρ γ p) ≤ f (xr ρ p) := by linarith
      have hm : move f ρ χ γ p = Move.outside := by
        unfold move; rw [if_neg h1, if_pos h3, if_pos hc]
      refine ⟨h1', h3, lt_of_le_of_lt hc h3, ?_⟩
      rw [hstep, hm]; rfl
    · right; right; right
      have hcv := hf.2 (Set.mem_univ p.1) (Set.mem_univ p.2) hp
        (by linarith : (0:ℝ) < 1 - γ) hγ0 (by ring)
      simp only [smul_eq_mul] at hcv
      have e : (1 - γ) * p.1 + γ * p.2 = xcc γ p := by unfold xcc; ring
      rw [e] at hcv
      have hm1 := mul_le_mul_of_nonneg_left hle (by linarith : (0:ℝ) ≤ 1 - γ)
      have hcc : f (xcc γ p) < f p.2 := by linarith
      have hm : move f ρ χ γ p = Move.inside := by
        unfold move; rw [if_neg h1, if_neg h3, if_pos hcc]
      refine ⟨not_lt.mp h3, hcc, ?_⟩
      rw [hstep, hm]; rfl

lemma step_basic {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {ρ χ γ σ : ℝ}
    (hpar : ParamsOK ρ χ γ σ) {p : ℝ × ℝ} (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2) :
    (step f ρ χ γ σ p).1 ≠ (step f ρ χ γ σ p).2 ∧
      f (step f ρ χ γ σ p).1 ≤ f (step f ρ χ γ σ p).2 ∧
      f (step f ρ χ γ σ p).2 ≤ f p.2 ∧ f (step f ρ χ γ σ p).1 ≤ f p.1 := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hd : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have nz : ∀ s : ℝ, s ≠ 0 → p.1 + s * (p.1 - p.2) ≠ p.1 := fun s hs h => by
    have : s * (p.1 - p.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hs h'
    · exact hd h'
  have hxe : xe ρ χ p ≠ p.1 := nz (ρ * χ) (mul_pos hρ (by linarith)).ne'
  have hxr : xr ρ p ≠ p.1 := nz ρ hρ.ne'
  have hxc : xc ρ γ p ≠ p.1 := nz (ρ * γ) (mul_pos hρ hγ0).ne'
  have hxcc : xcc γ p ≠ p.1 := by
    have := nz (-γ) (neg_ne_zero.mpr hγ0.ne')
    unfold xcc; intro h; apply this; linarith
  rcases step_spec hf hpar hp hle with ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, h3, e⟩ | ⟨h1, h2, e⟩
  · rw [e]
    exact ⟨hxe, by show f (xe ρ χ p) ≤ f p.1; linarith, hle,
      by show f (xe ρ χ p) ≤ f p.1; linarith⟩
  · rw [e]; exact ⟨hxr, h1.le, hle, h1.le⟩
  · rw [e]
    rcases place_cases f p.1 (xc ρ γ p) with ⟨e', h'⟩ | ⟨e', h'⟩ <;> rw [e']
    · exact ⟨hxc, h'.le, hle, h'.le⟩
    · exact ⟨hxc.symm, h', h3.le, le_rfl⟩
  · rw [e]
    rcases place_cases f p.1 (xcc γ p) with ⟨e', h'⟩ | ⟨e', h'⟩ <;> rw [e']
    · exact ⟨hxcc, h'.le, hle, h'.le⟩
    · exact ⟨hxcc.symm, h', h2.le, le_rfl⟩

lemma step_fst (f : ℝ → ℝ) (ρ χ γ σ : ℝ) (p : ℝ × ℝ)
    (h : (step f ρ χ γ σ p).2 ≠ p.1) : (step f ρ χ γ σ p).1 = p.1 := by
  have e : step f ρ χ γ σ p = place f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) := rfl
  rcases place_cases f p.1 (acceptedPoint ρ χ γ σ p (move f ρ χ γ p)) with ⟨e', _⟩ | ⟨e', _⟩
  · rw [e, e'] at h; exact absurd rfl h
  · rw [e, e']

/-- Same side, right of the minimizer: the step is an expansion toward `xmin`. -/
lemma same_r {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ) (hρχ : 1 ≤ ρ * χ)
    {r τ : ℝ} (hτ0 : 0 < τ) (hτe : ρ * χ * τ < r - xmin) {p : ℝ × ℝ}
    (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2)
    (h1 : r ≤ p.1) (h1' : p.1 < r + τ) (h2 : r ≤ p.2) (h2' : p.2 < r + τ) :
    |p.1 - p.2| ≤ |(step f ρ χ γ σ p).1 - (step f ρ χ γ σ p).2| ∧
      |(step f ρ χ γ σ p).1 - xmin| + |p.1 - p.2| ≤ |p.1 - xmin| := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hχ0 : 0 < χ := by linarith
  have hρχ0 : 0 < ρ * χ * τ := by positivity
  have hrx : xmin < r := by linarith
  have hlt : p.1 < p.2 := by
    rcases lt_or_gt_of_ne hp with h | h
    · exact h
    · exfalso
      have := mono_right hf hmin (by linarith : xmin ≤ p.2) h
      linarith
  have hδ : 0 < p.2 - p.1 := by linarith
  have hδτ : p.2 - p.1 < τ := by linarith
  have hxr : xr ρ p = p.1 - ρ * (p.2 - p.1) := by unfold xr; ring
  have hxe : xe ρ χ p = p.1 - ρ * χ * (p.2 - p.1) := by unfold xe; ring
  have hA : ρ * χ * (p.2 - p.1) < ρ * χ * τ := mul_lt_mul_of_pos_left hδτ (by positivity)
  have hB : ρ * (p.2 - p.1) < ρ * χ * (p.2 - p.1) := by
    have := mul_pos (mul_pos hρ hδ) (by linarith : (0:ℝ) < χ - 1)
    nlinarith
  have hC : 0 < ρ * (p.2 - p.1) := mul_pos hρ hδ
  have hxe_gt : xmin < xe ρ χ p := by rw [hxe]; linarith
  have hxr1 : f (xr ρ p) < f p.1 :=
    mono_right hf hmin (by rw [hxr]; linarith) (by rw [hxr]; linarith)
  have hxe1 : f (xe ρ χ p) < f (xr ρ p) :=
    mono_right hf hmin hxe_gt.le (by rw [hxe, hxr]; linarith)
  have hstep : step f ρ χ γ σ p = (xe ρ χ p, p.1) := by
    rcases step_spec hf hpar hp hle with ⟨_, _, e⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact e
    · linarith
    · linarith
    · linarith
  rw [hstep]
  show |p.1 - p.2| ≤ |xe ρ χ p - p.1| ∧ |xe ρ χ p - xmin| + |p.1 - p.2| ≤ |p.1 - xmin|
  rw [hxe]
  have e1 : |p.1 - p.2| = p.2 - p.1 := by rw [abs_sub_comm]; exact abs_of_pos hδ
  have e2 : |p.1 - ρ * χ * (p.2 - p.1) - p.1| = ρ * χ * (p.2 - p.1) := by
    rw [show p.1 - ρ * χ * (p.2 - p.1) - p.1 = -(ρ * χ * (p.2 - p.1)) by ring, abs_neg]
    exact abs_of_pos (by positivity)
  have e3 : |p.1 - ρ * χ * (p.2 - p.1) - xmin| = p.1 - ρ * χ * (p.2 - p.1) - xmin :=
    abs_of_pos (by linarith)
  have e4 : |p.1 - xmin| = p.1 - xmin := abs_of_pos (by linarith)
  rw [e1, e2, e3, e4]
  have := mul_le_mul_of_nonneg_right hρχ hδ.le
  constructor <;> linarith

/-- Same side, left of the minimizer. -/
lemma same_l {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ) (hρχ : 1 ≤ ρ * χ)
    {l τ : ℝ} (hτ0 : 0 < τ) (hτe : ρ * χ * τ < xmin - l) {p : ℝ × ℝ}
    (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2)
    (h1 : l - τ < p.1) (h1' : p.1 ≤ l) (h2 : l - τ < p.2) (h2' : p.2 ≤ l) :
    |p.1 - p.2| ≤ |(step f ρ χ γ σ p).1 - (step f ρ χ γ σ p).2| ∧
      |(step f ρ χ γ σ p).1 - xmin| + |p.1 - p.2| ≤ |p.1 - xmin| := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hχ0 : 0 < χ := by linarith
  have hρχ0 : 0 < ρ * χ * τ := by positivity
  have hlx : l < xmin := by linarith
  have hlt : p.2 < p.1 := by
    rcases lt_or_gt_of_ne hp with h | h
    · exfalso
      have := mono_left hf hmin h (by linarith : p.2 ≤ xmin)
      linarith
    · exact h
  have hδ : 0 < p.1 - p.2 := by linarith
  have hδτ : p.1 - p.2 < τ := by linarith
  have hxr : xr ρ p = p.1 + ρ * (p.1 - p.2) := by unfold xr; ring
  have hxe : xe ρ χ p = p.1 + ρ * χ * (p.1 - p.2) := by unfold xe; ring
  have hA : ρ * χ * (p.1 - p.2) < ρ * χ * τ := mul_lt_mul_of_pos_left hδτ (by positivity)
  have hB : ρ * (p.1 - p.2) < ρ * χ * (p.1 - p.2) := by
    have := mul_pos (mul_pos hρ hδ) (by linarith : (0:ℝ) < χ - 1)
    nlinarith
  have hC : 0 < ρ * (p.1 - p.2) := mul_pos hρ hδ
  have hxe_lt : xe ρ χ p < xmin := by rw [hxe]; linarith
  have hxr1 : f (xr ρ p) < f p.1 :=
    mono_left hf hmin (by rw [hxr]; linarith) (by rw [hxr]; linarith)
  have hxe1 : f (xe ρ χ p) < f (xr ρ p) :=
    mono_left hf hmin (by rw [hxe, hxr]; linarith) hxe_lt.le
  have hstep : step f ρ χ γ σ p = (xe ρ χ p, p.1) := by
    rcases step_spec hf hpar hp hle with ⟨_, _, e⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact e
    · linarith
    · linarith
    · linarith
  rw [hstep]
  show |p.1 - p.2| ≤ |xe ρ χ p - p.1| ∧ |xe ρ χ p - xmin| + |p.1 - p.2| ≤ |p.1 - xmin|
  rw [hxe]
  have e1 : |p.1 - p.2| = p.1 - p.2 := abs_of_pos hδ
  have e2 : |p.1 + ρ * χ * (p.1 - p.2) - p.1| = ρ * χ * (p.1 - p.2) := by
    rw [show p.1 + ρ * χ * (p.1 - p.2) - p.1 = ρ * χ * (p.1 - p.2) by ring]
    exact abs_of_pos (by positivity)
  have e3 : |p.1 + ρ * χ * (p.1 - p.2) - xmin| = xmin - (p.1 + ρ * χ * (p.1 - p.2)) := by
    rw [abs_of_neg (by linarith)]; ring
  have e4 : |p.1 - xmin| = xmin - p.1 := by rw [abs_of_neg (by linarith)]; ring
  rw [e1, e2, e3, e4]
  have := mul_le_mul_of_nonneg_right hρχ hδ.le
  constructor <;> linarith

/-- Opposite sides (best vertex left): an inside contraction lands strictly inside `(l, r)`. -/
lemma opp_lr {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ)
    {l r L τ : ℝ} (hin : ∀ x, l < x → x < r → f x < L) (hlx : l < xmin)
    (hτρ : τ < ρ * (r - l)) (hτ1 : (1 - γ) * τ < γ * (r - l)) (hτ2 : γ * τ < (1 - γ) * (r - l))
    {p : ℝ × ℝ} (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2)
    (h1 : l - τ < p.1) (h1' : p.1 ≤ l) (h2 : r ≤ p.2) (h2' : p.2 < r + τ)
    (hT : f p.2 < f (l - τ)) : f (step f ρ χ γ σ p).1 < L := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hxr : xr ρ p < l - τ := by
    have := mul_le_mul_of_nonneg_left (show p.1 - p.2 ≤ l - r by linarith) hρ.le
    unfold xr; linarith
  have hfxr : f (l - τ) < f (xr ρ p) := mono_left hf hmin hxr (by linarith)
  have hcc1 : l < xcc γ p := by
    have a := mul_lt_mul_of_pos_left h1 (by linarith : (0:ℝ) < 1 - γ)
    have b := mul_le_mul_of_nonneg_left h2 hγ0.le
    unfold xcc; nlinarith
  have hcc2 : xcc γ p < r := by
    have a := mul_le_mul_of_nonneg_left h1' (by linarith : (0:ℝ) ≤ 1 - γ)
    have b := mul_lt_mul_of_pos_left h2' hγ0
    unfold xcc; nlinarith
  have hfcc : f (xcc γ p) < L := hin _ hcc1 hcc2
  rcases step_spec hf hpar hp hle with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, e⟩
  · linarith
  · linarith
  · linarith
  · rw [e]
    rcases place_cases f p.1 (xcc γ p) with ⟨e', _⟩ | ⟨e', h'⟩
    · rw [e']; exact hfcc
    · rw [e']; exact lt_of_le_of_lt h' hfcc

/-- Opposite sides (best vertex right). -/
lemma opp_rl {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ)
    {l r L τ : ℝ} (hin : ∀ x, l < x → x < r → f x < L) (hrx : xmin < r) (hτ0 : 0 < τ)
    (hτρ : τ < ρ * (r - l)) (hτ1 : (1 - γ) * τ < γ * (r - l)) (hτ2 : γ * τ < (1 - γ) * (r - l))
    {p : ℝ × ℝ} (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2)
    (h1 : r ≤ p.1) (h1' : p.1 < r + τ) (h2 : l - τ < p.2) (h2' : p.2 ≤ l)
    (hT : f p.2 < f (r + τ)) : f (step f ρ χ γ σ p).1 < L := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hxr : r + τ < xr ρ p := by
    have := mul_le_mul_of_nonneg_left (show r - l ≤ p.1 - p.2 by linarith) hρ.le
    unfold xr; linarith
  have hfxr : f (r + τ) < f (xr ρ p) := mono_right hf hmin (by linarith) hxr
  have hcc1 : l < xcc γ p := by
    have a := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - γ)
    have b := mul_lt_mul_of_pos_left h2 hγ0
    unfold xcc; nlinarith
  have hcc2 : xcc γ p < r := by
    have a := mul_lt_mul_of_pos_left h1' (by linarith : (0:ℝ) < 1 - γ)
    have b := mul_le_mul_of_nonneg_left h2' hγ0.le
    unfold xcc; nlinarith
  have hfcc : f (xcc γ p) < L := hin _ hcc1 hcc2
  rcases step_spec hf hpar hp hle with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, e⟩
  · linarith
  · linarith
  · linarith
  · rw [e]
    rcases place_cases f p.1 (xcc γ p) with ⟨e', _⟩ | ⟨e', h'⟩
    · rw [e']; exact hfcc
    · rw [e']; exact lt_of_le_of_lt h' hfcc

/-- Fixed best vertex `c ∈ (l, r)`: the step must be an outside contraction. -/
lemma caseII_step {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {ρ χ γ σ : ℝ}
    (hpar : ParamsOK ρ χ γ σ) {l r L τ : ℝ} (hin : ∀ x, l < x → x < r → f x < L)
    {p : ℝ × ℝ} (hp : p.1 ≠ p.2) (hle : f p.1 ≤ f p.2)
    (hτa : γ * τ ≤ (1 - γ) * (r - p.1)) (hτb : γ * τ ≤ (1 - γ) * (p.1 - l))
    (hpos : (l - τ < p.2 ∧ p.2 ≤ l) ∨ (r ≤ p.2 ∧ p.2 < r + τ))
    (hcl : l < p.1) (hcr : p.1 < r)
    (hnot : (step f ρ χ γ σ p).2 ≠ p.1) (hL2 : L ≤ f (step f ρ χ γ σ p).2) :
    step f ρ χ γ σ p = (p.1, xc ρ γ p) ∧ f (xc ρ γ p) < f p.2 := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hcc : f (xcc γ p) < L := by
    apply hin <;> unfold xcc
    · rcases hpos with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · have := mul_lt_mul_of_pos_left (show p.1 - p.2 < p.1 - l + τ by linarith) hγ0
        linarith
      · have := mul_pos hγ0 (show 0 < p.2 - p.1 by linarith)
        linarith
    · rcases hpos with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · have := mul_pos hγ0 (show 0 < p.1 - p.2 by linarith)
        linarith
      · have := mul_lt_mul_of_pos_left (show p.2 - p.1 < r + τ - p.1 by linarith) hγ0
        linarith
  rcases step_spec hf hpar hp hle with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, h3, e⟩ | ⟨_, _, e⟩
  · rw [e] at hnot; exact absurd rfl hnot
  · rw [e] at hnot; exact absurd rfl hnot
  · rcases place_cases f p.1 (xc ρ γ p) with ⟨e', _⟩ | ⟨e', _⟩
    · rw [e, e'] at hnot; exact absurd rfl hnot
    · exact ⟨e.trans e', h3⟩
  · exfalso
    rcases place_cases f p.1 (xcc γ p) with ⟨e', _⟩ | ⟨e', _⟩
    · rw [e, e'] at hnot; exact hnot rfl
    · rw [e, e'] at hL2; exact absurd hL2 (not_le.mpr hcc)

lemma drift_contra (d E : ℕ → ℝ) (K : ℕ) (hd : 0 < d K) (hE : ∀ k, 0 ≤ E k)
    (h : ∀ k, K ≤ k → d k ≤ d (k+1) ∧ E (k+1) + d k ≤ E k) : False := by
  have key : ∀ j : ℕ, d K ≤ d (K + j) ∧ E (K + j) + j * d K ≤ E K := by
    intro j
    induction j with
    | zero => simp
    | succ n ih =>
      obtain ⟨h1, h2⟩ := h (K + n) (by omega)
      have e : ((n + 1 : ℕ) : ℝ) * d K = n * d K + d K := by push_cast; ring
      refine ⟨le_trans ih.1 h1, ?_⟩
      rw [show K + (n + 1) = K + n + 1 by omega, e]
      linarith [ih.1, ih.2]
  obtain ⟨j, hj⟩ := exists_nat_gt (E K / d K)
  have h1 := (key j).2
  have h2 := hE (K + j)
  have h3 : E K < j * d K := by rwa [div_lt_iff₀ hd] at hj
  linarith

lemma geo_contra {q δ1 δ2 : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (hδ1 : 0 < δ1) (w : ℕ → ℝ)
    (hw : ∀ j, w (j+1) = -q * w j) (hb : ∀ j, δ1 ≤ |w j| ∧ |w j| ≤ δ2) : False := by
  have habs : ∀ j, |w j| = q ^ j * |w 0| := by
    intro j
    induction j with
    | zero => simp
    | succ n ih => rw [hw n, abs_mul, abs_neg, abs_of_pos hq0, ih, pow_succ]; ring
  have hw0 : δ1 ≤ |w 0| := (hb 0).1
  have hw0' : |w 0| ≤ δ2 := (hb 0).2
  have hδ2 : 0 < δ2 := by linarith
  rcases lt_or_gt_of_ne hq1 with h | h
  · obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hδ1 hδ2) h
    have h1 := (hb j).1
    rw [habs j] at h1
    have h2 : q ^ j * |w 0| ≤ q ^ j * δ2 := mul_le_mul_of_nonneg_left hw0' (by positivity)
    have h3 : q ^ j * δ2 < δ1 := by rwa [lt_div_iff₀ hδ2] at hj
    linarith
  · obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (δ2 / δ1) h
    have h1 := (hb j).2
    rw [habs j] at h1
    have h2 : q ^ j * δ1 ≤ q ^ j * |w 0| := mul_le_mul_of_nonneg_left hw0 (by positivity)
    have h3 : δ2 < q ^ j * δ1 := by rwa [div_lt_iff₀ hδ1] at hj
    linarith

lemma exists_r {f : ℝ → ℝ} (hcont : Continuous f) {xmin L : ℝ}
    (hmono : ∀ a b, xmin ≤ a → a < b → f a < f b) (hL : f xmin < L)
    (hbdd : BddAbove {x | f x < L}) :
    ∃ r, xmin < r ∧ (∀ x, xmin ≤ x → x < r → f x < L) ∧ (∀ x, r ≤ x → L ≤ f x) := by
  have hnear : ∀ y, f y < L → ∃ ε > 0, ∀ z, |z - y| < ε → f z < L := by
    intro y hy
    have := (hcont.tendsto y).eventually (gt_mem_nhds hy)
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp this
    exact ⟨ε, hε, fun z hz => h (by rw [Real.dist_eq]; exact hz)⟩
  let S : Set ℝ := {x | xmin ≤ x ∧ f x < L}
  have hSne : S.Nonempty := ⟨xmin, le_rfl, hL⟩
  have hSb : BddAbove S := hbdd.mono (fun x hx => hx.2)
  obtain ⟨ε, hε, hε'⟩ := hnear xmin hL
  have hmem : xmin + ε / 2 ∈ S := ⟨by linarith, hε' _ (by
    rw [show xmin + ε / 2 - xmin = ε / 2 by ring, abs_of_pos (by linarith)]; linarith)⟩
  have hsup := le_csSup hSb hmem
  refine ⟨sSup S, by linarith, ?_, ?_⟩
  · intro x hx hxr
    obtain ⟨s, hs, hxs⟩ := exists_lt_of_lt_csSup hSne hxr
    exact lt_trans (hmono x s hx hxs) hs.2
  · intro x hx
    by_contra h
    push_neg at h
    obtain ⟨δ, hδ, hδ'⟩ := hnear x h
    have hxS : x + δ / 2 ∈ S := ⟨by linarith, hδ' _ (by
      rw [show x + δ / 2 - x = δ / 2 by ring, abs_of_pos (by linarith)]; linarith)⟩
    have := le_csSup hSb hxS
    linarith

lemma no_gap {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    {xmin : ℝ} (hmin : ∀ y, f xmin ≤ f y)
    {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ) (hρχ : 1 ≤ ρ * χ)
    (p : ℕ → ℝ × ℝ) (hrun : ∀ k, p (k+1) = step f ρ χ γ σ (p k))
    (hinv : ∀ k, (p k).1 ≠ (p k).2 ∧ f (p k).1 ≤ f (p k).2)
    {L : ℝ} (hmL : f xmin < L) (hbL : ∀ k, L ≤ f (p k).2)
    (hbT : ∀ T, L < T → ∃ K, ∀ k, K ≤ k → f (p k).2 < T) : False := by
  have hpar' := hpar
  obtain ⟨hρ, hχ, _, hγ0, hγ1, _, _⟩ := hpar'
  have hcont : Continuous f := continuousOn_univ.mp (hf.convexOn.continuousOn isOpen_univ)
  have hbA : BddAbove {x | f x < L} :=
    (hlev L).bddAbove.mono (fun x hx => le_of_lt (show f x < L from hx))
  have hbB : BddBelow {x | f x < L} :=
    (hlev L).bddBelow.mono (fun x hx => le_of_lt (show f x < L from hx))
  obtain ⟨r, hrx, hinR, houtR⟩ :=
    exists_r hcont (fun a b ha hab => mono_right hf hmin ha hab) hmL hbA
  obtain ⟨r', hrx', hinR', houtR'⟩ :=
    exists_r (f := fun x => f (-x)) (xmin := -xmin) (L := L) (hcont.comp continuous_neg)
      (fun a b ha hab => mono_left hf hmin (by linarith : -b < -a) (by linarith))
      (by simpa using hmL)
      (by
        obtain ⟨B, hB⟩ := hbB
        exact ⟨-B, fun x hx => by
          have := hB (show -x ∈ {x | f x < L} from hx)
          linarith⟩)
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = -r' := ⟨_, rfl⟩
  have hlx : l < xmin := by rw [hl]; linarith
  have hinL : ∀ x, l < x → x ≤ xmin → f x < L := fun x h1 h2 => by
    have := hinR' (-x) (by linarith) (by rw [hl] at h1; linarith)
    simpa using this
  have houtL : ∀ x, x ≤ l → L ≤ f x := fun x h => by
    have := houtR' (-x) (by rw [hl] at h; linarith)
    simpa using this
  have hin : ∀ x, l < x → x < r → f x < L := fun x h1 h2 => by
    rcases le_or_gt xmin x with h | h
    · exact hinR x h h2
    · exact hinL x h1 h.le
  have hfr : ∀ τ : ℝ, 0 < τ → L < f (r + τ) := fun τ hτ => by
    have h1 := houtR (r + τ / 2) (by linarith)
    have h2 := mono_right hf hmin (by linarith : xmin ≤ r + τ / 2) (by linarith : r + τ / 2 < r + τ)
    linarith
  have hfl : ∀ τ : ℝ, 0 < τ → L < f (l - τ) := fun τ hτ => by
    have h1 := houtL (l - τ / 2) (by linarith)
    have h2 := mono_left hf hmin (by linarith : l - τ < l - τ / 2) (by linarith : l - τ / 2 ≤ xmin)
    linarith
  have hpos : ∀ τ : ℝ, 0 < τ → ∀ x, L ≤ f x → f x < f (l - τ) → f x < f (r + τ) →
      (l - τ < x ∧ x ≤ l) ∨ (r ≤ x ∧ x < r + τ) := by
    intro τ hτ x h1 h2 h3
    rcases le_or_gt xmin x with hx | hx
    · right
      constructor
      · by_contra h; push_neg at h; linarith [hinR x hx h]
      · by_contra h; push_neg at h
        linarith [mono_right_le hf hmin (by linarith : xmin ≤ r + τ) h]
    · left
      constructor
      · by_contra h; push_neg at h
        linarith [mono_left_le hf hmin h (by linarith : l - τ ≤ xmin)]
      · by_contra h; push_neg at h; linarith [hinL x h hx.le]
  have hev : ∀ c a : ℝ, 0 < a → ∀ᶠ τ in 𝓝[>] (0:ℝ), c * τ < a := by
    intro c a ha
    have ht : Tendsto (fun τ : ℝ => c * τ) (𝓝 0) (𝓝 0) := by
      have := (continuous_const_mul c).tendsto 0
      simpa using this
    exact nhdsWithin_le_nhds (ht.eventually (gt_mem_nhds ha))
  by_cases hA : ∀ k, L ≤ f (p k).1
  · -- every vertex value stays at least `L`
    obtain ⟨τ, hτ0, h1, h2, h3, h4, h5⟩ :=
      ((eventually_mem_nhdsWithin).and ((hev 1 (ρ * (r - l)) (mul_pos hρ (by linarith))).and
        ((hev (1 - γ) (γ * (r - l)) (mul_pos hγ0 (by linarith))).and
        ((hev γ ((1 - γ) * (r - l)) (mul_pos (by linarith) (by linarith))).and
        ((hev (ρ * χ) (r - xmin) (by linarith)).and
        (hev (ρ * χ) (xmin - l) (by linarith))))))).exists
    have hτ : (0:ℝ) < τ := hτ0
    obtain ⟨K, hK⟩ := hbT (min (f (l - τ)) (f (r + τ))) (lt_min (hfl τ hτ) (hfr τ hτ))
    have key : ∀ k, K ≤ k → |(p k).1 - (p k).2| ≤ |(p (k+1)).1 - (p (k+1)).2| ∧
        |(p (k+1)).1 - xmin| + |(p k).1 - (p k).2| ≤ |(p k).1 - xmin| := by
      intro k hk
      have hb := hK k hk
      have hTl : f (p k).2 < f (l - τ) := lt_of_lt_of_le hb (min_le_left _ _)
      have hTr : f (p k).2 < f (r + τ) := lt_of_lt_of_le hb (min_le_right _ _)
      obtain ⟨hne, hle⟩ := hinv k
      have q1 := hpos τ hτ (p k).1 (hA k) (lt_of_le_of_lt hle hTl) (lt_of_le_of_lt hle hTr)
      have q2 := hpos τ hτ (p k).2 (hbL k) hTl hTr
      have hA1 := hA (k+1)
      rw [hrun k] at hA1 ⊢
      rcases q1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases q2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact same_l hf hmin hpar hρχ hτ h5 hne hle a1 a2 b1 b2
      · exfalso
        have := opp_lr hf hmin hpar hin hlx (by linarith) h2 h3 hne hle a1 a2 b1 b2 hTl
        linarith
      · exfalso
        have := opp_rl hf hmin hpar hin hrx hτ (by linarith) h2 h3 hne hle a1 a2 b1 b2 hTr
        linarith
      · exact same_r hf hmin hpar hρχ hτ h4 hne hle a1 a2 b1 b2
    exact drift_contra (fun k => |(p k).1 - (p k).2|) (fun k => |(p k).1 - xmin|) K
      (abs_pos.mpr (sub_ne_zero.mpr (hinv K).1)) (fun k => abs_nonneg _) key
  · -- the best value drops below `L`: the best vertex freezes
    push_neg at hA
    obtain ⟨K0, hK0⟩ := hA
    have hanti : Antitone (fun k => f (p k).1) := antitone_nat_of_succ_le (fun k => by
      show f (p (k+1)).1 ≤ f (p k).1
      rw [hrun k]; exact (step_basic hf hpar (hinv k).1 (hinv k).2).2.2.2)
    have hnot : ∀ k, K0 ≤ k → (p (k+1)).2 ≠ (p k).1 := fun k hk h => by
      have h1 := hbL (k+1)
      rw [h] at h1
      have h2 : f (p k).1 ≤ f (p K0).1 := hanti hk
      linarith
    have hfst : ∀ k, K0 ≤ k → (p (k+1)).1 = (p k).1 := fun k hk => by
      have := hnot k hk
      rw [hrun k] at this ⊢
      exact step_fst f ρ χ γ σ (p k) this
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (p K0).1 := ⟨_, rfl⟩
    have hc : ∀ k, K0 ≤ k → (p k).1 = c := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hcdef.symm
      | succ n hn ih => rw [hfst n hn, ih]
    have hfc : f c < L := by rw [hcdef]; exact hK0
    have hcl : l < c := by
      by_contra h; push_neg at h; linarith [houtL c h]
    have hcr : c < r := by
      by_contra h; push_neg at h; linarith [houtR c h]
    obtain ⟨τ, hτ0, h1, h2⟩ :=
      ((eventually_mem_nhdsWithin).and
        ((hev γ ((1 - γ) * (r - c)) (mul_pos (by linarith) (by linarith))).and
        (hev γ ((1 - γ) * (c - l)) (mul_pos (by linarith) (by linarith))))).exists
    have hτ : (0:ℝ) < τ := hτ0
    obtain ⟨K1, hK1⟩ := hbT (min (f (l - τ)) (f (r + τ))) (lt_min (hfl τ hτ) (hfr τ hτ))
    obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = max K0 K1 := ⟨_, rfl⟩
    have hpos2 : ∀ k, K ≤ k →
        (l - τ < (p k).2 ∧ (p k).2 ≤ l) ∨ (r ≤ (p k).2 ∧ (p k).2 < r + τ) := fun k hk => by
      have hb := hK1 k (le_trans (hKdef ▸ le_max_right _ _) hk)
      exact hpos τ hτ (p k).2 (hbL k) (lt_of_lt_of_le hb (min_le_left _ _))
        (lt_of_lt_of_le hb (min_le_right _ _))
    have hstep : ∀ k, K ≤ k →
        (p (k+1)).2 - c = -(ρ * γ) * ((p k).2 - c) ∧ f (p (k+1)).2 < f (p k).2 := by
      intro k hk
      have hk0 : K0 ≤ k := le_trans (hKdef ▸ le_max_left _ _) hk
      have hck := hc k hk0
      obtain ⟨hne, hle⟩ := hinv k
      have hn := hnot k hk0
      have hL2 := hbL (k+1)
      rw [hrun k] at hn hL2 ⊢
      have hs := caseII_step hf hpar hin hne hle (by rw [hck]; linarith) (by rw [hck]; linarith)
        (hpos2 k hk) (by rw [hck]; exact hcl) (by rw [hck]; exact hcr) hn hL2
      rw [hs.1]
      refine ⟨?_, hs.2⟩
      show xc ρ γ (p k) - c = _
      unfold xc; rw [hck]; ring
    have hwrec : ∀ j : ℕ, (p (K + (j+1))).2 - c = -(ρ * γ) * ((p (K + j)).2 - c) :=
      fun j => (hstep (K + j) (by omega)).1
    have hbounds : ∀ j : ℕ, min (r - c) (c - l) ≤ |(p (K + j)).2 - c| ∧
        |(p (K + j)).2 - c| ≤ (r - l) + τ := by
      intro j
      rcases hpos2 (K + j) (by omega) with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [abs_of_neg (by linarith)]
        constructor
        · linarith [min_le_right (r - c) (c - l)]
        · linarith
      · rw [abs_of_pos (by linarith)]
        constructor
        · linarith [min_le_left (r - c) (c - l)]
        · linarith
    rcases lt_trichotomy (ρ * γ) 1 with hq | hq | hq
    · exact geo_contra (mul_pos hρ hγ0) (ne_of_lt hq) (lt_min (by linarith) (by linarith))
        (fun j => (p (K + j)).2 - c) hwrec hbounds
    · have a := hwrec 0
      have b := hwrec 1
      rw [hq] at a b
      have e2 : (p (K + 2)).2 = (p K).2 := by
        simp only [Nat.zero_add, Nat.add_zero, neg_mul, one_mul] at a b
        have e3 : K + (1 + 1) = K + 2 := rfl
        rw [e3] at b
        linarith
      have s1 := (hstep K le_rfl).2
      have s2 := (hstep (K + 1) (by omega)).2
      have e4 : p (K + 1 + 1) = p (K + 2) := rfl
      rw [e4, e2] at s2
      linarith
    · exact geo_contra (mul_pos hρ hγ0) (ne_of_gt hq) (lt_min (by linarith) (by linarith))
        (fun j => (p (K + j)).2 - c) hwrec hbounds

lemma conv_of_val {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {xmin : ℝ}
    (hmin : ∀ y, f xmin ≤ f y) {z : ℕ → ℝ}
    (hz : Tendsto (fun k => f (z k)) atTop (𝓝 (f xmin))) : Tendsto z atTop (𝓝 xmin) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : f xmin < f (xmin + ε) := mono_right hf hmin le_rfl (by linarith)
  have h2 : f xmin < f (xmin - ε) := mono_left hf hmin (by linarith) le_rfl
  have hη : 0 < min (f (xmin + ε)) (f (xmin - ε)) - f xmin := by
    have := lt_min h1 h2; linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz _ hη
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rw [Real.dist_eq] at hd ⊢
  have hlt : f (z n) < min (f (xmin + ε)) (f (xmin - ε)) := by
    have := (abs_lt.mp hd).2; linarith
  rw [abs_lt]
  constructor
  · by_contra h
    push_neg at h
    have := mono_left_le hf hmin (show z n ≤ xmin - ε by linarith) (by linarith : xmin - ε ≤ xmin)
    linarith [min_le_right (f (xmin + ε)) (f (xmin - ε))]
  · by_contra h
    push_neg at h
    have := mono_right_le hf hmin (by linarith : xmin ≤ xmin + ε) (show xmin + ε ≤ z n by linarith)
    linarith [min_le_left (f (xmin + ε)) (f (xmin - ε))]

lemma main_conv {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    {xmin : ℝ} (hmin : ∀ y, f xmin ≤ f y)
    {ρ χ γ σ : ℝ} (hpar : ParamsOK ρ χ γ σ) (hρχ : 1 ≤ ρ * χ)
    (p : ℕ → ℝ × ℝ) (hrun : ∀ k, p (k+1) = step f ρ χ γ σ (p k))
    (h0 : (p 0).1 ≠ (p 0).2 ∧ f (p 0).1 ≤ f (p 0).2) :
    Tendsto (fun k => (p k).1) atTop (𝓝 xmin) ∧ Tendsto (fun k => (p k).2) atTop (𝓝 xmin) := by
  have hinv : ∀ k, (p k).1 ≠ (p k).2 ∧ f (p k).1 ≤ f (p k).2 := by
    intro k
    induction k with
    | zero => exact h0
    | succ n ih =>
      rw [hrun n]
      exact ⟨(step_basic hf hpar ih.1 ih.2).1, (step_basic hf hpar ih.1 ih.2).2.1⟩
  have hanti : Antitone (fun k => f (p k).2) := antitone_nat_of_succ_le (fun k => by
    show f (p (k+1)).2 ≤ f (p k).2
    rw [hrun k]; exact (step_basic hf hpar (hinv k).1 (hinv k).2).2.2.1)
  have hbdd : BddBelow (Set.range (fun k => f (p k).2)) :=
    ⟨f xmin, by rintro _ ⟨k, rfl⟩; exact hmin _⟩
  have htend := tendsto_atTop_ciInf hanti hbdd
  have hLge : f xmin ≤ ⨅ k, f (p k).2 := le_ciInf (fun k => hmin _)
  have hLeq : (⨅ k, f (p k).2) = f xmin := by
    by_contra hne
    have hlt : f xmin < ⨅ k, f (p k).2 := lt_of_le_of_ne hLge (Ne.symm hne)
    exact no_gap hf hlev hmin hpar hρχ p hrun hinv hlt (fun k => ciInf_le hbdd k)
      (fun T hT => by
        obtain ⟨K, hK⟩ := exists_lt_of_ciInf_lt hT
        exact ⟨K, fun k hk => lt_of_le_of_lt (hanti hk) hK⟩)
  rw [hLeq] at htend
  have h2 : Tendsto (fun k => (p k).2) atTop (𝓝 xmin) := conv_of_val hf hmin htend
  have h1' : Tendsto (fun k => f (p k).1) atTop (𝓝 (f xmin)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
      (fun k => hmin _) (fun k => (hinv k).2)
  exact ⟨conv_of_val hf hmin h1', h2⟩

end NM1DProof

open Filter Topology NelderMeadLD.Conv1D in
theorem solution (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ) :
    Tendsto (fun k => (run f ρ χ γ σ p0 k).1) atTop (𝓝 xmin) ∧
      Tendsto (fun k => (run f ρ χ γ σ p0 k).2) atTop (𝓝 xmin) := by
  have hrun : ∀ k, run f ρ χ γ σ p0 (k+1) = step f ρ χ γ σ (run f ρ χ γ σ p0 k) := fun k => by
    show (step f ρ χ γ σ)^[k+1] p0 = step f ρ χ γ σ ((step f ρ χ γ σ)^[k] p0)
    exact Function.iterate_succ_apply' _ _ _
  exact NM1DProof.main_conv hf hlev hmin hpar hρχ (run f ρ χ γ σ p0) hrun h0
