-- Prove2me | solution 1 for NonconvexAG.Smooth.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:23:29.582971+00:00
-- url     : https://prove2.me/submissions/4a8e30fb-a563-417b-a957-3684f6f7f978

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

set_option autoImplicit false
open NonconvexAG.Smooth

lemma nas_Gamma_one (α : ℕ → ℝ) : Gamma α 1 = 1 := by
  simp [Gamma]

lemma nas_Gamma_succ (α : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Gamma α (k + 1) = (1 - α (k + 1)) * Gamma α k := by
  unfold Gamma
  rw [Finset.prod_Icc_succ_top (by omega), mul_comm]

lemma nas_Gamma_pos (α : ℕ → ℝ) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) (k : ℕ) :
    0 < Gamma α k := by
  unfold Gamma
  apply Finset.prod_pos
  intro i hi
  have := hα i (Finset.mem_Icc.mp hi).1
  linarith [this.2]

lemma nas_one_sub {α β lam : ℕ → ℝ} (hs : AGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ 1 - α k := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; rw [hs.1]; simp
  · have := hs.2.1 k (by omega); linarith [this.2]

lemma nas_md_succ {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (k : ℕ) :
    xmdSeq g α β lam x0 (k + 1) =
      (1 - α (k + 1)) • xagSeq g α β lam x0 k + α (k + 1) • xSeq g α β lam x0 k := by
  simp [xmdSeq]

lemma nas_x_succ {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (k : ℕ) :
    xSeq g α β lam x0 (k + 1) =
      xSeq g α β lam x0 k - lam (k + 1) • g (xmdSeq g α β lam x0 (k + 1)) := by
  rw [nas_md_succ]; rfl

lemma nas_xag_succ {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (k : ℕ) :
    xagSeq g α β lam x0 (k + 1) =
      xmdSeq g α β lam x0 (k + 1) - β (k + 1) • g (xmdSeq g α β lam x0 (k + 1)) := by
  rw [nas_md_succ]; rfl

lemma nas_alpha_pos {α β lam : ℕ → ℝ} (hs : AGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) :
    0 < α k := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; rw [hs.1]; norm_num
  · exact (hs.2.1 k (by omega)).1

lemma nas_hasDerivAt_line {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x d : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ψ (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hΨ.2.1 (x + t • d)).hasFDerivAt
  have := h2.comp_hasDerivAt t h1
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this

lemma nas_descent {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x y : E n) :
    Ψ y ≤ Ψ x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => Ψ (x + t • d) - t * inner ℝ (g x) d - L / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hder : ∀ t, HasDerivAt ψ
      (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := nas_hasDerivAt_line Ψ g L hΨ x d t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (g x) d) (inner ℝ (g x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) d)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl]; push_cast; ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (fun t _ => (hder t).continuousAt.continuousWithinAt)
    · exact (fun t _ => (hder t).differentiableAt.differentiableWithinAt)
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t).deriv]
      have h1 : inner ℝ (g (x + t • d)) d - inner ℝ (g x) d = inner ℝ (g (x + t • d) - g x) d := by
        rw [inner_sub_left]
      have h2 : inner ℝ (g (x + t • d) - g x) d ≤ ‖g (x + t • d) - g x‖ * ‖d‖ :=
        real_inner_le_norm _ _
      have h3 : ‖g (x + t • d) - g x‖ ≤ L * ‖t • d‖ := by
        have := hΨ.2.2 (x + t • d) x
        simpa using this
      have h4 : ‖t • d‖ = t * ‖d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      have h5 : ‖g (x + t • d) - g x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ := by
        rw [h4] at h3
        exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      nlinarith
  have := hanti (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
    zero_le_one
  simp only [hψ] at this
  have hxd : x + d = y := by simp [hd]
  simp at this
  rw [hxd] at this
  linarith

lemma nas_grad_ineq {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (hconv : ConvexOn ℝ Set.univ Ψ)
    (w z : E n) : Ψ w + inner ℝ (g w) (z - w) ≤ Ψ z := by
  set d := z - w with hd
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => Ψ (w + t • d)) := by
    refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
    have h := hconv.2 (Set.mem_univ (w + a • d)) (Set.mem_univ (w + b • d)) hs ht hst
    obtain rfl : t = 1 - s := by linarith
    have : w + (s * a + (1 - s) * b) • d = s • (w + a • d) + (1 - s) • (w + b • d) := by
      module
    simp only [smul_eq_mul] at h ⊢
    rw [this]; exact h
  have h0 := nas_hasDerivAt_line Ψ g L hΨ w d 0
  simp only [zero_smul, add_zero] at h0
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one h0
  rw [slope_def_field] at this
  simp at this
  have hy : w + d = z := by simp [hd]
  rw [hy] at this
  linarith

lemma nas_lemma1_le (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1)
    (θ η : ℕ → ℝ) (N : ℕ) (h : ∀ k, 1 ≤ k → k ≤ N → θ k ≤ (1 - α k) * θ (k - 1) + η k) :
    ∀ k, 1 ≤ k → k ≤ N → θ k ≤ Gamma α k * ∑ i ∈ Finset.Icc 1 k, η i / Gamma α i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hN
    have := h 1 le_rfl hN
    simp [hα1, nas_Gamma_one] at this ⊢
    exact this
  | succ k hk ih =>
    intro hN
    have ih := ih (by omega)
    have h1 := h (k + 1) (by omega) hN
    simp only [Nat.add_sub_cancel] at h1
    have h2 : 0 ≤ 1 - α (k + 1) := by linarith [(hα (k + 1) (by omega)).2]
    have hG := nas_Gamma_pos α hα (k + 1)
    rw [Finset.sum_Icc_succ_top (by omega), nas_Gamma_succ α k hk]
    have h3 := mul_le_mul_of_nonneg_left ih h2
    have h4 : (1 - α (k + 1)) * Gamma α k * (η (k + 1) / ((1 - α (k + 1)) * Gamma α k))
        = η (k + 1) := by
      rw [nas_Gamma_succ α k hk] at hG
      rw [mul_div_assoc']
      exact mul_div_cancel_left₀ _ hG.ne'
    nlinarith [h4]

lemma nas_D_succ {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n) (j : ℕ) :
    xagSeq g α β lam x0 (j + 1) - xSeq g α β lam x0 (j + 1) =
      (1 - α (j + 1)) • (xagSeq g α β lam x0 j - xSeq g α β lam x0 j)
        + (lam (j + 1) - β (j + 1)) • g (xmdSeq g α β lam x0 (j + 1)) := by
  rw [nas_xag_succ, nas_x_succ, nas_md_succ]
  module

lemma nas_real_aux (α A B : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ((1 - α) * A + B) ^ 2 ≤ (1 - α) * A ^ 2 + B ^ 2 / α := by
  rw [show (1 - α) * A ^ 2 + B ^ 2 / α = (α * ((1 - α) * A ^ 2) + B ^ 2) / α by field_simp,
    le_div_iff₀ hα]
  nlinarith [mul_nonneg (sub_nonneg.mpr hα1) (sq_nonneg (α * A - B))]

lemma nas_D_sq {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (hs : AGStepsizes α β lam)
    (x0 : E n) (j : ℕ) :
    ‖xagSeq g α β lam x0 (j + 1) - xSeq g α β lam x0 (j + 1)‖ ^ 2 ≤
      (1 - α (j + 1)) * ‖xagSeq g α β lam x0 j - xSeq g α β lam x0 j‖ ^ 2
        + (lam (j + 1) - β (j + 1)) ^ 2 / α (j + 1) *
          ‖g (xmdSeq g α β lam x0 (j + 1))‖ ^ 2 := by
  have hpos : 0 < α (j + 1) := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [hs.1]; norm_num
    · exact (hs.2.1 (j + 1) (by omega)).1
  have hle : α (j + 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [hs.1]
    · exact (hs.2.1 (j + 1) (by omega)).2.le
  have h1 := nas_D_succ g α β lam x0 j
  have h2 : ‖xagSeq g α β lam x0 (j + 1) - xSeq g α β lam x0 (j + 1)‖ ≤
      (1 - α (j + 1)) * ‖xagSeq g α β lam x0 j - xSeq g α β lam x0 j‖
        + |lam (j + 1) - β (j + 1)| * ‖g (xmdSeq g α β lam x0 (j + 1))‖ := by
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (nas_one_sub hs _ (by omega)), Real.norm_eq_abs]
  have h3 := nas_real_aux (α (j + 1)) ‖xagSeq g α β lam x0 j - xSeq g α β lam x0 j‖
    (|lam (j + 1) - β (j + 1)| * ‖g (xmdSeq g α β lam x0 (j + 1))‖) hpos hle
  have h4 : 0 ≤ (1 - α (j + 1)) * ‖xagSeq g α β lam x0 j - xSeq g α β lam x0 j‖
        + |lam (j + 1) - β (j + 1)| * ‖g (xmdSeq g α β lam x0 (j + 1))‖ := by positivity
  have h5 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  refine h5.trans (h3.trans (le_of_eq ?_))
  rw [mul_pow, sq_abs]; ring

lemma nas_17 {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (hs : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k →
      ‖xagSeq g α β lam x0 k - xSeq g α β lam x0 k‖ ^ 2 ≤
        Gamma α k * ∑ τ ∈ Finset.Icc 1 k,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by
  intro k hk
  have := nas_lemma1_le α hs.1 hs.2.1
    (fun k => ‖xagSeq g α β lam x0 k - xSeq g α β lam x0 k‖ ^ 2)
    (fun k => (lam k - β k) ^ 2 / α k * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) k
    (by
      intro m hm _
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      simpa using nas_D_sq g α β lam hs x0 j) k hk le_rfl
  refine this.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 := (Finset.mem_Icc.mp hi).1
  ring

theorem nas_13 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k →
      ‖g (xSeq g α β lam x0 (k - 1)) - g (xmdSeq g α β lam x0 k)‖ ≤
        LΨ * (1 - α k) * ‖xagSeq g α β lam x0 (k - 1) - xSeq g α β lam x0 (k - 1)‖ := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine (hΨ.2.2 _ _).trans ?_
  have h1 : xSeq g α β lam x0 j - xmdSeq g α β lam x0 (j + 1) =
      (1 - α (j + 1)) • (xSeq g α β lam x0 j - xagSeq g α β lam x0 j) := by
    rw [nas_md_succ, smul_sub]; module
  rw [h1, norm_smul, Real.norm_of_nonneg (nas_one_sub hstep _ (by omega)), norm_sub_rev]
  nlinarith [le_refl LΨ]

theorem nas_22 {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ x : E n,
      α k * inner ℝ (g (xmdSeq g α β lam x0 k)) (xSeq g α β lam x0 (k - 1) - x) =
        α k / (2 * lam k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2)
          + α k * lam k / 2 * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
  intro k hk x
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hl : lam (j + 1) ≠ 0 := (hstep.2.2.2 (j + 1) (by omega)).ne'
  have h1 : xSeq g α β lam x0 (j + 1) - x =
      (xSeq g α β lam x0 j - x) - lam (j + 1) • g (xmdSeq g α β lam x0 (j + 1)) := by
    rw [nas_x_succ]; abel
  have e := norm_sub_sq_real (xSeq g α β lam x0 j - x) (lam (j + 1) • g (xmdSeq g α β lam x0 (j + 1)))
  have hc := real_inner_comm (g (xmdSeq g α β lam x0 (j + 1))) (xSeq g α β lam x0 j - x)
  rw [h1, e, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hc]
  field_simp
  ring

theorem nas_20 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ)
    (α β lam : ℕ → ℝ) (x0 : E n) :
    ∀ k, 1 ≤ k →
      Ψ (xagSeq g α β lam x0 k) ≤ Ψ (xmdSeq g α β lam x0 k) - β k * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        + LΨ * β k ^ 2 / 2 * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := nas_descent Ψ g LΨ hΨ (xmdSeq g α β lam x0 (j + 1)) (xagSeq g α β lam x0 (j + 1))
  have hy : xagSeq g α β lam x0 (j + 1) - xmdSeq g α β lam x0 (j + 1)
      = -(β (j + 1) • g (xmdSeq g α β lam x0 (j + 1))) := by
    rw [nas_xag_succ]; abel
  rw [hy, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs] at h
  linarith

theorem nas_15 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k →
      Ψ (xSeq g α β lam x0 k) ≤ Ψ (xSeq g α β lam x0 (k - 1)) - lam k * (1 - LΨ * lam k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        + LΨ * (1 - α k) ^ 2 / 2 * ‖xagSeq g α β lam x0 (k - 1) - xSeq g α β lam x0 (k - 1)‖ ^ 2 := by
  intro k hk
  have h13 := nas_13 Ψ g LΨ hΨ hL α β lam hstep x0 k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h13 ⊢
  set G := g (xmdSeq g α β lam x0 (j + 1)) with hG
  set Δ := xagSeq g α β lam x0 j - xSeq g α β lam x0 j with hΔ
  have hd := nas_descent Ψ g LΨ hΨ (xSeq g α β lam x0 j) (xSeq g α β lam x0 (j + 1))
  have hy : xSeq g α β lam x0 (j + 1) - xSeq g α β lam x0 j = -(lam (j + 1) • G) := by
    rw [nas_x_succ]; abel
  rw [hy, inner_neg_right, inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at hd
  have hlam := hstep.2.2.2 (j + 1) (by omega)
  have hi : inner ℝ (g (xSeq g α β lam x0 j)) G =
      ‖G‖ ^ 2 + inner ℝ (g (xSeq g α β lam x0 j) - G) G := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
  have hb : |inner ℝ (g (xSeq g α β lam x0 j) - G) G| ≤
      LΨ * (1 - α (j + 1)) * ‖Δ‖ * ‖G‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right h13 (norm_nonneg _)
  have hb2 := (abs_le.mp hb).1
  have h1a := nas_one_sub hstep (j + 1) (by omega)
  have key : 0 ≤ LΨ * ((1 - α (j + 1)) * ‖Δ‖ - lam (j + 1) * ‖G‖) ^ 2 :=
    mul_nonneg hL.le (sq_nonneg _)
  rw [hi] at hd
  nlinarith [mul_le_mul_of_nonneg_left hb2 hlam.le]

theorem nas_18 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k →
      Ψ (xSeq g α β lam x0 k) ≤ Ψ (xSeq g α β lam x0 (k - 1)) - lam k * (1 - LΨ * lam k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        + LΨ * Gamma α k / 2 * ∑ τ ∈ Finset.Icc 1 k,
            (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by
  intro k hk
  have h15 := nas_15 Ψ g LΨ hΨ hL α β lam hstep x0 k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h15 ⊢
  have hG := nas_Gamma_pos α hstep.2.1 (j + 1)
  have hterm : ∀ τ ∈ Finset.Icc 1 (j + 1), 0 ≤
      (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by
    intro τ hτ
    have hτ1 := (Finset.mem_Icc.mp hτ).1
    have hgp := nas_Gamma_pos α hstep.2.1 τ
    have hap : 0 < α τ := by
      rcases Nat.eq_or_lt_of_le hτ1 with h | h
      · subst h; rw [hstep.1]; norm_num
      · exact (hstep.2.1 τ (by omega)).1
    positivity
  have hsum_le : ∑ τ ∈ Finset.Icc 1 j,
      (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 ≤
      ∑ τ ∈ Finset.Icc 1 (j + 1),
      (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := hterm (j + 1) (by simp)
    linarith
  have hS0 : 0 ≤ ∑ τ ∈ Finset.Icc 1 (j + 1),
      (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 :=
    Finset.sum_nonneg hterm
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · subst h0
    have : α 1 = 1 := hstep.1
    simp only [this] at h15
    norm_num at h15
    have : 0 ≤ LΨ * Gamma α 1 / 2 * ∑ τ ∈ Finset.Icc 1 (0 + 1),
      (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by
      have := nas_Gamma_pos α hstep.2.1 1
      positivity
    linarith
  · have h17 := nas_17 g α β lam hstep x0 j hj
    have h1a := nas_one_sub hstep (j + 1) (by omega)
    have hGs := nas_Gamma_succ α j hj
    have hΓj := nas_Gamma_pos α hstep.2.1 j
    have hα1 : 1 - α (j + 1) ≤ 1 := by
      have := (hstep.2.1 (j + 1) (by omega)).1; linarith
    -- (1-α)^2 ‖Δ‖^2 ≤ (1-α)^2 Γ_j S_j ≤ Γ_{j+1} S_{j+1}
    have e1 : (1 - α (j + 1)) ^ 2 * ‖xagSeq g α β lam x0 j - xSeq g α β lam x0 j‖ ^ 2 ≤
        (1 - α (j + 1)) ^ 2 * (Gamma α j * ∑ τ ∈ Finset.Icc 1 j,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h17 (sq_nonneg _)
    have e2 : (1 - α (j + 1)) ^ 2 * (Gamma α j * ∑ τ ∈ Finset.Icc 1 j,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2) ≤
        Gamma α (j + 1) * ∑ τ ∈ Finset.Icc 1 (j + 1),
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by
      rw [hGs]
      have hS1 : 0 ≤ ∑ τ ∈ Finset.Icc 1 j,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 :=
        Finset.sum_nonneg (fun τ hτ => hterm τ (by
          have := Finset.mem_Icc.mp hτ; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩))
      have : (1 - α (j + 1)) ^ 2 * (Gamma α j * ∑ τ ∈ Finset.Icc 1 j,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2) =
          (1 - α (j + 1)) * ((1 - α (j + 1)) * Gamma α j * ∑ τ ∈ Finset.Icc 1 j,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2) := by ring
      rw [this]
      have h5 : (1 - α (j + 1)) * Gamma α j * ∑ τ ∈ Finset.Icc 1 j,
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 ≤
          (1 - α (j + 1)) * Gamma α j * ∑ τ ∈ Finset.Icc 1 (j + 1),
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
      have h6 : 0 ≤ (1 - α (j + 1)) * Gamma α j * ∑ τ ∈ Finset.Icc 1 (j + 1),
          (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 := by positivity
      nlinarith
    have e3 := mul_le_mul_of_nonneg_left (e1.trans e2) hL.le
    nlinarith
theorem nas_21 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n)
    (hconv : ConvexOn ℝ Set.univ Ψ) :
    ∀ k, 1 ≤ k → ∀ x : E n,
      Ψ (xmdSeq g α β lam x0 k) - ((1 - α k) * Ψ (xagSeq g α β lam x0 (k - 1)) + α k * Ψ x) ≤
        α k * inner ℝ (g (xmdSeq g α β lam x0 k)) (xSeq g α β lam x0 (k - 1) - x) := by
  intro k hk x
  have ha := (nas_alpha_pos hstep k hk).le
  have hb := nas_one_sub hstep k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set md := xmdSeq g α β lam x0 (j + 1) with hmd
  have h1 := nas_grad_ineq Ψ g LΨ hΨ hconv md (xagSeq g α β lam x0 j)
  have h2 := nas_grad_ineq Ψ g LΨ hΨ hconv md x
  have hmd' : md = (1 - α (j + 1)) • xagSeq g α β lam x0 j + α (j + 1) • xSeq g α β lam x0 j :=
    nas_md_succ g α β lam x0 j
  have hv : (1 - α (j + 1)) • (xagSeq g α β lam x0 j - md) + α (j + 1) • (x - md)
      = α (j + 1) • (x - xSeq g α β lam x0 j) := by
    rw [hmd']; module
  have h3 := congrArg (fun v => inner ℝ (g md) v) hv
  simp only [inner_add_right, inner_smul_right, inner_sub_right] at h3
  simp only [inner_sub_right] at h1 h2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h2 ha]

theorem nas_23 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) (hconv : ConvexOn ℝ Set.univ Ψ) :
    ∀ k, 1 ≤ k → α k * lam k ≤ β k → β k < 1 / LΨ → ∀ x : E n,
      Ψ (xagSeq g α β lam x0 k) ≤ (1 - α k) * Ψ (xagSeq g α β lam x0 (k - 1)) + α k * Ψ x
        + α k / (2 * lam k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2)
        - β k / 2 * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
  intro k hk h9 h9' x
  have h20 := nas_20 Ψ g LΨ hΨ α β lam x0 k hk
  have h21 := nas_21 Ψ g LΨ hΨ α β lam hstep x0 hconv k hk x
  have h22 := nas_22 g α β lam hstep x0 k hk x
  have hLβ : LΨ * β k < 1 := by
    rw [lt_div_iff₀ hL] at h9'; linarith
  have hn := sq_nonneg ‖g (xmdSeq g α β lam x0 k)‖
  nlinarith [mul_le_mul_of_nonneg_right h9 hn]

theorem nas_25_abs (a u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ) (hN : 1 ≤ N)
    (ha : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ a k)
    (h : ∀ k, 2 ≤ k → k ≤ N → a k ≤ a (k - 1)) :
    ∑ k ∈ Finset.Icc 1 N, a k * (u (k - 1) - u k) ≤ a 1 * u 0 := by
  have : ∀ m, 1 ≤ m → m ≤ N →
      ∑ k ∈ Finset.Icc 1 m, a k * (u (k - 1) - u k) + a m * u m ≤ a 1 * u 0 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; simp; linarith
    | succ m hm ih =>
      intro hmN
      have ih := ih (by omega)
      have h1 := h (m + 1) (by omega) hmN
      simp only [Nat.add_sub_cancel] at h1
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.add_sub_cancel]
      nlinarith [mul_le_mul_of_nonneg_right h1 (hu m)]
  have h2 := this N hN le_rfl
  have h3 : 0 ≤ a N * u N := mul_nonneg (ha N hN le_rfl) (hu N)
  linarith

theorem nas_25 {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) (N : ℕ) (hN : 1 ≤ N)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * Gamma α k) ≤ α (k - 1) / (lam (k - 1) * Gamma α (k - 1))) :
    ∀ x : E n,
      ∑ k ∈ Finset.Icc 1 N,
          α k / (lam k * Gamma α k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2) ≤
        ‖x0 - x‖ ^ 2 / lam 1 := by
  intro x
  have h := nas_25_abs (fun k => α k / (lam k * Gamma α k))
    (fun k => ‖xSeq g α β lam x0 k - x‖ ^ 2) (fun k => sq_nonneg _) N hN
    (by
      intro k hk _
      have := nas_alpha_pos hstep k hk
      have := hstep.2.2.2 k hk
      have := nas_Gamma_pos α hstep.2.1 k
      positivity)
    (fun k hk hkN => h210 k (Finset.mem_Icc.mpr ⟨by omega, hkN⟩) hk)
  refine h.trans (le_of_eq ?_)
  have h0 : xSeq g α β lam x0 0 = x0 := rfl
  simp only [h0, hstep.1, nas_Gamma_one]
  ring

theorem nas_24 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) (hconv : ConvexOn ℝ Set.univ Ψ) (N : ℕ) (hN : 1 ≤ N)
    (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ β k < 1 / LΨ)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * Gamma α k) ≤ α (k - 1) / (lam (k - 1) * Gamma α (k - 1))) :
    ∀ x : E n,
      (Ψ (xagSeq g α β lam x0 N) - Ψ x) / Gamma α N ≤
        ‖x0 - x‖ ^ 2 / (2 * lam 1)
          - ∑ k ∈ Finset.Icc 1 N, β k / (2 * Gamma α k) * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
  intro x
  have hmain := nas_lemma1_le α hstep.1 hstep.2.1
    (fun k => Ψ (xagSeq g α β lam x0 k) - Ψ x)
    (fun k => α k / (2 * lam k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2)
        - β k / 2 * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) N
    (by
      intro k hk hkN
      have := nas_23 Ψ g LΨ hΨ hL α β lam hstep x0 hconv k hk
        (h29 k (Finset.mem_Icc.mpr ⟨hk, hkN⟩)).1 (h29 k (Finset.mem_Icc.mpr ⟨hk, hkN⟩)).2 x
      linarith) N hN le_rfl
  have hG := nas_Gamma_pos α hstep.2.1 N
  have h25 := nas_25 g α β lam hstep x0 N hN h210 x
  have hl1 := hstep.2.2.2 1 le_rfl
  have hsum : ∑ i ∈ Finset.Icc 1 N,
      (α i / (2 * lam i) * (‖xSeq g α β lam x0 (i - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 i - x‖ ^ 2)
        - β i / 2 * (1 - LΨ * β i) * ‖g (xmdSeq g α β lam x0 i)‖ ^ 2) / Gamma α i =
      (1 / 2) * ∑ k ∈ Finset.Icc 1 N,
          α k / (lam k * Gamma α k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2)
      - ∑ k ∈ Finset.Icc 1 N, β k / (2 * Gamma α k) * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 := (Finset.mem_Icc.mp hi).1
    have := nas_Gamma_pos α hstep.2.1 i
    have := hstep.2.2.2 i hi1
    field_simp
  rw [div_le_iff₀ hG]
  rw [hsum] at hmain
  have h5 : (1 / 2) * ∑ k ∈ Finset.Icc 1 N,
          α k / (lam k * Gamma α k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2) ≤
        ‖x0 - x‖ ^ 2 / (2 * lam 1) := by
    have : ‖x0 - x‖ ^ 2 / (2 * lam 1) = (1 / 2) * (‖x0 - x‖ ^ 2 / lam 1) := by
      field_simp
    rw [this]; linarith
  have h6 := mul_le_mul_of_nonneg_left (show
    (1 / 2) * ∑ k ∈ Finset.Icc 1 N,
          α k / (lam k * Gamma α k) * (‖xSeq g α β lam x0 (k - 1) - x‖ ^ 2 - ‖xSeq g α β lam x0 k - x‖ ^ 2)
      - ∑ k ∈ Finset.Icc 1 N, β k / (2 * Gamma α k) * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
    ≤ ‖x0 - x‖ ^ 2 / (2 * lam 1)
      - ∑ k ∈ Finset.Icc 1 N, β k / (2 * Gamma α k) * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
    by linarith) hG.le
  linarith

theorem nas_19 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) (N : ℕ) :
    Ψ (xSeq g α β lam x0 N) ≤
      Ψ x0 - ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
  set A : ℕ → ℝ := fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 with hA
  set f : ℕ → ℝ := fun τ => (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * A τ with hf
  have tele : ∀ m : ℕ, Ψ (xSeq g α β lam x0 m) ≤ Ψ x0 + ∑ k ∈ Finset.Icc 1 m,
      (-(lam k * (1 - LΨ * lam k) * A k) + LΨ * Gamma α k / 2 * ∑ τ ∈ Finset.Icc 1 k, f τ) := by
    intro m
    induction m with
    | zero => simp [xSeq, agRun]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h18 := nas_18 Ψ g LΨ hΨ hL α β lam hstep x0 (m + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h18
      simp only [hA, hf]
      linarith
  have swap : ∑ k ∈ Finset.Icc 1 N, Gamma α k * ∑ τ ∈ Finset.Icc 1 k, f τ =
      ∑ τ ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc τ N, Gamma α k) * f τ := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm' (by intro x y; simp only [Finset.mem_Icc]; omega)
  have e1 : ∑ k ∈ Finset.Icc 1 N, LΨ * Gamma α k / 2 * ∑ τ ∈ Finset.Icc 1 k, f τ =
      LΨ / 2 * ∑ τ ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc τ N, Gamma α k) * f τ := by
    rw [← swap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ∀ τ ∈ Finset.Icc 1 N, lam τ * C LΨ α β lam N τ * A τ =
      lam τ * (1 - LΨ * lam τ) * A τ - LΨ / 2 * ((∑ k ∈ Finset.Icc τ N, Gamma α k) * f τ) := by
    intro τ hτ
    have hτ1 := (Finset.mem_Icc.mp hτ).1
    have := nas_Gamma_pos α hstep.2.1 τ
    have := nas_alpha_pos hstep τ hτ1
    have := hstep.2.2.2 τ hτ1
    simp only [C, hf]
    field_simp
  have e3 : ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k * A k =
      ∑ k ∈ Finset.Icc 1 N, lam k * (1 - LΨ * lam k) * A k
        - LΨ / 2 * ∑ τ ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc τ N, Gamma α k) * f τ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl e2
  have h := tele N
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, e1] at h
  simp only [hA] at e3 ⊢
  linarith

theorem nas_thm1 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n)
    (hbdd : BddBelow (Set.range Ψ)) (N : ℕ) (hN : 1 ≤ N) :
    ((∀ k ∈ Finset.Icc 1 N, 0 < C LΨ α β lam N k) →
      (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN) (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) ≤
        (Ψ x0 - ⨅ x, Ψ x) / ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k) ∧
    (∀ xstar : E n, ConvexOn ℝ Set.univ Ψ → (∀ x, Ψ xstar ≤ Ψ x) →
      (∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ β k < 1 / LΨ) →
      (∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
        α k / (lam k * Gamma α k) ≤ α (k - 1) / (lam (k - 1) * Gamma α (k - 1))) →
      (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN) (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) ≤
          ‖x0 - xstar‖ ^ 2 /
            (lam 1 * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) ∧
        Ψ (xagSeq g α β lam x0 N) - Ψ xstar ≤ Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)) := by
  set m := (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
    (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) with hm
  have hmle : ∀ k ∈ Finset.Icc 1 N, m ≤ ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := fun k hk =>
    Finset.inf'_le (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) hk
  have hne : (Finset.Icc 1 N).Nonempty := Finset.nonempty_Icc.mpr hN
  refine ⟨?_, ?_⟩
  · intro hC
    have hpos : 0 < ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k := by
      apply Finset.sum_pos _ hne
      intro k hk
      exact mul_pos (hstep.2.2.2 k (Finset.mem_Icc.mp hk).1) (hC k hk)
    rw [le_div_iff₀ hpos]
    have h19 := nas_19 Ψ g LΨ hΨ hL α β lam hstep x0 N
    have hinf : ⨅ x, Ψ x ≤ Ψ (xSeq g α β lam x0 N) := ciInf_le hbdd _
    have h1 : m * ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k ≤
        ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have := mul_pos (hstep.2.2.2 k (Finset.mem_Icc.mp hk).1) (hC k hk)
      nlinarith [hmle k hk]
    linarith
  · intro xstar hconv hmin h29 h210
    have h24 := nas_24 Ψ g LΨ hΨ hL α β lam hstep x0 hconv N hN h29 h210 xstar
    have hG := nas_Gamma_pos α hstep.2.1 N
    have hl1 := hstep.2.2.2 1 le_rfl
    have hterm : ∀ k ∈ Finset.Icc 1 N, 0 < (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) := by
      intro k hk
      have hk1 := (Finset.mem_Icc.mp hk).1
      have := nas_Gamma_pos α hstep.2.1 k
      have := hstep.2.2.1 k hk1
      have h9 := (h29 k hk).2
      have : LΨ * β k < 1 := by rw [lt_div_iff₀ hL] at h9; linarith
      have : 0 < 1 - LΨ * β k := by linarith
      positivity
    have hS : ∑ k ∈ Finset.Icc 1 N, β k / (2 * Gamma α k) * (1 - LΨ * β k) *
          ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 =
        (1 / 2) * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) *
          ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have := nas_Gamma_pos α hstep.2.1 k
      field_simp
    have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 N, β k / (2 * Gamma α k) * (1 - LΨ * β k) *
          ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
      rw [hS]
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg fun k hk => mul_nonneg (hterm k hk).le (sq_nonneg _)
    have hd0 : 0 ≤ (Ψ (xagSeq g α β lam x0 N) - Ψ xstar) / Gamma α N :=
      div_nonneg (sub_nonneg.mpr (hmin _)) hG.le
    refine ⟨?_, ?_⟩
    · have hW : 0 < ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) :=
        Finset.sum_pos hterm hne
      rw [le_div_iff₀ (mul_pos hl1 hW)]
      have h1 : m * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) ≤
          ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) *
            ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have := (hterm k hk).le
        nlinarith [hmle k hk]
      have h2 : (1 / 2) * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) *
          ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 ≤ ‖x0 - xstar‖ ^ 2 / (2 * lam 1) := by
        rw [← hS]; linarith
      have h3 : ‖x0 - xstar‖ ^ 2 / (2 * lam 1) = (‖x0 - xstar‖ ^ 2 / lam 1) / 2 := by
        field_simp
      have h4 : (‖x0 - xstar‖ ^ 2 / lam 1) * lam 1 = ‖x0 - xstar‖ ^ 2 := by
        field_simp
      have h5 : ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) *
            ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 ≤ ‖x0 - xstar‖ ^ 2 / lam 1 := by linarith
      calc m * (lam 1 * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k))
          = lam 1 * (m * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) := by ring
        _ ≤ lam 1 * (‖x0 - xstar‖ ^ 2 / lam 1) :=
            mul_le_mul_of_nonneg_left (h1.trans h5) hl1.le
        _ = ‖x0 - xstar‖ ^ 2 := by field_simp
    · rw [div_le_iff₀ hG] at h24
      have : Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1) =
          (‖x0 - xstar‖ ^ 2 / (2 * lam 1)) * Gamma α N := by ring
      rw [this]
      nlinarith

theorem nas_before_216 {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k →
      xagSeq g α β lam x0 k - xSeq g α β lam x0 k =
        Gamma α k • ∑ τ ∈ Finset.Icc 1 k, ((lam τ - β τ) / Gamma α τ) • g (xmdSeq g α β lam x0 τ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h := nas_D_succ g α β lam x0 0
    have h0 : xagSeq g α β lam x0 0 - xSeq g α β lam x0 0 = 0 := by
      simp [xagSeq, xSeq, agRun]
    rw [h0, hstep.1] at h
    simp only [zero_add, sub_self, zero_smul] at h
    simp [h, nas_Gamma_one]
  | succ k hk ih =>
    rw [nas_D_succ, ih, Finset.sum_Icc_succ_top (by omega), nas_Gamma_succ α k hk]
    have hG := nas_Gamma_pos α hstep.2.1 (k + 1)
    rw [nas_Gamma_succ α k hk] at hG
    have hne : (1 - α (k + 1)) * Gamma α k ≠ 0 := hG.ne'
    have e : ((1 - α (k + 1)) * Gamma α k) *
        ((lam (k + 1) - β (k + 1)) / ((1 - α (k + 1)) * Gamma α k)) =
        lam (k + 1) - β (k + 1) := by
      rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hne
    rw [smul_add, smul_smul, smul_smul, e]
theorem solution (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1)
    (θ η : ℕ → ℝ) (h : ∀ k, 1 ≤ k → θ k ≤ (1 - α k) * θ (k - 1) + η k) :
    ∀ k, 1 ≤ k → θ k ≤ Gamma α k * ∑ i ∈ Finset.Icc 1 k, η i / Gamma α i := fun k hk => nas_lemma1_le α hα1 hα θ η k (fun m hm _ => h m hm) k hk le_rfl
