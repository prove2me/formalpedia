-- Prove2me | solution 1 for NonconvexAG.Stoch.one_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:00:49.031986+00:00
-- url     : https://prove2.me/submissions/42fbcec8-235d-4fb7-ba53-106a41121d71

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Stoch_RSAG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open NonconvexAG.Stoch
open GhadimiLan.RSG (E)

lemma nast_Gamma_one (α : ℕ → ℝ) : NonconvexAG.Smooth.Gamma α 1 = 1 := by
  simp [NonconvexAG.Smooth.Gamma]

lemma nast_Gamma_succ (α : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    NonconvexAG.Smooth.Gamma α (k + 1) = (1 - α (k + 1)) * NonconvexAG.Smooth.Gamma α k := by
  unfold NonconvexAG.Smooth.Gamma
  rw [Finset.prod_Icc_succ_top (by omega), mul_comm]

lemma nast_Gamma_pos (α : ℕ → ℝ) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) (k : ℕ) :
    0 < NonconvexAG.Smooth.Gamma α k := by
  unfold NonconvexAG.Smooth.Gamma
  apply Finset.prod_pos
  intro i hi
  have := hα i (Finset.mem_Icc.mp hi).1
  linarith [this.2]

lemma nast_one_sub {α β lam : ℕ → ℝ} (hs : RSAGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ 1 - α k := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; rw [hs.1]; simp
  · have := hs.2.1 k (by omega); linarith [this.2]

lemma nast_alpha_pos {α β lam : ℕ → ℝ} (hs : RSAGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) :
    0 < α k := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; rw [hs.1]; norm_num
  · exact (hs.2.1 k (by omega)).1

lemma nast_md_succ {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) :
    xmdSeq G α β lam x0 ξ (k + 1) ω =
      (1 - α (k + 1)) • xagSeq G α β lam x0 ξ k ω + α (k + 1) • xSeq G α β lam x0 ξ k ω := by
  simp [xmdSeq]

lemma nast_x_succ {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) :
    xSeq G α β lam x0 ξ (k + 1) ω =
      xSeq G α β lam x0 ξ k ω
        - lam (k + 1) • G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω) := by
  rw [nast_md_succ]; rfl

lemma nast_xag_succ {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) :
    xagSeq G α β lam x0 ξ (k + 1) ω =
      xmdSeq G α β lam x0 ξ (k + 1) ω
        - β (k + 1) • G (xmdSeq G α β lam x0 ξ (k + 1) ω) (ξ (k + 1) ω) := by
  rw [nast_md_succ]; rfl

lemma nast_hasDerivAt_line {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x d : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Ψ (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hΨ.2.1 (x + t • d)).hasFDerivAt
  have := h2.comp_hasDerivAt t h1
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this

lemma nast_grad_ineq {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (L : ℝ)
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
  have h0 := nast_hasDerivAt_line Ψ g L hΨ w d 0
  simp only [zero_smul, add_zero] at h0
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one h0
  rw [slope_def_field] at this
  simp at this
  have hy : w + d = z := by simp [hd]
  rw [hy] at this
  linarith


lemma nast_descent {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L) (x y : E n) :
    Ψ y ≤ Ψ x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  set ψ : ℝ → ℝ := fun t => Ψ (x + t • d) - t * inner ℝ (g x) d - L / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  have hder : ∀ t, HasDerivAt ψ
      (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d - L * t * ‖d‖ ^ 2) t := by
    intro t
    have h1 := nast_hasDerivAt_line Ψ g L hΨ x d t
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

theorem nast_21 {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hconv : ConvexOn ℝ Set.univ Ψ)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω, ∀ x : E n,
      Ψ (xmdSeq G α β lam x0 ξ k ω)
          - ((1 - α k) * Ψ (xagSeq G α β lam x0 ξ (k - 1) ω) + α k * Ψ x) ≤
        α k * ⟪g (xmdSeq G α β lam x0 ξ k ω), xSeq G α β lam x0 ξ (k - 1) ω - x⟫_ℝ := by
  intro k hk ω x
  have ha := (nast_alpha_pos hstep k hk).le
  have hb := nast_one_sub hstep k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set md := xmdSeq G α β lam x0 ξ (j + 1) ω with hmd
  have h1 := nast_grad_ineq Ψ g LΨ hΨ hconv md (xagSeq G α β lam x0 ξ j ω)
  have h2 := nast_grad_ineq Ψ g LΨ hΨ hconv md x
  have hmd' : md = (1 - α (j + 1)) • xagSeq G α β lam x0 ξ j ω
      + α (j + 1) • xSeq G α β lam x0 ξ j ω :=
    nast_md_succ G α β lam x0 ξ j ω
  have hv : (1 - α (j + 1)) • (xagSeq G α β lam x0 ξ j ω - md) + α (j + 1) • (x - md)
      = α (j + 1) • (x - xSeq G α β lam x0 ξ j ω) := by
    rw [hmd']; module
  have h3 := congrArg (fun v => inner ℝ (g md) v) hv
  simp only [inner_add_right, inner_smul_right, inner_sub_right] at h3
  simp only [inner_sub_right] at h1 h2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h2 ha]

lemma nast_13 {n : ℕ} {Ω Ξ : Type*} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ)
    (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) (j : ℕ) (ω : Ω) :
    ‖g (xSeq G α β lam x0 ξ j ω) - g (xmdSeq G α β lam x0 ξ (j + 1) ω)‖ ≤
      LΨ * (1 - α (j + 1)) * ‖xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω‖ := by
  refine (hΨ.2.2 _ _).trans ?_
  have h1 : xSeq G α β lam x0 ξ j ω - xmdSeq G α β lam x0 ξ (j + 1) ω =
      (1 - α (j + 1)) • (xSeq G α β lam x0 ξ j ω - xagSeq G α β lam x0 ξ j ω) := by
    rw [nast_md_succ, smul_sub]; module
  rw [h1, norm_smul, Real.norm_of_nonneg (nast_one_sub hstep _ (by omega)), norm_sub_rev]
  nlinarith [le_refl LΨ]

theorem solution {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) {Ω Ξ : Type*} (G : E n → Ξ → E n)
    (ξ : ℕ → Ω → Ξ) (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω,
      Ψ (xSeq G α β lam x0 ξ k ω) ≤
        Ψ (xSeq G α β lam x0 ξ (k - 1) ω)
          - lam k * (1 - LΨ * lam k) * ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2
          + LΨ * (1 - α k) ^ 2 / 2 *
              ‖xagSeq G α β lam x0 ξ (k - 1) ω - xSeq G α β lam x0 ξ (k - 1) ω‖ ^ 2
          + LΨ * lam k ^ 2 / 2 * ‖delta G g α β lam x0 ξ k ω‖ ^ 2
          - lam k * ⟪g (xSeq G α β lam x0 ξ (k - 1) ω)
              - (LΨ * lam k) • g (xmdSeq G α β lam x0 ξ k ω),
              delta G g α β lam x0 ξ k ω⟫_ℝ := by
  intro k hk ω
  have hL : 0 ≤ LΨ := hΨ.1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h13 := nast_13 Ψ g LΨ hΨ G ξ α β lam hstep x0 j ω
  simp only [Nat.add_sub_cancel] at ⊢
  set gm := g (xmdSeq G α β lam x0 ξ (j + 1) ω) with hgm
  set d := delta G g α β lam x0 ξ (j + 1) ω with hd
  set Δ := xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω with hΔ
  set gx := g (xSeq G α β lam x0 ξ j ω) with hgx
  have hGd : G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) = gm + d := by
    simp [hd, delta, hgm]
  have hdesc := nast_descent Ψ g LΨ hΨ (xSeq G α β lam x0 ξ j ω)
    (xSeq G α β lam x0 ξ (j + 1) ω)
  have hy : xSeq G α β lam x0 ξ (j + 1) ω - xSeq G α β lam x0 ξ j ω
      = -(lam (j + 1) • (gm + d)) := by
    rw [nast_x_succ, hGd]; abel
  rw [hy, inner_neg_right, inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, inner_add_right, norm_add_sq_real] at hdesc
  have hlam := hstep.2.2.2 (j + 1) (by omega)
  have hi : inner ℝ gx gm = ‖gm‖ ^ 2 + inner ℝ (gx - gm) gm := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
  have hb : |inner ℝ (gx - gm) gm| ≤ LΨ * (1 - α (j + 1)) * ‖Δ‖ * ‖gm‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right h13 (norm_nonneg _)
  have hb2 := (abs_le.mp hb).1
  have key : 0 ≤ LΨ * ((1 - α (j + 1)) * ‖Δ‖ - lam (j + 1) * ‖gm‖) ^ 2 :=
    mul_nonneg hL (sq_nonneg _)
  rw [inner_sub_left, real_inner_smul_left]
  rw [hi] at hdesc
  have hc : inner ℝ gm d = inner ℝ d gm := real_inner_comm _ _
  nlinarith [mul_le_mul_of_nonneg_left hb2 hlam.le]
