-- Prove2me | solution 1 for NonconvexAG.Stoch.eq_2_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:57:46.691104+00:00
-- url     : https://prove2.me/submissions/efb74481-ba4e-4c99-a34b-9eafa9fbb4ad

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

theorem solution {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
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
