-- Prove2me | solution 1 for NonconvexAG.Stoch.eq_2_17_stoch
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:58:20.900502+00:00
-- url     : https://prove2.me/submissions/84054b8b-f501-4569-bfc0-7e75ed4d9bce

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

lemma nast_lemma1_le (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1)
    (θ η : ℕ → ℝ) (N : ℕ) (h : ∀ k, 1 ≤ k → k ≤ N → θ k ≤ (1 - α k) * θ (k - 1) + η k) :
    ∀ k, 1 ≤ k → k ≤ N → θ k ≤ NonconvexAG.Smooth.Gamma α k *
      ∑ i ∈ Finset.Icc 1 k, η i / NonconvexAG.Smooth.Gamma α i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hN
    have := h 1 le_rfl hN
    simp [hα1, nast_Gamma_one] at this ⊢
    exact this
  | succ k hk ih =>
    intro hN
    have ih := ih (by omega)
    have h1 := h (k + 1) (by omega) hN
    simp only [Nat.add_sub_cancel] at h1
    have h2 : 0 ≤ 1 - α (k + 1) := by linarith [(hα (k + 1) (by omega)).2]
    have hG := nast_Gamma_pos α hα (k + 1)
    rw [Finset.sum_Icc_succ_top (by omega), nast_Gamma_succ α k hk]
    have h3 := mul_le_mul_of_nonneg_left ih h2
    have h4 : (1 - α (k + 1)) * NonconvexAG.Smooth.Gamma α k *
        (η (k + 1) / ((1 - α (k + 1)) * NonconvexAG.Smooth.Gamma α k))
        = η (k + 1) := by
      rw [nast_Gamma_succ α k hk] at hG
      rw [mul_div_assoc']
      exact mul_div_cancel_left₀ _ hG.ne'
    nlinarith [h4]

lemma nast_D_succ {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (j : ℕ) (ω : Ω) :
    xagSeq G α β lam x0 ξ (j + 1) ω - xSeq G α β lam x0 ξ (j + 1) ω =
      (1 - α (j + 1)) • (xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω)
        + (lam (j + 1) - β (j + 1)) • G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) := by
  rw [nast_xag_succ, nast_x_succ, nast_md_succ]
  module

lemma nast_real_aux (α A B : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ((1 - α) * A + B) ^ 2 ≤ (1 - α) * A ^ 2 + B ^ 2 / α := by
  rw [show (1 - α) * A ^ 2 + B ^ 2 / α = (α * ((1 - α) * A ^ 2) + B ^ 2) / α by field_simp,
    le_div_iff₀ hα]
  nlinarith [mul_nonneg (sub_nonneg.mpr hα1) (sq_nonneg (α * A - B))]

lemma nast_D_sq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ)
    (hs : RSAGStepsizes α β lam) (x0 : E n) (ξ : ℕ → Ω → Ξ) (j : ℕ) (ω : Ω) :
    ‖xagSeq G α β lam x0 ξ (j + 1) ω - xSeq G α β lam x0 ξ (j + 1) ω‖ ^ 2 ≤
      (1 - α (j + 1)) * ‖xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω‖ ^ 2
        + (lam (j + 1) - β (j + 1)) ^ 2 / α (j + 1) *
          ‖G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω)‖ ^ 2 := by
  have hpos : 0 < α (j + 1) := nast_alpha_pos hs (j + 1) (by omega)
  have hle : α (j + 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rw [hs.1]
    · exact (hs.2.1 (j + 1) (by omega)).2.le
  have h1 := nast_D_succ G α β lam x0 ξ j ω
  have h2 : ‖xagSeq G α β lam x0 ξ (j + 1) ω - xSeq G α β lam x0 ξ (j + 1) ω‖ ≤
      (1 - α (j + 1)) * ‖xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω‖
        + |lam (j + 1) - β (j + 1)| * ‖G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω)‖ := by
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (nast_one_sub hs _ (by omega)),
      Real.norm_eq_abs]
  have h3 := nast_real_aux (α (j + 1)) ‖xagSeq G α β lam x0 ξ j ω - xSeq G α β lam x0 ξ j ω‖
    (|lam (j + 1) - β (j + 1)| * ‖G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω)‖) hpos hle
  have h5 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  refine h5.trans (h3.trans (le_of_eq ?_))
  rw [mul_pow, sq_abs]; ring

theorem solution {n : ℕ} (g : E n → E n) {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω,
      ‖xagSeq G α β lam x0 ξ (k - 1) ω - xSeq G α β lam x0 ξ (k - 1) ω‖ ^ 2 ≤
        NonconvexAG.Smooth.Gamma α (k - 1) * ∑ τ ∈ Finset.Icc 1 (k - 1),
          (lam τ - β τ) ^ 2 / (NonconvexAG.Smooth.Gamma α τ * α τ) *
            (‖g (xmdSeq G α β lam x0 ξ τ ω)‖ ^ 2 + ‖delta G g α β lam x0 ξ τ ω‖ ^ 2
              + 2 * ⟪g (xmdSeq G α β lam x0 ξ τ ω), delta G g α β lam x0 ξ τ ω⟫_ℝ) := by
  intro k hk ω
  have hnorm : ∀ τ, ‖g (xmdSeq G α β lam x0 ξ τ ω)‖ ^ 2 + ‖delta G g α β lam x0 ξ τ ω‖ ^ 2
      + 2 * ⟪g (xmdSeq G α β lam x0 ξ τ ω), delta G g α β lam x0 ξ τ ω⟫_ℝ
      = ‖G (xmdSeq G α β lam x0 ξ τ ω) (ξ τ ω)‖ ^ 2 := by
    intro τ
    have hG : G (xmdSeq G α β lam x0 ξ τ ω) (ξ τ ω)
        = g (xmdSeq G α β lam x0 ξ τ ω) + delta G g α β lam x0 ξ τ ω := by
      simp [delta]
    rw [hG, norm_add_sq_real]; ring
  simp only [hnorm]
  -- the claim for index k - 1 ≥ 0
  rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
  · rw [h0]
    simp [xagSeq, xSeq, rsagPath]
  · have := nast_lemma1_le α hstep.1 hstep.2.1
      (fun k => ‖xagSeq G α β lam x0 ξ k ω - xSeq G α β lam x0 ξ k ω‖ ^ 2)
      (fun k => (lam k - β k) ^ 2 / α k * ‖G (xmdSeq G α β lam x0 ξ k ω) (ξ k ω)‖ ^ 2) (k - 1)
      (by
        intro m hm _
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        simpa using nast_D_sq G α β lam hstep x0 ξ j ω) (k - 1) hpos le_rfl
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 := (Finset.mem_Icc.mp hi).1
    ring
