-- Prove2me | solution 1 for NonconvexAG.Stoch.eq_2_22_stoch
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:58:48.484048+00:00
-- url     : https://prove2.me/submissions/e92969e4-3894-470f-bb43-8ab6df5649e0

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

theorem solution {n : ℕ} (g : E n → E n) {Ω Ξ : Type*} (G : E n → Ξ → E n) (ξ : ℕ → Ω → Ξ)
    (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n) :
    ∀ k, 1 ≤ k → ∀ ω : Ω, ∀ x : E n,
      α k * ⟪g (xmdSeq G α β lam x0 ξ k ω) + delta G g α β lam x0 ξ k ω,
          xSeq G α β lam x0 ξ (k - 1) ω - x⟫_ℝ =
        α k / (2 * lam k) * (‖xSeq G α β lam x0 ξ (k - 1) ω - x‖ ^ 2
            - ‖xSeq G α β lam x0 ξ k ω - x‖ ^ 2)
          + α k * lam k / 2 * ‖g (xmdSeq G α β lam x0 ξ k ω) + delta G g α β lam x0 ξ k ω‖ ^ 2 := by
  intro k hk ω x
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hl : lam (j + 1) ≠ 0 := (hstep.2.2.2 (j + 1) (by omega)).ne'
  have hG : g (xmdSeq G α β lam x0 ξ (j + 1) ω) + delta G g α β lam x0 ξ (j + 1) ω
      = G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) := by
    simp [delta]
  rw [hG]
  have h1 : xSeq G α β lam x0 ξ (j + 1) ω - x =
      (xSeq G α β lam x0 ξ j ω - x)
        - lam (j + 1) • G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω) := by
    rw [nast_x_succ]; abel
  have e := norm_sub_sq_real (xSeq G α β lam x0 ξ j ω - x)
    (lam (j + 1) • G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω))
  have hc := real_inner_comm (G (xmdSeq G α β lam x0 ξ (j + 1) ω) (ξ (j + 1) ω))
    (xSeq G α β lam x0 ξ j ω - x)
  rw [h1, e, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hc]
  field_simp
  ring
