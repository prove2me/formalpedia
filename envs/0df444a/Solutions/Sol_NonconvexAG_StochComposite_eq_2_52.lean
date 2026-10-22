-- Prove2me | solution 1 for NonconvexAG.StochComposite.eq_2_52
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T14:38:12.979561+00:00
-- url     : https://prove2.me/submissions/d6d49d5f-d3c4-41bc-b92b-7890a1f1ed65

/-
Actual stochastic-proximal iterate bound (2.52), Ghadimi-Lan arXiv1310.3787v1 p13.
Original mathematics: Saeed Ghadimi and Guanghui Lan.
Platform formulation and existing initial-norm correction: mikedeng1.
Prior statement confirmation: Shuze Chen; no independent proof review claimed.
Alexander Richard Towell (queelius): research direction and stewardship.
OpenAI Codex: substantial proof construction, formalization and verification.
Lean/Mathlib contributors: norms, convex combinations, order and proof infrastructure.
No accepted theorem body is copied, and no mathematical novelty is claimed.
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
open NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (2.52), p. 13 (outer ends of the chain), along Algorithm 4: under Assumption 2 and
`‖x₀‖ ≤ M`, for every realization `ω`, every `k ≥ 1` and every point `x*` (the paper applies
it at an optimal solution). -/
theorem solution {n : ℕ} (P : E n → E n → ℝ → E n) (M : ℝ) (hA2 : Assumption2 P M)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    (hx0 : ‖x0‖ ≤ M) {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ xstar : E n,
      ‖xmd k ω - xstar‖ ^ 2 + α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤
        2 * (‖xstar‖ ^ 2 + 2 * M ^ 2) := by
  intro xk xag xmd ω k hk xstar
  have hM : 0 ≤ M := (norm_nonneg x0).trans hx0
  have hb (j : ℕ) : ‖xk j ω‖ ≤ M ∧ ‖xag j ω‖ ≤ M := by
    cases j with
    | zero => simpa [xk, xag, xSeq, xagSeq, rsagPath] using And.intro hx0 hx0
    | succ j =>
      change ‖P _ _ (lam (j + 1))‖ ≤ M ∧ ‖P _ _ (β (j + 1))‖ ≤ M
      exact ⟨hA2 _ _ _ (hstep.2.2.2.1 (j + 1) (by omega)),
        hA2 _ _ _ (hstep.2.2.1 (j + 1) (by omega))⟩
  have ha0 : 0 ≤ α k := by
    rcases Nat.eq_or_lt_of_le hk with he | he
    · subst k; rw [hstep.1]; norm_num
    · exact (hstep.2.1 k (by omega)).1.le
  have ha1 : α k ≤ 1 := by
    rcases Nat.eq_or_lt_of_le hk with he | he
    · subst k; rw [hstep.1]
    · exact (hstep.2.1 k (by omega)).2.le
  have hc0 : 0 ≤ 1 - α k := by linarith
  have hmd : ‖xmd k ω‖ ≤ M := by
    change ‖(1 - α k) • xag (k - 1) ω + α k • xk (k - 1) ω‖ ≤ M
    calc
      _ ≤ ‖(1 - α k) • xag (k - 1) ω‖ + ‖α k • xk (k - 1) ω‖ := norm_add_le _ _
      _ = (1 - α k) * ‖xag (k - 1) ω‖ + α k * ‖xk (k - 1) ω‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg ha0]
      _ ≤ (1 - α k) * M + α k * M := add_le_add
        (mul_le_mul_of_nonneg_left (hb (k - 1)).2 hc0)
        (mul_le_mul_of_nonneg_left (hb (k - 1)).1 ha0)
      _ = M := by ring
  have hmdsq : ‖xmd k ω‖ ^ 2 ≤ M ^ 2 := by
    nlinarith only [mul_self_le_mul_self (norm_nonneg (xmd k ω)) hmd]
  have hdist : ‖xmd k ω - xstar‖ ^ 2 ≤ 2 * M ^ 2 + 2 * ‖xstar‖ ^ 2 := by
    have hs := mul_self_le_mul_self (norm_nonneg (xmd k ω - xstar)) (norm_sub_le (xmd k ω) xstar)
    nlinarith only [hs, hmdsq, sq_nonneg (‖xmd k ω‖ - ‖xstar‖)]
  have hdiff : ‖xag (k - 1) ω - xk (k - 1) ω‖ ≤ 2 * M := by
    have hh := norm_sub_le (xag (k - 1) ω) (xk (k - 1) ω)
    linarith only [hh, (hb (k - 1)).1, (hb (k - 1)).2]
  have hdiffsq : ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith only [mul_self_le_mul_self (norm_nonneg (xag (k - 1) ω - xk (k - 1) ω)) hdiff]
  have hc : α k * (1 - α k) ≤ (1:ℝ) / 4 := by nlinarith only [sq_nonneg (α k - 1/2)]
  have hcross : α k * (1 - α k) * ‖xag (k - 1) ω - xk (k - 1) ω‖ ^ 2 ≤ M ^ 2 := by
    calc
      _ ≤ α k * (1 - α k) * (4 * M ^ 2) :=
        mul_le_mul_of_nonneg_left hdiffsq (mul_nonneg ha0 hc0)
      _ ≤ (1/4:ℝ) * (4 * M ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = M ^ 2 := by ring
  nlinarith only [hdist, hcross, sq_nonneg M]



#print axioms solution
