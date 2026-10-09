-- Prove2me | solution 1 for GhadimiLan.RSG.eq_2_9
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T22:50:06.127895+00:00
-- url     : https://prove2.me/submissions/a3623603-a82b-4eb9-a362-003dc0538317

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Theorems.Thm_GhadimiLan_RSG_eq_2_8
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Eq. (2.9): sum the one-step inequalities (2.8) for `k = 1, …, N`; the telescoping
`f(x_1) − f(x_{N+1})` appears, and `f(x_{N+1}) ≥ f*` gives the second form. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x) (N : ℕ) (hN : 1 ≤ N) (ω : Ω) :
    (∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2 ≤
      f x1 - f (x (N + 1) ω)
        - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2) ∧
    ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2 ≤
      f x1 - fstar
        - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 := by
  -- First conjunct: induction on `N ≥ 1`, peeling the top term of each sum and using (2.8).
  have h1 : ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2 ≤
      f x1 - f (x (N + 1) ω)
        - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 := by
    induction N, hN using Nat.le_induction with
    | base =>
      have h := GhadimiLan.RSG.eq_2_8 f g L hf G γ x1 ξ x hx 1 le_rfl ω
      have hfx1 : f x1 = f (x 1 ω) := by rw [hx.1 ω]
      simp only [Finset.Icc_self, Finset.sum_singleton]
      linarith
    | succ m hm ih =>
      have h := GhadimiLan.RSG.eq_2_8 f g L hf G γ x1 ξ x hx (m + 1) (Nat.le_add_left 1 m) ω
      simp only [Finset.sum_Icc_succ_top (Nat.le_add_left 1 m)]
      linarith
  refine ⟨h1, ?_⟩
  -- Second conjunct: `f* ≤ f(x_{N+1})` since `f*` is a lower bound of the range of `f`.
  have h2 : fstar ≤ f (x (N + 1) ω) := hfstar.1 ⟨_, rfl⟩
  linarith
