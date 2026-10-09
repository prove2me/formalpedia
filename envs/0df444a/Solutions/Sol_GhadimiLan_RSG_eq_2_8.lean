-- Prove2me | solution 1 for GhadimiLan.RSG.eq_2_8
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T22:48:36.520852+00:00
-- url     : https://prove2.me/submissions/a70d8499-c725-46e2-9789-b79b3eaac1c1

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Theorems.Thm_ConvexOptAlg_SmoothGD_lemma_3_4
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Eq. (2.8) (Ghadimi & Lan, proof of Theorem 2.1): the pathwise one-step descent inequality.
Proof: apply the quadratic upper bound (1.6) (Bubeck's Lemma 3.4, `lemma_3_4`) to the pair
`(x_{k+1}, x_k)`, substitute the recursion `x_{k+1} − x_k = −γ_k (∇f(x_k) + δ_k)` into the
inner product and the squared norm, expand, and collect terms. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ω Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x) (k : ℕ) (hk : 1 ≤ k) (ω : Ω) :
    f (x (k + 1) ω) ≤
      f (x k ω) - (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2
        - (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
        + L / 2 * γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 := by
  -- (1.6): quadratic upper bound from L-smoothness, applied to (x_{k+1}, x_k)
  have hub := ConvexOptAlg.SmoothGD.lemma_3_4 f g L hf (x (k + 1) ω) (x k ω)
  -- the recursion (2.2)
  have hstep : x (k + 1) ω = x k ω - γ k • G (x k ω) (ξ k ω) := hx.2 k hk ω
  -- G(x_k, ξ_k) = ∇f(x_k) + δ_k
  have hG : G (x k ω) (ξ k ω) = g (x k ω) + rsgNoise G g ξ x k ω := by
    unfold rsgNoise; abel
  set a := g (x k ω) with ha
  set d := rsgNoise G g ξ x k ω with hd
  set c := γ k with hc
  -- x_{k+1} − x_k = −γ_k (∇f(x_k) + δ_k)
  have hdiff : x (k + 1) ω - x k ω = -(c • (a + d)) := by
    rw [hstep, hG]; abel
  -- ⟨∇f(x_k), x_{k+1} − x_k⟩ = −γ_k (‖∇f(x_k)‖² + ⟨∇f(x_k), δ_k⟩)
  have h1 : ⟪a, x (k + 1) ω - x k ω⟫_ℝ = -(c * (‖a‖ ^ 2 + ⟪a, d⟫_ℝ)) := by
    rw [hdiff, inner_neg_right, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
  -- ‖x_{k+1} − x_k‖² = γ_k² (‖∇f(x_k)‖² + 2⟨∇f(x_k), δ_k⟩ + ‖δ_k‖²)
  have h2 : ‖x (k + 1) ω - x k ω‖ ^ 2 = c ^ 2 * (‖a‖ ^ 2 + 2 * ⟪a, d⟫_ℝ + ‖d‖ ^ 2) := by
    rw [hdiff, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real]
  rw [h1, h2] at hub
  -- keep the upper half of the absolute-value bound and collect terms
  have hub' := (abs_le.mp hub).2
  linarith [hub']
