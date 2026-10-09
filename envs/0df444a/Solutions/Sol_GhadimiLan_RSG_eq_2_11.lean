-- Prove2me | solution 1 for GhadimiLan.RSG.eq_2_11
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T23:08:31.034707+00:00
-- url     : https://prove2.me/submissions/c0c21412-df91-459e-8eee-fdb54d9b26ad

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Theorems.Thm_GhadimiLan_RSG_eq_2_9
import Theorems.Thm_GhadimiLan_RSG_eq_2_10
import Theorems.Thm_GhadimiLan_RSG_grad_sq_integrable
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Eq. (2.11): take expectations in the pathwise bound (2.9) (second conjunct, with `f*`),
kill the cross terms with (2.10) via the tower property `∫ μ[·|ℱ (k-1)] = ∫ ·`, and bound the
noise second moments by `σ²` using Assumption A1. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) :
    (∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ) ∧
    ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ ≤
      f x1 - fstar + L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 := by
  -- (a) integrability of ‖∇f(x_k)‖² for k = 1, …, N
  have hgi : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ :=
    fun k hk => grad_sq_integrable f g L hf G hG μ ℱ ξ σ γ x1 x hx hA1 k (Finset.mem_Icc.1 hk).1
  refine ⟨hgi, ?_⟩
  -- (e) cross terms: integrable and of zero mean, by (2.10) and the tower property
  have hcross : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) μ ∧
      ∫ ω, ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ ∂μ = 0 := by
    intro k hk
    obtain ⟨hint, hce⟩ :=
      eq_2_10 f g L hf G hG μ ℱ ξ σ γ x1 x hx hA1 k (Finset.mem_Icc.1 hk).1
    refine ⟨hint, ?_⟩
    have h1 := integral_condExp (μ := μ)
      (f := fun ω => ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) (ℱ.le (k - 1))
    have h2 := integral_congr_ae hce
    exact (h1.symm.trans h2).trans (by simp)
  -- noise second moments (Assumption A1, (1.3)); `rsgNoise` unfolds definitionally
  have hδi : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖rsgNoise G g ξ x k ω‖ ^ 2) μ :=
    fun k hk => hA1.integrable_sq_error k (Finset.mem_Icc.1 hk).1
  have hδv : ∀ k ∈ Finset.Icc 1 N, ∫ ω, ‖rsgNoise G g ξ x k ω‖ ^ 2 ∂μ ≤ σ ^ 2 :=
    fun k hk => hA1.variance_bound k (Finset.mem_Icc.1 hk).1
  -- (c) integrability of both sides of (2.9)
  have hA : Integrable
      (fun ω => ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2) μ :=
    integrable_finsetSum _ (fun k hk => (hgi k hk).const_mul _)
  have hS1 : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 N,
      (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) μ :=
    integrable_finsetSum _ (fun k hk => (hcross k hk).1.const_mul _)
  have hS2 : Integrable
      (fun ω => ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2) μ :=
    integrable_finsetSum _ (fun k hk => (hδi k hk).const_mul _)
  have hB1 : Integrable (fun ω => f x1 - fstar - ∑ k ∈ Finset.Icc 1 N,
      (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ) μ :=
    (integrable_const _).sub hS1
  have hB2 : Integrable
      (fun ω => L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2) μ :=
    hS2.const_mul _
  have hB : Integrable (fun ω => f x1 - fstar
      - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
      + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2) μ :=
    hB1.add hB2
  -- (b)+(c) integrate the pathwise inequality (2.9)
  have hmono := integral_mono hA hB
    (fun ω => (eq_2_9 f g L hf fstar hfstar G γ x1 ξ x hx N hN ω).2)
  -- (d) compute the left-hand integral
  have hAint : ∫ ω, ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ‖g (x k ω)‖ ^ 2 ∂μ
      = ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ := by
    rw [integral_finsetSum _ (fun k hk => (hgi k hk).const_mul _)]
    exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
  -- (e) the cross-term sum integrates to zero
  have hS1int : ∫ ω, ∑ k ∈ Finset.Icc 1 N,
      (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ ∂μ = 0 := by
    rw [integral_finsetSum _ (fun k hk => (hcross k hk).1.const_mul _)]
    exact Finset.sum_eq_zero
      (fun k hk => by rw [integral_const_mul, (hcross k hk).2, mul_zero])
  -- (f) the variance sum is at most σ² Σ γ_k²
  have hS2int : ∫ ω, ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 ∂μ
      ≤ σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 := by
    rw [integral_finsetSum _ (fun k hk => (hδi k hk).const_mul _), Finset.mul_sum]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [integral_const_mul, mul_comm (σ ^ 2)]
    exact mul_le_mul_of_nonneg_left (hδv k hk) (sq_nonneg _)
  -- (d) compute the right-hand integral
  have hBint : ∫ ω, (f x1 - fstar
      - ∑ k ∈ Finset.Icc 1 N, (γ k - L * γ k ^ 2) * ⟪g (x k ω), rsgNoise G g ξ x k ω⟫_ℝ
      + L / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2) ∂μ
      = f x1 - fstar
        + L / 2 * ∫ ω, ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 ∂μ := by
    rw [integral_add hB1 hB2, integral_sub (integrable_const _) hS1, integral_const_mul, hS1int,
      integral_const, probReal_univ, one_smul, sub_zero]
  rw [hAint, hBint] at hmono
  -- (g) conclude
  have hL2 : 0 ≤ L / 2 := by positivity
  calc ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ
      ≤ f x1 - fstar
        + L / 2 * ∫ ω, ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 * ‖rsgNoise G g ξ x k ω‖ ^ 2 ∂μ := hmono
    _ ≤ f x1 - fstar + L / 2 * (σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) :=
        by linarith [mul_le_mul_of_nonneg_left hS2int hL2]
    _ = f x1 - fstar + L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2 := by ring
