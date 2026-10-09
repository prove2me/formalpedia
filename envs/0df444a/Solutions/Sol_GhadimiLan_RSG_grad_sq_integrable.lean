-- Prove2me | solution 1 for GhadimiLan.RSG.grad_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T23:02:01.991194+00:00
-- url     : https://prove2.me/submissions/57d34fe1-1422-4ab2-a529-d7bb2036522b

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

namespace GhadimiLan.RSG.Sol_grad_sq_integrable

/-- Along an RSG run with a Borel oracle and adapted noise, every iterate `x k` (`k ≥ 1`) is
measurable for the ambient σ-algebra on `Ω` (induction along the recursion (2.2)). -/
private lemma iterate_measurable_ambient {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ)
    (hξ : ∀ k : ℕ, 1 ≤ k → Measurable[ℱ k] (ξ k))
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (k : ℕ) (hk : 1 ≤ k) : Measurable (x k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- `x 1` is the constant `x1`.
    have h1 : x 1 = fun _ => x1 := funext hx.1
    rw [h1]
    exact measurable_const
  | succ k hk ih =>
    -- `ξ k` is `ℱ k`-measurable, hence measurable for the ambient σ-algebra `ℱ k ≤ m`.
    have hξk : Measurable (ξ k) := (hξ k hk).mono (ℱ.le k) le_rfl
    have hGk : Measurable (fun ω => G (x k ω) (ξ k ω)) := hG.comp (ih.prodMk hξk)
    have hstep : x (k + 1) = fun ω => x k ω - γ k • G (x k ω) (ξ k ω) := funext (hx.2 k hk)
    rw [hstep]
    exact ih.sub (hGk.const_smul (γ k))

/-- The gradient map of an `L`-smooth function is `L`-Lipschitz (this is the third clause of
`IsBetaSmooth`, repackaged as `LipschitzWith`). -/
private lemma lipschitz_grad {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) : LipschitzWith ⟨L, hf.1⟩ g :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hf.2.2 x y

end GhadimiLan.RSG.Sol_grad_sq_integrable

open GhadimiLan.RSG.Sol_grad_sq_integrable

/-- Second-moment bound along an RSG run (Ghadimi & Lan, arXiv:1309.5549v1, proof of
Theorem 2.1, p. 7, where `E‖∇f(x_k)‖²` is used; the paper does not state integrability):
for `f ∈ C^{1,1}_L(ℝⁿ)`, a Borel oracle `G` and an RSG run under Assumption A1, `‖∇f(x_k)‖²`
is integrable for every `k ≥ 1`. The proof is an induction along the recursion:
`‖∇f(x_{k+1})‖ ≤ (1 + L|γ_k|)‖∇f(x_k)‖ + L|γ_k|‖δ_k‖` with `‖δ_k‖ ∈ L²` by (1.3), and
`∇f(x_1)` is constant. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ := by
  -- `g = ∇f` is Lipschitz, hence continuous, hence Borel.
  have hgc : Continuous g := (lipschitz_grad f g L hf).continuous
  have hmeas : ∀ j : ℕ, 1 ≤ j → Measurable (x j) :=
    iterate_measurable_ambient G hG ℱ ξ hA1.adapted γ x1 x hx
  have hgm : ∀ j : ℕ, 1 ≤ j → AEStronglyMeasurable (fun ω => g (x j ω)) μ :=
    fun j hj => (hgc.measurable.comp (hmeas j hj)).aestronglyMeasurable
  -- Main claim: `ω ↦ ∇f(x_j(ω))` is in `L²(μ)` for every `j ≥ 1`, by induction on `j`.
  have key : ∀ j : ℕ, 1 ≤ j → MemLp (fun ω => g (x j ω)) 2 μ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      -- `∇f(x_1) = ∇f(x1)` is constant and `μ` is finite.
      have h1 : (fun ω => g (x 1 ω)) = fun _ => g x1 := funext fun ω => by rw [hx.1 ω]
      rw [h1]
      exact memLp_const _
    | succ j hj ih =>
      have hL : 0 ≤ L := hf.1
      have hγ : 0 ≤ |γ j| := abs_nonneg _
      -- The oracle error `δ_j = G(x_j, ξ_j) − ∇f(x_j)` is in `L²` by (1.3).
      have hnoise : MemLp (fun ω => rsgNoise G g ξ x j ω) 2 μ := by
        have hm : AEStronglyMeasurable (fun ω => rsgNoise G g ξ x j ω) μ := by
          have hξj : Measurable (ξ j) := (hA1.adapted j hj).mono (ℱ.le j) le_rfl
          have hGj : Measurable (fun ω => G (x j ω) (ξ j ω)) :=
            hG.comp ((hmeas j hj).prodMk hξj)
          exact (hGj.sub (hgc.measurable.comp (hmeas j hj))).aestronglyMeasurable
        exact (memLp_two_iff_integrable_sq_norm hm).2 (hA1.integrable_sq_error j hj)
      -- The dominating function `(1 + L|γ_j|)‖∇f(x_j)‖ + L|γ_j|‖δ_j‖` is in `L²`.
      have hdom : MemLp (fun ω => (1 + L * |γ j|) * ‖g (x j ω)‖
          + L * |γ j| * ‖rsgNoise G g ξ x j ω‖) 2 μ :=
        (ih.norm.const_mul _).add (hnoise.norm.const_mul _)
      -- Pointwise bound from the Lipschitz gradient and the recursion (2.2):
      -- `‖∇f(x_{j+1})‖ ≤ ‖∇f(x_j)‖ + L‖x_{j+1} − x_j‖ = ‖∇f(x_j)‖ + L|γ_j|‖∇f(x_j) + δ_j‖`.
      have hbound : ∀ ω, ‖g (x (j + 1) ω)‖ ≤ (1 + L * |γ j|) * ‖g (x j ω)‖
          + L * |γ j| * ‖rsgNoise G g ξ x j ω‖ := by
        intro ω
        have h1 : ‖g (x (j + 1) ω)‖ ≤ ‖g (x j ω)‖ + ‖g (x (j + 1) ω) - g (x j ω)‖ :=
          norm_le_norm_add_norm_sub' _ _
        have h2 : ‖g (x (j + 1) ω) - g (x j ω)‖ ≤ L * ‖x (j + 1) ω - x j ω‖ := hf.2.2 _ _
        have h3 : ‖x (j + 1) ω - x j ω‖ = |γ j| * ‖G (x j ω) (ξ j ω)‖ := by
          rw [hx.2 j hj ω, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
        have h4 : ‖G (x j ω) (ξ j ω)‖ ≤ ‖g (x j ω)‖ + ‖rsgNoise G g ξ x j ω‖ := by
          have hG' : G (x j ω) (ξ j ω) = g (x j ω) + rsgNoise G g ξ x j ω := by
            unfold rsgNoise
            abel
          rw [hG']
          exact norm_add_le _ _
        calc ‖g (x (j + 1) ω)‖
            ≤ ‖g (x j ω)‖ + ‖g (x (j + 1) ω) - g (x j ω)‖ := h1
          _ ≤ ‖g (x j ω)‖ + L * ‖x (j + 1) ω - x j ω‖ := by linarith
          _ = ‖g (x j ω)‖ + L * (|γ j| * ‖G (x j ω) (ξ j ω)‖) := by rw [h3]
          _ ≤ ‖g (x j ω)‖ + L * (|γ j| * (‖g (x j ω)‖ + ‖rsgNoise G g ξ x j ω‖)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hγ) hL)
          _ = (1 + L * |γ j|) * ‖g (x j ω)‖ + L * |γ j| * ‖rsgNoise G g ξ x j ω‖ := by ring
      exact hdom.mono' (hgm (j + 1) (by omega)) (Filter.Eventually.of_forall hbound)
  exact (memLp_two_iff_integrable_sq_norm (hgm k hk)).1 (key k hk)
