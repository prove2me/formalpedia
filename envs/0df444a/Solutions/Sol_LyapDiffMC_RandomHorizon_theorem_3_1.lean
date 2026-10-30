-- Prove2me | solution 1 for LyapDiffMC.RandomHorizon.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:23:24.664015+00:00
-- url     : https://prove2.me/submissions/6dbb29f0-7134-42e6-8383-bd05a37fa229
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model
import Theorems.Thm_LyapDiffMC_RandomHorizon_theorem_3_1_I
import Theorems.Thm_LyapDiffMC_RandomHorizon_proof_3_1_derivative_equation
import Theorems.Thm_LyapDiffMC_RandomHorizon_proof_3_1_derivative_continuity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open LyapDiffMC.RandomHorizon in
theorem solution {S : Type*} [MeasurableSpace S] (M : Setting S)
    (a b θ₀ ε : ℝ) (hθ₀ : θ₀ ∈ Set.Ioo a b) (hε : 0 < ε)
    (hεΛ : Set.Icc (θ₀ - ε) (θ₀ + ε) ⊆ Set.Ioo a b)
    (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Ioo a b, Measurable (Function.uncurry (k θ)))
    -- A1 and A3: K(θ, x, dy) = k(θ, x, y) K(θ₀, x, dy) for x ∈ C, y ∈ C and y ∈ Cᶜ
    (hA13 : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C,
      discKernel M θ x = (discKernel M θ₀ x).withDensity (fun y => ENNReal.ofReal (k θ x y)))
    (hk_nonneg : ∀ θ ∈ Set.Ioo a b, ∀ x ∈ M.C, ∀ᵐ y ∂(discKernel M θ₀ x), 0 ≤ k θ x y)
    -- A2 and A3: k(·, x, y) is continuously differentiable on [θ₀ - ε, θ₀ + ε]
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    -- A3: r̃_ε(x) < ∞
    (hA3 : ∀ x ∈ M.C, rtilde M k θ₀ ε x < ⊤)
    -- f̃(θ, x) in (3.11) is a real number
    (hf_int : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      IntegrableOn M.f M.Cᶜ (discKernel M θ x))
    (v₀ v₁ : S → ℝ) (hv₀ : Measurable v₀) (hv₁ : Measurable v₁)
    (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x) (hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x)
    -- (3.11)
    (h311 : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₀ y) ∂(discKernel M θ x) + ‖ftilde M θ x‖ₑ
        ≤ ENNReal.ofReal (v₀ x))
    -- (3.12)
    (h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)) :
    -- (I): u*(·, x) is differentiable at θ₀, with derivative (3.25)
    (∀ x ∈ M.C,
      Integrable (fun y => (∫ z in M.C, kder k θ₀ ε θ₀ y z * uStar M θ₀ z ∂(discKernel M θ₀ y))
          + ∫ z in M.Cᶜ, kder k θ₀ ε θ₀ y z * M.f z ∂(discKernel M θ₀ y))
        (greenMeasure M θ₀ x) ∧
      HasDerivAt (fun θ => uStar M θ x)
        (∫ y, ((∫ z in M.C, kder k θ₀ ε θ₀ y z * uStar M θ₀ z ∂(discKernel M θ₀ y))
            + ∫ z in M.Cᶜ, kder k θ₀ ε θ₀ y z * M.f z ∂(discKernel M θ₀ y))
          ∂(greenMeasure M θ₀ x)) θ₀) ∧
    -- (II): under (3.14) and (3.12′), u*(·, x) is C¹ on [θ₀ - ε, θ₀ + ε]
    ((∀ x ∈ M.C,
        ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x) < ⊤) →
     (∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), ∀ x ∈ M.C,
        ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ x)
          + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ x)
          + ∫⁻ y in M.Cᶜ, omega k θ₀ ε x y * ‖M.f y‖ₑ ∂(discKernel M θ x)
          ≤ ENNReal.ofReal (v₁ x)) →
     ∀ x ∈ M.C, ContDiffOn ℝ 1 (fun θ => uStar M θ x) (Set.Icc (θ₀ - ε) (θ₀ + ε))) := by
  refine ⟨theorem_3_1_I M a b θ₀ ε hθ₀ hε hεΛ k hk_meas hA13 hk_nonneg hA2 hA3 hf_int v₀ v₁ hv₀ hv₁
    hv₀_nn hv₁_nn h311 h312, fun h314 h312' x hx => ?_⟩
  have hde := proof_3_1_derivative_equation M a b θ₀ ε hθ₀ hε hεΛ k hk_meas hA13 hk_nonneg hA2 hA3
    hf_int v₀ v₁ hv₀ hv₁ hv₀_nn hv₁_nn h311 h312 h314 h312'
  have hdc := proof_3_1_derivative_continuity M a b θ₀ ε hθ₀ hε hεΛ k hk_meas hA13 hk_nonneg hA2 hA3
    hf_int v₀ v₁ hv₀ hv₁ hv₀_nn hv₁_nn h311 h312 h314 h312' x hx
  have hu : UniqueDiffOn ℝ (Set.Icc (θ₀ - ε) (θ₀ + ε)) := uniqueDiffOn_Icc (by linarith)
  rw [contDiffOn_one_iff_derivWithin hu]
  exact ⟨fun θ hθ => (hde θ hθ x hx).1.differentiableWithinAt, hdc⟩
