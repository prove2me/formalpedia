-- Prove2me | solution 1 for GlobalTheory.lowest_weight_function_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:27.808618+00:00
-- url     : https://prove2.me/submissions/4a754caf-b7c2-4536-82e5-add26cc5860e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
import Theorems.Thm_GlobalTheory_lowest_weight_function_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x₀ : Frame X.Ψ r)
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hx₀' : x₀ ∈ X.dom)
    (m m' : Frame X.Ψ r → ℂ) (hm : DifferentiableOn ℂ m X.dom) (hm' : DifferentiableOn ℂ m' X.dom)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m (rmul x b) = bchar la b * m x)
    (hB' : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, m' (rmul x b) = bchar la b * m' x)
    (hT : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m x)
    (hT' : ∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom,
      m' (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) =
        (∏ τ, ∏ i, t τ i ^ la τ i) * m' x) :
    ∀ x ∈ X.dom, m x * m' x₀ = m' x * m x₀ := by
  intro x hx
  refine sub_eq_zero.1 (lowest_weight_function_unique X la x₀ hx₀ hx₀'
    (fun x => m x * m' x₀ - m' x * m x₀) ((hm.mul_const _).sub (hm'.mul_const _))
    (fun x hx b hb => ?_) (fun t ht x hx => ?_) (by ring) x hx)
  · rw [hB x hx b hb, hB' x hx b hb]; ring
  · rw [hT t ht x hx, hT' t ht x hx]; ring
end GlobalTheory
