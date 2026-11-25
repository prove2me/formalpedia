-- Prove2me | solution 1 for GlobalTheory.LowestWeight.contract_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:22.842978+00:00
-- url     : https://prove2.me/submissions/068ffcde-8d00-45b8-b7e5-4c8bde027c89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
import Theorems.Thm_GlobalTheory_LowestWeight_posDef_contract
import Theorems.Thm_GlobalTheory_LowestWeight_gramPos_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_dom_of_gramPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef


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
open GlobalTheory.LowestWeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.LowestWeight
theorem _root_.solution {x₀ : Frame X.Ψ r}
    (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    {y : Frame X.Ψ r} (hy : rmul x₀ y ∈ X.dom) (t : Fin r → ℂ) (ht : ∀ a, t a ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (h1 : ∀ a : Fin r, (a : ℕ) < X.p0 → ρ ≤ ‖t a‖)
    (h2 : ∀ a : Fin r, X.p0 ≤ (a : ℕ) → ‖t a‖ ≤ ρ) :
    rmul x₀ (fun τ => (diagonal t * mat y τ : Matrix (Fin r) (Fin r) ℂ)) ∈ X.dom := by
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · have h : (mat x₀ τ * mat y τ).det ≠ 0 := (hy τ).1
    change (mat x₀ τ * (diagonal t * mat y τ)).det ≠ 0
    rw [det_mul] at h
    rw [det_mul, det_mul, det_diagonal]
    exact mul_ne_zero (left_ne_zero_of_mul h)
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => ht a) (right_ne_zero_of_mul h))
  · have h := X.gramPos_posDef hy τ
    rw [gramPos_rmul X hx₀] at h
    exact (gramPos_rmul X hx₀ _ τ).symm ▸ posDef_contract _ _ _ t hρ h1 h2 h
end GlobalTheory.LowestWeight
