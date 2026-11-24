-- Prove2me | solution 1 for GlobalTheory.LowestWeight.gramPos_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:16.86533+00:00
-- url     : https://prove2.me/submissions/387ef261-1a2c-49b6-9d34-a49e0f51a207

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul


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
    (y : Frame X.Ψ r) (τ : X.Ψ) :
    X.gramPos (rmul x₀ y) τ = ((mat y τ)ᵀ * diagonal (fun a : Fin r => (sgn X.p0 a : ℂ)) *
      (mat y τ).map (starRingEnd ℂ)).submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by
  rw [← hx₀ τ, ← FrameDegreeData.gram_mul]
  rfl
end GlobalTheory.LowestWeight
