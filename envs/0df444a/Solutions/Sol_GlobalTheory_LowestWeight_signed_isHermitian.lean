-- Prove2me | solution 1 for GlobalTheory.LowestWeight.signed_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:31.230505+00:00
-- url     : https://prove2.me/submissions/8b6d1aa9-9329-4ba3-bc6e-8be516732c06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq

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
variable {r : ℕ}
namespace GlobalTheory.LowestWeight
theorem _root_.solution (s : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    (Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)).IsHermitian := by
  have h : Yᵀ = (Y.map (starRingEnd ℂ))ᴴ := by
    ext a b; simp
  rw [h]
  refine isHermitian_conjTranspose_mul_mul _ ?_
  rw [isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]
end GlobalTheory.LowestWeight
