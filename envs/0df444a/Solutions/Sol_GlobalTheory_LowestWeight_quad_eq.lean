-- Prove2me | solution 1 for GlobalTheory.LowestWeight.quad_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:30.315499+00:00
-- url     : https://prove2.me/submissions/53b89dac-a3b1-4dcd-8e86-1decb05e79d4

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
theorem _root_.solution {p : ℕ} (e : Fin p → Fin r) (s : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin p → ℂ) :
    star v ⬝ᵥ ((Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)).submatrix e e *ᵥ v) =
      ((∑ k, s k * ‖∑ a, Y k (e a) * conj (v a)‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ a b, (Yᵀ * diagonal (fun a => (s a : ℂ)) * Y.map (starRingEnd ℂ)) a b =
      ∑ k, Y k a * s k * conj (Y k b) := by
    intro a b
    rw [Matrix.mul_apply]
    simp [Matrix.mul_diagonal]
  push_cast
  simp only [dotProduct, mulVec, submatrix_apply, h, Pi.star_apply, Complex.star_def,
    ← Complex.mul_conj', map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
end GlobalTheory.LowestWeight
