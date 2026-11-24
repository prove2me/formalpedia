-- Prove2me | solution 1 for GlobalTheory.LowestWeight.posDef_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:12.367494+00:00
-- url     : https://prove2.me/submissions/bcac64ba-1eb0-4a13-b620-59b213ba0855

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq
import Theorems.Thm_GlobalTheory_LowestWeight_quad_eq
import Theorems.Thm_GlobalTheory_LowestWeight_signed_isHermitian

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
theorem _root_.solution {p : ℕ} (e : Fin p → Fin r) (p0 : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (t : Fin r → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (h1 : ∀ a : Fin r, (a : ℕ) < p0 → ρ ≤ ‖t a‖)
    (h2 : ∀ a : Fin r, p0 ≤ (a : ℕ) → ‖t a‖ ≤ ρ)
    (hY : ((Yᵀ * diagonal (fun a : Fin r => (sgn p0 a : ℂ)) *
      Y.map (starRingEnd ℂ)).submatrix e e).PosDef) :
    (((diagonal t * Y)ᵀ * diagonal (fun a : Fin r => (sgn p0 a : ℂ)) *
      (diagonal t * Y).map (starRingEnd ℂ)).submatrix e e).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ((signed_isHermitian _ _).submatrix e) fun v hv => ?_
  have h := hY.dotProduct_mulVec_pos hv
  rw [quad_eq] at h ⊢
  rw [Complex.zero_lt_real] at h ⊢
  refine (mul_pos (pow_pos hρ 2) h).trans_le ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have e1 : ∑ a, (diagonal t * Y) k (e a) * conj (v a) = t k * ∑ a, Y k (e a) * conj (v a) := by
    simp [Matrix.diagonal_mul, Finset.mul_sum, mul_assoc]
  rw [e1, norm_mul, mul_pow]
  set w := ‖∑ a, Y k (e a) * conj (v a)‖ ^ 2
  have hw : 0 ≤ w := by positivity
  unfold sgn
  split_ifs with hk
  · have : ρ ^ 2 ≤ ‖t k‖ ^ 2 := by gcongr; exact h1 k hk
    nlinarith
  · have : ‖t k‖ ^ 2 ≤ ρ ^ 2 := by gcongr; exact h2 k (not_lt.1 hk)
    nlinarith
end GlobalTheory.LowestWeight
