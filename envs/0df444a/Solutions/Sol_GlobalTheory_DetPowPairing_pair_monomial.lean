-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.pair_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:40.061987+00:00
-- url     : https://prove2.me/submissions/82a8871f-9858-43a8-bba1-b4448da31894

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution (A : σ →₀ ℕ) (c : C) (Q : MvPolynomial σ C) :
    pair (monomial A c) Q = c * wt C A * coeff A Q := by
  have h : monomial A c = c • (basisMonomials σ C) A := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pair, Module.Basis.constr_basis, LinearMap.smul_apply, LinearMap.smul_apply, lcoeff_apply,
    smul_eq_mul, smul_eq_mul, mul_assoc]
end GlobalTheory.DetPowPairing
