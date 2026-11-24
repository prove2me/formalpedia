-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_thetaLinForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:57.781776+00:00
-- url     : https://prove2.me/submissions/115550b6-0321-499b-84e8-36040894a420

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
import Theorems.Thm_GlobalTheory_thetaLinForm_apply
import Theorems.Thm_P2M_GlobalTheory_ofIntVec_single__0c7ebe1c80f5
import Theorems.Thm_GlobalTheory_linForm_eq_dotProduct
import Theorems.Thm_P2M_GlobalTheory_two_pi_I_ne_zero__c58fadd1bf16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ n n' : Fin g → ℤ, thetaLinForm n w = lam (τ *ᵥ ofIntVec n + ofIntVec n')) : w = 0 := by
  have hlam : (fun j => lam (Pi.single j 1)) = 0 := by
    funext j
    have hj := h 0 (Pi.single j 1)
    rw [thetaLinForm_apply, ofIntVec_zero, zero_dotProduct, mul_zero, mulVec_zero, zero_add,
      ofIntVec_single'] at hj
    exact hj.symm
  funext i
  have hi := h (Pi.single i 1) 0
  rw [thetaLinForm_apply, ofIntVec_single', single_dotProduct, _root_.one_mul, ofIntVec_zero, add_zero,
    linForm_eq_dotProduct lam, hlam, zero_dotProduct] at hi
  exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr two_pi_I_ne_zero')
end GlobalTheory
