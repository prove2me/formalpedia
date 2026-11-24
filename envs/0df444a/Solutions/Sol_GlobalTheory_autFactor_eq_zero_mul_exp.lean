-- Prove2me | solution 1 for GlobalTheory.autFactor_eq_zero_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:17.185924+00:00
-- url     : https://prove2.me/submissions/d130b9ca-2462-430d-8286-25d69c79e318

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
import Theorems.Thm_GlobalTheory_thetaLinForm_apply

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
theorem _root_.solution {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ)
    (z : Fin g → ℂ) : autFactor a b τ n n' z = autFactor a b τ n n' 0 * cexp (thetaLinForm n z) := by
  have key : ∀ x y : ℂ, eC (x - y) = eC x * cexp (-(2 * Real.pi * Complex.I) * y) := by
    intro x y
    rw [eC, eC, ← Complex.exp_add]
    congr 1
    ring
  simp only [autFactor]
  rw [key (-(ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n)) / 2) (ofIntVec n ⬝ᵥ z), dotProduct_zero, sub_zero,
    thetaLinForm_apply]
  ring
end GlobalTheory
