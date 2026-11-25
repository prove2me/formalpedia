-- Prove2me | solution 1 for GlobalTheory.OfPeriod.sesq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:48.803274+00:00
-- url     : https://prove2.me/submissions/a90d48c9-3dbd-4139-87a9-6711e8cd4bc5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
namespace GlobalTheory.OfPeriod
theorem _root_.solution {n : ℕ} (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ) (z w : Fin n → ℂ) :
    hermForm (Matrix.of fun i j => S (Pi.single i 1) (Pi.single j 1)) z w = S z w := by
  conv_rhs => rw [pi_eq_sum_univ' z, pi_eq_sum_univ' w]
  simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.OfPeriod
