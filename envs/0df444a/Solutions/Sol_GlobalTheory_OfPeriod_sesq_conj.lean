-- Prove2me | solution 1 for GlobalTheory.OfPeriod.sesq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:10.795745+00:00
-- url     : https://prove2.me/submissions/9c9e8772-b468-40f7-9e97-91f1c469de23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_sesq_apply
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
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    starRingEnd ℂ (sesq Hm z w) = sesq Hm w z := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  simp only [sesq_apply, hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
end GlobalTheory.OfPeriod
