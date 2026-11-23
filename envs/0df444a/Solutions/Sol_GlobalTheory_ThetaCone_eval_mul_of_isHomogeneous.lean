-- Prove2me | solution 1 for GlobalTheory.ThetaCone.eval_mul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:19.551271+00:00
-- url     : https://prove2.me/submissions/23573bfb-07a4-4764-84a6-cfaba789b8cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ThetaCone
open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaCone
theorem _root_.solution (q : ι → ℂ) (t : ℂ) {G : MvPolynomial ι ℂ} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => t * q i) G = t ^ m * eval q G := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hG (mem_support_iff.mp hs)
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at hw
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  ring
end GlobalTheory.ThetaCone
