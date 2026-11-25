-- Prove2me | solution 1 for GlobalTheory.DetPairingBound.cayDet_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:53.527097+00:00
-- url     : https://prove2.me/submissions/8c1e948b-de0b-4eb0-ba10-993070d294f3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.DetPairingBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
namespace GlobalTheory.DetPairingBound
theorem _root_.solution (n : ℕ) (C : Type) [CommRing C] :
    (cayDet n C).IsHomogeneous n := by
  show (Matrix.mvPolynomialX (Fin n) (Fin n) C).det.IsHomogeneous n
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← map_intCast (MvPolynomial.C : C →+* MvPolynomial (Fin n × Fin n) C)]
  refine IsHomogeneous.C_mul ?_ _
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i) (fun _ => 1)
    (fun i _ => by simpa [Matrix.mvPolynomialX_apply] using isHomogeneous_X (R := C) ((σ i, i) : Fin n × Fin n))
  simpa using h
end GlobalTheory.DetPairingBound
