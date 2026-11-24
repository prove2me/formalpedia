-- Prove2me | solution 1 for GlobalTheory.WeilSmooth.mid_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:52.145852+00:00
-- url     : https://prove2.me/submissions/0693c461-dbcd-4a24-af95-5676928472ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.WeilSmooth
namespace GlobalTheory.WeilSmooth
theorem _root_.solution {k : Type} [CommRing k] (a a' t t' : k) (ha : a * a' = 1) (ht : t * t' = 1) :
    ((nS ((a - 1) * t') * lS t * nS ((a' - 1) * t') * lS (-(t * a)) : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, a'] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (a-1)*ht - t*a*((a-1)*(a'-1)*t'*ht + t'*ha)
  · linear_combination (a-1)*(a'-1)*t' * ht + t' * ha
  · linear_combination (-t*a*(a'-1))*ht - t*ha
  · linear_combination (a'-1)*ht
end GlobalTheory.WeilSmooth
