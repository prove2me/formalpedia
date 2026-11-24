-- Prove2me | solution 1 for GlobalTheory.GammaOneProof.wn_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:52.207361+00:00
-- url     : https://prove2.me/submissions/830955a3-ba18-46aa-8ca2-caf5d1da8a48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianLatticeIsOpenIsCompactTestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KerLEqTraceDotProductOfIsIsomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PsiKMulNLEqOneOnIntegralLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierIndicatorHermitianIntegralLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConstantStandardHermitianEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GammaOneProof
namespace GlobalTheory.GammaOneProof
theorem _root_.solution (k : Type) [CommRing k] : (wS k * nS 1) ^ 3 = 1 := by
  have h : ((wS k * nS 1 : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, 1; -1, 0] * !![1, 1; 0, 1] := rfl
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_fin_two]
end GlobalTheory.GammaOneProof
