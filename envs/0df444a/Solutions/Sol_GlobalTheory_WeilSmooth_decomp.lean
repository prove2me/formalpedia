-- Prove2me | solution 1 for GlobalTheory.WeilSmooth.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:02.897571+00:00
-- url     : https://prove2.me/submissions/c3797329-7b70-4825-9d4f-de4ef9761c9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
import Theorems.Thm_GlobalTheory_WeilSmooth_sl_ext
import Theorems.Thm_GlobalTheory_WeilSmooth_mid_eq

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
theorem _root_.solution {k : Type} [CommRing k] (g : SpecialLinearGroup (Fin 2) k) (a' t t' : k)
    (ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * a' = 1) (ht : t * t' = 1) :
    g = lS ((g : Matrix (Fin 2) (Fin 2) k) 1 0 * a') * (nS (((g : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) * t') * lS t *
      nS ((a' - 1) * t') * lS (-(t * (g : Matrix (Fin 2) (Fin 2) k) 0 0))) *
      nS ((g : Matrix (Fin 2) (Fin 2) k) 0 1 * a') := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mid_eq _ _ _ _ ha ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 0 1) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0 * (g : Matrix (Fin 2) (Fin 2) k) 0 1 * a' +
      (g : Matrix (Fin 2) (Fin 2) k) 1 1) * ha + a' * hdet
end GlobalTheory.WeilSmooth
