-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.herm_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:13:22.677+00:00
-- url     : https://prove2.me/submissions/1ed18ef0-dda5-48eb-b593-46fc43907951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_normSq_param_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero
namespace GlobalTheory.HCXi.ConeZero
theorem _root_.solution (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1))
      (param n p) (param n p) = 0 := by
  have h := normSq_param_last n p
  rw [herm, dotProduct, Fin.sum_univ_castSucc]
  simp only [mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, one_mul, Pi.star_apply,
    RCLike.star_def, neg_mul, mul_neg, ← Complex.normSq_eq_conj_mul_self, h]
  simp only [param, Fin.snoc_castSucc, sqLen]
  push_cast
  ring
end GlobalTheory.HCXi.ConeZero
