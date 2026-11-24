-- Prove2me | solution 1 for GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:26.981574+00:00
-- url     : https://prove2.me/submissions/b96924d8-7668-4ec9-8a93-ffd56055d72d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model
namespace GlobalTheory.Tw.CentralizerAdjoin
theorem _root_.solution {N : Matrix (Fin n) (Fin n) R} (hN : IsUnit N) :
    N⁻¹ ∈ Algebra.adjoin R {N} := by
  have hd := (Matrix.isUnit_iff_isUnit_det N).mp hN
  have hc : IsUnit (N.charpoly.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hd
    exact isUnit_of_mul_isUnit_right hd
  have key := congrArg (aeval N) (Polynomial.X_mul_divX_add N.charpoly)
  rw [Matrix.aeval_self_charpoly, map_add, map_mul, aeval_X, aeval_C] at key
  have hinv : N⁻¹ = -((hc.unit⁻¹ : Rˣ) : R) • aeval N (divX N.charpoly) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, eq_neg_iff_add_eq_zero.mpr key, smul_neg, neg_smul, neg_neg,
      Algebra.algebraMap_eq_smul_one, smul_smul, hc.val_inv_mul, one_smul]
  rw [hinv]
  exact Subalgebra.smul_mem _ (aeval_mem_adjoin_singleton R N) _
end GlobalTheory.Tw.CentralizerAdjoin
