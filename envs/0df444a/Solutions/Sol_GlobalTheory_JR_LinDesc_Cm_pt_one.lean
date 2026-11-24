-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Cm_pt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:53:19.384985+00:00
-- url     : https://prove2.me/submissions/5ef324ec-3248-4db2-ab56-5eb25176be0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOne
import Theorems.Thm_GlobalTheory_JR_LinDesc_row_pow
import Theorems.Thm_GlobalTheory_JR_LinDesc_bas_apply
import Theorems.Thm_GlobalTheory_JR_LinDesc_row_mul


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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution (hG : A.IsGen τ p) (lam : F) (a : A.K) :
    Cm (pt A hG lam 1 a) = Algebra.traceMatrix F (bas A hG) * Algebra.leftMulMatrix (bas A hG) a := by
  ext i j
  have h1 : Cm (pt A hG lam 1 a) i j = Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ (i : ℕ) * a)) := by
    simp only [Cm, pt, Matrix.of_apply]
    rw [row_pow A hG]
  have h2 := congrFun (row_mul A hG a (τ ^ (i : ℕ))) j
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [h1, Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bas_apply]
  rw [mul_comm (τ ^ (i : ℕ)) a, ← h2]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (τ ^ (i : ℕ))]
end GlobalTheory.JR.LinDesc
