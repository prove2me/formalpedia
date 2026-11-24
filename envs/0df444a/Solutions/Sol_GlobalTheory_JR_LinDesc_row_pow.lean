-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.row_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:32.196951+00:00
-- url     : https://prove2.me/submissions/f05535ed-abbb-4ec7-bd89-bc0ae3c2f836

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOne
import Theorems.Thm_GlobalTheory_JR_LinDesc_leftMul_tau
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
theorem _root_.solution (hG : A.IsGen τ p) (c : A.K) (n : ℕ) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* (companion p) ^ n =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ n * c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, ← leftMul_tau A hG, row_mul]
    funext j
    congr 2
    ring
end GlobalTheory.JR.LinDesc
