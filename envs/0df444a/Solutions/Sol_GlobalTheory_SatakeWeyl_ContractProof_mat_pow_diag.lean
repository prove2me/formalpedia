-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.ContractProof.mat_pow_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:30.840095+00:00
-- url     : https://prove2.me/submissions/28f4ac4d-4aac-4690-8574-9f3eda043454

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.ContractProof
theorem _root_.solution {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (j : ℕ) :
    mat (s ^ j) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * c i)) := by
  induction j with
  | zero => simp [mat_one]
  | succ j ih =>
    rw [pow_succ, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; congr 1; push_cast; ring
end GlobalTheory.SatakeWeyl.ContractProof
