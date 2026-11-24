-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.TorusConjProof.mat_zpow_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:31.219861+00:00
-- url     : https://prove2.me/submissions/6ddf389e-85df-4bf1-a6ce-d39f665c8068

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviCentreDiagonalConjugationEq
import Theorems.Thm_GlobalTheory_SatakeWeyl_TorusConjProof_mat_inv_diag
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.TorusConjProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.TorusConjProof
theorem _root_.solution {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (d : ℤ) :
    mat (s ^ d) = Matrix.diagonal (fun i => ϖ ^ (d * b i)) := by
  induction d using Int.induction_on with
  | zero => simp [mat_one]
  | succ k ih =>
    rw [zpow_add_one, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring
  | pred k ih =>
    rw [zpow_sub_one, mat_mul, ih, mat_inv_diag hϖ hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring
end GlobalTheory.SatakeWeyl.TorusConjProof
