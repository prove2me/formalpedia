-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.indexTwo_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:58.217905+00:00
-- url     : https://prove2.me/submissions/7c7a8f14-07d6-4168-a5b7-fa60f6f02e22

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCard
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv
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
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {ϖ : L} (h0 : ϖ ≠ 0) (s g : GU σ 2)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i)) (y : L)
    (h : mat g = !![1, y; 0, 1]) : mat (s * g * s⁻¹) = !![1, ϖ * (ϖ * y); 0, 1] := by
  have e : mat s * mat g = !![1, ϖ * (ϖ * y); 0, 1] * mat s := by
    rw [hs, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rw [mat_mul, mat_mul, e, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
end GlobalTheory.SatakeWeyl
