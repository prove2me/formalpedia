-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Neg.expo_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:32.122682+00:00
-- url     : https://prove2.me/submissions/4cf4cbb8-f56b-4fa5-bdec-40d966d68728

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffLastSignChangeOfLeviReduction
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
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Neg
namespace GlobalTheory.SatakeWeyl.Neg
theorem _root_.solution {n m : ℕ} (h : 2 * m ≤ n) (A : ℕ → ℤ) (x : Fin n) :
    expo n m A x.rev = -expo n m A x := by
  have hx := x.2
  have hr : (x.rev : ℕ) = n - 1 - x := by rw [Fin.val_rev]; omega
  unfold expo
  rw [hr]
  have e : n - 1 - (n - 1 - x.val) = x.val := by omega
  rw [e]
  split_ifs <;> first | omega | simp
end GlobalTheory.SatakeWeyl.Neg
