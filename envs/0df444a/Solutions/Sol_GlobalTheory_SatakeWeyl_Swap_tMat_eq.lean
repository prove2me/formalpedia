-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Swap.tMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:28.151795+00:00
-- url     : https://prove2.me/submissions/7c7674a4-bd21-4d07-9a97-113b5f1e8dbd

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
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
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Swap
namespace GlobalTheory.SatakeWeyl.Swap
theorem _root_.solution {L : Type} [Field L] (ϖ : L) (n m : ℕ) (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun i => ϖ ^ ex n m a i := by
  unfold tMat ex
  congr 1
  funext i
  split_ifs <;> simp
end GlobalTheory.SatakeWeyl.Swap
