-- Prove2me | solution 1 for GlobalTheory.InertZeta.preLat_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:06.658005+00:00
-- url     : https://prove2.me/submissions/eda10b28-3f5e-462f-a410-1874ed5cc33f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
import Theorems.Thm_GlobalTheory_InertZeta_mem_scaledInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mem_preLat
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution (ϖ : L) (d : Fin n → ℕ) :
    preLat (Matrix.diagonal fun i => ϖ ^ d i) = AddSubgroup.pi Set.univ fun i => scaledInt (ϖ ^ d i) := by
  ext r
  rw [mem_preLat, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_scaledInt, Matrix.vecMul_diagonal, mul_comm (r _)]
end GlobalTheory.InertZeta
