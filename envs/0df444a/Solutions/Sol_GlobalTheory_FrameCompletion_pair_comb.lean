-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.pair_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:56.795923+00:00
-- url     : https://prove2.me/submissions/4422ac83-6b2e-4a76-abf5-287dddb4e23e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_add
import Theorems.Thm_GlobalTheory_FrameCompletion_conjT_smul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
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
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (s t s' t' : L) :
    cT σ (s • X + t • W) * Q * (s' • X + t' • W) =
      (σ s * s') • (cT σ X * Q * X) + (σ s * t') • (cT σ X * Q * W) + (σ t * s') • (cT σ W * Q * X) +
        (σ t * t') • (cT σ W * Q * W) := by
  simp only [conjT_add, conjT_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module
end GlobalTheory.FrameCompletion
