-- Prove2me | solution 1 for GlobalTheory.Doubling.sgn_mul_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:45.461209+00:00
-- url     : https://prove2.me/submissions/6710c70c-7d2b-4f17-99e6-9c8d73a93f7e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
variable [Fintype n] [Fintype ι]
variable {e}
variable [DecidableEq n] [DecidableEq ι]
variable (e)
namespace GlobalTheory.Doubling
theorem _root_.solution : blkMat e (1 : Matrix n n A) (-1) * blkMat e (1 : Matrix n n A) (-1) = 1 := by
  simp [blkMat_mul, blkMat_one]
end GlobalTheory.Doubling
