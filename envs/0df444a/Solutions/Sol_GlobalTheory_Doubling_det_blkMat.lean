-- Prove2me | solution 1 for GlobalTheory.Doubling.det_blkMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:24:59.004487+00:00
-- url     : https://prove2.me/submissions/1178bfb8-6ca9-455c-9dc4-6b0033e17f1c

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
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]
namespace GlobalTheory.Doubling
theorem _root_.solution (x : Matrix m m A) (y : Matrix n n A) : (blkMat e x y).det = x.det * y.det := by
  simp [blkMat]
end GlobalTheory.Doubling
