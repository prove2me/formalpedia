-- Prove2me | solution 1 for GlobalTheory.Doubling.submatrix_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:40:44.034556+00:00
-- url     : https://prove2.me/submissions/87127fb9-f457-49fe-874b-521f53763c35

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
namespace GlobalTheory.Doubling
theorem _root_.solution {M N : Matrix ι ι A} (h : M.submatrix e e = N.submatrix e e) : M = N := by
  simpa using congrArg (fun X => X.submatrix e.symm e.symm) h
end GlobalTheory.Doubling
