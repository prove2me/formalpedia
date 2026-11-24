-- Prove2me | solution 1 for GlobalTheory.Doubling.leviMat_leviElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:29.901288+00:00
-- url     : https://prove2.me/submissions/f3b2a0b5-c4de-4f28-84c8-7c00f4351fdc

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_leviElt_diag
import Theorems.Thm_GlobalTheory_Doubling_leviElt_mem_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
namespace GlobalTheory.Doubling
theorem _root_.solution (g : GL n A × GL n A) : leviMat e (leviElt e g).1 = g.1.1 := by
  refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
  have := congrFun ((mem_stabGL_diagSub.1 (leviElt_mem_diag e g)).mulVec_diag (Pi.single j 1)) (e (.inl i))
  rw [leviElt_diag, pairVec_inl, pairVec_inl] at this
  exact this.symm
end GlobalTheory.Doubling
