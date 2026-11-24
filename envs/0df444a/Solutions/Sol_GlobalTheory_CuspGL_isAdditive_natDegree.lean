-- Prove2me | solution 1 for GlobalTheory.CuspGL.isAdditive_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:28.154611+00:00
-- url     : https://prove2.me/submissions/bd82b053-bac4-4747-a263-5e51576badcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution : IsAdditive (fun P : F[X] => (P.natDegree : ℂ)) := by
  intro P Q hP hQ
  simp [hP.natDegree_mul hQ]
end GlobalTheory.CuspGL
