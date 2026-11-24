-- Prove2me | solution 1 for GlobalTheory.T.isClosed_isHermitianLogOfPosDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:15:07.637131+00:00
-- url     : https://prove2.me/submissions/4427641e-27d9-4102-a06d-49c00fca38b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDefStatement
import Theorems.Thm_GlobalTheory_ClassFin_isClosed_isLog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  first | exact @GlobalTheory.ClassFin.isClosed_isLog | exact GlobalTheory.ClassFin.isClosed_isLog | (intros; apply GlobalTheory.ClassFin.isClosed_isLog <;> assumption)
end _root_.GlobalTheory.T
