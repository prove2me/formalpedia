-- Prove2me | solution 1 for GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:47.89097+00:00
-- url     : https://prove2.me/submissions/69eea384-57ed-445a-8f5d-7236114d7ba4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparableStatement
import Theorems.Thm_GlobalTheory_SepGenElt_exists_aeval_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  first | exact @GlobalTheory.SepGenElt.exists_aeval_eq | exact GlobalTheory.SepGenElt.exists_aeval_eq | (intros; apply GlobalTheory.SepGenElt.exists_aeval_eq <;> assumption)
end _root_.GlobalTheory.T
