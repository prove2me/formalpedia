-- Prove2me | solution 1 for GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:32.187064+00:00
-- url     : https://prove2.me/submissions/93e68e06-5f41-4054-82f7-41ca5d138c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Theorems.Thm_GlobalTheory_SepGen_adjoin_eq_top_and_isReduced


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
theorem _root_.solution : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable → Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A := by
  first | exact @GlobalTheory.SepGen.adjoin_eq_top_and_isReduced | exact GlobalTheory.SepGen.adjoin_eq_top_and_isReduced | (intros; apply GlobalTheory.SepGen.adjoin_eq_top_and_isReduced <;> assumption)
end _root_.GlobalTheory.T
