-- Prove2me | solution 1 for GlobalTheory.NormIntegers.existsUnique_extend_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:04.211908+00:00
-- url     : https://prove2.me/submissions/5e00758e-1ebc-495f-9141-d91ded99b991

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_existsUnique_adicCompletion_ringHom_extend
import Theorems.Thm_GlobalTheory_NormIntegers_isAdicComplete_of_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
open GlobalTheory.NormIntegers
variable {C : Type*} [NormedField C] [IsUltrametricDist C] {O : Type*} [CommRing O] [Algebra O C]
  (hO : (NormedField.valuation (K := C)).Integers O)
include hO
namespace GlobalTheory.NormIntegers
theorem _root_.solution [CompleteSpace C] {A : Type*} [CommRing A] [IsLocalRing A]
    (hA : (IsLocalRing.maximalIdeal A).FG) (f : A →+* O) [IsLocalHom f] :
    ∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* O,
      g.comp (algebraMap A _) = f := by
  haveI := isLocalRing hO
  haveI : IsAdicComplete ((IsLocalRing.maximalIdeal A).map f) O :=
    isAdicComplete_of_fg hO (hA.map f) (IsLocalRing.map_maximalIdeal_lt_top f).ne
  exact existsUnique_adicCompletion_ringHom_extend _ hA f
end GlobalTheory.NormIntegers
