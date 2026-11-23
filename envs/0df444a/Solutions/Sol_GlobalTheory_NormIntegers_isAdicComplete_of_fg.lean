-- Prove2me | solution 1 for GlobalTheory.NormIntegers.isAdicComplete_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:48.200731+00:00
-- url     : https://prove2.me/submissions/ca23495f-ff2f-47fa-8884-9aada2c11ea7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_NormIntegers_eq_bot_or_eq_span_of_fg_of_ne_top

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
theorem _root_.solution [CompleteSpace C] {J : Ideal O} (hJ : J.FG) (hJ' : J ≠ ⊤) :
    IsAdicComplete J O := by
  rcases eq_bot_or_eq_span_of_fg_of_ne_top hO hJ hJ' with rfl | ⟨w, -, hw, rfl⟩
  · infer_instance
  · exact isAdicComplete_span_singleton hO hw
end GlobalTheory.NormIntegers
