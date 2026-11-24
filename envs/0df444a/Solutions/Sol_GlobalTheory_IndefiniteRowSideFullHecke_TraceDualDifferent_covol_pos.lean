-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:39:54.187855+00:00
-- url     : https://prove2.me/submissions/c8c67d2b-2832-4f31-9921-96467d306564

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
open NumberField nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
theorem _root_.solution {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol M := by
  refine mul_pos (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))) ?_
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg M)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.2 hM))
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
