-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:51.82831+00:00
-- url     : https://prove2.me/submissions/0c977f33-358e-485e-bd05-5a63dd879f24

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
theorem _root_.solution {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.traceDual M ↔ y ∈ FractionalIdeal.dual ℤ ℚ M := by
  change (∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n) ↔ _
  rw [FractionalIdeal.mem_dual hM]
  refine forall₂_congr fun a _ => ?_
  simp [Algebra.traceForm_apply, eq_comm]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
