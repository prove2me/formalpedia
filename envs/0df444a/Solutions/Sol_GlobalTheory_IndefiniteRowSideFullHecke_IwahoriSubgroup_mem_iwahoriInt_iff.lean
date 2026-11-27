-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:47:42.438091+00:00
-- url     : https://prove2.me/submissions/6d665c9a-eacd-4bf9-87b3-20690d89beb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_IwahoriSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
theorem _root_.solution (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] (r : ℕ)
    (g : GL (Fin r) (Int F)) :
    g ∈ iwahoriInt F r ↔ ∀ i j : Fin r, j < i →
      Valued.v (((g : Matrix (Fin r) (Fin r) (Int F)) i j : Int F) : F)
        < (1 : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro h i j hij
    have := h (i := i) (j := j) hij
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · intro h i j hij
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h i j hij)
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
