-- Prove2me | solution 1 for GlobalTheory.groupAlgebra_single_one_mem_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:58:57.931063+00:00
-- url     : https://prove2.me/submissions/63657be7-9783-4888-b8ca-d0d289addb1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A X : Type} [CommRing A] [AddCommGroup X]
    (R : Subring (AddMonoidAlgebra A X)) (h0 : ∀ a : A, AddMonoidAlgebra.single 0 a ∈ R) (α : X)
    (h : Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R} = ⊤) :
    AddMonoidAlgebra.single α (1 : A) ∈ R := by
  have key : ∀ a ∈ Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R},
      AddMonoidAlgebra.single α a ∈ R := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => rw [AddMonoidAlgebra.single_zero]; exact R.zero_mem
    | add x y _ _ hx hy => rw [AddMonoidAlgebra.single_add]; exact R.add_mem hx hy
    | smul c x _ hx =>
      have := R.mul_mem (h0 c) hx
      rwa [AddMonoidAlgebra.single_mul_single, zero_add] at this
  exact key 1 (h ▸ Submodule.mem_top)
end GlobalTheory
