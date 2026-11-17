-- Prove2me | solution 1 for N25.exists_forget_algEquiv_action
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:07.021077+00:00
-- url     : https://prove2.me/submissions/47a1ab36-2d09-4b36-b25d-6792edb514d4

import Mathlib

set_option autoImplicit false

namespace N25

/-- An algebra automorphism action has a ring automorphism action with the same
pointwise evaluation, preserving the supplied algebra structure parameter. -/
theorem _root_.solution
    {R A G : Type*} [CommSemiring R] [Semiring A] [Monoid G]
    [algebra : Algebra R A] (ρa : G →* (A ≃ₐ[R] A)) :
    ∃ ρ : G →* RingAut A, ∀ g x, ρ g x = ρa g x := by
  refine ⟨{ toFun := fun g => (ρa g).toRingEquiv
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext x
    change ρa 1 x = x
    rw [ρa.map_one]
    rfl
  · intro a b
    ext x
    change ρa (a*b) x = ρa a (ρa b x)
    rw [ρa.map_mul]
    rfl
  · intro g x
    rfl

end N25
