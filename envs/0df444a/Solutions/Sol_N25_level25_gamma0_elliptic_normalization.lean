-- Prove2me | solution 1 for N25.level25_gamma0_elliptic_normalization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:24.960167+00:00
-- url     : https://prove2.me/submissions/c28650da-da24-4603-9c09-b2492bcd3ea8

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Finite unit-normalized primitive-row orbit data at level twenty-five. -/
theorem _root_.solution :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let S : R → R := fun r => (r.2,-r.1)
    let ST : R → R := fun r => (r.2,r.2-r.1)
    let snorm : R → ℕ := fun r => min (code (normal r)) (code (normal (S r)))
    let stnorm : R → ℕ := fun r =>
      min (code (normal r)) (min (code (normal (ST r))) (code (normal (ST (ST r)))))
    (∀ r : R, primitive r → ∃ n : Fin 2,
      code (normal (if n.val=0 then r else S r)) = snorm r) ∧
    (∀ r : R, primitive r → ∃ n : Fin 3,
      code (normal (if n.val=0 then r else if n.val=1 then ST r else ST (ST r))) = stnorm r) ∧
    (∀ r : R, primitive r → snorm (S r) = snorm r ∧ stnorm (ST r) = stnorm r ∧
      primitive (S r) ∧ primitive (ST r)) := by
  decide +kernel

end N25
