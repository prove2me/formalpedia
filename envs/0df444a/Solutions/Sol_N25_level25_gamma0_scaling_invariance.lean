-- Prove2me | solution 1 for N25.level25_gamma0_scaling_invariance
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:26.869141+00:00
-- url     : https://prove2.me/submissions/f0c8ca06-c7ce-4d1e-a9b1-3f080f30d34a

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
    ∀ r : R, primitive r → ∀ u : (ZMod 25)ˣ,
      normal ((u:ZMod 25)*r.1,(u:ZMod 25)*r.2) = normal r ∧
      primitive ((u:ZMod 25)*r.1,(u:ZMod 25)*r.2) := by
  decide +kernel

end N25
