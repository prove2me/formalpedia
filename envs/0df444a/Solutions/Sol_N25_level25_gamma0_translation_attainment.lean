-- Prove2me | solution 1 for N25.level25_gamma0_translation_attainment
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:27.475876+00:00
-- url     : https://prove2.me/submissions/ba071795-91d3-4c6e-8c59-d45f57a1bd2b

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
    let translate : ℕ → R → R := fun n r => (r.1,r.2+(n:ZMod 25)*r.1)
    let tnorm : R → ℕ := fun r =>
      if r.1.val%5≠0 then 1 else if r.1=0 then 25
      else 25+5*((r.1.val/5)*((r.2.val : ZMod 5)⁻¹).val%5)
    ∀ r : R, primitive r → ∃ n : Fin 25, code (normal (translate n.val r)) = tnorm r := by
  decide +kernel

end N25
