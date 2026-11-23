-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.pairing_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:36.272802+00:00
-- url     : https://prove2.me/submissions/8a57707a-b4fe-40bd-a016-4916aaa09b71

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open PadicInt
variable {A : Type*} [AddCommGroup A] {L : Type*} [Field L] (N : ℕ) (e : A → A → L)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P Q : A} (hP : N • P = 0) (hQ : N • Q = 0) : e P Q ≠ 0 := by
  intro h
  have h1 := hpow P Q hP hQ
  rw [h, zero_pow hN] at h1
  exact zero_ne_one h1
end GroundTheory.Arith.Abelian
