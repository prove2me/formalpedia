-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.smul_top_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:45.306492+00:00
-- url     : https://prove2.me/submissions/0ecc7710-9073-4518-910c-1f2278a0ce18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution (I : Ideal V) : (I • ⊤ : Submodule V V) = I := by
  rw [smul_eq_mul, Ideal.mul_top]
end GlobalTheory.PadicUnitBall
