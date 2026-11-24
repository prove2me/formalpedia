-- Prove2me | solution 1 for GlobalTheory.WpFam.nsmul_zmod_eq_zero_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:47.5258+00:00
-- url     : https://prove2.me/submissions/7bdf7e0b-2684-4955-b5f6-5e1057849864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastMulTorsMemLatticeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
end GlobalTheory.WpFam
