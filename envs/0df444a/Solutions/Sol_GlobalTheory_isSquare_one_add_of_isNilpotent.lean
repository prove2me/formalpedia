-- Prove2me | solution 1 for GlobalTheory.isSquare_one_add_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:18:09.284823+00:00
-- url     : https://prove2.me/submissions/4d59ba3a-1f32-4d75-99a9-22fe5ad556e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFields
import Theorems.Thm_GlobalTheory_isSquare_one_add_of_pow_two_pow_eq_zero

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
theorem _root_.solution {A : Type} [CommRing A] (c : A) (hc : 2 * c = 1)
    {n : A} (hn : IsNilpotent n) : IsSquare (1 + n) := by
  obtain ⟨N, hN⟩ := hn
  exact isSquare_one_add_of_pow_two_pow_eq_zero c hc N n
    (pow_eq_zero_of_le (Nat.lt_two_pow_self).le hN)
end GlobalTheory
