-- Prove2me | solution 1 for GlobalTheory.PowerExtensionEvaluation.pow_le_comap_map_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:25.086225+00:00
-- url     : https://prove2.me/submissions/dcfa6775-a4d9-4729-bd61-da42ca231733

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PowerExtensionEvaluation
namespace GlobalTheory.PowerExtensionEvaluation
theorem _root_.solution {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (n : ℕ) : I ^ n ≤ ((I.map f) ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (Ideal.map_pow f I n))
end GlobalTheory.PowerExtensionEvaluation
