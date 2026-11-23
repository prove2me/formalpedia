-- Prove2me | solution 1 for GlobalTheory.pow_mul_le_comap_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:25.976636+00:00
-- url     : https://prove2.me/submissions/97109973-714d-4612-ad23-3db7e8690e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]
namespace GlobalTheory
theorem _root_.solution (φ : A →+* R) {J : Ideal A} {I : Ideal R} {k : ℕ}
    (hk : J.map φ ^ k ≤ I) (n : ℕ) : J ^ (k * n) ≤ (I ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, pow_mul]
  exact Ideal.pow_right_mono hk n
end GlobalTheory
