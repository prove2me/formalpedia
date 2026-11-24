-- Prove2me | solution 1 for GlobalTheory.WittGauss.pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:54.051643+00:00
-- url     : https://prove2.me/submissions/3b886be8-418c-4c69-beb2-eb87826d9668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))
include h1 hm
namespace GlobalTheory.WittGauss
theorem _root_.solution (x : R) (k : ℕ) : a (x ^ k) = a x ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [pow_succ, hm, ih, pow_succ]
end GlobalTheory.WittGauss
