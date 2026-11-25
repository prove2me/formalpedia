-- Prove2me | solution 1 for GlobalTheory.T.wittVector_gaussNorm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:38.506554+00:00
-- url     : https://prove2.me/submissions/dcfb1474-d55d-4580-9d1e-ef5b6ef26478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMulStatement
import Theorems.Thm_GlobalTheory_witt_gaussNorm_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  first | exact @GlobalTheory.witt_gaussNorm_mul | exact GlobalTheory.witt_gaussNorm_mul | (intros; apply GlobalTheory.witt_gaussNorm_mul <;> assumption)
end _root_.GlobalTheory.T
