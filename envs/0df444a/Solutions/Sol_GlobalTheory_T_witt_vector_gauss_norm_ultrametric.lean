-- Prove2me | solution 1 for GlobalTheory.T.witt_vector_gauss_norm_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:52.704892+00:00
-- url     : https://prove2.me/submissions/6d989511-1d2d-406c-b11f-8178441c7fb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametricStatement
import Theorems.Thm_GlobalTheory_WittGauss_gaussNorm_ultrametric_submul


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ ∀ x y, N (x * y) ≤ N x * N y := by
  first | exact @GlobalTheory.WittGauss.gaussNorm_ultrametric_submul | exact GlobalTheory.WittGauss.gaussNorm_ultrametric_submul | (intros; apply GlobalTheory.WittGauss.gaussNorm_ultrametric_submul <;> assumption)
end _root_.GlobalTheory.T
