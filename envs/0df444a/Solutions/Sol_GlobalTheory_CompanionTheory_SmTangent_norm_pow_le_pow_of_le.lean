-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmTangent.norm_pow_le_pow_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:55.011108+00:00
-- url     : https://prove2.me/submissions/eed42461-85d3-45e6-85e8-2ea19590c85d

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmTangent
variable {A : Type*} [NormedRing A]
namespace GlobalTheory.CompanionTheory.SmTangent
theorem _root_.solution (h1 : ‖(1 : A)‖ ≤ 1) {b : A} {C : ℝ} (hC : 1 ≤ C) (hb : ‖b‖ ≤ C) (k : ℕ) :
    ‖b ^ k‖ ≤ C ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖b ^ k * b‖ ≤ ‖b ^ k‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ C ^ k * C := by
        gcongr
end GlobalTheory.CompanionTheory.SmTangent
