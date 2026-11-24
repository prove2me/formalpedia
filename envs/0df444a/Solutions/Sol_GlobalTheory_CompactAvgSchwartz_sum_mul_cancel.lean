-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.sum_mul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:34.503809+00:00
-- url     : https://prove2.me/submissions/f376a888-4588-4aba-8373-4e307624c0a4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
namespace GlobalTheory.CompactAvgSchwartz
theorem _root_.solution {R : Type} [Ring R] {m n : ℕ} {A B : Matrix (Fin m) (Fin m) R} (h : B * A = 1)
    (y : Fin m → Fin n → R) : (fun i j => ∑ c, B i c * ∑ d, A c d * y d j) = y := by
  have hM : B * (A * Matrix.of y) = Matrix.of y := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  funext i j
  have := congrFun (congrFun hM i) j
  simpa [Matrix.mul_apply] using this
end GlobalTheory.CompactAvgSchwartz
