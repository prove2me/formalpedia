-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.lmul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:32.683274+00:00
-- url     : https://prove2.me/submissions/9f3ffa0e-4fbd-4cfe-8fcc-1bc7fc49ecb5

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
theorem _root_.solution {ι : Type} [Fintype ι] {m : ℕ} (n : ℕ) (A : ι → Matrix (Fin m) (Fin m) ℂ) (X : ι → Fin m → Fin n → ℂ) :
    lmul n A X = fun τ i j => ∑ c, A τ i c * X τ c j := rfl
end GlobalTheory.CompactAvgSchwartz
