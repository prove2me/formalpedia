-- Prove2me | solution 1 for GlobalTheory.eisTerm_at_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:06.209028+00:00
-- url     : https://prove2.me/submissions/17da0495-9333-45eb-8623-39d0eac35f87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormFderivLeOfClosedBallSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open Metric Complex
open GlobalTheory
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] [NumberField F] (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    eisTerm k 0 z p = (∏ τ, latPt z p τ)⁻¹ ^ k := by
  simp [eisTerm]
end GlobalTheory
