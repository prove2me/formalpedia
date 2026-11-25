-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.orth_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:52.164323+00:00
-- url     : https://prove2.me/submissions/9b1117ad-c265-48dd-8b64-9e77a8934597

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_Xa_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (F : FlagD H r) {a : ℕ} {x y : V} (hx : x ∈ F.Xa a)
    (h : ∀ b : Fin r, b.val < a → H.B (F.e b.castSucc) y = 0) : H.B x y = 0 := by
  have h2 : F.Xa a ≤ LinearMap.ker (H.B.flip y) :=
    GlobalTheory.DegCnt.LiftS.Xa_le (fun b hb => by rw [LinearMap.mem_ker, LinearMap.flip_apply]; exact h b hb)
  have h3 := h2 hx
  rwa [LinearMap.mem_ker, LinearMap.flip_apply] at h3
end GlobalTheory.DegCnt.LiftS
