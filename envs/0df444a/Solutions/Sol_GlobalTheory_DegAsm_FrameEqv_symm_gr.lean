-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameEqv.symm_gr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:10.435809+00:00
-- url     : https://prove2.me/submissions/42d8489f-6045-4704-b11c-1e4cc8f2d6f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrEqvEquivalence
import Theorems.Thm_GlobalTheory_DegAsm_FrameEqv_symm_xa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameEqv
open AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.FrameEqv
theorem _root_.solution {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (a : Fin (r + 1)) : n.symm (G'.e a) - G.e a ∈ G.Xa a.val := by
  have h1 := symm_xa h a.val _ (h a)
  have e1 : n.symm (G'.e a) - G.e a = -(n.symm (n (G.e a) - G'.e a)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
  rw [e1]
  exact (G.Xa a.val).neg_mem h1
end GlobalTheory.DegAsm.FrameEqv
