-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.inj_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:41.332091+00:00
-- url     : https://prove2.me/submissions/ddbab8af-d0a6-4a14-a30b-1090fe5be675

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution (u : Matrix m k F) (h : ∃ L : Matrix k m F, L * u = 1) :
    Function.Injective (Matrix.toLin' u) := by
  obtain ⟨L, hL⟩ := h
  intro x y hxy
  simp only [Matrix.toLin'_apply] at hxy
  have := congrArg (L *ᵥ ·) hxy
  simpa [Matrix.mulVec_mulVec, hL] using this
end GlobalTheory.SgAlg.WittSplit
