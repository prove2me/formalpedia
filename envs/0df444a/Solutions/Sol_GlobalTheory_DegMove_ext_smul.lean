-- Prove2me | solution 1 for GlobalTheory.DegMove.ext_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:59.253089+00:00
-- url     : https://prove2.me/submissions/d93b75b8-2be8-45ab-97e4-535450b92809

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry

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
noncomputable section
open GlobalTheory GlobalTheory.DegMove
variable {G R M : Type*} [Group G] [Ring R] [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M]
namespace GlobalTheory.DegMove
theorem _root_.solution (s : G) {A B : Submodule R M} (h : ∀ x, s • x ∈ A ↔ x ∈ B) : A = s • B := by
  ext y
  obtain ⟨x, rfl⟩ := MulAction.surjective s y
  rw [mem_iff, h]
end GlobalTheory.DegMove
