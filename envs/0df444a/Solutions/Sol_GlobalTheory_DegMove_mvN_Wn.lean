-- Prove2me | solution 1 for GlobalTheory.DegMove.mvN_Wn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:22.690564+00:00
-- url     : https://prove2.me/submissions/e35570b3-c8c5-41eb-ac46-3666051d7cc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Theorems.Thm_GlobalTheory_DegMove_smul_sup
import Theorems.Thm_GlobalTheory_DegMove_perp_smul
import Theorems.Thm_GlobalTheory_DegMove_mvN_Ist

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
variable (hs : s ∈ isomGrp H) (N : NF H r)
namespace GlobalTheory.DegMove
theorem _root_.solution : (mvN hs N).Wn = s • N.Wn := by
  unfold NF.Wn
  rw [mvN_Ist, ← perp_smul hs, ← smul_sup, ← smul_sup, ← mv_X hs, ← mv_X hs]
  rfl
end GlobalTheory.DegMove
