-- Prove2me | solution 1 for GlobalTheory.DegMove.isotropicFrameMapIsometry_pairComplement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:14.669312+00:00
-- url     : https://prove2.me/submissions/6484ccc0-ab7a-48cf-bcab-562dbdb487d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Theorems.Thm_GlobalTheory_DegMove_smul_sup

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
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
variable (hs : s ∈ isomGrp H) (F F' : FlagD H r)
namespace GlobalTheory.DegMove
theorem _root_.solution : V0 (mv hs F) (mv hs F') = s • V0 F F' := by
  unfold V0
  rw [mv_X, mv_X, ← smul_sup, ← smul_sup, Submodule.smul_span, ← Set.image_smul, Set.image_pair]
  rfl
end GlobalTheory.DegMove
