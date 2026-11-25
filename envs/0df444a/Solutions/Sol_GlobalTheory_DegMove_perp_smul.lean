-- Prove2me | solution 1 for GlobalTheory.DegMove.perp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:53.631961+00:00
-- url     : https://prove2.me/submissions/4e7aeac3-6d0b-49bf-8591-4ab70a157e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Theorems.Thm_GlobalTheory_DegMove_ext_smul
import Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


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
namespace GlobalTheory.DegMove
theorem _root_.solution (hs : s ∈ isomGrp H) (S : Submodule K V) : perp H (s • S) = s • perp H S := by
  refine ext_smul s fun x => ?_
  rw [mem_perp_iff, mem_perp_iff, s.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [memK, LinearEquiv.smul_def, (mem_isomGrp H s).1 hs]
end GlobalTheory.DegMove
