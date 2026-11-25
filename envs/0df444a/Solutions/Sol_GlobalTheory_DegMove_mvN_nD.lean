-- Prove2me | solution 1 for GlobalTheory.DegMove.mvN_nD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:20.442268+00:00
-- url     : https://prove2.me/submissions/5141e604-df7c-4361-883b-e8a8c615c2a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Theorems.Thm_GlobalTheory_DegMove_mv_Dl
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.DegMove
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} {s : V ≃ₗ[K] V}
variable (hs : s ∈ isomGrp H) (N : NF H r)
namespace GlobalTheory.DegMove
theorem _root_.solution (l : ℕ) : (mvN hs N).nD l = N.nD l := by
  unfold NF.nD
  change (if h : l ≤ r + 1 then |((Algebra.norm ℚ (Dl (mv hs N.F) (mv hs N.F') l h) : ℚ) : ℝ)| * _ else 0) = _
  simp only [mv_Dl]
  rfl
end GlobalTheory.DegMove
