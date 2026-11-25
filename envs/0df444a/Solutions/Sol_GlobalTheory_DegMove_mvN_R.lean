-- Prove2me | solution 1 for GlobalTheory.DegMove.mvN_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:39.325808+00:00
-- url     : https://prove2.me/submissions/4eaa4968-451c-4d4f-b8e5-41cbb658f1aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometry
import Theorems.Thm_GlobalTheory_DegMove_mv_inN

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
theorem _root_.solution : (mvN hs N).R = N.R.map (MulAut.conj s).toMonoidHom := by
  unfold NF.R
  rw [MonoidHom.map_closure]
  congr 1
  ext n
  obtain ⟨n, rfl⟩ := (MulAut.conj s).surjective n
  refine Iff.trans ?_ (Function.Injective.mem_set_image (MulAut.conj s).injective).symm
  exact and_congr (mv_inN hs N.F n) (mv_inN hs N.F' n)
end GlobalTheory.DegMove
