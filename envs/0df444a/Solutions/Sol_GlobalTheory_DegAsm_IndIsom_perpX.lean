-- Prove2me | solution 1 for GlobalTheory.DegAsm.IndIsom.perpX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:37:41.415059+00:00
-- url     : https://prove2.me/submissions/393c69cf-4296-4d17-a8d4-0db40292ce5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPair
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
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.IndIsom
variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.IndIsom
theorem _root_.solution (F : FlagD H r) {v : V} (hv : ∀ a : Fin (r + 1), H.B (F.e a) v = 0) :
    ∀ x ∈ F.X, H.B x v = 0 := by
  have h : F.X ≤ LinearMap.ker (H.B.flip v) := by
    rw [FlagD.X, FlagD.Xa, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    simpa using hv b.castSucc
  intro x hx
  simpa using h hx
end GlobalTheory.DegAsm.IndIsom
