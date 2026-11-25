-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.Hyp.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:22:45.271947+00:00
-- url     : https://prove2.me/submissions/bb81456e-469d-433f-88f3-bc935f05ddf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_swap_zero
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_ye
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameMove
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.FrameMove
namespace Hyp
theorem _root_.solution {e y : Fin r → V} (h : Hyp H e y) (s t s' t' : Fin r → K) {n n' : V}
    (h1 : ∀ a, H.B n (e a) = 0) (h2 : ∀ a, H.B n (y a) = 0) (h3 : ∀ a, H.B n' (e a) = 0) (h4 : ∀ a, H.B n' (y a) = 0) :
    H.B (∑ a, s a • e a + ∑ a, t a • y a + n) (∑ a, s' a • e a + ∑ a, t' a • y a + n') =
      ∑ a, s a * star (t' a) + ∑ a, t a * star (s' a) + H.B n n' := by
  have h3' := fun a => swap_zero (h3 a)
  have h4' := fun a => swap_zero (h4 a)
  simp [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, h.1, h.2.1, h.2.2, h.ye, h1, h2, h3', h4', mul_comm]
  exact add_comm _ _
end Hyp
end GlobalTheory.DegAsm.FrameMove
