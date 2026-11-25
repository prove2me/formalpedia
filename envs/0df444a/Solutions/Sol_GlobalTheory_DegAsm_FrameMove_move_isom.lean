-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.move_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:25.300185+00:00
-- url     : https://prove2.me/submissions/9aa4c10b-99da-4f52-a436-3be2b3f309f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_swap_zero
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_pair
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_mid_apply
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_mid_e
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_mid_y
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_move_apply
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_perp_of_span
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
theorem _root_.solution {e y e' y' : Fin r → V} (h : Hyp H e y) (h' : Hyp H e' y')
    (hs : ∀ a, e' a ∈ Submodule.span K (Set.range e)) (v w : V) :
    H.B (move H e y e' y' v) (move H e y e' y' w) = H.B v w := by
  have hd : ∀ u : V, u = ∑ a, H.B u (y a) • e a + ∑ a, H.B u (e a) • y a + mid H e y u := fun u => by
    rw [mid_apply]; abel
  have hp : ∀ u a, H.B (mid H e y u) (e' a) = 0 := fun u a => perp_of_span (h.mid_e u) (hs a)
  have hp' : ∀ u a, H.B (e' a) (mid H e y u) = 0 := fun u a => swap_zero (hp u a)
  have hm : H.B (mid H e' y' (mid H e y v)) (mid H e' y' (mid H e y w)) = H.B (mid H e y v) (mid H e y w) := by
    rw [mid_apply e' y' (mid H e y w)]
    simp only [map_sub, map_sum, LinearMap.map_smulₛₗ, h'.mid_e, h'.mid_y, smul_zero, Finset.sum_const_zero, sub_zero]
    rw [mid_apply e' y' (mid H e y v)]
    simp [hp, hp']
  rw [move_apply, move_apply, h'.pair _ _ _ _ (h'.mid_e _) (h'.mid_y _) (h'.mid_e _) (h'.mid_y _), hm]
  conv_rhs => rw [hd v, hd w]
  rw [h.pair _ _ _ _ (h.mid_e _) (h.mid_y _) (h.mid_e _) (h.mid_y _)]
end GlobalTheory.DegAsm.FrameMove
