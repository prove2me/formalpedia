-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.mem_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:16.552056+00:00
-- url     : https://prove2.me/submissions/74b6e19a-e91e-4475-910c-17e60ef789b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_xa_eq
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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.FrameMove
theorem _root_.solution {F G : FlagD H r} (h : SameGr F G) {Λ : Submodule (𝓞 K) V} (a : Fin (r + 1)) {t : K} {x : V}
    (hx : x ∈ Λ) (ht : x - t • G.e a ∈ G.Xa a.val) : t ∈ lead F Λ a := by
  rw [AdaptInv.xa_eq h] at ht
  have h1 : t • F.e a - x ∈ F.Xa a.val := by
    have := Submodule.neg_mem _ (Submodule.add_mem _ ht (Submodule.smul_mem _ t (h a)))
    convert this using 1
    rw [smul_sub]; abel
  have h2 : x + (t • F.e a - x) ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val) := Submodule.add_mem_sup hx h1
  simpa [lead] using h2
end GlobalTheory.DegAsm.FrameMove
