-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.self_mem_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:00.127805+00:00
-- url     : https://prove2.me/submissions/99e545d5-dc15-41b4-a3fd-a7ecd278497c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution (S : Frames L r k) (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have one : ∀ i j, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  refine ⟨1, 1, one, one, fun i j hij => ?_, fun i => ?_, fun i j => ⟨0, L.O.zero_mem, by simp⟩,
    fun j => ?_, fun j => ?_⟩
  · simp [Matrix.one_apply_ne hij.ne']
  · simp
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]
end GlobalTheory.HL.FrameStabLat
