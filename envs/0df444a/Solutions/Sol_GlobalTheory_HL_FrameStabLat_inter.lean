-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:08.209397+00:00
-- url     : https://prove2.me/submissions/cffe7354-7dce-48c3-8178-fd43b8b06c83

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution (A A' B : Submodule O V) (P P' W : Submodule E V) (hA : ∀ x ∈ A, x ∈ P)
    (hA' : ∀ x ∈ A', x ∈ P') (hB : ∀ x ∈ B, x ∈ W)
    (H : ∀ a ∈ P, ∀ a' ∈ P', ∀ w ∈ W, a + a' + w = 0 → a = 0 ∧ a' = 0) {x : V} (hx : x ∈ A ⊔ A' ⊔ B) :
    (x ∈ P → x ∈ A) ∧ (x ∈ P' → x ∈ A') := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 hy
  constructor
  · intro hP
    have := (H (a - (a + a' + w)) (P.sub_mem (hA a ha) hP) a' (hA' a' ha') w (hB w hw) (by abel)).1
    rw [← sub_eq_zero.1 this]; exact ha
  · intro hP
    have := (H a (hA a ha) (a' - (a + a' + w)) (P'.sub_mem (hA' a' ha') hP) w (hB w hw) (by abel)).2
    rw [← sub_eq_zero.1 this]; exact ha'
end GlobalTheory.HL.FrameStabLat
