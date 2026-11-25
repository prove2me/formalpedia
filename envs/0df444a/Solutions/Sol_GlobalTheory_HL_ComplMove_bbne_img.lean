-- Prove2me | solution 1 for GlobalTheory.HL.ComplMove.bbne_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:42.901717+00:00
-- url     : https://prove2.me/submissions/acf2faa9-0904-4b3f-a002-5d60eb6a936a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryComplementMovesHermitianTerms
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplMove
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
namespace GlobalTheory.HL.ComplMove
theorem _root_.solution (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by
  have hfam : ∀ i, g (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i := by
    intro i
    unfold HermSp.MMfam
    rcases hs : M.split with _ | gg <;> rcases i with i | i <;>
      simp [map_smul, map_sub, (hfix i).1, (hfix i).2]
  have hspan : ∀ v ∈ Submodule.span E (Set.range (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r))), g v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfam i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul s x _ hx => rw [map_smul, hx]
  have e : H.MMfam (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) := rfl
  unfold LocNG.BBne
  simp only [e]
  constructor
  · rintro ⟨v, hv, hs, hns⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have ew : g w = w := g.injective (hspan _ hs)
    change g w ∈ _ at hs
    change g w ∉ _ at hns
    rw [ew] at hs hns
    exact ⟨w, hw, hs, hns⟩
  · rintro ⟨v, hv, hs, hns⟩
    exact ⟨v, Submodule.mem_map.2 ⟨v, hv, hspan v hs⟩, hs, hns⟩
end GlobalTheory.HL.ComplMove
