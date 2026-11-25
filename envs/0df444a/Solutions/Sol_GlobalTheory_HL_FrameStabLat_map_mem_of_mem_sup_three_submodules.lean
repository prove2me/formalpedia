-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.map_mem_of_mem_sup_three_submodules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:14.888083+00:00
-- url     : https://prove2.me/submissions/5203859f-aa32-4e26-b23a-2bcbb3b29779

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
theorem _root_.solution (A A' B Λ : Submodule O V) (h : V ≃ₗ[E] V) (H1 : ∀ x ∈ A, h x ∈ Λ)
    (H2 : ∀ x ∈ A', h x ∈ Λ) (H3 : ∀ x ∈ B, h x ∈ Λ) : ∀ x ∈ A ⊔ A' ⊔ B, h x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, map_add]
  exact Λ.add_mem (Λ.add_mem (H1 a ha) (H2 a' ha')) (H3 w hw)
end GlobalTheory.HL.FrameStabLat
