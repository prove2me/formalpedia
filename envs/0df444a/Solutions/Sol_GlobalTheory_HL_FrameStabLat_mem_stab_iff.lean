-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.mem_stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:53.253859+00:00
-- url     : https://prove2.me/submissions/15ae7f40-6bd5-4e2e-ab79-bd9ac1ee82a1

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
theorem _root_.solution (Λ : Submodule O V) (h : V ≃ₗ[E] V) :
    h ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ↔ (∀ v ∈ Λ, h v ∈ Λ) ∧ ∀ v ∈ Λ, h⁻¹ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro H
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [← H]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨v, hv, rfl⟩
    · rw [← H] at hv
      obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
      have : h⁻¹ (h • u) = u := h.symm_apply_apply u
      rwa [this]
  · rintro ⟨H1, H2⟩
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact H1 u hu
    · intro hv
      exact ⟨h⁻¹ v, H2 v hv, h.apply_symm_apply v⟩
end GlobalTheory.HL.FrameStabLat
