-- Prove2me | solution 1 for GlobalTheory.HL.MoveWit.isSD_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:28.202492+00:00
-- url     : https://prove2.me/submissions/5000abf9-2d14-4014-b44c-68f22f7bdc05

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_HL_MoveWit_mem_smul
import Theorems.Thm_GlobalTheory_HL_MoveWit_inv_app
import Theorems.Thm_GlobalTheory_HL_MoveWit_app_inv
import Theorems.Thm_GlobalTheory_HL_TermBasic_mem_smul


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveWit
theorem _root_.solution {g : S.GLV} (hg : g ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (h : IsSD L S.Hm Λ) :
    IsSD L S.Hm (g • Λ) := by
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · exact h.1.1.map _
  · rw [eq_top_iff]
    intro v _
    have h1 : g⁻¹ v ∈ Submodule.span E (Λ : Set S.V) := by rw [h.1.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : S.V →ₗ[E] S.V) h1
    have h3 : (g : S.V →ₗ[E] S.V) (g⁻¹ v) = v := app_inv S g v
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_smul S g Λ _).2 (by
      have : g⁻¹ ((g : S.V →ₗ[E] S.V) w) = w := inv_app S g w
      rw [this]; exact hw)
  · rw [mem_smul, ← h.2]
    constructor
    · intro H x hx
      have := H (g x) ((mem_smul S g Λ _).2 (by rwa [inv_app]))
      rwa [← app_inv S g y, hg] at this
    · intro H x hx
      have := H _ ((mem_smul S g Λ _).1 hx)
      rwa [(isomG L S.Hm).inv_mem hg] at this
end GlobalTheory.HL.MoveWit
