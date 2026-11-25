-- Prove2me | solution 1 for GlobalTheory.HL.ComplAct.isSD_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:58:59.624213+00:00
-- url     : https://prove2.me/submissions/efe82c99-f125-4811-8dc1-709fb457fbcf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTerms
import Theorems.Thm_GlobalTheory_HL_ComplAct_mem_smul

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ComplAct
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.ComplAct
theorem _root_.solution {h : S.GLV} (hh : h ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) :
    IsSD L S.Hm (h • Λ) := by
  refine ⟨⟨hΛ.1.1.map _, ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have h1 : h⁻¹ x ∈ Submodule.span E (Λ : Set S.V) := by rw [hΛ.1.2]; trivial
    have h2 := Submodule.mem_map_of_mem (f := h.toLinearMap) h1
    rw [Submodule.map_span] at h2
    have h3 : h.toLinearMap (h⁻¹ x) = x := h.apply_symm_apply x
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem_pointwise_smul y h Λ hy
  · rw [mem_smul, ← hΛ.2]
    have hi := (isomG L S.Hm).inv_mem hh
    constructor
    · intro H x hx
      have := H (h x) (Submodule.smul_mem_pointwise_smul x h Λ hx)
      rw [← hi] at this
      have h3 : h⁻¹ (h x) = x := h.symm_apply_apply x
      rwa [h3] at this
    · intro H x hx
      rw [← hi]
      exact H _ ((mem_smul S h Λ x).1 hx)
end GlobalTheory.HL.ComplAct
