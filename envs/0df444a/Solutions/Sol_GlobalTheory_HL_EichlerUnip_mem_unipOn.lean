-- Prove2me | solution 1 for GlobalTheory.HL.EichlerUnip.mem_unipOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:33:23.328978+00:00
-- url     : https://prove2.me/submissions/80f8d23a-bffc-4093-ac8e-4a1dea3d98d1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacter
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.EichlerUnip
theorem _root_.solution {N : ℕ} {A B : Submodule E (Fin N → E)} (hBA : B ≤ A)
    (n : (Fin N → E) ≃ₗ[E] (Fin N → E)) (h1 : ∀ v ∈ A, n v - v ∈ B) (h2 : ∀ v ∈ A, n⁻¹ v - v ∈ B) :
    n ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : n⁻¹ (n v) = v := n.symm_apply_apply v
    rw [h4] at h3
    simpa using h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv
end GlobalTheory.HL.EichlerUnip
