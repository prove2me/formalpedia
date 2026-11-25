-- Prove2me | solution 1 for GlobalTheory.InvH.conj_unipOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:48:57.536826+00:00
-- url     : https://prove2.me/submissions/c4929023-81df-44c4-b912-3765cd4b7fe4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumOrbitNormaliser
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
open GlobalTheory GlobalTheory.InvH
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.InvH
theorem _root_.solution {n : ℕ} {A B : Submodule E (Fin n → E)} {h s : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (hs : s ∈ unipOn A B) :
    h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h.symm v ∈ A ↔ v ∈ A := fun v => by rw [← hA]; simp
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h.symm v)) ∈ A ↔ _
    rw [hA, hs.1, hA']
  · have := (hB _).2 (hs.2 _ ((hA' v).2 hv))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
end GlobalTheory.InvH
