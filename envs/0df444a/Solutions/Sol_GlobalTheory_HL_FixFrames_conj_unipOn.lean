-- Prove2me | solution 1 for GlobalTheory.HL.FixFrames.conj_unipOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:00:11.081336+00:00
-- url     : https://prove2.me/submissions/ce57404e-af4d-4b6d-b3b5-7afbad3d055e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFrameUnipotentExchangingDualIsotropicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryNormalisesStabil
import Theorems.Thm_GlobalTheory_HL_FixFrames_inv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FixFrames
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FixFrames
theorem _root_.solution (h : S.GLV) (A B : Submodule E S.V) (hA : ∀ v, h v ∈ A ↔ v ∈ A)
    (hB : ∀ v, h v ∈ B ↔ v ∈ B) (s : S.GLV) (hs : s ∈ unipOn A B) : h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h⁻¹ v ∈ A ↔ v ∈ A := fun v => by
    rw [← hA (h⁻¹ v), inv_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h⁻¹ v)) ∈ A ↔ v ∈ A
    rw [hA, hs.1, hA']
  · change h (s (h⁻¹ v)) - v ∈ B
    have e : h (s (h⁻¹ v)) - v = h (s (h⁻¹ v) - h⁻¹ v) := by
      rw [map_sub, inv_apply, LinearEquiv.apply_symm_apply]
    rw [e, hB]
    exact hs.2 _ ((hA' v).2 hv)
end GlobalTheory.HL.FixFrames
