-- Prove2me | solution 1 for GlobalTheory.T.relIndex_comap_pair_of_dense_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:52.611815+00:00
-- url     : https://prove2.me/submissions/762d3a21-50d4-47ec-ac77-1895017a082c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexComapPairOfDenseImage
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexComapPairOfDenseImageStatement
import Theorems.Thm_GlobalTheory_HL_relIndex_pair_comap_of_dense_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  first | exact @GlobalTheory.HL.relIndex_pair_comap_of_dense_image | exact GlobalTheory.HL.relIndex_pair_comap_of_dense_image | (intros; apply GlobalTheory.HL.relIndex_pair_comap_of_dense_image <;> assumption)
end _root_.GlobalTheory.T
