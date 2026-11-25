-- Prove2me | solution 1 for GlobalTheory.HL.relIndex_pair_comap_of_dense_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:32.739932+00:00
-- url     : https://prove2.me/submissions/091295ca-4749-49e3-82e3-6f534c7be5a9

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IndexComapEqOfCosetsHit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexComapPairOfDenseImage
import Theorems.Thm_GlobalTheory_HL_relIndex_comap_of_dense_image

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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  intro Γ G _ _ φ K U h
  refine ⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩
  refine relIndex_comap_of_dense_image φ U K fun g hg => ?_
  obtain ⟨γ, hγ⟩ := h g (Or.inl hg)
  exact ⟨γ, by rwa [inf_comm]⟩
end GlobalTheory.HL
