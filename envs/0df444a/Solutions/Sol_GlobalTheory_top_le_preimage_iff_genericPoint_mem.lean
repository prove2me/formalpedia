-- Prove2me | solution 1 for GlobalTheory.top_le_preimage_iff_genericPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:16:49.323843+00:00
-- url     : https://prove2.me/submissions/c276c476-56c9-4faa-9983-f1e523caf1c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y
namespace GlobalTheory
theorem _root_.solution {O K : Type} [CommRing O] [IsDomain O] [Field K]
    [Algebra O K] [FaithfulSMul O K] {Z : Scheme.{0}} (y : Spec (.of O) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ y) ⁻¹ᵁ U ↔ y (genericPoint _) ∈ U := by
  have key : ∀ q : Spec (.of K), (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ y) q =
      y (genericPoint _) := fun q => by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_bot_of_affine]
    refine congrArg y (PrimeSpectrum.ext ?_)
    rw [Subsingleton.elim q (⊥ : PrimeSpectrum K)]
    exact Ideal.comap_bot_of_injective (algebraMap O K) (FaithfulSMul.algebraMap_injective O K)
  refine ⟨fun h => ?_, fun h q _ => ?_⟩
  · rw [← key (⊥ : PrimeSpectrum K)]
    exact h (Set.mem_univ _)
  · rw [← key q] at h
    exact h
end GlobalTheory
