-- Prove2me | solution 1 for GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:39:27.964857+00:00
-- url     : https://prove2.me/submissions/439adf1b-cbb3-4fb2-8ec6-643ef3d35b6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_galoisAut_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletion_fractionalIdeal_iff
import Theorems.Thm_GlobalTheory_AdLat_mem_adelicCompletion_mul_inv_fractionalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  intro F E _ _ _ _ _
  exact ⟨fun I J x hx y hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
      (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) hx hy,
    one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, mem_adelicCompletion_mul_inv_fractionalIdeal F, fun c I I' h z hz => galoisAut_mem_adelicCompletionOfElementSet F c h hz⟩
end GlobalTheory.AdLat
