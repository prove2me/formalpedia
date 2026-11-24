-- Prove2me | solution 1 for GlobalTheory.AdLat.linearForm_integral_of_one_tmul_mem_adelicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:30.584911+00:00
-- url     : https://prove2.me/submissions/53f9e580-e128-4221-995b-84beccee3af3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_adele_mul_integral
import Theorems.Thm_GlobalTheory_AdLat_adele_add_integral
import Theorems.Thm_GlobalTheory_AdLat_adele_neg_integral
import Theorems.Thm_GlobalTheory_AdLat_adele_zero_integral
import Theorems.Thm_GlobalTheory_AdLat_mem_range_iff_adele_integral

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
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution {I : Set E} (t : E →ₗ[F] F)
    (ht : ∀ y ∈ I, t y ∈ (algebraMap (𝓞 F) F).range) {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F I) :
    t x ∈ (algebraMap (𝓞 F) F).range := by
  let T : RA F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
    (TensorProduct.rid F _).toLinearMap ∘ₗ LinearMap.lTensor _ t
  have hT : ∀ a y, T (a ⊗ₜ[F] y) = algebraMap F _ (t y) * a := by
    intro a y
    simp [T, Algebra.smul_def]
  have key : ∀ z ∈ hat1 F I, ∀ v, T z v ∈ v.adicCompletionIntegers F := by
    intro z hz v
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [hT]
      exact adele_mul_integral F
        ((mem_range_iff_adele_integral F _).1 (ht y hy) v) (ha v)
    | zero => rw [map_zero]; exact adele_zero_integral F v
    | add y z _ _ h1 h2 => rw [map_add]; exact adele_add_integral F h1 h2
    | neg y _ h1 => rw [map_neg]; exact adele_neg_integral F h1
  rw [mem_range_iff_adele_integral]
  have := key _ hx
  rwa [hT, mul_one] at this
end GlobalTheory.AdLat
