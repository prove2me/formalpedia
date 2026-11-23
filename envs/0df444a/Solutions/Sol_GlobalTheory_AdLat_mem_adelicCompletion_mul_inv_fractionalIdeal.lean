-- Prove2me | solution 1 for GlobalTheory.AdLat.mem_adelicCompletion_mul_inv_fractionalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.993101+00:00
-- url     : https://prove2.me/submissions/2bc8c257-d613-4283-9c06-044d7c6b08c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem

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
variable [NumberField E]
namespace GlobalTheory.AdLat
theorem _root_.solution (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E) (hI : I ≠ 0)
    (h : ∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) :
    z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  have key : ∀ w ∈ I * I⁻¹, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] w) ∈
      hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro w hw
    refine FractionalIdeal.mul_induction_on hw (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (K := ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
        (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) (h x hx) (one_tmul_mem_adelicCompletionOfElementSet F hy)
      rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    · rw [TensorProduct.tmul_add, mul_add]; exact add_mem hx hy
  have := key 1 h1
  rwa [← Algebra.TensorProduct.one_def, mul_one] at this
end GlobalTheory.AdLat
