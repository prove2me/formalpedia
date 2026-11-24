-- Prove2me | solution 1 for GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:21.97281+00:00
-- url     : https://prove2.me/submissions/c3864788-d9c2-499d-b671-76a9e761c962

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_linearForm_integral_of_one_tmul_mem_adelicCompletion

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
theorem _root_.solution (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I := by
  refine ⟨fun hx => ?_, fun hx => one_tmul_mem_adelicCompletionOfElementSet F hx⟩
  by_cases hI : I = 0
  · subst hI
    rw [FractionalIdeal.mem_zero_iff]
    by_contra h0
    obtain ⟨t, ht⟩ := Module.Projective.exists_dual_eq_one F h0
    apply RingOfIntegers.not_isField F
    rw [← IsFractionRing.surjective_iff_isField (K := F)]
    intro c
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (c • t) (fun y hy => by
      have hy' : y = 0 := (FractionalIdeal.mem_zero_iff _).1 hy
      rw [hy', map_zero]; exact zero_mem _) hx
    simpa [ht] using this
  · rw [← FractionalIdeal.dual_dual (𝓞 F) F I,
      FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero _ _ hI)]
    intro y hy
    rw [FractionalIdeal.mem_dual hI] at hy
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (Algebra.traceForm F E y) hy hx
    rwa [Algebra.traceForm_apply, mul_comm] at this
end GlobalTheory.AdLat
