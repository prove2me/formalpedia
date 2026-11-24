-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.hilbert90_matrix_subalgebra_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:58.477048+00:00
-- url     : https://prove2.me/submissions/65f118b5-0690-4c18-a14b-eec96018b66c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
import Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
variable {F : Type} [Field F] [Algebra F E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) (u : E) (hu : u * c u = 1) :
    ∃ α : 𝓞 E, α ≠ 0 ∧ u * c α = α := by
  have h0 : ∃ x : E, x ≠ 0 ∧ u * c x = x := by
    have key : ∀ θ : E, u * c (θ + u * c θ) = θ + u * c θ := by
      intro θ
      rw [map_add, map_mul, hc]
      linear_combination θ * hu
    by_cases h : 1 + u * c 1 = 0
    · have : ∃ θ, c θ ≠ θ := by
        by_contra hh
        push Not at hh
        exact hc1 (AlgEquiv.ext hh)
      obtain ⟨θ, hθ⟩ := this
      refine ⟨_, ?_, key θ⟩
      rw [map_one] at h
      intro h2
      apply hθ
      linear_combination c θ * h - h2
    · exact ⟨_, h, key 1⟩
  obtain ⟨x, hx, hux⟩ := h0
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  obtain ⟨q', hq'⟩ := exists_conj c q
  have hq0 : (q : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hq
    exact_mod_cast this
  have hp : (p : E) = x * q := by
    rw [← hpq]; exact (div_mul_cancel₀ _ hq0).symm
  have e : ((p * q' : 𝓞 E) : E) = x * q * c q := by
    rw [← hp, ← hq']; rfl
  refine ⟨p * q', ?_, ?_⟩
  · intro h
    rw [h] at e
    have hcq : c q ≠ 0 := by simpa using hq0
    exact mul_ne_zero (mul_ne_zero hx hq0) hcq (e.symm.trans rfl)
  · rw [e, map_mul, map_mul, hc]
    linear_combination (c q * q) * hux
end GlobalTheory.UnRep.NormOne
