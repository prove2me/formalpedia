-- Prove2me | solution 1 for GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:25.051563+00:00
-- url     : https://prove2.me/submissions/50390d37-de07-4d5e-93c5-3e40d5bd2a1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree (𝓞 E) N := by
  refine Module.IsTorsionFree.of_smul_eq_zero (fun c x hcx => ?_)
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have halg : IsAlgebraic ℤ c := (Algebra.IsIntegral.isIntegral (R := ℤ) c).isAlgebraic
    obtain ⟨m, hm, d, hd⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)
    have h1 : m • x = 0 := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E)]
      have : ((m : ℤ) : 𝓞 E) = d * c := by
        rw [mul_comm, ← hd]; simp
      rw [this, mul_smul, hcx, smul_zero]
    exact (smul_eq_zero.mp h1).resolve_left hm
end GlobalTheory
