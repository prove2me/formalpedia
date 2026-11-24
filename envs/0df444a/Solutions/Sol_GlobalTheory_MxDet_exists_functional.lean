-- Prove2me | solution 1 for GlobalTheory.MxDet.exists_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:36.562623+00:00
-- url     : https://prove2.me/submissions/cf25a3ed-9316-4a15-94b9-40031c238cc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
import Theorems.Thm_GlobalTheory_MxDet_iterD_linF_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.MxDet
namespace GlobalTheory.MxDet
theorem _root_.solution {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (linF x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_linF_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp
end GlobalTheory.MxDet
