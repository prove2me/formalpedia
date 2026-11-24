-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.eq_zero_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:23.300909+00:00
-- url     : https://prove2.me/submissions/0890b570-1ad9-49fb-8426-5b7d80df3c19

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_Inh_CharId_IsPolyFun_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CharId
open Polynomial Formalism.REAL
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace GlobalTheory.CompanionTheory.Inh.CharId
theorem _root_.solution (P : B[X]) (h : ∀ u : ℂ, P.eval (algebraMap ℂ B u) = 0) : P = 0 := by
  ext k
  rw [coeff_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  let q : ℂ[X] := ∑ i ∈ P.support, monomial i (ℓ (P.coeff i))
  have hq : q = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg ℓ (h u)
    rw [eval_eq_sum, Polynomial.sum, map_sum, map_zero] at this
    rw [eval_zero, ← this, eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, eval_monomial, smul_eq_mul,
      mul_comm]
  have hk := congrArg (fun r => r.coeff k) hq
  simp only [q, finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq'] at hk
  by_cases hs : k ∈ P.support
  · simpa [hs] using hk
  · simp [notMem_support_iff.mp hs]
end GlobalTheory.CompanionTheory.Inh.CharId
