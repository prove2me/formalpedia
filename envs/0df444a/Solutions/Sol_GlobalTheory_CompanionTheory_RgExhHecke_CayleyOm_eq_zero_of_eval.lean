-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.eq_zero_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:57.525833+00:00
-- url     : https://prove2.me/submissions/d2495e1e-e120-48de-94ef-2dd1714472e2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
theorem _root_.solution (R : A[X]) (h : ∀ y : ℂ, R.eval (algebraMap ℂ A y) = 0) : R = 0 := by
  ext k
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  let r : ℂ[X] := ∑ i ∈ R.support, monomial i (φ (R.coeff i))
  have hr : ∀ y, r.eval y = 0 := by
    intro y
    have hy := congrArg φ (h y)
    rw [eval_eq_sum, sum_def, map_sum, map_zero] at hy
    rw [← hy]
    simp only [r, eval_finsetSum, eval_monomial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have h0 : r = 0 := Polynomial.funext (by simpa using hr)
  have hc : r.coeff k = φ (R.coeff k) := by
    simp only [r, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
    by_cases hk : R.coeff k = 0 <;> simp [hk]
  rw [← hc, h0, coeff_zero]
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
