-- Prove2me | solution 1 for GlobalTheory.Idele.exists_adele_of_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:51.18731+00:00
-- url     : https://prove2.me/submissions/61c4b91f-42db-49f4-b28e-0cc7e949b1a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_exists_smul_eq
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_exists_adele_of_end_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk

set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (ψ : (𝔸ᶠ[R, K] ⧸ adelicIdeal I) →ₗ[R] (𝔸ᶠ[R, K] ⧸ adelicIdeal J)) :
    ∃ t : 𝔸ᶠ[R, K], ∀ a, ψ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (t * a) := by
  obtain ⟨s, hs⟩ := exists_smul_eq (one_ne_zero (α := FractionalIdeal R⁰ K)) hI
  obtain ⟨u, hu⟩ := exists_smul_eq (one_ne_zero (α := FractionalIdeal R⁰ K)) hJ
  obtain ⟨t, ht⟩ := exists_adele_of_end_one
    ((adelicMulEquiv u hu).symm.toLinearMap ∘ₗ ψ ∘ₗ (adelicMulEquiv s hs).toLinearMap)
  refine ⟨u * t * (s⁻¹ : 𝔸ᶠ[R, K]ˣ), fun a => ?_⟩
  have := ht ((s⁻¹ : 𝔸ᶠ[R, K]ˣ) * a)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, adelicMulEquiv_mk,
    LinearEquiv.symm_apply_eq, Units.mul_inv_cancel_left] at this
  rw [this, mul_assoc, mul_assoc]
end GlobalTheory.Idele
