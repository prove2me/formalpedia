-- Prove2me | solution 1 for GlobalTheory.Idele.existsUnique_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:31.583985+00:00
-- url     : https://prove2.me/submissions/dcdc0506-9879-4be9-85bf-1f94c792880e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_quotEquivAdelic_mulEquiv
import Theorems.Thm_GlobalTheory_Idele_exists_adele_of_linearMap
import Theorems.Thm_GlobalTheory_Idele_eq_zero_of_forall_mul_mem
import Theorems.Thm_GlobalTheory_Idele_mulEquiv_injective
import Theorems.Thm_GlobalTheory_Idele_ne_zero_of_linearEquiv
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
theorem _root_.solution {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K))) :
    ∃! t : 𝔸ᶠ[R, K]ˣ, ∃ h : J = t • I, φ = mulEquiv t hI h := by
  have hJ : J ≠ 0 := ne_zero_of_linearEquiv hI φ
  let ψ := (quotEquivAdelic hI).symm.trans (φ.trans (quotEquivAdelic hJ))
  obtain ⟨t, ht⟩ := exists_adele_of_linearMap hI hJ ψ.toLinearMap
  obtain ⟨s, hs⟩ := exists_adele_of_linearMap hJ hI ψ.symm.toLinearMap
  simp only [LinearEquiv.coe_coe] at ht hs
  have hst : s * t = 1 := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mul_mem hI fun x => ?_
    rw [sub_mul, ← Submodule.Quotient.eq, mul_assoc, ← hs, ← ht, LinearEquiv.symm_apply_apply,
      one_mul]
  let u : 𝔸ᶠ[R, K]ˣ := ⟨t, s, by rw [mul_comm, hst], hst⟩
  have hu : J = u • I := by
    ext x
    rw [← algebraMap_mem_adelicIdeal hJ, ← algebraMap_mem_adelicIdeal (smul_ne_zero u hI),
      ← Units.mul_inv_cancel_left u (algebraMap K 𝔸ᶠ[R, K] x), mul_mem_adelicIdeal_smul,
      ← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero]
    exact (ht _) ▸ ψ.map_eq_zero_iff
  have hφ : φ = mulEquiv u hI hu := by
    refine LinearEquiv.ext fun q => (quotEquivAdelic hJ).injective ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [quotEquivAdelic_mulEquiv, quotEquivAdelic_mk, adelicMulEquiv_mk]
    refine Eq.trans ?_ (ht _)
    rw [← quotEquivAdelic_mk hI]
    simp only [ψ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  refine ⟨u, ⟨hu, hφ⟩, ?_⟩
  rintro u' ⟨hu', hφ'⟩
  exact mulEquiv_injective hI hu' hu (hφ'.symm.trans hφ)
end GlobalTheory.Idele
