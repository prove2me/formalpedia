-- Prove2me | solution 1 for GlobalTheory.Idele.ne_zero_of_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:32.166053+00:00
-- url     : https://prove2.me/submissions/bd55f6fd-0eed-4434-870f-871d173daf4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
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
    (φ : (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K))) : J ≠ 0 := by
  rintro rfl
  obtain ⟨q, hq⟩ := φ.surjective (Submodule.Quotient.mk 1)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  obtain ⟨r, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap R K b ≠ 0 := by simpa using hb0
  have h0 : (b * c) • (Submodule.Quotient.mk (algebraMap R K r / algebraMap R K b) :
      K ⧸ (I : Submodule R K)) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    convert (I : Submodule R K).smul_mem r hc using 1
    simp only [Algebra.smul_def, map_mul]
    field_simp
  have h1 := congrArg φ h0
  rw [map_smul, hq, map_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_zero_iff] at h1
  simp [Algebra.smul_def, hb0, hc0] at h1
end GlobalTheory.Idele
