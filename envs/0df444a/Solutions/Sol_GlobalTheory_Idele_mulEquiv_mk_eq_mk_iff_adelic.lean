-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff_adelic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:45.988618+00:00
-- url     : https://prove2.me/submissions/58b142b7-d1dd-4220-a900-820b1b0dc8ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_quotEquivAdelic_mulEquiv
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
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (x y : K) :
    mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      (t : 𝔸ᶠ[R, K]) * algebraMap K _ x - algebraMap K _ y ∈ adelicIdeal J := by
  have hJ : J ≠ 0 := h ▸ smul_ne_zero t hI
  rw [← (quotEquivAdelic hJ).injective.eq_iff, quotEquivAdelic_mulEquiv, quotEquivAdelic_mk,
    quotEquivAdelic_mk, adelicMulEquiv_mk, Submodule.Quotient.eq]
end GlobalTheory.Idele
