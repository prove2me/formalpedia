-- Prove2me | solution 1 for GlobalTheory.Idele.eq_zero_of_forall_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:44.652662+00:00
-- url     : https://prove2.me/submissions/5fae47b0-80d7-4971-9475-bcddbad41518

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
theorem _root_.solution {J : FractionalIdeal R⁰ K} (hJ : J ≠ 0) {t : 𝔸ᶠ[R, K]}
    (h : ∀ x : K, t * algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal J) : t = 0 := by
  ext1 v
  by_contra hv
  have hv' : Valued.v (t v) ≠ 0 := by simpa using hv
  obtain ⟨x, hx⟩ := v.valuation_surjective K
    (exp (1 - FractionalIdeal.count K v J - log (Valued.v (t v))))
  have := (mem_adelicIdeal_iff hJ).1 (h x) v
  rw [adele_mul_apply, adele_algebraMap_apply, map_mul, valued_algebraMap, hx,
    ← exp_log hv', ← exp_add, exp_le_exp, log_exp] at this
  omega
end GlobalTheory.Idele
