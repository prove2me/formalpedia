-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:22.310963+00:00
-- url     : https://prove2.me/submissions/b456c57e-a15c-4625-b6d2-0dd53331b15f

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
theorem _root_.solution (t s : 𝔸ᶠ[R, K]ˣ) {I J L : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : J = s • I) (h' : L = t • J) (h'' : L = (t * s) • I) :
    mulEquiv (t * s) hI h'' = (mulEquiv s hI h).trans (mulEquiv t hJ h') := by
  have hL : L ≠ 0 := h' ▸ smul_ne_zero t hJ
  refine LinearEquiv.ext fun q => (quotEquivAdelic hL).injective ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearEquiv.trans_apply, quotEquivAdelic_mulEquiv, quotEquivAdelic_mulEquiv,
    quotEquivAdelic_mulEquiv]
  simp [mul_assoc]
end GlobalTheory.Idele
