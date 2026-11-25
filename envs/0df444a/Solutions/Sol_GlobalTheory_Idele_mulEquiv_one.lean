-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:59.677172+00:00
-- url     : https://prove2.me/submissions/3bb19641-61c2-4b04-b63a-7bd8f6e2f553

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_eq_mk_iff_adelic
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
theorem _root_.solution {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (h : I = (1 : 𝔸ᶠ[R, K]ˣ) • I) :
    mulEquiv 1 hI h = LinearEquiv.refl R _ := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearEquiv.refl_apply, mulEquiv_mk_eq_mk_iff_adelic]
  simp
end GlobalTheory.Idele
