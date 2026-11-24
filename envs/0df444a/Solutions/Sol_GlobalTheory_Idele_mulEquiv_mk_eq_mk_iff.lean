-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:12.731381+00:00
-- url     : https://prove2.me/submissions/aa33fbcf-ca23-4bd8-9bbd-e2cc14408094

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_eq_mk_iff_adelic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
      ∀ v : HeightOneSpectrum R, (t : 𝔸ᶠ[R, K]) v * algebraMap K (v.adicCompletion K) x -
        algebraMap K (v.adicCompletion K) y ∈ localIdeal v J :=
  mulEquiv_mk_eq_mk_iff_adelic t hI h x y
end GlobalTheory.Idele
