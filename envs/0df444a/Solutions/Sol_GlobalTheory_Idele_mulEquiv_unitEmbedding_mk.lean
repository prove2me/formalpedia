-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_unitEmbedding_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:31.405632+00:00
-- url     : https://prove2.me/submissions/23349835-5018-4f39-9f29-08e4d62cdde8

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
theorem _root_.solution (c : Kˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = FiniteAdeleRing.unitEmbedding R K c • I) (x : K) :
    mulEquiv (FiniteAdeleRing.unitEmbedding R K c) hI h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((c : K) * x) := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  simp
end GlobalTheory.Idele
