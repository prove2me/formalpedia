-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:04.640803+00:00
-- url     : https://prove2.me/submissions/69f9b27e-7e7a-489e-8463-36ae3e92df8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_quotEquivAdelic_mulEquiv
import Theorems.Thm_GlobalTheory_Idele_existsUnique_adele_of_linearMap
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
theorem _root_.solution {t s : 𝔸ᶠ[R, K]ˣ} {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (h' : J = s • I) (e : mulEquiv t hI h = mulEquiv s hI h') : t = s := by
  have hJ : J ≠ 0 := h ▸ smul_ne_zero t hI
  refine Units.ext ((existsUnique_adele_of_linearMap hI hJ (mulEquiv t hI h).toLinearMap).unique
    (fun x => ?_) fun x => ?_)
  · simp [quotEquivAdelic_mulEquiv]
  · simp [e, quotEquivAdelic_mulEquiv]
end GlobalTheory.Idele
