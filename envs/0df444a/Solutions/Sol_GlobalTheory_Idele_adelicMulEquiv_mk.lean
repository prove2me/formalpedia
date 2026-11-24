-- Prove2me | solution 1 for GlobalTheory.Idele.adelicMulEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:12.338286+00:00
-- url     : https://prove2.me/submissions/66405235-e0ff-4d22-8344-d79762569eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal

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
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : J = t • I)
    (a : 𝔸ᶠ[R, K]) :
    adelicMulEquiv t h (Submodule.Quotient.mk a) = Submodule.Quotient.mk ((t : 𝔸ᶠ[R, K]) * a) :=
  rfl
end GlobalTheory.Idele
