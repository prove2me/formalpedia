-- Prove2me | solution 1 for GlobalTheory.Idele.smul_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:06.855819+00:00
-- url     : https://prove2.me/submissions/c4f050d1-bee2-424e-90b5-85e2079fe8d5

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
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    t • I = I ↔ ∀ v, Valued.v ((t : 𝔸ᶠ[R, K]) v) = 1 := by
  constructor
  · intro h v
    have := count_smul t hI v
    rw [h] at this
    rw [valued_idele, show ord_vw t v = 0 by omega]
    simp
  · intro h
    refine eq_of_count_eq (smul_ne_zero t hI) hI fun v => ?_
    rw [count_smul t hI, ord_vw, h v]
    simp
end GlobalTheory.Idele
