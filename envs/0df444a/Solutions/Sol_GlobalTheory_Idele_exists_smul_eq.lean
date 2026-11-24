-- Prove2me | solution 1 for GlobalTheory.Idele.exists_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:16.329485+00:00
-- url     : https://prove2.me/submissions/c8b3a12d-ad4d-40f2-bbf1-31a7f4161df9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_exists_idealOf_eq

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
theorem _root_.solution {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    ∃ t : 𝔸ᶠ[R, K]ˣ, J = t • I := by
  obtain ⟨t, ht⟩ := exists_idealOf_eq (mul_ne_zero hJ (inv_ne_zero hI))
  exact ⟨t, by rw [smul_def, ht, mul_assoc, inv_mul_cancel₀ hI, mul_one]⟩
end GlobalTheory.Idele
