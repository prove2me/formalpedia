-- Prove2me | solution 1 for GlobalTheory.Idele.smul_le_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:05.004773+00:00
-- url     : https://prove2.me/submissions/a4e69925-6032-457a-a6c0-3df1897a46d3

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
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : I ≤ J) :
    t • I ≤ t • J := by
  rw [smul_def, smul_def]; gcongr
end GlobalTheory.Idele
