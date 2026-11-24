-- Prove2me | solution 1 for GlobalTheory.Idele.exists_exp_neg_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:17.949688+00:00
-- url     : https://prove2.me/submissions/d080c751-e120-48f4-b4df-fedf7845b7ae

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
theorem _root_.solution {γ : ℤᵐ⁰} (hγ : γ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < γ := by
  refine ⟨(log γ).natAbs + 1, ?_⟩
  conv_rhs => rw [← exp_log hγ]
  rw [exp_lt_exp]
  omega
end GlobalTheory.Idele
