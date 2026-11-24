-- Prove2me | solution 1 for GlobalTheory.Idele.mem_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:20.907656+00:00
-- url     : https://prove2.me/submissions/5ab2de4b-7abc-4b34-abc4-2155a60af8eb

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
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ t • I ↔ ∃ a ∈ adelicIdeal I, (t : 𝔸ᶠ[R, K]) * a = algebraMap K 𝔸ᶠ[R, K] x := by
  rw [← algebraMap_mem_adelicIdeal (smul_ne_zero t hI)]
  constructor
  · intro h
    refine ⟨(t⁻¹ : 𝔸ᶠ[R, K]ˣ) * algebraMap K 𝔸ᶠ[R, K] x, ?_, by simp⟩
    rw [← mul_mem_adelicIdeal_smul t]
    simpa using h
  · rintro ⟨a, ha, h⟩
    rw [← h, mul_mem_adelicIdeal_smul]
    exact ha
end GlobalTheory.Idele
