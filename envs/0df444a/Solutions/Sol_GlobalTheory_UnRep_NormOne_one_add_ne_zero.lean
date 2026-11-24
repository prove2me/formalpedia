-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.one_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:59.422801+00:00
-- url     : https://prove2.me/submissions/71783ba8-b513-4bef-8b72-29c7b7545940

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (N : ℕ) (hN : N ≠ 1) (z : 𝓞 E) : 1 + (N : 𝓞 E) * z ≠ 0 := by
  intro h
  have hu : IsUnit (N : 𝓞 E) := IsUnit.of_mul_eq_one (-z) (by linear_combination -h)
  have h2 := hu.map (Algebra.norm ℤ)
  have h3 : (N : 𝓞 E) = algebraMap ℤ (𝓞 E) (N : ℤ) := by simp
  rw [h3, Algebra.norm_algebraMap, isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne',
    Int.isUnit_iff] at h2
  omega
end GlobalTheory.UnRep.NormOne
