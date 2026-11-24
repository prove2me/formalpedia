-- Prove2me | solution 1 for GlobalTheory.TargetInequalityLemmas.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:43.728658+00:00
-- url     : https://prove2.me/submissions/5633a9ff-a2cc-4e34-992a-7cefe0b87230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetInequalityLemmas
open Polynomial
namespace GlobalTheory.TargetInequalityLemmas
theorem _root_.solution {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F ({θ} : Set K)) :
    ∃ d : R, d ≠ 0 ∧ (algebraMap R K d * z) ∈ Algebra.adjoin R ({θ} : Set K) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
  simp only [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors R) p, ?_⟩
  have hmap : (IsLocalization.integerNormalization (nonZeroDivisors R) p).map (algebraMap R F)
      = C (algebraMap R F b) * p := by
    rw [hb]
    ext i
    rw [coeff_smul, coeff_C_mul, Algebra.smul_def]
  rw [← aeval_map_algebraMap F, hmap, map_mul, aeval_C, ← IsScalarTower.algebraMap_apply]
end GlobalTheory.TargetInequalityLemmas
