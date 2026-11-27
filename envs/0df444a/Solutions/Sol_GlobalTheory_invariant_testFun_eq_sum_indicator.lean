-- Prove2me | solution 1 for GlobalTheory.invariant_testFun_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:25.466384+00:00
-- url     : https://prove2.me/submissions/e53c8511-9959-48f5-a6f6-0a0a1a5b6d11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_exists_eq_sum_indicator_of_right_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open LatticeIndicator
namespace GlobalTheory
theorem _root_.solution {O K : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) {M n : ℕ} (N : ℕ)
    (φ : Matrix (Fin M) (Fin n) K → ℂ)
    (hinv : ∀ (x : Matrix (Fin M) (Fin n) K) (k : GL (Fin n) O),
      φ (x * (k : Matrix (Fin n) (Fin n) O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix (Fin M) (Fin n) K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K ϖ ^ N • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix (Fin M) (Fin n) K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K ϖ ^ N • y) = φ x) :
    ∃ (r : ℕ) (h : Fin r → GL (Fin M) K) (c : Fin r → ℂ), ∀ x : Matrix (Fin M) (Fin n) K,
      φ x = ∑ l, c l * Set.indicator
        {y : Matrix (Fin M) (Fin n) K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 ((((h l)⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K) * x) :=
  exists_eq_sum_indicator_of_right_invariant (pow_ne_zero N hϖ.ne_zero) (pow_ne_zero N hϖ.ne_zero)
    φ hinv (by simpa only [map_pow] using hsupp) (by simpa only [map_pow] using hper)
end GlobalTheory
