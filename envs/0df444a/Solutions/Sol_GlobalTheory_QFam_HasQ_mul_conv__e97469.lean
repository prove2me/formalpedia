-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.mul_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:27.296832+00:00
-- url     : https://prove2.me/submissions/67abf4f1-7090-4301-97a7-d44913162a1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
namespace GlobalTheory.QFam
private lemma hasSum_conv_mul_of_multiplicative {a b : ℕ → ℂ} {e : ℕ → ℂ} {x y : ℂ}
    (he : ∀ m n, e (m + n) = e m * e n)
    (ha : HasSum (fun n => a n * e n) x) (hb : HasSum (fun n => b n * e n) y) :
    HasSum (fun n => conv a b n * e n) (x * y) := by
  have hna : Summable fun n => ‖a n * e n‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun n => ‖b n * e n‖ := summable_norm_iff.mpr hb.summable
  have hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum
  convert hS using 1
  funext n
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, he]
  ring
private lemma mvExp_add_character_germs (N : ℕ) (τ : ℍ) (m n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m + n : ℕ) : ℂ) * τ / N) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / N) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / N) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
end GlobalTheory.QFam
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace HasQ
theorem _root_.solution {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) :=
  fun τ => hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)
end HasQ
end GlobalTheory.QFam
