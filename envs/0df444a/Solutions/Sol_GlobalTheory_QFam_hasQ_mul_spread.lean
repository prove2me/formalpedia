-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_mul_spread
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:29.988938+00:00
-- url     : https://prove2.me/submissions/12707322-76e4-481f-a88f-65ab83efe6ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulLevelSubstPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution : ∀ (N M : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → 0 < M → HasQ N f a →
    HasQ (N * M) f (spread M a) := by
  intro N M f a hN hM h τ
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hinj : Function.Injective (fun k : ℕ => M * k) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hM hxy
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro n hn
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hn ⟨k, rfl⟩
  · convert h τ using 1
    funext k
    simp only [Function.comp, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left k hM]
    congr 2
    push_cast
    field_simp
end GlobalTheory.QFam
