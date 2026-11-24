-- Prove2me | solution 1 for GlobalTheory.GroupAlg.formallyUnramified_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:06:31.492815+00:00
-- url     : https://prove2.me/submissions/d771f5d7-8cd4-4ea1-ac19-cc0b722bd1b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution (n : ℕ) (hn : IsUnit (n : R)) (hX : ∀ x : X, n • x = 0) :
    Algebra.FormallyUnramified R R[X] := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g h
  ext x
  have hB : IsUnit (n : B) := by simpa using hn.map (algebraMap R B)
  have hfg : f (single x 1) - g (single x 1) ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun h (single x 1)
  have hp : ∀ k : R[X] →ₐ[R] B, k (single x 1) ^ n = 1 := fun k => by
    rw [← map_pow, single_pow, hX, one_pow, ← one_def, map_one]
  set a := f (single x 1)
  set b := g (single x 1)
  have hi : (a - b) * (a - b) = 0 := by
    have := Ideal.mul_mem_mul hfg hfg
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have key : ∀ m : ℕ, b * a ^ m = b ^ (m + 1) + m * b ^ m * (a - b) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ a, ← mul_assoc, ih]
      push_cast
      linear_combination (m * b ^ m) * hi
  have h3 := key n
  rw [pow_succ b, hp f, hp g] at h3
  have h4 : (n : B) * (a - b) = 0 := by linear_combination -h3
  have h5 : a - b = 0 := (hB.mul_right_eq_zero).1 h4
  exact sub_eq_zero.1 h5
end GlobalTheory.GroupAlg
