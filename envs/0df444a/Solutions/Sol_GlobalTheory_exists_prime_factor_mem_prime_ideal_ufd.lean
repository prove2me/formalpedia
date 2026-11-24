-- Prove2me | solution 1 for GlobalTheory.exists_prime_factor_mem_prime_ideal_ufd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:51.581348+00:00
-- url     : https://prove2.me/submissions/477df74c-a85f-431e-a263-79163e7a958e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [hI : I.IsPrime] (a : R) (ha : a ≠ 0)
    (haI : a ∈ I) : ∃ u : R, Prime u ∧ u ∣ a ∧ u ∈ I := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact absurd (I.eq_top_of_isUnit_mem haI hx) hI.ne_top
  | h₃ a p ha' hp ih =>
    rcases hI.mem_or_mem haI with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨u, hu, hua, huI⟩ := ih (right_ne_zero_of_mul ha) h
      exact ⟨u, hu, dvd_mul_of_dvd_right hua _, huI⟩
end GlobalTheory
