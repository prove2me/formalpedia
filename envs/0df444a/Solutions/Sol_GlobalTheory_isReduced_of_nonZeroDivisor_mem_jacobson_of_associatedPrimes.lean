-- Prove2me | solution 1 for GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:09.400003+00:00
-- url     : https://prove2.me/submissions/b398044a-23d9-4f15-9231-3f71dbc7a254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
import Theorems.Thm_GlobalTheory_mem_span_singleton_of_isNilpotent_of_associatedPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R →
      x ∈ Ideal.jacobson (⊥ : Ideal R) →
      (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
        IsDomain (Localization.AtPrime P)) → IsReduced R := by
  intro R _ _ x hx hj hP
  refine ⟨fun n hn => ?_⟩
  have key : ∀ k : ℕ, ∀ m : R, IsNilpotent m → m ∈ Ideal.span {x} ^ k := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      obtain ⟨m', rfl⟩ := Ideal.mem_span_singleton'.1
        (mem_span_singleton_of_isNilpotent_of_associatedPrimes x hP hm)
      have hm' : IsNilpotent m' := by
        obtain ⟨e, he⟩ := hm
        refine ⟨e, ?_⟩
        rw [mul_pow] at he
        exact (mem_nonZeroDivisors_iff_right.1 (pow_mem hx e)) _ he
      rw [pow_succ', mul_comm m' x]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih m' hm')
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (Ideal.span {x})
    ((Ideal.span_singleton_le_iff_mem _).2 hj)
  have : n ∈ (⨅ i : ℕ, (Ideal.span {x}) ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    simpa [smul_eq_mul, Ideal.mul_top] using key i n hn
  rw [hK] at this
  simpa using this
end GlobalTheory
