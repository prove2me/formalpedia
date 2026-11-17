-- Prove2me | solution 1 for N25.kummer_at_five_is_coboundary_of_N5Surj
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:43.696202+00:00
-- url     : https://prove2.me/submissions/6fe753b1-be72-4efc-9364-c9b63d55344a

import Mathlib
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_N25_pi5_bijective_of_N5Surj

noncomputable section

namespace N25

/-- A locally fixed preimage makes the rational-point Kummer cocycle a coboundary. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN5 : N5Surj)
    (P Q : J) (hP : P ∈ M) (hQ : piEnd Q = P) :
    ∃ v : ↥V, ∀ τ : G5, r5 τ • Q - Q = r5 τ • (v : J) - (v : J) := by
  have hP5 : P ∈ M5 := fun τ => hP (r5 τ)
  obtain ⟨Q5, hQ5⟩ := (pi5_bijective_of_N5Surj hPhi K2 hN5).2 ⟨P,hP5⟩
  have he : piEnd (Q5 : J) = P := congrArg Subtype.val hQ5
  refine ⟨⟨Q - Q5, ?_⟩, ?_⟩
  · change piEnd (Q - Q5) = 0
    rw [map_sub, hQ, he, sub_self]
  · intro τ
    change _ = r5 τ • (Q - (Q5 : J)) - (Q - (Q5 : J))
    rw [smul_sub, Q5.property τ]
    abel

end N25
