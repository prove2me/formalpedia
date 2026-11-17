-- Prove2me | solution 1 for N25.GlobalKummer.quotient_zero_on_five_inertia
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:44.420147+00:00
-- url     : https://prove2.me/submissions/0e3c0387-c0da-46fa-865b-67d0b9c79916

import Mathlib
import Definitions.Def_N25_GlobalKummerQuotient
import Theorems.Thm_N25_kummer_at_five_is_coboundary_of_N5Surj
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
import Theorems.Thm_N25_chi71_inertia_eq_one
import Definitions.Def_N25_LocalFiveArithmetic

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance quotientFivePrimeFive_s723d80 : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance quotientFivePrimeSeventyOne_s723d80 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The actual multiplicative quotient division cocycle vanishes on global
inertia at the chosen place over five, using the proved local coboundary. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN5 : N5Surj)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    (σ : Gal) (hσ : σ ∈ (ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ) :
    quotientDivisionCocycle hPhi K2 P Q hQ σ = 0 := by
  obtain ⟨v, hv⟩ := kummer_at_five_is_coboundary_of_N5Surj hPhi K2 hN5
    (P : J) Q P.property hQ
  obtain ⟨τ, hτ, hτglobal⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq 5 σ hσ
  have hτI : τ ∈ I5 := by
    change localGaloisToGlobal 5 τ ∈ (ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ
    rw [hτglobal]
    exact hσ
  have hχ : (ExtCitation.cycloChar 71 σ : ZMod 71) = 1 := by
    have h := chi71_inertia_eq_one τ hτI
    change ExtCitation.cycloChar 71 (localGaloisToGlobal 5 τ) = 1 at h
    rw [hτglobal] at h
    exact congrArg Units.val h
  have hcb : divisionCocycle hPhi P Q hQ σ = vAct σ v - v := by
    apply Subtype.ext
    change σ • Q - Q = σ • (v : J) - (v : J)
    have h := hv τ
    change localGaloisToGlobal 5 τ • Q - Q =
      localGaloisToGlobal 5 τ • (v : J) - (v : J) at h
    rw [hτglobal] at h
    exact h
  change K2.q (divisionCocycle hPhi P Q hQ σ) = 0
  rw [hcb, map_sub, K2.q_galois, hχ, one_mul, sub_self]

end N25.GlobalKummer
