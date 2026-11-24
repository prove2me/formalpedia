-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.SplitPlace.two_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:26.88716+00:00
-- url     : https://prove2.me/submissions/c0a022a0-82b6-40fd-b95d-0e29650f666b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPlace
namespace GlobalTheory.CMVal.Euler.SplitPlace
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (p : Ideal (𝓞 F)) [p.IsMaximal] (P P' : p.primesOver (𝓞 E)) (hne : P ≠ P') :
    (∀ R : p.primesOver (𝓞 E), R = P ∨ R = P') ∧
      ∀ R : p.primesOver (𝓞 E), R.1.ramificationIdx (𝓞 F) * R.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum
  have hpos : ∀ P : p.primesOver (𝓞 E),
      1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hall : ∀ R : p.primesOver (𝓞 E), R = P ∨ R = P' := by
    intro R
    by_contra hR
    push Not at hR
    have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
      P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {R, P, P'})
    rw [hsum, Finset.sum_insert (by simp [hR.1, hR.2]), Finset.sum_pair hne] at h3
    have := hpos R
    have := hpos P
    have := hpos P'
    omega
  refine ⟨hall, fun R => ?_⟩
  have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
    P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {P, P'})
  rw [hsum, Finset.sum_pair hne] at h3
  have := hpos P
  have := hpos P'
  rcases hall R with rfl | rfl <;> omega
end GlobalTheory.CMVal.Euler.SplitPlace
