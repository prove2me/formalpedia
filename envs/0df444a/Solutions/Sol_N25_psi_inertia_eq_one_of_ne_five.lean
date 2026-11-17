-- Prove2me | solution 1 for N25.psi_inertia_eq_one_of_ne_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:11.924993+00:00
-- url     : https://prove2.me/submissions/9a2d0204-e45a-425e-9f59-7e6d58799e6c

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one

set_option autoImplicit false

noncomputable section

namespace N25

/-- The literal order-five character is trivial on inertia at every prime
other than five, by prime-to-residue-characteristic rigidity of roots. -/
theorem _root_.solution {q : ℕ} (hq : q.Prime) (hq5 : q ≠ 5)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : psi σ = 1 := by
  have hq25 : ¬ q ∣ 25 := by
    intro h
    have hqdiv : q ∣ 5 := hq.dvd_of_dvd_pow (by simpa using h : q ∣ 5 ^ 2)
    exact hq5 (((Nat.dvd_prime Nat.prime_five).mp hqdiv).resolve_left hq.ne_one)
  have hχval : (1 : ZMod 25) = (chi25 σ : ZMod 25) := by
    apply modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 25) σ.toRingEquiv
    intro t ht
    have ht' : (t : AlgebraicClosure ℚ) ^ 25 = 1 := (mem_rootsOfUnity' 25 t).mp ht
    have hs := ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
      A hq hA hσ hq25 ht'
    change σ (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (1 : ZMod 25).val
    rw [show (1 : ZMod 25).val = 1 by decide, pow_one]
    exact hs
  have hχ : chi25 σ = 1 := (Units.ext hχval).symm
  change psiBar (chi25 σ) = 1
  rw [hχ, map_one]

end N25
