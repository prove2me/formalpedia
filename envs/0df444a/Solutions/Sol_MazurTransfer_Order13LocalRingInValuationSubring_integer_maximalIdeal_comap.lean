-- Prove2me | solution 1 for MazurTransfer.Order13LocalRingInValuationSubring.integer_maximalIdeal_comap
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T03:31:30.14502+00:00
-- url     : https://prove2.me/submissions/c2c39199-b30f-48e4-8561-2157555062d9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the canonical local integer coefficient ring is contained
in every valuation subring lying over the specified rational prime.
Named downstream consumer: inertia fixed lifts for integral order-13 norms.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Int

noncomputable section
open MazurTransfer
open Order13LocalIntegralCoefficientMaps
theorem solution (q : ℕ) [Fact q.Prime] {Ω : Type} [Field Ω]
    [Algebra (LocalRing q) Ω] (A : ValuationSubring Ω)
    (hA : A.LiesOverPrime q) :
    (IsLocalRing.maximalIdeal A).comap (Int.castRingHom A) = primeIdeal q := by
  let I := (IsLocalRing.maximalIdeal A).comap (Int.castRingHom A)
  have hI : I ≠ ⊤ := (Ideal.comap_isPrime _ _).ne_top
  have hqI : primeIdeal q ≤ I := by
    apply Ideal.span_le.mpr
    intro z hz
    have hzq : z = (q : ℤ) := Set.mem_singleton_iff.mp hz
    subst z
    change (Int.castRingHom A) (q : ℤ) ∈ IsLocalRing.maximalIdeal A
    have hmem : (q : A) ∈ IsLocalRing.maximalIdeal A :=
      ValuationSubring.coe_mem_nonunits_iff.mp (by
        simpa only [SubringClass.coe_natCast] using
          (show (q : Ω) ∈ A.nonunits from hA))
    simpa using hmem
  have hmax : (primeIdeal q).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  exact (Ideal.IsMaximal.eq_of_le hmax hI hqI).symm

#print axioms solution
