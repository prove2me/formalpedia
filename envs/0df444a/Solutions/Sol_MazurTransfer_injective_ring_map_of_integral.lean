-- Prove2me | solution 1 for MazurTransfer.injective_ring_map_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T14:36:26.114868+00:00
-- url     : https://prove2.me/submissions/40cc7694-b4d3-48de-9fe6-e576994bf4f3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: injectivity on the coefficient ring detects injectivity
on an integral domain integral over it. Named downstream consumer: extending
the order-13 diamond coordinate substitution to the actual function field.
-/
import Mathlib

noncomputable section
universe u v w
namespace MazurTransfer.PublicIntegralRingMapProof

theorem injective_of_integral (R : Type u) [CommRing R] [Nontrivial R]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    (B : Type w) [CommRing B] (f : A →+* B)
    (h : Function.Injective (f.comp (algebraMap R A))) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := R)
  change RingHom.ker (f.comp (algebraMap R A)) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp h

end MazurTransfer.PublicIntegralRingMapProof
#print axioms MazurTransfer.PublicIntegralRingMapProof.injective_of_integral

theorem solution (R : Type u) [CommRing R] [Nontrivial R]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    (B : Type w) [CommRing B] (f : A →+* B)
    (h : Function.Injective (f.comp (algebraMap R A))) : Function.Injective f := by
  exact MazurTransfer.PublicIntegralRingMapProof.injective_of_integral R A B f h

#print axioms solution
