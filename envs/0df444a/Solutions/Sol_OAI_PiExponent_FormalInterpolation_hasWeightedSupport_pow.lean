-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T06:23:02.235214+00:00
-- url     : https://prove2.me/submissions/c9a079b8-3db5-4620-a7a8-07b9e99f5f1a

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

namespace OAI.PiExponent.FormalInterpolation

theorem hasWeightedSupport_mul
    {m : Nat} (v : Fin (m + 1) -> Real) (B C : Real)
    (F G : MvPowerSeries (Fin (m + 1)) Complex)
    (hF : hasWeightedSupport v B F) (hG : hasWeightedSupport v C G) :
    hasWeightedSupport v (B + C) (F * G) := by
  classical
  intro b hb
  rw [MvPowerSeries.coeff_mul] at hb
  obtain ⟨⟨p, q⟩, hpq, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hp : MvPowerSeries.coeff p F ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hq : MvPowerSeries.coeff q G ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  let a : Fin (m + 1) -> Nat := Finsupp.equivFunOnFinite p
  let c : Fin (m + 1) -> Nat := Finsupp.equivFunOnFinite q
  have hpa : p = InterpolationMatrix.exponentVector a := by
    simp [a, InterpolationMatrix.exponentVector]
  have hqc : q = InterpolationMatrix.exponentVector c := by
    simp [c, InterpolationMatrix.exponentVector]
  have hab : a + c = b := by
    have hpq' : p + q = InterpolationMatrix.exponentVector b :=
      Finset.mem_antidiagonal.mp hpq
    have := congrArg Finsupp.equivFunOnFinite hpq'
    have hadd : Finsupp.equivFunOnFinite (p + q) =
        Finsupp.equivFunOnFinite p + Finsupp.equivFunOnFinite q := by
      ext i
      rfl
    rw [hadd] at this
    simpa [a, c, InterpolationMatrix.exponentVector] using this
  have hwa := hF a (by simpa [hpa] using hp)
  have hwc := hG c (by simpa [hqc] using hq)
  have hsum : (∑ i, ((b i : Real) * v i)) =
      (∑ i, ((a i : Real) * v i)) + (∑ i, ((c i : Real) * v i)) := by
    calc
      _ = ∑ i, (((a + c) i : Nat) : Real) * v i := by rw [hab]
      _ = _ := by simp [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  nlinarith

end OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (v : Fin (m + 1) -> Real) (B : Real)
    (hv : forall i, 0 <= v i)
    (F : MvPowerSeries (Fin (m + 1)) Complex)
    (hF : FormalInterpolation.hasWeightedSupport v B F) (n : Nat) :
    FormalInterpolation.hasWeightedSupport v ((n : Real) * B) (F ^ n) := by
  induction n with
  | zero =>
      intro b hb
      simp only [Nat.cast_zero, zero_mul] at hb ⊢
      have hidx : InterpolationMatrix.exponentVector b = 0 := by
        by_contra hidx
        apply hb
        simp [MvPowerSeries.coeff_one, hidx]
      have : b = 0 := by
        have hz : Finsupp.equivFunOnFinite.symm (0 : Fin (m + 1) -> Nat) =
            (0 : Finsupp (Fin (m + 1)) Nat) := by
          ext i
          simp [Finsupp.equivFunOnFinite]
        have hidx' : InterpolationMatrix.exponentVector b =
            InterpolationMatrix.exponentVector 0 := by
          rw [hidx]
          exact hz.symm
        exact Finsupp.equivFunOnFinite.symm.injective
          (by simpa [InterpolationMatrix.exponentVector] using hidx')
      rw [this]
      simp [InterpolationMatrix.exponentVector]
  | succ n ih =>
      have hmul := FormalInterpolation.hasWeightedSupport_mul v
        ((n : Real) * B) B (F ^ n) F ih hF
      simpa [pow_succ, Nat.cast_succ, add_mul] using hmul
