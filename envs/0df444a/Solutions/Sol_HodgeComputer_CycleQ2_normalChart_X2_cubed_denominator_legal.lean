-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_X2_cubed_denominator_legal
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T18:01:36.859888+00:00
-- url     : https://prove2.me/submissions/9e5dbffa-de65-4f31-ac68-03c4daf61507

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerCycleQ2Character
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Prime.Defs
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

private abbrev X2 : AmbientPoly n := X (R := ℂ) (2 : Fin 6)

private def vPoint : Fin 6 → ℂ := ![1, 0, 0, 0, 0, 0]

private lemma eval_F_vPoint : eval vPoint F = 1 := by
  unfold F
  simp [vPoint, eval_X, eval_C, eval_add, eval_mul, eval_pow]

private lemma not_X2_dvd_F : ¬ (X2 ∣ F) := by
  intro h
  have hdiv : eval vPoint X2 ∣ eval vPoint F := map_dvd (eval vPoint) h
  have hx : eval vPoint X2 = 0 := by
    change eval vPoint (X (R := ℂ) (2 : Fin 6)) = 0
    simp [vPoint, eval_X]
  rw [hx, eval_F_vPoint, zero_dvd_iff] at hdiv
  exact one_ne_zero hdiv

private lemma isRelPrime_F_X2 : IsRelPrime F X2 := by
  have hirr : Irreducible X2 :=
    (X_prime (R := ℂ) (σ := Fin 6) (i := (2 : Fin 6))).irreducible
  exact isRelPrime_comm.1 ((hirr.isRelPrime_iff_not_dvd).2 not_X2_dvd_F)

theorem solution :
    (MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ) ≠ 0 ∧
      ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)).IsHomogeneous 3 ∧
      ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)).totalDegree = 3 ∧
      IsRelPrime F ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ)) ∧
      IsCharacter 0 ((MvPolynomial.X (R := ℂ) (2 : Fin 6) : AmbientPoly n) ^ (3 : ℕ) :
        AmbientPoly 5) := by
  change X2 ^ 3 ≠ 0 ∧ (X2 ^ 3).IsHomogeneous 3 ∧ (X2 ^ 3).totalDegree = 3 ∧
    IsRelPrime F (X2 ^ 3) ∧ IsCharacter 0 (X2 ^ 3 : AmbientPoly 5)
  refine ⟨?ne, ?hom, ?td, ?rp, ?chi⟩
  · exact pow_ne_zero _ (X_ne_zero _)
  · exact isHomogeneous_X_pow _ _
  · exact totalDegree_X_pow _ _
  · exact IsRelPrime.pow_right isRelPrime_F_X2
  · intro d hd
    classical
    have hcoeff : coeff d (X2 ^ 3) = if Finsupp.single (2 : Fin 6) 3 = d then 1 else 0 :=
      coeff_X_pow (R := ℂ) (2 : Fin 6) d 3
    rw [hcoeff] at hd
    split_ifs at hd with hEq
    · subst hEq
      change (↑(Finsupp.weight (R := ℕ) sixthRootWeight (Finsupp.single (2 : Fin 6) 3)) : ZMod 6) = 0
      have hw :
          Finsupp.weight (R := ℕ) sixthRootWeight (Finsupp.single (2 : Fin 6) 3) =
            3 * sixthRootWeight (2 : Fin 6) := by
        simp [Finsupp.weight_single]
      rw [hw]
      simp [sixthRootWeight]
    · exact (hd rfl).elim
