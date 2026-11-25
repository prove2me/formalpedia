-- Prove2me | solution 1 for HodgeComputer.PolarizedK3Remainder.normalChart_X0_pow_ten_legal
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T03:07:51.319463+00:00
-- url     : https://prove2.me/submissions/86ef8527-6725-4e2e-a6b1-e0c230093d61

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option allowUnsafeReducibility true
attribute [reducible] HodgeComputer.PolarizedK3Remainder.n

noncomputable section

open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

private abbrev X0 : AmbientPoly n := X (R := ℂ) (0 : Fin 6)

/-- Point with \(X_0=0\) and all other coordinates \(1\). -/
private def pt : Fin 6 → ℂ := ![0, 1, 1, 1, 1, 1]

private lemma pt_0 : pt 0 = 0 := rfl
private lemma pt_1 : pt 1 = 1 := rfl
private lemma pt_2 : pt 2 = 1 := rfl
private lemma pt_3 : pt 3 = 1 := rfl
private lemma pt_4 : pt 4 = 1 := rfl
private lemma pt_5 : pt 5 = 1 := rfl

private lemma eval_pt_X0 : eval pt X0 = 0 := by
  simp [X0, eval_X, pt_0]

private lemma eval_pt_F_ne : eval pt F ≠ 0 := by
  simp only [F, map_add, map_mul, map_pow, map_ofNat, eval_C, eval_X,
    pt_0, pt_1, pt_2, pt_3, pt_4, pt_5]
  norm_num

private lemma not_X0_dvd_F : ¬ X0 ∣ F := by
  intro h
  obtain ⟨q, hq⟩ := h
  have hpt : eval pt F = 0 := by
    rw [hq, eval_mul, eval_pt_X0, zero_mul]
  exact eval_pt_F_ne hpt

private lemma isRelPrime_F_X0_pow_ten : IsRelPrime F (X0 ^ 10) := by
  rw [isRelPrime_comm]
  refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors
      (pow_ne_zero 10 (X_ne_zero (0 : Fin 6)))).mpr ?_
  intro d hdPow hdF hdPrime
  have hdX : d ∣ X0 := hdPrime.dvd_of_dvd_pow hdPow
  have hAssoc : Associated d X0 :=
    (hdPrime.dvd_prime_iff_associated (X_prime (i := (0 : Fin 6)))).mp hdX
  exact not_X0_dvd_F (hAssoc.symm.dvd.trans hdF)

theorem solution :
    let S : AmbientPoly n := (MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (10 : ℕ)
    S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S := by
  refine ⟨pow_ne_zero 10 (X_ne_zero (0 : Fin 6)), ?_, ?_⟩
  · exact (isHomogeneous_X (R := ℂ) (0 : Fin 6)).pow 10
  · exact isRelPrime_F_X0_pow_ten
