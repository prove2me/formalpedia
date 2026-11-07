-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.normalDerivative_relPrime
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T03:46:24.997602+00:00
-- url     : https://prove2.me/submissions/78bded48-06a7-471f-95db-c42aa8585902

import Definitions.Def_HodgeComputerFourPlusTwoResidual
import Definitions.Def_HodgeComputerNormalChart
import Theorems.Thm_HodgeComputer_Algebra_normalDerivative_relPrime_of_specialization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open HodgeComputer HodgeComputer.FourPlusTwoResidual MvPolynomial

private theorem nat_homogeneous (c : ℕ) : (c : AmbientPoly 5).IsHomogeneous 0 := by
  simpa only [map_natCast] using (isHomogeneous_C (Fin 6) (c : ℂ))

private theorem int_homogeneous (c : ℤ) : (c : AmbientPoly 5).IsHomogeneous 0 := by
  simpa only [map_intCast] using (isHomogeneous_C (Fin 6) (c : ℂ))

private theorem F_homogeneous : F.IsHomogeneous 6 := by
  unfold F
  exact ((((((((((((((isHomogeneous_X_pow 0 6).add ((((nat_homogeneous 5).mul (isHomogeneous_X_pow 0 5)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 5).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((nat_homogeneous 10).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 5)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 10).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add ((((nat_homogeneous 15).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((nat_homogeneous 10).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 3 6)).add ((((nat_homogeneous 5).mul (isHomogeneous_X_pow 3 5)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((nat_homogeneous 15).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 5)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 4 6)).add (isHomogeneous_X_pow 5 6))

private theorem A_homogeneous : A.IsHomogeneous 6 := by
  unfold A
  exact ((isHomogeneous_X_pow 0 3).mul (isHomogeneous_X_pow 3 3))

private abbrev split := MvPolynomial.finSuccEquiv ℂ 5
private lemma split_C (c : ℂ) : split (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [split, finSuccEquiv_apply]
private lemma split_X0 : split (MvPolynomial.X (0 : Fin 6)) = Polynomial.X := by
  exact finSuccEquiv_X_zero
private lemma split_X1 : split (MvPolynomial.X (1 : Fin 6)) = Polynomial.C (MvPolynomial.X (0 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (0 : Fin 5))
private lemma split_X2 : split (MvPolynomial.X (2 : Fin 6)) = Polynomial.C (MvPolynomial.X (1 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (1 : Fin 5))
private lemma split_X3 : split (MvPolynomial.X (3 : Fin 6)) = Polynomial.C (MvPolynomial.X (2 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (2 : Fin 5))
private lemma split_X4 : split (MvPolynomial.X (4 : Fin 6)) = Polynomial.C (MvPolynomial.X (3 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (3 : Fin 5))
private lemma split_X5 : split (MvPolynomial.X (5 : Fin 6)) = Polynomial.C (MvPolynomial.X (4 : Fin 5)) := by
  exact finSuccEquiv_X_succ (j := (4 : Fin 5))

private lemma top_coeff : (split F).coeff 6 = MvPolynomial.C (1 / 1 : ℂ) := by
  simp only [F, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, split_C,
    split_X0, split_X1, split_X2, split_X3, split_X4, split_X5]
  simp only [← Polynomial.C_pow, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_neg, Polynomial.coeff_mul_C, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num
  all_goals simp [div_eq_mul_inv]
  all_goals norm_num only [map_natCast, map_intCast]
  all_goals exact (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 5) ℂ) 1).symm

private def specialize : MvPolynomial (Fin 5) ℂ →+* ℂ :=
  eval (fun i : Fin 5 => if i = 1 then 1 else 0)

private def linePoly : Polynomial ℂ := (Polynomial.C (1 / 1 : ℂ) * Polynomial.X ^ 6 + Polynomial.C (1 / 1 : ℂ))

private lemma specialize_F : (split F).map specialize = linePoly := by
  have h0 : (0 : Fin 5) ≠ 1 := by decide
  have h2 : (2 : Fin 5) ≠ 1 := by decide
  have h3 : (3 : Fin 5) ≠ 1 := by decide
  have h4 : (4 : Fin 5) ≠ 1 := by decide
  simp only [F, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, split_C,
    split_X0, split_X1, split_X2, split_X3, split_X4, split_X5]
  norm_num [specialize, h0, h2, h3, h4,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X]
  all_goals simp only [linePoly, div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  all_goals norm_num only [map_one, inv_one, mul_one, one_mul]
  all_goals ring

private lemma line_relPrime : IsRelPrime linePoly linePoly.derivative := by
  apply IsCoprime.isRelPrime
  refine ⟨(Polynomial.C (1 / 1 : ℂ)), (Polynomial.C (-1 / 6 : ℂ) * Polynomial.X ^ 1), ?_⟩
  apply Polynomial.funext
  intro x
  norm_num [linePoly, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
    Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  all_goals ring

theorem solution : IsRelPrime F (NormalChart.normal F) := by
  apply HodgeComputer.Algebra.normalDerivative_relPrime_of_specialization 5 6 F (1 / 1 : ℂ)
    (fun i : Fin 5 => if i = 1 then 1 else 0) F_homogeneous (by norm_num) top_coeff
  change IsRelPrime ((split F).map specialize) (Polynomial.derivative ((split F).map specialize))
  rw [specialize_F]
  exact line_relPrime

#print axioms solution
