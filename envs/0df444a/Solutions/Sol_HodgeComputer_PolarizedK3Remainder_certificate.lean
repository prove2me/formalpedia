-- Prove2me | solution 1 for HodgeComputer.PolarizedK3Remainder.certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T03:58:32.205189+00:00
-- url     : https://prove2.me/submissions/fd23f9ba-e511-4bfb-87bc-c5bea4b51ce6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalDerivative_relPrime
import Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_residue_solvable
import Theorems.Thm_HodgeComputer_NormalChart_certificate_of_residue
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart
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

open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

private theorem nat_homogeneous (c : ℕ) : (c : AmbientPoly 5).IsHomogeneous 0 := by
  simpa only [map_natCast] using (isHomogeneous_C (Fin 6) (c : ℂ))

private theorem int_homogeneous (c : ℤ) : (c : AmbientPoly 5).IsHomogeneous 0 := by
  simpa only [map_intCast] using (isHomogeneous_C (Fin 6) (c : ℂ))

private theorem F_homogeneous : F.IsHomogeneous 6 := by
  unfold F
  exact ((((((((((((((((((((((((((((((((((((((((((isHomogeneous_X_pow 0 6).add ((((nat_homogeneous 5).mul (isHomogeneous_X_pow 0 5)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((nat_homogeneous 15).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X_pow 3 2))).add (((((nat_homogeneous 25).mul (isHomogeneous_X_pow 0 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 50).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 5).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 15).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 15).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((nat_homogeneous 15).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 4))).add (((((nat_homogeneous 50).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 3 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 5).mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 10).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((((nat_homogeneous 30).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 25).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 3 4)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((((nat_homogeneous 30).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((nat_homogeneous 15).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 5)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 150).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X_pow 5 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 10).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 75).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 5 4)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 1 6)).add ((((nat_homogeneous 10).mul (isHomogeneous_X_pow 1 5)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((nat_homogeneous 15).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X_pow 4 2))).add (((((nat_homogeneous 50).mul (isHomogeneous_X_pow 1 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 5).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 100).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 15).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((nat_homogeneous 15).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 4 4))).add (((((nat_homogeneous 100).mul (isHomogeneous_X_pow 1 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 15).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 2)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 50).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X_pow 4 4)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 2 6)).add (((((nat_homogeneous 75).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((nat_homogeneous 15).mul (isHomogeneous_X_pow 2 4)).mul (isHomogeneous_X_pow 5 2))).add (((((nat_homogeneous 150).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 3)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((nat_homogeneous 15).mul (isHomogeneous_X_pow 2 2)).mul (isHomogeneous_X_pow 5 4))).add (isHomogeneous_X_pow 3 6)).add ((((nat_homogeneous 5).mul (isHomogeneous_X_pow 3 5)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (((((nat_homogeneous 5).mul (isHomogeneous_X_pow 3 2)).mul (isHomogeneous_X_pow 4 3)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((nat_homogeneous 15).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X_pow 5 5)).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 4 6)).add ((((nat_homogeneous 10).mul (isHomogeneous_X_pow 4 5)).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 5 6))

private theorem A_homogeneous : A.IsHomogeneous 6 := by
  unfold A
  exact ((((((isHomogeneous_X ℂ (0 : Fin 6)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))

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

private theorem F_nonzero : F ≠ 0 := by
  intro hz
  have hc := top_coeff
  rw [hz, map_zero, Polynomial.coeff_zero] at hc
  have hne : (MvPolynomial.C (1 : ℂ) : MvPolynomial (Fin 5) ℂ) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (by norm_num)
  exact hne (by simpa only [div_one] using hc.symm)

private theorem normal_nonzero : NormalChart.normal F ≠ 0 := by
  intro hz
  have hcp := normalDerivative_relPrime
  rw [hz] at hcp
  have hu : IsUnit F := isRelPrime_zero_right.mp hcp
  have hd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have h6 := F_homogeneous.totalDegree F_nonzero
  omega

theorem solution :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.PolarizedK3Remainder.n)
      HodgeComputer.PolarizedK3Remainder.F
      HodgeComputer.PolarizedK3Remainder.A
      HodgeComputer.PolarizedK3Remainder.d
      HodgeComputer.PolarizedK3Remainder.q  := by
  obtain ⟨S, W, Q, hS, hShom, hFS, hWhom, hres⟩ := normalChart_residue_solvable
  refine ⟨NormalChart.denominator F S, NormalChart.numerator F A S W, Q, ?_⟩
  exact HodgeComputer.NormalChart.certificate_of_residue F A S W Q
    F_nonzero F_homogeneous A_homogeneous normal_nonzero normalDerivative_relPrime
    hS hShom hFS hWhom hres

#print axioms solution
