-- Prove2me | solution 1 for HodgeComputer.KleinCoupledCharacter.certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T03:58:41.752207+00:00
-- url     : https://prove2.me/submissions/1b05f2a0-ab8d-4830-a680-d794c6668c3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_KleinCoupledCharacter_normalDerivative_relPrime
import Theorems.Thm_HodgeComputer_KleinCoupledCharacter_normalChart_residue_solvable
import Theorems.Thm_HodgeComputer_NormalChart_certificate_of_residue
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Definitions.Def_HodgeComputerKleinCoupledCharacter
import Definitions.Def_HodgeComputerNormalChart
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open HodgeComputer HodgeComputer.KleinCoupledCharacter MvPolynomial

private theorem nat_homogeneous (c : ℕ) : (c : AmbientPoly 5).IsHomogeneous 0 := by
  simpa only [map_natCast] using (isHomogeneous_C (Fin 6) (c : ℂ))

private theorem F_homogeneous : F.IsHomogeneous 6 := by
  unfold F
  exact ((((((((((isHomogeneous_X_pow 0 5).mul (isHomogeneous_X ℂ (1 : Fin 6))).add ((((((nat_homogeneous 10).mul (isHomogeneous_X_pow 0 3)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((((((nat_homogeneous 5).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X_pow 1 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add ((isHomogeneous_X ℂ (0 : Fin 6)).mul (isHomogeneous_X_pow 2 5))).add ((isHomogeneous_X_pow 1 5).mul (isHomogeneous_X ℂ (2 : Fin 6)))).add ((((((nat_homogeneous 15).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X_pow 2 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul (isHomogeneous_C (Fin 6) (1 / 7 : ℂ)))).add (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add (isHomogeneous_X_pow 5 6))

theorem relPrime_of_specialization {R K : Type*} [CommRing R] [IsDomain R]
    [CommRing K] [IsDomain K] (φ : R →+* K) (f g : Polynomial R)
    (hf : IsUnit f.leadingCoeff)
    (hfg : IsRelPrime (f.map φ) (g.map φ)) : IsRelPrime f g := by
  intro d hdf hdg
  apply Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ
  · exact isUnit_of_dvd_unit (Polynomial.leadingCoeff_dvd_leadingCoeff hdf) hf
  · exact hfg (map_dvd (Polynomial.mapRingHom φ) hdf)
      (map_dvd (Polynomial.mapRingHom φ) hdg)


private def chart :=
  (renameEquiv ℂ (Equiv.swap (0 : Fin 6) 5)).trans (finSuccEquiv ℂ 5)

private lemma chart_C (c : ℂ) : chart (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [chart, renameEquiv_apply, finSuccEquiv_apply]
private lemma chart_X0 : chart (MvPolynomial.X (0 : Fin 6)) = Polynomial.C (MvPolynomial.X (4 : Fin 5)) := by
  change finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) (X (0 : Fin 6))) = _
  rw [rename_X, show (Equiv.swap (0 : Fin 6) 5) (0 : Fin 6) = 5 from by decide]
  exact finSuccEquiv_X_succ (j := (4 : Fin 5))
private lemma chart_X1 : chart (MvPolynomial.X (1 : Fin 6)) = Polynomial.C (MvPolynomial.X (0 : Fin 5)) := by
  change finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) (X (1 : Fin 6))) = _
  rw [rename_X, show (Equiv.swap (0 : Fin 6) 5) (1 : Fin 6) = 1 from by decide]
  exact finSuccEquiv_X_succ (j := (0 : Fin 5))
private lemma chart_X2 : chart (MvPolynomial.X (2 : Fin 6)) = Polynomial.C (MvPolynomial.X (1 : Fin 5)) := by
  change finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) (X (2 : Fin 6))) = _
  rw [rename_X, show (Equiv.swap (0 : Fin 6) 5) (2 : Fin 6) = 2 from by decide]
  exact finSuccEquiv_X_succ (j := (1 : Fin 5))
private lemma chart_X3 : chart (MvPolynomial.X (3 : Fin 6)) = Polynomial.C (MvPolynomial.X (2 : Fin 5)) := by
  change finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) (X (3 : Fin 6))) = _
  rw [rename_X, show (Equiv.swap (0 : Fin 6) 5) (3 : Fin 6) = 3 from by decide]
  exact finSuccEquiv_X_succ (j := (2 : Fin 5))
private lemma chart_X4 : chart (MvPolynomial.X (4 : Fin 6)) = Polynomial.C (MvPolynomial.X (3 : Fin 5)) := by
  change finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) (X (4 : Fin 6))) = _
  rw [rename_X, show (Equiv.swap (0 : Fin 6) 5) (4 : Fin 6) = 4 from by decide]
  exact finSuccEquiv_X_succ (j := (3 : Fin 5))
private lemma chart_X5 : chart (MvPolynomial.X (5 : Fin 6)) = Polynomial.X := by
  change finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) (X (5 : Fin 6))) = _
  rw [rename_X, show (Equiv.swap (0 : Fin 6) 5) (5 : Fin 6) = 0 from by decide]
  exact finSuccEquiv_X_zero

private lemma top_coeff : (chart F).coeff 6 = 1 := by
  simp only [F, map_add, map_mul, map_pow, map_ofNat, chart_C,
    chart_X0, chart_X1, chart_X2, chart_X3, chart_X4, chart_X5]
  simp only [← Polynomial.C_pow, Polynomial.coeff_add, Polynomial.coeff_mul_C,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X,
    Polynomial.coeff_mul_X]
  norm_num

private lemma leading_unit : IsUnit (chart F).leadingCoeff := by
  have hh : (rename (Equiv.swap (0 : Fin 6) 5) F).IsHomogeneous 6 :=
    F_homogeneous.rename_isHomogeneous
  have hdeg : (chart F).natDegree ≤ 6 := by
    change (finSuccEquiv ℂ 5 (rename (Equiv.swap (0 : Fin 6) 5) F)).natDegree ≤ 6
    rw [natDegree_finSuccEquiv]
    exact (degreeOf_le_totalDegree _ 0).trans hh.totalDegree_le
  have hc : (chart F).coeff 6 ≠ 0 := by rw [top_coeff]; exact one_ne_zero
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc, top_coeff]
  exact isUnit_one

private theorem A_homogeneous : A.IsHomogeneous 6 := by
  unfold A
  exact (isHomogeneous_X_pow 0 3).mul (isHomogeneous_X_pow 3 3)

private theorem F_nonzero : F ≠ 0 := by
  intro hz
  have hc := top_coeff
  rw [hz, map_zero, Polynomial.coeff_zero] at hc
  norm_num at hc

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
      (n := HodgeComputer.KleinCoupledCharacter.n)
      HodgeComputer.KleinCoupledCharacter.F
      HodgeComputer.KleinCoupledCharacter.A
      HodgeComputer.KleinCoupledCharacter.d
      HodgeComputer.KleinCoupledCharacter.q  := by
  obtain ⟨S, W, Q, hS, hShom, hFS, hWhom, hres⟩ := normalChart_residue_solvable
  refine ⟨NormalChart.denominator F S, NormalChart.numerator F A S W, Q, ?_⟩
  exact HodgeComputer.NormalChart.certificate_of_residue F A S W Q
    F_nonzero F_homogeneous A_homogeneous normal_nonzero normalDerivative_relPrime
    hS hShom hFS hWhom hres

#print axioms solution
