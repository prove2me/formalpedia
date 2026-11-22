-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.normalChart_residue_of_coreCertificate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:46.163588+00:00
-- url     : https://prove2.me/submissions/83bdfb8e-2661-479f-8cf7-e1dda1aaf525

import Definitions.Def_HodgeComputerFourPlusTwoResidual
import Definitions.Def_HodgeComputerFourPlusTwoCore
import Definitions.Def_HodgeComputerNormalChart
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MvPolynomial HodgeComputer HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

namespace FP2NormalBridge

abbrev CorePoly := MvPolynomial (Fin 4) ℂ
abbrev BinaryPoly := MvPolynomial (Fin 2) ℂ
abbrev SixPoly := MvPolynomial (Fin 6) ℂ

private def F6 : SixPoly := F
private def A6 : SixPoly := A

def binaryB : BinaryPoly :=
  X 0 ^ 6 + C (15 / 7 : ℂ) * X 0 ^ 4 * X 1 ^ 2 +
    C (10 / 7 : ℂ) * X 0 ^ 2 * X 1 ^ 4 + X 1 ^ 6

def liftCore : CorePoly →+* SixPoly := (rename ![0, 1, 3, 4]).toRingHom
def liftBinary : BinaryPoly →+* SixPoly := (rename ![2, 5]).toRingHom

lemma liftCore_X0 : liftCore (X 0) = X 0 := by simp [liftCore]
lemma liftCore_X1 : liftCore (X 1) = X 1 := by simp [liftCore]
lemma liftCore_X2 : liftCore (X 2) = X 3 := by simp [liftCore]
lemma liftCore_X3 : liftCore (X 3) = X 4 := by simp [liftCore]
lemma liftBinary_X0 : liftBinary (X 0) = X 2 := by simp [liftBinary]
lemma liftBinary_X1 : liftBinary (X 1) = X 5 := by simp [liftBinary]

lemma targetF_eq : F6 = liftCore core + liftBinary binaryB := by
  apply MvPolynomial.funext (σ := Fin 6)
  intro x
  simp only [F6, F, core, binaryB, liftCore, liftBinary, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, eval_rename, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three]
  ring

lemma targetA_eq : A6 = liftCore coreSource := by
  simp only [A6, A, coreSource, map_mul, map_pow, liftCore_X0, liftCore_X2]

lemma core_hom : core.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  have hC := isHomogeneous_C (Fin 4) (R := ℂ)
  have t1 : (X 0 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 0).pow 6
  have t2 : (C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 5)).mul (hX 1)
  have t3 : (C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((((hC _).mul ((hX 0).pow 3)).mul (hX 1)).mul (hX 2)).mul (hX 3)
  have t4 : (C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul (hX 0)).mul ((hX 1).pow 5)
  have t5 : (C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((((hC _).mul (hX 0)).mul (hX 1)).mul ((hX 2).pow 3)).mul (hX 3)
  have t6 : (X 1 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 1).pow 6
  have t7 : (X 2 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 2).pow 6
  have t8 : (C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 5)).mul (hX 3)
  have t9 : (C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul (hX 2)).mul ((hX 3).pow 5)
  have t10 : (X 3 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 3).pow 6
  unfold core
  exact ((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add t10

lemma binaryB_hom : binaryB.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 2) ℂ
  have hC := isHomogeneous_C (Fin 2) (R := ℂ)
  have b1 : (X 0 ^ 6 : BinaryPoly).IsHomogeneous 6 := (hX 0).pow 6
  have b2 : (C (15 / 7 : ℂ) * X 0 ^ 4 * X 1 ^ 2 : BinaryPoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 4)).mul ((hX 1).pow 2)
  have b3 : (C (10 / 7 : ℂ) * X 0 ^ 2 * X 1 ^ 4 : BinaryPoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 2)).mul ((hX 1).pow 4)
  have b4 : (X 1 ^ 6 : BinaryPoly).IsHomogeneous 6 := (hX 1).pow 6
  unfold binaryB
  exact ((b1.add b2).add b3).add b4

lemma liftCore_hom {p : CorePoly} {m : ℕ} (hp : p.IsHomogeneous m) :
    (liftCore p).IsHomogeneous m := by
  rw [p.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro d hd
  have hdeg : d 0 + d 1 + d 2 + d 3 = m := by
    have h := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, add_assoc] using h
  rw [monomial_eq, map_mul]
  have hC_eq : liftCore (C (coeff d p)) = C (coeff d p) := by simp [liftCore]
  rw [hC_eq]
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
    map_mul, map_pow, liftCore_X0, liftCore_X1, liftCore_X2, liftCore_X3]
  have h0 : ((X (0 : Fin 6) : SixPoly) ^ d 0).IsHomogeneous (1 * d 0) :=
    (isHomogeneous_X ℂ (0 : Fin 6)).pow (d 0)
  have h1 : ((X (1 : Fin 6) : SixPoly) ^ d 1).IsHomogeneous (1 * d 1) :=
    (isHomogeneous_X ℂ (1 : Fin 6)).pow (d 1)
  have h2 : ((X (3 : Fin 6) : SixPoly) ^ d 2).IsHomogeneous (1 * d 2) :=
    (isHomogeneous_X ℂ (3 : Fin 6)).pow (d 2)
  have h3 : ((X (4 : Fin 6) : SixPoly) ^ d 3).IsHomogeneous (1 * d 3) :=
    (isHomogeneous_X ℂ (4 : Fin 6)).pow (d 3)
  have hprod := (isHomogeneous_C (Fin 6) (coeff d p)).mul (((h0.mul h1).mul h2).mul h3)
  exact (show 0 + (1 * d 0 + 1 * d 1 + 1 * d 2 + 1 * d 3) = m by omega) ▸ hprod

lemma liftBinary_hom {p : BinaryPoly} {m : ℕ} (hp : p.IsHomogeneous m) :
    (liftBinary p).IsHomogeneous m := by
  rw [p.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro d hd
  have hdeg : d 0 + d 1 = m := by
    have h := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using h
  rw [monomial_eq, map_mul]
  have hC_eq : liftBinary (C (coeff d p)) = C (coeff d p) := by simp [liftBinary]
  rw [hC_eq]
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
    map_mul, map_pow, liftBinary_X0, liftBinary_X1]
  have h0 : ((X (2 : Fin 6) : SixPoly) ^ d 0).IsHomogeneous (1 * d 0) :=
    (isHomogeneous_X ℂ (2 : Fin 6)).pow (d 0)
  have h1 : ((X (5 : Fin 6) : SixPoly) ^ d 1).IsHomogeneous (1 * d 1) :=
    (isHomogeneous_X ℂ (5 : Fin 6)).pow (d 1)
  have hprod := (isHomogeneous_C (Fin 6) (coeff d p)).mul (h0.mul h1)
  exact (show 0 + (1 * d 0 + 1 * d 1) = m by omega) ▸ hprod

lemma pderiv_liftCore (p : CorePoly) (j : Fin 6) :
    pderiv j (liftCore p) =
      if j = 0 then liftCore (pderiv 0 p)
      else if j = 1 then liftCore (pderiv 1 p)
      else if j = 3 then liftCore (pderiv 2 p)
      else if j = 4 then liftCore (pderiv 3 p)
      else 0 := by
  induction p using MvPolynomial.induction_on generalizing j with
  | C z =>
    simp only [liftCore, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C, pderiv_C, map_zero]
    split_ifs <;> rfl
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    split_ifs <;> ring
  | mul_X p i hp =>
    rw [map_mul]
    fin_cases i <;> fin_cases j <;>
      simp [liftCore_X0, liftCore_X1, liftCore_X2, liftCore_X3, pderiv_X, hp]

lemma pderiv_liftBinary (p : BinaryPoly) (j : Fin 6) :
    pderiv j (liftBinary p) =
      if j = 2 then liftBinary (pderiv 0 p)
      else if j = 5 then liftBinary (pderiv 1 p)
      else 0 := by
  induction p using MvPolynomial.induction_on generalizing j with
  | C z =>
    simp only [liftBinary, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C, pderiv_C, map_zero]
    split_ifs <;> rfl
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    split_ifs <;> ring
  | mul_X p i hp =>
    rw [map_mul]
    fin_cases i <;> fin_cases j <;>
      simp [liftBinary_X0, liftBinary_X1, pderiv_X, hp]

private def atZero : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X}

private abbrev Coeff5 := MvPolynomial (Fin 5) ℂ
private def univF : Polynomial Coeff5 := MvPolynomial.finSuccEquiv ℂ 5 F6
private def cF5 : Coeff5 := C (5 / 7 : ℂ) * X 0
private def cF3 : Coeff5 := C (5 / 7 : ℂ) * X 0 * X 2 * X 3
private def cF1 : Coeff5 :=
  C (10 / 7 : ℂ) * X 0 ^ 5 + C (10 / 7 : ℂ) * X 0 * X 2 ^ 3 * X 3
private def cF0 : Coeff5 :=
  X 0 ^ 6 + X 1 ^ 6 + C (15 / 7 : ℂ) * X 1 ^ 4 * X 4 ^ 2 +
    C (10 / 7 : ℂ) * X 1 ^ 2 * X 4 ^ 4 + X 2 ^ 6 +
    C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 + C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 + X 3 ^ 6 + X 4 ^ 6

private lemma univF_formula :
    univF = Polynomial.X ^ 6 +
      (Polynomial.C cF5 * Polynomial.X ^ 5 + Polynomial.C cF3 * Polynomial.X ^ 3 +
        Polynomial.C cF1 * Polynomial.X + Polynomial.C cF0) := by
  have hX0 : MvPolynomial.finSuccEquiv ℂ 5 (X 0) = Polynomial.X := by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX1 : MvPolynomial.finSuccEquiv ℂ 5 (X 1) = Polynomial.C (X 0) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX2 : MvPolynomial.finSuccEquiv ℂ 5 (X 2) = Polynomial.C (X 1) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX3 : MvPolynomial.finSuccEquiv ℂ 5 (X 3) = Polynomial.C (X 2) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX4 : MvPolynomial.finSuccEquiv ℂ 5 (X 4) = Polynomial.C (X 3) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hX5 : MvPolynomial.finSuccEquiv ℂ 5 (X 5) = Polynomial.C (X 4) := by
    simp [MvPolynomial.finSuccEquiv_apply]; rfl
  have hC : ∀ c : ℂ, MvPolynomial.finSuccEquiv ℂ 5 (C c) = Polynomial.C (C c) := by
    intro c; simp [MvPolynomial.finSuccEquiv_apply]
  unfold univF
  rw [targetF_eq]
  unfold core binaryB
  simp only [map_add, map_mul, map_pow, liftCore_X0, liftCore_X1, liftCore_X2, liftCore_X3,
    liftBinary_X0, liftBinary_X1]
  have hLC : ∀ c : ℂ, liftCore (C c) = C c := fun c => by simp [liftCore]
  have hLB : ∀ c : ℂ, liftBinary (C c) = C c := fun c => by simp [liftBinary]
  simp only [hLC, hLB, map_add, map_mul, map_pow, hX0, hX1, hX2, hX3, hX4, hX5, hC,
    cF5, cF3, cF1, cF0]
  ring

lemma F6_irreducible : Irreducible F6 := by
  have hX0_poly : (Polynomial.X : Polynomial ℂ) = Polynomial.X - Polynomial.C 0 := by simp
  have hatZero : atZero.IsPrime := by
    rw [atZero, hX0_poly]
    exact (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero 0)).mpr
      (Polynomial.prime_X_sub_C 0)
  let sec : Polynomial ℂ := (Polynomial.X + 1) ^ 6 - 1
  let P : Polynomial (Polynomial ℂ) := Polynomial.X ^ 6 + Polynomial.C sec
  have hP_irred : Irreducible P := by
    have hmon : P.Monic := Polynomial.monic_X_pow_add_C sec (by decide)
    have hdP : P.natDegree = 6 := Polynomial.natDegree_X_pow_add_C
    have hmem : sec ∈ atZero := by
      rw [atZero, Ideal.mem_span_singleton, hX0_poly, Polynomial.dvd_iff_isRoot]
      simp [sec, Polynomial.IsRoot]
    have hnot_sq : sec ∉ atZero ^ 2 := by
      intro hsq
      rw [atZero, hX0_poly, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hsq
      have hd : (Polynomial.X - Polynomial.C (0 : ℂ) : Polynomial ℂ) ∣
          Polynomial.derivative sec := by
        simpa using Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hsq
      have he := Polynomial.dvd_iff_isRoot.mp hd
      have hsec_d : Polynomial.eval 0 (Polynomial.derivative sec) = 6 := by
        have hcomp : sec = (Polynomial.X ^ 6 - 1 : Polynomial ℂ).comp (Polynomial.X + 1) := by
          simp [sec]
        rw [hcomp, Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_comp]
        simp
        norm_num
      rw [Polynomial.IsRoot, hsec_d] at he
      norm_num at he
    have heis : P.IsEisensteinAt atZero := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hmon.leadingCoeff, atZero, Ideal.mem_span_singleton, hX0_poly, Polynomial.dvd_iff_isRoot]
        simp [Polynomial.IsRoot]
      · intro m hm; rw [hdP] at hm
        by_cases hm0 : m = 0
        · subst hm0; simpa [P] using hmem
        · have h6m : 6 ≠ m := by omega
          simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, hm0, Ne.symm h6m]
      · simpa [P] using hnot_sq
    exact heis.irreducible hatZero hmon.isPrimitive (by rw [hdP]; decide)
  have hmon : univF.Monic := by
    rw [univF_formula]
    have hlt : (Polynomial.C cF5 * Polynomial.X ^ 5 + Polynomial.C cF3 * Polynomial.X ^ 3 +
        Polynomial.C cF1 * Polynomial.X + Polynomial.C cF0).degree < 6 := by compute_degree!
    exact Polynomial.monic_X_pow_add hlt
  let spec5 : Coeff5 →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, 0, Polynomial.X + 1, 0, Polynomial.C Complex.I]
  have hspec : univF.map spec5 = P := by
    have hi2 : (Polynomial.C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
      rw [← Polynomial.C_pow, Complex.I_sq, map_neg, map_one]
    have hi6 : (Polynomial.C Complex.I : Polynomial ℂ) ^ 6 = -1 := by
      calc
        (Polynomial.C Complex.I : Polynomial ℂ) ^ 6 =
            ((Polynomial.C Complex.I : Polynomial ℂ) ^ 2) ^ 3 := by ring
        _ = (-1) ^ 3 := by rw [hi2]
        _ = -1 := by norm_num
    rw [univF_formula]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    have hs5 : spec5 cF5 = 0 := by simp [spec5, cF5]
    have hs3 : spec5 cF3 = 0 := by simp [spec5, cF3]
    have hs1 : spec5 cF1 = 0 := by simp [spec5, cF1]
    have hs0 : spec5 cF0 = sec := by
      have hv0 : spec5 (X 0) = 0 := by simp [spec5]
      have hv1 : spec5 (X 1) = 0 := by simp [spec5]
      have hv2 : spec5 (X 2) = Polynomial.X + 1 := by simp [spec5]
      have hv3 : spec5 (X 3) = 0 := by simp [spec5]
      have hv4 : spec5 (X 4) = Polynomial.C Complex.I := by simp [spec5]
      have hvC : ∀ z : ℂ, spec5 (C z) = Polynomial.C z := fun z => by simp [spec5]
      unfold cF0
      dsimp only [sec]
      simp only [map_add, map_mul, map_pow, hv0, hv1, hv2, hv3, hv4, hvC, hi6]
      ring
    rw [hs5, hs3, hs1, hs0]; simp [P]
  have hu : Irreducible univF :=
    Polynomial.Monic.irreducible_of_irreducible_map spec5 univF hmon (hspec ▸ hP_irred)
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp hu

lemma not_dvd_liftCore {P : CorePoly} (hP : P ≠ 0) : ¬ (F6 ∣ liftCore P) := by
  have hex : ∃ v : Fin 4 → ℂ, eval v P ≠ 0 := by
    by_contra h
    apply hP
    apply MvPolynomial.funext
    intro v
    rw [map_zero]
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  let qPoly : Polynomial ℂ := Polynomial.X ^ 6 + Polynomial.C (eval v core)
  have hq_deg : 0 < qPoly.degree := by
    rw [Polynomial.degree_X_pow_add_C (by decide)]; decide
  obtain ⟨z, hz⟩ := Complex.exists_root hq_deg
  let w : Fin 6 → ℂ := ![v 0, v 1, z, v 2, v 3, 0]
  have hev_core : ∀ R : CorePoly, eval w (liftCore R) = eval v R := by
    intro R
    rw [liftCore, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
    have hw : w ∘ ![0, 1, 3, 4] = v := by ext i; fin_cases i <;> rfl
    rw [hw]
  have hevF : eval w F6 = 0 := by
    rw [targetF_eq, eval_add, hev_core]
    have hevB : eval w (liftBinary binaryB) = z ^ 6 := by
      simp only [liftBinary, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
      simp [binaryB, w]
    rw [hevB]
    rw [Polynomial.IsRoot] at hz
    simp only [qPoly, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hz
    linear_combination hz
  rintro ⟨Q, hQ⟩
  have hev := congrArg (eval w) hQ
  rw [hev_core, eval_mul, hevF, zero_mul] at hev
  exact hv hev

lemma not_dvd_liftBinary : ¬ (F6 ∣ liftBinary binaryB) := by
  let w : Fin 6 → ℂ := ![Complex.I, 0, 1, 0, 0, 0]
  have hi6 : Complex.I ^ 6 = -1 := by
    calc
      Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by rw [← pow_mul]
      _ = -1 := by rw [Complex.I_sq]; norm_num
  have hevF : eval w F6 = 0 := by
    rw [targetF_eq, eval_add]
    simp only [liftCore, liftBinary, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
    simp [core, binaryB, w, hi6]
  have hevB : eval w (liftBinary binaryB) = 1 := by
    simp only [liftBinary, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
    simp [binaryB, w]
  rintro ⟨Q, hQ⟩
  have hev := congrArg (eval w) hQ
  rw [hevB, eval_mul, hevF, zero_mul] at hev
  exact one_ne_zero hev

lemma pderiv_comm6 (i j : Fin 6) (G : SixPoly) :
    pderiv i (pderiv j G) = pderiv j (pderiv i G) := by
  induction G using MvPolynomial.induction_on with
  | C z => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f k hf =>
      have hpi : pderiv i (Pi.single (M := fun _ : Fin 6 => SixPoly) j 1 k) = 0 := by
        by_cases hkj : k = j
        · subst hkj; simp
        · simp [Pi.single_eq_of_ne hkj]
      have hpj : pderiv j (Pi.single (M := fun _ : Fin 6 => SixPoly) i 1 k) = 0 := by
        by_cases hki : k = i
        · subst hki; simp
        · simp [Pi.single_eq_of_ne hki]
      simp only [pderiv_mul, pderiv_X, map_add, hf]
      rw [hpi, hpj]
      ring

lemma residue_eq_normal_sq_mul_divNum
    (S : SixPoly) (N6 : Fin 6 → SixPoly)
    (hdir : ∑ i : Fin 6, pderiv i F6 * N6 i = A6 * S) :
    NormalChart.residue F6 A6 S (fun j => N6 j.succ) =
      NormalChart.normal F6 ^ 2 *
        (S * (∑ i : Fin 6, pderiv i (N6 i)) - ∑ i : Fin 6, pderiv i S * N6 i) := by
  set P : SixPoly := NormalChart.normal F6
  have hP_def : pderiv 0 F6 = P := rfl
  have hP0 : P * N6 0 = A6 * S -
      (pderiv 1 F6 * N6 1 + pderiv 2 F6 * N6 2 + pderiv 3 F6 * N6 3 +
        pderiv 4 F6 * N6 4 + pderiv 5 F6 * N6 5) := by
    have hs := hdir
    simp only [Fin.sum_univ_six, hP_def] at hs
    linear_combination hs
  have hP0_deriv : pderiv 0 P * N6 0 + P * pderiv 0 (N6 0) =
      pderiv 0 A6 * S + A6 * pderiv 0 S -
        ((pderiv 1 P * N6 1 + pderiv 1 F6 * pderiv 0 (N6 1)) +
         (pderiv 2 P * N6 2 + pderiv 2 F6 * pderiv 0 (N6 2)) +
         (pderiv 3 P * N6 3 + pderiv 3 F6 * pderiv 0 (N6 3)) +
         (pderiv 4 P * N6 4 + pderiv 4 F6 * pderiv 0 (N6 4)) +
         (pderiv 5 P * N6 5 + pderiv 5 F6 * pderiv 0 (N6 5))) := by
    have hd := congrArg (pderiv 0) hP0
    simp only [pderiv_mul, map_sub, map_add] at hd
    rw [pderiv_comm6 0 1 F6, pderiv_comm6 0 2 F6, pderiv_comm6 0 3 F6,
        pderiv_comm6 0 4 F6, pderiv_comm6 0 5 F6, hP_def] at hd
    linear_combination hd
  unfold NormalChart.residue
  change S ^ 2 * (P * pderiv 0 A6 - A6 * pderiv 0 P) +
    ∑ j : Fin 5,
      (P ^ 2 * S * pderiv j.succ (N6 j.succ) -
        P * S * pderiv j.succ F6 * pderiv 0 (N6 j.succ) +
        (pderiv j.succ F6 * (S * pderiv 0 P + P * pderiv 0 S) -
          P * (S * pderiv j.succ P + P * pderiv j.succ S)) * N6 j.succ) = _
  simp only [Fin.sum_univ_five, Fin.sum_univ_six]
  dsimp only [Fin.succ]
  change S ^ 2 * (P * pderiv 0 A6 - A6 * pderiv 0 P) +
    ((P ^ 2 * S * pderiv 1 (N6 1) - P * S * pderiv 1 F6 * pderiv 0 (N6 1) +
        (pderiv 1 F6 * (S * pderiv 0 P + P * pderiv 0 S) -
          P * (S * pderiv 1 P + P * pderiv 1 S)) * N6 1) +
     (P ^ 2 * S * pderiv 2 (N6 2) - P * S * pderiv 2 F6 * pderiv 0 (N6 2) +
        (pderiv 2 F6 * (S * pderiv 0 P + P * pderiv 0 S) -
          P * (S * pderiv 2 P + P * pderiv 2 S)) * N6 2) +
     (P ^ 2 * S * pderiv 3 (N6 3) - P * S * pderiv 3 F6 * pderiv 0 (N6 3) +
        (pderiv 3 F6 * (S * pderiv 0 P + P * pderiv 0 S) -
          P * (S * pderiv 3 P + P * pderiv 3 S)) * N6 3) +
     (P ^ 2 * S * pderiv 4 (N6 4) - P * S * pderiv 4 F6 * pderiv 0 (N6 4) +
        (pderiv 4 F6 * (S * pderiv 0 P + P * pderiv 0 S) -
          P * (S * pderiv 4 P + P * pderiv 4 S)) * N6 4) +
     (P ^ 2 * S * pderiv 5 (N6 5) - P * S * pderiv 5 F6 * pderiv 0 (N6 5) +
        (pderiv 5 F6 * (S * pderiv 0 P + P * pderiv 0 S) -
          P * (S * pderiv 5 P + P * pderiv 5 S)) * N6 5)) = _
  linear_combination
    -P * S * hP0_deriv + (S * pderiv 0 P + P * pderiv 0 S) * hP0

theorem bridge_proof
    (D : CorePoly) (N : Fin 4 → CorePoly) (h : CoreCertificate D N) :
    ∃ (S : SixPoly) (W : Fin 5 → SixPoly) (Q : SixPoly),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ IsRelPrime F6 S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      NormalChart.residue F6 A6 S W = F6 * Q := by
  rcases h with ⟨hD_ne, ⟨k, hD_hom, hN_hom⟩, hcore⟩
  let H6 : SixPoly := liftCore core
  let B6 : SixPoly := liftBinary binaryB
  let D_ : SixPoly := liftCore D
  let K : SixPoly := liftCore (coreSource * D - ∑ i, pderiv i core * N i)
  let S : SixPoly := 6 * D_ * H6 * B6
  let N6 : Fin 6 → SixPoly :=
    ![6 * H6 * B6 * liftCore (N 0),
      6 * H6 * B6 * liftCore (N 1),
      H6 * K * X 2,
      6 * H6 * B6 * liftCore (N 2),
      6 * H6 * B6 * liftCore (N 3),
      H6 * K * X 5]
  let Q6 : SixPoly := -24 * D_ * H6 * B6 * K
  have hcore_ne : core ≠ 0 := by
    intro hc; have hev := congrArg (eval ![1, 0, 0, 0]) hc; simp [core] at hev
  have hDC_ne : D * core ≠ 0 := mul_ne_zero hD_ne hcore_ne
  have hndvd_DC : ¬ (F6 ∣ D_ * H6) := by
    rw [show D_ * H6 = liftCore (D * core) from (map_mul _ D core).symm]
    exact not_dvd_liftCore hDC_ne
  have hndvd_6 : ¬ (F6 ∣ (6 : SixPoly)) := by
    rintro ⟨Q, hQ⟩
    have hev := congrArg (eval (0 : Fin 6 → ℂ)) hQ
    have hF0 : eval (0 : Fin 6 → ℂ) F6 = 0 := by
      rw [targetF_eq, eval_add]
      simp only [liftCore, liftBinary, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
      simp [core, binaryB]
    rw [eval_mul, hF0, zero_mul, map_ofNat] at hev
    norm_num at hev
  have hprimeF : Prime F6 :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp F6_irreducible
  have hndvd_S : ¬ (F6 ∣ S) := by
    have h1 : ¬ (F6 ∣ 6 * (D_ * H6)) := fun hd =>
      (hprimeF.dvd_or_dvd hd).elim hndvd_6 hndvd_DC
    have h2 : ¬ (F6 ∣ 6 * (D_ * H6) * B6) := fun hd =>
      (hprimeF.dvd_or_dvd hd).elim h1 not_dvd_liftBinary
    simpa [S, mul_assoc] using h2
  have hS_ne : S ≠ 0 := fun h0 => hndvd_S (h0 ▸ dvd_zero F6)
  have hrelPrime : IsRelPrime F6 S := F6_irreducible.isRelPrime_iff_not_dvd.mpr hndvd_S
  have h6_hom : (6 : SixPoly).IsHomogeneous 0 := by
    rw [← map_ofNat C 6]; exact isHomogeneous_C _ _
  have hH6_hom : H6.IsHomogeneous 6 := liftCore_hom core_hom
  have hB6_hom : B6.IsHomogeneous 6 := liftBinary_hom binaryB_hom
  have hD_hom6 : D_.IsHomogeneous (k + 1) := liftCore_hom hD_hom
  have hS_deg : S.IsHomogeneous (k + 13) := by
    have hm := ((h6_hom.mul hD_hom6).mul hH6_hom).mul hB6_hom
    exact (show 0 + (k + 1) + 6 + 6 = k + 13 by omega) ▸ hm
  have hS_tot : S.totalDegree = k + 13 := hS_deg.totalDegree hS_ne
  have hK_hom : K.IsHomogeneous (k + 7) := by
    apply liftCore_hom
    have hA_hom : coreSource.IsHomogeneous 6 :=
      ((isHomogeneous_X ℂ (0 : Fin 4)).pow 3).mul ((isHomogeneous_X ℂ (2 : Fin 4)).pow 3)
    have ht1 : (coreSource * D).IsHomogeneous (k + 7) :=
      (show 6 + (k + 1) = k + 7 by omega) ▸ hA_hom.mul hD_hom
    have ht2 : (∑ i, pderiv i core * N i).IsHomogeneous (k + 7) := by
      apply IsHomogeneous.sum
      intro i _
      exact (show (6 - 1) + (k + 2) = k + 7 by omega) ▸ (core_hom.pderiv (i := i)).mul (hN_hom i)
    exact ht1.sub ht2
  have hN6_hom : ∀ i : Fin 6, (N6 i).IsHomogeneous (k + 14) := by
    intro i
    fin_cases i
    · change (6 * H6 * B6 * liftCore (N 0)).IsHomogeneous (k + 14)
      exact (show 0 + 6 + 6 + (k + 2) = k + 14 by omega) ▸
        (((h6_hom.mul hH6_hom).mul hB6_hom).mul (liftCore_hom (hN_hom 0)))
    · change (6 * H6 * B6 * liftCore (N 1)).IsHomogeneous (k + 14)
      exact (show 0 + 6 + 6 + (k + 2) = k + 14 by omega) ▸
        (((h6_hom.mul hH6_hom).mul hB6_hom).mul (liftCore_hom (hN_hom 1)))
    · change (H6 * K * X 2).IsHomogeneous (k + 14)
      exact (show 6 + (k + 7) + 1 = k + 14 by omega) ▸
        ((hH6_hom.mul hK_hom).mul (isHomogeneous_X ℂ (2 : Fin 6)))
    · change (6 * H6 * B6 * liftCore (N 2)).IsHomogeneous (k + 14)
      exact (show 0 + 6 + 6 + (k + 2) = k + 14 by omega) ▸
        (((h6_hom.mul hH6_hom).mul hB6_hom).mul (liftCore_hom (hN_hom 2)))
    · change (6 * H6 * B6 * liftCore (N 3)).IsHomogeneous (k + 14)
      exact (show 0 + 6 + 6 + (k + 2) = k + 14 by omega) ▸
        (((h6_hom.mul hH6_hom).mul hB6_hom).mul (liftCore_hom (hN_hom 3)))
    · change (H6 * K * X 5).IsHomogeneous (k + 14)
      exact (show 6 + (k + 7) + 1 = k + 14 by omega) ▸
        ((hH6_hom.mul hK_hom).mul (isHomogeneous_X ℂ (5 : Fin 6)))
  have hEB : liftBinary (pderiv 0 binaryB) * X 2 +
      liftBinary (pderiv 1 binaryB) * X 5 = 6 * B6 := by
    have hE := congrArg liftBinary binaryB_hom.sum_X_mul_pderiv
    simp only [map_add, map_mul, Fin.sum_univ_two, liftBinary_X0,
      liftBinary_X1, nsmul_eq_mul, map_natCast] at hE
    change _ = 6 * liftBinary binaryB
    linear_combination hE
  have hK_def : liftCore (∑ i, pderiv i core * N i) =
      liftCore coreSource * D_ - K := by
    dsimp [K, D_]; rw [map_sub, map_mul]; ring
  have hdir_core : ∀ p : CorePoly,
      liftCore (pderiv 0 p) * liftCore (N 0) +
      liftCore (pderiv 1 p) * liftCore (N 1) +
      liftCore (pderiv 2 p) * liftCore (N 2) +
      liftCore (pderiv 3 p) * liftCore (N 3) =
      liftCore (∑ i, pderiv i p * N i) := by
    intro p; simp only [Fin.sum_univ_four, map_add, map_mul]
  have hpd6 : ∀ j : Fin 6, pderiv j (6 : SixPoly) = 0 := fun j => by
    rw [← map_ofNat C 6, pderiv_C]
  have hN0 : N6 0 = 6 * H6 * B6 * liftCore (N 0) := rfl
  have hN1 : N6 1 = 6 * H6 * B6 * liftCore (N 1) := rfl
  have hN2 : N6 2 = H6 * K * X 2 := rfl
  have hN3 : N6 3 = 6 * H6 * B6 * liftCore (N 2) := rfl
  have hN4 : N6 4 = 6 * H6 * B6 * liftCore (N 3) := rfl
  have hN5 : N6 5 = H6 * K * X 5 := rfl
  have hpK2 : pderiv 2 K = 0 := by dsimp [K]; rw [pderiv_liftCore]; simp
  have hpK5 : pderiv 5 K = 0 := by dsimp [K]; rw [pderiv_liftCore]; simp
  have hdir6 : (∑ i : Fin 6, pderiv i F6 * N6 i) = A6 * S := by
    rw [targetF_eq, targetA_eq]
    simp only [Fin.sum_univ_six, hN0, hN1, hN2, hN3, hN4, hN5]
    dsimp only [S]
    simp only [map_add, pderiv_liftCore, pderiv_liftBinary, Fin.reduceEq, ite_true, ite_false,
      add_zero, zero_add]
    have hdH := hdir_core core
    linear_combination 6 * H6 * B6 * hdH + 6 * H6 * B6 * hK_def + H6 * K * hEB
  have hdiv6 : S * (∑ i : Fin 6, pderiv i (N6 i)) - ∑ i : Fin 6, pderiv i S * N6 i = F6 * Q6 := by
    have hcore_lift : 3 * H6 *
        (D_ * (liftCore (pderiv 0 (N 0)) +
               liftCore (pderiv 1 (N 1)) +
               liftCore (pderiv 2 (N 2)) +
               liftCore (pderiv 3 (N 3))) -
         (liftCore (pderiv 0 D) * liftCore (N 0) +
          liftCore (pderiv 1 D) * liftCore (N 1) +
          liftCore (pderiv 2 D) * liftCore (N 2) +
          liftCore (pderiv 3 D) * liftCore (N 3))) =
        -2 * D_ * K := by
      have h0 := congrArg liftCore hcore
      simp only [Fin.sum_univ_four, map_zero, map_sub, map_add, map_mul, map_pow, map_ofNat] at h0
      dsimp [H6, D_, K]
      simp only [Fin.sum_univ_four, map_sub, map_add, map_mul]
      linear_combination h0
    rw [targetF_eq]
    simp only [Fin.sum_univ_six, hN0, hN1, hN2, hN3, hN4, hN5]
    dsimp only [S, Q6, H6, B6, D_]
    simp only [pderiv_mul, hpd6, hpK2, hpK5, pderiv_liftCore, pderiv_liftBinary, pderiv_X_self,
      Fin.reduceEq, ite_true, ite_false]
    change (6 * liftCore D * liftCore core * liftBinary binaryB) * _ - _ =
      (liftCore core + liftBinary binaryB) *
        (-24 * liftCore D * liftCore core * liftBinary binaryB * K)
    dsimp only [H6, B6, D_] at hcore_lift hEB
    linear_combination
      12 * liftCore core * liftBinary binaryB ^ 2 * hcore_lift -
      6 * liftCore D * liftCore core ^ 2 * K * hEB
  refine ⟨S, fun j => N6 j.succ, NormalChart.normal F6 ^ 2 * Q6,
    hS_ne, hS_tot ▸ hS_deg, hrelPrime, ?_, ?_⟩
  · intro j; rw [hS_tot]; exact hN6_hom j.succ
  · rw [residue_eq_normal_sq_mul_divNum S N6 hdir6, hdiv6]
    ring

end FP2NormalBridge

theorem solution
    (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (h : HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) :
    ∃ (S : HodgeComputer.AmbientPoly HodgeComputer.FourPlusTwoResidual.n)
      (W : Fin 5 → HodgeComputer.AmbientPoly HodgeComputer.FourPlusTwoResidual.n)
      (Q : HodgeComputer.AmbientPoly HodgeComputer.FourPlusTwoResidual.n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧
      IsRelPrime HodgeComputer.FourPlusTwoResidual.F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      HodgeComputer.NormalChart.residue
        HodgeComputer.FourPlusTwoResidual.F
        HodgeComputer.FourPlusTwoResidual.A S W =
        HodgeComputer.FourPlusTwoResidual.F * Q :=
  FP2NormalBridge.bridge_proof D N h
