-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.noOneComponentCertificate
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:43:06.783201+00:00
-- url     : https://prove2.me/submissions/7afa7ffd-9150-4439-9be9-5bb4a6f8e6dc

import Definitions.Def_HodgeComputerFourPlusTwoResidual
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FinCases

open MvPolynomial
open scoped BigOperators

open HodgeComputer
open HodgeComputer.FourPlusTwoResidual

set_option autoImplicit false
noncomputable section

private abbrev P := AmbientPoly 5

private lemma five_div_seven : ((5 : ℂ) * (1 / 7) : ℂ) = 5 / 7 := by norm_num
private lemma ten_div_seven : ((10 : ℂ) * (1 / 7) : ℂ) = 10 / 7 := by norm_num
private lemma fifteen_div_seven : ((15 : ℂ) * (1 / 7) : ℂ) = 15 / 7 := by norm_num

private lemma pack_ofNat (n : ℕ) (p : P) {c : ℂ}
    (hcast : (OfNat.ofNat n : P) = C (n : ℂ))
    (hc : (n : ℂ) * (1 / 7 : ℂ) = c) :
    (OfNat.ofNat n : P) * p * C (1 / 7 : ℂ) = C c * p := by
  rw [hcast, mul_assoc, mul_comm p, ← mul_assoc, ← C_mul, hc]

private lemma pack3_5 (p q : P) :
    (5 : P) * p * q * C (1 / 7 : ℂ) = C (5 / 7 : ℂ) * p * q := by
  rw [mul_assoc (5 : P) p, pack_ofNat 5 (p * q) (C_eq_coe_nat 5).symm five_div_seven, ← mul_assoc]

private lemma pack3_10 (p q : P) :
    (10 : P) * p * q * C (1 / 7 : ℂ) = C (10 / 7 : ℂ) * p * q := by
  rw [mul_assoc (10 : P) p, pack_ofNat 10 (p * q) (C_eq_coe_nat 10).symm ten_div_seven, ← mul_assoc]

private lemma pack3_15 (p q : P) :
    (15 : P) * p * q * C (1 / 7 : ℂ) = C (15 / 7 : ℂ) * p * q := by
  rw [mul_assoc (15 : P) p, pack_ofNat 15 (p * q) (C_eq_coe_nat 15).symm fifteen_div_seven, ← mul_assoc]

private lemma pack5_5 (p q r s : P) :
    (5 : P) * p * q * r * s * C (1 / 7 : ℂ) = C (5 / 7 : ℂ) * p * q * r * s := by
  calc
    (5 : P) * p * q * r * s * C (1 / 7 : ℂ)
        = (5 : P) * (p * q * r * s) * C (1 / 7 : ℂ) := by ring
      _ = C (5 / 7 : ℂ) * (p * q * r * s) :=
        pack_ofNat 5 (p * q * r * s) (C_eq_coe_nat 5).symm five_div_seven
      _ = C (5 / 7 : ℂ) * p * q * r * s := by ring

private lemma pack5_10 (p q r s : P) :
    (10 : P) * p * q * r * s * C (1 / 7 : ℂ) = C (10 / 7 : ℂ) * p * q * r * s := by
  calc
    (10 : P) * p * q * r * s * C (1 / 7 : ℂ)
        = (10 : P) * (p * q * r * s) * C (1 / 7 : ℂ) := by ring
      _ = C (10 / 7 : ℂ) * (p * q * r * s) :=
        pack_ofNat 10 (p * q * r * s) (C_eq_coe_nat 10).symm ten_div_seven
      _ = C (10 / 7 : ℂ) * p * q * r * s := by ring

private lemma F_eq :
    F =
      (X (0 : Fin 6) : P) ^ 6
        + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
        + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
        + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
        + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
        + (X (1 : Fin 6) : P) ^ 6
        + (X (2 : Fin 6) : P) ^ 6
        + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
        + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
        + (X (3 : Fin 6) : P) ^ 6
        + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
        + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
        + (X (4 : Fin 6) : P) ^ 6
        + (X (5 : Fin 6) : P) ^ 6 := by
  unfold F n
  rw [pack3_5 (X (0 : Fin 6) ^ 5) (X 1)]
  rw [pack5_5 (X (0 : Fin 6) ^ 3) (X 1) (X 3) (X 4)]
  rw [pack3_10 (X (0 : Fin 6)) (X 1 ^ 5)]
  rw [pack5_10 (X (0 : Fin 6)) (X 1) (X 3 ^ 3) (X 4)]
  rw [pack3_15 (X (2 : Fin 6) ^ 4) (X 5 ^ 2)]
  rw [pack3_10 (X (2 : Fin 6) ^ 2) (X 5 ^ 4)]
  rw [pack3_5 (X (3 : Fin 6) ^ 5) (X 4)]
  rw [pack3_15 (X (3 : Fin 6)) (X 4 ^ 5)]

private lemma A_eq : A = (X (0 : Fin 6) : P) ^ 3 * X (3 : Fin 6) ^ 3 := by
  unfold A n
  rfl

set_option maxHeartbeats 400000

private lemma directional_oneComponent {M : P} {N : Fin 6 → P}
    (i : Fin 6) (hN : ∀ j : Fin 6, j ≠ i → N j = 0) :
    directional (n := 5) M N = pderiv i M * N i := by
  unfold directional
  refine (Finset.sum_eq_single (a := i) (fun j _ hj => ?_) (fun hi => ?_)).trans ?_
  · rw [hN j hj, mul_zero]
  · exact (hi (Finset.mem_univ i)).elim
  · rfl

private lemma divergence_oneComponent {N : Fin 6 → P}
    (i : Fin 6) (hN : ∀ j : Fin 6, j ≠ i → N j = 0) :
    divergence (n := 5) N = pderiv i (N i) := by
  unfold divergence
  refine (Finset.sum_eq_single (a := i) (fun j _ hj => ?_) (fun hi => ?_)).trans ?_
  · rw [hN j hj, map_zero]
  · exact (hi (Finset.mem_univ i)).elim
  · rfl

private lemma one_component_defect (f a D : P) (N : Fin 6 → P)
    (i : Fin 6) (hN : ∀ j : Fin 6, j ≠ i → N j = 0) :
    defect (n := 5) f a D 1 N =
      a * D ^ 2 - D * pderiv i f * N i + f * (D * pderiv i (N i) - pderiv i D * N i) := by
  unfold defect divergenceNumerator
  have hq : ((1 : ℕ) : P) = 1 := Nat.cast_one
  rw [hq, one_mul, directional_oneComponent (M := f) i hN,
    directional_oneComponent (M := D) i hN, divergence_oneComponent i hN]
  ring

private lemma pderiv_sq (i : Fin 6) (D : P) :
    pderiv i (D ^ 2) = (2 : P) * D * pderiv i D := by
  rw [pderiv_pow, pow_one, Nat.cast_ofNat]

private lemma pderiv_mul3 (i : Fin 6) (f g h : P) :
    pderiv i (f * g * h) =
      pderiv i f * g * h + f * pderiv i g * h + f * g * pderiv i h := by
  simp only [pderiv_mul]
  ring

/-- The one-component obstruction polynomial \(C_u = A_u F_u - A F_{uu}\). -/
private def Cu (f a : P) (i : Fin 6) : P :=
  pderiv i a * pderiv i f - a * pderiv i (pderiv i f)

private lemma oneComponent_cleared (f a D : P) (N : Fin 6 → P) (Q : P)
    (i : Fin 6) (hid : defect (n := 5) f a D 1 N = f ^ 2 * Q)
    (hN : ∀ j : Fin 6, j ≠ i → N j = 0) :
    a * D ^ 2 - pderiv i f * N i * D
      = f * (f * Q - (D * pderiv i (N i) - pderiv i D * N i)) := by
  have hident :
      a * D ^ 2 - D * pderiv i f * N i + f * (D * pderiv i (N i) - pderiv i D * N i) = f ^ 2 * Q := by
    simpa [one_component_defect f a D N i hN] using hid
  calc
    a * D ^ 2 - pderiv i f * N i * D
        = a * D ^ 2 - D * pderiv i f * N i := by ring
      _ = (a * D ^ 2 - D * pderiv i f * N i + f * (D * pderiv i (N i) - pderiv i D * N i))
            - f * (D * pderiv i (N i) - pderiv i D * N i) := by ring
      _ = f ^ 2 * Q - f * (D * pderiv i (N i) - pderiv i D * N i) := by rw [hident]
      _ = f * (f * Q - (D * pderiv i (N i) - pderiv i D * N i)) := by ring

private lemma oneComponent_div_W (f a D Ni : P) (i : Fin 6) (S : P)
    (hS : a * D ^ 2 - pderiv i f * Ni * D = f * S)
    (Q : P)
    (hSdef : S = f * Q - (D * pderiv i Ni - pderiv i D * Ni)) :
    f ∣ pderiv i a * D ^ 2 + (2 : P) * a * D * pderiv i D
      - pderiv i (pderiv i f) * Ni * D - (2 : P) * pderiv i f * Ni * pderiv i D := by
  have hderiv :
      pderiv i (a * D ^ 2) - pderiv i (pderiv i f * Ni * D)
        = pderiv i f * S + f * pderiv i S := by
    have h := ((pderiv i).map_sub (a * D ^ 2) (pderiv i f * Ni * D)).symm
    -- h : pderiv (a D²) - pderiv (f_i Ni D) = pderiv (a D² - f_i Ni D)
    have h' : pderiv i (a * D ^ 2) - pderiv i (pderiv i f * Ni * D) = pderiv i (f * S) := by
      simpa [hS] using h
    rw [h', pderiv_mul]
  have hAL : pderiv i (a * D ^ 2) = pderiv i a * D ^ 2 + a * ((2 : P) * D * pderiv i D) := by
    rw [pderiv_mul, pderiv_sq]
  have hAR : pderiv i (pderiv i f * Ni * D) =
      pderiv i (pderiv i f) * Ni * D + pderiv i f * pderiv i Ni * D
        + pderiv i f * Ni * pderiv i D :=
    pderiv_mul3 i (pderiv i f) Ni D
  refine ⟨pderiv i S + pderiv i f * Q, ?_⟩
  calc
    pderiv i a * D ^ 2 + (2 : P) * a * D * pderiv i D
        - pderiv i (pderiv i f) * Ni * D - (2 : P) * pderiv i f * Ni * pderiv i D
        = (pderiv i (a * D ^ 2) - pderiv i (pderiv i f * Ni * D))
            + pderiv i f * pderiv i Ni * D - pderiv i f * Ni * pderiv i D := by
          rw [hAL, hAR]; ring
      _ = pderiv i f * S + f * pderiv i S
            + pderiv i f * pderiv i Ni * D - pderiv i f * Ni * pderiv i D := by
          rw [hderiv]
      _ = pderiv i f * (f * Q - (D * pderiv i Ni - pderiv i D * Ni))
            + f * pderiv i S
            + pderiv i f * pderiv i Ni * D - pderiv i f * Ni * pderiv i D := by
          rw [hSdef]
      _ = f * (pderiv i S + pderiv i f * Q) := by ring

private lemma oneComponent_div_step2 (f a D Ni : P) (i : Fin 6) (S : P)
    (hS : a * D ^ 2 - pderiv i f * Ni * D = f * S)
    (hW : f ∣ pderiv i a * D ^ 2 + (2 : P) * a * D * pderiv i D
      - pderiv i (pderiv i f) * Ni * D - (2 : P) * pderiv i f * Ni * pderiv i D) :
    f ∣ pderiv i a * D ^ 3 - pderiv i (pderiv i f) * Ni * D ^ 2 := by
  have hWD : f ∣ (pderiv i a * D ^ 2 + (2 : P) * a * D * pderiv i D
      - pderiv i (pderiv i f) * Ni * D - (2 : P) * pderiv i f * Ni * pderiv i D) * D :=
    dvd_mul_of_dvd_left hW D
  have hcancel : f ∣ (a * D ^ 2 - pderiv i f * Ni * D) * ((2 : P) * pderiv i D) :=
    dvd_mul_of_dvd_left ⟨S, hS⟩ _
  have hdiffexpr :
      (pderiv i a * D ^ 2 + (2 : P) * a * D * pderiv i D
        - pderiv i (pderiv i f) * Ni * D - (2 : P) * pderiv i f * Ni * pderiv i D) * D
        - (a * D ^ 2 - pderiv i f * Ni * D) * ((2 : P) * pderiv i D)
      = pderiv i a * D ^ 3 - pderiv i (pderiv i f) * Ni * D ^ 2 := by
    ring
  have := dvd_sub hWD hcancel
  rwa [hdiffexpr] at this

private lemma oneComponent_div_Cu (f a D Ni : P) (i : Fin 6) (S : P)
    (hS : a * D ^ 2 - pderiv i f * Ni * D = f * S)
    (h2 : f ∣ pderiv i a * D ^ 3 - pderiv i (pderiv i f) * Ni * D ^ 2) :
    f ∣ Cu f a i * D ^ 3 := by
  have h1 : f ∣ (pderiv i a * D ^ 3 - pderiv i (pderiv i f) * Ni * D ^ 2) * pderiv i f :=
    dvd_mul_of_dvd_left h2 _
  have h2' : f ∣ (a * D ^ 2 - pderiv i f * Ni * D) * (pderiv i (pderiv i f) * D) :=
    dvd_mul_of_dvd_left ⟨S, hS⟩ _
  have hdiffexpr :
      (pderiv i a * D ^ 3 - pderiv i (pderiv i f) * Ni * D ^ 2) * pderiv i f
        - (a * D ^ 2 - pderiv i f * Ni * D) * (pderiv i (pderiv i f) * D)
      = Cu f a i * D ^ 3 := by
    simp only [Cu]
    ring
  have := dvd_sub h1 h2'
  rwa [hdiffexpr] at this

private lemma dvd_Cu_of_oneComponent (f a D : P) (N : Fin 6 → P) (Q : P)
    (i : Fin 6) (hid : defect (n := 5) f a D 1 N = f ^ 2 * Q)
    (hlegal : IsRelPrime f D) (hN : ∀ j : Fin 6, j ≠ i → N j = 0) :
    f ∣ Cu f a i := by
  set Ni := N i
  set S : P := f * Q - (D * pderiv i Ni - pderiv i D * Ni)
  have hS : a * D ^ 2 - pderiv i f * Ni * D = f * S :=
    oneComponent_cleared f a D N Q i hid hN
  have hW := oneComponent_div_W f a D Ni i S hS Q rfl
  have h2 := oneComponent_div_step2 f a D Ni i S hS hW
  have h3 := oneComponent_div_Cu f a D Ni i S hS h2
  have hpow : IsRelPrime f (D ^ 3) := hlegal.pow_right
  exact hpow.dvd_of_dvd_mul_right (by simpa [mul_comm] using h3)


/-! Explicit derivatives of `A` and `F`, and non-divisibility of each `C_u`. -/

private lemma pderiv_A_0 :
    pderiv (0 : Fin 6) (X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 3) =
      (3 : P) * X (0 : Fin 6) ^ 2 * X (3 : Fin 6) ^ 3 := by
  rw [pderiv_mul, pderiv_pow, pderiv_X_self, pderiv_pow,
    pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 0)]
  simp [Nat.cast_ofNat]

private lemma A_as : (A : P) = X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 3 := by
  delta A n; rfl

private lemma pderiv_A_0' : pderiv (0 : Fin 6) (A : P) =
    (3 : P) * X (0 : Fin 6) ^ 2 * X (3 : Fin 6) ^ 3 := by
  erw [A_as]; exact pderiv_A_0

private lemma pderiv_A_3 :
    pderiv (3 : Fin 6) (X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 3) =
      (3 : P) * X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 2 := by
  rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 3),
    pderiv_pow, pderiv_X_self]
  simp [Nat.cast_ofNat]
  ring

private lemma pderiv_A_3' : pderiv (3 : Fin 6) (A : P) =
    (3 : P) * X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 2 := by
  erw [A_as]; exact pderiv_A_3

private lemma pderiv_A_of_ne_aux {i : Fin 6} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    pderiv i (X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 3 : P) = 0 := by
  rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne h0.symm, pderiv_pow, pderiv_X_of_ne h3.symm]
  simp

private lemma pderiv_A_of_ne {i : Fin 6} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    pderiv i (A : P) = 0 := by
  erw [A_as]; exact pderiv_A_of_ne_aux h0 h3

private lemma pderiv_X_pow_self (i : Fin 6) (k : ℕ) :
    pderiv i ((X i : P) ^ k) = (k : P) * X i ^ (k - 1) := by
  rw [pderiv_pow, pderiv_X_self, mul_one]

private lemma pderiv_X_pow_of_ne {i j : Fin 6} (h : j ≠ i) (k : ℕ) :
    pderiv i ((X j : P) ^ k) = 0 := by
  rw [pderiv_pow, pderiv_X_of_ne h, mul_zero]

private lemma pderiv_C_mul' (c : ℂ) (p : P) (i : Fin 6) :
    pderiv i (C c * p) = C c * pderiv i p := pderiv_C_mul


private def specVal (i j : Fin 6) : ℂ :=
  if j = i then 0
  else if i ≠ 2 ∧ i ≠ 5 then (if j = 2 then 1 else 0)
  else (if j = 0 then 1 else 0)

private def spec (i : Fin 6) : P →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun j : Fin 6 => if j = i then Polynomial.X else Polynomial.C (specVal i j))

private lemma spec_X (i j : Fin 6) :
    spec i (X j : P) = if j = i then Polynomial.X else Polynomial.C (specVal i j) := by
  simp [spec]

private lemma spec_pderiv (i : Fin 6) (p : P) :
    spec i (pderiv i p) = Polynomial.derivative (spec i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [spec, Polynomial.derivative_C]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hpderiv : pderiv i (p * X j) = pderiv i p * X j + p * pderiv i (X j) := pderiv_mul
    rw [hpderiv, map_add, map_mul, map_mul, hp, spec_X]
    have hX : Polynomial.derivative (spec i (X j : P)) = spec i (pderiv i (X j)) := by
      rw [spec_X]
      by_cases h : j = i
      · subst h
        simp [map_one, Polynomial.derivative_X]
      · simp [pderiv_X_of_ne h, h, Polynomial.derivative_C, map_zero]
    have hprod : Polynomial.derivative (spec i (p * X j)) =
        Polynomial.derivative (spec i p) * spec i (X j) + spec i p * Polynomial.derivative (spec i (X j)) := by
      rw [map_mul, Polynomial.derivative_mul]
    rw [hprod, hX, spec_X]

private lemma spec_Cu (i : Fin 6) (f a : P) :
    spec i (Cu f a i) =
      Polynomial.derivative (spec i a) * Polynomial.derivative (spec i f)
        - spec i a * Polynomial.derivative (Polynomial.derivative (spec i f)) := by
  simp only [Cu, map_sub, map_mul, spec_pderiv]


private lemma five_div_seven_ne : (5 / 7 : ℂ) ≠ 0 := by norm_num
private lemma ten_div_seven_ne : (10 / 7 : ℂ) ≠ 0 := by norm_num
private lemma fifteen_div_seven_ne : (15 / 7 : ℂ) ≠ 0 := by norm_num
private lemma C_five_ne : (C (5 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr five_div_seven_ne
private lemma C_ten_ne : (C (10 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr ten_div_seven_ne
private lemma C_fifteen_ne : (C (15 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr fifteen_div_seven_ne

private lemma X_pow_ne (i : Fin 6) (k : ℕ) : ((X i : P) ^ k) ≠ 0 :=
  pow_ne_zero k (X_ne_zero (R := ℂ) i)

private lemma deg_C_mul {c : ℂ} (hc : c ≠ 0) {p : P} (hp : p ≠ 0) (i : Fin 6) :
    degreeOf i (C c * p) = degreeOf i p := by
  rw [degreeOf_mul_eq (C_eq_zero.not.mpr hc) hp, degreeOf_C, zero_add]

private lemma deg_X_pow_self (i : Fin 6) (k : ℕ) :
    degreeOf i ((X i : P) ^ k) = k := by
  rw [degreeOf_pow_eq i (X i : P) k (X_ne_zero (R := ℂ) i), degreeOf_X_self, mul_one]

private lemma monomialA_ne : (X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 3 : P) ≠ 0 :=
  mul_ne_zero (X_pow_ne (0 : Fin 6) 3) (X_pow_ne (3 : Fin 6) 3)

private lemma A_ne : (A : P) ≠ 0 := by
  delta A n
  exact monomialA_ne

/- Specializations used for the `a` and `c` charts. -/
private def val0 : Fin 6 → ℂ :=
  fun j => if j = 2 then 1 else if j = 3 then 1 else 0

private def val3 : Fin 6 → ℂ :=
  fun j => if j = 0 then 1 else if j = 2 then 1 else 0

private def spec0 : P →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun j : Fin 6 => if j = 0 then Polynomial.X else Polynomial.C (val0 j))

private def spec3 : P →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun j : Fin 6 => if j = 3 then Polynomial.X else Polynomial.C (val3 j))

private lemma spec0_pderiv (p : P) :
    spec0 (pderiv (0 : Fin 6) p) = Polynomial.derivative (spec0 p) := by
  -- Reuse the general argument with this particular evaluation map.
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [spec0, Polynomial.derivative_C]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hpderiv : pderiv (0 : Fin 6) (p * X j) =
        pderiv (0 : Fin 6) p * X j + p * pderiv (0 : Fin 6) (X j) := pderiv_mul
    have hX : spec0 (X j : P) = if j = 0 then Polynomial.X else Polynomial.C (val0 j) := by
      simp [spec0]
    have hpd : Polynomial.derivative (spec0 (X j : P)) = spec0 (pderiv (0 : Fin 6) (X j)) := by
      rw [hX]
      by_cases h : j = (0 : Fin 6)
      · subst h
        simp [map_one, Polynomial.derivative_X]
      · simp [pderiv_X_of_ne h, h, Polynomial.derivative_C, map_zero]
    rw [hpderiv, map_add, map_mul, map_mul, hp]
    have hprod : Polynomial.derivative (spec0 (p * X j)) =
        Polynomial.derivative (spec0 p) * spec0 (X j)
          + spec0 p * Polynomial.derivative (spec0 (X j)) := by
      rw [map_mul, Polynomial.derivative_mul]
    rw [hprod, hpd]

private lemma spec3_pderiv (p : P) :
    spec3 (pderiv (3 : Fin 6) p) = Polynomial.derivative (spec3 p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [spec3, Polynomial.derivative_C]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hpderiv : pderiv (3 : Fin 6) (p * X j) =
        pderiv (3 : Fin 6) p * X j + p * pderiv (3 : Fin 6) (X j) := pderiv_mul
    have hpd : Polynomial.derivative (spec3 (X j : P)) = spec3 (pderiv (3 : Fin 6) (X j)) := by
      by_cases h : j = (3 : Fin 6)
      · subst h
        simp [spec3, map_one, Polynomial.derivative_X]
      · simp [spec3, pderiv_X_of_ne h, h, Polynomial.derivative_C, map_zero]
    rw [hpderiv, map_add, map_mul, map_mul, hp]
    have hprod : Polynomial.derivative (spec3 (p * X j)) =
        Polynomial.derivative (spec3 p) * spec3 (X j)
          + spec3 p * Polynomial.derivative (spec3 (X j)) := by
      rw [map_mul, Polynomial.derivative_mul]
    rw [hprod, hpd]



private def Apoly : P := X (0 : Fin 6) ^ 3 * X (3 : Fin 6) ^ 3

private def Fpoly : P :=
  (X (0 : Fin 6) : P) ^ 6
    + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
    + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
    + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
    + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
    + (X (1 : Fin 6) : P) ^ 6
    + (X (2 : Fin 6) : P) ^ 6
    + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
    + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
    + (X (3 : Fin 6) : P) ^ 6
    + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
    + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
    + (X (4 : Fin 6) : P) ^ 6
    + (X (5 : Fin 6) : P) ^ 6

private lemma Apoly_eq : (A : P) = Apoly := by
  delta A n
  rfl

private lemma Fpoly_eq : (F : P) = Fpoly := by
  delta n
  exact F_eq

private lemma coeff_identity :
    Polynomial.C (3 : ℂ) * Polynomial.X ^ 7 * Polynomial.C 6
      - Polynomial.X ^ 7 * Polynomial.C 6 * Polynomial.C 5
      = -12 * Polynomial.X ^ 7 := by
  calc
    Polynomial.C (3 : ℂ) * Polynomial.X ^ 7 * Polynomial.C 6
        - Polynomial.X ^ 7 * Polynomial.C 6 * Polynomial.C 5
        = Polynomial.C (3 : ℂ) * Polynomial.C 6 * Polynomial.X ^ 7
            - Polynomial.C 6 * Polynomial.C 5 * Polynomial.X ^ 7 := by ring
      _ = Polynomial.C ((3 : ℂ) * 6) * Polynomial.X ^ 7
            - Polynomial.C ((6 : ℂ) * 5) * Polynomial.X ^ 7 := by
          rw [← Polynomial.C_mul, ← Polynomial.C_mul]
      _ = Polynomial.C (18 : ℂ) * Polynomial.X ^ 7 - Polynomial.C (30 : ℂ) * Polynomial.X ^ 7 := by
          norm_num
      _ = (Polynomial.C (18 : ℂ) - Polynomial.C (30 : ℂ)) * Polynomial.X ^ 7 := by ring
      _ = Polynomial.C ((18 : ℂ) - 30) * Polynomial.X ^ 7 := by rw [← Polynomial.C_sub]
      _ = Polynomial.C (-12 : ℂ) * Polynomial.X ^ 7 := by norm_num
      _ = -12 * Polynomial.X ^ 7 := by
          have h12 : Polynomial.C (12 : ℂ) = (12 : Polynomial ℂ) :=
            (Polynomial.C_eq_natCast 12).symm
          simp [Polynomial.C_neg, h12]

private lemma spec0_Fpoly : spec0 Fpoly = Polynomial.X ^ 6 + 2 := by
  unfold Fpoly spec0
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp [val0]
  ring

private lemma spec0_Apoly : spec0 Apoly = Polynomial.X ^ 3 := by
  unfold Apoly spec0
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  simp [val0]


private lemma C3_eq : Polynomial.C (3 : ℂ) = (3 : Polynomial ℂ) :=
  (Polynomial.C_eq_natCast 3).symm

private lemma C6_eq : Polynomial.C (6 : ℂ) = (6 : Polynomial ℂ) :=
  (Polynomial.C_eq_natCast 6).symm

private lemma C30_eq : Polynomial.C (30 : ℂ) = (30 : Polynomial ℂ) :=
  (Polynomial.C_eq_natCast 30).symm

private lemma deriv_X3 : Polynomial.derivative (Polynomial.X ^ 3 : Polynomial ℂ) =
    (3 : Polynomial ℂ) * Polynomial.X ^ 2 := by
  rw [Polynomial.derivative_X_pow, Nat.cast_ofNat, C3_eq]

private lemma deriv_X6_add_two :
    Polynomial.derivative (Polynomial.X ^ 6 + 2 : Polynomial ℂ) =
      (6 : Polynomial ℂ) * Polynomial.X ^ 5 := by
  rw [Polynomial.derivative_add, Polynomial.derivative_X_pow, Nat.cast_ofNat, C6_eq]
  have h2 : Polynomial.derivative (2 : Polynomial ℂ) = 0 := by
    have h : (2 : Polynomial ℂ) = Polynomial.C (2 : ℂ) := (Polynomial.C_eq_natCast 2).symm
    rw [h, Polynomial.derivative_C]
  rw [h2, add_zero]

private lemma deriv_six_X5 :
    Polynomial.derivative ((6 : Polynomial ℂ) * Polynomial.X ^ 5) =
      (30 : Polynomial ℂ) * Polynomial.X ^ 4 := by
  rw [← C6_eq, Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Nat.cast_ofNat]
  rw [← mul_assoc, ← Polynomial.C_mul]
  have : (6 : ℂ) * 5 = 30 := by norm_num
  rw [this, C30_eq]

private lemma spec0_Cu_poly :
    spec0 (Cu Fpoly Apoly 0) = -12 * Polynomial.X ^ 7 := by
  unfold Cu
  rw [map_sub, map_mul, map_mul]
  rw [spec0_pderiv Apoly, spec0_pderiv Fpoly, spec0_pderiv ((pderiv 0) Fpoly)]
  rw [spec0_pderiv Fpoly, spec0_Apoly, spec0_Fpoly]
  rw [deriv_X3, deriv_X6_add_two, deriv_six_X5]
  ring

private lemma spec3_Fpoly : spec3 Fpoly = Polynomial.X ^ 6 + 2 := by
  unfold Fpoly spec3
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp [val3]
  ring

private lemma spec3_Apoly : spec3 Apoly = Polynomial.X ^ 3 := by
  unfold Apoly spec3
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  simp [val3]

private lemma spec3_Cu_poly :
    spec3 (Cu Fpoly Apoly 3) = -12 * Polynomial.X ^ 7 := by
  unfold Cu
  rw [map_sub, map_mul, map_mul]
  rw [spec3_pderiv Apoly, spec3_pderiv Fpoly, spec3_pderiv ((pderiv 3) Fpoly)]
  rw [spec3_pderiv Fpoly, spec3_Apoly, spec3_Fpoly]
  rw [deriv_X3, deriv_X6_add_two, deriv_six_X5]
  ring

private lemma two_poly_eq_C : (2 : Polynomial ℂ) = Polynomial.C (2 : ℂ) :=
  (Polynomial.C_eq_natCast 2).symm

private lemma not_dvd_Xpow6_add_two :
    ¬ (Polynomial.X ^ 6 + 2 : Polynomial ℂ) ∣ ((-12 : Polynomial ℂ) * Polynomial.X ^ 7) := by
  intro hdiv
  have hform : (Polynomial.X ^ 6 + 2 : Polynomial ℂ) = Polynomial.X ^ 6 + Polynomial.C (2 : ℂ) := by
    rw [two_poly_eq_C]
  rw [hform] at hdiv
  have hdeg : (Polynomial.X ^ 6 + Polynomial.C (2 : ℂ) : Polynomial ℂ).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_add_C (by decide : (0 : ℕ) < 6)]
    simp
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 6 + Polynomial.C (2 : ℂ) : Polynomial ℂ) hdeg
  have hr0 : r ≠ 0 := by
    intro hz
    have heval : Polynomial.eval r (Polynomial.X ^ 6 + Polynomial.C (2 : ℂ)) = 2 := by
      subst hz
      simp
    have hroot : Polynomial.eval r (Polynomial.X ^ 6 + Polynomial.C (2 : ℂ)) = 0 := hr
    exact (by norm_num : (2 : ℂ) ≠ 0) (heval.symm ▸ hroot)
  have hr6 : r ^ 6 = -2 := by
    have : r ^ 6 + 2 = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] using hr
    linear_combination this
  have hrootC : Polynomial.IsRoot ((-12 : Polynomial ℂ) * Polynomial.X ^ 7) r := hr.dvd hdiv
  have hevalC : Polynomial.eval r ((-12 : Polynomial ℂ) * Polynomial.X ^ 7) = 24 * r := by
    have hr7 : r ^ 7 = r * r ^ 6 := by ring
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hr7, hr6]
    ring
  have hzero : Polynomial.eval r ((-12 : Polynomial ℂ) * Polynomial.X ^ 7) = 0 := hrootC
  have : (24 : ℂ) * r = 0 := hevalC ▸ hzero
  have h24 : (24 : ℂ) ≠ 0 := by norm_num
  exact hr0 (mul_eq_zero.mp this |>.resolve_left h24)


private lemma not_dvd_Cu_0 : ¬ Fpoly ∣ Cu Fpoly Apoly 0 := by
  intro h
  have hspec : spec0 Fpoly ∣ spec0 (Cu Fpoly Apoly 0) := map_dvd spec0 h
  rw [spec0_Fpoly, spec0_Cu_poly] at hspec
  exact not_dvd_Xpow6_add_two hspec

private lemma not_dvd_Cu_3 : ¬ Fpoly ∣ Cu Fpoly Apoly 3 := by
  intro h
  have hspec : spec3 Fpoly ∣ spec3 (Cu Fpoly Apoly 3) := map_dvd spec3 h
  rw [spec3_Fpoly, spec3_Cu_poly] at hspec
  exact not_dvd_Xpow6_add_two hspec

private lemma degreeOf_le_of_dvd {p q : P} (h : p ∣ q) (hq : q ≠ 0) (i : Fin 6) :
    degreeOf i p ≤ degreeOf i q := by
  obtain ⟨r, rfl⟩ := h
  have hp : p ≠ 0 := fun hp => hq (by simp [hp])
  have hr : r ≠ 0 := fun hr => hq (by simp [hr])
  rw [degreeOf_mul_eq hp hr]
  exact Nat.le_add_right _ _

private lemma deg_le_add {i : Fin 6} {p q : P} {k : ℕ}
    (hp : degreeOf i p ≤ k) (hq : degreeOf i q ≤ k) :
    degreeOf i (p + q) ≤ k :=
  (degreeOf_add_le i p q).trans (max_le hp hq)

private lemma deg_pow_X (j : Fin 6) (k : ℕ) (i : Fin 6) :
    degreeOf i ((X j : P) ^ k) ≤ if j = i then k else 0 := by
  by_cases h : j = i
  · subst h
    simp [degreeOf_X_self_pow]
  · rw [degreeOf_X_pow_of_ne k (Ne.symm h)]
    simp [h]

private lemma deg_C_pow (c : ℂ) (j : Fin 6) (k : ℕ) (i : Fin 6) :
    degreeOf i (C c * (X j : P) ^ k) ≤ if j = i then k else 0 :=
  (degreeOf_C_mul_le ((X j : P) ^ k) i c).trans (deg_pow_X j k i)

private lemma deg_C_pow_mul (c : ℂ) (j1 : Fin 6) (k1 : ℕ) (j2 : Fin 6) (k2 : ℕ) (i : Fin 6) :
    degreeOf i (C c * (X j1 : P) ^ k1 * (X j2 : P) ^ k2) ≤
      (if j1 = i then k1 else 0) + (if j2 = i then k2 else 0) :=
  (degreeOf_mul_le i (C c * (X j1 : P) ^ k1) ((X j2 : P) ^ k2)).trans
    (add_le_add (deg_C_pow c j1 k1 i) (deg_pow_X j2 k2 i))

private lemma deg_C_three (c : ℂ) (j1 : Fin 6) (k1 : ℕ) (j2 : Fin 6) (k2 : ℕ)
    (j3 : Fin 6) (k3 : ℕ) (i : Fin 6) :
    degreeOf i (C c * (X j1 : P) ^ k1 * (X j2 : P) ^ k2 * (X j3 : P) ^ k3) ≤
      (if j1 = i then k1 else 0) + (if j2 = i then k2 else 0) + (if j3 = i then k3 else 0) :=
  (degreeOf_mul_le i (C c * (X j1 : P) ^ k1 * (X j2 : P) ^ k2) ((X j3 : P) ^ k3)).trans
    (add_le_add (deg_C_pow_mul c j1 k1 j2 k2 i) (deg_pow_X j3 k3 i))

private lemma deg_C_four (c : ℂ) (j1 : Fin 6) (k1 : ℕ) (j2 : Fin 6) (k2 : ℕ)
    (j3 : Fin 6) (k3 : ℕ) (j4 : Fin 6) (k4 : ℕ) (i : Fin 6) :
    degreeOf i (C c * (X j1 : P) ^ k1 * (X j2 : P) ^ k2 * (X j3 : P) ^ k3 * (X j4 : P) ^ k4) ≤
      (if j1 = i then k1 else 0) + (if j2 = i then k2 else 0)
        + (if j3 = i then k3 else 0) + (if j4 = i then k4 else 0) :=
  (degreeOf_mul_le i
      (C c * (X j1 : P) ^ k1 * (X j2 : P) ^ k2 * (X j3 : P) ^ k3)
      ((X j4 : P) ^ k4)).trans
    (add_le_add (deg_C_three c j1 k1 j2 k2 j3 k3 i) (deg_pow_X j4 k4 i))

private lemma C_eq_nat (k : ℕ) : (k : P) = C (k : ℂ) :=
  (C_eq_coe_nat k).symm

private lemma C2P : (2 : P) = C (2 : ℂ) := by
  have hP : (2 : P) = ((2 : ℕ) : P) := Nat.cast_ofNat.symm
  have hC : (2 : ℂ) = ((2 : ℕ) : ℂ) := Nat.cast_ofNat.symm
  rw [hP, hC]
  exact (C_eq_coe_nat 2).symm
private lemma C3P : (3 : P) = C (3 : ℂ) := by
  have hP : (3 : P) = ((3 : ℕ) : P) := Nat.cast_ofNat.symm
  have hC : (3 : ℂ) = ((3 : ℕ) : ℂ) := Nat.cast_ofNat.symm
  rw [hP, hC]
  exact (C_eq_coe_nat 3).symm
private lemma C4P : (4 : P) = C (4 : ℂ) := by
  have hP : (4 : P) = ((4 : ℕ) : P) := Nat.cast_ofNat.symm
  have hC : (4 : ℂ) = ((4 : ℕ) : ℂ) := Nat.cast_ofNat.symm
  rw [hP, hC]
  exact (C_eq_coe_nat 4).symm
private lemma C5P : (5 : P) = C (5 : ℂ) := by
  have hP : (5 : P) = ((5 : ℕ) : P) := Nat.cast_ofNat.symm
  have hC : (5 : ℂ) = ((5 : ℕ) : ℂ) := Nat.cast_ofNat.symm
  rw [hP, hC]
  exact (C_eq_coe_nat 5).symm
private lemma C6P : (6 : P) = C (6 : ℂ) := by
  have hP : (6 : P) = ((6 : ℕ) : P) := Nat.cast_ofNat.symm
  have hC : (6 : ℂ) = ((6 : ℕ) : ℂ) := Nat.cast_ofNat.symm
  rw [hP, hC]
  exact (C_eq_coe_nat 6).symm
private lemma C30P : (30 : P) = C (30 : ℂ) := by
  have hP : (30 : P) = ((30 : ℕ) : P) := Nat.cast_ofNat.symm
  have hC : (30 : ℂ) = ((30 : ℕ) : ℂ) := Nat.cast_ofNat.symm
  rw [hP, hC]
  exact (C_eq_coe_nat 30).symm

private lemma six_ne : (6 : P) ≠ 0 := by
  rw [C6P, ne_eq, C_eq_zero]; norm_num
private lemma thirty_ne : (30 : P) ≠ 0 := by
  rw [C30P, ne_eq, C_eq_zero]; norm_num
private lemma C200_ne : (C (200 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr (by norm_num)
private lemma C300_ne : (C (300 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr (by norm_num)
private lemma C180_ne : (C (180 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr (by norm_num)
private lemma C20_ne : (C (20 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr (by norm_num)
private lemma C30_over_7_ne : (C (30 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr (by norm_num)
private lemma C120_ne : (C (120 / 7 : ℂ) : P) ≠ 0 := C_eq_zero.not.mpr (by norm_num)

private lemma pderiv_pow6 (i : Fin 6) :
    pderiv i ((X i : P) ^ 6) = (6 : P) * X i ^ 5 := by
  rw [pderiv_X_pow_self, Nat.cast_ofNat]

private lemma pderiv_pow5 (i : Fin 6) :
    pderiv i ((X i : P) ^ 5) = (5 : P) * X i ^ 4 := by
  rw [pderiv_X_pow_self, Nat.cast_ofNat]

private lemma pderiv_pow4 (i : Fin 6) :
    pderiv i ((X i : P) ^ 4) = (4 : P) * X i ^ 3 := by
  rw [pderiv_X_pow_self, Nat.cast_ofNat]

private lemma pderiv_pow3 (i : Fin 6) :
    pderiv i ((X i : P) ^ 3) = (3 : P) * X i ^ 2 := by
  rw [pderiv_X_pow_self, Nat.cast_ofNat]

private lemma pderiv_pow2 (i : Fin 6) :
    pderiv i ((X i : P) ^ 2) = (2 : P) * X i := by
  rw [pderiv_X_pow_self, Nat.cast_ofNat, pow_one]

private lemma six_mul_five : (6 : P) * (5 : P) = (30 : P) := by
  rw [C6P, C5P, C30P, ← C_mul]
  congr 1
  norm_num

private lemma six_mul_X5_pderiv (i : Fin 6) :
    pderiv i ((6 : P) * X i ^ 5) = (30 : P) * X i ^ 4 := by
  rw [C6P, pderiv_C_mul, pderiv_pow5, ← C6P, ← mul_assoc, six_mul_five]

/-! Second partials of `Fpoly` in the four coordinates independent of `A`. -/


private lemma nest_C (a b : ℂ) (p q : P) :
    C a * (p * (C b * q)) = C (a * b) * p * q := by
  calc
    C a * (p * (C b * q)) = C a * C b * p * q := by ring
    _ = C (a * b) * p * q := by rw [← C_mul]

private lemma nest_C3 (a b c : ℂ) (p q : P) :
    C a * (p * (C b * (C c * q))) = C (a * b * c) * p * q := by
  have h : C b * (C c * q) = C (b * c) * q := by
    rw [← mul_assoc, ← C_mul]
  rw [h, nest_C]
  congr 1
  ring

private lemma nest_C_mid (a b c : ℂ) (p q : P) :
    C a * (C b * (C c * p) * q) = C (a * b * c) * p * q := by
  calc
    C a * (C b * (C c * p) * q) = C a * C b * C c * p * q := by ring
    _ = C (a * b * c) * p * q := by rw [← C_mul, ← C_mul]

private lemma nest_C_comm (a b : ℂ) (p : P) :
    C a * (p * C b) = C (a * b) * p := by
  rw [mul_comm p, ← mul_assoc, ← C_mul]

private lemma nest_C_one (a b : ℂ) (q : P) :
    C a * (C b * (1 : P) * q) = C (a * b) * q := by
  rw [mul_one, ← mul_assoc, ← C_mul]

private lemma pderiv2_Fpoly_1 :
    pderiv (1 : Fin 6) (pderiv (1 : Fin 6) Fpoly) =
      (30 : P) * X (1 : Fin 6) ^ 4
        + C (200 / 7 : ℂ) * X (0 : Fin 6) * X (1 : Fin 6) ^ 3 := by
  have hsplit :
      Fpoly =
        (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6)
        + ((X (0 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) := by
    unfold Fpoly
    ring
  have hrest :
      pderiv (1 : Fin 6)
        ((X (0 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) = 0 := by
    simp [map_add, pderiv_C_mul, pderiv_mul, pderiv_pow,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (2 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (5 : Fin 6) ≠ 1)]
  rw [hsplit, map_add, hrest, add_zero]
  -- first derivatives of the b-dependent terms
  have d1 : pderiv (1 : Fin 6) (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1) =
      C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_X_pow_of_ne (by decide : (0 : Fin 6) ≠ 1),
      mul_zero, pderiv_X_self]
    ring
  have d2 : pderiv (1 : Fin 6) (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4) =
      C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 3 * X 4 := by
    rw [pderiv_mul, pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_pow_of_ne (by decide : (0 : Fin 6) ≠ 1),
      pderiv_X_self,
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 1)]
    ring
  have d3 : pderiv (1 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5) =
      C (10 / 7 : ℂ) * X (0 : Fin 6) * ((5 : P) * X (1 : Fin 6) ^ 4) := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 1),
      pderiv_pow5]
    ring
  have d4 : pderiv (1 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4) =
      C (10 / 7 : ℂ) * X (0 : Fin 6) * X 3 ^ 3 * X 4 := by
    rw [pderiv_mul, pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 1),
      pderiv_X_self,
      pderiv_X_pow_of_ne (by decide : (3 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 1)]
    ring
  have d5 : pderiv (1 : Fin 6) ((X (1 : Fin 6) : P) ^ 6) = (6 : P) * X (1 : Fin 6) ^ 5 :=
    pderiv_pow6 1
  have dpart :
      pderiv (1 : Fin 6)
        (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6) =
        C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * ((5 : P) * X (1 : Fin 6) ^ 4)
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 3 ^ 3 * X 4
          + (6 : P) * X (1 : Fin 6) ^ 5 := by
    rw [map_add, map_add, map_add, map_add, d1, d2, d3, d4, d5]
  rw [dpart]
  -- second derivatives: the linear-in-b terms vanish
  have dd1 : pderiv (1 : Fin 6) (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5) = 0 := by
    rw [pderiv_C_mul, pderiv_X_pow_of_ne (by decide : (0 : Fin 6) ≠ 1), mul_zero]
  have dd2 : pderiv (1 : Fin 6) (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 3 * X 4) = 0 := by
    rw [pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_pow_of_ne (by decide : (0 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 1)]
    ring
  have dd3 : pderiv (1 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * ((5 : P) * X (1 : Fin 6) ^ 4)) =
      C (200 / 7 : ℂ) * X (0 : Fin 6) * X (1 : Fin 6) ^ 3 := by
    have hexp :
        pderiv (1 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * ((5 : P) * X (1 : Fin 6) ^ 4)) =
          C (10 / 7 : ℂ) * (X (0 : Fin 6) * (C (5 : ℂ) * (C (4 : ℂ) * X (1 : Fin 6) ^ 3))) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul, pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 1),
        zero_mul, zero_add, C5P, pderiv_C_mul, pderiv_pow4, C4P]
    rw [hexp, nest_C3]
    have hc : (10 / 7 : ℂ) * 5 * 4 = 200 / 7 := by norm_num
    rw [hc]
  have dd4 : pderiv (1 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * X 3 ^ 3 * X 4) = 0 := by
    rw [pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 1),
      pderiv_X_pow_of_ne (by decide : (3 : Fin 6) ≠ 1),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 1)]
    ring
  have dd5 : pderiv (1 : Fin 6) ((6 : P) * X (1 : Fin 6) ^ 5) = (30 : P) * X (1 : Fin 6) ^ 4 :=
    six_mul_X5_pderiv 1
  rw [map_add, map_add, map_add, map_add, dd1, dd2, dd3, dd4, dd5]
  ring

private lemma pderiv2_Fpoly_4 :
    pderiv (4 : Fin 6) (pderiv (4 : Fin 6) Fpoly) =
      (30 : P) * X (4 : Fin 6) ^ 4
        + C (300 / 7 : ℂ) * X (3 : Fin 6) * X (4 : Fin 6) ^ 3 := by
  have hsplit :
      Fpoly =
        (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6)
        + ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + (X (1 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
          + (X (3 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) := by
    unfold Fpoly
    ring
  have hrest :
      pderiv (4 : Fin 6)
        ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + (X (1 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
          + (X (3 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) = 0 := by
    simp [map_add, pderiv_C_mul, pderiv_mul, pderiv_pow,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (2 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (5 : Fin 6) ≠ 4)]
  rw [hsplit, map_add, hrest, add_zero]
  have d1 : pderiv (4 : Fin 6) (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4) =
      C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 := by
    rw [pderiv_mul, pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_pow_of_ne (by decide : (0 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 4),
      pderiv_X_self]
    ring
  have d2 : pderiv (4 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4) =
      C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 := by
    rw [pderiv_mul, pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 4),
      pderiv_X_pow_of_ne (by decide : (3 : Fin 6) ≠ 4),
      pderiv_X_self]
    ring
  have d3 : pderiv (4 : Fin 6) (C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4) =
      C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_X_pow_of_ne (by decide : (3 : Fin 6) ≠ 4),
      pderiv_X_self]
    ring
  have d4 : pderiv (4 : Fin 6) (C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5) =
      C (15 / 7 : ℂ) * X (3 : Fin 6) * ((5 : P) * X (4 : Fin 6) ^ 4) := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 4),
      pderiv_pow5]
    ring
  have d5 : pderiv (4 : Fin 6) ((X (4 : Fin 6) : P) ^ 6) = (6 : P) * X (4 : Fin 6) ^ 5 :=
    pderiv_pow6 4
  have dpart :
      pderiv (4 : Fin 6)
        (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6) =
        C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * ((5 : P) * X (4 : Fin 6) ^ 4)
          + (6 : P) * X (4 : Fin 6) ^ 5 := by
    rw [map_add, map_add, map_add, map_add, d1, d2, d3, d4, d5]
  rw [dpart]
  have dd1 : pderiv (4 : Fin 6) (C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3) = 0 := by
    rw [pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_pow_of_ne (by decide : (0 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 4)]
    ring
  have dd2 : pderiv (4 : Fin 6) (C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3) = 0 := by
    rw [pderiv_mul, pderiv_mul, pderiv_C_mul,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 4),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 4),
      pderiv_X_pow_of_ne (by decide : (3 : Fin 6) ≠ 4)]
    ring
  have dd3 : pderiv (4 : Fin 6) (C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5) = 0 := by
    rw [pderiv_C_mul, pderiv_X_pow_of_ne (by decide : (3 : Fin 6) ≠ 4), mul_zero]
  have dd4 : pderiv (4 : Fin 6) (C (15 / 7 : ℂ) * X (3 : Fin 6) * ((5 : P) * X (4 : Fin 6) ^ 4)) =
      C (300 / 7 : ℂ) * X (3 : Fin 6) * X (4 : Fin 6) ^ 3 := by
    have hexp :
        pderiv (4 : Fin 6) (C (15 / 7 : ℂ) * X (3 : Fin 6) * ((5 : P) * X (4 : Fin 6) ^ 4)) =
          C (15 / 7 : ℂ) * (X (3 : Fin 6) * (C (5 : ℂ) * (C (4 : ℂ) * X (4 : Fin 6) ^ 3))) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul, pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 4),
        zero_mul, zero_add, C5P, pderiv_C_mul, pderiv_pow4, C4P]
    rw [hexp, nest_C3]
    have hc : (15 / 7 : ℂ) * 5 * 4 = 300 / 7 := by norm_num
    rw [hc]
  have dd5 : pderiv (4 : Fin 6) ((6 : P) * X (4 : Fin 6) ^ 5) = (30 : P) * X (4 : Fin 6) ^ 4 :=
    six_mul_X5_pderiv 4
  rw [map_add, map_add, map_add, map_add, dd1, dd2, dd3, dd4, dd5]
  ring

private lemma pderiv2_Fpoly_2 :
    pderiv (2 : Fin 6) (pderiv (2 : Fin 6) Fpoly) =
      (30 : P) * X (2 : Fin 6) ^ 4
        + C (180 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X (5 : Fin 6) ^ 2
        + C (20 / 7 : ℂ) * X (5 : Fin 6) ^ 4 := by
  have hsplit :
      Fpoly =
        ((X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4)
        + ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) := by
    unfold Fpoly
    ring
  have hrest :
      pderiv (2 : Fin 6)
        ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) = 0 := by
    simp [map_add, pderiv_C_mul, pderiv_mul, pderiv_pow,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 2),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 2),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 2),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 2),
      pderiv_X_of_ne (by decide : (5 : Fin 6) ≠ 2)]
  rw [hsplit, map_add, hrest, add_zero]
  have d0 : pderiv (2 : Fin 6) ((X (2 : Fin 6) : P) ^ 6) = (6 : P) * X (2 : Fin 6) ^ 5 :=
    pderiv_pow6 2
  have d1 : pderiv (2 : Fin 6) (C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2) =
      C (15 / 7 : ℂ) * ((4 : P) * X (2 : Fin 6) ^ 3) * X 5 ^ 2 := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_pow4,
      pderiv_X_pow_of_ne (by decide : (5 : Fin 6) ≠ 2)]
    ring
  have d2 : pderiv (2 : Fin 6) (C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4) =
      C (10 / 7 : ℂ) * ((2 : P) * X (2 : Fin 6)) * X 5 ^ 4 := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_pow2,
      pderiv_X_pow_of_ne (by decide : (5 : Fin 6) ≠ 2)]
    ring
  have dpart :
      pderiv (2 : Fin 6)
        ((X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4) =
        (6 : P) * X (2 : Fin 6) ^ 5
          + C (15 / 7 : ℂ) * ((4 : P) * X (2 : Fin 6) ^ 3) * X 5 ^ 2
          + C (10 / 7 : ℂ) * ((2 : P) * X (2 : Fin 6)) * X 5 ^ 4 := by
    rw [map_add, map_add, d0, d1, d2]
  rw [dpart]
  have dd0 : pderiv (2 : Fin 6) ((6 : P) * X (2 : Fin 6) ^ 5) = (30 : P) * X (2 : Fin 6) ^ 4 :=
    six_mul_X5_pderiv 2
  have dd1 : pderiv (2 : Fin 6) (C (15 / 7 : ℂ) * ((4 : P) * X (2 : Fin 6) ^ 3) * X 5 ^ 2) =
      C (180 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X (5 : Fin 6) ^ 2 := by
    have hexp :
        pderiv (2 : Fin 6) (C (15 / 7 : ℂ) * ((4 : P) * X (2 : Fin 6) ^ 3) * X 5 ^ 2) =
          C (15 / 7 : ℂ) * (C (4 : ℂ) * (C (3 : ℂ) * X (2 : Fin 6) ^ 2) * X 5 ^ 2) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul, C4P, pderiv_C_mul, pderiv_pow3,
        pderiv_X_pow_of_ne (by decide : (5 : Fin 6) ≠ 2), mul_zero, add_zero, C3P]
    rw [hexp, nest_C_mid]
    have hc : (15 / 7 : ℂ) * 4 * 3 = 180 / 7 := by norm_num
    rw [hc]
  have dd2 : pderiv (2 : Fin 6) (C (10 / 7 : ℂ) * ((2 : P) * X (2 : Fin 6)) * X 5 ^ 4) =
      C (20 / 7 : ℂ) * X (5 : Fin 6) ^ 4 := by
    have hexp :
        pderiv (2 : Fin 6) (C (10 / 7 : ℂ) * ((2 : P) * X (2 : Fin 6)) * X 5 ^ 4) =
          C (10 / 7 : ℂ) * (C (2 : ℂ) * (1 : P) * X 5 ^ 4) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul, C2P, pderiv_C_mul, pderiv_X_self, mul_one,
        pderiv_X_pow_of_ne (by decide : (5 : Fin 6) ≠ 2), mul_zero, add_zero]
    rw [hexp, nest_C_one]
    have hc : (10 / 7 : ℂ) * 2 = 20 / 7 := by norm_num
    rw [hc]
  rw [map_add, map_add, dd0, dd1, dd2]

private lemma pderiv2_Fpoly_5 :
    pderiv (5 : Fin 6) (pderiv (5 : Fin 6) Fpoly) =
      (30 : P) * X (5 : Fin 6) ^ 4
        + C (120 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X (5 : Fin 6) ^ 2
        + C (30 / 7 : ℂ) * X (2 : Fin 6) ^ 4 := by
  have hsplit :
      Fpoly =
        ((X (5 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4)
        + ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6) := by
    unfold Fpoly
    ring
  have hrest :
      pderiv (5 : Fin 6)
        ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6) = 0 := by
    simp [map_add, pderiv_C_mul, pderiv_mul, pderiv_pow,
      pderiv_X_of_ne (by decide : (0 : Fin 6) ≠ 5),
      pderiv_X_of_ne (by decide : (1 : Fin 6) ≠ 5),
      pderiv_X_of_ne (by decide : (2 : Fin 6) ≠ 5),
      pderiv_X_of_ne (by decide : (3 : Fin 6) ≠ 5),
      pderiv_X_of_ne (by decide : (4 : Fin 6) ≠ 5)]
  rw [hsplit, map_add, hrest, add_zero]
  have d0 : pderiv (5 : Fin 6) ((X (5 : Fin 6) : P) ^ 6) = (6 : P) * X (5 : Fin 6) ^ 5 :=
    pderiv_pow6 5
  have d1 : pderiv (5 : Fin 6) (C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2) =
      C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * ((2 : P) * X (5 : Fin 6)) := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_X_pow_of_ne (by decide : (2 : Fin 6) ≠ 5),
      pderiv_pow2]
    ring
  have d2 : pderiv (5 : Fin 6) (C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4) =
      C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * ((4 : P) * X (5 : Fin 6) ^ 3) := by
    rw [pderiv_mul, pderiv_C_mul, pderiv_X_pow_of_ne (by decide : (2 : Fin 6) ≠ 5),
      pderiv_pow4]
    ring
  have dpart :
      pderiv (5 : Fin 6)
        ((X (5 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4) =
        (6 : P) * X (5 : Fin 6) ^ 5
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * ((2 : P) * X (5 : Fin 6))
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * ((4 : P) * X (5 : Fin 6) ^ 3) := by
    rw [map_add, map_add, d0, d1, d2]
  rw [dpart]
  have dd0 : pderiv (5 : Fin 6) ((6 : P) * X (5 : Fin 6) ^ 5) = (30 : P) * X (5 : Fin 6) ^ 4 :=
    six_mul_X5_pderiv 5
  have dd1 : pderiv (5 : Fin 6) (C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * ((2 : P) * X (5 : Fin 6))) =
      C (30 / 7 : ℂ) * X (2 : Fin 6) ^ 4 := by
    have hexp :
        pderiv (5 : Fin 6) (C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * ((2 : P) * X (5 : Fin 6))) =
          C (15 / 7 : ℂ) * (X (2 : Fin 6) ^ 4 * (C (2 : ℂ) * (1 : P))) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul,
        pderiv_X_pow_of_ne (by decide : (2 : Fin 6) ≠ 5), zero_mul, zero_add,
        C2P, pderiv_C_mul, pderiv_X_self]
    rw [hexp, mul_one, nest_C_comm]
    have hc : (15 / 7 : ℂ) * 2 = 30 / 7 := by norm_num
    rw [hc]
  have dd2 : pderiv (5 : Fin 6) (C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * ((4 : P) * X (5 : Fin 6) ^ 3)) =
      C (120 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X (5 : Fin 6) ^ 2 := by
    have hexp :
        pderiv (5 : Fin 6) (C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * ((4 : P) * X (5 : Fin 6) ^ 3)) =
          C (10 / 7 : ℂ) * (X (2 : Fin 6) ^ 2 * (C (4 : ℂ) * (C (3 : ℂ) * X (5 : Fin 6) ^ 2))) := by
      rw [mul_assoc, pderiv_C_mul, pderiv_mul,
        pderiv_X_pow_of_ne (by decide : (2 : Fin 6) ≠ 5), zero_mul, zero_add,
        C4P, pderiv_C_mul, pderiv_pow3, C3P]
    rw [hexp, nest_C3]
    have hc : (10 / 7 : ℂ) * 4 * 3 = 120 / 7 := by norm_num
    rw [hc]
  rw [map_add, map_add, dd0, dd1, dd2]
  ring



private lemma Cu_eq_neg_A_pderiv2 {i : Fin 6} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    Cu Fpoly Apoly i = -Apoly * pderiv i (pderiv i Fpoly) := by
  unfold Cu Apoly
  rw [pderiv_A_of_ne_aux h0 h3, zero_mul, zero_sub]
  ring

/-- Specializations that keep \(A=a^3c^3\) nonzero: \(a=s=c=1\), and the chart variable free. -/
private def valKeepA (i j : Fin 6) : ℂ :=
  if j = 0 ∨ j = 3 then 1
  else if j = 2 then (if i = 5 then 0 else 1)
  else 0

private def specKeepA (i : Fin 6) : P →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C
    (fun j : Fin 6 => if j = i then Polynomial.X else Polynomial.C (valKeepA i j))

private lemma specKeepA_pderiv (i : Fin 6) (p : P) :
    specKeepA i (pderiv i p) = Polynomial.derivative (specKeepA i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [specKeepA, Polynomial.derivative_C]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p j hp =>
    have hpderiv : pderiv i (p * X j) = pderiv i p * X j + p * pderiv i (X j) := pderiv_mul
    have hX : specKeepA i (X j : P) =
        if j = i then Polynomial.X else Polynomial.C (valKeepA i j) := by
      simp [specKeepA]
    have hpd : Polynomial.derivative (specKeepA i (X j : P)) = specKeepA i (pderiv i (X j)) := by
      rw [hX]
      by_cases h : j = i
      · subst h
        simp [map_one, Polynomial.derivative_X]
      · simp [pderiv_X_of_ne h, h, Polynomial.derivative_C, map_zero]
    rw [hpderiv, map_add, map_mul, map_mul, hp]
    have hprod : Polynomial.derivative (specKeepA i (p * X j)) =
        Polynomial.derivative (specKeepA i p) * specKeepA i (X j)
          + specKeepA i p * Polynomial.derivative (specKeepA i (X j)) := by
      rw [map_mul, Polynomial.derivative_mul]
    rw [hprod, hpd]

private lemma specKeepA_eval_Fpoly (i : Fin 6) :
    specKeepA i Fpoly =
      specKeepA i
        ((X (0 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 5 * X 1
          + C (5 / 7 : ℂ) * X (0 : Fin 6) ^ 3 * X 1 * X 3 * X 4
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 ^ 5
          + C (10 / 7 : ℂ) * X (0 : Fin 6) * X 1 * X 3 ^ 3 * X 4
          + (X (1 : Fin 6) : P) ^ 6
          + (X (2 : Fin 6) : P) ^ 6
          + C (15 / 7 : ℂ) * X (2 : Fin 6) ^ 4 * X 5 ^ 2
          + C (10 / 7 : ℂ) * X (2 : Fin 6) ^ 2 * X 5 ^ 4
          + (X (3 : Fin 6) : P) ^ 6
          + C (5 / 7 : ℂ) * X (3 : Fin 6) ^ 5 * X 4
          + C (15 / 7 : ℂ) * X (3 : Fin 6) * X 4 ^ 5
          + (X (4 : Fin 6) : P) ^ 6
          + (X (5 : Fin 6) : P) ^ 6) := by
  unfold Fpoly
  rfl

private lemma specKeepA_C_eval (i : Fin 6) (c : ℂ) :
    specKeepA i (C c) = Polynomial.C c := by
  simp [specKeepA, coe_eval₂Hom]

private lemma specKeepA_X (i j : Fin 6) :
    specKeepA i (X j : P) = if j = i then Polynomial.X else Polynomial.C (valKeepA i j) := by
  simp [specKeepA]

private lemma not_dvd_degree6_of_le4 {p q : Polynomial ℂ}
    (hp : p.natDegree = 6) (hq : q.natDegree ≤ 4) (hq0 : q ≠ 0) :
    ¬ p ∣ q := by
  intro h
  have hle := Polynomial.natDegree_le_of_dvd h hq0
  rw [hp] at hle
  exact (by decide : ¬ (6 : ℕ) ≤ 4) (hle.trans hq)

private lemma natDegree_X_pow_add_of_lt (p : Polynomial ℂ) (hp : p.natDegree < 6) :
    (Polynomial.X ^ 6 + p).natDegree = 6 := by
  have hX : (Polynomial.X ^ 6 : Polynomial ℂ).natDegree = 6 := by
    simp [Polynomial.natDegree_X_pow]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> simpa [hX]

private lemma specKeepA_Apoly_one {i : Fin 6} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    specKeepA i Apoly = 1 := by
  unfold Apoly
  rw [map_mul, map_pow, map_pow, specKeepA_X, specKeepA_X]
  rw [if_neg h0.symm, if_neg h3.symm]
  simp [valKeepA]

private lemma specKeepA_Fpoly_1 :
    specKeepA (1 : Fin 6) Fpoly =
      Polynomial.X ^ 6 + Polynomial.C (10 / 7 : ℂ) * Polynomial.X ^ 5
        + Polynomial.C (5 / 7 : ℂ) * Polynomial.X + 3 := by
  unfold Fpoly specKeepA valKeepA
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp
  ring

private lemma specKeepA_Fpoly_4 :
    specKeepA (4 : Fin 6) Fpoly =
      Polynomial.X ^ 6 + Polynomial.C (15 / 7 : ℂ) * Polynomial.X ^ 5
        + Polynomial.C (5 / 7 : ℂ) * Polynomial.X + 3 := by
  unfold Fpoly specKeepA valKeepA
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp
  ring

private lemma specKeepA_Fpoly_2 :
    specKeepA (2 : Fin 6) Fpoly = Polynomial.X ^ 6 + 2 := by
  unfold Fpoly specKeepA valKeepA
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp
  ring

private lemma specKeepA_Fpoly_5 :
    specKeepA (5 : Fin 6) Fpoly = Polynomial.X ^ 6 + 2 := by
  unfold Fpoly specKeepA valKeepA
  simp only [coe_eval₂Hom]
  simp_rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp
  ring

private lemma specKeepA_pderiv2_1 :
    specKeepA (1 : Fin 6) (pderiv (1 : Fin 6) (pderiv (1 : Fin 6) Fpoly)) =
      (30 : Polynomial ℂ) * Polynomial.X ^ 4
        + Polynomial.C (200 / 7 : ℂ) * Polynomial.X ^ 3 := by
  rw [pderiv2_Fpoly_1, map_add, map_mul, C30P, specKeepA_C_eval, map_pow, specKeepA_X]
  rw [map_mul, map_mul, specKeepA_C_eval, specKeepA_X, map_pow, specKeepA_X]
  simp [valKeepA, C30_eq]

private lemma specKeepA_pderiv2_4 :
    specKeepA (4 : Fin 6) (pderiv (4 : Fin 6) (pderiv (4 : Fin 6) Fpoly)) =
      (30 : Polynomial ℂ) * Polynomial.X ^ 4
        + Polynomial.C (300 / 7 : ℂ) * Polynomial.X ^ 3 := by
  rw [pderiv2_Fpoly_4, map_add, map_mul, C30P, specKeepA_C_eval, map_pow, specKeepA_X]
  rw [map_mul, map_mul, specKeepA_C_eval, specKeepA_X, map_pow, specKeepA_X]
  simp [valKeepA, C30_eq]

private lemma specKeepA_pderiv2_2 :
    specKeepA (2 : Fin 6) (pderiv (2 : Fin 6) (pderiv (2 : Fin 6) Fpoly)) =
      (30 : Polynomial ℂ) * Polynomial.X ^ 4 := by
  rw [pderiv2_Fpoly_2, map_add, map_add]
  rw [map_mul, C30P, specKeepA_C_eval, map_pow, specKeepA_X]
  rw [map_mul, map_mul, specKeepA_C_eval, map_pow, specKeepA_X, map_pow, specKeepA_X]
  rw [map_mul, specKeepA_C_eval, map_pow, specKeepA_X]
  simp [valKeepA, C30_eq]

private lemma specKeepA_pderiv2_5 :
    specKeepA (5 : Fin 6) (pderiv (5 : Fin 6) (pderiv (5 : Fin 6) Fpoly)) =
      (30 : Polynomial ℂ) * Polynomial.X ^ 4 := by
  rw [pderiv2_Fpoly_5, map_add, map_add]
  rw [map_mul, C30P, specKeepA_C_eval, map_pow, specKeepA_X]
  rw [map_mul, map_mul, specKeepA_C_eval, map_pow, specKeepA_X, map_pow, specKeepA_X]
  rw [map_mul, specKeepA_C_eval, map_pow, specKeepA_X]
  simp [valKeepA, C30_eq]

private lemma specKeepA_Cu_indep {i : Fin 6} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    specKeepA i (Cu Fpoly Apoly i) =
      -specKeepA i (pderiv i (pderiv i Fpoly)) := by
  rw [Cu_eq_neg_A_pderiv2 h0 h3, map_mul, map_neg, specKeepA_Apoly_one h0 h3]
  ring

private lemma natDegree_X6_plus_low3 (c5 c1 : ℂ) :
    (Polynomial.X ^ 6 + Polynomial.C c5 * Polynomial.X ^ 5
      + Polynomial.C c1 * Polynomial.X + 3 : Polynomial ℂ).natDegree = 6 := by
  have hlow :
      (Polynomial.C c5 * Polynomial.X ^ 5 + Polynomial.C c1 * Polynomial.X + 3 :
        Polynomial ℂ).natDegree < 6 := by
    have h1 : (Polynomial.C c5 * Polynomial.X ^ 5 : Polynomial ℂ).natDegree ≤ 5 := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      simp [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have h2 : (Polynomial.C c1 * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
    have h3 : (3 : Polynomial ℂ).natDegree = 0 := by
      have : (3 : Polynomial ℂ) = Polynomial.C (3 : ℂ) := by
        have hP : (3 : Polynomial ℂ) = ((3 : ℕ) : Polynomial ℂ) := Nat.cast_ofNat.symm
        have hC : (3 : ℂ) = ((3 : ℕ) : ℂ) := Nat.cast_ofNat.symm
        rw [hP, hC]
        exact (Polynomial.C_eq_natCast 3).symm
      rw [this, Polynomial.natDegree_C]
    have : (Polynomial.C c5 * Polynomial.X ^ 5 + Polynomial.C c1 * Polynomial.X + 3 :
        Polynomial ℂ).natDegree ≤ 5 := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      apply max_le
      · exact (Polynomial.natDegree_add_le _ _).trans (max_le h1 (h2.trans (by decide : 1 ≤ 5)))
      · exact le_trans (le_of_eq h3) (by decide)
    exact Nat.lt_succ_iff.mpr this
  have hassoc :
      (Polynomial.X ^ 6 + Polynomial.C c5 * Polynomial.X ^ 5
        + Polynomial.C c1 * Polynomial.X + 3 : Polynomial ℂ) =
      Polynomial.X ^ 6 + (Polynomial.C c5 * Polynomial.X ^ 5
        + Polynomial.C c1 * Polynomial.X + 3) := by ring
  rw [hassoc, natDegree_X_pow_add_of_lt _ hlow]

private lemma natDegree_X6_add_two :
    (Polynomial.X ^ 6 + 2 : Polynomial ℂ).natDegree = 6 := by
  have h2 : (2 : Polynomial ℂ).natDegree = 0 := by
    have : (2 : Polynomial ℂ) = Polynomial.C (2 : ℂ) := two_poly_eq_C
    rw [this, Polynomial.natDegree_C]
  exact natDegree_X_pow_add_of_lt 2 (by rw [h2]; decide)

private lemma natDegree_le4_thirty_X4 :
    ((30 : Polynomial ℂ) * Polynomial.X ^ 4).natDegree ≤ 4 := by
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h30 : (30 : Polynomial ℂ).natDegree = 0 := by
    have : (30 : Polynomial ℂ) = Polynomial.C (30 : ℂ) := by
      have hP : (30 : Polynomial ℂ) = ((30 : ℕ) : Polynomial ℂ) := Nat.cast_ofNat.symm
      have hC : (30 : ℂ) = ((30 : ℕ) : ℂ) := Nat.cast_ofNat.symm
      rw [hP, hC]
      exact (Polynomial.C_eq_natCast 30).symm
    rw [this, Polynomial.natDegree_C]
  simp [h30, Polynomial.natDegree_X_pow]

private lemma natDegree_le4_thirty_plus (c : ℂ) :
    ((30 : Polynomial ℂ) * Polynomial.X ^ 4 + Polynomial.C c * Polynomial.X ^ 3).natDegree ≤ 4 := by
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  apply max_le
  · exact natDegree_le4_thirty_X4
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    simp [Polynomial.natDegree_X_pow]

private lemma thirty_X4_ne : ((30 : Polynomial ℂ) * Polynomial.X ^ 4) ≠ 0 := by
  have h30 : (30 : Polynomial ℂ) ≠ 0 := by
    have : (30 : Polynomial ℂ) = Polynomial.C (30 : ℂ) := by
      have hP : (30 : Polynomial ℂ) = ((30 : ℕ) : Polynomial ℂ) := Nat.cast_ofNat.symm
      have hC : (30 : ℂ) = ((30 : ℕ) : ℂ) := Nat.cast_ofNat.symm
      rw [hP, hC]
      exact (Polynomial.C_eq_natCast 30).symm
    rw [this, ne_eq, Polynomial.C_eq_zero]
    norm_num
  exact mul_ne_zero h30 (pow_ne_zero 4 Polynomial.X_ne_zero)

private lemma thirty_plus_ne (c : ℂ) :
    ((30 : Polynomial ℂ) * Polynomial.X ^ 4 + Polynomial.C c * Polynomial.X ^ 3) ≠ 0 := by
  have hdeg :
      ((30 : Polynomial ℂ) * Polynomial.X ^ 4 + Polynomial.C c * Polynomial.X ^ 3).natDegree = 4 := by
    have hL : ((30 : Polynomial ℂ) * Polynomial.X ^ 4).natDegree = 4 := by
      have h30 : (30 : Polynomial ℂ) ≠ 0 := by
        have : (30 : Polynomial ℂ) = Polynomial.C (30 : ℂ) := by
          have hP : (30 : Polynomial ℂ) = ((30 : ℕ) : Polynomial ℂ) := Nat.cast_ofNat.symm
          have hC : (30 : ℂ) = ((30 : ℕ) : ℂ) := Nat.cast_ofNat.symm
          rw [hP, hC]
          exact (Polynomial.C_eq_natCast 30).symm
        rw [this, ne_eq, Polynomial.C_eq_zero]
        norm_num
      rw [Polynomial.natDegree_mul h30 (pow_ne_zero 4 Polynomial.X_ne_zero)]
      have : (30 : Polynomial ℂ).natDegree = 0 := by
        have : (30 : Polynomial ℂ) = Polynomial.C (30 : ℂ) := by
          have hP : (30 : Polynomial ℂ) = ((30 : ℕ) : Polynomial ℂ) := Nat.cast_ofNat.symm
          have hC : (30 : ℂ) = ((30 : ℕ) : ℂ) := Nat.cast_ofNat.symm
          rw [hP, hC]
          exact (Polynomial.C_eq_natCast 30).symm
        rw [this, Polynomial.natDegree_C]
      simp [this, Polynomial.natDegree_X_pow]
    have hR : (Polynomial.C c * Polynomial.X ^ 3).natDegree ≤ 3 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp [Polynomial.natDegree_X_pow])
    have hlt : (Polynomial.C c * Polynomial.X ^ 3).natDegree <
        ((30 : Polynomial ℂ) * Polynomial.X ^ 4).natDegree := by
      rw [hL]
      exact Nat.lt_succ_iff.mpr hR
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hL]
  exact Polynomial.ne_zero_of_natDegree_gt (lt_of_lt_of_eq (by decide : (0 : ℕ) < 4) hdeg.symm)


private lemma not_dvd_Cu_1 : ¬ Fpoly ∣ Cu Fpoly Apoly 1 := by
  intro h
  have hspec : specKeepA (1 : Fin 6) Fpoly ∣ specKeepA (1 : Fin 6) (Cu Fpoly Apoly 1) :=
    map_dvd _ h
  rw [specKeepA_Fpoly_1, specKeepA_Cu_indep (by decide) (by decide), specKeepA_pderiv2_1] at hspec
  have hq0 : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4
      + Polynomial.C (200 / 7 : ℂ) * Polynomial.X ^ 3) : Polynomial ℂ) ≠ 0 :=
    neg_ne_zero.mpr (thirty_plus_ne _)
  have hq : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4
      + Polynomial.C (200 / 7 : ℂ) * Polynomial.X ^ 3) : Polynomial ℂ).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_neg]
    exact natDegree_le4_thirty_plus _
  exact not_dvd_degree6_of_le4 (natDegree_X6_plus_low3 _ _) hq hq0 hspec

private lemma not_dvd_Cu_4 : ¬ Fpoly ∣ Cu Fpoly Apoly 4 := by
  intro h
  have hspec : specKeepA (4 : Fin 6) Fpoly ∣ specKeepA (4 : Fin 6) (Cu Fpoly Apoly 4) :=
    map_dvd _ h
  rw [specKeepA_Fpoly_4, specKeepA_Cu_indep (by decide) (by decide), specKeepA_pderiv2_4] at hspec
  have hq0 : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4
      + Polynomial.C (300 / 7 : ℂ) * Polynomial.X ^ 3) : Polynomial ℂ) ≠ 0 :=
    neg_ne_zero.mpr (thirty_plus_ne _)
  have hq : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4
      + Polynomial.C (300 / 7 : ℂ) * Polynomial.X ^ 3) : Polynomial ℂ).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_neg]
    exact natDegree_le4_thirty_plus _
  exact not_dvd_degree6_of_le4 (natDegree_X6_plus_low3 _ _) hq hq0 hspec

private lemma not_dvd_Cu_2 : ¬ Fpoly ∣ Cu Fpoly Apoly 2 := by
  intro h
  have hspec : specKeepA (2 : Fin 6) Fpoly ∣ specKeepA (2 : Fin 6) (Cu Fpoly Apoly 2) :=
    map_dvd _ h
  rw [specKeepA_Fpoly_2, specKeepA_Cu_indep (by decide) (by decide), specKeepA_pderiv2_2] at hspec
  have hq0 : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4) : Polynomial ℂ) ≠ 0 :=
    neg_ne_zero.mpr thirty_X4_ne
  have hq : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4) : Polynomial ℂ).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_neg]
    exact natDegree_le4_thirty_X4
  exact not_dvd_degree6_of_le4 natDegree_X6_add_two hq hq0 hspec

private lemma not_dvd_Cu_5 : ¬ Fpoly ∣ Cu Fpoly Apoly 5 := by
  intro h
  have hspec : specKeepA (5 : Fin 6) Fpoly ∣ specKeepA (5 : Fin 6) (Cu Fpoly Apoly 5) :=
    map_dvd _ h
  rw [specKeepA_Fpoly_5, specKeepA_Cu_indep (by decide) (by decide), specKeepA_pderiv2_5] at hspec
  have hq0 : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4) : Polynomial ℂ) ≠ 0 :=
    neg_ne_zero.mpr thirty_X4_ne
  have hq : (-((30 : Polynomial ℂ) * Polynomial.X ^ 4) : Polynomial ℂ).natDegree ≤ 4 := by
    rw [Polynomial.natDegree_neg]
    exact natDegree_le4_thirty_X4
  exact not_dvd_degree6_of_le4 natDegree_X6_add_two hq hq0 hspec


private lemma not_dvd_Cu_Fpoly (i : Fin 6) : ¬ Fpoly ∣ Cu Fpoly Apoly i := by
  fin_cases i
  · exact not_dvd_Cu_0
  · exact not_dvd_Cu_1
  · exact not_dvd_Cu_2
  · exact not_dvd_Cu_3
  · exact not_dvd_Cu_4
  · exact not_dvd_Cu_5

set_option maxHeartbeats 2000000

private lemma AmbientPoly_n_eq_P : AmbientPoly n = P := by
  delta n
  rfl

private lemma identity_in_P {D : AmbientPoly n} {N : Fin (n + 1) → AmbientPoly n}
    {Q : AmbientPoly n} (h : defect F A D 1 N = F ^ 2 * Q) :
    defect (n := 5) (F : P) (A : P) (D : P) 1 (fun j : Fin 6 => (N (Fin.cast (by delta n; rfl) j) : P))
      = (F : P) ^ 2 * (Q : P) := by
  delta n
  exact h

private lemma legal_in_P {D : AmbientPoly n} (h : IsRelPrime F D) :
    IsRelPrime (F : P) (D : P) := by
  delta n
  exact h

private lemma oneComponent_in_P {N : Fin (n + 1) → AmbientPoly n} {i : Fin (n + 1)}
    (hN : ∀ j, j ≠ i → N j = 0) :
    ∀ j : Fin 6, j ≠ Fin.cast (by delta n; rfl) i →
      (N (Fin.cast (by delta n; rfl) j) : P) = 0 := by
  delta n
  exact hN

theorem solution :
    ¬ ∃ (i : Fin (n + 1)) (D : AmbientPoly n)
      (N : Fin (n + 1) → AmbientPoly n) (Q : AmbientPoly n),
        Verify F A 6 1 D N Q ∧ ∀ j, j ≠ i → N j = 0 := by
  rintro ⟨i, D, N, Q, hV, hN⟩
  have hid0 : defect F A D 1 N = F ^ 2 * Q := by
    have h := hV.identity
    rw [show (1 + 1 = 2) from rfl] at h
    exact h
  have hid := identity_in_P hid0
  have hdiv : (F : P) ∣ Cu (F : P) (A : P) (Fin.cast (by delta n; rfl) i) :=
    dvd_Cu_of_oneComponent (F : P) (A : P) (D : P)
      (fun j : Fin 6 => (N (Fin.cast (by delta n; rfl) j) : P)) (Q : P)
      (Fin.cast (by delta n; rfl) i) hid (legal_in_P hV.denominator_legal)
      (oneComponent_in_P hN)
  have hdiv' : Fpoly ∣ Cu Fpoly Apoly (Fin.cast (by delta n; rfl) i) := by
    rw [← Fpoly_eq, ← Apoly_eq]
    exact hdiv
  exact not_dvd_Cu_Fpoly _ hdiv'

end
