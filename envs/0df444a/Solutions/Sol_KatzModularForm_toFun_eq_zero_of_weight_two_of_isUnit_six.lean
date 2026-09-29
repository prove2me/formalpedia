-- Prove2me | solution 1 for KatzModularForm.toFun_eq_zero_of_weight_two_of_isUnit_six
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/77aba939-9281-5fd1-86d1-00d73d24cd98

import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six

set_option autoImplicit false

noncomputable section

namespace Sum56K6

open MvPolynomial

def w46 : Fin 2 → ℕ := ![4, 6]

@[scoped simp] theorem w46_zero : w46 0 = 4 := rfl
@[scoped simp] theorem w46_one : w46 1 = 6 := rfl

theorem weight_w46 (d : Fin 2 →₀ ℕ) : Finsupp.weight w46 d = 4 * d 0 + 6 * d 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (w46 i))]
  simp only [Fin.sum_univ_two, w46_zero, w46_one, smul_eq_mul]
  ring

variable {R : Type} [CommRing R]

def D : MvPolynomial (Fin 2) R := C 4 * X 0 ^ 3 + C 27 * X 1 ^ 2

theorem isWeightedHomogeneous_X0_pow (n : ℕ) :
    IsWeightedHomogeneous w46 (X 0 ^ n : MvPolynomial (Fin 2) R) (4 * n) := by
  have h := (isWeightedHomogeneous_X R w46 (0 : Fin 2)).pow n
  rw [w46_zero, smul_eq_mul, mul_comm] at h
  exact h

theorem isWeightedHomogeneous_X1_pow (n : ℕ) :
    IsWeightedHomogeneous w46 (X 1 ^ n : MvPolynomial (Fin 2) R) (6 * n) := by
  have h := (isWeightedHomogeneous_X R w46 (1 : Fin 2)).pow n
  rw [w46_one, smul_eq_mul, mul_comm] at h
  exact h

theorem iso_mono (i j n : ℕ) (h : 4 * i + 6 * j = n) (c : R) :
    IsWeightedHomogeneous w46 (C c * (X 0 ^ i * X 1 ^ j) : MvPolynomial (Fin 2) R) n := by
  have := ((isWeightedHomogeneous_X0_pow (R := R) i).mul
    (isWeightedHomogeneous_X1_pow (R := R) j)).C_mul c
  rwa [h] at this

theorem isWeightedHomogeneous_D : IsWeightedHomogeneous w46 (D : MvPolynomial (Fin 2) R) 12 := by
  have h3 := iso_mono (R := R) 3 0 12 (by norm_num) 4
  have h2 := iso_mono (R := R) 0 2 12 (by norm_num) 27
  rw [pow_zero, mul_one] at h3
  rw [pow_zero, one_mul] at h2
  exact h3.add h2

theorem monomial_fin2 (d : Fin 2 →₀ ℕ) (c : R) :
    monomial d c = C c * (X 0 ^ d 0 * X 1 ^ d 1) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ fun i => pow_zero _, Fin.prod_univ_two]

theorem weightedHomogeneousComponent_mul_left {σ : Type} {w : σ → ℕ} {φ : MvPolynomial σ R}
    {m : ℕ} (hφ : IsWeightedHomogeneous w φ m) (n : ℕ) (ψ : MvPolynomial σ R) :
    weightedHomogeneousComponent w (m + n) (φ * ψ) =
      φ * weightedHomogeneousComponent w n ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl ?_
    rintro ⟨e, f⟩ hef
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hef
    dsimp only
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hf
    · rfl
    · by_cases he : coeff e φ = 0
      · rw [he, zero_mul, zero_mul]
      · exfalso
        apply hf
        have hwe : Finsupp.weight w e = m := hφ he
        have hsum : Finsupp.weight w e + Finsupp.weight w f = m + n := by
          rw [← map_add, hef]
          exact hd
        omega
  · symm
    refine Finset.sum_eq_zero ?_
    rintro ⟨e, f⟩ hef
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hef
    dsimp only
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hf
    · by_cases he : coeff e φ = 0
      · rw [he, zero_mul]
      · exfalso
        apply hd
        rw [← hef, map_add, hφ he, hf]
    · rw [mul_zero]

theorem key_monomial (hu : IsUnit (27 : R)) (N i j : ℕ) (h : 4 * i + 6 * j = 12 * N + 14)
    (c : R) :
    ∃ (Q : MvPolynomial (Fin 2) R) (ρ : R),
      C c * (X 0 ^ i * X 1 ^ j) = D * Q + C ρ * (X 0 ^ (3 * N + 2) * X 1) := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨b, hb⟩ : ∃ b, j = 2 * b + 1 := ⟨j / 2, by omega⟩
  have hi : i + 3 * b = 3 * N + 2 := by omega
  subst hb
  have hX1sq : (X 1 ^ 2 : MvPolynomial (Fin 2) R) = C v * (D - C 4 * X 0 ^ 3) := by
    unfold D
    have h1 : (C v * C 27 : MvPolynomial (Fin 2) R) = 1 := by
      rw [← map_mul, mul_comm, hv, map_one]
    linear_combination (-(X 1 ^ 2 : MvPolynomial (Fin 2) R)) * h1
  obtain ⟨E, hE⟩ :=
    sub_dvd_pow_sub_pow (D - C 4 * X 0 ^ 3 : MvPolynomial (Fin 2) R) (-(C 4 * X 0 ^ 3)) b
  refine ⟨C (c * v ^ b) * (X 0 ^ i * X 1) * E, c * v ^ b * (-4) ^ b, ?_⟩
  have hpow : (X 1 ^ (2 * b + 1) : MvPolynomial (Fin 2) R)
      = X 1 * (C v) ^ b * (D - C 4 * X 0 ^ 3) ^ b := by
    rw [pow_succ, pow_mul, hX1sq, mul_pow]
    ring
  have hX0 : (X 0 ^ (3 * N + 2) : MvPolynomial (Fin 2) R) = X 0 ^ i * (X 0 ^ 3) ^ b := by
    rw [← pow_mul, ← pow_add, hi]
  rw [hpow, hX0]
  simp only [map_mul, map_pow, map_neg]
  linear_combination (C c * (C v) ^ b * (X 0 ^ i * X 1)) * hE

theorem key (hu : IsUnit (27 : R)) (N : ℕ) (P : MvPolynomial (Fin 2) R)
    (hP : IsWeightedHomogeneous w46 P (12 * N + 14)) :
    ∃ (Q : MvPolynomial (Fin 2) R) (ρ : R), IsWeightedHomogeneous w46 Q (12 * N + 2) ∧
      P = D * Q + C ρ * (X 0 ^ (3 * N + 2) * X 1) := by
  classical
  have hmono : ∀ d ∈ P.support, ∃ (Q : MvPolynomial (Fin 2) R) (ρ : R),
      monomial d (coeff d P) = D * Q + C ρ * (X 0 ^ (3 * N + 2) * X 1) := by
    intro d hd
    have hw : 4 * d 0 + 6 * d 1 = 12 * N + 14 := by
      rw [← weight_w46]
      exact hP (mem_support_iff.mp hd)
    obtain ⟨Q, ρ, hQ⟩ := key_monomial hu N (d 0) (d 1) hw (coeff d P)
    exact ⟨Q, ρ, by rw [monomial_fin2]; exact hQ⟩
  choose! Qf ρf hQρ using hmono
  have hsum : P = D * (∑ d ∈ P.support, Qf d)
      + C (∑ d ∈ P.support, ρf d) * (X 0 ^ (3 * N + 2) * X 1) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hQρ
  have hm : IsWeightedHomogeneous w46
      (C (∑ d ∈ P.support, ρf d) * (X 0 ^ (3 * N + 2) * X 1) : MvPolynomial (Fin 2) R)
      (12 * N + 14) := by
    have := iso_mono (R := R) (3 * N + 2) 1 (12 * N + 14) (by ring) (∑ d ∈ P.support, ρf d)
    rwa [pow_one] at this
  have hiso : IsWeightedHomogeneous w46
      (P - C (∑ d ∈ P.support, ρf d) * (X 0 ^ (3 * N + 2) * X 1)) (12 * N + 14) :=
    (weightedHomogeneousSubmodule R w46 _).sub_mem hP hm
  have hDQ : D * (∑ d ∈ P.support, Qf d)
      = P - C (∑ d ∈ P.support, ρf d) * (X 0 ^ (3 * N + 2) * X 1) := by
    linear_combination (-1 : MvPolynomial (Fin 2) R) * hsum
  have hc := weightedHomogeneousComponent_mul_left (isWeightedHomogeneous_D (R := R))
    (12 * N + 2) (∑ d ∈ P.support, Qf d)
  rw [hDQ, show 12 + (12 * N + 2) = 12 * N + 14 by ring,
    hiso.weightedHomogeneousComponent_same] at hc
  exact ⟨weightedHomogeneousComponent w46 (12 * N + 2) (∑ d ∈ P.support, Qf d),
    ∑ d ∈ P.support, ρf d, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
    by linear_combination hc⟩

theorem eq_zero_of_iso_two (P : MvPolynomial (Fin 2) R) (hP : IsWeightedHomogeneous w46 P 2) :
    P = 0 := by
  ext d
  rw [coeff_zero]
  by_contra h
  have := hP h
  rw [weight_w46] at this
  omega

theorem aeval_eq_zero_of_dvd (hu : IsUnit (27 : R)) {T : Type} [CommRing T] [Algebra R T]
    (q α β e : T) (hα : IsUnit α) (hβ : IsUnit β) (he : IsUnit e)
    (hD : aeval ![α, β] (D : MvPolynomial (Fin 2) R) = q * e)
    (hq : ∀ x : T, q * x = 0 → x = 0) (hC : ∀ r : R, q ∣ algebraMap R T r → r = 0) :
    ∀ (N : ℕ) (P : MvPolynomial (Fin 2) R), IsWeightedHomogeneous w46 P (12 * N + 2) →
      q ^ N ∣ aeval ![α, β] P → P = 0 := by
  intro N
  induction N with
  | zero =>
    intro P hP _
    exact eq_zero_of_iso_two P hP
  | succ N ih =>
    intro P hP hdvd
    have hP' : IsWeightedHomogeneous w46 P (12 * N + 14) := by
      rwa [show 12 * (N + 1) + 2 = 12 * N + 14 by ring] at hP
    obtain ⟨Q, ρ, hQ, hPQ⟩ := key hu N P hP'
    have hevP : aeval ![α, β] P
        = q * e * aeval ![α, β] Q + algebraMap R T ρ * (α ^ (3 * N + 2) * β) := by
      rw [hPQ]
      simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, hD]
    have h1 : q ∣ algebraMap R T ρ * (α ^ (3 * N + 2) * β) := by
      have hqP : q ∣ aeval ![α, β] P := dvd_trans (dvd_pow_self q (Nat.succ_ne_zero N)) hdvd
      rw [hevP] at hqP
      exact (dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_right q e) _)).mp hqP
    have hρ : ρ = 0 := hC ρ (((hα.pow _).mul hβ).dvd_mul_right.mp h1)
    rw [hρ, map_zero, zero_mul, add_zero] at hevP
    obtain ⟨z, hz⟩ := hdvd
    have hx : q * e * aeval ![α, β] Q = q ^ (N + 1) * z := hevP.symm.trans hz
    have hcancel : e * aeval ![α, β] Q = q ^ N * z := by
      refine sub_eq_zero.mp (hq _ ?_)
      linear_combination hx
    obtain ⟨ei, hei⟩ := he.exists_left_inv
    have h3 : q ^ N ∣ aeval ![α, β] Q :=
      ⟨ei * z, by linear_combination (-(aeval ![α, β] Q)) * hei + ei * hcancel⟩
    rw [hPQ, ih Q hQ h3, hρ, map_zero, mul_zero, zero_mul, add_zero]

theorem isUnit_two_mul_three (h6 : IsUnit (6 : R)) : IsUnit ((2 : R) * 3) := by
  norm_num
  exact h6

theorem isUnit_two (h6 : IsUnit (6 : R)) : IsUnit (2 : R) :=
  isUnit_of_mul_isUnit_left (isUnit_two_mul_three h6)

theorem isUnit_three (h6 : IsUnit (6 : R)) : IsUnit (3 : R) :=
  isUnit_of_mul_isUnit_right (isUnit_two_mul_three h6)

theorem isUnit_twentyseven (h6 : IsUnit (6 : R)) : IsUnit (27 : R) := by
  have h := (isUnit_three h6).pow 3
  norm_num at h
  exact h

theorem isUnit_sixteen {A : Type} [CommRing A] [Algebra R A] (h6 : IsUnit (6 : R)) :
    IsUnit (16 : A) := by
  have h := ((isUnit_two h6).map (algebraMap R A)).pow 4
  rw [map_ofNat] at h
  norm_num at h
  exact h

theorem Δ_of_short {A : Type} [CommRing A] (W : WeierstrassCurve A) (h1 : W.a₁ = 0)
    (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h1, h2, h3]
  ring

theorem aeval_D {A : Type} [CommRing A] [Algebra R A] (f : Fin 2 → A) :
    aeval f (D : MvPolynomial (Fin 2) R) = 4 * f 0 ^ 3 + 27 * f 1 ^ 2 := by
  simp only [D, map_add, map_mul, map_pow, MvPolynomial.aeval_X, map_ofNat]

variable (R)

def WS : WeierstrassCurve (MvPolynomial (Fin 2) R) := ⟨0, 0, 0, X 0, X 1⟩

@[scoped simp] theorem WS_a₁ : (WS R).a₁ = 0 := rfl
@[scoped simp] theorem WS_a₂ : (WS R).a₂ = 0 := rfl
@[scoped simp] theorem WS_a₃ : (WS R).a₃ = 0 := rfl
@[scoped simp] theorem WS_a₄ : (WS R).a₄ = X 0 := rfl
@[scoped simp] theorem WS_a₆ : (WS R).a₆ = X 1 := rfl

theorem WS_Δ : (WS R).Δ = -16 * D := by
  rw [Δ_of_short (WS R) rfl rfl rfl]
  simp only [WS_a₄, WS_a₆, D, map_ofNat]

abbrev L : Type := Localization.Away (D : MvPolynomial (Fin 2) R)

def WSL : WeierstrassCurve (L R) := (WS R).map (algebraMap (MvPolynomial (Fin 2) R) (L R))

theorem isUnit_algebraMap_D : IsUnit (algebraMap (MvPolynomial (Fin 2) R) (L R) D) :=
  IsLocalization.Away.algebraMap_isUnit D

theorem WSL_Δ_isUnit (h6 : IsUnit (6 : R)) : IsUnit (WSL R).Δ := by
  rw [WSL, WeierstrassCurve.map_Δ, WS_Δ, map_mul, map_neg, map_ofNat]
  exact (isUnit_sixteen (A := L R) h6).neg.mul (isUnit_algebraMap_D R)

def gS (h6 : IsUnit (6 : R)) {k : ℤ} (φ : KatzModularForm R k) : L R :=
  φ.toFun (WSL R) (WSL_Δ_isUnit R h6)

abbrev Lam : Type := LaurentPolynomial (L R)

def iota : L R →ₐ[R] Lam R where
  toRingHom := LaurentPolynomial.C
  commutes' := fun r => (LaurentPolynomial.algebraMap_apply r).symm

@[scoped simp] theorem iota_apply (x : L R) : iota R x = LaurentPolynomial.C x := rfl

def toLaurentA : Polynomial (L R) →ₐ[R] Lam R where
  toRingHom := Polynomial.toLaurent
  commutes' := fun r => by
    show Polynomial.toLaurent (algebraMap R (Polynomial (L R)) r) = algebraMap R (Lam R) r
    rw [Polynomial.algebraMap_apply, Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply]

@[scoped simp] theorem toLaurentA_apply (p : Polynomial (L R)) : toLaurentA R p = Polynomial.toLaurent p :=
  rfl

def Uu : (Lam R)ˣ where
  val := LaurentPolynomial.T (-1)
  inv := LaurentPolynomial.T 1
  val_inv := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

@[scoped simp] theorem Uu_inv_val : ((Uu R)⁻¹ : (Lam R)ˣ).val = LaurentPolynomial.T 1 := rfl

def Cee : WeierstrassCurve.VariableChange (Lam R) := ⟨Uu R, 0, 0, 0⟩

@[scoped simp] theorem Cee_u : (Cee R).u = Uu R := rfl
@[scoped simp] theorem Cee_r : (Cee R).r = 0 := rfl
@[scoped simp] theorem Cee_s : (Cee R).s = 0 := rfl
@[scoped simp] theorem Cee_t : (Cee R).t = 0 := rfl

def hvL : Fin 2 → Polynomial (L R) := fun i =>
  Polynomial.X ^ w46 i * Polynomial.C (algebraMap (MvPolynomial (Fin 2) R) (L R) (X i))

def sig0 : MvPolynomial (Fin 2) R →ₐ[R] Lam R := (toLaurentA R).comp (aeval (hvL R))

theorem sig0_apply (P : MvPolynomial (Fin 2) R) :
    sig0 R P = Polynomial.toLaurent (aeval (hvL R) P) := rfl

theorem sig0_X (i : Fin 2) :
    sig0 R (X i) = LaurentPolynomial.T (w46 i : ℕ)
      * LaurentPolynomial.C (algebraMap (MvPolynomial (Fin 2) R) (L R) (X i)) := by
  simp only [sig0_apply, MvPolynomial.aeval_X, hvL, map_mul, Polynomial.toLaurent_X_pow,
    Polynomial.toLaurent_C]

theorem sig0_C (r : R) : sig0 R (C r) = LaurentPolynomial.C (algebraMap R (L R) r) := by
  rw [sig0_apply, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Polynomial.toLaurent_C]

def WSΛ : WeierstrassCurve (Lam R) := (WSL R).map (LaurentPolynomial.C)

theorem map_sig0_eq : (WS R).map (sig0 R).toRingHom = Cee R • WSΛ R := by
  ext
  · simp [WeierstrassCurve.variableChange_a₁, WSΛ, WSL, WS]
  · simp [WeierstrassCurve.variableChange_a₂, WSΛ, WSL, WS]
  · simp [WeierstrassCurve.variableChange_a₃, WSΛ, WSL, WS]
  · simp only [WeierstrassCurve.map_a₄, WS_a₄, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sig0_X,
      w46_zero, WeierstrassCurve.variableChange_a₄, Cee_u, Cee_r, Cee_s, Cee_t, Uu_inv_val,
      WSΛ, WSL, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WS_a₁, WS_a₂, WS_a₃, map_zero, mul_zero, sub_zero, add_zero,
      LaurentPolynomial.T_pow, Nat.cast_ofNat]
    norm_num
  · simp only [WeierstrassCurve.map_a₆, WS_a₆, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sig0_X,
      w46_one, WeierstrassCurve.variableChange_a₆, Cee_u, Cee_r, Cee_t, Uu_inv_val,
      WSΛ, WSL, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WS_a₁, WS_a₂, WS_a₃, WS_a₄, map_zero, mul_zero, zero_mul,
      sub_zero, add_zero, LaurentPolynomial.T_pow, Nat.cast_ofNat]
    norm_num

theorem isUnit_sig0_D (h6 : IsUnit (6 : R)) : IsUnit (sig0 R D) := by
  have hΛ : IsUnit (WSΛ R).Δ := by
    rw [WSΛ, WeierstrassCurve.map_Δ]
    exact (WSL_Δ_isUnit R h6).map _
  have h : sig0 R (WS R).Δ = (Cee R • WSΛ R).Δ := by
    rw [← map_sig0_eq, WeierstrassCurve.map_Δ]
    rfl
  have h' : IsUnit (sig0 R (WS R).Δ) := by
    rw [h]
    exact KatzModularForm.isUnit_Δ_variableChange _ hΛ
  rw [WS_Δ, map_mul] at h'
  exact isUnit_of_mul_isUnit_right h'

def sigL (h6 : IsUnit (6 : R)) : L R →ₐ[R] Lam R where
  toRingHom := IsLocalization.Away.lift D (g := (sig0 R).toRingHom) (isUnit_sig0_D R h6)
  commutes' := fun r => by
    show IsLocalization.Away.lift D (g := (sig0 R).toRingHom) (isUnit_sig0_D R h6)
        (algebraMap R (L R) r) = algebraMap R (Lam R) r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (L R),
      IsLocalization.Away.lift_eq]
    exact (sig0 R).commutes r

theorem sigL_algebraMap (h6 : IsUnit (6 : R)) (p : MvPolynomial (Fin 2) R) :
    sigL R h6 (algebraMap (MvPolynomial (Fin 2) R) (L R) p) = sig0 R p :=
  IsLocalization.Away.lift_eq D (isUnit_sig0_D R h6) p

theorem sigL_comp (h6 : IsUnit (6 : R)) :
    ((sigL R h6 : L R →ₐ[R] Lam R) : L R →+* Lam R).comp
      (algebraMap (MvPolynomial (Fin 2) R) (L R)) = (sig0 R).toRingHom :=
  RingHom.ext fun p => sigL_algebraMap R h6 p

theorem WSΛ_eq : WSΛ R = (WSL R).map ((iota R : L R →ₐ[R] Lam R) : L R →+* Lam R) := by
  ext <;> rfl

variable {R}

theorem toFun_congr {k : ℤ} (φ : KatzModularForm R k) {A : Type} [CommRing A] [Algebra R A]
    {W W' : WeierstrassCurve A} (h : W = W') (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) :
    φ.toFun W hW = φ.toFun W' hW' := by
  subst h
  rfl

variable (R)

theorem Uu_inv_zpow_two_val :
    (((Uu R)⁻¹ ^ (2 : ℤ) : (Lam R)ˣ) : Lam R) = LaurentPolynomial.T 2 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_pow_eq_pow_val,
    Uu_inv_val, LaurentPolynomial.T_pow]
  norm_num

theorem scaling_law (h6 : IsUnit (6 : R)) (φ : KatzModularForm R 2) :
    sigL R h6 (gS R h6 φ) = LaurentPolynomial.T 2 * iota R (gS R h6 φ) := by
  have hΛ : IsUnit (WSΛ R).Δ := by
    rw [WSΛ, WeierstrassCurve.map_Δ]
    exact (WSL_Δ_isUnit R h6).map _
  have hcurve : (WSL R).map ((sigL R h6 : L R →ₐ[R] Lam R) : L R →+* Lam R)
      = Cee R • WSΛ R := by
    rw [WSL, WeierstrassCurve.map_map, sigL_comp, map_sig0_eq]
  have hσ := φ.map_toFun (sigL R h6) (WSL R) (WSL_Δ_isUnit R h6)
    (KatzModularForm.isUnit_Δ_map _ (WSL_Δ_isUnit R h6))
  have hι := φ.map_toFun (iota R) (WSL R) (WSL_Δ_isUnit R h6)
    (KatzModularForm.isUnit_Δ_map _ (WSL_Δ_isUnit R h6))
  have hvc := φ.toFun_variableChange (Cee R) (WSΛ R) hΛ
    (KatzModularForm.isUnit_Δ_variableChange _ hΛ)
  calc sigL R h6 (gS R h6 φ)
      = φ.toFun ((WSL R).map ((sigL R h6 : L R →ₐ[R] Lam R) : L R →+* Lam R))
        (KatzModularForm.isUnit_Δ_map _ (WSL_Δ_isUnit R h6)) := hσ.symm
    _ = φ.toFun (Cee R • WSΛ R) (KatzModularForm.isUnit_Δ_variableChange _ hΛ) :=
        toFun_congr φ hcurve _ _
    _ = (((Cee R).u⁻¹ ^ (2 : ℤ) : (Lam R)ˣ) : Lam R) * φ.toFun (WSΛ R) hΛ := hvc
    _ = LaurentPolynomial.T 2 * φ.toFun (WSΛ R) hΛ := by rw [Cee_u, Uu_inv_zpow_two_val]
    _ = LaurentPolynomial.T 2 * iota R (gS R h6 φ) := by
        rw [toFun_congr φ (WSΛ_eq R) hΛ (KatzModularForm.isUnit_Δ_map _ (WSL_Δ_isUnit R h6)),
          hι]
        rfl

theorem aeval_hvL_monomial (d : Fin 2 →₀ ℕ) (c : R) :
    aeval (hvL R) (monomial d c)
      = Polynomial.X ^ Finsupp.weight w46 d
        * Polynomial.C (algebraMap (MvPolynomial (Fin 2) R) (L R) (monomial d c)) := by
  rw [monomial_fin2, map_mul, map_mul, map_pow, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X, weight_w46]
  simp only [hvL, w46_zero, w46_one, Polynomial.algebraMap_apply, map_mul, map_pow,
    IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (L R), MvPolynomial.algebraMap_eq]
  ring

theorem coeff_aeval_hvL (P : MvPolynomial (Fin 2) R) (n : ℕ) :
    Polynomial.coeff (aeval (hvL R) P) n
      = algebraMap (MvPolynomial (Fin 2) R) (L R) (weightedHomogeneousComponent w46 n P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_hvL_monomial, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
    by_cases h : Finsupp.weight w46 d = n
    · rw [if_pos h.le, ← h, Nat.sub_self, if_pos rfl,
        (isWeightedHomogeneous_monomial w46 d c rfl).weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial w46 d c rfl).weightedHomogeneousComponent_ne n
        (Ne.symm h), map_zero]
      split_ifs with h1 h2
      · exfalso; omega
      · rfl
      · rfl
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, hp, hq, map_add, map_add]

theorem extraction (h6 : IsUnit (6 : R)) (φ : KatzModularForm R 2) :
    ∃ (N : ℕ) (P : MvPolynomial (Fin 2) R), IsWeightedHomogeneous w46 P (12 * N + 2) ∧
      gS R h6 φ * algebraMap (MvPolynomial (Fin 2) R) (L R) D ^ N
        = algebraMap (MvPolynomial (Fin 2) R) (L R) P := by
  obtain ⟨N, P₀, hP₀⟩ := IsLocalization.Away.surj (D : MvPolynomial (Fin 2) R) (gS R h6 φ)
  refine ⟨N, weightedHomogeneousComponent w46 (12 * N + 2) P₀,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  rw [hP₀]

  have hσ := congrArg (sigL R h6) hP₀
  rw [map_mul, map_pow, sigL_algebraMap, sigL_algebraMap, scaling_law] at hσ
  have hD : sig0 R D = LaurentPolynomial.T 12
      * LaurentPolynomial.C (algebraMap (MvPolynomial (Fin 2) R) (L R) D) := by
    simp only [D, map_add, map_mul, map_pow, map_ofNat, sig0_X, w46_zero, w46_one,
      Nat.cast_ofNat, mul_pow, LaurentPolynomial.T_pow]
    norm_num
    ring
  rw [hD, mul_pow, LaurentPolynomial.T_pow, iota_apply] at hσ

  have hlhs : LaurentPolynomial.T 2 * LaurentPolynomial.C (gS R h6 φ)
      * (LaurentPolynomial.T ((N : ℤ) * 12) * LaurentPolynomial.C
        (algebraMap (MvPolynomial (Fin 2) R) (L R) D) ^ N)
      = Polynomial.toLaurent (Polynomial.X ^ (12 * N + 2)
        * Polynomial.C (algebraMap (MvPolynomial (Fin 2) R) (L R) P₀)) := by
    rw [map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, ← hP₀, map_mul, map_pow]
    have hT : (LaurentPolynomial.T 2 * LaurentPolynomial.T ((N : ℤ) * 12) : Lam R)
        = LaurentPolynomial.T ((12 * N + 2 : ℕ) : ℤ) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      push_cast
      ring
    rw [← hT]
    ring
  rw [hlhs, sig0_apply] at hσ
  have hpoly := Polynomial.toLaurent_injective hσ

  have hc := congrArg (fun p => Polynomial.coeff p (12 * N + 2)) hpoly
  simp only [Polynomial.coeff_X_pow_mul', le_refl, if_true, Nat.sub_self, Polynomial.coeff_C_zero,
    coeff_aeval_hvL] at hc
  exact hc

variable {R}

def i6 (h6 : IsUnit (6 : R)) : R := ↑(h6.unit⁻¹)

theorem six_mul_i6 (h6 : IsUnit (6 : R)) : 6 * i6 h6 = 1 := h6.mul_val_inv

theorem isUnit_i6 (h6 : IsUnit (6 : R)) : IsUnit (i6 h6) := Units.isUnit _

theorem isUnit_two_alg {A : Type} [CommRing A] [Algebra R A] (h6 : IsUnit (6 : R)) :
    IsUnit (2 : A) := by
  have h := (isUnit_two h6).map (algebraMap R A)
  rwa [map_ofNat] at h

section Norm

variable {A : Type} [CommRing A]

def nS (j : A) (W : WeierstrassCurve A) : A := -(3 * j * W.a₁)

def nR (j : A) (W : WeierstrassCurve A) : A := -(2 * j * (W.a₂ - nS j W * W.a₁ - nS j W ^ 2))

def nT (j : A) (W : WeierstrassCurve A) : A := -(3 * j * (W.a₃ + nR j W * W.a₁))

def normVC (j : A) (W : WeierstrassCurve A) : WeierstrassCurve.VariableChange A :=
  ⟨1, nR j W, nS j W, nT j W⟩

@[scoped simp] theorem normVC_u (j : A) (W : WeierstrassCurve A) : (normVC j W).u = 1 := rfl
@[scoped simp] theorem normVC_r (j : A) (W : WeierstrassCurve A) : (normVC j W).r = nR j W := rfl
@[scoped simp] theorem normVC_s (j : A) (W : WeierstrassCurve A) : (normVC j W).s = nS j W := rfl
@[scoped simp] theorem normVC_t (j : A) (W : WeierstrassCurve A) : (normVC j W).t = nT j W := rfl

theorem normVC_a₁ {j : A} (hj : 6 * j = 1) (W : WeierstrassCurve A) :
    (normVC j W • W).a₁ = 0 := by
  simp only [WeierstrassCurve.variableChange_a₁, normVC_u, normVC_s, inv_one, Units.val_one,
    one_mul, nS]
  linear_combination (-W.a₁) * hj

theorem normVC_a₂ {j : A} (hj : 6 * j = 1) (W : WeierstrassCurve A) :
    (normVC j W • W).a₂ = 0 := by
  simp only [WeierstrassCurve.variableChange_a₂, normVC_u, normVC_r, normVC_s, inv_one,
    Units.val_one, one_pow, one_mul, nR]
  linear_combination (-(W.a₂ - nS j W * W.a₁ - nS j W ^ 2)) * hj

theorem normVC_a₃ {j : A} (hj : 6 * j = 1) (W : WeierstrassCurve A) :
    (normVC j W • W).a₃ = 0 := by
  simp only [WeierstrassCurve.variableChange_a₃, normVC_u, normVC_r, normVC_t, inv_one,
    Units.val_one, one_pow, one_mul, nT]
  linear_combination (-(W.a₃ + nR j W * W.a₁)) * hj

theorem normVC_map {B : Type} [CommRing B] (f : A →+* B) (j : A) (W : WeierstrassCurve A) :
    (normVC j W).map f = normVC (f j) (W.map f) := by
  ext
  · simp [normVC, WeierstrassCurve.VariableChange.map]
  · simp [normVC, WeierstrassCurve.VariableChange.map, nR, nS, map_ofNat f 2, map_ofNat f 3]
  · simp [normVC, WeierstrassCurve.VariableChange.map, nS, map_ofNat f 3]
  · simp [normVC, WeierstrassCurve.VariableChange.map, nR, nS, nT, map_ofNat f 2, map_ofNat f 3]

theorem normVC_Δ (j : A) (W : WeierstrassCurve A) : (normVC j W • W).Δ = W.Δ := by
  rw [WeierstrassCurve.variableChange_Δ, normVC_u, inv_one, Units.val_one, one_pow, one_mul]

theorem isUnit_D_normVC {j : A} (hj : 6 * j = 1) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    IsUnit (4 * (normVC j W • W).a₄ ^ 3 + 27 * (normVC j W • W).a₆ ^ 2) := by
  have h := hW
  rw [← normVC_Δ j W, Δ_of_short _ (normVC_a₁ hj W) (normVC_a₂ hj W) (normVC_a₃ hj W)] at h
  exact isUnit_of_mul_isUnit_right h

variable [Algebra R A]

theorem normVC_smul_eq {j : A} (hj : 6 * j = 1) (W : WeierstrassCurve A) :
    normVC j W • W = (WS R).map
      (aeval ![(normVC j W • W).a₄, (normVC j W • W).a₆] :
        MvPolynomial (Fin 2) R →ₐ[R] A).toRingHom := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · rw [normVC_a₁ hj]; simp [WS]
  · rw [normVC_a₂ hj]; simp [WS]
  · rw [normVC_a₃ hj]; simp [WS]
  · simp [WS]
  · simp [WS]

theorem isUnit_aeval_D (a b : A) (h : IsUnit (4 * a ^ 3 + 27 * b ^ 2)) :
    IsUnit ((aeval ![a, b] : MvPolynomial (Fin 2) R →ₐ[R] A).toRingHom D) := by
  show IsUnit (aeval ![a, b] (D : MvPolynomial (Fin 2) R))
  rw [aeval_D]
  simpa using h

def evL (a b : A) (h : IsUnit (4 * a ^ 3 + 27 * b ^ 2)) : L R →ₐ[R] A where
  toRingHom := IsLocalization.Away.lift D
    (g := (aeval ![a, b] : MvPolynomial (Fin 2) R →ₐ[R] A).toRingHom) (isUnit_aeval_D a b h)
  commutes' := fun r => by
    show IsLocalization.Away.lift D (isUnit_aeval_D (R := R) a b h) (algebraMap R (L R) r)
      = algebraMap R A r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (L R),
      IsLocalization.Away.lift_eq]
    exact (aeval _).commutes r

theorem evL_algebraMap (a b : A) (h : IsUnit (4 * a ^ 3 + 27 * b ^ 2))
    (p : MvPolynomial (Fin 2) R) :
    evL (R := R) a b h (algebraMap (MvPolynomial (Fin 2) R) (L R) p) = aeval ![a, b] p :=
  IsLocalization.Away.lift_eq D (isUnit_aeval_D (R := R) a b h) p

theorem evL_comp (a b : A) (h : IsUnit (4 * a ^ 3 + 27 * b ^ 2)) :
    ((evL (R := R) a b h : L R →ₐ[R] A) : L R →+* A).comp
      (algebraMap (MvPolynomial (Fin 2) R) (L R))
      = (aeval ![a, b] : MvPolynomial (Fin 2) R →ₐ[R] A).toRingHom :=
  RingHom.ext fun p => evL_algebraMap a b h p

theorem toFun_eq_evL (h6 : IsUnit (6 : R)) {k : ℤ} (φ : KatzModularForm R k) {j : A}
    (hj : 6 * j = 1) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    φ.toFun W hW = evL (R := R) (normVC j W • W).a₄ (normVC j W • W).a₆
      (isUnit_D_normVC hj W hW) (gS R h6 φ) := by
  have hD := isUnit_D_normVC hj W hW
  have hWn : IsUnit (normVC j W • W).Δ := by rw [normVC_Δ]; exact hW

  have h1 : φ.toFun (normVC j W • W) hWn = φ.toFun W hW := by
    rw [φ.toFun_variableChange (normVC j W) W hW hWn, normVC_u, inv_one, one_zpow,
      Units.val_one, one_mul]

  have hcurve : (WSL R).map ((evL (R := R) _ _ hD : L R →ₐ[R] A) : L R →+* A)
      = normVC j W • W := by
    rw [WSL, WeierstrassCurve.map_map, evL_comp, ← normVC_smul_eq hj W]
  have h3 := φ.map_toFun (evL (R := R) _ _ hD) (WSL R) (WSL_Δ_isUnit R h6)
    (KatzModularForm.isUnit_Δ_map _ (WSL_Δ_isUnit R h6))
  rw [← h1, ← toFun_congr φ hcurve (KatzModularForm.isUnit_Δ_map _ (WSL_Δ_isUnit R h6)) hWn, h3]
  rfl

theorem toFun_eq_zero_of_gS (h6 : IsUnit (6 : R)) {k : ℤ} (φ : KatzModularForm R k)
    (h0 : gS R h6 φ = 0) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) : φ.toFun W hW = 0 := by
  have hj : 6 * algebraMap R A (i6 h6) = 1 := by
    rw [← map_ofNat (algebraMap R A) 6, ← map_mul, six_mul_i6, map_one]
  rw [toFun_eq_evL h6 φ hj W hW, h0, map_zero]

end Norm

def Wps : WeierstrassCurve (PowerSeries R) :=
  ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom R))

def ofPSa : PowerSeries R →ₐ[R] LaurentSeries R :=
  { HahnSeries.ofPowerSeries ℤ R with commutes' := fun _ => rfl }

@[scoped simp] theorem ofPSa_apply (x : PowerSeries R) :
    ofPSa (R := R) x = HahnSeries.ofPowerSeries ℤ R x := rfl

theorem tateLaurent_eq :
    ModularCurve.tateLaurent R = (Wps (R := R)).map (HahnSeries.ofPowerSeries ℤ R) := by
  rw [Wps, WeierstrassCurve.map_map]
  rfl

def αT (h6 : IsUnit (6 : R)) : PowerSeries R :=
  (normVC (PowerSeries.C (i6 h6)) (Wps (R := R)) • Wps).a₄

def βT (h6 : IsUnit (6 : R)) : PowerSeries R :=
  (normVC (PowerSeries.C (i6 h6)) (Wps (R := R)) • Wps).a₆

theorem hjP (h6 : IsUnit (6 : R)) : 6 * PowerSeries.C (i6 h6) = 1 := by
  rw [← map_ofNat PowerSeries.C 6, ← map_mul, six_mul_i6, map_one]

theorem D_tate (h6 : IsUnit (6 : R)) :
    -16 * (4 * αT h6 ^ 3 + 27 * βT h6 ^ 2)
      = PowerSeries.map (Int.castRingHom R) ModularCurve.tatePowerSeries.Δ := by
  show -16 * (4 * (normVC (PowerSeries.C (i6 h6)) (Wps (R := R)) • Wps).a₄ ^ 3
      + 27 * (normVC (PowerSeries.C (i6 h6)) (Wps (R := R)) • Wps).a₆ ^ 2) = _
  rw [← Δ_of_short _ (normVC_a₁ (hjP h6) _) (normVC_a₂ (hjP h6) _) (normVC_a₃ (hjP h6) _),
    normVC_Δ]
  show ((ModularCurve.tatePowerSeries).map (PowerSeries.map (Int.castRingHom R))).Δ = _
  rw [WeierstrassCurve.map_Δ]

open ModularCurve in

theorem tateΔ_eq_X_mul : ∃ v : PowerSeries R, IsUnit v ∧
    PowerSeries.map (Int.castRingHom R) tatePowerSeries.Δ = PowerSeries.X * v := by
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  have hd0 : PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom R) tatePowerSeries.Δ)
      = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hc0, map_zero]
  have hd1 : PowerSeries.coeff 1 (PowerSeries.map (Int.castRingHom R) tatePowerSeries.Δ) = 1 := by
    rw [PowerSeries.coeff_map, hc1, map_one]
  obtain ⟨v, hv⟩ : (PowerSeries.X : PowerSeries R)
      ∣ PowerSeries.map (Int.castRingHom R) tatePowerSeries.Δ := PowerSeries.X_dvd_iff.mpr hd0
  refine ⟨v, ?_, hv⟩
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h1v : PowerSeries.coeff 1 (PowerSeries.map (Int.castRingHom R) tatePowerSeries.Δ)
      = PowerSeries.constantCoeff v := by
    rw [hv, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
  rw [← h1v, hd1]
  exact isUnit_one

theorem constantCoeff_map_apply (f : ℤ →+* R) (φ : PowerSeries ℤ) :
    PowerSeries.constantCoeff (PowerSeries.map f φ) = f (PowerSeries.constantCoeff φ) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem Wps_map_constantCoeff :
    (Wps (R := R)).map (PowerSeries.constantCoeff (R := R)) = ⟨1, 0, 0, 0, 0⟩ := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Wps, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ModularCurve.tatePowerSeries_a₁,
      ModularCurve.tatePowerSeries_a₂, ModularCurve.tatePowerSeries_a₃,
      ModularCurve.tatePowerSeries_a₄, ModularCurve.tatePowerSeries_a₆, map_one, map_zero,
      constantCoeff_map_apply, ModularCurve.constantCoeff_tateA4,
      ModularCurve.constantCoeff_tateA6]

theorem constantCoeff_αT (h6 : IsUnit (6 : R)) :
    PowerSeries.constantCoeff (αT h6) = -27 * i6 h6 ^ 4 := by
  have h := congrArg WeierstrassCurve.a₄
    (WeierstrassCurve.map_variableChange (Wps (R := R)) (normVC (PowerSeries.C (i6 h6)) Wps)
      (PowerSeries.constantCoeff (R := R)))
  rw [WeierstrassCurve.map_a₄, normVC_map, Wps_map_constantCoeff, PowerSeries.constantCoeff_C]
    at h
  show PowerSeries.constantCoeff ((normVC (PowerSeries.C (i6 h6)) (Wps (R := R)) • Wps).a₄) = _
  rw [← h]
  simp only [WeierstrassCurve.variableChange_a₄, normVC_u, normVC_r, normVC_s, normVC_t, nR, nS,
    nT, inv_one, Units.val_one, one_pow, one_mul, mul_zero, mul_one, sub_zero, zero_sub,
    add_zero, zero_add]
  linear_combination (36 * i6 h6 ^ 3 - 135 * i6 h6 ^ 4 + 162 * i6 h6 ^ 5) * six_mul_i6 h6

theorem constantCoeff_βT (h6 : IsUnit (6 : R)) :
    PowerSeries.constantCoeff (βT h6) = 1944 * i6 h6 ^ 8 := by
  have h := congrArg WeierstrassCurve.a₆
    (WeierstrassCurve.map_variableChange (Wps (R := R)) (normVC (PowerSeries.C (i6 h6)) Wps)
      (PowerSeries.constantCoeff (R := R)))
  rw [WeierstrassCurve.map_a₆, normVC_map, Wps_map_constantCoeff, PowerSeries.constantCoeff_C]
    at h
  show PowerSeries.constantCoeff ((normVC (PowerSeries.C (i6 h6)) (Wps (R := R)) • Wps).a₆) = _
  rw [← h]
  simp only [WeierstrassCurve.variableChange_a₆, normVC_u, normVC_r, normVC_t, nR, nS,
    nT, inv_one, Units.val_one, one_pow, one_mul, mul_zero, mul_one, sub_zero, zero_sub,
    add_zero, zero_add]
  linear_combination (-108 * i6 h6 ^ 5 + 540 * i6 h6 ^ 6 - 1620 * i6 h6 ^ 7 + 972 * i6 h6 ^ 8)
    * six_mul_i6 h6

theorem isUnit_αT (h6 : IsUnit (6 : R)) : IsUnit (αT h6) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_αT]
  exact ((isUnit_twentyseven h6).neg.mul ((isUnit_i6 h6).pow 4) : IsUnit (-27 * i6 h6 ^ 4))

theorem isUnit_βT (h6 : IsUnit (6 : R)) : IsUnit (βT h6) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_βT]
  have h1944 : IsUnit (1944 : R) := by
    have := ((isUnit_two h6).pow 3).mul ((isUnit_three h6).pow 5)
    norm_num at this
    exact this
  exact h1944.mul ((isUnit_i6 h6).pow 8)

theorem D_tate_eq_X_mul (h6 : IsUnit (6 : R)) : ∃ e : PowerSeries R, IsUnit e ∧
    aeval ![αT h6, βT h6] (D : MvPolynomial (Fin 2) R) = PowerSeries.X * e := by
  obtain ⟨v, hv, hδ⟩ := tateΔ_eq_X_mul (R := R)
  have h16 : IsUnit (16 : PowerSeries R) := isUnit_sixteen h6
  refine ⟨-(↑(h16.unit⁻¹) * v), (h16.unit⁻¹.isUnit.mul hv).neg, ?_⟩
  have hD : -16 * aeval ![αT h6, βT h6] (D : MvPolynomial (Fin 2) R) = PowerSeries.X * v := by
    rw [aeval_D, ← hδ, ← D_tate h6]
    simp
  have hinv : (↑(h16.unit⁻¹) : PowerSeries R) * 16 = 1 := h16.val_inv_mul
  linear_combination (-(↑(h16.unit⁻¹) : PowerSeries R)) * hD
    - (aeval ![αT h6, βT h6] (D : MvPolynomial (Fin 2) R)) * hinv

theorem gS_eq_zero (h6 : IsUnit (6 : R)) (φ : KatzModularForm R 2) (g : PowerSeries R)
    (hg : φ.qExpansion = HahnSeries.ofPowerSeries ℤ R g) : gS R h6 φ = 0 := by
  obtain ⟨N, P, hP, hgP⟩ := extraction R h6 φ

  have hj : 6 * HahnSeries.ofPowerSeries ℤ R (PowerSeries.C (i6 h6)) = 1 := by
    rw [← map_ofNat (HahnSeries.ofPowerSeries ℤ R) 6, ← map_mul, hjP, map_one]
  have hTΔ : IsUnit (ModularCurve.tateLaurent R).Δ := (ModularCurve.tateLaurent R).isUnit_Δ
  have hDT := isUnit_D_normVC hj (ModularCurve.tateLaurent R) hTΔ
  have hq := toFun_eq_evL (A := LaurentSeries R) h6 φ hj (ModularCurve.tateLaurent R) hTΔ
  have hg' : evL (R := R) _ _ hDT (gS R h6 φ) = HahnSeries.ofPowerSeries ℤ R g := by
    rw [← hq]
    exact hg

  have h1 := congrArg (evL (R := R) _ _ hDT) hgP
  rw [map_mul, map_pow, evL_algebraMap, evL_algebraMap, hg'] at h1

  have hcurve : normVC (HahnSeries.ofPowerSeries ℤ R (PowerSeries.C (i6 h6)))
      (ModularCurve.tateLaurent R) • ModularCurve.tateLaurent R
      = ((normVC (PowerSeries.C (i6 h6)) (Wps (R := R))) • Wps).map
        (HahnSeries.ofPowerSeries ℤ R) := by
    rw [tateLaurent_eq, ← normVC_map, WeierstrassCurve.map_variableChange]
  have ha4 : (normVC (HahnSeries.ofPowerSeries ℤ R (PowerSeries.C (i6 h6)))
      (ModularCurve.tateLaurent R) • ModularCurve.tateLaurent R).a₄
      = HahnSeries.ofPowerSeries ℤ R (αT h6) := by
    rw [hcurve, WeierstrassCurve.map_a₄]
    rfl
  have ha6 : (normVC (HahnSeries.ofPowerSeries ℤ R (PowerSeries.C (i6 h6)))
      (ModularCurve.tateLaurent R) • ModularCurve.tateLaurent R).a₆
      = HahnSeries.ofPowerSeries ℤ R (βT h6) := by
    rw [hcurve, WeierstrassCurve.map_a₆]
    rfl
  rw [ha4, ha6] at h1

  have hnat : ∀ Q : MvPolynomial (Fin 2) R,
      aeval ![HahnSeries.ofPowerSeries ℤ R (αT h6), HahnSeries.ofPowerSeries ℤ R (βT h6)] Q
        = HahnSeries.ofPowerSeries ℤ R (aeval ![αT h6, βT h6] Q) := by
    intro Q
    have hv : (![HahnSeries.ofPowerSeries ℤ R (αT h6), HahnSeries.ofPowerSeries ℤ R (βT h6)]
        : Fin 2 → LaurentSeries R) = fun i => ofPSa (R := R) (![αT h6, βT h6] i) := by
      funext i
      fin_cases i <;> rfl
    rw [hv, ← ofPSa_apply, MvPolynomial.comp_aeval_apply]
  rw [hnat, hnat, ← map_pow, ← map_mul] at h1
  have h2 : g * aeval ![αT h6, βT h6] (D : MvPolynomial (Fin 2) R) ^ N
      = aeval ![αT h6, βT h6] P := HahnSeries.ofPowerSeries_injective h1

  obtain ⟨e, he, hDe⟩ := D_tate_eq_X_mul h6
  have hdvd : PowerSeries.X ^ N ∣ aeval ![αT h6, βT h6] P := ⟨g * e ^ N, by rw [← h2, hDe]; ring⟩
  have hXreg : ∀ x : PowerSeries R, PowerSeries.X * x = 0 → x = 0 := fun x hx =>
    PowerSeries.X_mul_cancel (hx.trans (mul_zero _).symm)
  have hXC : ∀ r : R, PowerSeries.X ∣ algebraMap R (PowerSeries R) r → r = 0 := by
    intro r hr
    rw [PowerSeries.algebraMap_eq] at hr
    have := PowerSeries.X_dvd_iff.mp hr
    rwa [PowerSeries.constantCoeff_C] at this
  have hP0 : P = 0 := aeval_eq_zero_of_dvd (isUnit_twentyseven h6) PowerSeries.X (αT h6) (βT h6)
    e (isUnit_αT h6) (isUnit_βT h6) he hDe hXreg hXC N P hP hdvd
  rw [hP0, map_zero] at hgP
  exact ((isUnit_algebraMap_D R).pow N).mul_left_eq_zero.mp hgP

theorem k6 (h6 : IsUnit (6 : R)) (φ : KatzModularForm R 2) (g : PowerSeries R)
    (hg : φ.qExpansion = HahnSeries.ofPowerSeries ℤ R g) {A : Type} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) : φ.toFun W hW = 0 :=
  toFun_eq_zero_of_gS h6 φ (gS_eq_zero h6 φ g hg) W hW

end Sum56K6
p2m_reactivate "P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.Sum56K6"

theorem solution
    (R : Type) [CommRing R] (h6 : IsUnit (6 : R)) (F : KatzModularForm R 2)
    (g : PowerSeries R) (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ R g)
    (A : Type) [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    F.toFun W hW = 0 :=
  Sum56K6.k6 h6 F g hg W hW

end
p2m_reactivate "P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.Sum56K6"

end S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six
end P2MW
export P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six (solution)
