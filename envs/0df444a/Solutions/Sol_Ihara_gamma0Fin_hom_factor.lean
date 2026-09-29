-- Prove2me | solution 1 for Ihara.gamma0Fin_hom_factor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f3cb6e96-198d-5224-b256-ad77bc9a7b25

import Definitions.Def_IharaGamma0Fin
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_gamma0Fin_hom_factor

namespace Ihara
p2m_export "Ihara" "Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe"
namespace SolKillFin
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section Torsion

variable {A : Type*} [AddCommGroup A]

theorem eq_zero_of_two_nsmul (h2 : ∀ a : A, a + a = 0 → a = 0) {a : A} (h : 2 • a = 0) : a = 0 :=
  h2 a (by rwa [two_nsmul] at h)

theorem eq_zero_of_three_nsmul (h3 : ∀ a : A, a + a + a = 0 → a = 0) {a : A} (h : 3 • a = 0) :
    a = 0 :=
  h3 a (by rwa [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul] at h)

theorem eq_zero_of_twentyfour_nsmul (h2 : ∀ a : A, a + a = 0 → a = 0)
    (h3 : ∀ a : A, a + a + a = 0 → a = 0) {a : A} (h : 24 • a = 0) : a = 0 := by
  have h12 : 12 • a = 0 :=
    eq_zero_of_two_nsmul h2 (by rwa [← mul_nsmul, show (2 * 12 : ℕ) = 24 from rfl])
  have h6 : 6 • a = 0 :=
    eq_zero_of_two_nsmul h2 (by rwa [← mul_nsmul, show (2 * 6 : ℕ) = 12 from rfl])
  have h3' : 3 • a = 0 :=
    eq_zero_of_two_nsmul h2 (by rwa [← mul_nsmul, show (2 * 3 : ℕ) = 6 from rfl])
  exact eq_zero_of_three_nsmul h3 h3'

end Torsion

section TorusTrick

theorem exists_coprime_gcd_sq_sub_one_dvd (M : ℕ) (hM : M ≠ 0) :
    ∃ t : ℕ, 1 ≤ t ∧ t.Coprime M ∧ (t ^ 2 - 1).gcd M ∣ 24 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hM
  have hco : (2 ^ k).Coprime m := (Nat.coprime_two_left.mpr hm).pow_left k
  obtain ⟨t₀, ht₀2, ht₀m⟩ := Nat.chineseRemainder hco 3 2

  set t := t₀ + 3 * (2 ^ k * m) with ht
  have ht3 : 3 ≤ t := by
    have : 1 ≤ 2 ^ k * m := Nat.one_le_iff_ne_zero.mpr hM
    omega
  have ht2 : t ≡ 3 [MOD 2 ^ k] :=
    (Nat.ModEq.add_right _ ht₀2).trans (by
      rw [Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.mul_mod_right, mul_zero, Nat.zero_mod, add_zero,
        Nat.mod_mod])
  have htm : t ≡ 2 [MOD m] :=
    (Nat.ModEq.add_right _ ht₀m).trans (by
      rw [Nat.ModEq, Nat.add_mod, Nat.mul_mod, mul_comm (2 ^ k) m, Nat.mul_mod_right, mul_zero,
        Nat.zero_mod, add_zero, Nat.mod_mod])
  refine ⟨t, by omega, ?_, ?_⟩
  ·
    refine Nat.Coprime.mul_right ?_ ?_
    ·
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · apply Nat.Coprime.pow_right
        rw [Nat.coprime_two_right]
        have h2 : t ≡ 3 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 hk.ne') ht2
        rw [Nat.odd_iff, h2]
    · have := htm.gcd_eq
      rw [Nat.Coprime, this]
      exact Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 2) (Nat.coprime_two_left.mpr hm)
  ·
    rw [Nat.Coprime.gcd_mul _ hco, show (24 : ℕ) = 8 * 3 from rfl]
    refine Nat.mul_dvd_mul ?_ ?_
    · have h9 : t ^ 2 ≡ 9 [MOD 2 ^ k] := ht2.pow 2
      have h8 : t ^ 2 - 1 ≡ 8 [MOD 2 ^ k] :=
        Nat.ModEq.add_right_cancel' 1 (by rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))])
      rw [h8.gcd_eq]
      exact Nat.gcd_dvd_left 8 _
    · have h4 : t ^ 2 ≡ 4 [MOD m] := htm.pow 2
      have h3 : t ^ 2 - 1 ≡ 3 [MOD m] :=
        Nat.ModEq.add_right_cancel' 1 (by rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))])
      rw [h3.gcd_eq]
      exact Nat.gcd_dvd_left 3 _

variable {A : Type*} [AddCommGroup A]

theorem addMonoidHom_zmod_eq_zero_of_units {M : ℕ} [NeZero M] (h2 : ∀ a : A, a + a = 0 → a = 0)
    (h3 : ∀ a : A, a + a + a = 0 → a = 0) (f : ZMod M →+ A)
    (hf : ∀ (t : (ZMod M)ˣ) (b : ZMod M), f (((t : ZMod M) ^ 2 - 1) * b) = 0) : f = 0 := by
  obtain ⟨t, ht1, htco, hgcd⟩ := exists_coprime_gcd_sq_sub_one_dvd M (NeZero.ne M)
  set g := (t ^ 2 - 1).gcd M with hg

  have hbez : ((g : ℕ) : ZMod M) =
      (((t ^ 2 - 1 : ℕ) : ℤ) : ZMod M) * ((Nat.gcdA (t ^ 2 - 1) M : ℤ) : ZMod M) := by
    have h := congrArg (fun z : ℤ => (z : ZMod M)) (Nat.gcd_eq_gcd_ab (t ^ 2 - 1) M)
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul,
      add_zero] at h
    rw [hg, h, Int.cast_natCast]
  have hunit : (((t ^ 2 - 1 : ℕ) : ℤ) : ZMod M) = ((ZMod.unitOfCoprime t htco : (ZMod M)ˣ) : ZMod M) ^ 2 - 1 := by
    rw [ZMod.coe_unitOfCoprime, Int.cast_natCast, Nat.cast_sub (Nat.one_le_pow _ _ ht1), Nat.cast_pow,
      Nat.cast_one]
  have hg' : ∀ b : ZMod M, f ((g : ZMod M) * b) = 0 := by
    intro b
    have := hf (ZMod.unitOfCoprime t htco) (((Nat.gcdA (t ^ 2 - 1) M : ℤ) : ZMod M) * b)
    rwa [← mul_assoc, ← hunit, ← hbez] at this
  obtain ⟨e, he⟩ := hgcd
  ext b
  rw [AddMonoidHom.zero_apply]
  apply eq_zero_of_twentyfour_nsmul h2 h3
  rw [← map_nsmul, nsmul_eq_mul, show ((24 : ℕ) : ZMod M) = (g : ZMod M) * (e : ZMod M) by
    rw [← Nat.cast_mul, ← he], mul_assoc]
  exact hg' _

end TorusTrick

section Elementary

variable {R : Type*} [CommRing R]

def uElt (b : R) : SL(2, R) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def vElt (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def hElt (t : Rˣ) : SL(2, R) :=
  ⟨!![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)], by rw [Matrix.det_fin_two_of]; simp⟩

@[scoped simp] theorem uElt_coe (b : R) : (uElt b : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl
@[scoped simp] theorem vElt_coe (c : R) : (vElt c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl
@[scoped simp] theorem hElt_coe (t : Rˣ) :
    (hElt t : Matrix (Fin 2) (Fin 2) R) = !![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)] := rfl

theorem uElt_add (b b' : R) : uElt (b + b') = uElt b * uElt b' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem vElt_add (c c' : R) : vElt (c + c') = vElt c * vElt c' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem uElt_zero : uElt (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem vElt_zero : vElt (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hElt_mul (s t : Rˣ) : hElt (s * t) = hElt s * hElt t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem hElt_one : hElt (1 : Rˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hElt_inv (t : Rˣ) : (hElt t)⁻¹ = hElt t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← hElt_mul, mul_inv_cancel, hElt_one])

theorem hElt_inv_mul_uElt_mul_hElt (t : Rˣ) (b : R) :
    (hElt t)⁻¹ * uElt b * hElt t = uElt ((t : R) ^ 2 * b) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  rw [hElt_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, uElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination h1

theorem hElt_mul_vElt_mul_hElt_inv (t : Rˣ) (c : R) :
    hElt t * vElt c * (hElt t)⁻¹ = vElt ((t : R) ^ 2 * c) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  rw [hElt_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, vElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination h1

theorem uElt_mul_vElt (b c : R) (t : Rˣ) (ht : (t : R) = 1 + b * c) :
    uElt b * vElt c = vElt (c * ((t⁻¹ : Rˣ) : R)) * hElt t⁻¹ * uElt (b * ((t⁻¹ : Rˣ) : R)) := by
  have htinv : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  have hkey : ((t⁻¹ : Rˣ) : R) * (1 + b * c) = 1 := by rw [← ht, Units.inv_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, uElt_coe, vElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination -ht
  · linear_combination -b * htinv
  · linear_combination -c * htinv
  · linear_combination -(c * b * ((t⁻¹ : Rˣ) : R)) * htinv - hkey

theorem eq_vElt_mul_hElt_mul_uElt (g : SL(2, R)) (a : Rˣ)
    (ha : (g : Matrix (Fin 2) (Fin 2) R) 0 0 = a) :
    g = vElt ((g : Matrix (Fin 2) (Fin 2) R) 1 0 * ((a⁻¹ : Rˣ) : R)) * hElt a⁻¹ *
      uElt ((g : Matrix (Fin 2) (Fin 2) R) 0 1 * ((a⁻¹ : Rˣ) : R)) := by
  have hainv : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := Units.mul_inv a
  have hdet := g.det_coe
  rw [Matrix.det_fin_two, ha] at hdet
  have hkey : ((a⁻¹ : Rˣ) : R) * ((a : R) * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0) =
        ((a⁻¹ : Rˣ) : R) := by
    rw [hdet, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, uElt_coe, vElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) R) 0 1) * hainv
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) R) 1 0) * hainv
  · linear_combination hkey - ((g : Matrix (Fin 2) (Fin 2) R) 1 1 +
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 * ((a⁻¹ : Rˣ) : R)) * hainv

end Elementary

section StableRange

theorem exists_isUnit_add_mul_of_ringEquiv_prod {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (e : R ≃+* S × T)
    (hS : ∀ a c : S, IsCoprime a c → ∃ x : S, IsUnit (a + x * c))
    (hT : ∀ a c : T, IsCoprime a c → ∃ x : T, IsUnit (a + x * c)) :
    ∀ a c : R, IsCoprime a c → ∃ x : R, IsUnit (a + x * c) := by
  intro a c hac
  obtain ⟨x₁, hx₁⟩ := hS (e a).1 (e c).1 (hac.map ((RingHom.fst S T).comp e.toRingHom))
  obtain ⟨x₂, hx₂⟩ := hT (e a).2 (e c).2 (hac.map ((RingHom.snd S T).comp e.toRingHom))
  refine ⟨e.symm (x₁, x₂), ?_⟩
  have he : e (a + e.symm (x₁, x₂) * c) = ((e a).1 + x₁ * (e c).1, (e a).2 + x₂ * (e c).2) := by
    rw [map_add, map_mul, RingEquiv.apply_symm_apply]
    rfl
  obtain ⟨y₁, hy₁⟩ := hx₁.exists_right_inv
  obtain ⟨y₂, hy₂⟩ := hx₂.exists_right_inv
  have hunit : IsUnit (e (a + e.symm (x₁, x₂) * c)) := by
    rw [he]
    exact IsUnit.of_mul_eq_one (y₁, y₂) (Prod.ext hy₁ hy₂)
  simpa using hunit.map e.symm

theorem exists_isUnit_add_mul_primePow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (a c : ZMod (p ^ n))
    (hac : IsCoprime a c) : ∃ x : ZMod (p ^ n), IsUnit (a + x * c) := by
  by_cases ha : IsUnit a
  · exact ⟨0, by rwa [zero_mul, add_zero]⟩
  ·
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    have hpa : p ∣ a.val := by
      by_contra h
      exact ha (by rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hn).mpr h)
    obtain ⟨k, hk⟩ := hpa
    have hnil : IsNilpotent a := by
      refine ⟨n, ?_⟩
      rw [← ZMod.natCast_zmod_val a, hk, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self,
        zero_mul]
    obtain ⟨u, v, huv⟩ := hac
    have hva : IsNilpotent (u * a) := by
      obtain ⟨m, hm⟩ := hnil
      exact ⟨m, by rw [mul_pow, hm, mul_zero]⟩
    have hvc : IsUnit (v * c) := by
      have : v * c = 1 - u * a := by rw [← huv]; ring
      rw [this]
      exact hva.isUnit_one_sub
    have hc : IsUnit c := isUnit_of_mul_isUnit_right hvc
    obtain ⟨w, hw⟩ := hc.exists_left_inv
    refine ⟨(1 - a) * w, ?_⟩
    rw [mul_assoc, hw, mul_one, add_sub_cancel]
    exact isUnit_one

theorem exists_isUnit_add_mul_zmod {M : ℕ} (hM : M ≠ 0) (a c : ZMod M) (hac : IsCoprime a c) :
    ∃ x : ZMod M, IsUnit (a + x * c) := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hM
  | one => exact ⟨0, isUnit_of_subsingleton _⟩
  | prime_pow p n hp hn => exact exists_isUnit_add_mul_primePow hp hn a c hac
  | coprime m n hm hn hmn ihm ihn =>
    exact exists_isUnit_add_mul_of_ringEquiv_prod (ZMod.chineseRemainder hmn)
      (fun a c h => ihm (by omega) a c h) (fun a c h => ihn (by omega) a c h) a c hac

end StableRange

section CongruenceQuotient

variable (N M : ℕ)

def uG (b : ZMod M) : Gamma0Fin N M :=
  ⟨uElt b, by rw [mem_Gamma0Fin, uElt_coe]; exact ⟨0, by simp⟩⟩

def vG (c : ZMod M) : Gamma0Fin N M :=
  ⟨vElt ((N : ZMod M) * c), by rw [mem_Gamma0Fin, vElt_coe]; exact ⟨c, by simp⟩⟩

def hG (t : (ZMod M)ˣ) : Gamma0Fin N M :=
  ⟨hElt t, by rw [mem_Gamma0Fin, hElt_coe]; exact ⟨0, by simp⟩⟩

@[scoped simp] theorem uG_coe (b : ZMod M) : ((uG N M b : Gamma0Fin N M) : SL(2, ZMod M)) = uElt b := rfl
@[scoped simp] theorem vG_coe (c : ZMod M) :
    ((vG N M c : Gamma0Fin N M) : SL(2, ZMod M)) = vElt ((N : ZMod M) * c) := rfl
@[scoped simp] theorem hG_coe (t : (ZMod M)ˣ) : ((hG N M t : Gamma0Fin N M) : SL(2, ZMod M)) = hElt t := rfl

theorem uG_add (b b' : ZMod M) : uG N M (b + b') = uG N M b * uG N M b' :=
  Subtype.ext (uElt_add b b')

theorem uG_zero : uG N M 0 = 1 := Subtype.ext uElt_zero

theorem vG_add (c c' : ZMod M) : vG N M (c + c') = vG N M c * vG N M c' :=
  Subtype.ext (by rw [Subgroup.coe_mul, vG_coe, vG_coe, vG_coe, mul_add, vElt_add])

theorem vG_zero : vG N M 0 = 1 := Subtype.ext (by rw [vG_coe, mul_zero, vElt_zero]; rfl)

def hGHom : (ZMod M)ˣ →* Gamma0Fin N M where
  toFun := hG N M
  map_one' := Subtype.ext hElt_one
  map_mul' s t := Subtype.ext (hElt_mul s t)

@[scoped simp] theorem hGHom_apply (t : (ZMod M)ˣ) : hGHom N M t = hG N M t := rfl

theorem hG_inv (t : (ZMod M)ˣ) : (hG N M t)⁻¹ = hG N M t⁻¹ := by
  rw [← hGHom_apply, ← map_inv, hGHom_apply]

theorem hG_inv_mul_uG_mul_hG (t : (ZMod M)ˣ) (b : ZMod M) :
    (hG N M t)⁻¹ * uG N M b * hG N M t = uG N M ((t : ZMod M) ^ 2 * b) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hG_coe, uG_coe, uG_coe]
    exact hElt_inv_mul_uElt_mul_hElt t b)

theorem hG_mul_vG_mul_hG_inv (t : (ZMod M)ˣ) (c : ZMod M) :
    hG N M t * vG N M c * (hG N M t)⁻¹ = vG N M ((t : ZMod M) ^ 2 * c) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hG_coe, vG_coe, vG_coe,
      mul_left_comm]
    exact hElt_mul_vElt_mul_hElt_inv t _)

theorem uG_mul_vG_one (k : ZMod M) (t : (ZMod M)ˣ) (ht : (t : ZMod M) = 1 + k * N) :
    uG N M k * vG N M 1 = vG N M ((t⁻¹ : (ZMod M)ˣ) : ZMod M) * hG N M t⁻¹ *
      uG N M (k * ((t⁻¹ : (ZMod M)ˣ) : ZMod M)) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, uG_coe, vG_coe, vG_coe, hG_coe, uG_coe,
      mul_one]
    exact uElt_mul_vElt k (N : ZMod M) t ht)

end CongruenceQuotient

section Factor

variable {N M : ℕ} [NeZero M] (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
  (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
  (Φ : Gamma0Fin N M →* Multiplicative A)

include h2 h3

theorem map_uG_eq_one (b : ZMod M) : Φ (uG N M b) = 1 := by
  let f : ZMod M →+ A :=
    { toFun := fun b => Multiplicative.toAdd (Φ (uG N M b))
      map_zero' := by simp only [uG_zero, map_one, toAdd_one]
      map_add' := fun b b' => by simp only [uG_add, map_mul, toAdd_mul] }
  have hf : ∀ (t : (ZMod M)ˣ) (b : ZMod M), f (((t : ZMod M) ^ 2 - 1) * b) = 0 := by
    intro t b
    have key : Φ (uG N M ((t : ZMod M) ^ 2 * b)) = Φ (uG N M b) := by
      rw [← hG_inv_mul_uG_mul_hG, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    rw [sub_mul, one_mul, map_sub, sub_eq_zero]
    show Multiplicative.toAdd (Φ (uG N M ((t : ZMod M) ^ 2 * b))) = Multiplicative.toAdd (Φ (uG N M b))
    rw [key]
  have h0 := addMonoidHom_zmod_eq_zero_of_units h2 h3 f hf
  have : f b = 0 := by rw [h0]; rfl
  exact toAdd_eq_zero.mp this

theorem map_vG_eq_one (c : ZMod M) : Φ (vG N M c) = 1 := by
  let f : ZMod M →+ A :=
    { toFun := fun c => Multiplicative.toAdd (Φ (vG N M c))
      map_zero' := by simp only [vG_zero, map_one, toAdd_one]
      map_add' := fun c c' => by simp only [vG_add, map_mul, toAdd_mul] }
  have hf : ∀ (t : (ZMod M)ˣ) (c : ZMod M), f (((t : ZMod M) ^ 2 - 1) * c) = 0 := by
    intro t c
    have key : Φ (vG N M ((t : ZMod M) ^ 2 * c)) = Φ (vG N M c) := by
      rw [← hG_mul_vG_mul_hG_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    rw [sub_mul, one_mul, map_sub, sub_eq_zero]
    show Multiplicative.toAdd (Φ (vG N M ((t : ZMod M) ^ 2 * c))) = Multiplicative.toAdd (Φ (vG N M c))
    rw [key]
  have h0 := addMonoidHom_zmod_eq_zero_of_units h2 h3 f hf
  have : f c = 0 := by rw [h0]; rfl
  exact toAdd_eq_zero.mp this

theorem map_hG_eq_one_of_cast_eq_one (t : (ZMod M)ˣ)
    (ht : ZMod.castHom hNM (ZMod N) (t : ZMod M) = 1) : Φ (hG N M t) = 1 := by

  have hN0 : ZMod.castHom hNM (ZMod N) ((t : ZMod M) - 1) = 0 := by rw [map_sub, ht, map_one, sub_self]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hN0
  obtain ⟨k, hk⟩ := hN0
  have htk : (t : ZMod M) = 1 + (k : ZMod M) * N := by
    have : (t : ZMod M) - 1 = (((t : ZMod M) - 1).val : ZMod M) := (ZMod.natCast_zmod_val _).symm
    rw [hk, Nat.cast_mul, mul_comm] at this
    rw [← this, add_sub_cancel]
  have hsteinberg := congrArg Φ (uG_mul_vG_one N M (k : ZMod M) t htk)
  rw [map_mul, map_mul, map_mul, map_uG_eq_one h2 h3, map_uG_eq_one h2 h3, map_vG_eq_one h2 h3,
    map_vG_eq_one h2 h3, one_mul, one_mul, mul_one, ← hG_inv, map_inv] at hsteinberg
  exact inv_eq_one.mp hsteinberg.symm

omit [NeZero M] h2 h3 in
theorem uG_mul_apply_zero_zero (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 0 0 =
      (g : SL(2, ZMod M)) 0 0 + x * (g : SL(2, ZMod M)) 1 0 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] h2 h3 in
theorem uG_mul_apply_one_zero (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 1 0 = (g : SL(2, ZMod M)) 1 0 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] h2 h3 in
theorem uG_mul_apply_one_one (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 = (g : SL(2, ZMod M)) 1 1 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem map_eq_map_hG_of_isUnit (g : Gamma0Fin N M) (a : (ZMod M)ˣ)
    (ha : (g : SL(2, ZMod M)) 0 0 = a) : Φ g = Φ (hG N M a⁻¹) := by
  obtain ⟨r, hr⟩ := g.2
  have hbruhat := eq_vElt_mul_hElt_mul_uElt (g : SL(2, ZMod M)) a ha
  have hG' : g = vG N M (r * ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) * hG N M a⁻¹ *
      uG N M ((g : SL(2, ZMod M)) 0 1 * ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, vG_coe, hG_coe, uG_coe, ← mul_assoc (N : ZMod M), ← hr]
    exact hbruhat
  rw [hG', map_mul, map_mul, map_uG_eq_one h2 h3, map_vG_eq_one h2 h3, one_mul, mul_one]

theorem gamma0Fin_hom_factor :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Φ = χ.comp (gamma0FinUnitsChar N M hNM) := by
  have hM : M ≠ 0 := NeZero.ne M

  set ψ : (ZMod M)ˣ →* Multiplicative A := Φ.comp (hGHom N M) with hψ
  have hker : (ZMod.unitsMap hNM).ker ≤ ψ.ker := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    have ht' : ZMod.castHom hNM (ZMod N) (t : ZMod M) = 1 := by
      have := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) ht
      simpa [ZMod.unitsMap, Units.coe_map] using this
    rw [hψ, MonoidHom.comp_apply, hGHom_apply]
    exact map_hG_eq_one_of_cast_eq_one hNM h2 h3 Φ t ht'
  have hsurj := ZMod.unitsMap_surjective (n := N) (m := M) hNM
  let χ : (ZMod N)ˣ →* Multiplicative A :=
    (ZMod.unitsMap hNM).liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨ψ, hker⟩
  have hχ : ∀ t : (ZMod M)ˣ, χ (ZMod.unitsMap hNM t) = Φ (hG N M t) := by
    intro t
    exact (ZMod.unitsMap hNM).liftOfRightInverse_comp_apply (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨ψ, hker⟩ t
  refine ⟨χ, MonoidHom.ext fun g => ?_⟩

  have hcop : IsCoprime ((g : SL(2, ZMod M)) 0 0) ((g : SL(2, ZMod M)) 1 0) := by
    refine ⟨(g : SL(2, ZMod M)) 1 1, -((g : SL(2, ZMod M)) 0 1), ?_⟩
    have hdet := (g : SL(2, ZMod M)).det_coe
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet
  obtain ⟨x, hx⟩ := exists_isUnit_add_mul_zmod hM _ _ hcop
  set s : (ZMod M)ˣ := hx.unit with hs
  set g' : Gamma0Fin N M := uG N M x * g with hg'
  have hs0 : ((g' : Gamma0Fin N M) : SL(2, ZMod M)) 0 0 = s := by
    rw [hg', uG_mul_apply_zero_zero, hs, IsUnit.unit_spec]
  have hΦ : Φ g = Φ (hG N M s⁻¹) := by
    rw [← map_eq_map_hG_of_isUnit h2 h3 Φ g' s hs0, hg', map_mul, map_uG_eq_one h2 h3, one_mul]

  have hchar : gamma0FinUnitsChar N M hNM g = (ZMod.unitsMap hNM s)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    ext
    rw [Units.val_mul, gamma0FinUnitsChar_coe, Units.val_one]
    have hdet := ((g' : Gamma0Fin N M) : SL(2, ZMod M)).det_coe
    rw [Matrix.det_fin_two, hs0, hg', uG_mul_apply_one_one, uG_mul_apply_one_zero] at hdet
    have := congrArg (ZMod.castHom hNM (ZMod N)) hdet
    rw [map_sub, map_mul, map_mul, castHom_apply_one_zero N M hNM g, mul_zero, sub_zero, map_one,
      mul_comm] at this
    simpa [ZMod.unitsMap, Units.coe_map] using this
  rw [MonoidHom.comp_apply, hchar, ← map_inv, hχ, hΦ]

end Factor

end Ihara.SolKillFin
p2m_reactivate "P2MW.S_Ihara_gamma0Fin_hom_factor.Ihara P2MW.S_Ihara_gamma0Fin_hom_factor.Ihara.SolKillFin"
p2m_reactivate "P2MW.S_Ihara_gamma0Fin_hom_factor.Ihara"

theorem solution {N M : ℕ} [NeZero M] (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Φ : Ihara.Gamma0Fin N M →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Φ = χ.comp (Ihara.gamma0FinUnitsChar N M hNM) :=
  Ihara.SolKillFin.gamma0Fin_hom_factor hNM h2 h3 Φ

end S_Ihara_gamma0Fin_hom_factor
end P2MW
export P2MW.S_Ihara_gamma0Fin_hom_factor (solution)
