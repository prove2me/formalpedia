-- Prove2me | solution 1 for Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/05419aaf-7628-58dc-910d-637b1404c6e5

import Definitions.Def_IharaIota
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_IharaGamma0Fin
import Definitions.Def_Gamma0Away
import Definitions.Def_Gamma0AwayUnitsChar
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaAmalgam
import Definitions.Def_IharaAmalgamMap
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Ihara_amalgamToGamma0Away_injective
import Theorems.Thm_Ihara_amalgamToGamma0Away_surjective
import Theorems.Thm_HeckeEis_postcomp_heckeOperatorHom
import Theorems.Thm_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar
import Theorems.Thm_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff
import Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
import Theorems.Thm_Ihara_exists_principalCongruenceAway_le_of_finiteIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex"
namespace ParabolicFin
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section Elementary

variable {R : Type*} [CommRing R]

private def uElt (b : R) : SL(2, R) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private def vElt (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private def hElt (t : Rˣ) : SL(2, R) :=
  ⟨!![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)], by rw [Matrix.det_fin_two_of]; simp⟩

@[scoped simp] private theorem uElt_coe (b : R) : (uElt b : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl
@[scoped simp] private theorem vElt_coe (c : R) : (vElt c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl
@[scoped simp] private theorem hElt_coe (t : Rˣ) :
    (hElt t : Matrix (Fin 2) (Fin 2) R) = !![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)] := rfl

private theorem uElt_add (b b' : R) : uElt (b + b') = uElt b * uElt b' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem vElt_add (c c' : R) : vElt (c + c') = vElt c * vElt c' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem uElt_zero : uElt (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem vElt_zero : vElt (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem hElt_mul (s t : Rˣ) : hElt (s * t) = hElt s * hElt t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem hElt_one : hElt (1 : Rˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem hElt_inv (t : Rˣ) : (hElt t)⁻¹ = hElt t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← hElt_mul, mul_inv_cancel, hElt_one])

private theorem hElt_inv_mul_uElt_mul_hElt (t : Rˣ) (b : R) :
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

private theorem hElt_mul_vElt_mul_hElt_inv (t : Rˣ) (c : R) :
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

private theorem uElt_mul_vElt (b c : R) (t : Rˣ) (ht : (t : R) = 1 + b * c) :
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

private theorem eq_vElt_mul_hElt_mul_uElt (g : SL(2, R)) (a : Rˣ)
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

private theorem exists_isUnit_add_mul_of_ringEquiv_prod {R S T : Type*} [CommRing R] [CommRing S]
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

private theorem exists_isUnit_add_mul_primePow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (a c : ZMod (p ^ n))
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

private theorem exists_isUnit_add_mul_zmod {M : ℕ} (hM : M ≠ 0) (a c : ZMod M) (hac : IsCoprime a c) :
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

private def uG (b : ZMod M) : Gamma0Fin N M :=
  ⟨uElt b, by rw [mem_Gamma0Fin, uElt_coe]; exact ⟨0, by simp⟩⟩

private def vG (c : ZMod M) : Gamma0Fin N M :=
  ⟨vElt ((N : ZMod M) * c), by rw [mem_Gamma0Fin, vElt_coe]; exact ⟨c, by simp⟩⟩

private def hG (t : (ZMod M)ˣ) : Gamma0Fin N M :=
  ⟨hElt t, by rw [mem_Gamma0Fin, hElt_coe]; exact ⟨0, by simp⟩⟩

@[scoped simp] private theorem uG_coe (b : ZMod M) : ((uG N M b : Gamma0Fin N M) : SL(2, ZMod M)) = uElt b := rfl
@[scoped simp] private theorem vG_coe (c : ZMod M) :
    ((vG N M c : Gamma0Fin N M) : SL(2, ZMod M)) = vElt ((N : ZMod M) * c) := rfl
@[scoped simp] private theorem hG_coe (t : (ZMod M)ˣ) : ((hG N M t : Gamma0Fin N M) : SL(2, ZMod M)) = hElt t := rfl

private theorem uG_add (b b' : ZMod M) : uG N M (b + b') = uG N M b * uG N M b' :=
  Subtype.ext (uElt_add b b')

private theorem uG_zero : uG N M 0 = 1 := Subtype.ext uElt_zero

private theorem vG_add (c c' : ZMod M) : vG N M (c + c') = vG N M c * vG N M c' :=
  Subtype.ext (by rw [Subgroup.coe_mul, vG_coe, vG_coe, vG_coe, mul_add, vElt_add])

private theorem vG_zero : vG N M 0 = 1 := Subtype.ext (by rw [vG_coe, mul_zero, vElt_zero]; rfl)

private def hGHom : (ZMod M)ˣ →* Gamma0Fin N M where
  toFun := hG N M
  map_one' := Subtype.ext hElt_one
  map_mul' s t := Subtype.ext (hElt_mul s t)

@[scoped simp] private theorem hGHom_apply (t : (ZMod M)ˣ) : hGHom N M t = hG N M t := rfl

private theorem hG_inv (t : (ZMod M)ˣ) : (hG N M t)⁻¹ = hG N M t⁻¹ := by
  rw [← hGHom_apply, ← map_inv, hGHom_apply]

private theorem hG_inv_mul_uG_mul_hG (t : (ZMod M)ˣ) (b : ZMod M) :
    (hG N M t)⁻¹ * uG N M b * hG N M t = uG N M ((t : ZMod M) ^ 2 * b) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hG_coe, uG_coe, uG_coe]
    exact hElt_inv_mul_uElt_mul_hElt t b)

private theorem hG_mul_vG_mul_hG_inv (t : (ZMod M)ˣ) (c : ZMod M) :
    hG N M t * vG N M c * (hG N M t)⁻¹ = vG N M ((t : ZMod M) ^ 2 * c) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hG_coe, vG_coe, vG_coe,
      mul_left_comm]
    exact hElt_mul_vElt_mul_hElt_inv t _)

private theorem uG_mul_vG_one (k : ZMod M) (t : (ZMod M)ˣ) (ht : (t : ZMod M) = 1 + k * N) :
    uG N M k * vG N M 1 = vG N M ((t⁻¹ : (ZMod M)ˣ) : ZMod M) * hG N M t⁻¹ *
      uG N M (k * ((t⁻¹ : (ZMod M)ˣ) : ZMod M)) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, uG_coe, vG_coe, vG_coe, hG_coe, uG_coe,
      mul_one]
    exact uElt_mul_vElt k (N : ZMod M) t ht)

end CongruenceQuotient

section Factor

variable {N M : ℕ} [NeZero M] (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
  (Φ : Gamma0Fin N M →* Multiplicative A)
  (hu : Φ (uG N M 1) = 1) (hv : Φ (vG N M 1) = 1)

omit [NeZero M] in
include hu in

private theorem map_uG_eq_one (b : ZMod M) : Φ (uG N M b) = 1 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective b
  induction k using Int.induction_on with
  | zero => rw [Int.cast_zero, uG_zero, map_one]
  | succ n ih => rw [Int.cast_add, Int.cast_one, uG_add, map_mul, ih, hu, one_mul]
  | pred n ih =>
    have h : ((-(n : ℤ) - 1 : ℤ) : ZMod M) + 1 = ((-(n : ℤ) : ℤ) : ZMod M) := by push_cast; ring
    have h1 : Φ (uG N M (((-(n : ℤ) - 1 : ℤ) : ZMod M))) * Φ (uG N M 1) = 1 := by
      rw [← map_mul, ← uG_add, h, ih]
    rwa [hu, mul_one] at h1

omit [NeZero M] in
include hv in

private theorem map_vG_eq_one (c : ZMod M) : Φ (vG N M c) = 1 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
  induction k using Int.induction_on with
  | zero => rw [Int.cast_zero, vG_zero, map_one]
  | succ n ih => rw [Int.cast_add, Int.cast_one, vG_add, map_mul, ih, hv, one_mul]
  | pred n ih =>
    have h : ((-(n : ℤ) - 1 : ℤ) : ZMod M) + 1 = ((-(n : ℤ) : ℤ) : ZMod M) := by push_cast; ring
    have h1 : Φ (vG N M (((-(n : ℤ) - 1 : ℤ) : ZMod M))) * Φ (vG N M 1) = 1 := by
      rw [← map_mul, ← vG_add, h, ih]
    rwa [hv, mul_one] at h1

include hu hv in

private theorem map_hG_eq_one_of_cast_eq_one (t : (ZMod M)ˣ)
    (ht : ZMod.castHom hNM (ZMod N) (t : ZMod M) = 1) : Φ (hG N M t) = 1 := by

  have hN0 : ZMod.castHom hNM (ZMod N) ((t : ZMod M) - 1) = 0 := by rw [map_sub, ht, map_one, sub_self]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hN0
  obtain ⟨k, hk⟩ := hN0
  have htk : (t : ZMod M) = 1 + (k : ZMod M) * N := by
    have : (t : ZMod M) - 1 = (((t : ZMod M) - 1).val : ZMod M) := (ZMod.natCast_zmod_val _).symm
    rw [hk, Nat.cast_mul, mul_comm] at this
    rw [← this, add_sub_cancel]
  have hsteinberg := congrArg Φ (uG_mul_vG_one N M (k : ZMod M) t htk)
  rw [map_mul, map_mul, map_mul, map_uG_eq_one Φ hu, map_uG_eq_one Φ hu, map_vG_eq_one Φ hv,
    map_vG_eq_one Φ hv, one_mul, one_mul, mul_one, ← hG_inv, map_inv] at hsteinberg
  exact inv_eq_one.mp hsteinberg.symm

omit [NeZero M] in
private theorem uG_mul_apply_zero_zero (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 0 0 =
      (g : SL(2, ZMod M)) 0 0 + x * (g : SL(2, ZMod M)) 1 0 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] in
private theorem uG_mul_apply_one_zero (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 1 0 = (g : SL(2, ZMod M)) 1 0 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] in
private theorem uG_mul_apply_one_one (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 = (g : SL(2, ZMod M)) 1 1 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] in
include hu hv in

private theorem map_eq_map_hG_of_isUnit (g : Gamma0Fin N M) (a : (ZMod M)ˣ)
    (ha : (g : SL(2, ZMod M)) 0 0 = a) : Φ g = Φ (hG N M a⁻¹) := by
  obtain ⟨r, hr⟩ := g.2
  have hbruhat := eq_vElt_mul_hElt_mul_uElt (g : SL(2, ZMod M)) a ha
  have hG' : g = vG N M (r * ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) * hG N M a⁻¹ *
      uG N M ((g : SL(2, ZMod M)) 0 1 * ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, vG_coe, hG_coe, uG_coe, ← mul_assoc (N : ZMod M), ← hr]
    exact hbruhat
  rw [hG', map_mul, map_mul, map_uG_eq_one Φ hu, map_vG_eq_one Φ hv, one_mul, mul_one]

include hu hv in

private theorem gamma0Fin_hom_factor :
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
    exact map_hG_eq_one_of_cast_eq_one hNM Φ hu hv t ht'
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
    rw [← map_eq_map_hG_of_isUnit Φ hu hv g' s hs0, hg', map_mul, map_uG_eq_one Φ hu, one_mul]

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

end Ihara.ParabolicFin
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara"

namespace Ihara p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex" end Ihara
p2m_open_scoped "Ihara" in

private theorem Ihara.gamma0Fin_hom_factor_of_map_unipotent_eq_one {N M : ℕ} [NeZero M] (hNM : N ∣ M)
    {A : Type*} [AddCommGroup A] (Φ : Ihara.Gamma0Fin N M →* Multiplicative A)
    (hu : Φ (Ihara.ParabolicFin.uG N M 1) = 1) (hv : Φ (Ihara.ParabolicFin.vG N M 1) = 1) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Φ = χ.comp (Ihara.gamma0FinUnitsChar N M hNM) :=
  Ihara.ParabolicFin.gamma0Fin_hom_factor hNM Φ hu hv

namespace Ihara
p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex"
p2m_open "Ihara"

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Bridge

variable (N M q : ℕ)

private theorem castHom_comp_zAwayToZMod (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q) (hNM : N ∣ M) :
    (ZMod.castHom hNM (ZMod N)).comp (zAwayToZMod M q hMq) = zAwayToZMod N q hNq := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) ?_
  ext a
  simp only [RingHom.comp_apply, zAwayToZMod_algebraMap, map_intCast]

private theorem slAwayReduction_mem_Gamma0Fin (hMq : Nat.Coprime M q) (g : Gamma0Away N q) :
    slAwayReduction M q hMq (g : SL(2, ZAway q)) ∈ Gamma0Fin N M := by
  obtain ⟨r, hr⟩ := g.2
  refine ⟨zAwayToZMod M q hMq r, ?_⟩
  show ((g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map (zAwayToZMod M q hMq) 1 0 =
    (N : ZMod M) * zAwayToZMod M q hMq r
  rw [Matrix.map_apply, hr, map_mul, map_natCast]

private noncomputable def gamma0AwayToFin (hMq : Nat.Coprime M q) : Gamma0Away N q →* Gamma0Fin N M :=
  ((slAwayReduction M q hMq).comp (Gamma0Away N q).subtype).codRestrict (Gamma0Fin N M)
    (fun g => slAwayReduction_mem_Gamma0Fin N M q hMq g)

@[scoped simp]
private theorem coe_gamma0AwayToFin (hMq : Nat.Coprime M q) (g : Gamma0Away N q) :
    ((gamma0AwayToFin N M q hMq g : Gamma0Fin N M) : SL(2, ZMod M)) =
      slAwayReduction M q hMq (g : SL(2, ZAway q)) :=
  rfl

private theorem gamma0FinUnitsChar_comp_gamma0AwayToFin (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q)
    (hNM : N ∣ M) :
    (gamma0FinUnitsChar N M hNM).comp (gamma0AwayToFin N M q hMq) = gamma0AwayUnitsChar N q hNq := by
  ext g
  rw [MonoidHom.comp_apply, gamma0FinUnitsChar_coe, gamma0AwayUnitsChar_coe, coe_gamma0AwayToFin,
    slAwayReduction_coe, Matrix.map_apply, ← RingHom.comp_apply, castHom_comp_zAwayToZMod N M q hMq hNq hNM]
  rfl

private theorem mem_ker_gamma0AwayToFin_iff (hMq : Nat.Coprime M q) (g : Gamma0Away N q) :
    g ∈ (gamma0AwayToFin N M q hMq).ker ↔ (g : SL(2, ZAway q)) ∈ principalCongruenceAway M q hMq := by
  rw [MonoidHom.mem_ker, mem_principalCongruenceAway_iff, ← coe_gamma0AwayToFin]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

private theorem gamma0AwayToFin_vertexZeroAway (hMq : Nat.Coprime M q) (γ : Gamma0 N) :
    ((gamma0AwayToFin N M q hMq (vertexZeroAway N q γ) : Gamma0Fin N M) : SL(2, ZMod M)) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (γ : SL(2, ℤ)) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  show zAwayToZMod M q hMq (algebraMap ℤ (ZAway q) (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j)) =
    ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M)
  rw [zAwayToZMod_algebraMap]

private theorem gamma0AwayToFin_surjective [NeZero M] (hMq : Nat.Coprime M q) (hNM : N ∣ M)
    (hSL : Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)))) :
    Function.Surjective (gamma0AwayToFin N M q hMq) := by
  intro g
  obtain ⟨γ, hγ⟩ := hSL (g : SL(2, ZMod M))
  obtain ⟨x, hx⟩ := g.2

  have h10 : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M)) = (N : ZMod M) * x := by
    rw [← hx, ← hγ]
    rfl
  have hN : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have hval : (N : ZMod M) * x = (((N * x.val : ℕ) : ℤ) : ZMod M) := by
      rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hval, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
    have hNM' : (N : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hNM
    have h1 := dvd_add (hNM'.trans h10) (dvd_mul_right (N : ℤ) (x.val : ℤ))
    rwa [Nat.cast_mul, sub_add_cancel] at h1
  have hmem : γ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hN
  refine ⟨vertexZeroAway N q ⟨γ, hmem⟩, Subtype.ext ?_⟩
  rw [gamma0AwayToFin_vertexZeroAway, hγ]

end Bridge
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

section Divisibility

variable (N q : ℕ)

private theorem natCast_dvd_of_zAwayToZMod_eq_zero (hNq : Nat.Coprime N q) {z : ZAway q}
    (hz : zAwayToZMod N q hNq z = 0) : (N : ZAway q) ∣ z := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (q : ℤ)) z
  simp only at h
  have ha : ((a : ℤ) : ZMod N) = 0 := by
    have h' := congrArg (zAwayToZMod N q hNq) h
    rw [map_mul, hz, zero_mul, zAwayToZMod_algebraMap] at h'
    exact h'.symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a N).mp ha
  have hs : IsUnit (algebraMap ℤ (ZAway q) s) := IsLocalization.map_units (ZAway q) s
  refine ⟨algebraMap ℤ (ZAway q) b * ↑hs.unit⁻¹, ?_⟩
  have hN : (N : ZAway q) = algebraMap ℤ (ZAway q) (N : ℤ) := by simp
  calc z = z * algebraMap ℤ (ZAway q) s * ↑hs.unit⁻¹ := by
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
    _ = algebraMap ℤ (ZAway q) a * ↑hs.unit⁻¹ := by rw [h]
    _ = (N : ZAway q) * (algebraMap ℤ (ZAway q) b * ↑hs.unit⁻¹) := by
        rw [hb, map_mul, hN, mul_assoc]

private theorem principalCongruenceAway_le_gamma0Away (hNq : Nat.Coprime N q) :
    principalCongruenceAway N q hNq ≤ Gamma0Away N q := by
  intro g hg
  rw [mem_principalCongruenceAway_iff] at hg
  rw [mem_Gamma0Away]
  refine natCast_dvd_of_zAwayToZMod_eq_zero N q hNq ?_
  have h := congrArg (fun x : SL(2, ZMod N) => (x : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0) hg
  simp only [slAwayReduction_coe, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h
  exact h

private theorem principalCongruenceAway_le_of_dvd {a b : ℕ} (hab : a ∣ b) (haq : Nat.Coprime a q)
    (hbq : Nat.Coprime b q) :
    principalCongruenceAway b q hbq ≤ principalCongruenceAway a q haq := by
  intro g hg
  rw [mem_principalCongruenceAway_iff] at hg ⊢
  have h1 : ((g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map (zAwayToZMod b q hbq) = 1 := by
    have := congrArg (fun X : SL(2, ZMod b) => (X : Matrix (Fin 2) (Fin 2) (ZMod b))) hg
    simpa [slAwayReduction_coe] using this
  apply Subtype.ext
  rw [slAwayReduction_coe, ← castHom_comp_zAwayToZMod a b q hbq haq hab, RingHom.coe_comp,
    ← Matrix.map_map, h1, Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {N q} in

private theorem mem_of_coe_mem_map_subtype {Γ : Subgroup SL(2, ZAway q)} {K : Subgroup Γ} {g : Γ}
    (h : (g : SL(2, ZAway q)) ∈ K.map Γ.subtype) : g ∈ K := by
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp h
  have : k = g := Subtype.ext hkg
  exact this ▸ hk

end Divisibility
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

end Ihara
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

namespace Ihara
p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by

  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ

  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  ·
    by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_or_dvd h3 with h4 | h4
      · exact not_dvd_primeSel pp hpd (natCast_dvd_int.mp h4)
      · exact Hγ p pp h1 hpd h4
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  ·
    push_cast
    simp

end ArithmeticLemmas
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

section Lifting

private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by

  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d

  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h

  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))

  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ

  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez

  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this

  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  ·
    push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  ·
    push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

private theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end Lifting
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

end Ihara
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

namespace Ihara
p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex"
p2m_open "Ihara"

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Away

private def tGamma0 (N : ℕ) : Gamma0 N :=
  ⟨ModularGroup.T, by rw [Gamma0_mem, ModularGroup.coe_T]; simp⟩

private def lGamma0 (N : ℕ) : Gamma0 N :=
  ⟨⟨!![1, 0; (N : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩, by rw [Gamma0_mem]; simp⟩

@[scoped simp] private theorem coe_tGamma0 (N : ℕ) : ((tGamma0 N : Gamma0 N) : SL(2, ℤ)) = ModularGroup.T := rfl

@[scoped simp] private theorem coe_coe_lGamma0 (N : ℕ) :
    (((lGamma0 N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (N : ℤ), 1] := rfl

private theorem trace_sq_tGamma0 (N : ℕ) :
    (((tGamma0 N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [coe_tGamma0, ModularGroup.coe_T, Matrix.trace_fin_two_of]; norm_num

private theorem trace_sq_lGamma0 (N : ℕ) :
    (((lGamma0 N : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [coe_coe_lGamma0, Matrix.trace_fin_two_of]; norm_num

private theorem gamma0AwayToFin_vertexZeroAway_tGamma0 {N M q : ℕ} (hMq : Nat.Coprime M q) :
    gamma0AwayToFin N M q hMq (vertexZeroAway N q (tGamma0 N)) = ParabolicFin.uG N M 1 := by
  apply Subtype.ext
  rw [gamma0AwayToFin_vertexZeroAway, ParabolicFin.uG_coe]
  apply Subtype.ext
  rw [coe_tGamma0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_T, ParabolicFin.uElt]

private theorem gamma0AwayToFin_vertexZeroAway_lGamma0 {N M q : ℕ} (hMq : Nat.Coprime M q) :
    gamma0AwayToFin N M q hMq (vertexZeroAway N q (lGamma0 N)) = ParabolicFin.vG N M 1 := by
  apply Subtype.ext
  rw [gamma0AwayToFin_vertexZeroAway, ParabolicFin.vG_coe]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_coe_lGamma0, ParabolicFin.vElt]

private theorem gamma0Away_hom_factor_of_ker_le_of_map_unipotent {N M q : ℕ} [NeZero M]
    (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q) (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
    (Ψ : Gamma0Away N q →* Multiplicative A)
    (hsurj : Function.Surjective (gamma0AwayToFin N M q hMq))
    (hker : (gamma0AwayToFin N M q hMq).ker ≤ Ψ.ker)
    (hu : Ψ (vertexZeroAway N q (tGamma0 N)) = 1) (hv : Ψ (vertexZeroAway N q (lGamma0 N)) = 1) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (gamma0AwayUnitsChar N q hNq) := by
  set Φ : Gamma0Fin N M →* Multiplicative A :=
    (gamma0AwayToFin N M q hMq).liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨Ψ, hker⟩ with hΦ
  have hΦΨ : Φ.comp (gamma0AwayToFin N M q hMq) = Ψ :=
    (gamma0AwayToFin N M q hMq).liftOfRightInverse_comp (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨Ψ, hker⟩
  have hu' : Φ (ParabolicFin.uG N M 1) = 1 := by
    have h := DFunLike.congr_fun hΦΨ (vertexZeroAway N q (tGamma0 N))
    rw [MonoidHom.comp_apply, gamma0AwayToFin_vertexZeroAway_tGamma0 hMq] at h
    rw [h, hu]
  have hv' : Φ (ParabolicFin.vG N M 1) = 1 := by
    have h := DFunLike.congr_fun hΦΨ (vertexZeroAway N q (lGamma0 N))
    rw [MonoidHom.comp_apply, gamma0AwayToFin_vertexZeroAway_lGamma0 hMq] at h
    rw [h, hv]
  obtain ⟨χ, hχ⟩ := Ihara.gamma0Fin_hom_factor_of_map_unipotent_eq_one hNM Φ hu' hv'
  refine ⟨χ, ?_⟩
  rw [← hΦΨ, hχ, MonoidHom.comp_assoc, gamma0FinUnitsChar_comp_gamma0AwayToFin N M q hMq hNq hNM]

private theorem gamma0Away_hom_factor_of_csp {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q)
    (hcsp : ∀ (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Ihara.ZAway q))) [K.FiniteIndex],
      ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ Ihara.principalCongruenceAway M q hMq ≤ K)
    {A : Type*} [AddCommGroup A] [Finite A] (Ψ : Gamma0Away N q →* Multiplicative A)
    (hu : Ψ (vertexZeroAway N q (tGamma0 N)) = 1) (hv : Ψ (vertexZeroAway N q (lGamma0 N)) = 1) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (gamma0AwayUnitsChar N q hqN) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hq.one_lt.ne' (Nat.coprime_zero_left q |>.mp hqN)
  haveI : NeZero N := ⟨hN0⟩

  set K : Subgroup SL(2, ZAway q) := Ψ.ker.map (Gamma0Away N q).subtype with hK
  have hΓidx : (Gamma0Away N q).index ≠ 0 := by
    have hle := principalCongruenceAway_le_gamma0Away N q hqN
    have hdvd := Subgroup.index_dvd_of_le hle
    have hNidx : (principalCongruenceAway N q hqN).index ≠ 0 := by
      show (slAwayReduction N q hqN).ker.index ≠ 0
      rw [Subgroup.index_ker]
      exact Nat.card_pos.ne'
    exact fun h0 => hNidx (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have hkeridx : Ψ.ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  haveI : K.FiniteIndex := ⟨by rw [hK, Subgroup.index_map_subtype]; exact Nat.mul_ne_zero hkeridx hΓidx⟩
  obtain ⟨M, hMq, hM0, hle⟩ := hcsp K

  have hNMq : Nat.Coprime (N * M) q := Nat.Coprime.mul_left hqN hMq
  haveI : NeZero (N * M) := ⟨Nat.mul_ne_zero hN0 hM0⟩
  have hker : (gamma0AwayToFin N (N * M) q hNMq).ker ≤ Ψ.ker := by
    intro g hg
    rw [mem_ker_gamma0AwayToFin_iff] at hg
    have hg' : (g : SL(2, ZAway q)) ∈ K :=
      hle (principalCongruenceAway_le_of_dvd q (Dvd.intro_left N rfl) hMq hNMq hg)
    exact mem_of_coe_mem_map_subtype hg'
  have hsurj : Function.Surjective (gamma0AwayToFin N (N * M) q hNMq) :=
    gamma0AwayToFin_surjective N (N * M) q hNMq (Dvd.intro M rfl) (SL2_reduction_surjective (N * M))
  exact gamma0Away_hom_factor_of_ker_le_of_map_unipotent hNMq hqN (Dvd.intro M rfl) Ψ hsurj hker hu hv

end Away
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

end Ihara
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

namespace Ihara
p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex"
p2m_open "Ihara"

open CongruenceSubgroup
open scoped MatrixGroups

private noncomputable def amalgamEquiv (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) :
    iharaAmalgam N q ≃* Gamma0Away N q :=
  MulEquiv.ofBijective (amalgamToGamma0Away N q)
    ⟨amalgamToGamma0Away_injective hq hqN, amalgamToGamma0Away_surjective N q hqN hq⟩

@[scoped simp]
private theorem amalgamEquiv_apply (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) (x : iharaAmalgam N q) :
    amalgamEquiv N q hq hqN x = amalgamToGamma0Away N q x :=
  rfl

private theorem coe_amalgamEquiv_vertex_zero (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) (g : Gamma0 N) :
    ((amalgamEquiv N q hq hqN (iharaVertex N q 0 g) : Gamma0Away N q) : SL(2, ZAway q)) =
      vertexZero N q g := by
  rw [amalgamEquiv_apply, coe_amalgamToGamma0Away, amalgamToAway_vertex_zero]

private theorem coe_amalgamEquiv_vertex_one (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) (g : Gamma0 N) :
    ((amalgamEquiv N q hq hqN (iharaVertex N q 1 g) : Gamma0Away N q) : SL(2, ZAway q)) =
      vertexOne N q g := by
  rw [amalgamEquiv_apply, coe_amalgamToGamma0Away, amalgamToAway_vertex_one]

end Ihara
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

namespace Ihara
p2m_export "Ihara" "ι₀ ι₁ slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff ZAway Gamma0Away mem_Gamma0Away vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaLift iharaLift_vertex_zero iharaLift_vertex_one zAwayToZMod zAwayToZMod_algebraMap gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway vertexOneAway gamma0AwayUnitsChar_comp_vertexZeroAway gamma0AwayUnitsChar_comp_vertexOneAway gamma0UnitsHom gamma0UnitsChar Gamma0Fin mem_Gamma0Fin castHom_apply_one_zero gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective exists_principalCongruenceAway_le_of_finiteIndex"
p2m_open "Ihara"

open CongruenceSubgroup

open scoped MatrixGroups

section AssemblyCSP

variable (N q : ℕ)

section KernelPairLift

variable {A : Type*} [AddCommGroup A]

private def levelZeroHom (φ : Additive (Gamma0 N) →+ A) : Gamma0 N →* Multiplicative A :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (φ (Additive.ofMul g)))
    (fun a b => congrArg Multiplicative.ofAdd (map_add φ (Additive.ofMul a) (Additive.ofMul b)))

private def levelOneNegHom (ψ : Additive (Gamma0 N) →+ A) : Gamma0 N →* Multiplicative A :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (-(ψ (Additive.ofMul g))))
    (fun a b => congrArg Multiplicative.ofAdd (by
      rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
        map_add, neg_add]
      rfl))

@[scoped simp]
private theorem levelZeroHom_apply (φ : Additive (Gamma0 N) →+ A) (g : Gamma0 N) :
    levelZeroHom N φ g = Multiplicative.ofAdd (φ (Additive.ofMul g)) :=
  rfl

@[scoped simp]
private theorem levelOneNegHom_apply (ψ : Additive (Gamma0 N) →+ A) (g : Gamma0 N) :
    levelOneNegHom N ψ g = Multiplicative.ofAdd (-(ψ (Additive.ofMul g))) :=
  rfl

private theorem levelHoms_compat (φ ψ : Additive (Gamma0 N) →+ A)
    (hker : ∀ γ : Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0) :
    (levelZeroHom N φ).comp (ι₀ N q) = (levelOneNegHom N ψ).comp (ι₁ N q) := by
  ext γ
  exact congrArg Multiplicative.ofAdd (eq_neg_of_add_eq_zero_left (hker γ))

private noncomputable def kernelPairLift (φ ψ : Additive (Gamma0 N) →+ A)
    (hker : ∀ γ : Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0) :
    iharaAmalgam N q →* Multiplicative A :=
  iharaLift (levelZeroHom N φ) (levelOneNegHom N ψ) (levelHoms_compat N q φ ψ hker)

private theorem kernelPairLift_vertex_zero (φ ψ : Additive (Gamma0 N) →+ A)
    (hker : ∀ γ : Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0) (g : Gamma0 N) :
    kernelPairLift N q φ ψ hker (iharaVertex N q 0 g)
      = Multiplicative.ofAdd (φ (Additive.ofMul g)) :=
  iharaLift_vertex_zero _ _ _ g

private theorem kernelPairLift_vertex_one (φ ψ : Additive (Gamma0 N) →+ A)
    (hker : ∀ γ : Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0) (g : Gamma0 N) :
    kernelPairLift N q φ ψ hker (iharaVertex N q 1 g)
      = Multiplicative.ofAdd (-(ψ (Additive.ofMul g))) :=
  iharaLift_vertex_one _ _ _ g

end KernelPairLift
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

variable {A : Type*} [AddCommGroup A]

private theorem amalgamEquiv_vertex_zero (hq : q.Prime) (hqN : N.Coprime q) (g : Gamma0 N) :
    amalgamEquiv N q hq hqN (iharaVertex N q 0 g) = vertexZeroAway N q g :=
  Subtype.ext (by rw [coe_amalgamEquiv_vertex_zero]; rfl)

private theorem amalgamEquiv_vertex_one (hq : q.Prime) (hqN : N.Coprime q) (g : Gamma0 N) :
    amalgamEquiv N q hq hqN (iharaVertex N q 1 g) = vertexOneAway N q g :=
  Subtype.ext (by rw [coe_amalgamEquiv_vertex_one]; rfl)

private theorem ihara_hom_factor_of_csp (hq : q.Prime) (hqN : N.Coprime q)
    (hcsp : ∀ (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Ihara.ZAway q))) [K.FiniteIndex],
      ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ Ihara.principalCongruenceAway M q hMq ≤ K)
    [Finite A] (φ ψ : Additive (Gamma0 N) →+ A)
    (hker : ∀ γ : Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0)
    (hφT : φ (Additive.ofMul (tGamma0 N)) = 0) (hφL : φ (Additive.ofMul (lGamma0 N)) = 0) :
    (∃ χ : Additive (ZMod N)ˣ →+ A, φ = χ.comp (gamma0UnitsChar N)) ∧
    (∃ χ : Additive (ZMod N)ˣ →+ A, ψ = χ.comp (gamma0UnitsChar N)) := by
  set e := amalgamEquiv N q hq hqN with he
  set Φ := kernelPairLift N q φ ψ hker with hΦ
  set Ψ : Gamma0Away N q →* Multiplicative A :=
    Φ.comp (e.symm : Gamma0Away N q ≃* iharaAmalgam N q).toMonoidHom with hΨ
  have hΨ0 : ∀ g : Gamma0 N, Ψ (vertexZeroAway N q g) = Multiplicative.ofAdd (φ (Additive.ofMul g)) := by
    intro g
    have hvz : e.symm ((vertexZeroAway N q g)) = iharaVertex N q 0 g := by
      rw [← amalgamEquiv_vertex_zero N q hq hqN g, ← he, MulEquiv.symm_apply_apply]
    simp only [hΨ, hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hvz, kernelPairLift_vertex_zero]
  have hu : Ψ (vertexZeroAway N q (tGamma0 N)) = 1 := by rw [hΨ0, hφT, ofAdd_zero]
  have hv : Ψ (vertexZeroAway N q (lGamma0 N)) = 1 := by rw [hΨ0, hφL, ofAdd_zero]
  obtain ⟨χ', hχ'⟩ := gamma0Away_hom_factor_of_csp hq hqN hcsp Ψ hu hv

  have hval0 : ∀ g : Gamma0 N, Φ (iharaVertex N q 0 g) = χ' (gamma0UnitsHom N g) := by
    intro g
    have hv : e.symm ((vertexZeroAway N q g)) = iharaVertex N q 0 g := by
      rw [← amalgamEquiv_vertex_zero N q hq hqN g, ← he, MulEquiv.symm_apply_apply]
    have h := congrArg (fun F => F (vertexZeroAway N q g)) hχ'
    simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [hv] at h
    rw [h]
    have hc := congrArg (fun F => F g) (gamma0AwayUnitsChar_comp_vertexZeroAway N q hqN)
    simp only [MonoidHom.comp_apply] at hc
    rw [hc]
  have hval1 : ∀ g : Gamma0 N, Φ (iharaVertex N q 1 g) = χ' (gamma0UnitsHom N g) := by
    intro g
    have hv1 : e.symm ((vertexOneAway N q g)) = iharaVertex N q 1 g := by
      rw [← amalgamEquiv_vertex_one N q hq hqN g, ← he, MulEquiv.symm_apply_apply]
    have h := congrArg (fun F => F (vertexOneAway N q g)) hχ'
    simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [hv1] at h
    rw [h]
    have hc := congrArg (fun F => F g) (gamma0AwayUnitsChar_comp_vertexOneAway N q hqN)
    simp only [MonoidHom.comp_apply] at hc
    rw [hc]
  constructor
  · refine ⟨AddMonoidHom.toMultiplicativeRight.symm χ', ?_⟩
    ext a
    have h0 := (kernelPairLift_vertex_zero N q φ ψ hker (Additive.toMul a)).symm.trans
      (hval0 (Additive.toMul a))
    have := congrArg Multiplicative.toAdd h0
    simp at this
    exact this
  · refine ⟨-(AddMonoidHom.toMultiplicativeRight.symm χ'), ?_⟩
    ext a
    have h1 := (kernelPairLift_vertex_one N q φ ψ hker (Additive.toMul a)).symm.trans
      (hval1 (Additive.toMul a))
    have := congrArg Multiplicative.toAdd h1
    have hψ : -(ψ a) = Multiplicative.toAdd (χ' (gamma0UnitsHom N (Additive.toMul a))) := by
      simpa using this
    have := congrArg Neg.neg hψ
    rw [neg_neg] at this
    simp at this ⊢
    exact this

end AssemblyCSP
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

end Ihara
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

namespace IharaModThree

open CongruenceSubgroup

private def IharaParabolicFactoring (N q : ℕ) : Prop :=
  ∀ (φ ψ : Additive (Gamma0 N) →+ ℤ),
    φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
    ψ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ →
    (∀ γ : Gamma0 (N * q),
      (Int.castAddHom (ZMod 3)).comp φ (Ihara.ι₀ N q γ) + (Int.castAddHom (ZMod 3)).comp ψ (Ihara.ι₁ N q γ) = 0) →
    (∃ χ : Additive (ZMod N)ˣ →+ ZMod 3,
        (Int.castAddHom (ZMod 3)).comp φ = χ.comp (Ihara.gamma0UnitsChar N)) ∧
    (∃ χ : Additive (ZMod N)ˣ →+ ZMod 3,
        (Int.castAddHom (ZMod 3)).comp ψ = χ.comp (Ihara.gamma0UnitsChar N))

private theorem iharaParabolicFactoring_of_csp (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hcsp : ∀ (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Ihara.ZAway q))) [K.FiniteIndex],
      ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ Ihara.principalCongruenceAway M q hMq ≤ K) :
    IharaParabolicFactoring N q := by
  unfold IharaParabolicFactoring
  intro φ ψ hφ hψ hker
  have hNq : N.Coprime q := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN))
  have hφ' := (ModularCurve.Period.mem_parabolicHoms_iff).mp hφ
  have hφT : (Int.castAddHom (ZMod 3)).comp φ (Additive.ofMul (Ihara.tGamma0 N)) = 0 := by
    rw [AddMonoidHom.comp_apply, hφ' _ (Ihara.trace_sq_tGamma0 N), map_zero]
  have hφL : (Int.castAddHom (ZMod 3)).comp φ (Additive.ofMul (Ihara.lGamma0 N)) = 0 := by
    rw [AddMonoidHom.comp_apply, hφ' _ (Ihara.trace_sq_lGamma0 N), map_zero]
  exact Ihara.ihara_hom_factor_of_csp N q hq hNq hcsp ((Int.castAddHom (ZMod 3)).comp φ)
    ((Int.castAddHom (ZMod 3)).comp ψ) hker hφT hφL

end IharaModThree
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

namespace IharaModThree

open CongruenceSubgroup

private theorem kernelPair_mod_three_of_dvd (N q : ℕ) (φ ψ : Additive (Gamma0 N) →+ ℤ)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      (3 : ℤ) ∣ φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ)) (γ : Gamma0 (N * q)) :
    (Int.castAddHom (ZMod 3)).comp φ (Ihara.ι₀ N q γ) + (Int.castAddHom (ZMod 3)).comp ψ (Ihara.ι₁ N q γ) = 0 := by
  have h := hker γ
  have h3 : ((φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast h)
  show ((φ (Ihara.ι₀ N q γ) : ℤ) : ZMod 3) + ((ψ (Ihara.ι₁ N q γ) : ℤ) : ZMod 3) = 0
  rw [← Int.cast_add]
  exact h3

private theorem exists_eq_three_smul_of_factors (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ : Additive (Gamma0 N) →+ ℤ) (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)
    (hfac : ∃ χ : Additive (ZMod N)ˣ →+ ZMod 3,
      (Int.castAddHom (ZMod 3)).comp φ = χ.comp (Ihara.gamma0UnitsChar N)) :
    ∃ φ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (3 : ℤ) • φ' := by
  obtain ⟨χ, hχ⟩ := hfac
  have hTpar : HeckeEis.heckeOperatorHom N ℓ ℤ φ ∈ ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ :=
    ModularCurve.Period.heckeOperatorHom_preserves_parabolic N ℓ ℤ φ
      (ModularCurve.Period.mem_parabolicHoms_iff.1 hφ)
  have hmem : HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ ∈
      ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ :=
    Submodule.sub_mem _ hTpar (Submodule.smul_mem _ ((ℓ : ℤ) + 1) hφ)
  have hE : HeckeEis.heckeOperatorHom N ℓ (ZMod 3) ((Int.castAddHom (ZMod 3)).comp φ) =
      (ℓ + 1) • (Int.castAddHom (ZMod 3)).comp φ := by
    rw [hχ]
    exact HeckeEis.heckeOperatorHom_comp_gamma0UnitsChar N (ZMod 3) hℓ hℓN χ
  have hred : (Int.castAddHom (ZMod 3)).comp (HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ) = 0 := by
    refine AddMonoidHom.ext fun g => ?_
    show (((HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ) g : ℤ) : ZMod 3) = 0
    have hnat := DFunLike.congr_fun (HeckeEis.postcomp_heckeOperatorHom N ℓ (Int.castAddHom (ZMod 3)) φ) g
    have hEg := DFunLike.congr_fun hE g
    simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom] at hnat
    rw [AddMonoidHom.sub_apply, Int.cast_sub]
    rw [show ((((ℓ : ℤ) + 1) • φ) g : ℤ) = ((ℓ : ℤ) + 1) * φ g from rfl]
    rw [hnat, hEg]
    rw [show (((ℓ + 1) • ((Int.castAddHom (ZMod 3)).comp φ)) g) =
      (ℓ + 1) • (((φ g : ℤ)) : ZMod 3) from rfl]
    rw [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨x', hx'⟩ :=
    (LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff (p := 3)
      (⟨_, hmem⟩ : ModularCurve.Period.parabolicHoms ℤ (Gamma0 N) ℤ)).1 hred
  refine ⟨(x' : Additive (Gamma0 N) →+ ℤ), ?_⟩
  have h := congrArg Subtype.val hx'
  rw [Submodule.coe_smul, Nat.cast_ofNat] at h
  exact h

private theorem head_of_factoring (N q : ℕ) (hfac : IharaParabolicFactoring N q)
    (hq : q.Prime) (hqN : ¬ q ∣ N)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hψ : ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      (3 : ℤ) ∣ φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ))
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q) :
    (∃ φ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (3 : ℤ) • φ') ∧
    (∃ ψ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = (3 : ℤ) • ψ') := by
  have _hq := hq
  have _hqN := hqN
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (Dvd.dvd.mul_right h q)
  obtain ⟨hφfac, hψfac⟩ := hfac φ ψ hφ hψ (kernelPair_mod_three_of_dvd N q φ ψ hker)
  exact ⟨exists_eq_three_smul_of_factors N hℓ hℓN φ hφ hφfac,
    exists_eq_three_smul_of_factors N hℓ hℓN ψ hψ hψfac⟩

end IharaModThree
p2m_reactivate "P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.Ihara.ParabolicFin"

theorem solution
    (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hψ : ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      (3 : ℤ) ∣ φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ))
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q) :
    (∃ φ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (3 : ℤ) • φ') ∧
    (∃ ψ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = (3 : ℤ) • ψ') :=
  IharaModThree.head_of_factoring N q
    (IharaModThree.iharaParabolicFactoring_of_csp N q hq hqN fun K hK =>
      @Ihara.exists_principalCongruenceAway_le_of_finiteIndex q hq K hK)
    hq hqN φ ψ hφ hψ hker hℓ hℓM

end S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
end P2MW
export P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel (solution)
