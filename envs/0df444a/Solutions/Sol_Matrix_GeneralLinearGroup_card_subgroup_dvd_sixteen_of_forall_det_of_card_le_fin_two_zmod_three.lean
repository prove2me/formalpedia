-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2b6f40db-7b5d-579e-a7f8-44ad21daa249

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false
set_option linter.deprecated false

section

open scoped MatrixGroups Pointwise

namespace FLT
namespace Gapsw2T1Gl2F3Lattice

theorem gapsw2_t1_card_gl2_zmod3_eq_48 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

abbrev gapsw2T1SplitCartanPred (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Prop :=
  (M 0 1 = 0 ∧ M 1 0 = 0) ∨ (M 0 0 = 0 ∧ M 1 1 = 0)

abbrev gapsw2T1NonsplitCartanPred (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Prop :=
  (M 0 0 = M 1 1 ∧ M 0 1 = -(M 1 0)) ∨ (M 0 0 = -(M 1 1) ∧ M 0 1 = M 1 0)

theorem gapsw2_t1_mulVec_fin_two_apply (M : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (v : Fin 2 → ZMod 3) (i : Fin 2) :
    Matrix.mulVec M v i = M i 0 * v 0 + M i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 4000000 in

theorem gapsw2_t1_order_three_exists_fixed_vector_scalar :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * M = 1 → M ≠ 1 →
      ∃ a b : ZMod 3, ¬(a = 0 ∧ b = 0) ∧
        M 0 0 * a + M 0 1 * b = a ∧ M 1 0 * a + M 1 1 * b = b := by
  decide +kernel

theorem gapsw2_t1_order_three_exists_fixed_vector :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * M = 1 → M ≠ 1 →
      ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ Matrix.mulVec M v = v := by
  intro M h3 hne
  obtain ⟨a, b, hab, h0, h1⟩ := gapsw2_t1_order_three_exists_fixed_vector_scalar M h3 hne
  refine ⟨![a, b], ?_, ?_⟩
  · intro hv
    exact hab ⟨by simpa using congrFun hv 0, by simpa using congrFun hv 1⟩
  · funext i
    fin_cases i
    · simpa [gapsw2_t1_mulVec_fin_two_apply] using h0
    · simpa [gapsw2_t1_mulVec_fin_two_apply] using h1

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 4000000 in

theorem gapsw2_t1_order_three_fixed_line_unique_scalar :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * M = 1 → M ≠ 1 →
      ∀ a b x y : ZMod 3, ¬(a = 0 ∧ b = 0) →
        M 0 0 * a + M 0 1 * b = a → M 1 0 * a + M 1 1 * b = b →
        M 0 0 * x + M 0 1 * y = x → M 1 0 * x + M 1 1 * y = y →
        ∃ c : ZMod 3, x = c * a ∧ y = c * b := by
  decide +kernel

theorem gapsw2_t1_order_three_fixed_line_unique :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * M = 1 → M ≠ 1 →
      ∀ v w : Fin 2 → ZMod 3, v ≠ 0 → Matrix.mulVec M v = v → Matrix.mulVec M w = w →
        ∃ c : ZMod 3, w = c • v := by
  intro M h3 hne v w hv0 hvfix hwfix
  have hva := congrFun hvfix 0
  have hvb := congrFun hvfix 1
  have hwa := congrFun hwfix 0
  have hwb := congrFun hwfix 1
  rw [gapsw2_t1_mulVec_fin_two_apply] at hva hvb hwa hwb
  have hv0' : ¬(v 0 = 0 ∧ v 1 = 0) := by
    intro h
    apply hv0
    funext i
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  obtain ⟨c, hcx, hcy⟩ := gapsw2_t1_order_three_fixed_line_unique_scalar M h3 hne
    (v 0) (v 1) (w 0) (w 1) hv0' hva hvb hwa hwb
  refine ⟨c, funext fun i => ?_⟩
  fin_cases i
  · simpa using hcx
  · simpa using hcy

def gapsw2T1U : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 0, 1]

def gapsw2T1L : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 1, 1]

def gapsw2T1UpowTable : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![1, !![1, 1; 0, 1], !![1, 2; 0, 1]]

def gapsw2T1LpowTable : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![1, !![1, 0; 1, 1], !![1, 0; 2, 1]]

theorem gapsw2_t1_UpowTable_eq_pow :
    ∀ a : Fin 3, gapsw2T1UpowTable a = gapsw2T1U ^ (a : ℕ) := by
  decide +kernel

theorem gapsw2_t1_LpowTable_eq_pow :
    ∀ a : Fin 3, gapsw2T1LpowTable a = gapsw2T1L ^ (a : ℕ) := by
  decide +kernel

theorem gapsw2_t1_L_sq_sq :
    gapsw2T1L * gapsw2T1L * (gapsw2T1L * gapsw2T1L) = gapsw2T1L := by
  decide +kernel

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 4000000 in

theorem gapsw2_t1_order_three_pair_simultaneous_conjugation_scalar :
    ∀ u w : Matrix (Fin 2) (Fin 2) (ZMod 3),
      u * u * u = 1 → u ≠ 1 → w * w * w = 1 → w ≠ 1 →
      (∀ a b : ZMod 3,
        u 0 0 * a + u 0 1 * b = a → u 1 0 * a + u 1 1 * b = b →
        w 0 0 * a + w 0 1 * b = a → w 1 0 * a + w 1 1 * b = b →
        a = 0 ∧ b = 0) →
      ∃ g : Matrix (Fin 2) (Fin 2) (ZMod 3),
        g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 ∧ g * gapsw2T1U = u * g ∧
          (g * gapsw2T1L = w * g ∨ g * (gapsw2T1L * gapsw2T1L) = w * g) := by
  decide +kernel

theorem gapsw2_t1_order_three_pair_simultaneous_conjugation :
    ∀ u w : Matrix (Fin 2) (Fin 2) (ZMod 3),
      u * u * u = 1 → u ≠ 1 → w * w * w = 1 → w ≠ 1 →
      (∀ v : Fin 2 → ZMod 3, Matrix.mulVec u v = v → Matrix.mulVec w v = v → v = 0) →
      ∃ g : Matrix (Fin 2) (Fin 2) (ZMod 3),
        g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 ∧ g * gapsw2T1U = u * g ∧
          (g * gapsw2T1L = w * g ∨ g * (gapsw2T1L * gapsw2T1L) = w * g) := by
  intro u w hu3 hu1 hw3 hw1 hcomm
  refine gapsw2_t1_order_three_pair_simultaneous_conjugation_scalar u w hu3 hu1 hw3 hw1 ?_
  intro a b hua hub hwa hwb
  have h0 : (![a, b] : Fin 2 → ZMod 3) = 0 := by
    refine hcomm ![a, b] ?_ ?_
    · funext i
      fin_cases i
      · simpa [gapsw2_t1_mulVec_fin_two_apply] using hua
      · simpa [gapsw2_t1_mulVec_fin_two_apply] using hub
    · funext i
      fin_cases i
      · simpa [gapsw2_t1_mulVec_fin_two_apply] using hwa
      · simpa [gapsw2_t1_mulVec_fin_two_apply] using hwb
  exact ⟨by simpa using congrFun h0 0, by simpa using congrFun h0 1⟩

theorem gapsw2_t1_sl2_bruhat_four_factor :
    ∀ S : Matrix (Fin 2) (Fin 2) (ZMod 3), S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 →
      ∃ a b c d : Fin 3, S = gapsw2T1UpowTable a * gapsw2T1LpowTable b *
        gapsw2T1UpowTable c * gapsw2T1LpowTable d := by
  decide +kernel

theorem gapsw2_t1_nonsplit_pred_mul :
    ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 3),
      gapsw2T1NonsplitCartanPred A → gapsw2T1NonsplitCartanPred B →
        gapsw2T1NonsplitCartanPred (A * B) := by
  decide +kernel

theorem gapsw2_t1_nonsplit_pred_inv :
    ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 3),
      gapsw2T1NonsplitCartanPred A → A * B = 1 → gapsw2T1NonsplitCartanPred B := by
  decide +kernel

theorem gapsw2_t1_nonsplit_pred_one :
    gapsw2T1NonsplitCartanPred (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  decide +kernel

theorem gapsw2_t1_split_pred_mul :
    ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 3),
      gapsw2T1SplitCartanPred A → gapsw2T1SplitCartanPred B →
        gapsw2T1SplitCartanPred (A * B) := by
  decide +kernel

theorem gapsw2_t1_split_pred_inv :
    ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 3),
      gapsw2T1SplitCartanPred A → A * B = 1 → gapsw2T1SplitCartanPred B := by
  decide +kernel

theorem gapsw2_t1_split_pred_one :
    gapsw2T1SplitCartanPred (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  decide +kernel

def gapsw2T1CartanNonsplitNormalizerGL3 : Subgroup (GL (Fin 2) (ZMod 3)) where
  carrier := {g : GL (Fin 2) (ZMod 3) |
    gapsw2T1NonsplitCartanPred (g : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := by
    show gapsw2T1NonsplitCartanPred
      ((1 : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    rw [Units.val_one]
    exact gapsw2_t1_nonsplit_pred_one
  mul_mem' := by
    intro a b ha hb
    show gapsw2T1NonsplitCartanPred
      ((a * b : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    rw [Units.val_mul]
    exact gapsw2_t1_nonsplit_pred_mul _ _ ha hb
  inv_mem' := by
    intro a ha
    show gapsw2T1NonsplitCartanPred
      ((a⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    refine gapsw2_t1_nonsplit_pred_inv (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) _ ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

def gapsw2T1CartanSplitNormalizerGL3 : Subgroup (GL (Fin 2) (ZMod 3)) where
  carrier := {g : GL (Fin 2) (ZMod 3) |
    gapsw2T1SplitCartanPred (g : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := by
    show gapsw2T1SplitCartanPred
      ((1 : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    rw [Units.val_one]
    exact gapsw2_t1_split_pred_one
  mul_mem' := by
    intro a b ha hb
    show gapsw2T1SplitCartanPred
      ((a * b : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    rw [Units.val_mul]
    exact gapsw2_t1_split_pred_mul _ _ ha hb
  inv_mem' := by
    intro a ha
    show gapsw2T1SplitCartanPred
      ((a⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    refine gapsw2_t1_split_pred_inv (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) _ ha ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem gapsw2_t1_nonsplit_units_subtype_card :
    Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod 3) //
      gapsw2T1NonsplitCartanPred M ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0} = 16 := by
  decide +kernel

def gapsw2T1NonsplitUnitsEquiv :
    ↥gapsw2T1CartanNonsplitNormalizerGL3 ≃
      {M : Matrix (Fin 2) (Fin 2) (ZMod 3) //
        gapsw2T1NonsplitCartanPred M ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0} where
  toFun x := ⟨((x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)),
    x.property, by
      have h := Matrix.GeneralLinearGroup.det_ne_zero (x : GL (Fin 2) (ZMod 3))
      rwa [Matrix.det_fin_two] at h⟩
  invFun M := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M.1
    (by rw [Matrix.det_fin_two]; exact M.2.2), M.2.1⟩
  left_inv x := Subtype.ext (Units.ext rfl)
  right_inv M := Subtype.ext rfl

theorem gapsw2_t1_card_cartanNonsplitNormalizerGL3 :
    Nat.card ↥gapsw2T1CartanNonsplitNormalizerGL3 = 16 := by
  rw [Nat.card_congr gapsw2T1NonsplitUnitsEquiv, Nat.card_eq_fintype_card]
  exact gapsw2_t1_nonsplit_units_subtype_card

set_option maxHeartbeats 3200000 in

theorem gapsw2_t1_gl2F3_subgroup_dichotomy (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hirr : ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v)
    (hns : ∀ g : GL (Fin 2) (ZMod 3),
      ¬ ∀ h ∈ H, g⁻¹ * h * g ∈ gapsw2T1CartanNonsplitNormalizerGL3)
    (_hsp : ∀ g : GL (Fin 2) (ZMod 3),
      ¬ ∀ h ∈ H, g⁻¹ * h * g ∈ gapsw2T1CartanSplitNormalizerGL3)
    (hdet : ∀ d : (ZMod 3)ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = d) :
    H = ⊤ := by

  suffices hSL : ∀ t : GL (Fin 2) (ZMod 3),
      ((t : Matrix (Fin 2) (Fin 2) (ZMod 3))).det = 1 → t ∈ H by
    rw [Subgroup.eq_top_iff']
    intro x
    obtain ⟨h, hh, hdx⟩ := hdet (Matrix.GeneralLinearGroup.det x)
    have h1 : Matrix.GeneralLinearGroup.det (h⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hdx, inv_mul_cancel]
    have h2 := congrArg (Units.val) h1
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
    have h3 : x = h * (h⁻¹ * x) := (mul_inv_cancel_left h x).symm
    rw [h3]
    exact mul_mem hh (hSL _ h2)
  by_cases h3 : 3 ∣ Nat.card ↥H

  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3

    have hu3' : orderOf (x : GL (Fin 2) (ZMod 3)) = 3 := (Subgroup.orderOf_coe x).trans hx
    have hu_mem : (x : GL (Fin 2) (ZMod 3)) ∈ H := x.2
    have hu_pow : (x : GL (Fin 2) (ZMod 3)) ^ 3 = 1 := by

      have h := pow_orderOf_eq_one (x : GL (Fin 2) (ZMod 3))
      rwa [hu3'] at h
    have hu_ne : (x : GL (Fin 2) (ZMod 3)) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hu3'
      omega
    have hum3 : ((x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
      have h1 := congrArg (Units.val) hu_pow
      rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at h1
    have hum_ne : ((x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := by
      intro h
      exact hu_ne (Units.ext (by rw [h, Units.val_one]))
    obtain ⟨v, hv0, hvfix⟩ := gapsw2_t1_order_three_exists_fixed_vector _ hum3 hum_ne

    have hex : ∃ b, b ∈ H ∧ ¬ ∃ c : ZMod 3,
        Matrix.mulVec (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v := by
      by_contra hno
      push_neg at hno
      exact hirr ⟨v, hv0, fun h hh => hno h hh⟩
    obtain ⟨b, hbH, hbnc⟩ := hex

    set u : GL (Fin 2) (ZMod 3) := (x : GL (Fin 2) (ZMod 3))
    set w : GL (Fin 2) (ZMod 3) := MulAut.conj b u with hw_def
    have hwH : w ∈ H := by
      rw [hw_def, MulAut.conj_apply]
      exact mul_mem (mul_mem hbH hu_mem) (inv_mem hbH)
    have hw_pow : w ^ 3 = 1 := by
      rw [hw_def, ← map_pow, hu_pow, map_one]
    have hw_ne : w ≠ 1 := by
      intro hweq
      have h1 := congrArg (MulAut.conj b).symm hweq
      rw [hw_def, MulEquiv.symm_apply_apply, map_one] at h1
      exact hu_ne h1
    have hwm3 : (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
      have h1 := congrArg (Units.val) hw_pow
      rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at h1
    have hwm_ne : (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := by
      intro h
      exact hw_ne (Units.ext (by rw [h, Units.val_one]))

    have hwb : w * b = b * u := by
      rw [hw_def, MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one]
    have hwbm : (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (u : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      have h1 := congrArg (Units.val) hwb
      rwa [Units.val_mul, Units.val_mul] at h1

    have hv'0 : Matrix.mulVec (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) v ≠ 0 := by
      intro h0
      apply hv0
      have h1 : Matrix.mulVec ((b⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
          (Matrix.mulVec (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) v) =
            Matrix.mulVec ((b⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 := by
        rw [h0]
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have hv'fix : Matrix.mulVec (w : Matrix (Fin 2) (Fin 2) (ZMod 3))
        (Matrix.mulVec (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) v) =
          Matrix.mulVec (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) v := by
      rw [Matrix.mulVec_mulVec, hwbm, ← Matrix.mulVec_mulVec, hvfix]

    have hguard : ∀ z : Fin 2 → ZMod 3,
        Matrix.mulVec (u : Matrix (Fin 2) (Fin 2) (ZMod 3)) z = z →
        Matrix.mulVec (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) z = z → z = 0 := by
      intro z hz1 hz2
      by_contra hz0
      obtain ⟨c, hzc⟩ :=
        gapsw2_t1_order_three_fixed_line_unique _ hum3 hum_ne v z hv0 hvfix hz1
      have hc0 : c ≠ 0 := fun hc => hz0 (by rw [hzc, hc, zero_smul])
      have hwv : Matrix.mulVec (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = v := by
        have h2 : c • Matrix.mulVec (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v := by
          rw [← Matrix.mulVec_smul, ← hzc, hz2]
        have h3 := congrArg (fun t => c⁻¹ • t) h2
        simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h3
        exact h3
      obtain ⟨c', hvc'⟩ := gapsw2_t1_order_three_fixed_line_unique _ hwm3 hwm_ne
        (Matrix.mulVec (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) v) v hv'0 hv'fix hwv
      have hc'0 : c' ≠ 0 := fun hc' => hv0 (by rw [hvc', hc', zero_smul])
      refine hbnc ⟨c'⁻¹, ?_⟩
      have h4 := congrArg (fun t => c'⁻¹ • t) hvc'
      simp only [smul_smul, inv_mul_cancel₀ hc'0, one_smul] at h4
      exact h4.symm

    obtain ⟨gm, hgdet, hgU, hgL⟩ := gapsw2_t1_order_three_pair_simultaneous_conjugation
      _ _ hum3 hum_ne hwm3 hwm_ne hguard
    set gU : GL (Fin 2) (ZMod 3) :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero gm
        (by rw [Matrix.det_fin_two]; exact hgdet)
    have hgU' : ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        gapsw2T1U = (u : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := hgU
    have hinv_l' : ((gU⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have huStd : ((gU⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        (u : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = gapsw2T1U := by
      rw [mul_assoc, ← hgU', ← mul_assoc, hinv_l', one_mul]

    obtain ⟨l, hlval, hlφ⟩ : ∃ l : GL (Fin 2) (ZMod 3),
        ((l : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = gapsw2T1L ∧
          MulAut.conj gU l ∈ H := by
      rcases hgL with hbr | hbr
      · refine ⟨gU⁻¹ * w * gU, ?_, ?_⟩
        · have hbr' : ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
              gapsw2T1L = (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
                ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := hbr
          rw [Units.val_mul, Units.val_mul, mul_assoc, ← hbr', ← mul_assoc, hinv_l',
            one_mul]
        · have h7 : gU⁻¹ * w * gU = (MulAut.conj gU).symm w := by
            rw [MulAut.conj_symm_apply]
          rw [h7, MulEquiv.apply_symm_apply]
          exact hwH
      · refine ⟨(gU⁻¹ * w * gU) ^ 2, ?_, ?_⟩
        · have hbr' : ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
              (gapsw2T1L * gapsw2T1L) = (w : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
                ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := hbr
          have h8 : ((gU⁻¹ * w * gU : GL (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)) = gapsw2T1L * gapsw2T1L := by
            rw [Units.val_mul, Units.val_mul, mul_assoc, ← hbr', ← mul_assoc, hinv_l',
              one_mul]
          rw [Units.val_pow_eq_pow_val, h8, pow_two]
          exact gapsw2_t1_L_sq_sq
        · have h7 : gU⁻¹ * w * gU = (MulAut.conj gU).symm w := by
            rw [MulAut.conj_symm_apply]
          rw [h7, map_pow, MulEquiv.apply_symm_apply]
          exact pow_mem hwH 2

    intro t htdet
    have hsval : ((gU⁻¹ * t * gU : GL (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm]
      have h9 : ((gU⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det *
          ((gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
        rw [← Matrix.det_mul, hinv_l', Matrix.det_one]
      rw [h9, one_mul]
      exact htdet
    have hsentry : ((gU⁻¹ * t * gU : GL (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 *
        ((gU⁻¹ * t * gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1 -
        ((gU⁻¹ * t * gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1 *
        ((gU⁻¹ * t * gU : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact hsval
    obtain ⟨a, b2, c, d, hfact⟩ := gapsw2_t1_sl2_bruhat_four_factor _ hsentry
    simp only [gapsw2_t1_UpowTable_eq_pow, gapsw2_t1_LpowTable_eq_pow] at hfact
    simp only [Units.val_mul] at hfact

    have hunit : gU⁻¹ * t * gU = (gU⁻¹ * u * gU) ^ (a : ℕ) * l ^ (b2 : ℕ) *
        (gU⁻¹ * u * gU) ^ (c : ℕ) * l ^ (d : ℕ) := by
      refine Units.ext ?_
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [huStd, hlval]
      exact hfact
    have hconj : MulAut.conj gU (gU⁻¹ * t * gU) = t := by
      have h7 : gU⁻¹ * t * gU = (MulAut.conj gU).symm t := by
        rw [MulAut.conj_symm_apply]
      rw [h7, MulEquiv.apply_symm_apply]
    have hcu : MulAut.conj gU (gU⁻¹ * u * gU) = u := by
      have h7 : gU⁻¹ * u * gU = (MulAut.conj gU).symm u := by
        rw [MulAut.conj_symm_apply]
      rw [h7, MulEquiv.apply_symm_apply]
    have ht' : t = MulAut.conj gU ((gU⁻¹ * u * gU) ^ (a : ℕ) * l ^ (b2 : ℕ) *
        (gU⁻¹ * u * gU) ^ (c : ℕ) * l ^ (d : ℕ)) := by
      rw [← hunit, hconj]

    rw [ht', map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hcu]
    exact mul_mem (mul_mem (mul_mem (pow_mem hu_mem _) (pow_mem hlφ _))
      (pow_mem hu_mem _)) (pow_mem hlφ _)

  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd48 : Nat.card ↥H ∣ 48 := by
      have h := Subgroup.card_subgroup_dvd_card H
      rwa [gapsw2_t1_card_gl2_zmod3_eq_48] at h
    have hcop : Nat.Coprime (Nat.card ↥H) 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
    have h16 : Nat.card ↥H ∣ 16 := by
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [show (16 * 3 : ℕ) = 48 by norm_num]
      exact hdvd48

    have h16' : Nat.card ↥H ∣ 2 ^ 4 := by
      have h24 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h24]
      exact h16
    obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h16'
    have hp2 : IsPGroup 2 ↥H := IsPGroup.iff_card.mpr ⟨k, hk⟩
    obtain ⟨S, hHS⟩ := hp2.exists_le_sylow
    have hpN : IsPGroup 2 ↥gapsw2T1CartanNonsplitNormalizerGL3 :=
      IsPGroup.iff_card.mpr
        ⟨4, by rw [gapsw2_t1_card_cartanNonsplitNormalizerGL3]; norm_num⟩
    obtain ⟨S₀, hS₀le⟩ := hpN.exists_le_sylow
    have hcardle : Nat.card ↥(S₀ : Subgroup (GL (Fin 2) (ZMod 3))) ≤ 16 := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp S₀.isPGroup'
      have hd : Nat.card ↥(S₀ : Subgroup (GL (Fin 2) (ZMod 3))) ∣ 48 := by
        have h := Subgroup.card_subgroup_dvd_card (S₀ : Subgroup (GL (Fin 2) (ZMod 3)))
        rwa [gapsw2_t1_card_gl2_zmod3_eq_48] at h
      rw [hm] at hd ⊢
      have hc : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by decide)
      have hd16 : (2 : ℕ) ^ m ∣ 16 := by
        refine hc.dvd_of_dvd_mul_right ?_
        rw [show (16 * 3 : ℕ) = 48 by norm_num]
        exact hd
      exact Nat.le_of_dvd (by norm_num) hd16
    have hNeq : gapsw2T1CartanNonsplitNormalizerGL3 =
        (S₀ : Subgroup (GL (Fin 2) (ZMod 3))) :=
      Subgroup.eq_of_le_of_card_ge hS₀le
        (by rw [gapsw2_t1_card_cartanNonsplitNormalizerGL3]; exact hcardle)
    haveI : Finite (Sylow 2 (GL (Fin 2) (ZMod 3))) :=
      Finite.of_injective
        (fun P : Sylow 2 (GL (Fin 2) (ZMod 3)) =>
          ((P : Subgroup (GL (Fin 2) (ZMod 3))) : Set (GL (Fin 2) (ZMod 3))))
        (fun P Q h => Sylow.ext (SetLike.coe_injective h))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 2) (ZMod 3)) S₀ S
    have hScoe : (S : Subgroup (GL (Fin 2) (ZMod 3))) =
        MulAut.conj g • gapsw2T1CartanNonsplitNormalizerGL3 := by
      rw [← hg, Sylow.coe_subgroup_smul, ← hNeq]
    refine (hns g (fun h' hh' => ?_)).elim
    have hx : h' ∈ MulAut.conj g • gapsw2T1CartanNonsplitNormalizerGL3 := by
      rw [← hScoe]
      exact hHS hh'
    have hy := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx
    rwa [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv] at hy

end FLT.Gapsw2T1Gl2F3Lattice

end

section

open Module NumberField

open scoped IntermediateField NumberField MatrixGroups

namespace FLT
namespace Gapsw6W4SmallDegreeImageDescent

open FLT.Gapsw2T1Gl2F3Lattice

local instance gapsw6_w4_isAlgebraicQbar :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 4000000 in

theorem gapsw6_w4_split_units_subtype_card :
    Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod 3) //
      gapsw2T1SplitCartanPred M ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0} = 8 := by
  decide +kernel

def gapsw6W4SplitUnitsEquiv :
    ↥gapsw2T1CartanSplitNormalizerGL3 ≃
      {M : Matrix (Fin 2) (Fin 2) (ZMod 3) //
        gapsw2T1SplitCartanPred M ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0} where
  toFun x := ⟨((x : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)),
    x.property, by
      have h := Matrix.GeneralLinearGroup.det_ne_zero (x : GL (Fin 2) (ZMod 3))
      rwa [Matrix.det_fin_two] at h⟩
  invFun M := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M.1
    (by rw [Matrix.det_fin_two]; exact M.2.2), M.2.1⟩
  left_inv x := Subtype.ext (Units.ext rfl)
  right_inv M := Subtype.ext rfl

theorem gapsw6_w4_card_cartanSplitNormalizerGL3 :
    Nat.card ↥gapsw2T1CartanSplitNormalizerGL3 = 8 := by
  rw [Nat.card_congr gapsw6W4SplitUnitsEquiv, Nat.card_eq_fintype_card]
  exact gapsw6_w4_split_units_subtype_card

theorem gapsw6_w4_card_dvd_of_conj_le
    (H N : Subgroup (GL (Fin 2) (ZMod 3))) (g : GL (Fin 2) (ZMod 3))
    (hcontain : ∀ h ∈ H, g⁻¹ * h * g ∈ N) :
    Nat.card ↥H ∣ Nat.card ↥N := by
  have hinj : Function.Injective
      ((MulAut.conj g⁻¹).toMonoidHom :
        GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ZMod 3)) :=
    (MulAut.conj g⁻¹).injective
  have hle : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ N := by
    rintro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    show (MulAut.conj g⁻¹) h ∈ N
    rw [MulAut.conj_apply, inv_inv]
    exact hcontain h hh
  have hcard : Nat.card ↥H = Nat.card ↥(H.map (MulAut.conj g⁻¹).toMonoidHom) :=
    Nat.card_congr (Subgroup.equivMapOfInjective H _ hinj).toEquiv
  rw [hcard]
  exact Subgroup.card_dvd_of_le hle

theorem gapsw6_w4_census_cartan_containment
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hirr : ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v)
    (hdet : ∀ d : (ZMod 3)ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = d)
    (hle : Nat.card ↥H ≤ 24) :
    (∃ g : GL (Fin 2) (ZMod 3),
      ∀ h ∈ H, g⁻¹ * h * g ∈ gapsw2T1CartanNonsplitNormalizerGL3) ∨
    (∃ g : GL (Fin 2) (ZMod 3),
      ∀ h ∈ H, g⁻¹ * h * g ∈ gapsw2T1CartanSplitNormalizerGL3) := by
  by_contra hcon
  have hns : ∀ g : GL (Fin 2) (ZMod 3),
      ¬ ∀ h ∈ H, g⁻¹ * h * g ∈ gapsw2T1CartanNonsplitNormalizerGL3 :=
    fun g hg => hcon (Or.inl ⟨g, hg⟩)
  have hsp : ∀ g : GL (Fin 2) (ZMod 3),
      ¬ ∀ h ∈ H, g⁻¹ * h * g ∈ gapsw2T1CartanSplitNormalizerGL3 :=
    fun g hg => hcon (Or.inr ⟨g, hg⟩)
  have htop := gapsw2_t1_gl2F3_subgroup_dichotomy H hirr hns hsp hdet
  have hcard48 : Nat.card ↥H = 48 := by
    rw [htop]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans gapsw2_t1_card_gl2_zmod3_eq_48
  omega

end FLT.Gapsw6W4SmallDegreeImageDescent

end

section

open Module NumberField

open scoped IntermediateField NumberField MatrixGroups

namespace FLT
namespace Gapsw7X2DihedralLevelOneExclusion

open FLT.Gapsw2T1Gl2F3Lattice FLT.Gapsw6W4SmallDegreeImageDescent

local instance gapsw7_x2_isAlgebraicQbar :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

theorem gapsw7_x2_card_dvd_sixteen_of_cartan_conj (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hconj :
      (∃ g : GL (Fin 2) (ZMod 3), ∀ h ∈ H,
        g⁻¹ * h * g ∈ gapsw2T1CartanNonsplitNormalizerGL3) ∨
      (∃ g : GL (Fin 2) (ZMod 3), ∀ h ∈ H,
        g⁻¹ * h * g ∈ gapsw2T1CartanSplitNormalizerGL3)) :
    Nat.card ↥H ∣ 16 := by
  rcases hconj with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hd := gapsw6_w4_card_dvd_of_conj_le H gapsw2T1CartanNonsplitNormalizerGL3 g hg
    rwa [gapsw2_t1_card_cartanNonsplitNormalizerGL3] at hd
  · have hd := gapsw6_w4_card_dvd_of_conj_le H gapsw2T1CartanSplitNormalizerGL3 g hg
    rw [gapsw6_w4_card_cartanSplitNormalizerGL3] at hd
    exact hd.trans ⟨2, rfl⟩

end FLT.Gapsw7X2DihedralLevelOneExclusion

end

open FLT.Gapsw6W4SmallDegreeImageDescent FLT.Gapsw7X2DihedralLevelOneExclusion in
theorem solution
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hirr : ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v)
    (hdet : ∀ d : (ZMod 3)ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = d)
    (hle : Nat.card H ≤ 24) :
    Nat.card H ∣ 16 :=
  gapsw7_x2_card_dvd_sixteen_of_cartan_conj H (gapsw6_w4_census_cartan_containment H hirr hdet hle)

end S_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three (solution)
