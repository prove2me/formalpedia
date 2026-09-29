-- Prove2me | solution 1 for Ihara.principalCongruenceAway_le_commutator_sup_mennickeQ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c7f4f124-bce5-5eae-9572-08883ec2cda3

import Definitions.Def_IharaMennickeCarrier
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ

set_option Elab.async false

section Inl_A3_SLAwayCarrier_d2

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ ZAway slToAway coe_slToAway zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix
open scoped MatrixGroups

noncomputable section

variable (q : ℕ)

def lowerUnip (x : ZAway q) : SL(2, ZAway q) :=
  ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
theorem lowerUnip_coe (x : ZAway q) :
    ((lowerUnip q x : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; x, 1] := rfl

def upperUnip (y : ZAway q) : SL(2, ZAway q) :=
  ⟨!![1, y; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
theorem upperUnip_coe (y : ZAway q) :
    ((upperUnip q y : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, y; 0, 1] := rfl

theorem lowerUnip_zero : lowerUnip q 0 = 1 := by
  apply Subtype.ext
  rw [lowerUnip_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem upperUnip_zero : upperUnip q 0 = 1 := by
  apply Subtype.ext
  rw [upperUnip_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem lowerUnip_mul (x y : ZAway q) :
    lowerUnip q x * lowerUnip q y = lowerUnip q (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerUnip_coe, lowerUnip_coe, lowerUnip_coe,
    Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem upperUnip_mul (y z : ZAway q) :
    upperUnip q y * upperUnip q z = upperUnip q (y + z) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, upperUnip_coe, upperUnip_coe, upperUnip_coe,
    Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem lowerUnip_inv (x : ZAway q) : (lowerUnip q x)⁻¹ = lowerUnip q (-x) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowerUnip_mul, add_neg_cancel, lowerUnip_zero]

theorem upperUnip_inv (y : ZAway q) : (upperUnip q y)⁻¹ = upperUnip q (-y) := by
  apply inv_eq_of_mul_eq_one_right
  rw [upperUnip_mul, add_neg_cancel, upperUnip_zero]

def elementarySubgroup : Subgroup SL(2, ZAway q) :=
  Subgroup.closure (Set.range (lowerUnip q) ∪ Set.range (upperUnip q))

theorem lowerUnip_mem_elementarySubgroup (x : ZAway q) :
    lowerUnip q x ∈ elementarySubgroup q :=
  Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)

theorem upperUnip_mem_elementarySubgroup (y : ZAway q) :
    upperUnip q y ∈ elementarySubgroup q :=
  Subgroup.subset_closure (Or.inr ⟨y, rfl⟩)

def mennickeB : SL(2, ℤ) :=
  ⟨!![0, 1; -1, 0], by norm_num [Matrix.det_fin_two_of]⟩

@[scoped simp]
theorem mennickeB_coe :
    ((mennickeB : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := rfl

theorem mennickeB_inv_eq :
    (mennickeB)⁻¹ =
      (⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩ : SL(2, ℤ)) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; 1, 0] = _
  rw [Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem slToAway_mennickeB_coe :
    ((slToAway q mennickeB : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![0, 1; -1, 0] := by
  rw [coe_slToAway, mennickeB_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem slToAway_mennickeB_inv_coe :
    (((slToAway q mennickeB)⁻¹ : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![0, -1; 1, 0] := by
  rw [← map_inv, mennickeB_inv_eq, coe_slToAway]
  show ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ (ZAway q))) = _
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem mennickeB_conj_lowerUnip (x : ZAway q) :
    slToAway q mennickeB * lowerUnip q x * (slToAway q mennickeB)⁻¹ =
      upperUnip q (-x) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    slToAway_mennickeB_coe, slToAway_mennickeB_inv_coe, lowerUnip_coe, upperUnip_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem upperUnip_eq_conj_lowerUnip (y : ZAway q) :
    upperUnip q y =
      slToAway q mennickeB * lowerUnip q (-y) * (slToAway q mennickeB)⁻¹ := by
  rw [mennickeB_conj_lowerUnip, neg_neg]

theorem mennickeB_sq : mennickeB ^ 2 = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, mennickeB_coe, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mennickeB_pow_four : mennickeB ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, mennickeB_sq, neg_one_sq]

theorem slToAway_mennickeB_pow_four : (slToAway q mennickeB) ^ 4 = 1 := by
  rw [← map_pow, mennickeB_pow_four, map_one]

theorem slToAway_mennickeB_eq_unipotent_word :
    slToAway q mennickeB =
      lowerUnip q (-1) * upperUnip q 1 * lowerUnip q (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, slToAway_mennickeB_coe, lowerUnip_coe,
    upperUnip_coe, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mennickeU_inv_coe :
    (((mennickeU q)⁻¹ : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![qInv q, 0; 0, ((q : ℕ) : ZAway q)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl (mennickeU q)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mennickeU]

theorem natCast_q_pow_mul_qInv_pow (k : ℕ) :
    ((q : ℕ) : ZAway q) ^ k * qInv q ^ k = 1 := by
  rw [← mul_pow, natCast_q_mul_qInv, one_pow]

theorem qInv_pow_mul_natCast_q_pow (k : ℕ) :
    qInv q ^ k * ((q : ℕ) : ZAway q) ^ k = 1 := by
  rw [← mul_pow, qInv_mul_natCast_q, one_pow]

theorem qInv_pow_mul_mul_qInv_pow (k : ℕ) (x : ZAway q) :
    qInv q ^ k * x * qInv q ^ k = x * qInv q ^ (2 * k) := by
  rw [two_mul, pow_add]; ring

theorem natCast_q_pow_mul_mul_natCast_q_pow (k : ℕ) (x : ZAway q) :
    ((q : ℕ) : ZAway q) ^ k * x * ((q : ℕ) : ZAway q) ^ k =
      x * ((q : ℕ) : ZAway q) ^ (2 * k) := by
  rw [two_mul, pow_add]; ring

theorem mennickeU_pow_coe (k : ℕ) :
    ((mennickeU q ^ k : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![((q : ℕ) : ZAway q) ^ k, 0; 0, qInv q ^ k] := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeU_coe,
      Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ]

theorem mennickeU_pow_inv_coe (k : ℕ) :
    (((mennickeU q ^ k)⁻¹ : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![qInv q ^ k, 0; 0, ((q : ℕ) : ZAway q) ^ k] := by
  rw [← inv_pow]
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeU_inv_coe,
      Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ]

theorem mennickeU_pow_conj_lowerUnip (k : ℕ) (x : ZAway q) :
    mennickeU q ^ k * lowerUnip q x * (mennickeU q ^ k)⁻¹ =
      lowerUnip q (x * qInv q ^ (2 * k)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, mennickeU_pow_coe, mennickeU_pow_inv_coe,
    lowerUnip_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [natCast_q_pow_mul_qInv_pow q, qInv_pow_mul_natCast_q_pow q,
      qInv_pow_mul_mul_qInv_pow q]

theorem mennickeU_pow_inv_conj_lowerUnip (k : ℕ) (x : ZAway q) :
    (mennickeU q ^ k)⁻¹ * lowerUnip q x * mennickeU q ^ k =
      lowerUnip q (x * ((q : ℕ) : ZAway q) ^ (2 * k)) := by
  have h := mennickeU_pow_conj_lowerUnip q k (x * ((q : ℕ) : ZAway q) ^ (2 * k))
  rw [mul_assoc x, natCast_q_pow_mul_qInv_pow q (2 * k), mul_one] at h
  rw [← h]
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]

theorem mennickeU_inv_conj_lowerUnip (x : ZAway q) :
    (mennickeU q)⁻¹ * lowerUnip q x * mennickeU q =
      lowerUnip q (((q : ℕ) : ZAway q) ^ 2 * x) := by
  have h := mennickeU_pow_inv_conj_lowerUnip q 1 x
  rw [pow_one, mul_one, mul_comm x] at h
  exact h

theorem algebraMap_natCast_q_mul_qInv :
    algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) * qInv q = 1 := by
  have h : algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) = ((q : ℕ) : ZAway q) := by
    push_cast; ring
  rw [h, natCast_q_mul_qInv]

theorem exists_eq_algebraMap_mul_invSelf_pow_even (x : ZAway q) :
    ∃ (a : ℤ) (k : ℕ), x = algebraMap ℤ (ZAway q) a * qInv q ^ (2 * k) := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := ZAway q) ((q : ℕ) : ℤ) x
  replace ha : x * algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) ^ n = algebraMap ℤ (ZAway q) a :=
    ha
  have hx : x = algebraMap ℤ (ZAway q) a * qInv q ^ n := by
    have h1 : x * (algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) ^ n * qInv q ^ n) =
        algebraMap ℤ (ZAway q) a * qInv q ^ n := by rw [← mul_assoc, ha]
    rwa [← mul_pow, algebraMap_natCast_q_mul_qInv, one_pow, mul_one] at h1
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · exact ⟨a, k, by rw [hx, hk]⟩
  · refine ⟨a * ((q : ℕ) : ℤ), k + 1, ?_⟩
    rw [hx, hk, map_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    calc algebraMap ℤ (ZAway q) a * qInv q ^ (2 * k + 1)
        = algebraMap ℤ (ZAway q) a * (algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) * qInv q) *
            qInv q ^ (2 * k + 1) := by rw [algebraMap_natCast_q_mul_qInv, mul_one]
      _ = algebraMap ℤ (ZAway q) a * algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) *
            (qInv q ^ (2 * k + 1) * qInv q) := by ring

theorem exists_eq_algebraMap_mul_invSelf_pow (x : ZAway q) :
    ∃ (a : ℤ) (k : ℕ), x = algebraMap ℤ (ZAway q) a * qInv q ^ k := by
  obtain ⟨a, k, h⟩ := exists_eq_algebraMap_mul_invSelf_pow_even q x
  exact ⟨a, 2 * k, h⟩

theorem slToAway_mennickeA_eq_lowerUnip_one :
    slToAway q mennickeA = lowerUnip q 1 := by
  apply Subtype.ext
  rw [coe_slToAway, mennickeA_coe, lowerUnip_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem slToAway_mennickeA_pow_eq_lowerUnip (k : ℕ) :
    (slToAway q mennickeA) ^ k = lowerUnip q ((k : ℕ) : ZAway q) := by
  apply Subtype.ext
  rw [← map_pow, coe_slToAway, mennickeA_pow_coe, lowerUnip_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem slToAway_mennickeA_zpow_eq_lowerUnip (a : ℤ) :
    (slToAway q mennickeA) ^ a = lowerUnip q (algebraMap ℤ (ZAway q) a) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [zpow_natCast, slToAway_mennickeA_pow_eq_lowerUnip]
    congr 1; push_cast; ring
  · rw [_root_.zpow_neg, zpow_natCast, slToAway_mennickeA_pow_eq_lowerUnip, lowerUnip_inv]
    congr 1; push_cast; ring

theorem mennickeU_pow_conj_slToAway_mennickeA_zpow (k : ℕ) (a : ℤ) :
    mennickeU q ^ k * (slToAway q mennickeA) ^ a * (mennickeU q ^ k)⁻¹ =
      lowerUnip q (algebraMap ℤ (ZAway q) a * qInv q ^ (2 * k)) := by
  rw [slToAway_mennickeA_zpow_eq_lowerUnip q a, mennickeU_pow_conj_lowerUnip q k]

theorem lowerUnip_eq_conj_slToAway_mennickeA_zpow (x : ZAway q) :
    ∃ (a : ℤ) (k : ℕ),
      lowerUnip q x =
        mennickeU q ^ k * (slToAway q mennickeA) ^ a * (mennickeU q ^ k)⁻¹ := by
  obtain ⟨a, k, hx⟩ := exists_eq_algebraMap_mul_invSelf_pow_even q x
  exact ⟨a, k, by rw [mennickeU_pow_conj_slToAway_mennickeA_zpow q k a, ← hx]⟩

end

end Ihara
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Inl_A3_SLAwayCarrier_d2
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Inl_A3_SLAwayElemGen

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ ZAway slToAway coe_slToAway zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix
open scoped MatrixGroups

noncomputable section

theorem exists_int_quotient_remainder (c d : ℤ) (hc : c ≠ 0) :
    ∃ s r : ℤ, d = s * c + r ∧ r.natAbs < c.natAbs := by
  have habs : (0 : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast Int.natAbs_pos.mpr hc
  have hdiv := Int.emod_add_ediv_mul d (c.natAbs : ℤ)
  have hr0 : 0 ≤ d % (c.natAbs : ℤ) := Int.emod_nonneg d (by omega)
  have hrlt : d % (c.natAbs : ℤ) < (c.natAbs : ℤ) := Int.emod_lt_of_pos d habs
  rcases Int.natAbs_eq c with hpos | hneg
  · exact ⟨d / (c.natAbs : ℤ), d % (c.natAbs : ℤ),
      by linear_combination -hdiv - (d / (c.natAbs : ℤ)) * hpos, by omega⟩
  · exact ⟨-(d / (c.natAbs : ℤ)), d % (c.natAbs : ℤ),
      by linear_combination -hdiv + (d / (c.natAbs : ℤ)) * hneg, by omega⟩

variable (q : ℕ)

def numeratorAbsSet (x : ZAway q) : Set ℕ :=
  {n : ℕ | ∃ (a : ℤ) (k : ℕ), x = algebraMap ℤ (ZAway q) a * qInv q ^ k ∧ a.natAbs = n}

theorem numeratorAbsSet_nonempty (x : ZAway q) : (numeratorAbsSet q x).Nonempty := by
  obtain ⟨a, k, h⟩ := exists_eq_algebraMap_mul_invSelf_pow q x
  exact ⟨a.natAbs, a, k, h, rfl⟩

def numeratorNorm (x : ZAway q) : ℕ := sInf (numeratorAbsSet q x)

theorem exists_numeratorNorm_rep (x : ZAway q) :
    ∃ (a : ℤ) (k : ℕ),
      x = algebraMap ℤ (ZAway q) a * qInv q ^ k ∧ a.natAbs = numeratorNorm q x :=
  Nat.sInf_mem (numeratorAbsSet_nonempty q x)

theorem numeratorNorm_le (x : ZAway q) (a : ℤ) (k : ℕ)
    (h : x = algebraMap ℤ (ZAway q) a * qInv q ^ k) :
    numeratorNorm q x ≤ a.natAbs :=
  Nat.sInf_le ⟨a, k, h, rfl⟩

@[scoped simp]
theorem numeratorNorm_zero : numeratorNorm q 0 = 0 :=
  Nat.le_zero.mp (Nat.sInf_le ⟨0, 0, by rw [map_zero, zero_mul], rfl⟩)

theorem numeratorNorm_eq_zero_iff [NeZero q] (x : ZAway q) :
    numeratorNorm q x = 0 ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨a, k, hrep, habs⟩ := exists_numeratorNorm_rep q x
    rw [h] at habs
    rw [hrep, Int.natAbs_eq_zero.mp habs, map_zero, zero_mul]
  · rintro rfl; exact numeratorNorm_zero q

theorem numeratorNorm_pos [NeZero q] {x : ZAway q} (hx : x ≠ 0) :
    0 < numeratorNorm q x := by
  rcases Nat.eq_zero_or_pos (numeratorNorm q x) with h | h
  · exact absurd ((numeratorNorm_eq_zero_iff q x).mp h) hx
  · exact h

theorem numeratorNorm_neg (x : ZAway q) : numeratorNorm q (-x) = numeratorNorm q x := by
  apply le_antisymm
  · obtain ⟨a, k, hrep, habs⟩ := exists_numeratorNorm_rep q x
    calc numeratorNorm q (-x) ≤ (-a).natAbs :=
          numeratorNorm_le q (-x) (-a) k (by rw [map_neg]; linear_combination -hrep)
      _ = a.natAbs := Int.natAbs_neg a
      _ = numeratorNorm q x := habs
  · obtain ⟨a, k, hrep, habs⟩ := exists_numeratorNorm_rep q (-x)
    calc numeratorNorm q x ≤ (-a).natAbs :=
          numeratorNorm_le q x (-a) k (by rw [map_neg]; linear_combination -hrep)
      _ = a.natAbs := Int.natAbs_neg a
      _ = numeratorNorm q (-x) := habs

theorem exists_numeratorNorm_remainder_lt [NeZero q] (c d : ZAway q) (hc : c ≠ 0) :
    ∃ t : ZAway q, numeratorNorm q (d - t * c) < numeratorNorm q c := by
  obtain ⟨c₀, k, hcrep, hcabs⟩ := exists_numeratorNorm_rep q c
  obtain ⟨d₀, m, hdrep⟩ := exists_eq_algebraMap_mul_invSelf_pow q d
  have hc₀ : c₀ ≠ 0 := fun h => hc (by rw [hcrep, h, map_zero, zero_mul])
  obtain ⟨s, r, hsr, hrlt⟩ := exists_int_quotient_remainder c₀ d₀ hc₀
  refine ⟨algebraMap ℤ (ZAway q) (s * ((q : ℕ) : ℤ) ^ k) * qInv q ^ m, ?_⟩
  have hqk : algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) ^ k * qInv q ^ k = 1 := by
    rw [← mul_pow, algebraMap_natCast_q_mul_qInv, one_pow]
  have hmapped : algebraMap ℤ (ZAway q) d₀ =
      algebraMap ℤ (ZAway q) s * algebraMap ℤ (ZAway q) c₀ + algebraMap ℤ (ZAway q) r := by
    rw [← map_mul, ← map_add]; exact congrArg _ hsr
  have hkey : d - (algebraMap ℤ (ZAway q) (s * ((q : ℕ) : ℤ) ^ k) * qInv q ^ m) * c =
      algebraMap ℤ (ZAway q) r * qInv q ^ m := by
    rw [hdrep, hcrep, map_mul, map_pow]
    linear_combination (qInv q ^ m) * hmapped -
      (algebraMap ℤ (ZAway q) s * algebraMap ℤ (ZAway q) c₀ * qInv q ^ m) * hqk
  rw [hkey]
  calc numeratorNorm q (algebraMap ℤ (ZAway q) r * qInv q ^ m) ≤ r.natAbs :=
        numeratorNorm_le q _ r m rfl
    _ < c₀.natAbs := hrlt
    _ = numeratorNorm q c := hcabs

theorem exists_numeratorNorm_add_lt [NeZero q] (c d : ZAway q) (hc : c ≠ 0) :
    ∃ t : ZAway q, numeratorNorm q (d + t * c) < numeratorNorm q c := by
  obtain ⟨t, ht⟩ := exists_numeratorNorm_remainder_lt q c d hc
  exact ⟨-t, by rw [show d + -t * c = d - t * c from by ring]; exact ht⟩

def mennickeDiag (a d : ZAway q) (h : a * d = 1) : SL(2, ZAway q) :=
  ⟨!![a, 0; 0, d], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

@[scoped simp]
theorem mennickeDiag_coe (a d : ZAway q) (h : a * d = 1) :
    ((mennickeDiag q a d h : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![a, 0; 0, d] := rfl

theorem mennickeDiag_eq_unipotent_word (a d : ZAway q) (h : a * d = 1) :
    mennickeDiag q a d h =
      upperUnip q a * lowerUnip q (-d) * upperUnip q a *
        (upperUnip q (-1) * lowerUnip q 1 * upperUnip q (-1)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, upperUnip_coe, lowerUnip_coe,
    mennickeDiag_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
      | ring1
      | linear_combination h
      | linear_combination -h
      | linear_combination a * h
      | linear_combination -(a * h)
      | linear_combination a * a * h
      | linear_combination -(a * a * h)
      | linear_combination d * h
      | linear_combination -(d * h)
      | exact Or.inl (by linear_combination h)
      | exact Or.inl (by linear_combination -h)

theorem mennickeDiag_mem_elementarySubgroup (a d : ZAway q) (h : a * d = 1) :
    mennickeDiag q a d h ∈ elementarySubgroup q := by
  rw [mennickeDiag_eq_unipotent_word q a d h]
  exact mul_mem
    (mul_mem (mul_mem (upperUnip_mem_elementarySubgroup q a)
      (lowerUnip_mem_elementarySubgroup q (-d)))
      (upperUnip_mem_elementarySubgroup q a))
    (mul_mem (mul_mem (upperUnip_mem_elementarySubgroup q (-1))
      (lowerUnip_mem_elementarySubgroup q 1))
      (upperUnip_mem_elementarySubgroup q (-1)))

theorem mennickeU_eq_mennickeDiag :
    mennickeU q = mennickeDiag q ((q : ℕ) : ZAway q) (qInv q) (natCast_q_mul_qInv q) :=
  Subtype.ext rfl

theorem mennickeU_mem_elementarySubgroup : mennickeU q ∈ elementarySubgroup q := by
  rw [mennickeU_eq_mennickeDiag q]
  exact mennickeDiag_mem_elementarySubgroup q _ _ _

theorem slToAway_mennickeB_mem_elementarySubgroup :
    slToAway q mennickeB ∈ elementarySubgroup q := by
  rw [slToAway_mennickeB_eq_unipotent_word q]
  exact mul_mem (mul_mem (lowerUnip_mem_elementarySubgroup q (-1))
    (upperUnip_mem_elementarySubgroup q 1))
    (lowerUnip_mem_elementarySubgroup q (-1))

theorem literal_mul_apply_one_zero {R : Type*} [CommRing R]
    (p₀ p₁ r₀ r₁ : R) (M : Matrix (Fin 2) (Fin 2) R) :
    (!![p₀, p₁; r₀, r₁] * M) 1 0 = r₀ * M 0 0 + r₁ * M 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp

theorem diag_mul_eq_one_of_bottomLeft_eq_zero (g : SL(2, ZAway q))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 *
      (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  exact hdet

theorem eq_diag_mul_upper_of_bottomLeft_eq_zero (g : SL(2, ZAway q))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = 0) :
    g = mennickeDiag q ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0)
          ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1)
          (diag_mul_eq_one_of_bottomLeft_eq_zero q g hc) *
        upperUnip q ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 *
          (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) := by
  have had := diag_mul_eq_one_of_bottomLeft_eq_zero q g hc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, mennickeDiag_coe, upperUnip_coe,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp; linear_combination (-((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1)) * had
  · simp [hc]
  · simp

theorem mem_elementarySubgroup_of_c_eq_zero (g : SL(2, ZAway q))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = 0) :
    g ∈ elementarySubgroup q := by
  rw [eq_diag_mul_upper_of_bottomLeft_eq_zero q g hc]
  exact mul_mem (mennickeDiag_mem_elementarySubgroup q _ _ _)
    (upperUnip_mem_elementarySubgroup q _)

theorem descent_bottomLeft (t : ZAway q) (g : SL(2, ZAway q)) :
    ((slToAway q mennickeB * upperUnip q t * g : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 =
      -((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
        t * (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    slToAway_mennickeB_coe, upperUnip_coe, Matrix.mul_fin_two,
    literal_mul_apply_one_zero]
  ring

theorem mem_elementarySubgroup_of_numeratorNorm_lt [NeZero q] :
    ∀ (n : ℕ) (g : SL(2, ZAway q)),
      numeratorNorm q ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0) < n →
      g ∈ elementarySubgroup q := by
  intro n
  induction n with
  | zero => exact fun g hg => absurd hg (Nat.not_lt_zero _)
  | succ n ih =>
    intro g hg
    by_cases hc : (g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = 0
    · exact mem_elementarySubgroup_of_c_eq_zero q g hc
    · obtain ⟨t, ht⟩ := exists_numeratorNorm_add_lt q
        ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0)
        ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0) hc
      have hstep : slToAway q mennickeB * upperUnip q t * g ∈
          elementarySubgroup q := by
        apply ih
        rw [descent_bottomLeft q t g, numeratorNorm_neg]
        exact lt_of_lt_of_le ht (Nat.lt_succ_iff.mp hg)
      have hrec : (upperUnip q t)⁻¹ * ((slToAway q mennickeB)⁻¹ *
          (slToAway q mennickeB * upperUnip q t * g)) = g := by
        rw [mul_assoc (slToAway q mennickeB), inv_mul_cancel_left, inv_mul_cancel_left]
      rw [← hrec]
      exact mul_mem (inv_mem (upperUnip_mem_elementarySubgroup q t))
        (mul_mem (inv_mem (slToAway_mennickeB_mem_elementarySubgroup q)) hstep)

theorem elementarySubgroup_eq_top [NeZero q] : elementarySubgroup q = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  exact mem_elementarySubgroup_of_numeratorNorm_lt q
    (numeratorNorm q ((g : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0) + 1) g
    (Nat.lt_succ_self _)

end
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Inl_A3_SLAwayElemGen
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Inl_P1_pruned_Thm_SL2_ZMod_perfect

open Matrix

open scoped MatrixGroups
open scoped commutatorElement

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ ZAway slToAway coe_slToAway zAwayToZMod_algebraMap"
p2m_open "Ihara"

section Helpers
variable {G : Type*} [Group G]

theorem normal_of_generator_conj {S : Set G} {K : Subgroup G}
    (htop : Subgroup.closure S = ⊤)
    (hconj : ∀ g ∈ S, (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K)) :
    K.Normal := by
  have key : ∀ g : G, (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K) := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [htop]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hconj x hx
    | one => refine ⟨fun n hn => ?_, fun n hn => ?_⟩ <;> simpa using hn
    | mul x y hx hy ihx ihy =>
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · have h2 := ihx.1 _ (ihy.1 n hn)
        have heq : x * (y * n * y⁻¹) * x⁻¹ = x * y * n * (x * y)⁻¹ := by group
        rwa [heq] at h2
      · have h2 := ihy.2 _ (ihx.2 n hn)
        have heq : y⁻¹ * (x⁻¹ * n * x) * y = (x * y)⁻¹ * n * (x * y) := by group
        rwa [heq] at h2
    | inv x hx ihx =>
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · simpa using ihx.2 n hn
      · simpa using ihx.1 n hn
  exact ⟨fun n hn g => (key g).1 n hn⟩

theorem commutator_le_of_pair_gen {x y : G} {K : Subgroup G}
    (hN : K.Normal) (htop : Subgroup.closure ({x, y} : Set G) = ⊤) (hxy : ⁅x, y⁆ ∈ K) :
    commutator G ≤ K := by
  haveI := hN
  set π : G →* G ⧸ K := QuotientGroup.mk' K
  have hc : Commute (π x) (π y) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hxy
  have hgen : Subgroup.closure ({π x, π y} : Set (G ⧸ K)) = ⊤ := by
    have himg : ({π x, π y} : Set (G ⧸ K)) = π '' {x, y} := (Set.image_pair π x y).symm
    rw [himg, ← MonoidHom.map_closure, htop]
    exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective K)
  have hall : ∀ a b : G ⧸ K, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.centralizer ({π x, π y} : Set (G ⧸ K)) := by
      have h1 : Subgroup.closure ({π x, π y} : Set (G ⧸ K)) ≤
          Subgroup.centralizer ({π x, π y} : Set (G ⧸ K)) := by
        rw [Subgroup.closure_le]
        intro u hu
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · rfl
        · exact hc.symm.eq
        · exact hc.eq
        · rfl
      exact h1 (by rw [hgen]; exact Subgroup.mem_top a)
    have hb : b ∈ Subgroup.centralizer ({a} : Set (G ⧸ K)) := by
      have h2 : Subgroup.closure ({π x, π y} : Set (G ⧸ K)) ≤
          Subgroup.centralizer ({a} : Set (G ⧸ K)) := by
        rw [Subgroup.closure_le]
        intro v hv
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw; subst hw
        exact (Subgroup.mem_centralizer_iff.mp ha v hv).symm
      exact h2 (by rw [hgen]; exact Subgroup.mem_top b)
    exact Subgroup.mem_centralizer_iff.mp hb a (Set.mem_singleton a)
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro g ⟨a, b, rfl⟩
  have hone : π ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (hall (π a) (π b))
  rw [SetLike.mem_coe, ← QuotientGroup.ker_mk' K, MonoidHom.mem_ker]
  exact hone

end Helpers
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Unipotents
variable (m : ℕ)

def upperE (x : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, x; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def lowerE (x : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

variable {m}

@[scoped simp]
theorem upperE_coe (x : ZMod m) :
    ((upperE m x : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, x; 0, 1] := rfl

@[scoped simp]
theorem lowerE_coe (x : ZMod m) :
    ((lowerE m x : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, 0; x, 1] := rfl

theorem upperE_mul (x y : ZMod m) : upperE m x * upperE m y = upperE m (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, upperE_coe, upperE_coe, upperE_coe, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp; ring

theorem lowerE_mul (x y : ZMod m) : lowerE m x * lowerE m y = lowerE m (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerE_coe, lowerE_coe, lowerE_coe, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

@[scoped simp]
theorem upperE_zero : upperE m 0 = 1 := by
  apply Subtype.ext; rw [upperE_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

@[scoped simp]
theorem lowerE_zero : lowerE m 0 = 1 := by
  apply Subtype.ext; rw [lowerE_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem lowerE_natCast (k : ℕ) : lowerE m (k : ZMod m) = lowerE m 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← ih, lowerE_mul, Nat.cast_succ]

theorem upperE_natCast (k : ℕ) : upperE m (k : ZMod m) = upperE m 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← ih, upperE_mul, Nat.cast_succ]

theorem lowerE_eq_pow [NeZero m] (x : ZMod m) : lowerE m x = lowerE m 1 ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact lowerE_natCast x.val

theorem upperE_eq_pow [NeZero m] (x : ZMod m) : upperE m x = upperE m 1 ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact upperE_natCast x.val

variable (m) in

def rotB : SL(2, ZMod m) := upperE m 1 * lowerE m (-1) * upperE m 1

theorem rotB_coe :
    ((rotB m : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![0, 1; -1, 0] := by
  rw [rotB, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, upperE_coe,
    lowerE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rotB_mul_upperE (x : ZMod m) : rotB m * upperE m x = lowerE m (-x) * rotB m := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, rotB_coe,
    upperE_coe, lowerE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rotB_pow_four : rotB m ^ 4 = 1 := by
  have hsq : ((rotB m * rotB m : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) =
      !![-1, 0; 0, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, rotB_coe, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h4 : rotB m ^ 4 = (rotB m * rotB m) * (rotB m * rotB m) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  apply Subtype.ext
  rw [h4, Matrix.SpecialLinearGroup.coe_mul, hsq, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end Unipotents
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Generation
variable {m : ℕ}

theorem eq_unipotent_word_of_bottomLeft_inv (X : SL(2, ZMod m)) (v : ZMod m)
    (hv : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 * v = 1) :
    X = upperE m (((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) * v) *
          lowerE m ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) *
          upperE m (((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * v) := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 *
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 *
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
    have h := X.2; rwa [Matrix.det_fin_two] at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    upperE_coe, lowerE_coe, upperE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  symm; ext i j; fin_cases i <;> fin_cases j
  · simp; linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) * hv
  · simp
    linear_combination v * hdet +
      ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 +
        ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) *
        ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * v) * hv
  · simp
  · simp; linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * hv

theorem mem_closure_unipotents_of_isUnit_bottomLeft (X : SL(2, ZMod m))
    (h : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0)) :
    X ∈ Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) := by
  obtain ⟨u, hu⟩ := h
  have hv : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 * (↑u⁻¹ : ZMod m) = 1 := by
    rw [← hu]; exact u.mul_inv
  rw [eq_unipotent_word_of_bottomLeft_inv X (↑u⁻¹ : ZMod m) hv]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)

theorem isUnit_of_castHom_ne_zero {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (x : ZMod (p ^ k))
    (h : ZMod.castHom (dvd_pow_self p hk) (ZMod p) x ≠ 0) : IsUnit x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd; apply h
  have hx : x = ((x.val : ℕ) : ZMod (p ^ k)) := (ZMod.natCast_zmod_val x).symm
  rw [hx, map_natCast, ZMod.natCast_eq_zero_iff]; exact hdvd

theorem isUnit_or_isUnit_of_det (hm : IsPrimePow m) {a b c d : ZMod m}
    (h : a * d - b * c = 1) : IsUnit a ∨ IsUnit c := by
  obtain ⟨p, k, hpp, hkpos, rfl⟩ := hm
  have hp : p.Prime := Nat.prime_iff.mpr hpp
  have hk : k ≠ 0 := hkpos.ne'
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  by_contra hcon; rw [not_or] at hcon
  have ha : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a = 0 := by
    by_contra h0; exact hcon.1 (isUnit_of_castHom_ne_zero hp hk a h0)
  have hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra h0; exact hcon.2 (isUnit_of_castHom_ne_zero hp hk c h0)
  have h1 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) (a * d - b * c) = 1 := by
    rw [h, map_one]
  rw [map_sub, map_mul, map_mul, ha, hc, zero_mul, mul_zero, sub_zero] at h1
  exact one_ne_zero h1.symm

theorem isUnit_add_of_isUnit_of_not_isUnit (hm : IsPrimePow m) {a c : ZMod m}
    (ha : IsUnit a) (hc : ¬IsUnit c) : IsUnit (a + c) := by
  obtain ⟨p, k, hpp, hkpos, rfl⟩ := hm
  have hp : p.Prime := Nat.prime_iff.mpr hpp
  have hk : k ≠ 0 := hkpos.ne'
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hc0 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra h0; exact hc (isUnit_of_castHom_ne_zero hp hk c h0)
  have ha0 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a ≠ 0 := by
    intro h0
    have hmap := ha.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p))
    rw [h0] at hmap; exact not_isUnit_zero hmap
  apply isUnit_of_castHom_ne_zero hp hk
  rw [map_add, hc0, add_zero]; exact ha0

theorem closure_unipotents_eq_top (hm : IsPrimePow m) :
    Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) = ⊤ := by
  rw [eq_top_iff]; intro X _
  by_cases hc : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0)
  · exact mem_closure_unipotents_of_isUnit_bottomLeft X hc
  · have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 *
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 *
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
      have h := X.2; rwa [Matrix.det_fin_two] at h
    have ha : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0) :=
      (isUnit_or_isUnit_of_det hm hdet).resolve_right hc
    have hentry : ((lowerE m 1 * X : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 =
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, lowerE_coe, Matrix.mul_apply, Fin.sum_univ_two]
      simp
    have hsum : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) :=
      isUnit_add_of_isUnit_of_not_isUnit hm ha hc
    have h2 : lowerE m 1 * X ∈
        Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) := by
      apply mem_closure_unipotents_of_isUnit_bottomLeft
      rw [hentry]; exact hsum
    have h3 : X = lowerE m (-1) * (lowerE m 1 * X) := by
      rw [← mul_assoc, lowerE_mul, neg_add_cancel, lowerE_zero, one_mul]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)) h2

theorem closure_pair_eq_top (hm : IsPrimePow m) :
    Subgroup.closure ({upperE m 1, lowerE m 1} : Set (SL(2, ZMod m))) = ⊤ := by
  haveI : NeZero m := ⟨by have := hm.two_le; omega⟩
  rw [eq_top_iff, ← closure_unipotents_eq_top hm, Subgroup.closure_le]
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · rw [SetLike.mem_coe, upperE_eq_pow t]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  · rw [SetLike.mem_coe, lowerE_eq_pow t]
    exact Subgroup.pow_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _

end Generation
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section AbelianizationBound

variable (m : ℕ) in

def alphaA : Abelianization (SL(2, ZMod m)) := Abelianization.of (lowerE m 1)

variable {m : ℕ}

theorem of_lowerE_natCast (k : ℕ) :
    Abelianization.of (lowerE m (k : ZMod m)) = alphaA m ^ k := by
  rw [lowerE_natCast, map_pow, alphaA]

theorem of_upperE (x : ZMod m) :
    Abelianization.of (upperE m x) = Abelianization.of (lowerE m (-x)) := by
  have h := congrArg Abelianization.of (rotB_mul_upperE (m := m) x)
  rw [map_mul, map_mul] at h
  rw [mul_comm (Abelianization.of (lowerE m (-x))) (Abelianization.of (rotB m))] at h
  exact mul_left_cancel h

theorem alphaA_pow_self : alphaA m ^ m = 1 := by
  rw [← of_lowerE_natCast, ZMod.natCast_self, lowerE_zero, map_one]

theorem of_lowerE_neg_one : Abelianization.of (lowerE m (-1)) = (alphaA m)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, alphaA, ← map_mul, lowerE_mul, neg_add_cancel, lowerE_zero, map_one]

theorem of_rotB : Abelianization.of (rotB m) = (alphaA m)⁻¹ ^ 3 := by
  have hupper : Abelianization.of (upperE m 1) = (alphaA m)⁻¹ := by
    rw [of_upperE, of_lowerE_neg_one]
  rw [rotB, map_mul, map_mul, hupper, of_lowerE_neg_one]; group

theorem alphaA_pow_twelve : alphaA m ^ 12 = 1 := by
  have h := congrArg Abelianization.of (rotB_pow_four (m := m))
  rw [map_pow, map_one, of_rotB, ← pow_mul] at h
  rw [show (3 * 4 : ℕ) = 12 from rfl] at h
  rwa [inv_pow, inv_eq_one] at h

theorem orderOf_alphaA_dvd_self : orderOf (alphaA m) ∣ m :=
  orderOf_dvd_of_pow_eq_one alphaA_pow_self

theorem orderOf_alphaA_dvd_twelve : orderOf (alphaA m) ∣ 12 :=
  orderOf_dvd_of_pow_eq_one alphaA_pow_twelve

end AbelianizationBound
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section RowOne
variable {m : ℕ}

end RowOne
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Inl_P1_pruned_Thm_SL2_ZMod_perfect
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Inl_A3_TableLowerBound

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ ZAway slToAway coe_slToAway zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix
open scoped MatrixGroups
open scoped commutatorElement

section Certificates

structure MennickeCommutatorCertificate (m : ℕ) where

  K : List (SL(2, ZMod m))

  hone : (1 : SL(2, ZMod m)) ∈ K

  hmul : ∀ x ∈ K, ∀ y ∈ K, x * y ∈ K

  hinv : ∀ x ∈ K, ∃ y ∈ K, x * y = 1

  hconjU : ∀ x ∈ K, ∃ y ∈ K, upperE m 1 * x = y * upperE m 1

  hconjU' : ∀ x ∈ K, ∃ y ∈ K, x * upperE m 1 = upperE m 1 * y

  hconjL : ∀ x ∈ K, ∃ y ∈ K, lowerE m 1 * x = y * lowerE m 1

  hconjL' : ∀ x ∈ K, ∃ y ∈ K, x * lowerE m 1 = lowerE m 1 * y

  hcomm : ∃ k ∈ K, upperE m 1 * lowerE m 1 = k * (lowerE m 1 * upperE m 1)

namespace MennickeCommutatorCertificate

variable {m : ℕ} (c : MennickeCommutatorCertificate m)

def subgroup : Subgroup (SL(2, ZMod m)) where
  carrier := {x | x ∈ c.K}
  one_mem' := c.hone
  mul_mem' := fun ha hb => c.hmul _ ha _ hb
  inv_mem' := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := c.hinv x hx
    have h : x⁻¹ = y := inv_eq_of_mul_eq_one_right hxy
    rw [Set.mem_setOf_eq, h]
    exact hy

theorem mem_subgroup_iff {x : SL(2, ZMod m)} : x ∈ c.subgroup ↔ x ∈ c.K := Iff.rfl

theorem subgroup_normal (hm : IsPrimePow m) : (c.subgroup).Normal := by
  apply normal_of_generator_conj (closure_pair_eq_top hm)
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · constructor
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjU n hn
      have h : upperE m 1 * n * (upperE m 1)⁻¹ = y := by
        rw [hxy, mul_inv_cancel_right]
      rw [mem_subgroup_iff, h]
      exact hy
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjU' n hn
      have h : (upperE m 1)⁻¹ * n * upperE m 1 = y := by
        rw [mul_assoc, hxy, inv_mul_cancel_left]
      rw [mem_subgroup_iff, h]
      exact hy
  · constructor
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjL n hn
      have h : lowerE m 1 * n * (lowerE m 1)⁻¹ = y := by
        rw [hxy, mul_inv_cancel_right]
      rw [mem_subgroup_iff, h]
      exact hy
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjL' n hn
      have h : (lowerE m 1)⁻¹ * n * lowerE m 1 = y := by
        rw [mul_assoc, hxy, inv_mul_cancel_left]
      rw [mem_subgroup_iff, h]
      exact hy

theorem commutator_le (hm : IsPrimePow m) :
    commutator (SL(2, ZMod m)) ≤ c.subgroup := by
  apply commutator_le_of_pair_gen (c.subgroup_normal hm) (closure_pair_eq_top hm)
  obtain ⟨k, hk, hkeq⟩ := c.hcomm
  have h : ⁅upperE m 1, lowerE m 1⁆ = k := by
    rw [commutatorElement_def]
    rw [show upperE m 1 * lowerE m 1 * (upperE m 1)⁻¹ * (lowerE m 1)⁻¹ =
      (upperE m 1 * lowerE m 1) * (lowerE m 1 * upperE m 1)⁻¹ by group]
    rw [hkeq, mul_assoc, mul_inv_cancel, mul_one]
  rw [mem_subgroup_iff, h]
  exact hk

theorem not_mem_commutator (hm : IsPrimePow m) {x : SL(2, ZMod m)} (hx : x ∉ c.K) :
    x ∉ commutator (SL(2, ZMod m)) :=
  fun h => hx (c.commutator_le hm h)

theorem of_ne_one (hm : IsPrimePow m) {x : SL(2, ZMod m)} (hx : x ∉ c.K) :
    Abelianization.of x ≠ 1 := by
  intro h
  apply c.not_mem_commutator hm hx
  have hker : x ∈ MonoidHom.ker (Abelianization.of (G := SL(2, ZMod m))) :=
    MonoidHom.mem_ker.mpr h
  rwa [Abelianization.ker_of] at hker

end MennickeCommutatorCertificate
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

theorem isPrimePow_two : IsPrimePow 2 := ⟨2, 1, Nat.prime_two.prime, one_pos, by norm_num⟩

theorem isPrimePow_three : IsPrimePow 3 := ⟨3, 1, Nat.prime_three.prime, one_pos, by norm_num⟩

theorem isPrimePow_four : IsPrimePow 4 := ⟨2, 2, Nat.prime_two.prime, two_pos, by norm_num⟩

def cert2 : MennickeCommutatorCertificate 2 where
  K := [⟨!![1, 0; 0, 1], by decide⟩,
        ⟨!![0, 1; 1, 1], by decide⟩,
        ⟨!![1, 1; 1, 0], by decide⟩]
  hone := by decide
  hmul := by decide
  hinv := by decide
  hconjU := by decide
  hconjU' := by decide
  hconjL := by decide
  hconjL' := by decide
  hcomm := by decide

def cert3 : MennickeCommutatorCertificate 3 where
  K := [⟨!![1, 0; 0, 1], by decide⟩,
        ⟨!![2, 0; 0, 2], by decide⟩,
        ⟨!![0, 1; 2, 0], by decide⟩,
        ⟨!![0, 2; 1, 0], by decide⟩,
        ⟨!![1, 1; 1, 2], by decide⟩,
        ⟨!![1, 2; 2, 2], by decide⟩,
        ⟨!![2, 1; 1, 1], by decide⟩,
        ⟨!![2, 2; 2, 1], by decide⟩]
  hone := by decide
  hmul := by decide
  hinv := by decide
  hconjU := by decide
  hconjU' := by decide
  hconjL := by decide
  hconjL' := by decide
  hcomm := by decide

set_option maxRecDepth 4096 in

def cert4 : MennickeCommutatorCertificate 4 where
  K := [⟨!![1, 0; 0, 1], by decide⟩,
        ⟨!![0, 1; 3, 3], by decide⟩,
        ⟨!![0, 3; 1, 3], by decide⟩,
        ⟨!![1, 1; 1, 2], by decide⟩,
        ⟨!![1, 2; 2, 1], by decide⟩,
        ⟨!![1, 3; 3, 2], by decide⟩,
        ⟨!![2, 1; 1, 1], by decide⟩,
        ⟨!![2, 3; 3, 1], by decide⟩,
        ⟨!![3, 0; 2, 3], by decide⟩,
        ⟨!![3, 1; 3, 0], by decide⟩,
        ⟨!![3, 2; 0, 3], by decide⟩,
        ⟨!![3, 3; 1, 0], by decide⟩]
  hone := by decide
  hmul := by decide
  hinv := by decide
  hconjU := by decide
  hconjU' := by decide
  hconjL := by decide
  hconjL' := by decide
  hcomm := by decide

theorem orderOf_alphaA_two : orderOf (alphaA 2) = 2 := by
  have hne : alphaA 2 ≠ 1 := cert2.of_ne_one isPrimePow_two (by decide)
  have hdvd : orderOf (alphaA 2) ∣ 2 := orderOf_alphaA_dvd_self
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem orderOf_alphaA_three : orderOf (alphaA 3) = 3 := by
  have hne : alphaA 3 ≠ 1 := cert3.of_ne_one isPrimePow_three (by decide)
  have hdvd : orderOf (alphaA 3) ∣ 3 := orderOf_alphaA_dvd_self
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem orderOf_alphaA_four : orderOf (alphaA 4) = 4 := by
  have hsq : alphaA 4 ^ 2 ≠ 1 := by
    have h2 : alphaA 4 ^ 2 = Abelianization.of (lowerE 4 2) := by
      rw [alphaA, ← map_pow]
      congr 1
      rw [pow_two, lowerE_mul]
      norm_num
    rw [h2]
    exact cert4.of_ne_one isPrimePow_four (by decide)
  have hdvd : orderOf (alphaA 4) ∣ 2 ^ 2 := by
    rw [show (2 ^ 2 : ℕ) = 4 from rfl]
    exact orderOf_alphaA_dvd_self
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases j
  · rw [pow_zero] at hord
    exact absurd (by rw [orderOf_eq_one_iff.mp hord, one_pow]) hsq
  · rw [pow_one] at hord
    have h2 : alphaA 4 ^ 2 = 1 := by
      have hpow := pow_orderOf_eq_one (alphaA 4)
      rwa [hord] at hpow
    exact absurd h2 hsq
  · rw [hord]
    norm_num

end Certificates
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Transfer

variable {m m' : ℕ}

def redSL (h : m' ∣ m) : SL(2, ZMod m) →* SL(2, ZMod m') :=
  SpecialLinearGroup.map (ZMod.castHom h (ZMod m'))

theorem redSL_lowerE (h : m' ∣ m) (x : ZMod m) :
    redSL h (lowerE m x) = lowerE m' (ZMod.castHom h (ZMod m') x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-ZMod.castHom_apply, redSL, lowerE, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply]

theorem orderOf_alphaA_dvd_of_dvd (h : m' ∣ m) :
    orderOf (alphaA m') ∣ orderOf (alphaA m) := by
  set ψ : SL(2, ZMod m) →* Abelianization (SL(2, ZMod m')) :=
    (Abelianization.of).comp (redSL h) with hψdef
  have hψ : ψ (lowerE m 1) = alphaA m' := by
    show Abelianization.of (redSL h (lowerE m 1)) = alphaA m'
    rw [redSL_lowerE, map_one]
    rfl
  have hfact : ψ (lowerE m 1) = Abelianization.lift ψ (alphaA m) := by
    rw [alphaA, Abelianization.lift_apply_of]
  rw [← hψ, hfact]
  exact orderOf_map_dvd (Abelianization.lift ψ) (alphaA m)

theorem gcd_twelve_dvd_orderOf_alphaA (m : ℕ) :
    Nat.gcd m 12 ∣ orderOf (alphaA m) := by
  have h2 : 2 ∣ m → 2 ∣ orderOf (alphaA m) := fun h => by
    have hh := orderOf_alphaA_dvd_of_dvd h
    rwa [orderOf_alphaA_two] at hh
  have h3 : 3 ∣ m → 3 ∣ orderOf (alphaA m) := fun h => by
    have hh := orderOf_alphaA_dvd_of_dvd h
    rwa [orderOf_alphaA_three] at hh
  have h4 : 4 ∣ m → 4 ∣ orderOf (alphaA m) := fun h => by
    have hh := orderOf_alphaA_dvd_of_dvd h
    rwa [orderOf_alphaA_four] at hh
  have hgm : Nat.gcd m 12 ∣ m := Nat.gcd_dvd_left m 12
  have hg12 : Nat.gcd m 12 ∣ 12 := Nat.gcd_dvd_right m 12
  revert hgm hg12
  generalize Nat.gcd m 12 = g
  intro hgm hg12
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · simp at hg12
    · exact h
  have hle : g ≤ 12 := Nat.le_of_dvd (by norm_num) hg12
  interval_cases g
  · exact one_dvd _
  · exact h2 hgm
  · exact h3 hgm
  · exact h4 hgm
  · exact absurd hg12 (by norm_num)
  · have hm2 : 2 ∣ m := dvd_trans (by norm_num) hgm
    have hm3 : 3 ∣ m := dvd_trans (by norm_num) hgm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (h2 hm2) (h3 hm3)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · have hm4 : 4 ∣ m := dvd_trans (by norm_num) hgm
    have hm3 : 3 ∣ m := dvd_trans (by norm_num) hgm
    have h12 : (12 : ℕ) = 4 * 3 := by norm_num
    rw [h12]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (h4 hm4) (h3 hm3)

end Transfer
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Inl_A3_TableLowerBound
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Inl_A3_MennickeHabel
set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ ZAway slToAway coe_slToAway zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix
open scoped MatrixGroups
open scoped commutatorElement

section ReductionSeam

variable (m q : ℕ)

theorem slAwayReduction_slToAway (hmq : Nat.Coprime m q) (A : SL(2, ℤ)) :
    slAwayReduction m q hmq (slToAway q A) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) A := by
  refine Subtype.ext ?_
  rw [slAwayReduction_coe, coe_slToAway, Matrix.map_map]
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Function.comp_apply, Int.coe_castRingHom]
  exact zAwayToZMod_algebraMap m q hmq ((A : Matrix (Fin 2) (Fin 2) ℤ) i j)

theorem slAwayReduction_slToAway_mennickeA (hmq : Nat.Coprime m q) :
    slAwayReduction m q hmq (slToAway q mennickeA) = lowerE m 1 := by
  rw [slAwayReduction_slToAway m q hmq mennickeA]
  apply Subtype.ext
  have h1 : ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) mennickeA :
      SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ((mennickeA : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom (ZMod m)) := rfl
  rw [h1, mennickeA_coe, lowerE_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

end ReductionSeam
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section AbelianQuotient

variable (q : ℕ)
variable (D : Subgroup SL(2, ZAway q)) [D.Normal]

theorem mennickeAbelianized_mul_comm
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) (a b : SL(2, ZAway q)) :
    QuotientGroup.mk' D a * QuotientGroup.mk' D b =
      QuotientGroup.mk' D b * QuotientGroup.mk' D a := by
  have h1 : ⁅a, b⁆ ∈ D :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have h2 : QuotientGroup.mk' D ⁅a, b⁆ = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact h1
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem mennickeAbelianized_conj
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) (c g : SL(2, ZAway q)) :
    QuotientGroup.mk' D (c * g * c⁻¹) = QuotientGroup.mk' D g := by
  rw [map_mul, map_mul, map_inv, mennickeAbelianized_mul_comm q D hcomm c g,
    mul_inv_cancel_right]

theorem mennickeAbelianized_lowerUnip_mem_zpowers
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) (x : ZAway q) :
    QuotientGroup.mk' D (lowerUnip q x) ∈
      Subgroup.zpowers (QuotientGroup.mk' D (slToAway q mennickeA)) := by
  obtain ⟨a, k, heq⟩ := lowerUnip_eq_conj_slToAway_mennickeA_zpow q x
  rw [heq, mennickeAbelianized_conj q D hcomm (mennickeU q ^ k)
    ((slToAway q mennickeA) ^ a), map_zpow]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) a

theorem mennickeAbelianized_upperUnip_mem_zpowers
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) (y : ZAway q) :
    QuotientGroup.mk' D (upperUnip q y) ∈
      Subgroup.zpowers (QuotientGroup.mk' D (slToAway q mennickeA)) := by
  rw [upperUnip_eq_conj_lowerUnip q y,
    mennickeAbelianized_conj q D hcomm (slToAway q mennickeB) (lowerUnip q (-y))]
  exact mennickeAbelianized_lowerUnip_mem_zpowers q D hcomm (-y)

theorem mennickeAbelianized_mem_zpowers [NeZero q]
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) (g : SL(2, ZAway q)) :
    QuotientGroup.mk' D g ∈
      Subgroup.zpowers (QuotientGroup.mk' D (slToAway q mennickeA)) := by
  have hg : g ∈ elementarySubgroup q := by
    rw [elementarySubgroup_eq_top q]
    exact Subgroup.mem_top g
  have hle : elementarySubgroup q ≤
      Subgroup.comap (QuotientGroup.mk' D)
        (Subgroup.zpowers (QuotientGroup.mk' D (slToAway q mennickeA))) := by
    rw [elementarySubgroup, Subgroup.closure_le]
    rintro z (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact Subgroup.mem_comap.mpr
        (mennickeAbelianized_lowerUnip_mem_zpowers q D hcomm x)
    · exact Subgroup.mem_comap.mpr
        (mennickeAbelianized_upperUnip_mem_zpowers q D hcomm y)
  exact Subgroup.mem_comap.mp (hle hg)

theorem mennickeAbelianized_mennickeB_eq
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) :
    QuotientGroup.mk' D (slToAway q mennickeB) =
      (QuotientGroup.mk' D (slToAway q mennickeA))⁻¹ ^ 3 := by
  have hlU : QuotientGroup.mk' D (lowerUnip q (-1)) =
      (QuotientGroup.mk' D (slToAway q mennickeA))⁻¹ := by
    have h1 : lowerUnip q (-1 : ZAway q) = (slToAway q mennickeA)⁻¹ := by
      have h2 := slToAway_mennickeA_zpow_eq_lowerUnip q (-1)
      rw [_root_.zpow_neg, zpow_one] at h2
      have h3 : algebraMap ℤ (ZAway q) (-1) = (-1 : ZAway q) := by
        rw [map_neg, map_one]
      rw [h3] at h2
      exact h2.symm
    rw [h1, map_inv]
  have huU : QuotientGroup.mk' D (upperUnip q 1) =
      QuotientGroup.mk' D (lowerUnip q (-1)) := by
    rw [upperUnip_eq_conj_lowerUnip q 1,
      mennickeAbelianized_conj q D hcomm (slToAway q mennickeB)
        (lowerUnip q (-(1 : ZAway q)))]
  rw [slToAway_mennickeB_eq_unipotent_word q, map_mul, map_mul, huU, hlU]
  group

theorem mennickeAbelianized_mennickeA_pow_twelve
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D) :
    (QuotientGroup.mk' D (slToAway q mennickeA)) ^ 12 = 1 := by
  have hB4 : (QuotientGroup.mk' D (slToAway q mennickeB)) ^ 4 = 1 := by
    rw [← map_pow, slToAway_mennickeB_pow_four q, map_one]
  rw [mennickeAbelianized_mennickeB_eq q D hcomm, ← pow_mul,
    show (3 * 4 : ℕ) = 12 by norm_num, inv_pow, inv_eq_one] at hB4
  exact hB4

end AbelianQuotient
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

section Habel

variable (m q : ℕ) [NeZero q]

theorem habel_engine (hmq : Nat.Coprime m q) (D : Subgroup SL(2, ZAway q))
    [D.Normal]
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D)
    (hAm : (slToAway q mennickeA) ^ m ∈ D)
    (hker : D ≤ ((Abelianization.of).comp (slAwayReduction m q hmq)).ker) :
    principalCongruenceAway m q hmq ≤ D := by
  intro X hX
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (mennickeAbelianized_mem_zpowers q D hcomm X)
  have hjG : ((slToAway q mennickeA) ^ j)⁻¹ * X ∈ D := by
    have h1 : QuotientGroup.mk' D ((slToAway q mennickeA) ^ j) =
        QuotientGroup.mk' D X := by
      rw [map_zpow]
      exact hj
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact h1
  have hρ : ((Abelianization.of).comp (slAwayReduction m q hmq))
      (((slToAway q mennickeA) ^ j)⁻¹ * X) = 1 :=
    MonoidHom.mem_ker.mp (hker hjG)
  rw [map_mul, map_inv, map_zpow] at hρ
  have hfX : ((Abelianization.of).comp (slAwayReduction m q hmq)) X = 1 := by
    rw [MonoidHom.comp_apply, (mem_principalCongruenceAway_iff m q hmq).mp hX, map_one]
  rw [hfX, mul_one, inv_eq_one] at hρ
  have hfA : ((Abelianization.of).comp (slAwayReduction m q hmq))
      (slToAway q mennickeA) = alphaA m := by
    rw [MonoidHom.comp_apply, slAwayReduction_slToAway_mennickeA m q hmq]
    rfl
  rw [hfA] at hρ
  have hdvd_am : (orderOf (alphaA m) : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr hρ
  have hA_m : (QuotientGroup.mk' D (slToAway q mennickeA)) ^ m = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hAm
  have hA_12 : (QuotientGroup.mk' D (slToAway q mennickeA)) ^ 12 = 1 :=
    mennickeAbelianized_mennickeA_pow_twelve q D hcomm
  have hordA : orderOf (QuotientGroup.mk' D (slToAway q mennickeA)) ∣ Nat.gcd m 12 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hA_m) (orderOf_dvd_of_pow_eq_one hA_12)
  have hchain : (orderOf (QuotientGroup.mk' D (slToAway q mennickeA)) : ℤ) ∣ j :=
    dvd_trans (Int.natCast_dvd_natCast.mpr
      (hordA.trans (gcd_twelve_dvd_orderOf_alphaA m))) hdvd_am
  have hAjD : (slToAway q mennickeA) ^ j ∈ D := by
    have h1 : (QuotientGroup.mk' D (slToAway q mennickeA)) ^ j = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp hchain
    rw [← map_zpow] at h1
    have h2 : (slToAway q mennickeA) ^ j ∈ (QuotientGroup.mk' D).ker :=
      MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h2
  have hX_eq : X = (slToAway q mennickeA) ^ j *
      (((slToAway q mennickeA) ^ j)⁻¹ * X) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hX_eq]
  exact D.mul_mem hAjD hjG

theorem principalCongruenceAway_le_commutator_sup_mennickeQ_impl (hmq : Nat.Coprime m q) :
    principalCongruenceAway m q hmq ≤
      _root_.commutator SL(2, ZAway q) ⊔ mennickeQ q m := by
  apply habel_engine m q hmq
  · exact le_sup_left
  · have h1 : mennickeQ q m ≤ _root_.commutator SL(2, ZAway q) ⊔ mennickeQ q m :=
      le_sup_right
    exact h1 (Subgroup.subset_normalClosure (Set.mem_singleton _))
  · apply sup_le
    · exact Abelianization.commutator_subset_ker _
    · intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        (mem_principalCongruenceAway_iff m q hmq).mp
          (normalClosure_le_principalCongruenceAway m q hmq hx), map_one]

theorem principalCongruenceAway_le_of_commutator_le_of_pow_mem (hmq : Nat.Coprime m q)
    (D : Subgroup SL(2, ZAway q)) [D.Normal]
    (hcomm : _root_.commutator SL(2, ZAway q) ≤ D)
    (hAm : (slToAway q mennickeA) ^ m ∈ D) :
    principalCongruenceAway m q hmq ≤ D := by
  refine le_trans (principalCongruenceAway_le_commutator_sup_mennickeQ_impl m q hmq) ?_
  exact sup_le hcomm
    (Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hAm))

end Habel
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

end Inl_A3_MennickeHabel
p2m_reactivate "P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.Ihara"

open scoped MatrixGroups in
theorem solution (m q : ℕ) [NeZero q] (hmq : Nat.Coprime m q) :
    Ihara.principalCongruenceAway m q hmq ≤ commutator SL(2, Ihara.ZAway q) ⊔ Ihara.mennickeQ q m :=
  Ihara.principalCongruenceAway_le_commutator_sup_mennickeQ_impl m q hmq

end S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ
end P2MW
export P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ (solution)
