-- Prove2me | solution 1 for Ihara.exists_replacement_lowerUnip
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/61b34dbc-f1f1-5ea3-a9cd-af3e14f45a67

import Definitions.Def_IharaMennickeCarrier
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Archimedean
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_exists_replacement_lowerUnip

set_option Elab.async false
set_option autoImplicit false

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe ZAway q_mul_invSelf invSelf_mul_q slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
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
  · rw [zpow_neg, zpow_natCast, slToAway_mennickeA_pow_eq_lowerUnip, lowerUnip_inv]
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
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe ZAway q_mul_invSelf invSelf_mul_q slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
p2m_open "Ihara"

open scoped MatrixGroups

section ScalarHelpers

variable (q : ℕ)

theorem natCast_q_pow_mul_invSelf_pow (k : ℕ) :
    ((q : ℕ) : ZAway q) ^ k * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k
      = 1 := by
  rw [← mul_pow, q_mul_invSelf, one_pow]

theorem invSelf_pow_mul_natCast_q_pow (k : ℕ) :
    IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k * ((q : ℕ) : ZAway q) ^ k
      = 1 := by
  rw [← mul_pow, invSelf_mul_q, one_pow]

theorem natCast_q_pow_mul_mul_invSelf_pow_eq_self (k : ℕ) (x : ZAway q) :
    ((q : ℕ) : ZAway q) ^ k * x
        * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k = x := by
  calc ((q : ℕ) : ZAway q) ^ k * x
          * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k
      = x * (((q : ℕ) : ZAway q) ^ k
          * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k) := by ring
    _ = x := by rw [natCast_q_pow_mul_invSelf_pow, mul_one]

theorem invSelf_pow_mul_mul_natCast_q_pow_eq_self (k : ℕ) (x : ZAway q) :
    IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k * x
        * ((q : ℕ) : ZAway q) ^ k = x := by
  calc IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k * x
          * ((q : ℕ) : ZAway q) ^ k
      = x * (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) ^ k
          * ((q : ℕ) : ZAway q) ^ k) := by ring
    _ = x := by rw [invSelf_pow_mul_natCast_q_pow, mul_one]

theorem coe_entries_det (X : SL(2, ZAway q)) :
    (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 -
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 *
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact X.2

end ScalarHelpers
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

section ArithHelpers

theorem isUnit_intCast_zmod_iff_coprime (A : ℤ) (n : ℕ) :
    IsUnit ((A : ℤ) : ZMod n) ↔ Nat.Coprime A.natAbs n := by
  rw [← ZMod.isUnit_iff_coprime]
  constructor
  · intro h
    rcases Int.natAbs_eq A with hA | hA
    · rwa [hA, Int.cast_natCast] at h
    · rw [hA, Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff] at h
      exact h
  · intro h
    rcases Int.natAbs_eq A with hA | hA
    · rw [hA, Int.cast_natCast]; exact h
    · rw [hA, Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff]; exact h

theorem exists_coprime_factorization (A₀ B₀ : ℤ) (hB₀ : B₀ ≠ 0) :
    ∃ (g : ℕ) (A B : ℤ), (g : ℤ) * A = A₀ ∧ (g : ℤ) * B = B₀ ∧ Int.gcd A B = 1 ∧
      B ≠ 0 := by
  have hgne : Int.gcd A₀ B₀ ≠ 0 := fun h => hB₀ (Int.gcd_eq_zero_iff.mp h).2
  refine ⟨Int.gcd A₀ B₀, A₀ / (Int.gcd A₀ B₀ : ℤ), B₀ / (Int.gcd A₀ B₀ : ℤ),
    Int.mul_ediv_cancel' (Int.gcd_dvd_left A₀ B₀),
    Int.mul_ediv_cancel' (Int.gcd_dvd_right A₀ B₀), ?_, ?_⟩
  · exact Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero hgne)
  · intro h
    apply hB₀
    rw [← Int.mul_ediv_cancel' (Int.gcd_dvd_right A₀ B₀), h, mul_zero]

end ArithHelpers
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe ZAway q_mul_invSelf invSelf_mul_q slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

noncomputable section

section QInvConj

variable (q : ℕ)

theorem qInv_mul_algebraMap_q :
    qInv q * algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ) = 1 := by
  rw [map_natCast]
  exact qInv_mul_natCast_q q

theorem natCast_q_pow_mul_mul_qInv_pow_eq_self (k : ℕ) (x : ZAway q) :
    ((q : ℕ) : ZAway q) ^ k * x * qInv q ^ k = x := by
  calc ((q : ℕ) : ZAway q) ^ k * x * qInv q ^ k
      = x * (((q : ℕ) : ZAway q) ^ k * qInv q ^ k) := by ring
    _ = x := by rw [natCast_q_pow_mul_qInv_pow, mul_one]

theorem qInv_pow_mul_mul_natCast_q_pow_eq_self (k : ℕ) (x : ZAway q) :
    qInv q ^ k * x * ((q : ℕ) : ZAway q) ^ k = x := by
  calc qInv q ^ k * x * ((q : ℕ) : ZAway q) ^ k
      = x * (qInv q ^ k * ((q : ℕ) : ZAway q) ^ k) := by ring
    _ = x := by rw [qInv_pow_mul_natCast_q_pow, mul_one]

end QInvConj
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

section KernelCharacterization

variable (q m : ℕ)

theorem zAwayToZMod_eq_zero_iff (hmq : Nat.Coprime m q) (x : ZAway q) :
    zAwayToZMod m q hmq x = 0 ↔ ∃ y : ZAway q, x = (m : ZAway q) * y := by
  constructor
  · intro hx
    obtain ⟨j, k, hjk⟩ := exists_eq_algebraMap_mul_invSelf_pow q x
    have hqu : IsUnit (zAwayToZMod m q hmq (qInv q)) := by
      refine ⟨Units.mkOfMulEqOne _ (zAwayToZMod m q hmq (algebraMap ℤ (ZAway q) ((q : ℕ) : ℤ))) ?_, rfl⟩
      rw [← map_mul, qInv_mul_algebraMap_q, map_one]
    have hj0 : ((j : ℤ) : ZMod m) = 0 := by
      have hx' : ((j : ℤ) : ZMod m) * zAwayToZMod m q hmq (qInv q) ^ k = 0 := by
        rw [← zAwayToZMod_algebraMap m q hmq j, ← map_pow, ← map_mul, ← hjk]
        exact hx
      exact ((hqu.pow k).mul_left_eq_zero).mp hx'
    obtain ⟨j', hj'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd j m).mp hj0
    refine ⟨algebraMap ℤ (ZAway q) j' * qInv q ^ k, ?_⟩
    rw [hjk, hj', map_mul, map_natCast]
    ring
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem mem_principalCongruenceAway_iff_entries (hmq : Nat.Coprime m q)
    (X : SL(2, ZAway q)) :
    X ∈ principalCongruenceAway m q hmq ↔
      (zAwayToZMod m q hmq ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0) = 1 ∧
       zAwayToZMod m q hmq ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) = 0 ∧
       zAwayToZMod m q hmq ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0) = 0 ∧
       zAwayToZMod m q hmq ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1) = 1) := by
  have hcoe : ((slAwayReduction m q hmq X : SL(2, ZMod m)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ((X : Matrix (Fin 2) (Fin 2) (ZAway q))).map (zAwayToZMod m q hmq) := rfl
  rw [mem_principalCongruenceAway_iff]
  constructor
  · intro h
    have h' : ((X : Matrix (Fin 2) (Fin 2) (ZAway q))).map (zAwayToZMod m q hmq) =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
      rw [← hcoe, h, Matrix.SpecialLinearGroup.coe_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h00 := congrFun (congrFun h' 0) 0
      simpa [Matrix.map_apply, Matrix.one_apply] using h00
    · have h01 := congrFun (congrFun h' 0) 1
      simpa [Matrix.map_apply, Matrix.one_apply] using h01
    · have h10 := congrFun (congrFun h' 1) 0
      simpa [Matrix.map_apply, Matrix.one_apply] using h10
    · have h11 := congrFun (congrFun h' 1) 1
      simpa [Matrix.map_apply, Matrix.one_apply] using h11
  · rintro ⟨h00, h01, h10, h11⟩
    apply Subtype.ext
    show ((X : Matrix (Fin 2) (Fin 2) (ZAway q))).map (zAwayToZMod m q hmq) =
      ((1 : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m))
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, h00, h01, h10, h11]

end KernelCharacterization
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

section RelativeUnipotents

variable (q m : ℕ)

theorem lowerUnip_natCast_mul_mem_normalClosure (w : ZAway q) :
    lowerUnip q ((m : ZAway q) * w) ∈
      Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) := by
  obtain ⟨j, k, hjk⟩ := exists_eq_algebraMap_mul_invSelf_pow_even q w
  have hmw : (m : ZAway q) * w = algebraMap ℤ (ZAway q) ((m : ℤ) * j) * qInv q ^ (2 * k) := by
    rw [hjk, map_mul, map_natCast]
    ring
  have hkey : lowerUnip q ((m : ZAway q) * w) =
      mennickeU q ^ k * (slToAway q mennickeA) ^ ((m : ℤ) * j) *
        (mennickeU q ^ k)⁻¹ := by
    rw [slToAway_mennickeA_zpow_eq_lowerUnip q ((m : ℤ) * j),
      mennickeU_pow_conj_lowerUnip q k, hmw]
  rw [hkey]
  refine Subgroup.normalClosure_normal.conj_mem _ ?_ (mennickeU q ^ k)
  rw [zpow_mul, zpow_natCast]
  exact zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) j

theorem upperUnip_natCast_mul_mem_normalClosure (w : ZAway q) :
    upperUnip q ((m : ZAway q) * w) ∈
      Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) := by
  rw [upperUnip_eq_conj_lowerUnip]
  refine Subgroup.normalClosure_normal.conj_mem _ ?_ (slToAway q mennickeB)
  have h : -((m : ZAway q) * w) = (m : ZAway q) * (-w) := by ring
  rw [h]
  exact lowerUnip_natCast_mul_mem_normalClosure q m (-w)

theorem lowerUnip_natCast_mul_mem_principalCongruenceAway (hmq : Nat.Coprime m q)
    (w : ZAway q) :
    lowerUnip q ((m : ZAway q) * w) ∈ principalCongruenceAway m q hmq := by
  rw [mem_principalCongruenceAway_iff_entries q m hmq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [lowerUnip_coe] <;> simp

theorem upperUnip_natCast_mul_mem_principalCongruenceAway (hmq : Nat.Coprime m q)
    (w : ZAway q) :
    upperUnip q ((m : ZAway q) * w) ∈ principalCongruenceAway m q hmq := by
  rw [mem_principalCongruenceAway_iff_entries q m hmq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [upperUnip_coe] <;> simp

end RelativeUnipotents
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

section EntryLemmas

variable (q : ℕ)

theorem mennickeU_pow_conj_coe (t : ℕ) (X : SL(2, ZAway q)) :
    ((mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹ : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * ((q : ℕ) : ZAway q) ^ (2 * t);
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 * qInv q ^ (2 * t),
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    mennickeU_pow_coe, mennickeU_pow_inv_coe, habcd, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [natCast_q_pow_mul_mul_qInv_pow_eq_self, qInv_pow_mul_mul_natCast_q_pow_eq_self,
      natCast_q_pow_mul_mul_natCast_q_pow, qInv_pow_mul_mul_qInv_pow]

theorem mul_upperUnip_coe (X : SL(2, ZAway q)) (y : ZAway q) :
    ((X * upperUnip q y : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * y +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1;
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 * y +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, upperUnip_coe, habcd, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mul_lowerUnip_coe (X : SL(2, ZAway q)) (w : ZAway q) :
    ((X * lowerUnip q w : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * w,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1;
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 * w,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerUnip_coe, habcd, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lowerUnip_mul_coe (w : ZAway q) (X : SL(2, ZAway q)) :
    ((lowerUnip q w * X : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1;
         w * (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0,
         w * (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerUnip_coe, habcd, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end EntryLemmas
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

section FirstRowLemma

variable (q m : ℕ)

theorem eq_lowerUnip_natCast_mul_of_firstRow_eq [NeZero q] (hmq : Nat.Coprime m q)
    (X X' : SL(2, ZAway q))
    (hX : X ∈ principalCongruenceAway m q hmq) (hX' : X' ∈ principalCongruenceAway m q hmq)
    (h00 : (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0)
    (h01 : (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) :
    ∃ z : ZAway q, X' = lowerUnip q ((m : ZAway q) * z) * X := by
  obtain ⟨-, -, hγ0, -⟩ := (mem_principalCongruenceAway_iff_entries q m hmq X).mp hX
  obtain ⟨-, -, hγ'0, -⟩ := (mem_principalCongruenceAway_iff_entries q m hmq X').mp hX'
  obtain ⟨c₀, hc₀⟩ := (zAwayToZMod_eq_zero_iff q m hmq _).mp hγ0
  obtain ⟨c₀', hc₀'⟩ := (zAwayToZMod_eq_zero_iff q m hmq _).mp hγ'0
  have hdX := coe_entries_det q X
  have hdX' := coe_entries_det q X'
  rw [hc₀] at hdX
  rw [hc₀', h00, h01] at hdX'
  refine ⟨c₀' * (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 -
    (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 * c₀, ?_⟩
  apply Subtype.ext
  rw [lowerUnip_mul_coe, Matrix.eta_fin_two
    ((X' : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)), h00, h01, hc₀, hc₀']
  ext i j
  fin_cases i <;> fin_cases j <;> simp

  · linear_combination (-(m : ZAway q) * c₀') * hdX + ((m : ZAway q) * c₀) * hdX'
  · linear_combination (-(X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1) * hdX +
      ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1) * hdX'

theorem mk_eq_mk_of_firstRow_eq [NeZero q] (hmq : Nat.Coprime m q) (X X' : SL(2, ZAway q))
    (hX : X ∈ principalCongruenceAway m q hmq) (hX' : X' ∈ principalCongruenceAway m q hmq)
    (h00 : (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0)
    (h01 : (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) :
    QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X := by
  obtain ⟨z, hz⟩ :=
    eq_lowerUnip_natCast_mul_of_firstRow_eq q m hmq X X' hX hX' h00 h01
  rw [hz, map_mul]
  have h1 : QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (lowerUnip q ((m : ZAway q) * z)) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact lowerUnip_natCast_mul_mem_normalClosure q m z
  rw [h1, one_mul]

end FirstRowLemma
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

section CommutingExponents

variable (q m : ℕ)

def commutingExponents
    (x : SL(2, ZAway q) ⧸ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) : AddSubgroup ℤ where
  carrier := {t : ℤ | Commute ((QuotientGroup.mk' (Subgroup.normalClosure
    ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) (mennickeU q)) ^ t) x}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zpow_zero]
    exact Commute.one_left x
  add_mem' := by
    intro s t hs ht
    simp only [Set.mem_setOf_eq] at hs ht ⊢
    rw [zpow_add]
    exact hs.mul_left ht
  neg_mem' := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [zpow_neg]
    exact ht.inv_left

theorem mem_commutingExponents_iff
    (x : SL(2, ZAway q) ⧸ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) (t : ℤ) :
    t ∈ commutingExponents q m x ↔
      Commute ((QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) (mennickeU q)) ^ t) x :=
  Iff.rfl

theorem natCast_mem_commutingExponents_iff (X : SL(2, ZAway q)) (t : ℕ) :
    ((t : ℤ) ∈ commutingExponents q m (QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X)) ↔
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
          (mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹) =
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X := by
  rw [mem_commutingExponents_iff, zpow_natCast, ← map_pow, map_mul, map_mul, map_inv,
    mul_inv_eq_iff_eq_mul]
  exact Iff.rfl

theorem exists_generator_commutingExponents
    (x : SL(2, ZAway q) ⧸ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) :
    ∃ N : ℕ, ∀ t : ℤ, t ∈ commutingExponents q m x ↔ (N : ℤ) ∣ t := by
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic (commutingExponents q m x)
  refine ⟨g.natAbs, fun t => ?_⟩
  rw [hg, AddSubgroup.mem_closure_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    rw [Int.natAbs_dvd, smul_eq_mul]
    exact dvd_mul_left g n
  · intro h
    rw [Int.natAbs_dvd] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [smul_eq_mul, hc]; ring⟩

theorem natCast_mem_commutingExponents_of_dvd [NeZero q] (hmq : Nat.Coprime m q)
    (X : SL(2, ZAway q)) (hX : X ∈ principalCongruenceAway m q hmq)
    (A : ℤ) (u v : ZAway q) (huv : u * v = 1)
    (hα : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 = algebraMap ℤ (ZAway q) A * u)
    (t : ℕ) (hdvd : A ∣ (q : ℤ) ^ (2 * t) - 1) :
    ((t : ℕ) : ℤ) ∈ commutingExponents q m (QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X) := by
  rw [natCast_mem_commutingExponents_iff]
  obtain ⟨s, hs⟩ := hdvd

  obtain ⟨hα1, hβ0, hγ0, hδ1⟩ := (mem_principalCongruenceAway_iff_entries q m hmq X).mp hX
  obtain ⟨b₀, hb₀⟩ := (zAwayToZMod_eq_zero_iff q m hmq _).mp hβ0

  have hYmem : mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹ ∈
      principalCongruenceAway m q hmq :=
    Subgroup.Normal.conj_mem inferInstance X hX (mennickeU q ^ t)
  have hYcoe := mennickeU_pow_conj_coe q t X

  have hym : -(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v =
      (m : ZAway q) * (-(b₀ * algebraMap ℤ (ZAway q) s * v)) := by
    rw [hb₀]; ring

  have hyQ : upperUnip q
      (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v) ∈
      Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) := by
    rw [hym]; exact upperUnip_natCast_mul_mem_normalClosure q m _
  have hyN : upperUnip q
      (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v) ∈
      principalCongruenceAway m q hmq := by
    rw [hym]; exact upperUnip_natCast_mul_mem_principalCongruenceAway q m hmq _

  have hZmem : (mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹) * upperUnip q
      (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v) ∈
      principalCongruenceAway m q hmq :=
    mul_mem hYmem hyN

  have hsZ : ((q : ℕ) : ZAway q) ^ (2 * t) - 1 = algebraMap ℤ (ZAway q) A * algebraMap ℤ (ZAway q) s := by
    rw [← map_mul, ← hs, map_sub, map_pow, map_one, map_natCast]

  have hZ00 : (((mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹) * upperUnip q
      (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v) :
      SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 := by
    rw [mul_upperUnip_coe, hYcoe]
    simp
  have hZ01 : (((mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹) * upperUnip q
      (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v) :
      SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 := by
    rw [mul_upperUnip_coe, hYcoe]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]

    rw [hα]
    linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) * hsZ -
      algebraMap ℤ (ZAway q) A * algebraMap ℤ (ZAway q) s * ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) * huv

  have hZX := mk_eq_mk_of_firstRow_eq q m hmq X _ hX hZmem hZ00 hZ01

  have hZY : QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
        ((mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹) * upperUnip q
          (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v)) =
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
          (mennickeU q ^ t * X * (mennickeU q ^ t)⁻¹) := by
    rw [map_mul]
    have h1 : QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
        (upperUnip q
          (-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) s * v)) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hyQ
    rw [h1, mul_one]
  exact hZY.symm.trans hZX

theorem exists_replacement_lowerUnip_impl [NeZero q] (hmq : Nat.Coprime m q) (X : SL(2, ZAway q))
    (hX : X ∈ principalCongruenceAway m q hmq)
    (A B : ℤ) (u u' v' : ZAway q) (hu'v' : u' * v' = 1)
    (hα : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 = algebraMap ℤ (ZAway q) A * u)
    (hβ : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 = algebraMap ℤ (ZAway q) B * u') (k : ℤ) :
    ∃ X' : SL(2, ZAway q), X' ∈ principalCongruenceAway m q hmq ∧
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
        algebraMap ℤ (ZAway q) (A + B * (m : ℤ) * k) * u ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 := by
  refine ⟨X * lowerUnip q ((m : ZAway q) * (algebraMap ℤ (ZAway q) k * u * v')), ?_, ?_, ?_, ?_⟩
  · exact mul_mem hX (lowerUnip_natCast_mul_mem_principalCongruenceAway q m hmq _)
  · rw [map_mul]
    have h1 : QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
        (lowerUnip q ((m : ZAway q) * (algebraMap ℤ (ZAway q) k * u * v'))) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact lowerUnip_natCast_mul_mem_normalClosure q m _
    rw [h1, mul_one]
  · rw [mul_lowerUnip_coe]
    simp only [Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    rw [hα, hβ, map_add, map_mul, map_mul, map_natCast]
    linear_combination (algebraMap ℤ (ZAway q) B * (m : ZAway q) * algebraMap ℤ (ZAway q) k * u) * hu'v'
  · rw [mul_lowerUnip_coe]
    simp

end CommutingExponents
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

end
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara"

open scoped MatrixGroups commutatorElement in
open _root_.Ihara _root_.P2MW.S_Ihara_exists_replacement_lowerUnip.Ihara in
theorem solution (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (X : SL(2, ZAway q))
    (hX : X ∈ principalCongruenceAway m q hmq)
    (A B : ℤ) (u u' v' : ZAway q) (hu'v' : u' * v' = 1)
    (hα : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 = algebraMap ℤ (ZAway q) A * u)
    (hβ : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 = algebraMap ℤ (ZAway q) B * u') (k : ℤ) :
    ∃ X' : SL(2, ZAway q), X' ∈ principalCongruenceAway m q hmq ∧
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
        algebraMap ℤ (ZAway q) (A + B * (m : ℤ) * k) * u ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 :=
  Ihara.exists_replacement_lowerUnip_impl q m hmq X hX A B u u' v' hu'v' hα hβ k

#print axioms solution

end S_Ihara_exists_replacement_lowerUnip
end P2MW
export P2MW.S_Ihara_exists_replacement_lowerUnip (solution)
