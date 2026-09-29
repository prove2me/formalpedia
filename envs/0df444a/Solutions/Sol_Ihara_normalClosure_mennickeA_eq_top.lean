-- Prove2me | solution 1 for Ihara.normalClosure_mennickeA_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/009c7a62-4f20-5459-ae21-6944794c313a

import Definitions.Def_Gamma0Away
import Definitions.Def_IharaAmalgamMap
import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_normalClosure_mennickeA_eq_top

namespace SolH10

open Ihara

section InlSLAwayCarrier

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

end InlSLAwayCarrier

section InlSLAwayElemGen

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

end InlSLAwayElemGen

section InlR1bSlice

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

variable (q : ℕ) [NeZero q]

omit [NeZero q] in

theorem lowerUnip_mem_normalClosure (x : ZAway q) :
    lowerUnip q x ∈
      Subgroup.normalClosure ({slToAway q mennickeA} : Set SL(2, ZAway q)) := by
  obtain ⟨a, k, heq⟩ := lowerUnip_eq_conj_slToAway_mennickeA_zpow q x
  rw [heq]
  exact Subgroup.normalClosure_normal.conj_mem _
    (zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) a) (mennickeU q ^ k)

omit [NeZero q] in

theorem upperUnip_mem_normalClosure (y : ZAway q) :
    upperUnip q y ∈
      Subgroup.normalClosure ({slToAway q mennickeA} : Set SL(2, ZAway q)) := by
  rw [upperUnip_eq_conj_lowerUnip]
  exact Subgroup.normalClosure_normal.conj_mem _
    (lowerUnip_mem_normalClosure q (-y)) (slToAway q mennickeB)

omit [NeZero q] in

theorem elementarySubgroup_le_normalClosure :
    elementarySubgroup q ≤
      Subgroup.normalClosure ({slToAway q mennickeA} : Set SL(2, ZAway q)) := by
  have h : Set.range (lowerUnip q) ∪ Set.range (upperUnip q) ⊆
      ↑(Subgroup.normalClosure ({slToAway q mennickeA} : Set SL(2, ZAway q))) := by
    rintro g (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact lowerUnip_mem_normalClosure q x
    · exact upperUnip_mem_normalClosure q y
  exact (Subgroup.closure_le _).mpr h

theorem normalClosure_mennickeA_eq_top :
    Subgroup.normalClosure ({slToAway q mennickeA} : Set SL(2, ZAway q)) = ⊤ :=
  le_antisymm le_top
    (le_trans (le_of_eq (elementarySubgroup_eq_top q).symm)
      (elementarySubgroup_le_normalClosure q))

end

end InlR1bSlice

end SolH10
p2m_reactivate "P2MW.S_Ihara_normalClosure_mennickeA_eq_top.SolH10"

open scoped MatrixGroups in

theorem solution (q : ℕ) [NeZero q] :
    Subgroup.normalClosure
      ({Ihara.slToAway q Ihara.mennickeA} : Set SL(2, Ihara.ZAway q)) = ⊤ :=
  SolH10.normalClosure_mennickeA_eq_top q

end S_Ihara_normalClosure_mennickeA_eq_top
end P2MW
export P2MW.S_Ihara_normalClosure_mennickeA_eq_top (solution)
