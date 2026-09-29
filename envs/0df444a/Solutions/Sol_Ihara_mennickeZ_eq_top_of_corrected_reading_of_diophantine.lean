-- Prove2me | solution 1 for Ihara.mennickeZ_eq_top_of_corrected_reading_of_diophantine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/10b3fbbe-6d5f-55df-89bc-53817985eaac

import Theorems.Thm_Ihara_mennickeLemma21
import Definitions.Def_IharaMennickeCarrier
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Totient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine

set_option Elab.async false
set_option autoImplicit false

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
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

theorem lowerUnip_mul (x y : ZAway q) :
    lowerUnip q x * lowerUnip q y = lowerUnip q (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerUnip_coe, lowerUnip_coe, lowerUnip_coe,
    Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem lowerUnip_inv (x : ZAway q) : (lowerUnip q x)⁻¹ = lowerUnip q (-x) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowerUnip_mul, add_neg_cancel, lowerUnip_zero]

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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
p2m_open "Ihara"

open scoped MatrixGroups

section ScalarHelpers

variable (q : ℕ)

theorem coe_entries_det (X : SL(2, ZAway q)) :
    (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 -
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 *
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact X.2

end ScalarHelpers
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

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
  rw [_root_.zpow_mul, zpow_natCast]
  exact zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) j

theorem upperUnip_natCast_mul_mem_normalClosure (w : ZAway q) :
    upperUnip q ((m : ZAway q) * w) ∈
      Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) := by
  rw [upperUnip_eq_conj_lowerUnip]
  refine Subgroup.normalClosure_normal.conj_mem _ ?_ (slToAway q mennickeB)
  have h : -((m : ZAway q) * w) = (m : ZAway q) * (-w) := by ring
  rw [h]
  exact lowerUnip_natCast_mul_mem_normalClosure q m (-w)

theorem upperUnip_natCast_mul_mem_principalCongruenceAway (hmq : Nat.Coprime m q)
    (w : ZAway q) :
    upperUnip q ((m : ZAway q) * w) ∈ principalCongruenceAway m q hmq := by
  rw [mem_principalCongruenceAway_iff_entries q m hmq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [upperUnip_coe] <;> simp

end RelativeUnipotents
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section EntryLemmas

variable (q : ℕ)

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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

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
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section CommutingExponents

variable (q m : ℕ)

end CommutingExponents
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

noncomputable section

section GateSlice

variable (q : ℕ)

end GateSlice
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section Lemma21AndEngines

variable (q m : ℕ) [NeZero q]

scoped instance mennickeZ_normal (hmq : Nat.Coprime m q) : (mennickeZ q m hmq).Normal := by
  haveI hmap : (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
      (principalCongruenceAway m q hmq)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rw [mennickeZ]
  exact Subgroup.Normal.comap inferInstance _

end Lemma21AndEngines
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

noncomputable section

variable (q m : ℕ) [NeZero q]

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

theorem eq_top_of_normal_of_mennickeA_mem (Z : Subgroup SL(2, ZAway q)) [Z.Normal]
    (hA : slToAway q mennickeA ∈ Z) : Z = ⊤ := by
  rw [← top_le_iff, ← normalClosure_mennickeA_eq_top q]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hA)

theorem normalClosure_mennickeA_pow_one_eq_top :
    Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ 1} : Set SL(2, ZAway q)) = ⊤ := by
  rw [pow_one]
  exact normalClosure_mennickeA_eq_top q

end
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

namespace Ihara
p2m_export "Ihara" "mennickeLemma21 mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction principalCongruenceAway mem_principalCongruenceAway_iff normalClosure_le_principalCongruenceAway qInv natCast_q_mul_qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff mennickeQ_le_mennickeZ MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

noncomputable section

section GenericDictionaries

variable {G : Type*} [Group G]

theorem commutator_mem_iff_commute_mk (N : Subgroup G) [N.Normal] (g x : G) :
    ⁅g, x⁆ ∈ N ↔
      Commute (QuotientGroup.mk' N g) (QuotientGroup.mk' N x) := by
  have key : ⁅g, x⁆ ∈ N ↔ QuotientGroup.mk' N ⁅g, x⁆ = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  rw [key, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact Iff.rfl

theorem mk_conj_eq_of_commutator_mem (N : Subgroup G) [N.Normal] {g x : G}
    (h : ⁅g, x⁆ ∈ N) :
    QuotientGroup.mk' N (g * x * g⁻¹) = QuotientGroup.mk' N x := by
  have h1 : QuotientGroup.mk' N ⁅g, x⁆ = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact h
  rw [commutatorElement_def, map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem commute_of_inv_mul_mul_eq {α ξ : G} (h : α⁻¹ * ξ * α = ξ) : Commute α ξ := by
  show α * ξ = ξ * α
  calc α * ξ = α * (α⁻¹ * ξ * α) := by rw [h]
    _ = ξ * α := by group

theorem commute_of_isCoprime_zpow {α ξ : G} {t : ℤ} {n : ℕ}
    (hcop : IsCoprime t (n : ℤ)) (ht : Commute (α ^ t) ξ)
    (hn : Commute (α ^ ((n : ℕ) : ℤ)) ξ) :
    Commute α ξ := by
  obtain ⟨c, d, hcd⟩ := hcop
  have hα : α = (α ^ t) ^ c * (α ^ ((n : ℕ) : ℤ)) ^ d := by
    rw [← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add,
      show t * c + ((n : ℕ) : ℤ) * d = c * t + d * ((n : ℕ) : ℤ) by ring, hcd, zpow_one]
  rw [hα]
  exact (ht.zpow_left c).mul_left (hn.zpow_left d)

end GenericDictionaries
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section EntryHelpers

variable (q : ℕ) [NeZero q]

omit [NeZero q] in

theorem mul_mennickeB_coe (X : SL(2, ZAway q)) :
    ((X * slToAway q mennickeB : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![-(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0;
         -(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, slToAway_mennickeB_coe, habcd,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring1

omit [NeZero q] in

theorem mul_mennickeB_inv_coe (X : SL(2, ZAway q)) :
    ((X * (slToAway q mennickeB)⁻¹ : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1,
         -(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0;
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1,
         -(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, slToAway_mennickeB_inv_coe, habcd,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring1

omit [NeZero q] in

theorem mennickeU_pow_inv_sandwich_coe (k : ℕ) (W : SL(2, ZAway q)) :
    (((mennickeU q ^ k)⁻¹ * W * (mennickeU q ^ k)⁻¹ : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(W : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * qInv q ^ (2 * k),
         (W : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1;
         (W : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0,
         (W : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 * ((q : ℕ) : ZAway q) ^ (2 * k)] := by
  obtain ⟨a, b, c, d, habcd⟩ : ∃ a b c d,
      (W : Matrix (Fin 2) (Fin 2) (ZAway q)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    mennickeU_pow_inv_coe, habcd, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [natCast_q_pow_mul_mul_qInv_pow_eq_self, qInv_pow_mul_mul_natCast_q_pow_eq_self,
      natCast_q_pow_mul_mul_natCast_q_pow, qInv_pow_mul_mul_qInv_pow]

end EntryHelpers
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section TwoFifteen

variable (q : ℕ) [NeZero q]

omit [NeZero q] in

theorem lowerUnip_inv_conj_coe (w : ZAway q) (X : SL(2, ZAway q)) :
    (((lowerUnip q w)⁻¹ * X * lowerUnip q w : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![(X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * w,
         (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1;
         -(w * ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * w)) +
           ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 +
            (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1 * w),
         -(w * (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1) +
           (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 1] := by
  rw [lowerUnip_inv, mul_assoc,
    lowerUnip_mul_coe q (-w) (X * lowerUnip q w), mul_lowerUnip_coe q X w]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring1

omit [NeZero q] in

theorem mennicke_two_fifteen (t : ℤ) (X : SL(2, ZAway q)) :
    ((((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t :
        SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) t ∧
    ((((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t :
        SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 := by
  rw [slToAway_mennickeA_zpow_eq_lowerUnip q t]
  constructor
  · rw [lowerUnip_inv_conj_coe]
    simp
  · rw [lowerUnip_inv_conj_coe]
    simp

end TwoFifteen
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section WordIdentity

variable (q : ℕ) [NeZero q]

omit [NeZero q] in
private theorem word_step2_coe (u : ℕ) :
    ((lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB :
        SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![0, 1; -1, ((q : ℕ) : ZAway q) ^ (2 * u)] := by
  rw [mul_mennickeB_coe, lowerUnip_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in
private theorem word_step3_coe (u : ℕ) :
    ((lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (qInv q ^ (2 * u)) : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![qInv q ^ (2 * u), 1; 0, ((q : ℕ) : ZAway q) ^ (2 * u)] := by
  rw [mul_lowerUnip_coe, word_step2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination natCast_q_pow_mul_qInv_pow q (2 * u)

omit [NeZero q] in
private theorem word_step4_coe (u : ℕ) :
    ((lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (qInv q ^ (2 * u)) * slToAway q mennickeB :
        SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![-1, qInv q ^ (2 * u); -(((q : ℕ) : ZAway q) ^ (2 * u)), 0] := by
  rw [mul_mennickeB_coe, word_step3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in
private theorem word_step5_coe (u : ℕ) :
    ((lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (qInv q ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![0, qInv q ^ (2 * u); -(((q : ℕ) : ZAway q) ^ (2 * u)), 0] := by
  rw [mul_lowerUnip_coe, word_step4_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination qInv_pow_mul_natCast_q_pow q (2 * u)

omit [NeZero q] in
private theorem word_step6_coe (u : ℕ) :
    ((lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (qInv q ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) *
        (slToAway q mennickeB)⁻¹ : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![qInv q ^ (2 * u), 0; 0, ((q : ℕ) : ZAway q) ^ (2 * u)] := by
  rw [mul_mennickeB_inv_coe, word_step5_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in

theorem mennicke_word_eq_mennickeU_pow_inv (u : ℕ) :
    lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (qInv q ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) *
        (slToAway q mennickeB)⁻¹ =
      (mennickeU q ^ (2 * u))⁻¹ := by
  apply Subtype.ext
  rw [word_step6_coe, mennickeU_pow_inv_coe]

omit [NeZero q] in

theorem mennicke_relation_word_eq_one :
    slToAway q mennickeA * slToAway q mennickeB * slToAway q mennickeA *
        slToAway q mennickeB * slToAway q mennickeA *
        (slToAway q mennickeB)⁻¹ = 1 := by
  have h := mennicke_word_eq_mennickeU_pow_inv q 0
  simp only [Nat.mul_zero, pow_zero, ← slToAway_mennickeA_eq_lowerUnip_one, inv_one] at h
  exact h

end WordIdentity
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section TwoTwentyFour

variable (q m : ℕ) [NeZero q]

omit [NeZero q] in

theorem mk_lowerUnip_eq_mk_mennickeA {x c : ZAway q}
    (hx : x = (m : ZAway q) * c + 1) :
    QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (lowerUnip q x) =
    QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (slToAway q mennickeA) := by
  rw [hx, ← lowerUnip_mul q ((m : ZAway q) * c) 1, ← slToAway_mennickeA_eq_lowerUnip_one, map_mul]
  have h1 : QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (lowerUnip q ((m : ZAway q) * c)) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact lowerUnip_natCast_mul_mem_normalClosure q m c
  rw [h1, one_mul]

theorem mennickeU_pow_mem_normalClosure_of_dvd (u : ℕ) (hdvd : m ∣ q ^ (2 * u) - 1) :
    mennickeU q ^ (2 * u) ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) := by

  obtain ⟨c, hc⟩ := hdvd
  have hq1 : 1 ≤ q ^ (2 * u) :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqc : q ^ (2 * u) = m * c + 1 := by omega
  have hcast : ((q : ℕ) : ZAway q) ^ (2 * u) = (m : ZAway q) * (c : ZAway q) + 1 := by
    rw [← Nat.cast_pow, hqc]
    push_cast
    ring
  have hcast' : qInv q ^ (2 * u) =
      (m : ZAway q) * (-((c : ZAway q) * qInv q ^ (2 * u))) + 1 := by
    linear_combination (-(qInv q ^ (2 * u))) * hcast +
      natCast_q_pow_mul_qInv_pow q (2 * u)

  have hword := mennicke_word_eq_mennickeU_pow_inv q u
  have hU : mennickeU q ^ (2 * u) =
      (lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (qInv q ^ (2 * u)) * slToAway q mennickeB *
        lowerUnip q (((q : ℕ) : ZAway q) ^ (2 * u)) *
        (slToAway q mennickeB)⁻¹)⁻¹ := by
    rw [hword, inv_inv]

  rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure
    ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))), MonoidHom.mem_ker, hU]
  rw [map_inv, map_mul, map_mul, map_mul, map_mul, map_mul]
  rw [mk_lowerUnip_eq_mk_mennickeA q m hcast,
    mk_lowerUnip_eq_mk_mennickeA q m hcast']
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    mennicke_relation_word_eq_one q, map_one, inv_one]

end TwoTwentyFour
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section TwoTwenty

variable (q m : ℕ) [NeZero q]

omit [NeZero q] in

theorem mennicke_two_nineteen (s : ℕ) (t : ℤ) (X : SL(2, ZAway q))
    (h17 : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) t =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * ((q : ℕ) : ZAway q) ^ (2 * s)) :
    (((mennickeU q ^ s)⁻¹ *
        (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
        (mennickeU q ^ s)⁻¹ : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 ∧
    (((mennickeU q ^ s)⁻¹ *
        (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
        (mennickeU q ^ s)⁻¹ : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 := by
  obtain ⟨hW00, hW01⟩ := mennicke_two_fifteen q t X
  rw [h17] at hW00
  constructor
  · rw [mennickeU_pow_inv_sandwich_coe]
    simp only [Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply]
    rw [hW00, mul_assoc, natCast_q_pow_mul_qInv_pow, mul_one]
  · rw [mennickeU_pow_inv_sandwich_coe]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply]
    rw [hW01]

set_option maxHeartbeats 3200000 in
theorem mennicke_two_twenty_of_lemma21 (hmq : Nat.Coprime m q)
    (h21 : MennickeLemma21 q m hmq)
    (X : SL(2, ZAway q)) (hX : X ∈ principalCongruenceAway m q hmq)
    (s : ℕ) (t : ℤ)
    (h16 : mennickeU q ^ (2 * s) ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
    (h17 : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) t =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * ((q : ℕ) : ZAway q) ^ (2 * s)) :
    QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) =
    QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X := by

  have hWmem : ((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t ∈
      principalCongruenceAway m q hmq := by
    have h := Subgroup.Normal.conj_mem (inferInstance :
      (principalCongruenceAway m q hmq).Normal) X hX
      (((slToAway q mennickeA) ^ t)⁻¹)
    rwa [inv_inv] at h

  obtain ⟨hV00, hV01⟩ := mennicke_two_nineteen q s t X h17

  have hU2s_inv : (mennickeU q ^ (2 * s))⁻¹ ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) :=
    Subgroup.inv_mem _ h16

  have hVdecomp : (mennickeU q ^ s)⁻¹ *
      (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
      (mennickeU q ^ s)⁻¹ =
      ((mennickeU q ^ s)⁻¹ *
        (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
        mennickeU q ^ s) * (mennickeU q ^ (2 * s))⁻¹ := by
    rw [two_mul, pow_add]
    group

  have hVmem : (mennickeU q ^ s)⁻¹ *
      (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
      (mennickeU q ^ s)⁻¹ ∈ principalCongruenceAway m q hmq := by
    rw [hVdecomp]
    refine Subgroup.mul_mem _ ?_ ?_
    · have h := Subgroup.Normal.conj_mem (inferInstance :
        (principalCongruenceAway m q hmq).Normal) _ hWmem ((mennickeU q ^ s)⁻¹)
      rwa [inv_inv] at h
    · exact normalClosure_le_principalCongruenceAway m q hmq hU2s_inv

  have hmkV : QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      ((mennickeU q ^ s)⁻¹ *
        (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
        (mennickeU q ^ s)⁻¹) =
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      ((mennickeU q ^ s)⁻¹ *
        (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
        mennickeU q ^ s) := by
    rw [hVdecomp, map_mul]
    have h1 : QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
        ((mennickeU q ^ (2 * s))⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hU2s_inv
    rw [h1, mul_one]

  have hVX := mk_eq_mk_of_firstRow_eq q m hmq X _ hX hVmem hV00 hV01

  have hUs : (mennickeU q ^ s)⁻¹ ∈ mennickeZ q m hmq :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ ((mennickeLemma21_iff q m hmq).mp h21) s)
  have hconj : ⁅(mennickeU q ^ s)⁻¹,
      ((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t⁆ ∈
      Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) :=
    (mem_mennickeZ_iff q m hmq _).mp hUs _ hWmem
  have hWconj : QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      ((mennickeU q ^ s)⁻¹ *
        (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) *
        mennickeU q ^ s) =
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (((slToAway q mennickeA) ^ t)⁻¹ * X * (slToAway q mennickeA) ^ t) := by
    have h := mk_conj_eq_of_commutator_mem (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) hconj
    rwa [inv_inv] at h

  exact hWconj.symm.trans (hmkV.symm.trans hVX)

end TwoTwenty
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section TwoTwentySix

variable (q m : ℕ) [NeZero q]

theorem commutator_mennickeA_mem_of_solution (hmq : Nat.Coprime m q)
    (h21 : MennickeLemma21 q m hmq)
    (X : SL(2, ZAway q)) (hX : X ∈ principalCongruenceAway m q hmq)
    (s : ℕ) (t : ℤ)
    (h16 : mennickeU q ^ (2 * s) ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
    (h17 : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) t =
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 * ((q : ℕ) : ZAway q) ^ (2 * s))
    (h25 : IsCoprime t (m : ℤ)) :
    ⁅slToAway q mennickeA, X⁆ ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) := by

  have h20 := mennicke_two_twenty_of_lemma21 q m hmq h21 X hX s t h16 h17
  rw [map_mul, map_mul, map_inv, map_zpow] at h20
  have hcommt : Commute ((QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (slToAway q mennickeA)) ^ t)
      (QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X) :=
    commute_of_inv_mul_mul_eq h20

  have hAm0 : QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      ((slToAway q mennickeA) ^ m) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hAm1 : (QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (slToAway q mennickeA)) ^ ((m : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast,
      ← map_pow (QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))))
        (slToAway q mennickeA) m,
      hAm0]
  have hcommm : Commute ((QuotientGroup.mk' (Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
      (slToAway q mennickeA)) ^ ((m : ℕ) : ℤ))
      (QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X) := by
    rw [hAm1]
    exact Commute.one_left _

  rw [commutator_mem_iff_commute_mk]
  exact commute_of_isCoprime_zpow h25 hcommt hcommm

theorem mennickeA_mem_mennickeZ_of_solutions (hmq : Nat.Coprime m q)
    (hsol : ∀ X ∈ principalCongruenceAway m q hmq,
      ∃ X' ∈ principalCongruenceAway m q hmq,
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
          QuotientGroup.mk' (Subgroup.normalClosure
            ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X ∧
        ∃ (s : ℕ) (t : ℤ),
          mennickeU q ^ (2 * s) ∈ Subgroup.normalClosure
            ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) ∧
          ((X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
              (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) t =
            (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 *
              ((q : ℕ) : ZAway q) ^ (2 * s)) ∧
          IsCoprime t (m : ℤ)) :
    slToAway q mennickeA ∈ mennickeZ q m hmq := by
  rw [mem_mennickeZ_iff]
  intro X hX
  obtain ⟨X', hX'mem, hmkeq, s, t, h16, h17, h25⟩ := hsol X hX

  have h1 : ⁅slToAway q mennickeA, X'⁆ ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) :=
    commutator_mennickeA_mem_of_solution q m hmq (mennickeLemma21 q m hmq) X' hX'mem
      s t h16 h17 h25

  rw [commutator_mem_iff_commute_mk] at h1 ⊢
  rwa [hmkeq] at h1

theorem mennickeZ_eq_top_of_solutions (hmq : Nat.Coprime m q)
    (hsol : ∀ X ∈ principalCongruenceAway m q hmq,
      ∃ X' ∈ principalCongruenceAway m q hmq,
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
          QuotientGroup.mk' (Subgroup.normalClosure
            ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X ∧
        ∃ (s : ℕ) (t : ℤ),
          mennickeU q ^ (2 * s) ∈ Subgroup.normalClosure
            ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) ∧
          ((X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 +
              (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 * algebraMap ℤ (ZAway q) t =
            (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 *
              ((q : ℕ) : ZAway q) ^ (2 * s)) ∧
          IsCoprime t (m : ℤ)) :
    mennickeZ q m hmq = ⊤ :=
  eq_top_of_normal_of_mennickeA_mem q (mennickeZ q m hmq)
    (mennickeA_mem_mennickeZ_of_solutions q m hmq hsol)

end TwoTwentySix
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section DirichletSteps

end DirichletSteps
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section ArithmeticEngine

theorem mennicke_lifting_step {y M : ℤ} {ℓ : ℕ} (hℓM : (ℓ : ℤ) ∣ M)
    (hy : M ∣ y - 1) : (M * ℓ) ∣ y ^ ℓ - 1 := by
  rw [← geom_sum_mul y ℓ]
  have hℓy : (ℓ : ℤ) ∣ y - 1 := hℓM.trans hy
  have hsum : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range ℓ, y ^ i := by
    have h1 : ∀ i ∈ Finset.range ℓ, (ℓ : ℤ) ∣ y ^ i - 1 := fun i _ =>
      hℓy.trans (sub_one_dvd_pow_sub_one y i)
    have h2 : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range ℓ, (y ^ i - 1) := Finset.dvd_sum h1
    have h3 : ∑ i ∈ Finset.range ℓ, (y ^ i - 1) =
        (∑ i ∈ Finset.range ℓ, y ^ i) - (ℓ : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
    rw [h3] at h2
    have h4 := dvd_add h2 (dvd_refl (ℓ : ℤ))
    rwa [sub_add_cancel] at h4
  rw [mul_comm M (ℓ : ℤ)]
  exact mul_dvd_mul hsum hy

theorem mennicke_lifting_iterate {y : ℤ} {ℓ f : ℕ} (hf : 1 ≤ f)
    (hy : ((ℓ : ℤ) ^ f) ∣ y - 1) (k : ℕ) :
    ((ℓ : ℤ) ^ (f + k)) ∣ y ^ ℓ ^ k - 1 := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    have hstep : ((ℓ : ℤ) ^ (f + k) * ℓ) ∣ (y ^ ℓ ^ k) ^ ℓ - 1 :=
      mennicke_lifting_step (dvd_pow_self (ℓ : ℤ) (by omega : f + k ≠ 0)) ih
    have h1 : (ℓ : ℤ) ^ (f + k) * ℓ = (ℓ : ℤ) ^ (f + (k + 1)) := by
      rw [show f + (k + 1) = (f + k) + 1 by omega, pow_succ]
    have h2 : (y ^ ℓ ^ k) ^ ℓ = y ^ ℓ ^ (k + 1) := by
      rw [← pow_mul, ← pow_succ]
    rwa [h1, h2] at hstep

theorem mennicke_two_twentyone_of_corrected_reading (x m : ℕ) (hx : 2 ≤ x) (hm : m ≠ 0)
    (hdvd : (x - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (x - 1)) :
    m ∣ x ^ (m / (x - 1)) - 1 := by
  have hd0 : x - 1 ≠ 0 := by omega
  have hx1 : (1 : ℕ) ≤ x := by omega

  have hu : 0 < m / (x - 1) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd) (by omega)

  have hXgt : 1 < x ^ (m / (x - 1)) :=
    lt_of_lt_of_le (by omega : (1 : ℕ) < x) (Nat.le_self_pow (by omega) x)
  have hX0 : x ^ (m / (x - 1)) - 1 ≠ 0 := by omega

  rw [← Nat.factorization_le_iff_dvd hm hX0, Finsupp.le_iff]
  intro ℓ hℓsupp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hℓsupp
  obtain ⟨hℓp, hℓm, -⟩ := hℓsupp

  set e := m.factorization ℓ with he
  set f := (x - 1).factorization ℓ with hf

  have hℓd : ℓ ∣ x - 1 := hsupp ℓ hℓp hℓm
  have hf1 : 1 ≤ f := hℓp.factorization_pos_of_dvd hd0 hℓd

  have hfact_le : (x - 1).factorization ≤ m.factorization :=
    (Nat.factorization_le_iff_dvd hd0 hm).mpr hdvd
  have hfe : f ≤ e := Finsupp.le_def.mp hfact_le ℓ

  have hpf_nat : ℓ ^ f ∣ x - 1 := Nat.ordProj_dvd (x - 1) ℓ
  have hpf_int : ((ℓ : ℤ)) ^ f ∣ (x : ℤ) - 1 := by
    have h := Int.natCast_dvd_natCast.mpr hpf_nat
    rwa [Nat.cast_pow, Nat.cast_sub hx1, Nat.cast_one] at h

  have hlift : ((ℓ : ℤ)) ^ e ∣ (x : ℤ) ^ ℓ ^ (e - f) - 1 := by
    have h := mennicke_lifting_iterate hf1 hpf_int (e - f)
    rwa [Nat.add_sub_cancel' hfe] at h

  have hu_fact : (m / (x - 1)).factorization ℓ = e - f := by
    rw [Nat.factorization_div hdvd, Finsupp.tsub_apply]
  have hdvd_u : ℓ ^ (e - f) ∣ m / (x - 1) := by
    rw [← hu_fact]
    exact Nat.ordProj_dvd _ _

  have hchain : (x : ℤ) ^ ℓ ^ (e - f) - 1 ∣ (x : ℤ) ^ (m / (x - 1)) - 1 :=
    dvd_pow_sub_one_of_dvd hdvd_u

  have hint : ((ℓ : ℤ)) ^ e ∣ (x : ℤ) ^ (m / (x - 1)) - 1 := hlift.trans hchain
  have hnat : ℓ ^ e ∣ x ^ (m / (x - 1)) - 1 := by
    have hcast : ((x ^ (m / (x - 1)) - 1 : ℕ) : ℤ) = (x : ℤ) ^ (m / (x - 1)) - 1 := by
      rw [Nat.cast_sub (le_of_lt hXgt), Nat.cast_pow, Nat.cast_one]
    rw [← Int.natCast_dvd_natCast, hcast, Nat.cast_pow]
    exact hint
  exact (hℓp.pow_dvd_iff_le_factorization hX0).mp hnat

theorem mennicke_two_thirty_implies_two_twentyone (q m : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0)
    (hdvd : (q ^ 2 - 1) ∣ m) (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) :
    m ∣ q ^ (2 * (m / (q ^ 2 - 1))) - 1 := by
  have hx : 2 ≤ q ^ 2 := le_trans hq (Nat.le_self_pow (by omega) q)
  have h := mennicke_two_twentyone_of_corrected_reading (q ^ 2) m hx hm hdvd hsupp
  rwa [pow_mul]

end ArithmeticEngine
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section TwoFourteen

variable (q m : ℕ) [NeZero q]

omit [NeZero q] in

theorem exists_mennicke_firstRow_data (hmq : Nat.Coprime m q) (hm : m ≠ 1)
    (X : SL(2, ZAway q)) (hX : X ∈ principalCongruenceAway m q hmq)
    (hX01 : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 ≠ 0) :
    ∃ (a b : ℤ) (v : ZAway q),
      a ≠ 0 ∧ b ≠ 0 ∧ IsCoprime a b ∧ IsCoprime a (m : ℤ) ∧
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 = algebraMap ℤ (ZAway q) a * v ∧
      (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 = algebraMap ℤ (ZAway q) ((m : ℤ) * b) * v := by

  obtain ⟨hα1, hβ0, -, -⟩ := (mem_principalCongruenceAway_iff_entries q m hmq X).mp hX

  obtain ⟨y₀, hy₀⟩ := (zAwayToZMod_eq_zero_iff q m hmq _).mp hβ0

  obtain ⟨a₁, k₁, ha₁⟩ := exists_eq_algebraMap_mul_invSelf_pow_even q
    ((X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0)
  obtain ⟨c₁, k₂, hc₁⟩ := exists_eq_algebraMap_mul_invSelf_pow_even q y₀

  have hX00 : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
      algebraMap ℤ (ZAway q) (a₁ * (q : ℤ) ^ (2 * k₂)) * qInv q ^ (2 * (k₁ + k₂)) := by
    rw [ha₁, map_mul, map_pow, map_natCast]
    linear_combination (-(algebraMap ℤ (ZAway q) a₁ * qInv q ^ (2 * k₁))) *
      natCast_q_pow_mul_qInv_pow q (2 * k₂)
  have hX01' : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
      algebraMap ℤ (ZAway q) ((m : ℤ) * (c₁ * (q : ℤ) ^ (2 * k₁))) * qInv q ^ (2 * (k₁ + k₂)) := by
    rw [hy₀, hc₁, map_mul, map_mul, map_pow, map_natCast, map_natCast]
    linear_combination (-((m : ZAway q) * algebraMap ℤ (ZAway q) c₁ * qInv q ^ (2 * k₂))) *
      natCast_q_pow_mul_qInv_pow q (2 * k₁)

  have hmc₀ : (m : ℤ) * (c₁ * (q : ℤ) ^ (2 * k₁)) ≠ 0 := by
    intro h
    apply hX01
    rw [hX01', h, map_zero, zero_mul]

  obtain ⟨g, a, B, hga, hgB, hgcd, hBne⟩ :=
    exists_coprime_factorization (a₁ * (q : ℤ) ^ (2 * k₂))
      ((m : ℤ) * (c₁ * (q : ℤ) ^ (2 * k₁))) hmc₀
  have hcopaB : IsCoprime a B := Int.isCoprime_iff_gcd_eq_one.mpr hgcd

  have hα1' : (1 : ZMod m) = ((a₁ * (q : ℤ) ^ (2 * k₂) : ℤ) : ZMod m) *
      zAwayToZMod m q hmq (qInv q ^ (2 * (k₁ + k₂))) := by
    rw [← hα1, hX00, map_mul, zAwayToZMod_algebraMap]
  have hua₀ : IsUnit ((a₁ * (q : ℤ) ^ (2 * k₂) : ℤ) : ZMod m) :=
    IsUnit.of_mul_eq_one _ hα1'.symm

  have hga₀ : (g : ℤ) ∣ a₁ * (q : ℤ) ^ (2 * k₂) := ⟨a, hga.symm⟩
  have hgm : Nat.Coprime g m := by
    have h1 : Nat.Coprime (a₁ * (q : ℤ) ^ (2 * k₂)).natAbs m :=
      (isUnit_intCast_zmod_iff_coprime _ m).mp hua₀
    have h2 : g ∣ (a₁ * (q : ℤ) ^ (2 * k₂)).natAbs := by
      rw [← Int.natCast_dvd_natCast]
      exact Int.dvd_natAbs.mpr hga₀
    exact Nat.Coprime.coprime_dvd_left h2 h1

  have hmB : (m : ℤ) ∣ B := by
    have h1 : (m : ℤ) ∣ (g : ℤ) * B := ⟨c₁ * (q : ℤ) ^ (2 * k₁), hgB⟩
    exact IsCoprime.dvd_of_dvd_mul_left ((Nat.Coprime.isCoprime hgm.symm)) h1
  obtain ⟨b, hb⟩ := hmB

  have hbne : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hBne hb
  have hcop_ab : IsCoprime a b := by
    have h := hcopaB
    rw [hb] at h
    exact h.of_mul_right_right
  have hcop_am : IsCoprime a (m : ℤ) := by
    have h := hcopaB
    rw [hb] at h
    exact h.of_mul_right_left
  have hane : a ≠ 0 := by
    rintro rfl
    have h1 : IsUnit ((m : ℤ)) := isCoprime_zero_left.mp hcop_am
    rw [Int.isUnit_iff] at h1
    rcases h1 with h1 | h1
    · exact hm (by exact_mod_cast h1)
    · omega

  refine ⟨a, b, algebraMap ℤ (ZAway q) (g : ℤ) * qInv q ^ (2 * (k₁ + k₂)),
    hane, hbne, hcop_ab, hcop_am, ?_, ?_⟩
  · rw [hX00, ← hga]
    simp only [map_mul]
    ring
  · rw [hX01', ← hgB, hb]
    simp only [map_mul]
    ring

end TwoFourteen
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section DiophantineCarrier

def MennickeDiophantineSolutionAt (q m u : ℕ) : Prop :=
  ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → IsCoprime a b → IsCoprime a (m : ℤ) →
    ∃ (r : ℕ) (y t : ℤ),
      (b + a * y) * (m : ℤ) * t = a * ((q : ℤ) ^ (2 * (r * u)) - 1) ∧
      IsCoprime t (m : ℤ)

theorem mennickeDiophantineSolutionAt_one (q u : ℕ) :
    MennickeDiophantineSolutionAt q 1 u := by
  intro a b _ _ _ _
  refine ⟨0, 0, 0, ?_, ?_⟩
  · norm_num
  · rw [Nat.cast_one]
    exact isCoprime_one_right

end DiophantineCarrier
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section Headline

variable (q m : ℕ) [NeZero q]

set_option maxHeartbeats 6400000 in

theorem mennickeZ_eq_top_of_dvd_of_diophantine (hmq : Nat.Coprime m q) (u : ℕ)
    (h21 : m ∣ q ^ (2 * u) - 1)
    (hsol : MennickeDiophantineSolutionAt q m u) :
    mennickeZ q m hmq = ⊤ := by

  by_cases hm1 : m = 1
  · subst hm1
    rw [← top_le_iff, ← normalClosure_mennickeA_pow_one_eq_top q]
    exact mennickeQ_le_mennickeZ q 1 hmq

  have h16u : mennickeU q ^ (2 * u) ∈ Subgroup.normalClosure
      ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)) :=
    mennickeU_pow_mem_normalClosure_of_dvd q m u h21

  apply mennickeZ_eq_top_of_solutions q m hmq
  intro X hX
  by_cases hX01 : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 = 0
  ·

    refine ⟨X, hX, rfl, 0, 1, ?_, ?_, ?_⟩
    · rw [Nat.mul_zero, pow_zero]
      exact Subgroup.one_mem _
    · rw [hX01, Nat.mul_zero, pow_zero, zero_mul, add_zero, mul_one]
    · exact isCoprime_one_left
  ·
    obtain ⟨a, b, v, hane, hbne, hab, ham, hX00v, hX01v⟩ :=
      exists_mennicke_firstRow_data q m hmq hm1 X hX hX01
    obtain ⟨r, y, t, h17int, h25⟩ := hsol a b hane hbne hab ham

    refine ⟨X * upperUnip q ((m : ZAway q) * algebraMap ℤ (ZAway q) y), ?_, ?_, r * u, t,
      ?_, ?_, h25⟩
    ·
      exact Subgroup.mul_mem _ hX
        (upperUnip_natCast_mul_mem_principalCongruenceAway q m hmq _)
    ·
      rw [map_mul]
      have h1 : QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q)))
          (upperUnip q ((m : ZAway q) * algebraMap ℤ (ZAway q) y)) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact upperUnip_natCast_mul_mem_normalClosure q m _
      rw [h1, mul_one]
    ·
      have h2ru : 2 * (r * u) = (2 * u) * r := by ring
      rw [h2ru, pow_mul]
      exact Subgroup.pow_mem _ h16u r
    ·
      have hX'00 : ((X * upperUnip q ((m : ZAway q) * algebraMap ℤ (ZAway q) y) :
          SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
          algebraMap ℤ (ZAway q) a * v := by
        rw [mul_upperUnip_coe]
        simp only [Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.of_apply]
        exact hX00v
      have hX'01 : ((X * upperUnip q ((m : ZAway q) * algebraMap ℤ (ZAway q) y) :
          SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
          algebraMap ℤ (ZAway q) a * v * ((m : ZAway q) * algebraMap ℤ (ZAway q) y) +
            algebraMap ℤ (ZAway q) ((m : ℤ) * b) * v := by
        rw [mul_upperUnip_coe]
        simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.of_apply]
        rw [hX00v, hX01v]
      rw [hX'00, hX'01]

      have key : a + ((m : ℤ) * b * t + a * ((m : ℤ) * y) * t) =
          a * (q : ℤ) ^ (2 * (r * u)) := by
        linear_combination h17int
      have hcast : algebraMap ℤ (ZAway q) (a + ((m : ℤ) * b * t + a * ((m : ℤ) * y) * t)) =
          algebraMap ℤ (ZAway q) (a * (q : ℤ) ^ (2 * (r * u))) := by
        rw [key]
      simp only [map_add, map_mul, map_pow, map_natCast] at hcast
      simp only [map_mul, map_natCast]
      linear_combination v * hcast

end Headline
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

section CorrectedReading

variable (q m : ℕ) [NeZero q]

set_option maxHeartbeats 3200000 in
theorem mennickeZ_eq_top_of_corrected_reading_of_diophantine_impl
    (hmq : Nat.Coprime m q) (hq : 2 ≤ q)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (hsol : MennickeDiophantineSolutionAt q m (m / (q ^ 2 - 1))) :
    mennickeZ q m hmq = ⊤ := by

  have hm : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hmq
    omega

  have h21 : m ∣ q ^ (2 * (m / (q ^ 2 - 1))) - 1 :=
    mennicke_two_thirty_implies_two_twentyone q m hq hm hdvd hsupp
  exact mennickeZ_eq_top_of_dvd_of_diophantine q m hmq (m / (q ^ 2 - 1)) h21 hsol

end CorrectedReading
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara"

open scoped MatrixGroups commutatorElement in
open _root_.Ihara _root_.P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.Ihara in
theorem solution
    (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (hq : 2 ≤ q)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (hsol : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → IsCoprime a b → IsCoprime a (m : ℤ) →
      ∃ (r : ℕ) (y t : ℤ),
        (b + a * y) * (m : ℤ) * t = a * ((q : ℤ) ^ (2 * (r * (m / (q ^ 2 - 1)))) - 1) ∧
        IsCoprime t (m : ℤ)) :
    Ihara.mennickeZ q m hmq = ⊤ :=
  Ihara.mennickeZ_eq_top_of_corrected_reading_of_diophantine_impl q m hmq hq hdvd hsupp hsol

#print axioms solution

end S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine
end P2MW
export P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine (solution)
