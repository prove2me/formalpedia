-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.phi_eq_phiTwo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4e6e3eba-6e47-564f-9218-9d175094c294

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Theorems.Thm_ModularCurve_coeff_jNum_le_six
import Theorems.Thm_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Polynomial PowerSeries
p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one coeff_jq_of_lt dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData qTwist qTwist_coeff qTwist_one_apply jqModC_rat phiTwoC2 phiTwoC1 phiTwoC0 phiTwo coeff_jNum_le_six eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero ModularPolynomialData.natDegree_coeff_le PhiGen.splits_prime_of_isPrimitiveRoot"
p2m_open "ModularCurve"
namespace PhiTwoCalc

variable {R : Type*} [CommRing R]

def LowCoeffs (f : R⟦X⟧) (L : List R) : Prop :=
  ∀ i : ℕ, i < L.length → PowerSeries.coeff i f = L.getD i 0

def conv (L M : List R) : List R :=
  (List.range (min L.length M.length)).map
    fun k => ((List.range (k + 1)).map fun i => L.getD i 0 * M.getD (k - i) 0).sum

theorem length_conv (L M : List R) : (conv L M).length = min L.length M.length := by simp [conv]

theorem finset_sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem getD_conv (L M : List R) {k : ℕ} (hk : k < min L.length M.length) :
    (conv L M).getD k 0 = ∑ i ∈ Finset.range (k + 1), L.getD i 0 * M.getD (k - i) 0 := by
  rw [conv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp [finset_sum_range_eq_list_sum]

theorem LowCoeffs.mul {f g : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g M) :
    LowCoeffs (f * g) (conv L M) := by
  intro k hk
  rw [length_conv] at hk
  rw [getD_conv L M hk, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hf i (by omega), hg (k - i) (by omega)]

theorem LowCoeffs.congr {f : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (h : L = M) : LowCoeffs f M :=
  h ▸ hf

theorem getD_map_intCast (l : List ℤ) (i : ℕ) : (l.map (Int.cast : ℤ → R)).getD i 0 = ((l.getD i 0 : ℤ) : R) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem conv_map_intCast (L M : List ℤ) :
    conv (L.map (Int.cast : ℤ → R)) (M.map (Int.cast : ℤ → R)) = (conv L M).map (Int.cast : ℤ → R) := by
  simp only [conv, List.length_map, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, getD_map_intCast]
  rw [Int.cast_list_sum, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp [Function.comp_apply, Int.cast_mul]

noncomputable abbrev ofPS (F : ℚ⟦X⟧) : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ F

theorem coeff_ofPS (F : ℚ⟦X⟧) (m : ℤ) :
    (ofPS F).coeff m = if 0 ≤ m then PowerSeries.coeff m.toNat F else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, HahnSeries.ofPowerSeries_apply_coeff]
  · exact ofPowerSeries_coeff_of_neg F (by omega)

theorem coeff_single_mul_ofPS (a : ℤ) (r : ℚ) (F : ℚ⟦X⟧) (m : ℤ) :
    (HahnSeries.single a r * ofPS F).coeff m = if a ≤ m then r * PowerSeries.coeff (m - a).toNat F else 0 := by
  rw [HahnSeries.coeff_single_mul, coeff_ofPS]
  by_cases h : a ≤ m
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h, mul_zero]

theorem eq_single_mul_ofPS (x : LaurentSeries ℚ) (a : ℤ) (hx : ∀ m < a, x.coeff m = 0) :
    x = HahnSeries.single a 1 * ofPS (PowerSeries.mk fun i => x.coeff (a + i)) := by
  ext m
  rw [coeff_single_mul_ofPS, one_mul]
  split_ifs with h
  · rw [PowerSeries.coeff_mk]; congr 1; omega
  · exact hx m (by omega)

def NF (x : LaurentSeries ℚ) (a : ℤ) (L : List ℤ) : Prop :=
  ∃ F : ℚ⟦X⟧, x = HahnSeries.single a 1 * ofPS F ∧ LowCoeffs F (L.map (Int.cast : ℤ → ℚ))

theorem NF.mul {x y : LaurentSeries ℚ} {a b : ℤ} {L M : List ℤ} (hx : NF x a L) (hy : NF y b M) :
    NF (x * y) (a + b) (conv L M) := by
  obtain ⟨F, rfl, hF⟩ := hx
  obtain ⟨G, rfl, hG⟩ := hy
  refine ⟨F * G, ?_, ?_⟩
  · rw [mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul]
    congr 1
    exact (map_mul (HahnSeries.ofPowerSeries ℤ ℚ) F G).symm
  · rw [← conv_map_intCast]; exact hF.mul hG

theorem NF.congr {x : LaurentSeries ℚ} {a : ℤ} {L M : List ℤ} (hx : NF x a L) (h : L = M) : NF x a M := h ▸ hx

theorem NF.coeff {x : LaurentSeries ℚ} {a : ℤ} {L : List ℤ} (hx : NF x a L) (m : ℤ) (hm : (m - a).toNat < L.length) :
    x.coeff m = if a ≤ m then ((L.getD (m - a).toNat 0 : ℤ) : ℚ) else 0 := by
  obtain ⟨F, rfl, hF⟩ := hx
  rw [coeff_single_mul_ofPS, one_mul]
  split_ifs with h
  · rw [hF _ (by simpa using hm), getD_map_intCast]
  · rfl

theorem coeff_jq_eq (i : ℕ) : jq.coeff (-1 + (i : ℤ)) = ((PowerSeries.coeff i jNum : ℤ) : ℚ) := by
  rw [show jq = HahnSeries.single (-1 : ℤ) 1 * ofPS jNumQ from rfl, coeff_single_mul_ofPS, one_mul,
    if_pos (by omega), show (-1 + (i : ℤ) - -1).toNat = i by omega, jNumQ, PowerSeries.coeff_map]
  simp

def LJ : List ℤ := [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600]

theorem coeff_jNum_eq_LJ (i : ℕ) (hi : i < 7) : (PowerSeries.coeff i jNum : ℤ) = LJ.getD i 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ModularCurve.coeff_jNum_le_six
  interval_cases i <;> simp [LJ, h0, h1, h2, h3, h4, h5, h6]

theorem nf_jq : NF jq (-1) LJ := by
  refine ⟨PowerSeries.mk fun i => jq.coeff (-1 + i), eq_single_mul_ofPS jq (-1) (fun m hm => coeff_jq_of_lt hm), ?_⟩
  intro i hi
  simp only [List.length_map, LJ, List.length_cons, List.length_nil] at hi
  rw [PowerSeries.coeff_mk, coeff_jq_eq, coeff_jNum_eq_LJ i (by omega), getD_map_intCast]

def LC : List ℤ := [-1, 744, -196884, 21493760, -864299970, 20245856256, -333202640600]

theorem nf_qTwist_neg_one_jq : NF (qTwist (-1 : ℚˣ) jq) (-1) LC := by
  refine ⟨PowerSeries.mk fun i => (qTwist (-1 : ℚˣ) jq).coeff (-1 + i),
    eq_single_mul_ofPS _ (-1) (fun m hm => by rw [qTwist_coeff, coeff_jq_of_lt hm, mul_zero]), ?_⟩
  intro i hi
  simp only [List.length_map, LC, List.length_cons, List.length_nil] at hi
  rw [PowerSeries.coeff_mk, qTwist_coeff, coeff_jq_eq, coeff_jNum_eq_LJ i (by omega)]
  rw [getD_map_intCast]
  interval_cases i <;> simp [LJ, LC, Units.val_zpow_eq_zpow_val] <;> norm_num

def LA : List ℤ := [1, 0, 0, 0, 744, 0, 0]

theorem nf_qExpand_four_jq : NF (qExpand ℚ 4 jq) (-4) LA := by
  refine ⟨PowerSeries.mk fun i => (qExpand ℚ 4 jq).coeff (-4 + i), eq_single_mul_ofPS _ (-4) (fun m hm => ?_), ?_⟩
  · by_cases h : (4 : ℤ) ∣ m
    · obtain ⟨c, rfl⟩ := h
      have h4 := qExpand_coeff_mul (R := ℚ) 4 jq c
      rw [Nat.cast_ofNat] at h4
      rw [h4]
      exact coeff_jq_of_lt (by omega)
    · exact qExpand_coeff_of_not_dvd 4 jq (by exact_mod_cast h)
  · intro i hi
    simp only [List.length_map, LA, List.length_cons, List.length_nil] at hi
    rw [PowerSeries.coeff_mk]
    interval_cases i
    · rw [show (-4 : ℤ) + ((0 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) * (-1) by norm_num, qExpand_coeff_mul, coeff_jq_neg_one]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [show (-4 : ℤ) + ((4 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) * 0 by norm_num, qExpand_coeff_mul,
        show (0 : ℤ) = -1 + ((1 : ℕ) : ℤ) by norm_num, coeff_jq_eq, coeff_jNum_eq_LJ 1 (by omega)]; simp [LA, LJ]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]

def L2 : List ℤ := [1, 0, 744, 0, 196884, 0, 21493760]

theorem nf_qExpand_two_jq : NF (qExpand ℚ 2 jq) (-2) L2 := by
  refine ⟨PowerSeries.mk fun i => (qExpand ℚ 2 jq).coeff (-2 + i), eq_single_mul_ofPS _ (-2) (fun m hm => ?_), ?_⟩
  · by_cases h : (2 : ℤ) ∣ m
    · obtain ⟨c, rfl⟩ := h
      have h2 := qExpand_coeff_mul (R := ℚ) 2 jq c
      rw [Nat.cast_ofNat] at h2
      rw [h2]
      exact coeff_jq_of_lt (by omega)
    · exact qExpand_coeff_of_not_dvd 2 jq (by exact_mod_cast h)
  · intro i hi
    simp only [List.length_map, L2, List.length_cons, List.length_nil] at hi
    rw [PowerSeries.coeff_mk]
    interval_cases i
    · rw [show (-2 : ℤ) + ((0 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1) by norm_num, qExpand_coeff_mul, coeff_jq_neg_one]; simp [L2]
    · rw [qExpand_coeff_of_not_dvd 2 jq (by decide)]; simp [L2]
    · rw [show (-2 : ℤ) + ((2 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1 + ((1 : ℕ) : ℤ)) by norm_num, qExpand_coeff_mul,
        coeff_jq_eq, coeff_jNum_eq_LJ 1 (by omega)]; simp [L2, LJ]
    · rw [qExpand_coeff_of_not_dvd 2 jq (by decide)]; simp [L2]
    · rw [show (-2 : ℤ) + ((4 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1 + ((2 : ℕ) : ℤ)) by norm_num, qExpand_coeff_mul,
        coeff_jq_eq, coeff_jNum_eq_LJ 2 (by omega)]; simp [L2, LJ]
    · rw [qExpand_coeff_of_not_dvd 2 jq (by decide)]; simp [L2]
    · rw [show (-2 : ℤ) + ((6 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1 + ((3 : ℕ) : ℤ)) by norm_num, qExpand_coeff_mul,
        coeff_jq_eq, coeff_jNum_eq_LJ 3 (by omega)]; simp [L2, LJ]

end PhiTwoCalc
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum jNumQ jq ofPowerSeries_coeff_of_neg coeff_jq_neg_one coeff_jq_of_lt dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData qTwist qTwist_coeff qTwist_one_apply jqModC_rat phiTwoC2 phiTwoC1 phiTwoC0 phiTwo coeff_jNum_le_six eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero ModularPolynomialData.natDegree_coeff_le PhiGen.splits_prime_of_isPrimitiveRoot"
p2m_open "ModularCurve"
namespace PhiTwoCalc

theorem nf_AB : NF (qExpand ℚ 4 jq * jq) (-5) [1, 744, 196884, 21493760, 864300714, 20246409792, 333349122296] :=
  (nf_qExpand_four_jq.mul nf_jq).congr (by decide)
theorem nf_ACm : NF (qExpand ℚ 4 jq * qTwist (-1 : ℚˣ) jq) (-5)
    [-1, 744, -196884, 21493760, -864300714, 20246409792, -333349122296] :=
  (nf_qExpand_four_jq.mul nf_qTwist_neg_one_jq).congr (by decide)
theorem nf_BCm : NF (jq * qTwist (-1 : ℚˣ) jq) (-2) [-1, 0, 159768, 0, -8509194516, 0, 151107477178368] :=
  (nf_jq.mul nf_qTwist_neg_one_jq).congr (by decide)
theorem nf_ABCm : NF (qExpand ℚ 4 jq * jq * qTwist (-1 : ℚˣ) jq) (-6)
    [-1, 0, 159768, 0, -8509195260, 0, 151107596045760] :=
  (nf_AB.mul nf_qTwist_neg_one_jq).congr (by decide)
theorem nf_J22 : NF (qExpand ℚ 2 jq * qExpand ℚ 2 jq) (-4) [1, 0, 1488, 0, 947304, 0, 335950912] :=
  (nf_qExpand_two_jq.mul nf_qExpand_two_jq).congr (by decide)
theorem nf_J23 : NF (qExpand ℚ 2 jq * qExpand ℚ 2 jq * qExpand ℚ 2 jq) (-6) [1, 0, 2232, 0, 2251260, 0, 1355202240] :=
  (nf_J22.mul nf_qExpand_two_jq).congr (by decide)

theorem isPrimitiveRoot_neg_one : IsPrimitiveRoot ((-1 : ℚˣ) : ℚ) 2 := by
  simpa using IsPrimitiveRoot.neg_one (R := ℚ) 0 (by norm_num)

theorem eval₂_qExpand_two_jq (P : Polynomial ℤ) :
    Polynomial.eval₂ (Int.castRingHom (LaurentSeries ℚ)) (qExpand ℚ 2 jq) P = qExpand ℚ 2 (evalAtJ P) := by
  have : (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (qExpand ℚ 2 jq))
      = (qExpand ℚ 2).comp evalAtJ := by
    refine Polynomial.ringHom_ext (fun z => by simp) ?_
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply, evalAtJ_X]
  exact congrArg (fun f => f P) (congrArg DFunLike.coe this)

theorem cubic_expand (a b c : LaurentSeries ℚ) :
    (Polynomial.X - Polynomial.C a) * ((Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c))
      = Polynomial.X ^ 3 - Polynomial.C (a + b + c) * Polynomial.X ^ 2
        + Polynomial.C (a * b + a * c + b * c) * Polynomial.X - Polynomial.C (a * b * c) := by
  simp only [map_add, map_mul]
  ring

theorem coeff_identities (data : ModularPolynomialData 2) :
    qExpand ℚ 2 (evalAtJ (data.Φ.coeff 2)) = -(qExpand ℚ 4 jq + jq + qTwist (-1 : ℚˣ) jq) ∧
    qExpand ℚ 2 (evalAtJ (data.Φ.coeff 1))
      = qExpand ℚ 4 jq * jq + qExpand ℚ 4 jq * qTwist (-1 : ℚˣ) jq + jq * qTwist (-1 : ℚˣ) jq ∧
    qExpand ℚ 2 (evalAtJ (data.Φ.coeff 0)) = -(qExpand ℚ 4 jq * jq * qTwist (-1 : ℚˣ) jq) := by
  have h := ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot (K := ℚ) 2 (-1) isPrimitiveRoot_neg_one data
  have e4 : qExpand ℚ (2 * 2) jq = qExpand ℚ 4 jq := rfl
  rw [jqModC_rat, Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one, qTwist_one_apply,
    e4, cubic_expand] at h
  have hc : ∀ k, qExpand ℚ 2 (evalAtJ (data.Φ.coeff k))
      = (Polynomial.X ^ 3 - Polynomial.C (qExpand ℚ 4 jq + jq + qTwist (-1 : ℚˣ) jq) * Polynomial.X ^ 2
        + Polynomial.C (qExpand ℚ 4 jq * jq + qExpand ℚ 4 jq * qTwist (-1 : ℚˣ) jq + jq * qTwist (-1 : ℚˣ) jq) * Polynomial.X
        - Polynomial.C (qExpand ℚ 4 jq * jq * qTwist (-1 : ℚˣ) jq)).coeff k := by
    intro k
    rw [← h, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom, eval₂_qExpand_two_jq]
  refine ⟨?_, ?_, ?_⟩ <;> [rw [hc 2]; rw [hc 1]; rw [hc 0]] <;>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_X_pow, Polynomial.coeff_C] <;>
    norm_num

theorem phiTwo_coeff :
    phiTwo.coeff 0 = phiTwoC0 ∧ phiTwo.coeff 1 = phiTwoC1 ∧ phiTwo.coeff 2 = phiTwoC2 ∧ phiTwo.coeff 3 = 1 ∧
      ∀ n, 4 ≤ n → phiTwo.coeff n = 0 := by
  have hdeg : phiTwo.natDegree ≤ 3 := by unfold phiTwo; compute_degree!
  refine ⟨?_, ?_, ?_, ?_, fun n hn => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)⟩ <;>
    simp [phiTwo, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]

theorem natDegree_phiTwoC : phiTwoC0.natDegree ≤ 3 ∧ phiTwoC1.natDegree ≤ 3 ∧ phiTwoC2.natDegree ≤ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold phiTwoC0; compute_degree!
  · unfold phiTwoC1; compute_degree!
  · unfold phiTwoC2; compute_degree!

theorem qExpand_evalAtJ_phiTwoC :
    qExpand ℚ 2 (evalAtJ phiTwoC2)
      = -(qExpand ℚ 2 jq * qExpand ℚ 2 jq) + HahnSeries.C (1488 : ℚ) * qExpand ℚ 2 jq - HahnSeries.C (162000 : ℚ) ∧
    qExpand ℚ 2 (evalAtJ phiTwoC1)
      = HahnSeries.C (1488 : ℚ) * (qExpand ℚ 2 jq * qExpand ℚ 2 jq) + HahnSeries.C (40773375 : ℚ) * qExpand ℚ 2 jq
        + HahnSeries.C (8748000000 : ℚ) ∧
    qExpand ℚ 2 (evalAtJ phiTwoC0)
      = qExpand ℚ 2 jq * qExpand ℚ 2 jq * qExpand ℚ 2 jq - HahnSeries.C (162000 : ℚ) * (qExpand ℚ 2 jq * qExpand ℚ 2 jq)
        + HahnSeries.C (8748000000 : ℚ) * qExpand ℚ 2 jq - HahnSeries.C (157464000000000 : ℚ) := by
  simp only [map_ofNat]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    rw [← eval₂_qExpand_two_jq]
    simp only [phiTwoC2, phiTwoC1, phiTwoC0, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_neg]
    ring

theorem coeff_C_mul' (r : ℚ) (x : LaurentSeries ℚ) (m : ℤ) : (HahnSeries.C r * x).coeff m = r * x.coeff m := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_C' (r : ℚ) (m : ℤ) : (HahnSeries.C r : LaurentSeries ℚ).coeff m = if m = 0 then r else 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem coeff_eq_coeff_qExpand_two (f : LaurentSeries ℚ) (m : ℤ) : f.coeff m = (qExpand ℚ 2 f).coeff (2 * m) := by
  have h := qExpand_coeff_mul (R := ℚ) 2 f m
  rw [Nat.cast_ofNat] at h
  exact h.symm

set_option maxHeartbeats 3200000 in
theorem ModularPolynomialData.phi_eq_phiTwo' (data : ModularPolynomialData 2) : data.Φ = phiTwo := by
  obtain ⟨h2, h1, h0⟩ := coeff_identities data
  obtain ⟨p0, p1, p2, p3, pge⟩ := phiTwo_coeff
  obtain ⟨e2, e1, e0⟩ := qExpand_evalAtJ_phiTwoC
  obtain ⟨d0, d1, d2⟩ := natDegree_phiTwoC
  have hdeg3 : data.Φ.natDegree = 3 := by
    rw [data.natDegree_eq, dedekindPsi, Nat.prime_two.divisors, Finset.filter_insert, if_pos squarefree_one,
      Finset.filter_singleton, if_pos Nat.prime_two.squarefree, Finset.sum_insert (by simp), Finset.sum_singleton]

  have cA := fun n (hn : (n - (-4 : ℤ)).toNat < 7) => nf_qExpand_four_jq.coeff n hn
  have cB := fun n (hn : (n - (-1 : ℤ)).toNat < 7) => nf_jq.coeff n hn
  have cC := fun n (hn : (n - (-1 : ℤ)).toNat < 7) => nf_qTwist_neg_one_jq.coeff n hn
  have cAB := fun n (hn : (n - (-5 : ℤ)).toNat < 7) => nf_AB.coeff n hn
  have cAC := fun n (hn : (n - (-5 : ℤ)).toNat < 7) => nf_ACm.coeff n hn
  have cBC := fun n (hn : (n - (-2 : ℤ)).toNat < 7) => nf_BCm.coeff n hn
  have cABC := fun n (hn : (n - (-6 : ℤ)).toNat < 7) => nf_ABCm.coeff n hn
  have cJ2 := fun n (hn : (n - (-2 : ℤ)).toNat < 7) => nf_qExpand_two_jq.coeff n hn
  have cJ22 := fun n (hn : (n - (-4 : ℤ)).toNat < 7) => nf_J22.coeff n hn
  have cJ23 := fun n (hn : (n - (-6 : ℤ)).toNat < 7) => nf_J23.coeff n hn
  have cA_6 := cA (-6) (by decide)
  have cA_4 := cA (-4) (by decide)
  have cA_2 := cA (-2) (by decide)
  have cA_0 := cA 0 (by decide)
  have cB_6 := cB (-6) (by decide)
  have cB_4 := cB (-4) (by decide)
  have cB_2 := cB (-2) (by decide)
  have cB_0 := cB 0 (by decide)
  have cC_6 := cC (-6) (by decide)
  have cC_4 := cC (-4) (by decide)
  have cC_2 := cC (-2) (by decide)
  have cC_0 := cC 0 (by decide)
  have cAB_6 := cAB (-6) (by decide)
  have cAB_4 := cAB (-4) (by decide)
  have cAB_2 := cAB (-2) (by decide)
  have cAB_0 := cAB 0 (by decide)
  have cAC_6 := cAC (-6) (by decide)
  have cAC_4 := cAC (-4) (by decide)
  have cAC_2 := cAC (-2) (by decide)
  have cAC_0 := cAC 0 (by decide)
  have cBC_6 := cBC (-6) (by decide)
  have cBC_4 := cBC (-4) (by decide)
  have cBC_2 := cBC (-2) (by decide)
  have cBC_0 := cBC 0 (by decide)
  have cABC_6 := cABC (-6) (by decide)
  have cABC_4 := cABC (-4) (by decide)
  have cABC_2 := cABC (-2) (by decide)
  have cABC_0 := cABC 0 (by decide)
  have cJ2_6 := cJ2 (-6) (by decide)
  have cJ2_4 := cJ2 (-4) (by decide)
  have cJ2_2 := cJ2 (-2) (by decide)
  have cJ2_0 := cJ2 0 (by decide)
  have cJ22_6 := cJ22 (-6) (by decide)
  have cJ22_4 := cJ22 (-4) (by decide)
  have cJ22_2 := cJ22 (-2) (by decide)
  have cJ22_0 := cJ22 0 (by decide)
  have cJ23_6 := cJ23 (-6) (by decide)
  have cJ23_4 := cJ23 (-4) (by decide)
  have cJ23_2 := cJ23 (-2) (by decide)
  have cJ23_0 := cJ23 0 (by decide)
  apply Polynomial.ext
  intro k
  rcases Nat.lt_or_ge k 3 with hk | hk
  ·
    rw [← sub_eq_zero]
    apply ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero _ 3
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (ModularPolynomialData.natDegree_coeff_le 2 data k).trans (by norm_num)
      · interval_cases k
        · rw [p0]; exact d0
        · rw [p1]; exact d1
        · rw [p2]; exact d2
    · intro m hm1 hm2
      rw [map_sub, HahnSeries.coeff_sub, coeff_eq_coeff_qExpand_two, coeff_eq_coeff_qExpand_two (evalAtJ _), sub_eq_zero]
      have hm1' : -3 ≤ m := by omega
      interval_cases k
      · rw [p0, h0, e0]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C',
            cA_6, cA_4, cA_2, cA_0, cB_6, cB_4, cB_2, cB_0, cC_6, cC_4, cC_2, cC_0, cAB_6, cAB_4, cAB_2, cAB_0, cAC_6, cAC_4, cAC_2, cAC_0, cBC_6, cBC_4, cBC_2, cBC_0, cABC_6, cABC_4, cABC_2, cABC_0, cJ2_6, cJ2_4, cJ2_2, cJ2_0, cJ22_6, cJ22_4, cJ22_2, cJ22_0, cJ23_6, cJ23_4, cJ23_2, cJ23_0]
          norm_num [LA, LJ, LC, L2, Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
      · rw [p1, h1, e1]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C',
            cA_6, cA_4, cA_2, cA_0, cB_6, cB_4, cB_2, cB_0, cC_6, cC_4, cC_2, cC_0, cAB_6, cAB_4, cAB_2, cAB_0, cAC_6, cAC_4, cAC_2, cAC_0, cBC_6, cBC_4, cBC_2, cBC_0, cABC_6, cABC_4, cABC_2, cABC_0, cJ2_6, cJ2_4, cJ2_2, cJ2_0, cJ22_6, cJ22_4, cJ22_2, cJ22_0, cJ23_6, cJ23_4, cJ23_2, cJ23_0]
          norm_num [LA, LJ, LC, L2, Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
      · rw [p2, h2, e2]
        interval_cases m <;>
        · simp only [Int.reduceMul, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Int.reduceToNat, Int.reduceLE,
            HahnSeries.coeff_neg, HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_C_mul', coeff_C',
            cA_6, cA_4, cA_2, cA_0, cB_6, cB_4, cB_2, cB_0, cC_6, cC_4, cC_2, cC_0, cAB_6, cAB_4, cAB_2, cAB_0, cAC_6, cAC_4, cAC_2, cAC_0, cBC_6, cBC_4, cBC_2, cBC_0, cABC_6, cABC_4, cABC_2, cABC_0, cJ2_6, cJ2_4, cJ2_2, cJ2_0, cJ22_6, cJ22_4, cJ22_2, cJ22_0, cJ23_6, cJ23_4, cJ23_2, cJ23_0]
          norm_num [LA, LJ, LC, L2, Int.reduceToNat, Int.reduceSub, Int.reduceNeg]
  ·
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · have : k = 3 := by omega
      subst this
      rw [p3]
      have := data.monic
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg3] at this
      exact this
    · rw [pge k hk4, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg3]; omega)]

end PhiTwoCalc
end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.ModularCurve Polynomial"

theorem solution (data : ModularPolynomialData 2) : data.Φ = phiTwo :=
  ModularCurve.PhiTwoCalc.ModularPolynomialData.phi_eq_phiTwo' data

end S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo (solution)
