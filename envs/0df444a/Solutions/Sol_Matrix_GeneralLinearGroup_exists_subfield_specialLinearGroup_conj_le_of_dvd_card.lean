-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/53d2d7d7-08ae-56f0-a4e9-90bf2e6db5d3

import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card

set_option autoImplicit false

open Matrix MatrixGroups

namespace P2mDicksonGL2

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

lemma funext_fin_two {α : Type} {f g : Fin 2 → α} (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    f = g := by
  funext i; fin_cases i
  · exact h0
  · exact h1

lemma mulVec_e0 (M : 𝕄) : M *ᵥ ![1, 0] = ![M 0 0, M 1 0] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma mulVec_e1 (M : 𝕄) : M *ᵥ ![0, 1] = ![M 0 1, M 1 1] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma mulVec_fin_two (M : 𝕄) (x y : K) :
    M *ᵥ ![x, y] = ![M 0 0 * x + M 0 1 * y, M 1 0 * x + M 1 1 * y] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma sq_sub_one_apply (M : 𝕄) :
    ((M - 1) ^ 2 : 𝕄) 0 0 = (M 0 0 - 1) * (M 0 0 - 1) + M 0 1 * M 1 0 ∧
    ((M - 1) ^ 2 : 𝕄) 0 1 = (M 0 0 - 1) * M 0 1 + M 0 1 * (M 1 1 - 1) ∧
    ((M - 1) ^ 2 : 𝕄) 1 0 = M 1 0 * (M 0 0 - 1) + (M 1 1 - 1) * M 1 0 ∧
    ((M - 1) ^ 2 : 𝕄) 1 1 = M 1 0 * M 0 1 + (M 1 1 - 1) * (M 1 1 - 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.sub_apply]

lemma trace_of_unip {M : 𝕄} (h : (M - 1) ^ 2 = 0) : M 0 0 + M 1 1 = 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := sq_sub_one_apply M
  rw [h] at h00 h01 h10 h11
  simp only [Matrix.zero_apply] at h00 h01 h10 h11
  by_cases htr : M 0 0 + M 1 1 - 2 = 0
  · linear_combination htr
  · have h01' : M 0 1 * (M 0 0 + M 1 1 - 2) = 0 := by linear_combination -h01
    have h10' : M 1 0 * (M 0 0 + M 1 1 - 2) = 0 := by linear_combination -h10
    have e01 : M 0 1 = 0 := (mul_eq_zero.mp h01').resolve_right htr
    have e10 : M 1 0 = 0 := (mul_eq_zero.mp h10').resolve_right htr
    rw [e01, zero_mul, add_zero] at h00
    rw [e01, mul_zero, zero_add] at h11
    have e00 : M 0 0 = 1 := by
      have := mul_self_eq_zero.mp h00.symm
      linear_combination this
    have e11 : M 1 1 = 1 := by
      have := mul_self_eq_zero.mp h11.symm
      linear_combination this
    rw [e00, e11]; norm_num

lemma exists_fixed_vec {M : 𝕄} (h : (M - 1) ^ 2 = 0) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ M *ᵥ v = v := by
  have hdet : Matrix.det (M - 1) = 0 := by
    have h2 : Matrix.det (M - 1) ^ 2 = 0 := by
      rw [← Matrix.det_pow, h, Matrix.det_zero]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine ⟨v, hv, ?_⟩
  have h1 : (M - 1) *ᵥ v = M *ᵥ v - (1 : 𝕄) *ᵥ v := Matrix.sub_mulVec M 1 v
  rw [Matrix.one_mulVec, hMv] at h1
  exact sub_eq_zero.mp h1.symm

lemma eq_one_of_fixes_two {M : 𝕄} {v w : Fin 2 → K}
    (hv : M *ᵥ v = v) (hw : M *ᵥ w = w) (hD : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    M = 1 := by
  set D := v 0 * w 1 - v 1 * w 0 with hDdef
  have hcancel : ∀ x y : Fin 2 → K, D • x = D • y → x = y := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hD hi
  have hfix : ∀ x y : K, M *ᵥ (x • v + y • w) = x • v + y • w := by
    intro x y
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw]
  have he0 : (w 1 : K) • v + (-(v 1)) • w = D • ![1, 0] := by
    funext i; fin_cases i <;> simp [hDdef] <;> ring
  have he1 : (-(w 0) : K) • v + (v 0) • w = D • ![0, 1] := by
    funext i; fin_cases i <;> simp [hDdef] <;> ring
  have h0 : D • M *ᵥ ![1, 0] = D • ![1, 0] := by
    rw [← Matrix.mulVec_smul, ← he0, hfix]
  have h1 : D • M *ᵥ ![0, 1] = D • ![0, 1] := by
    rw [← Matrix.mulVec_smul, ← he1, hfix]
  have h0' := hcancel _ _ h0
  have h1' := hcancel _ _ h1
  rw [mulVec_e0] at h0'
  rw [mulVec_e1] at h1'
  have e00 : M 0 0 = 1 := by simpa using congrFun h0' 0
  have e10 : M 1 0 = 0 := by simpa using congrFun h0' 1
  have e01 : M 0 1 = 0 := by simpa using congrFun h1' 0
  have e11 : M 1 1 = 1 := by simpa using congrFun h1' 1
  rw [Matrix.eta_fin_two M, e00, e10, e01, e11, ← Matrix.one_fin_two]

lemma exists_smul_eq_of_cross_eq_zero {v w : Fin 2 → K} (hv : v ≠ 0)
    (hD : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : K, w = c • v := by
  have hkey : v 0 * w 1 = v 1 * w 0 := sub_eq_zero.mp hD
  rcases eq_or_ne (v 0) 0 with h0 | h0
  · have hv1 : v 1 ≠ 0 := by
      intro h1; exact hv (funext_fin_two (by simpa using h0) (by simpa using h1))
    have hw0 : w 0 = 0 := by
      have hmul : v 1 * w 0 = 0 := by rw [← hkey, h0, zero_mul]
      exact (mul_eq_zero.mp hmul).resolve_left hv1
    refine ⟨w 1 / v 1, funext_fin_two ?_ ?_⟩
    · simp [hw0, h0]
    · simp [div_mul_cancel₀ _ hv1]
  · refine ⟨w 0 / v 0, funext_fin_two ?_ ?_⟩
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hkey

lemma coeffs_eq_zero_of_cross_ne_zero {v w : Fin 2 → K} {x y : K}
    (h : x • v + y • w = 0) (hD : v 0 * w 1 - v 1 * w 0 ≠ 0) : x = 0 ∧ y = 0 := by
  have h0 : x * v 0 + y * w 0 = 0 := by simpa using congrFun h 0
  have h1 : x * v 1 + y * w 1 = 0 := by simpa using congrFun h 1
  constructor
  · have : x * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination w 1 * h0 - w 0 * h1
    exact (mul_eq_zero.mp this).resolve_right hD
  · have : y * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * h1 - v 1 * h0
    exact (mul_eq_zero.mp this).resolve_right hD

lemma eq_upper_of_fixes_e0 {Q : 𝕄} (hQ : (Q - 1) ^ 2 = 0)
    (hfix : Q *ᵥ ![1, 0] = ![1, 0]) : Q = !![1, Q 0 1; 0, 1] := by
  rw [mulVec_e0] at hfix
  have e00 : Q 0 0 = 1 := by simpa using congrFun hfix 0
  have e10 : Q 1 0 = 0 := by simpa using congrFun hfix 1
  have e11 : Q 1 1 = 1 := by
    have := trace_of_unip hQ
    rw [e00] at this
    linear_combination this
  conv_lhs => rw [Matrix.eta_fin_two Q]
  rw [e00, e10, e11]

lemma eq_lower_of_fixes_e1 {Q : 𝕄} (hQ : (Q - 1) ^ 2 = 0)
    (hfix : Q *ᵥ ![0, 1] = ![0, 1]) : Q = !![1, 0; Q 1 0, 1] := by
  rw [mulVec_e1] at hfix
  have e01 : Q 0 1 = 0 := by simpa using congrFun hfix 0
  have e11 : Q 1 1 = 1 := by simpa using congrFun hfix 1
  have e00 : Q 0 0 = 1 := by
    have := trace_of_unip hQ
    rw [e11] at this
    linear_combination this
  conv_lhs => rw [Matrix.eta_fin_two Q]
  rw [e00, e01, e11]

lemma sq_eq_zero_of_pow_eq_zero {N : 𝕄} {m : ℕ} (hm : N ^ m = 0) : N ^ 2 = 0 := by

  have hCH : N ^ 2 = (N 0 0 + N 1 1) • N - N.det • (1 : 𝕄) := by
    rw [Matrix.det_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact one_ne_zero hm
  have hdet : N.det = 0 := by
    have : N.det ^ m = 0 := by rw [← Matrix.det_pow, hm, Matrix.det_zero]
    exact pow_eq_zero_iff hm0 |>.mp this
  rw [hdet, zero_smul, sub_zero] at hCH

  set t := N 0 0 + N 1 1 with ht
  have hpow : ∀ k : ℕ, N ^ (k + 1) = t ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, smul_mul_assoc, ← pow_two, hCH, smul_smul, ← pow_succ]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  rw [hpow k] at hm
  rcases smul_eq_zero.mp hm with htk | hN
  · have ht0 : t = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at htk
      · exact pow_eq_zero_iff hk.ne' |>.mp htk
    rw [hCH, ht0, zero_smul]
  · rw [hN, pow_two, mul_zero]

open ModularCurve

section SL2

def diagElem (a : K) (ha : a ≠ 0) : SL(2, K) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

@[scoped simp] lemma diagElem_coe (a : K) (ha : a ≠ 0) :
    (diagElem a ha : 𝕄) = !![a, 0; 0, a⁻¹] := rfl

lemma diagElem_eq_word (a : K) (ha : a ≠ 0) :
    diagElem a ha = upperElem a * lowerElem (-a⁻¹) * upperElem a *
      (upperElem (1 : K) * lowerElem (-1) * upperElem 1)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha]

lemma upper_diag_upper_diag (x a : K) (ha : a ≠ 0) :
    upperElem x * diagElem a ha * upperElem (-x) * diagElem a⁻¹ (inv_ne_zero ha) =
      upperElem (x * (1 - a ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, ha]; try (field_simp; ring))

lemma eq_upper_lower_upper (s : SL(2, K)) (hc : (s : 𝕄) 1 0 ≠ 0) :
    s = upperElem (((s : 𝕄) 0 0 - 1) / (s : 𝕄) 1 0) * lowerElem ((s : 𝕄) 1 0) *
      upperElem (((s : 𝕄) 1 1 - 1) / (s : 𝕄) 1 0) := by
  have hdet : (s : 𝕄) 0 0 * (s : 𝕄) 1 1 - (s : 𝕄) 0 1 * (s : 𝕄) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact s.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  · ring
  · linear_combination (-1 : K) * hdet
  · ring

lemma lowerElem_one_mul_apply_one_zero (s : SL(2, K)) :
    ((lowerElem (1 : K) * s : SL(2, K)) : 𝕄) 1 0 = (s : 𝕄) 0 0 + (s : 𝕄) 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma map_mem_of_elem_mem (G : Subgroup SL(2, K)) (F : Subfield K)
    (hU : ∀ t : K, t ∈ F → upperElem t ∈ G) (hL : ∀ t : K, t ∈ F → lowerElem t ∈ G)
    (s : SL(2, F)) : Matrix.SpecialLinearGroup.map F.subtype s ∈ G := by

  have key : ∀ r : SL(2, K), (∀ i j, (r : 𝕄) i j ∈ F) → (r : 𝕄) 1 0 ≠ 0 → r ∈ G := by
    intro r hr hc
    rw [eq_upper_lower_upper r hc]
    refine mul_mem (mul_mem (hU _ ?_) (hL _ (hr 1 0))) (hU _ ?_)
    · exact F.div_mem (F.sub_mem (hr 0 0) F.one_mem) (hr 1 0)
    · exact F.div_mem (F.sub_mem (hr 1 1) F.one_mem) (hr 1 0)
  set r : SL(2, K) := Matrix.SpecialLinearGroup.map F.subtype s with hr
  have hrF : ∀ i j, (r : 𝕄) i j ∈ F := by
    intro i j
    simp [hr]
  by_cases hc : (r : 𝕄) 1 0 = 0
  ·
    have hdet : (r : 𝕄) 0 0 * (r : 𝕄) 1 1 - (r : 𝕄) 0 1 * (r : 𝕄) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact r.2
    have ha : (r : 𝕄) 0 0 ≠ 0 := by
      intro h0
      rw [h0, hc] at hdet
      simp at hdet
    have hmem : lowerElem (1 : K) * r ∈ G := by
      refine key _ ?_ ?_
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first
          | exact hrF 0 0
          | exact hrF 0 1
          | exact F.add_mem (hrF 0 0) (hrF 1 0)
          | exact F.add_mem (hrF 0 1) (hrF 1 1)
      · rw [lowerElem_one_mul_apply_one_zero, hc, add_zero]
        exact ha
    have h1 : lowerElem (1 : K) ∈ G := hL 1 F.one_mem
    have : r = (lowerElem (1 : K))⁻¹ * (lowerElem (1 : K) * r) := by group
    rw [this]
    exact mul_mem (inv_mem h1) hmem
  · exact key r hrF hc

end SL2

section RationalLines

lemma upperElem_inv (x : K) : (upperElem x)⁻¹ = upperElem (-x) := by
  rw [inv_eq_iff_mul_eq_one, upperElem_mul, add_neg_cancel, upperElem_zero]

lemma upperElem_conj_upperElem (x t : K) :
    upperElem x * upperElem t * (upperElem x)⁻¹ = upperElem t := by
  rw [upperElem_inv, upperElem_mul, upperElem_mul]
  congr 1; ring

lemma upperElem_mulVec (t y z : K) : (upperElem t : 𝕄) *ᵥ ![y, z] = ![y + t * z, z] := by
  rw [upperElem_coe]
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma conj_unip {M P Q : 𝕄} (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : (M - 1) ^ 2 = 0) :
    (P * M * Q - 1) ^ 2 = 0 := by
  have key : P * M * Q - 1 = P * (M - 1) * Q := by
    rw [mul_sub, sub_mul, mul_one, hPQ]
  have hsq : (P * (M - 1) * Q) ^ 2 = P * ((M - 1) * (Q * P) * (M - 1)) * Q := by
    rw [pow_two]; noncomm_ring
  rw [key, hsq, hQP, mul_one, ← pow_two, h, mul_zero, zero_mul]

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_rational_fixed_vec (hp2 : p ≠ 2) (G : Subgroup SL(2, K)) [Finite G]
    (F : Subfield K)
    (hΛ : ∀ t : K, upperElem t ∈ G ↔ t ∈ F) (hΛ' : ∀ t : K, lowerElem t ∈ G ↔ t ∈ F)
    {a : K} (haF : a ∈ F) (ha3 : a ^ 3 ≠ a)
    {u : SL(2, K)} (huG : u ∈ G) (hunip : ((u : 𝕄) - 1) ^ 2 = 0) (hu1 : u ≠ 1) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ (u : 𝕄) *ᵥ (fun i => (v i : K)) = fun i => (v i : K) := by
  obtain ⟨v₀, hv₀, hfix⟩ := exists_fixed_vec hunip
  have hfix0 : (u : 𝕄) 0 0 * v₀ 0 + (u : 𝕄) 0 1 * v₀ 1 = v₀ 0 := by
    have := congrFun hfix 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hfix1 : (u : 𝕄) 1 0 * v₀ 0 + (u : 𝕄) 1 1 * v₀ 1 = v₀ 1 := by
    have := congrFun hfix 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_cases h1 : v₀ 1 = 0
  ·
    have hv00 : v₀ 0 ≠ 0 := fun h0 =>
      hv₀ (funext_fin_two (by simpa using h0) (by simpa using h1))
    rw [h1, mul_zero, add_zero] at hfix0 hfix1
    have e00 : (u : 𝕄) 0 0 = 1 := by
      have : ((u : 𝕄) 0 0 - 1) * v₀ 0 = 0 := by linear_combination hfix0
      have := (mul_eq_zero.mp this).resolve_right hv00
      linear_combination this
    have e10 : (u : 𝕄) 1 0 = 0 := (mul_eq_zero.mp hfix1).resolve_right hv00
    refine ⟨![1, 0], ?_, ?_⟩
    · intro h; simpa using congrFun h 0
    · have hcoe : (fun i => (((![1, 0] : Fin 2 → F) i : F) : K)) = ![1, 0] :=
        funext_fin_two (by simp) (by simp)
      rw [hcoe, mulVec_e0, e00, e10]
  ·
    set x : K := v₀ 0 / v₀ 1 with hx
    have hux : (u : 𝕄) *ᵥ ![x, 1] = ![x, 1] := by
      rw [mulVec_fin_two]
      refine funext_fin_two ?_ ?_
      · simp only [Matrix.cons_val_zero]
        rw [hx]; field_simp; linear_combination hfix0
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hx]; field_simp; linear_combination hfix1

    set G' : Subgroup SL(2, K) := G.comap (MulAut.conj (upperElem x)).toMonoidHom with hG'
    have memG' : ∀ s : SL(2, K), s ∈ G' ↔ upperElem x * s * (upperElem x)⁻¹ ∈ G := by
      intro s; rfl
    haveI : Finite G' := by
      rw [hG', Subgroup.comap_equiv_eq_map_symm']
      exact Set.Finite.to_subtype ((Set.toFinite (G : Set SL(2, K))).image _)
    have hupG' : ∀ t : K, upperElem t ∈ G' ↔ t ∈ F := by
      intro t; rw [memG', upperElem_conj_upperElem, hΛ]

    set u' : SL(2, K) := (upperElem x)⁻¹ * u * upperElem x with hu'
    have hu'G' : u' ∈ G' := by
      rw [memG', hu']
      have : upperElem x * ((upperElem x)⁻¹ * u * upperElem x) * (upperElem x)⁻¹ = u := by
        group
      rw [this]; exact huG
    have hUU : ((upperElem x : SL(2, K)) : 𝕄) * ((upperElem x)⁻¹ : SL(2, K)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    have hUU' : (((upperElem x)⁻¹ : SL(2, K)) : 𝕄) * (upperElem x : SL(2, K)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    have hu'unip : ((u' : 𝕄) - 1) ^ 2 = 0 := by
      rw [hu', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact conj_unip hUU' hUU hunip
    have hu'fix : (u' : 𝕄) *ᵥ ![0, 1] = ![0, 1] := by
      rw [hu', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, upperElem_mulVec, upperElem_inv,
        mul_one, zero_add, hux, upperElem_mulVec]
      refine funext_fin_two ?_ ?_ <;> simp
    have hu'form := eq_lower_of_fixes_e1 hu'unip hu'fix
    set m : K := (u' : 𝕄) 1 0 with hm
    have hu'eq : u' = lowerElem m := Subtype.ext hu'form
    have hm0 : m ≠ 0 := by
      intro hm0
      apply hu1
      have h1 : u' = 1 := by rw [hu'eq, hm0, lowerElem_zero]
      calc u = upperElem x * u' * (upperElem x)⁻¹ := by rw [hu']; group
        _ = 1 := by rw [h1]; group

    rcases Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite hp2 G'
        ((hupG' 1).mpr F.one_mem) ⟨m, hm0, hu'eq ▸ hu'G'⟩ with ⟨-, hsmall⟩ | ⟨F', -, hΛ₁, hΛ₁'⟩
    · exact absurd (hsmall a ((hupG' a).mpr haF)) ha3
    · have hFF' : ∀ t : K, t ∈ F' ↔ t ∈ F := fun t => by rw [← hΛ₁ t, hupG']
      have hlowG' : ∀ t : K, t ∈ F → lowerElem t ∈ G' := fun t ht =>
        (hΛ₁' t).mpr ((hFF' t).mpr ht)
      have ha0 : a ≠ 0 := by rintro rfl; exact ha3 (by ring)
      have ha2 : 1 - a ^ 2 ≠ 0 := by
        intro h; apply ha3; linear_combination (-a) * h

      have hdG' : diagElem a ha0 ∈ G' := by
        rw [diagElem_eq_word]
        refine mul_mem (mul_mem (mul_mem ((hupG' _).mpr haF) (hlowG' _ ?_))
          ((hupG' _).mpr haF)) (inv_mem (mul_mem (mul_mem ((hupG' _).mpr F.one_mem)
          (hlowG' _ (F.neg_mem F.one_mem))) ((hupG' _).mpr F.one_mem)))
        exact F.neg_mem (F.inv_mem haF)
      have hdG : diagElem a⁻¹ (inv_ne_zero ha0) ∈ G := by
        rw [diagElem_eq_word]
        refine mul_mem (mul_mem (mul_mem ((hΛ _).mpr (F.inv_mem haF)) ((hΛ' _).mpr ?_))
          ((hΛ _).mpr (F.inv_mem haF))) (inv_mem (mul_mem (mul_mem ((hΛ _).mpr F.one_mem)
          ((hΛ' _).mpr (F.neg_mem F.one_mem))) ((hΛ _).mpr F.one_mem)))
        rw [inv_inv]; exact F.neg_mem haF
      have hkey : upperElem (x * (1 - a ^ 2)) ∈ G := by
        rw [← upper_diag_upper_diag x a ha0, ← upperElem_inv]
        exact mul_mem ((memG' _).mp hdG') hdG
      have hxF : x ∈ F := by
        have h := (hΛ _).mp hkey
        have : x = x * (1 - a ^ 2) / (1 - a ^ 2) := by field_simp
        rw [this]
        exact F.div_mem h (F.sub_mem F.one_mem (F.pow_mem haF 2))
      refine ⟨![⟨x, hxF⟩, 1], ?_, ?_⟩
      · intro h; simpa using congrFun h 1
      · have hcoe : (fun i => (((![⟨x, hxF⟩, 1] : Fin 2 → F) i : F) : K)) = ![x, 1] :=
          funext_fin_two (by simp) (by simp)
        rw [hcoe, hux]

end RationalLines

section Rational

theorem exists_smul_map_of_rational_lines (F : Subfield K) (h : 𝕄) (hdet : h.det ≠ 0)
    (v₁ v₂ v₃ : Fin 2 → F)
    (c₁ c₂ c₃ : K)
    (h₁ : h *ᵥ ![1, 0] = c₁ • fun i => (v₁ i : K))
    (h₂ : h *ᵥ ![0, 1] = c₂ • fun i => (v₂ i : K))
    (h₃ : h *ᵥ ![1, 1] = c₃ • fun i => (v₃ i : K)) :
    ∃ (a : K) (m : GL (Fin 2) F),
      h = a • ((Matrix.GeneralLinearGroup.map F.subtype m : GL (Fin 2) K) : 𝕄) := by

  rw [mulVec_e0] at h₁
  rw [mulVec_e1] at h₂
  rw [mulVec_fin_two] at h₃
  simp only [mul_one] at h₃
  have e00 : h 0 0 = c₁ * v₁ 0 := by simpa using congrFun h₁ 0
  have e10 : h 1 0 = c₁ * v₁ 1 := by simpa using congrFun h₁ 1
  have e01 : h 0 1 = c₂ * v₂ 0 := by simpa using congrFun h₂ 0
  have e11 : h 1 1 = c₂ * v₂ 1 := by simpa using congrFun h₂ 1
  have s0 : h 0 0 + h 0 1 = c₃ * v₃ 0 := by simpa using congrFun h₃ 0
  have s1 : h 1 0 + h 1 1 = c₃ * v₃ 1 := by simpa using congrFun h₃ 1

  set δ : F := v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 with hδ
  have hdet' : h.det = c₁ * c₂ * (δ : K) := by
    rw [Matrix.det_fin_two, e00, e10, e01, e11, hδ]; push_cast; ring
  have hc₁ : c₁ ≠ 0 := by intro hc; apply hdet; rw [hdet', hc]; ring
  have hc₂ : c₂ ≠ 0 := by intro hc; apply hdet; rw [hdet', hc]; ring
  have hδ0 : δ ≠ 0 := by
    intro hδ0; apply hdet; rw [hdet', hδ0]; simp
  have hδK : (δ : K) ≠ 0 := fun hh => hδ0 (by exact_mod_cast hh)

  set α : F := (v₃ 0 * v₂ 1 - v₃ 1 * v₂ 0) / δ with hα
  set β : F := (v₁ 0 * v₃ 1 - v₁ 1 * v₃ 0) / δ with hβ
  have hδK' : ((v₁ 0 : F) : K) * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0 := by
    have : ((v₁ 0 : F) : K) * v₂ 1 - v₁ 1 * v₂ 0 = (δ : K) := by rw [hδ]; push_cast; ring
    rw [this]; exact hδK
  have hαK : (α : K) = ((v₃ 0 : K) * v₂ 1 - v₃ 1 * v₂ 0) / (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0) := by
    rw [hα, hδ]; push_cast; ring
  have hβK : (β : K) = ((v₁ 0 : K) * v₃ 1 - v₁ 1 * v₃ 0) / (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0) := by
    rw [hβ, hδ]; push_cast; ring
  have hv30 : (v₃ 0 : K) = α * v₁ 0 + β * v₂ 0 := by
    rw [hαK, hβK, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hδK']
    ring
  have hv31 : (v₃ 1 : K) = α * v₁ 1 + β * v₂ 1 := by
    rw [hαK, hβK, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hδK']
    ring

  have hlin : (c₁ - c₃ * α) • (fun i => (v₁ i : K)) + (c₂ - c₃ * β) • (fun i => (v₂ i : K))
      = 0 := by
    refine funext_fin_two ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination s0 - e00 - e01 + c₃ * hv30
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination s1 - e10 - e11 + c₃ * hv31
  have hcross : (fun i => (v₁ i : K)) 0 * (fun i => (v₂ i : K)) 1 -
      (fun i => (v₁ i : K)) 1 * (fun i => (v₂ i : K)) 0 ≠ 0 := by
    simp only
    have : ((v₁ 0 : F) : K) * v₂ 1 - v₁ 1 * v₂ 0 = (δ : K) := by rw [hδ]; push_cast; ring
    rw [this]; exact hδK
  obtain ⟨hα', hβ'⟩ := coeffs_eq_zero_of_cross_ne_zero hlin hcross
  have hc₁' : c₁ = c₃ * α := by linear_combination hα'
  have hc₂' : c₂ = c₃ * β := by linear_combination hβ'
  have hα0 : α ≠ 0 := by
    intro h0; apply hc₁; rw [hc₁', h0]; simp
  have hβ0 : β ≠ 0 := by
    intro h0; apply hc₂; rw [hc₂', h0]; simp

  have hmdet : (!![α * v₁ 0, β * v₂ 0; α * v₁ 1, β * v₂ 1] : Matrix (Fin 2) (Fin 2) F).det
      ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have : α * v₁ 0 * (β * v₂ 1) - β * v₂ 0 * (α * v₁ 1) = α * β * δ := by rw [hδ]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hα0 hβ0) hδ0
  refine ⟨c₃, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hmdet, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.map,
      RingHom.mapMatrix_apply, e00, e01, e10, e11, hc₁', hc₂'] <;> ring

end Rational

section Setup

variable {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "GL₂" => GL (Fin 2) K

def diagGL (a : K) (ha : a ≠ 0) : GL₂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, 1] (by simp [Matrix.det_fin_two_of, ha])

lemma toGL_upperElem_mul_diagGL (a : K) (ha : a ≠ 0) (t : K) :
    Matrix.SpecialLinearGroup.toGL (upperElem t) * diagGL a ha =
      diagGL a ha * Matrix.SpecialLinearGroup.toGL (upperElem (a⁻¹ * t)) := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, upperElem_coe, diagGL,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]

lemma toGL_lowerElem_mul_diagGL (a : K) (ha : a ≠ 0) (t : K) :
    Matrix.SpecialLinearGroup.toGL (lowerElem t) * diagGL a ha =
      diagGL a ha * Matrix.SpecialLinearGroup.toGL (lowerElem (a * t)) := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, lowerElem_coe, diagGL,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma diagGL_conj_upperElem (a : K) (ha : a ≠ 0) (s : K) :
    diagGL a ha * Matrix.SpecialLinearGroup.toGL (upperElem s) * (diagGL a ha)⁻¹ =
      Matrix.SpecialLinearGroup.toGL (upperElem (a * s)) := by
  rw [mul_inv_eq_iff_eq_mul, toGL_upperElem_mul_diagGL, inv_mul_cancel_left₀ ha]

lemma diagGL_conj_lowerElem (a : K) (ha : a ≠ 0) (s : K) :
    diagGL a ha * Matrix.SpecialLinearGroup.toGL (lowerElem s) * (diagGL a ha)⁻¹ =
      Matrix.SpecialLinearGroup.toGL (lowerElem (a⁻¹ * s)) := by
  rw [mul_inv_eq_iff_eq_mul, toGL_lowerElem_mul_diagGL, mul_inv_cancel_left₀ ha]

lemma diagGL_inv_conj_upperElem (a : K) (ha : a ≠ 0) (t : K) :
    (diagGL a ha)⁻¹ * Matrix.SpecialLinearGroup.toGL (upperElem t) * diagGL a ha =
      Matrix.SpecialLinearGroup.toGL (upperElem (a⁻¹ * t)) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul, toGL_upperElem_mul_diagGL]

lemma unip_of_pow_prime_pow_eq_one {x : GL₂} {k : ℕ} (hx : x ^ p ^ k = 1) :
    ((x : 𝕄) - 1) ^ 2 = 0 := by
  have hM : (x : 𝕄) ^ p ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hN : ((x : 𝕄) - 1) ^ p ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right (x : 𝕄)), hM, one_pow, sub_self]
  exact sq_eq_zero_of_pow_eq_zero hN

theorem exists_conj_standard (H : Subgroup GL₂)
    (P : Subgroup GL₂) (hPH : P ≤ H) {k : ℕ} (hcard : Nat.card P = p ^ k)
    (hP1 : ∃ x ∈ P, x ≠ 1)
    (hirr : ∀ v : Fin 2 → K, v ≠ 0 → ∃ h ∈ H, ((h : GL₂) : 𝕄) *ᵥ v ∉ K ∙ v) :
    ∃ (g : GL₂) (μ : K), μ ≠ 0 ∧
      g * Matrix.SpecialLinearGroup.toGL (upperElem (1 : K)) * g⁻¹ ∈ H ∧
      g * Matrix.SpecialLinearGroup.toGL (lowerElem μ) * g⁻¹ ∈ H ∧
      ∀ x ∈ P, ∃ t : K, g⁻¹ * x * g = Matrix.SpecialLinearGroup.toGL (upperElem t) := by
  classical

  haveI : Finite P :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hunip : ∀ x ∈ P, ((x : 𝕄) - 1) ^ 2 = 0 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : P) ^ p ^ k = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have h2 : x ^ p ^ k = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    exact unip_of_pow_prime_pow_eq_one h2
  obtain ⟨h₀, hh₀P, hh₀1⟩ := hP1

  obtain ⟨v, hv0, hv⟩ := exists_fixed_vec (hunip h₀ hh₀P)
  obtain ⟨h, hhH, hmove⟩ := hirr v hv0
  set w : Fin 2 → K := ((h : GL₂) : 𝕄) *ᵥ v with hwdef
  have hD : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro hD0
    obtain ⟨c, hc⟩ := exists_smul_eq_of_cross_eq_zero hv0 hD0
    exact hmove (Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩)

  have hdetg₀ : Matrix.det (!![v 0, w 0; v 1, w 1] : 𝕄) ≠ 0 := by
    rw [Matrix.det_fin_two_of]; intro hc; apply hD; linear_combination hc
  set g₀ : GL₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetg₀ with hg₀def
  have hg₀coe : (g₀ : 𝕄) = !![v 0, w 0; v 1, w 1] := rfl
  have hg₀inv : ((g₀⁻¹ : GL₂) : 𝕄) * (g₀ : 𝕄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg₀inv' : (g₀ : 𝕄) * ((g₀⁻¹ : GL₂) : 𝕄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg₀e0 : (g₀ : 𝕄) *ᵥ ![1, 0] = v := by
    rw [hg₀coe, mulVec_e0]; exact funext_fin_two (by simp) (by simp)
  have hg₀e1 : (g₀ : 𝕄) *ᵥ ![0, 1] = w := by
    rw [hg₀coe, mulVec_e1]; exact funext_fin_two (by simp) (by simp)
  have hg₀iv : ((g₀⁻¹ : GL₂) : 𝕄) *ᵥ v = ![1, 0] := by
    rw [← hg₀e0, Matrix.mulVec_mulVec, hg₀inv, Matrix.one_mulVec]
  have hg₀iw : ((g₀⁻¹ : GL₂) : 𝕄) *ᵥ w = ![0, 1] := by
    rw [← hg₀e1, Matrix.mulVec_mulVec, hg₀inv, Matrix.one_mulVec]

  have hconjunip : ∀ y : GL₂, ((y : 𝕄) - 1) ^ 2 = 0 →
      (((g₀⁻¹ * y * g₀ : GL₂) : 𝕄) - 1) ^ 2 = 0 := by
    intro y hy
    rw [Units.val_mul, Units.val_mul]
    exact conj_unip hg₀inv hg₀inv' hy
  have hconjfix : ∀ (y : GL₂) (z : Fin 2 → K), (y : 𝕄) *ᵥ z = z →
      ((g₀⁻¹ * y * g₀ : GL₂) : 𝕄) *ᵥ (((g₀⁻¹ : GL₂) : 𝕄) *ᵥ z) =
        ((g₀⁻¹ : GL₂) : 𝕄) *ᵥ z := by
    intro y z hz
    rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec,
      mul_assoc (((g₀⁻¹ : GL₂) : 𝕄) * (y : 𝕄)), hg₀inv', mul_one,
      ← Matrix.mulVec_mulVec, hz]

  set a : K := ((g₀⁻¹ * h₀ * g₀ : GL₂) : 𝕄) 0 1 with hadef
  have hh₀'fix : ((g₀⁻¹ * h₀ * g₀ : GL₂) : 𝕄) *ᵥ ![1, 0] = ![1, 0] := by
    have := hconjfix h₀ v hv; rwa [hg₀iv] at this
  have hh₀'form : ((g₀⁻¹ * h₀ * g₀ : GL₂) : 𝕄) = !![1, a; 0, 1] :=
    eq_upper_of_fixes_e0 (hconjunip h₀ (hunip h₀ hh₀P)) hh₀'fix
  have hh₀'eq : g₀⁻¹ * h₀ * g₀ = Matrix.SpecialLinearGroup.toGL (upperElem a) :=
    Units.ext hh₀'form
  have ha : a ≠ 0 := by
    intro ha0
    apply hh₀1
    have h1 : g₀⁻¹ * h₀ * g₀ = 1 := by rw [hh₀'eq, ha0, upperElem_zero, map_one]
    calc h₀ = g₀ * (g₀⁻¹ * h₀ * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [h1]; group

  have hPupper : ∀ x ∈ P, ∃ t : K,
      g₀⁻¹ * x * g₀ = Matrix.SpecialLinearGroup.toGL (upperElem t) := by
    intro x hx
    set x' : GL₂ := g₀⁻¹ * x * g₀ with hx'
    have hx'unip : ((x' : 𝕄) - 1) ^ 2 = 0 := hconjunip x (hunip x hx)

    have hprod : (((x' * (g₀⁻¹ * h₀ * g₀) : GL₂) : 𝕄) - 1) ^ 2 = 0 := by
      have : x' * (g₀⁻¹ * h₀ * g₀) = g₀⁻¹ * (x * h₀) * g₀ := by rw [hx']; group
      rw [this]
      exact hconjunip _ (hunip _ (P.mul_mem hx hh₀P))
    rw [Units.val_mul, hh₀'form] at hprod

    have htr := trace_of_unip hx'unip
    have htr' := trace_of_unip hprod
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at htr'
    have e10 : (x' : 𝕄) 1 0 = 0 := by
      have : a * (x' : 𝕄) 1 0 = 0 := by linear_combination htr' - htr
      exact (mul_eq_zero.mp this).resolve_left ha
    obtain ⟨h00, -, -, -⟩ := sq_sub_one_apply (x' : 𝕄)
    rw [hx'unip, Matrix.zero_apply, e10, mul_zero, add_zero] at h00
    have e00 : (x' : 𝕄) 0 0 = 1 := by
      have := mul_self_eq_zero.mp h00.symm; linear_combination this
    have hfix : (x' : 𝕄) *ᵥ ![1, 0] = ![1, 0] := by
      rw [mulVec_e0, e00, e10]
    exact ⟨(x' : 𝕄) 0 1, Units.ext (eq_upper_of_fixes_e0 hx'unip hfix)⟩

  set u₂ : GL₂ := h * h₀ * h⁻¹ with hu₂
  have hu₂H : u₂ ∈ H := H.mul_mem (H.mul_mem hhH (hPH hh₀P)) (H.inv_mem hhH)
  have hu₂unip : ((u₂ : 𝕄) - 1) ^ 2 = 0 := by
    rw [hu₂, Units.val_mul, Units.val_mul]
    refine conj_unip ?_ ?_ (hunip h₀ hh₀P)
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu₂w : (u₂ : 𝕄) *ᵥ w = w := by
    rw [hu₂, hwdef, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ ((h⁻¹ : GL₂) : 𝕄), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec, hv]
  set b : K := ((g₀⁻¹ * u₂ * g₀ : GL₂) : 𝕄) 1 0 with hbdef
  have hu₂'fix : ((g₀⁻¹ * u₂ * g₀ : GL₂) : 𝕄) *ᵥ ![0, 1] = ![0, 1] := by
    have := hconjfix u₂ w hu₂w; rwa [hg₀iw] at this
  have hu₂'form : ((g₀⁻¹ * u₂ * g₀ : GL₂) : 𝕄) = !![1, 0; b, 1] :=
    eq_lower_of_fixes_e1 (hconjunip u₂ hu₂unip) hu₂'fix
  have hu₂'eq : g₀⁻¹ * u₂ * g₀ = Matrix.SpecialLinearGroup.toGL (lowerElem b) :=
    Units.ext hu₂'form
  have hb : b ≠ 0 := by
    intro hb0
    have h1 : g₀⁻¹ * u₂ * g₀ = 1 := by rw [hu₂'eq, hb0, lowerElem_zero, map_one]
    have hu₂1 : u₂ = 1 := by
      calc u₂ = g₀ * (g₀⁻¹ * u₂ * g₀) * g₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    apply hh₀1
    calc h₀ = h⁻¹ * u₂ * h := by rw [hu₂]; group
      _ = 1 := by rw [hu₂1]; group

  refine ⟨g₀ * diagGL a ha, a * b, mul_ne_zero ha hb, ?_, ?_, ?_⟩
  · have key : g₀ * diagGL a ha * Matrix.SpecialLinearGroup.toGL (upperElem (1 : K)) *
        (g₀ * diagGL a ha)⁻¹ = g₀ * (diagGL a ha *
          Matrix.SpecialLinearGroup.toGL (upperElem (1 : K)) * (diagGL a ha)⁻¹) * g₀⁻¹ := by
      group
    rw [key, diagGL_conj_upperElem, mul_one, ← hh₀'eq]
    have : g₀ * (g₀⁻¹ * h₀ * g₀) * g₀⁻¹ = h₀ := by group
    rw [this]; exact hPH hh₀P
  · have key : g₀ * diagGL a ha * Matrix.SpecialLinearGroup.toGL (lowerElem (a * b)) *
        (g₀ * diagGL a ha)⁻¹ = g₀ * (diagGL a ha *
          Matrix.SpecialLinearGroup.toGL (lowerElem (a * b)) * (diagGL a ha)⁻¹) * g₀⁻¹ := by
      group
    rw [key, diagGL_conj_lowerElem, inv_mul_cancel_left₀ ha, ← hu₂'eq]
    have : g₀ * (g₀⁻¹ * u₂ * g₀) * g₀⁻¹ = u₂ := by group
    rw [this]; exact hu₂H
  · intro x hx
    obtain ⟨t, ht⟩ := hPupper x hx
    refine ⟨a⁻¹ * t, ?_⟩
    have key : (g₀ * diagGL a ha)⁻¹ * x * (g₀ * diagGL a ha) =
        (diagGL a ha)⁻¹ * (g₀⁻¹ * x * g₀) * diagGL a ha := by group
    rw [key, ht, diagGL_inv_conj_upperElem]

end Setup

section Assembly

variable {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "GL₂" => GL (Fin 2) K

lemma card_le_three_of_forall_conj_upper (P : Subgroup GL₂) (g : GL₂)
    (hP : ∀ x ∈ P, ∃ t : K,
      g⁻¹ * x * g = Matrix.SpecialLinearGroup.toGL (upperElem t) ∧ t ^ 3 = t) :
    Nat.card P ≤ 3 := by
  classical
  let S : Finset K := {0, 1, -1}
  have hmemS : ∀ t : K, t ^ 3 = t → t ∈ S := by
    intro t ht
    have : t * (t - 1) * (t + 1) = 0 := by linear_combination ht
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · simp [S, h]
      · simp [S, sub_eq_zero.mp h]
    · simp [S, eq_neg_of_add_eq_zero_left h]
  choose f hf using hP
  let φ : P → S := fun x => ⟨f x.1 x.2, hmemS _ (hf x.1 x.2).2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have ht : f x hx = f y hy := by
      have := congrArg Subtype.val hxy; simpa [φ] using this
    have h1 := (hf x hx).1
    have h2 := (hf y hy).1
    rw [ht, ← h2] at h1
    exact Subtype.ext (by simpa using h1)
  calc Nat.card P ≤ Nat.card S := Nat.card_le_card_of_injective φ hφ
    _ = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 3 := Finset.card_le_three

lemma p_eq_three_of_forall_cube (hp2 : p ≠ 2) (F : Subfield K)
    (hF : ∀ t : K, t ∈ F → t ^ 3 = t) : p = 3 := by
  have h2 : (2 : K) ^ 3 = 2 := hF 2 (by exact_mod_cast natCast_mem F 2)
  have h6 : ((6 : ℕ) : K) = 0 := by push_cast; linear_combination h2
  rw [CharP.cast_eq_zero_iff K p] at h6
  have hp : p.Prime := Fact.out
  have : p ∣ 2 * 3 := h6
  rcases (Nat.Prime.dvd_mul hp).mp this with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h

lemma exists_rational_image (hp2 : p ≠ 2) (G : Subgroup SL(2, K)) [Finite G]
    (F : Subfield K)
    (hΛ : ∀ t : K, upperElem t ∈ G ↔ t ∈ F) (hΛ' : ∀ t : K, lowerElem t ∈ G ↔ t ∈ F)
    {a : K} (haF : a ∈ F) (ha3 : a ^ 3 ≠ a) (h₂ : GL₂)
    (hnorm : ∀ s ∈ G, ∃ s' ∈ G, ((s' : SL(2, K)) : 𝕄) = (h₂ : 𝕄) * s * ((h₂⁻¹ : GL₂) : 𝕄))
    {s : SL(2, K)} (hs : s ∈ G) (hsunip : ((s : 𝕄) - 1) ^ 2 = 0) (hs1 : s ≠ 1)
    {P : Fin 2 → K} (hP : (s : 𝕄) *ᵥ P = P) :
    ∃ (v : Fin 2 → F) (c : K), (h₂ : 𝕄) *ᵥ P = c • fun i => (v i : K) := by
  obtain ⟨s', hs'G, hs'⟩ := hnorm s hs
  have hinv : ((h₂⁻¹ : GL₂) : 𝕄) * (h₂ : 𝕄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : (h₂ : 𝕄) * ((h₂⁻¹ : GL₂) : 𝕄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hs'unip : ((s' : 𝕄) - 1) ^ 2 = 0 := by rw [hs']; exact conj_unip hinv' hinv hsunip
  have hs'1 : s' ≠ 1 := by
    intro h1
    apply hs1
    apply Subtype.ext
    have h1' : (h₂ : 𝕄) * s * ((h₂⁻¹ : GL₂) : 𝕄) = 1 := by rw [← hs', h1]; rfl
    calc (s : 𝕄) = ((h₂⁻¹ : GL₂) : 𝕄) * ((h₂ : 𝕄) * s * ((h₂⁻¹ : GL₂) : 𝕄)) * (h₂ : 𝕄) := by
          rw [mul_assoc, mul_assoc, hinv, mul_one, ← mul_assoc, hinv, one_mul]
      _ = 1 := by rw [h1', mul_one, hinv]
  obtain ⟨v, hv0, hv⟩ := exists_rational_fixed_vec hp2 G F hΛ hΛ' haF ha3 hs'G hs'unip hs'1

  have hfix : (s' : 𝕄) *ᵥ ((h₂ : 𝕄) *ᵥ P) = (h₂ : 𝕄) *ᵥ P := by
    rw [hs', Matrix.mulVec_mulVec, mul_assoc, hinv, mul_one, ← Matrix.mulVec_mulVec, hP]
  have hvK : (fun i => (v i : K)) ≠ 0 := by
    intro h0; apply hv0; funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply, ZeroMemClass.coe_eq_zero] at this
    simpa using this
  refine ⟨v, ?_⟩
  by_contra hc
  push Not at hc

  have hD : (fun i => (v i : K)) 0 * ((h₂ : 𝕄) *ᵥ P) 1 -
      (fun i => (v i : K)) 1 * ((h₂ : 𝕄) *ᵥ P) 0 ≠ 0 := by
    intro hD
    obtain ⟨c, hc'⟩ := exists_smul_eq_of_cross_eq_zero hvK hD
    exact hc c hc'
  exact hs'1 (Subtype.ext (eq_one_of_fixes_two hv hfix hD))

lemma lowerElem_mulVec (t y z : K) : (lowerElem t : 𝕄) *ᵥ ![y, z] = ![y, t * y + z] := by
  rw [lowerElem_coe]
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_smul_map_of_normalises (hp2 : p ≠ 2) (G : Subgroup SL(2, K)) [Finite G]
    (F : Subfield K)
    (hΛ : ∀ t : K, upperElem t ∈ G ↔ t ∈ F) (hΛ' : ∀ t : K, lowerElem t ∈ G ↔ t ∈ F)
    {a : K} (haF : a ∈ F) (ha3 : a ^ 3 ≠ a) (h₂ : GL₂)
    (hnorm : ∀ s ∈ G, ∃ s' ∈ G, ((s' : SL(2, K)) : 𝕄) = (h₂ : 𝕄) * s * ((h₂⁻¹ : GL₂) : 𝕄)) :
    ∃ (c : K) (m : GL (Fin 2) F),
      (h₂ : 𝕄) = c • ((Matrix.GeneralLinearGroup.map F.subtype m : GL₂) : 𝕄) := by
  have hU : upperElem (1 : K) ∈ G := (hΛ 1).mpr F.one_mem
  have hL : lowerElem (1 : K) ∈ G := (hΛ' 1).mpr F.one_mem
  have hT : upperElem (1 : K) * lowerElem 1 * upperElem (-1) ∈ G :=
    G.mul_mem (G.mul_mem hU hL) ((hΛ _).mpr (F.neg_mem F.one_mem))

  have hUunip : (((upperElem (1 : K) : SL(2, K)) : 𝕄) - 1) ^ 2 = 0 := by
    rw [upperElem_coe]; ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hLunip : (((lowerElem (1 : K) : SL(2, K)) : 𝕄) - 1) ^ 2 = 0 := by
    rw [lowerElem_coe]; ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hTcoe : ((upperElem (1 : K) * lowerElem 1 * upperElem (-1) : SL(2, K)) : 𝕄) =
      !![2, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, upperElem_coe,
      upperElem_coe, lowerElem_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)
  have hTunip : (((upperElem (1 : K) * lowerElem 1 * upperElem (-1) : SL(2, K)) : 𝕄) - 1) ^ 2
      = 0 := by
    rw [hTcoe]; ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
      norm_num
  have hU1 : upperElem (1 : K) ≠ 1 := by
    intro h
    have := congrArg (fun s : SL(2, K) => (s : 𝕄) 0 1) h
    simp at this
  have hL1 : lowerElem (1 : K) ≠ 1 := by
    intro h
    have := congrArg (fun s : SL(2, K) => (s : 𝕄) 1 0) h
    simp at this
  have hT1 : upperElem (1 : K) * lowerElem 1 * upperElem (-1) ≠ 1 := by
    intro h
    have := congrArg (fun s : SL(2, K) => (s : 𝕄) 1 0) h
    simp only [hTcoe] at this
    simp at this
  have hUfix : ((upperElem (1 : K) : SL(2, K)) : 𝕄) *ᵥ ![1, 0] = ![1, 0] := by
    rw [upperElem_mulVec]; simp
  have hLfix : ((lowerElem (1 : K) : SL(2, K)) : 𝕄) *ᵥ ![0, 1] = ![0, 1] := by
    rw [lowerElem_mulVec]; simp
  have hTfix : ((upperElem (1 : K) * lowerElem 1 * upperElem (-1) : SL(2, K)) : 𝕄) *ᵥ ![1, 1]
      = ![1, 1] := by
    rw [hTcoe, mulVec_fin_two]
    exact funext_fin_two (by simp; norm_num) (by simp)
  obtain ⟨v₁, c₁, h₁⟩ := exists_rational_image hp2 G F hΛ hΛ' haF ha3 h₂ hnorm hU hUunip hU1 hUfix
  obtain ⟨v₂, c₂, h₂'⟩ := exists_rational_image hp2 G F hΛ hΛ' haF ha3 h₂ hnorm hL hLunip hL1 hLfix
  obtain ⟨v₃, c₃, h₃⟩ := exists_rational_image hp2 G F hΛ hΛ' haF ha3 h₂ hnorm hT hTunip hT1 hTfix
  have hdet : (h₂ : 𝕄).det ≠ 0 := by
    have : IsUnit (h₂ : 𝕄).det := by
      rw [← Matrix.isUnit_iff_isUnit_det]; exact Units.isUnit h₂
    exact this.ne_zero
  exact exists_smul_map_of_rational_lines F (h₂ : 𝕄) hdet v₁ v₂ v₃ c₁ c₂ c₃ h₁ h₂' h₃

end Assembly

end P2mDicksonGL2
p2m_reactivate "P2MW.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card.P2mDicksonGL2"

open P2mDicksonGL2 ModularCurve in
theorem solution
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (H : Subgroup (GL (Fin 2) K)) [Finite H] (hdvd : p ∣ Nat.card H)
    (hirr : ∀ v : Fin 2 → K, v ≠ 0 →
      ∃ h ∈ H, ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∉ K ∙ v) :
    (p = 3 ∧ ¬ 9 ∣ Nat.card H) ∨
    ∃ (F : Subfield K) (_ : Finite F) (g : GL (Fin 2) K),
      (∀ s : SL(2, F),
        g * (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map F.subtype s)) * g⁻¹ ∈ H) ∧
      (∀ h ∈ H, ∃ (a : K) (m : GL (Fin 2) F),
        ((g⁻¹ * h * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          a • ((Matrix.GeneralLinearGroup.map F.subtype m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  classical

  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  set P' : Subgroup (GL (Fin 2) K) := (P : Subgroup H).map H.subtype with hP'
  have hP'H : P' ≤ H := Subgroup.map_subtype_le _
  have hcardP' : Nat.card P' = Nat.card P := Subgroup.card_subtype H P
  have hcardP : Nat.card P = p ^ (Nat.card H).factorization p := Sylow.card_eq_multiplicity P
  have hpP : p ∣ Nat.card P := by
    have := Sylow.pow_dvd_card_of_pow_dvd_card P (n := 1) (by simpa using hdvd)
    simpa using this
  have hP1 : ∃ x ∈ P', x ≠ 1 := by
    rcases P'.bot_or_exists_ne_one with h | h
    · exfalso
      have h1 : Nat.card P' = 1 := by rw [h]; exact Subgroup.card_bot
      rw [hcardP'] at h1
      rw [h1, Nat.dvd_one] at hpP
      exact (Fact.out : p.Prime).one_lt.ne' hpP
    · exact h
  obtain ⟨g, μ, hμ, hU1, hLμ, hPup⟩ :=
    exists_conj_standard H P' hP'H (hcardP'.trans hcardP) hP1 hirr

  set G : Subgroup SL(2, K) :=
    H.comap ((MulAut.conj g).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL) with hG
  have memG : ∀ s : SL(2, K), s ∈ G ↔ g * Matrix.SpecialLinearGroup.toGL s * g⁻¹ ∈ H :=
    fun s => Iff.rfl
  haveI : Finite G := by
    refine Finite.of_injective
      (fun s : G => (⟨g * Matrix.SpecialLinearGroup.toGL s.1 * g⁻¹, (memG _).mp s.2⟩ : H)) ?_
    intro s t hst
    have h1 : g * Matrix.SpecialLinearGroup.toGL s.1 * g⁻¹ =
        g * Matrix.SpecialLinearGroup.toGL t.1 * g⁻¹ := congrArg Subtype.val hst
    rw [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective h1)

  have not9 : p = 3 → (∀ x ∈ P', ∃ t : K,
      g⁻¹ * x * g = Matrix.SpecialLinearGroup.toGL (upperElem t) ∧ t ^ 3 = t) →
      ¬ 9 ∣ Nat.card H := by
    intro hp3 hall h9
    subst hp3
    have h3 := card_le_three_of_forall_conj_upper P' g hall
    have h9P : 3 ^ 2 ∣ Nat.card P := Sylow.pow_dvd_card_of_pow_dvd_card P (n := 2) h9
    rw [← hcardP'] at h9P
    have hpos : 0 < Nat.card P' := by
      rw [hcardP', hcardP]; positivity
    have := Nat.le_of_dvd hpos h9P
    omega
  have hmemU : ∀ x ∈ P', ∀ t : K,
      g⁻¹ * x * g = Matrix.SpecialLinearGroup.toGL (upperElem t) → upperElem t ∈ G := by
    intro x hx t ht
    rw [memG, ← ht]
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]; exact hP'H hx

  rcases Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite hp2 G
      ((memG _).mpr hU1) ⟨μ, hμ, (memG _).mpr hLμ⟩ with ⟨hp3, hsmall⟩ | ⟨F, hFfin, hΛ, hΛ'⟩
  · refine Or.inl ⟨hp3, not9 hp3 ?_⟩
    intro x hx
    obtain ⟨t, ht⟩ := hPup x hx
    exact ⟨t, ht, hsmall t (hmemU x hx t ht)⟩
  · by_cases hsm : ∀ t : K, t ∈ F → t ^ 3 = t
    · have hp3 := p_eq_three_of_forall_cube hp2 F hsm
      refine Or.inl ⟨hp3, not9 hp3 ?_⟩
      intro x hx
      obtain ⟨t, ht⟩ := hPup x hx
      exact ⟨t, ht, hsm t ((hΛ t).mp (hmemU x hx t ht))⟩
    · push Not at hsm
      obtain ⟨a, haF, ha3⟩ := hsm
      refine Or.inr ⟨F, hFfin, g, ?_, ?_⟩
      · intro s
        exact (memG _).mp (map_mem_of_elem_mem G F (fun t ht => (hΛ t).mpr ht)
          (fun t ht => (hΛ' t).mpr ht) s)
      · intro h hh
        refine exists_smul_map_of_normalises hp2 G F hΛ hΛ' haF ha3 (g⁻¹ * h * g) ?_
        intro s hs

        set y : GL (Fin 2) K := g⁻¹ * h * g * Matrix.SpecialLinearGroup.toGL s * (g⁻¹ * h * g)⁻¹
          with hy
        have hydet : Matrix.det (y : Matrix (Fin 2) (Fin 2) K) = 1 := by
          have h1 : Matrix.GeneralLinearGroup.det y = 1 := by
            rw [hy, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
            apply Units.ext
            simp
          have := congrArg Units.val h1
          simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
        refine ⟨⟨(y : Matrix (Fin 2) (Fin 2) K), hydet⟩, ?_, ?_⟩
        · rw [memG]
          have hval : Matrix.SpecialLinearGroup.toGL
              (⟨(y : Matrix (Fin 2) (Fin 2) K), hydet⟩ : SL(2, K)) = y := Units.ext rfl
          rw [hval, hy]
          have : g * (g⁻¹ * h * g * Matrix.SpecialLinearGroup.toGL s * (g⁻¹ * h * g)⁻¹) * g⁻¹ =
              h * (g * Matrix.SpecialLinearGroup.toGL s * g⁻¹) * h⁻¹ := by group
          rw [this]
          exact H.mul_mem (H.mul_mem hh ((memG s).mp hs)) (H.inv_mem hh)
        · show (y : Matrix (Fin 2) (Fin 2) K) = _
          rw [hy, Units.val_mul, Units.val_mul]
          rfl

end S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card (solution)
