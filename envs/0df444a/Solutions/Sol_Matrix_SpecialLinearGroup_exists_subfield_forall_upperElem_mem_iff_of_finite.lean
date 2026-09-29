-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2f56adbc-6a39-5301-a384-cf223a01e395

import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import Theorems.Thm_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite

set_option autoImplicit false

open Matrix MatrixGroups ModularCurve

namespace P2mDicksonSL2

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

lemma eq_upper_of_unip_mul_upper {M : 𝕄} (hM : (M - 1) ^ 2 = 0) {a : K} (ha : a ≠ 0)
    (hMa : (M * !![1, a; 0, 1] - 1) ^ 2 = 0) : M = !![1, M 0 1; 0, 1] := by
  have htr := trace_of_unip hM
  have htr' := trace_of_unip hMa
  simp [Matrix.mul_apply, Fin.sum_univ_two] at htr'
  have e10 : M 1 0 = 0 := by
    have : a * M 1 0 = 0 := by linear_combination htr' - htr
    exact (mul_eq_zero.mp this).resolve_left ha
  obtain ⟨h00, -, -, -⟩ := sq_sub_one_apply M
  rw [hM, Matrix.zero_apply, e10, mul_zero, add_zero] at h00
  have e00 : M 0 0 = 1 := by
    have := mul_self_eq_zero.mp h00.symm; linear_combination this
  have e11 : M 1 1 = 1 := by linear_combination htr - e00
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [e00, e10, e11]

lemma eq_lower_of_unip_mul_lower {M : 𝕄} (hM : (M - 1) ^ 2 = 0) {a : K} (ha : a ≠ 0)
    (hMa : (M * !![1, 0; a, 1] - 1) ^ 2 = 0) : M = !![1, 0; M 1 0, 1] := by
  have htr := trace_of_unip hM
  have htr' := trace_of_unip hMa
  simp [Matrix.mul_apply, Fin.sum_univ_two] at htr'
  have e01 : M 0 1 = 0 := by
    have : a * M 0 1 = 0 := by linear_combination htr' - htr
    exact (mul_eq_zero.mp this).resolve_left ha
  obtain ⟨-, -, -, h11⟩ := sq_sub_one_apply M
  rw [hM, Matrix.zero_apply, e01, mul_zero, zero_add] at h11
  have e11 : M 1 1 = 1 := by
    have := mul_self_eq_zero.mp h11.symm; linear_combination this
  have e00 : M 0 0 = 1 := by linear_combination htr - e11
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [e00, e01, e11]

lemma upperElem_inv (x : K) : (upperElem x)⁻¹ = upperElem (-x) := by
  rw [inv_eq_iff_mul_eq_one, upperElem_mul, add_neg_cancel, upperElem_zero]

lemma lowerElem_inv (x : K) : (lowerElem x)⁻¹ = lowerElem (-x) := by
  rw [inv_eq_iff_mul_eq_one, lowerElem_mul, add_neg_cancel, lowerElem_zero]

lemma upperElem_injective : Function.Injective (upperElem : K → SL(2, K)) := by
  intro a b h
  have := congrArg (fun s : SL(2, K) => (s : 𝕄) 0 1) h
  simpa using this

lemma lowerElem_injective : Function.Injective (lowerElem : K → SL(2, K)) := by
  intro a b h
  have := congrArg (fun s : SL(2, K) => (s : 𝕄) 1 0) h
  simpa using this

lemma upperElem_ne_lowerElem (a b : K) (ha : a ≠ 0) : upperElem a ≠ lowerElem b := by
  intro h
  have := congrArg (fun s : SL(2, K) => (s : 𝕄) 0 1) h
  simp at this
  exact ha this

lemma upperElem_mulVec (t y z : K) : (upperElem t : 𝕄) *ᵥ ![y, z] = ![y + t * z, z] := by
  rw [upperElem_coe]
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma lowerElem_mulVec (t y z : K) : (lowerElem t : 𝕄) *ᵥ ![y, z] = ![y, t * y + z] := by
  rw [lowerElem_coe]
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma lul_fixes (μ s : K) :
    ((lowerElem μ * upperElem s * lowerElem (-μ) : SL(2, K)) : 𝕄) *ᵥ ![1, μ] = ![1, μ] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, lowerElem_mulVec, upperElem_mulVec,
    lowerElem_mulVec]
  refine funext_fin_two ?_ ?_ <;> simp

lemma ulu_fixes (l s : K) :
    ((upperElem l * lowerElem s * upperElem (-l) : SL(2, K)) : 𝕄) *ᵥ ![l, 1] = ![l, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, upperElem_mulVec, lowerElem_mulVec,
    upperElem_mulVec]
  refine funext_fin_two ?_ ?_ <;> simp

def diagElem (a : K) (ha : a ≠ 0) : SL(2, K) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

lemma diagElem_eq_word (a : K) (ha : a ≠ 0) :
    diagElem a ha = upperElem a * lowerElem (-a⁻¹) * upperElem a *
      (upperElem (1 : K) * lowerElem (-1) * upperElem 1)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagElem, Matrix.mul_apply, Fin.sum_univ_two, ha]

lemma diagElem_conj_upperElem (a : K) (ha : a ≠ 0) (t : K) :
    diagElem a ha * upperElem t * (diagElem a ha)⁻¹ = upperElem (a ^ 2 * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [diagElem, Matrix.mul_apply, Fin.sum_univ_two]; try field_simp)

lemma weyl_conj_upperElem (t : K) :
    (upperElem (1 : K) * lowerElem (-1) * upperElem 1) * upperElem t *
      (upperElem (1 : K) * lowerElem (-1) * upperElem 1)⁻¹ = lowerElem (-t) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section Sylows

variable {p : ℕ} [Fact p.Prime] [CharP K p]

lemma unip_of_pow_eq_one {s : SL(2, K)} {k : ℕ} (hs : s ^ p ^ k = 1) :
    ((s : 𝕄) - 1) ^ 2 = 0 := by
  have hM : (s : 𝕄) ^ p ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hs]; rfl
  have hN : ((s : 𝕄) - 1) ^ p ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right (s : 𝕄)), hM, one_pow, sub_self]
  exact sq_eq_zero_of_pow_eq_zero hN

variable (G : Subgroup SL(2, K))

def upperSub : Subgroup G where
  carrier := {g | ∃ t : K, (g : SL(2, K)) = upperElem t}
  mul_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [Subgroup.coe_mul, hs, ht, upperElem_mul]⟩
  one_mem' := ⟨0, by rw [upperElem_zero]; rfl⟩
  inv_mem' := by
    rintro a ⟨s, hs⟩
    exact ⟨-s, by rw [Subgroup.coe_inv, hs, upperElem_inv]⟩

def lowerSub : Subgroup G where
  carrier := {g | ∃ t : K, (g : SL(2, K)) = lowerElem t}
  mul_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [Subgroup.coe_mul, hs, ht, lowerElem_mul]⟩
  one_mem' := ⟨0, by rw [lowerElem_zero]; rfl⟩
  inv_mem' := by
    rintro a ⟨s, hs⟩
    exact ⟨-s, by rw [Subgroup.coe_inv, hs, lowerElem_inv]⟩

variable {G}

lemma mem_upperSub {g : G} : g ∈ upperSub G ↔ ∃ t : K, (g : SL(2, K)) = upperElem t := Iff.rfl
lemma mem_lowerSub {g : G} : g ∈ lowerSub G ↔ ∃ t : K, (g : SL(2, K)) = lowerElem t := Iff.rfl

omit [Fact p.Prime] in
lemma upperElem_pow_char (t : K) : (upperElem t) ^ p = 1 := by
  rw [upperElem_pow, CharP.cast_eq_zero, zero_mul, upperElem_zero]

omit [Fact p.Prime] in
lemma lowerElem_pow_char (t : K) : (lowerElem t) ^ p = 1 := by
  rw [lowerElem_pow, CharP.cast_eq_zero, zero_mul, lowerElem_zero]

omit [Fact p.Prime] in
lemma isPGroup_upperSub : IsPGroup p (upperSub G) := by
  rintro ⟨g, ⟨t, ht⟩⟩
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  simp only [pow_one, Subgroup.coe_pow, ht, upperElem_pow_char]
  rfl

omit [Fact p.Prime] in
lemma isPGroup_lowerSub : IsPGroup p (lowerSub G) := by
  rintro ⟨g, ⟨t, ht⟩⟩
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  simp only [pow_one, Subgroup.coe_pow, ht, lowerElem_pow_char]
  rfl

lemma unip_of_mem_pGroup {Q : Subgroup G} (hQ : IsPGroup p Q) {g : G} (hg : g ∈ Q) :
    (((g : SL(2, K)) : 𝕄) - 1) ^ 2 = 0 := by
  obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
  have : (g : SL(2, K)) ^ p ^ k = 1 := by
    have := congrArg (fun x : Q => ((x : G) : SL(2, K))) hk
    simpa using this
  exact unip_of_pow_eq_one this

lemma le_upperSub_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup p Q) {a : K} (ha : a ≠ 0)
    {u : G} (hu : (u : SL(2, K)) = upperElem a) (huQ : u ∈ Q) : Q ≤ upperSub G := by
  intro g hg
  have h1 := unip_of_mem_pGroup hQ hg
  have h2 := unip_of_mem_pGroup hQ (Q.mul_mem hg huQ)
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu, upperElem_coe] at h2
  exact ⟨((g : SL(2, K)) : 𝕄) 0 1, Subtype.ext (eq_upper_of_unip_mul_upper h1 ha h2)⟩

lemma le_lowerSub_of_isPGroup {Q : Subgroup G} (hQ : IsPGroup p Q) {a : K} (ha : a ≠ 0)
    {u : G} (hu : (u : SL(2, K)) = lowerElem a) (huQ : u ∈ Q) : Q ≤ lowerSub G := by
  intro g hg
  have h1 := unip_of_mem_pGroup hQ hg
  have h2 := unip_of_mem_pGroup hQ (Q.mul_mem hg huQ)
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu, lowerElem_coe] at h2
  exact ⟨((g : SL(2, K)) : 𝕄) 1 0, Subtype.ext (eq_lower_of_unip_mul_lower h1 ha h2)⟩

def upperSylow (hU : upperElem (1 : K) ∈ G) : Sylow p G where
  toSubgroup := upperSub G
  isPGroup' := isPGroup_upperSub
  is_maximal' := by
    intro Q hQ hle
    exact le_antisymm (le_upperSub_of_isPGroup hQ one_ne_zero (u := ⟨_, hU⟩) rfl
      (hle ⟨1, rfl⟩)) hle

def lowerSylow {μ : K} (hμ : μ ≠ 0) (hL : lowerElem μ ∈ G) : Sylow p G where
  toSubgroup := lowerSub G
  isPGroup' := isPGroup_lowerSub
  is_maximal' := by
    intro Q hQ hle
    exact le_antisymm (le_lowerSub_of_isPGroup hQ hμ (u := ⟨_, hL⟩) rfl (hle ⟨μ, rfl⟩)) hle

lemma upperSub_inf_eq_bot (hU : upperElem (1 : K) ∈ G) (Q : Sylow p G)
    (hQ : Q ≠ upperSylow (p := p) hU) : (upperSub G) ⊓ (Q : Subgroup G) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨t, ht⟩, hgQ⟩
  rw [Subgroup.mem_bot]
  by_contra hg1
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hg1
    exact Subtype.ext (by rw [ht, upperElem_zero]; rfl)
  apply hQ
  have hle : (Q : Subgroup G) ≤ upperSub G := le_upperSub_of_isPGroup Q.isPGroup' ht0 ht hgQ
  exact Sylow.ext (Q.is_maximal' (isPGroup_upperSub (G := G)) hle).symm

lemma lowerSub_inf_eq_bot {μ : K} (hμ : μ ≠ 0) (hL : lowerElem μ ∈ G) (Q : Sylow p G)
    (hQ : Q ≠ lowerSylow (p := p) hμ hL) : (lowerSub G) ⊓ (Q : Subgroup G) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨t, ht⟩, hgQ⟩
  rw [Subgroup.mem_bot]
  by_contra hg1
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hg1
    exact Subtype.ext (by rw [ht, lowerElem_zero]; rfl)
  apply hQ
  have hle : (Q : Subgroup G) ≤ lowerSub G := le_lowerSub_of_isPGroup Q.isPGroup' ht0 ht hgQ
  exact Sylow.ext (Q.is_maximal' (isPGroup_lowerSub (G := G)) hle).symm

end Sylows

section Orbit

lemma exists_smul_eq_of_card_sylow {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p H) (hPQ : P ≠ Q)
    (hTI : ∀ Q' : Sylow p H, Q' ≠ P → (P : Subgroup H) ⊓ (Q' : Subgroup H) = ⊥)
    (hcard : Nat.card (Sylow p H) = Nat.card P + 1)
    (Q' : Sylow p H) (hQ' : Q' ≠ P) : ∃ u : P, (u : H) • Q = Q' := by
  classical
  let f : Option P → Sylow p H := fun o => o.elim P (fun u => (u : H) • Q)
  have hPfix : ∀ u : P, (u : H) • P = P := fun u =>
    Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer u.2)
  have hf : Function.Injective f := by
    rintro (_ | u) (_ | v) huv
    · rfl
    · exfalso; apply hPQ
      change P = (v : H) • Q at huv
      have : ((v : H)⁻¹) • ((v : H) • Q) = Q := inv_smul_smul _ _
      rw [← huv, ← Subgroup.coe_inv, hPfix] at this
      exact this
    · exfalso; apply hPQ
      change (u : H) • Q = P at huv
      have : ((u : H)⁻¹) • ((u : H) • Q) = Q := inv_smul_smul _ _
      rw [huv, ← Subgroup.coe_inv, hPfix] at this
      exact this
    · change (u : H) • Q = (v : H) • Q at huv
      have h1 : ((v : H)⁻¹ * u) • Q = Q := by rw [mul_smul, huv, inv_smul_smul]
      rw [Sylow.smul_eq_iff_mem_normalizer] at h1
      have h2 : ((v⁻¹ * u : P) : H) ∈ (P : Subgroup H) ⊓ (Q : Subgroup H) := by
        rw [← IsPGroup.inf_normalizer_sylow P.isPGroup' Q]
        exact ⟨(v⁻¹ * u).2, h1⟩
      rw [hTI Q (Ne.symm hPQ), Subgroup.mem_bot] at h2
      have : v⁻¹ * u = 1 := Subtype.ext h2
      rw [inv_mul_eq_one] at this
      rw [this]
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hcard, Finite.card_option])
  obtain ⟨o, ho⟩ := hbij.2 Q'
  rcases o with _ | u
  · exact absurd ho.symm hQ'
  · exact ⟨u, ho⟩

end Orbit

section Main

variable {p : ℕ} [Fact p.Prime] [CharP K p]

lemma card_upperSub (G : Subgroup SL(2, K)) :
    Nat.card (upperSub G) = Nat.card {t : K // upperElem t ∈ G} := by
  refine (Nat.card_eq_of_bijective (fun t : {t : K // upperElem t ∈ G} =>
    (⟨⟨upperElem t.1, t.2⟩, t.1, rfl⟩ : upperSub G)) ⟨?_, ?_⟩).symm
  · intro a b h
    have := congrArg (fun x : upperSub G => ((x : G) : SL(2, K))) h
    exact Subtype.ext (upperElem_injective this)
  · rintro ⟨⟨g, hg⟩, t, ht⟩
    refine ⟨⟨t, ?_⟩, ?_⟩
    · change g = upperElem t at ht
      rw [← ht]; exact hg
    · exact Subtype.ext (Subtype.ext ht.symm)

lemma card_lowerSub (G : Subgroup SL(2, K)) :
    Nat.card (lowerSub G) = Nat.card {t : K // lowerElem t ∈ G} := by
  refine (Nat.card_eq_of_bijective (fun t : {t : K // lowerElem t ∈ G} =>
    (⟨⟨lowerElem t.1, t.2⟩, t.1, rfl⟩ : lowerSub G)) ⟨?_, ?_⟩).symm
  · intro a b h
    have := congrArg (fun x : lowerSub G => ((x : G) : SL(2, K))) h
    exact Subtype.ext (lowerElem_injective this)
  · rintro ⟨⟨g, hg⟩, t, ht⟩
    refine ⟨⟨t, ?_⟩, ?_⟩
    · change g = lowerElem t at ht
      rw [← ht]; exact hg
    · exact Subtype.ext (Subtype.ext ht.symm)

lemma four_le_card {G : Subgroup SL(2, K)} [Finite G] (h2 : (2 : K) ≠ 0)
    (hU : upperElem (1 : K) ∈ G) {t : K} (ht : upperElem t ∈ G)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm1 : t ≠ -1) : 4 ≤ Nat.card {t : K // upperElem t ∈ G} := by
  haveI : Finite {t : K // upperElem t ∈ G} :=
    Finite.of_injective (fun x : {t : K // upperElem t ∈ G} => (⟨upperElem x.1, x.2⟩ : G))
      (fun a b h => Subtype.ext (upperElem_injective (congrArg Subtype.val h)))
  have hU0 : upperElem (0 : K) ∈ G := by rw [upperElem_zero]; exact G.one_mem
  have hUm : upperElem (-1 : K) ∈ G := by rw [← upperElem_inv]; exact G.inv_mem hU
  let f : Fin 4 → {t : K // upperElem t ∈ G} := ![⟨0, hU0⟩, ⟨1, hU⟩, ⟨-1, hUm⟩, ⟨t, ht⟩]
  have h1m : (1 : K) ≠ -1 := by
    intro h; apply h2; linear_combination h
  have hf : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hv ⊢ <;>
      first
      | exact absurd hv h1m
      | exact absurd hv.symm h1m
      | exact absurd hv h0
      | exact absurd hv.symm h0
      | exact absurd hv h1
      | exact absurd hv.symm h1
      | exact absurd hv hm1
      | exact absurd hv.symm hm1
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem main (hp2 : p ≠ 2) (G : Subgroup SL(2, K)) [Finite G]
    (hU : upperElem (1 : K) ∈ G) (hL : ∃ μ : K, μ ≠ 0 ∧ lowerElem μ ∈ G) :
    (p = 3 ∧ ∀ t : K, upperElem t ∈ G → t ^ 3 = t) ∨
    ∃ F : Subfield K, Finite F ∧
      (∀ t : K, upperElem t ∈ G ↔ t ∈ F) ∧
      (∀ t : K, lowerElem t ∈ G ↔ t ∈ F) := by
  classical
  obtain ⟨μ, hμ, hLμ⟩ := hL
  have hprime : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp this)
  set S₁ : Sylow p G := upperSylow hU with hS₁
  set S₂ : Sylow p G := lowerSylow hμ hLμ with hS₂
  have hne : S₁ ≠ S₂ := by
    intro h
    have h1 : (⟨upperElem 1, hU⟩ : G) ∈ (S₁ : Subgroup G) := ⟨1, rfl⟩
    rw [h] at h1
    obtain ⟨t, ht⟩ := h1
    exact upperElem_ne_lowerElem 1 t one_ne_zero ht
  have hcard₁ : Nat.card S₁ = Nat.card {t : K // upperElem t ∈ G} := card_upperSub G
  have hcard₂ : Nat.card S₂ = Nat.card {t : K // lowerElem t ∈ G} := card_lowerSub G
  have hcard₁₂ : Nat.card S₁ = Nat.card S₂ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

  have hUnat : ∀ n : ℕ, upperElem (n : K) ∈ G := by
    intro n
    have : upperElem (n : K) = (upperElem (1 : K)) ^ n := by rw [upperElem_pow, mul_one]
    rw [this]; exact G.pow_mem hU n
  by_cases hq : 3 < Nat.card S₁
  swap
  ·
    push Not at hq
    have hsmall : ∀ t : K, upperElem t ∈ G → t = 0 ∨ t = 1 ∨ t = -1 := by
      intro t ht
      by_contra hc
      push Not at hc
      have := four_le_card h2 hU ht hc.1 hc.2.1 hc.2.2
      rw [← hcard₁] at this
      omega
    refine Or.inl ⟨?_, ?_⟩
    · rcases hsmall 2 (by exact_mod_cast hUnat 2) with h | h | h
      · exact absurd h h2
      · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero
      · have h3 : ((3 : ℕ) : K) = 0 := by push_cast; linear_combination h
        rw [CharP.cast_eq_zero_iff K p] at h3
        exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).mp h3
    · intro t ht
      rcases hsmall t ht with rfl | rfl | rfl <;> ring
  ·
    have hn : Nat.card (Sylow p G) = Nat.card S₁ + 1 := by
      refine Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite hp2 G S₁ hq ?_
      intro h1
      rw [Nat.card_eq_one_iff_unique] at h1
      exact hne (h1.1.elim S₁ S₂)
    have hn' : Nat.card (Sylow p G) = Nat.card S₂ + 1 := by rw [hn, hcard₁₂]
    have hTI₁ : ∀ Q : Sylow p G, Q ≠ S₁ → (S₁ : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ :=
      fun Q hQ => upperSub_inf_eq_bot hU Q hQ
    have hTI₂ : ∀ Q : Sylow p G, Q ≠ S₂ → (S₂ : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ :=
      fun Q hQ => lowerSub_inf_eq_bot hμ hLμ Q hQ

    have hinvL : ∀ m : K, lowerElem m ∈ G → m ≠ 0 → upperElem m⁻¹ ∈ G := by
      intro m hm hm0
      set g : G := ⟨lowerElem m, hm⟩ with hg
      have hgS₂ : g ∈ (S₂ : Subgroup G) := ⟨m, rfl⟩
      have hQ : g • S₁ ≠ S₁ := by
        intro h
        rw [Sylow.smul_eq_iff_mem_normalizer] at h
        have : g ∈ (S₂ : Subgroup G) ⊓ (S₁ : Subgroup G) := by
          rw [← IsPGroup.inf_normalizer_sylow S₂.isPGroup' S₁]; exact ⟨hgS₂, h⟩
        rw [hTI₂ S₁ hne, Subgroup.mem_bot] at this
        have := congrArg (fun x : G => (x : SL(2, K))) this
        simp only [hg, OneMemClass.coe_one] at this
        exact hm0 (by simpa using lowerElem_injective (this.trans lowerElem_zero.symm))
      obtain ⟨u, hu⟩ := exists_smul_eq_of_card_sylow S₁ S₂ hne hTI₁ hn (g • S₁) hQ
      obtain ⟨l, hl⟩ := u.2

      have hmark : g * ⟨upperElem 1, hU⟩ * g⁻¹ ∈ ((g • S₁ : Sylow p G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]; exact ⟨⟨upperElem 1, hU⟩, ⟨1, rfl⟩, rfl⟩
      rw [← hu, Sylow.coe_subgroup_smul] at hmark
      obtain ⟨x, ⟨s, hs⟩, hx⟩ := hmark
      have hxeq : (u : G) * x * (u : G)⁻¹ = g * ⟨upperElem 1, hU⟩ * g⁻¹ := hx
      have hmat := congrArg (fun y : G => ((y : SL(2, K)) : 𝕄)) hxeq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hl, hs, hg, upperElem_inv,
        lowerElem_inv] at hmat

      have hfix1 := ulu_fixes (K := K) l s
      have hfix2 := lul_fixes (K := K) m 1
      rw [hmat] at hfix1
      by_contra hc
      have hD : (![l, 1] : Fin 2 → K) 0 * (![1, m] : Fin 2 → K) 1 -
          (![l, 1] : Fin 2 → K) 1 * (![1, m] : Fin 2 → K) 0 ≠ 0 := by
        simp
        intro h
        apply hc
        have hl' : l = m⁻¹ := by field_simp; linear_combination h
        rw [← hl']
        have := (u : G).2; rw [hl] at this; exact this
      have h1 := eq_one_of_fixes_two hfix1 hfix2 hD
      have : (lowerElem m * upperElem 1 * lowerElem (-m) : SL(2, K)) = 1 := Subtype.ext h1
      rw [← lowerElem_inv, conj_eq_one_iff] at this
      exact one_ne_zero (upperElem_injective (this.trans upperElem_zero.symm))

    have hinvU : ∀ l : K, upperElem l ∈ G → l ≠ 0 → lowerElem l⁻¹ ∈ G := by
      intro l hl hl0
      set g : G := ⟨upperElem l, hl⟩ with hg
      have hgS₁ : g ∈ (S₁ : Subgroup G) := ⟨l, rfl⟩
      have hQ : g • S₂ ≠ S₂ := by
        intro h
        rw [Sylow.smul_eq_iff_mem_normalizer] at h
        have : g ∈ (S₁ : Subgroup G) ⊓ (S₂ : Subgroup G) := by
          rw [← IsPGroup.inf_normalizer_sylow S₁.isPGroup' S₂]; exact ⟨hgS₁, h⟩
        rw [hTI₁ S₂ (Ne.symm hne), Subgroup.mem_bot] at this
        have := congrArg (fun x : G => (x : SL(2, K))) this
        simp only [hg, OneMemClass.coe_one] at this
        exact hl0 (by simpa using upperElem_injective (this.trans upperElem_zero.symm))
      obtain ⟨v, hv⟩ := exists_smul_eq_of_card_sylow S₂ S₁ (Ne.symm hne) hTI₂ hn' (g • S₂) hQ
      obtain ⟨m, hm⟩ := v.2
      have hmark : g * ⟨lowerElem μ, hLμ⟩ * g⁻¹ ∈ ((g • S₂ : Sylow p G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]; exact ⟨⟨lowerElem μ, hLμ⟩, ⟨μ, rfl⟩, rfl⟩
      rw [← hv, Sylow.coe_subgroup_smul] at hmark
      obtain ⟨x, ⟨s, hs⟩, hx⟩ := hmark
      have hxeq : (v : G) * x * (v : G)⁻¹ = g * ⟨lowerElem μ, hLμ⟩ * g⁻¹ := hx
      have hmat := congrArg (fun y : G => ((y : SL(2, K)) : 𝕄)) hxeq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm, hs, hg, upperElem_inv,
        lowerElem_inv] at hmat
      have hfix1 := lul_fixes (K := K) m s
      have hfix2 := ulu_fixes (K := K) l μ
      rw [hmat] at hfix1
      by_contra hc
      have hD : (![1, m] : Fin 2 → K) 0 * (![l, 1] : Fin 2 → K) 1 -
          (![1, m] : Fin 2 → K) 1 * (![l, 1] : Fin 2 → K) 0 ≠ 0 := by
        simp
        intro h
        apply hc
        have hm' : m = l⁻¹ := by field_simp; linear_combination -h
        rw [← hm']
        have := (v : G).2; rw [hm] at this; exact this
      have h1 := eq_one_of_fixes_two hfix1 hfix2 hD
      have : (upperElem l * lowerElem μ * upperElem (-l) : SL(2, K)) = 1 := Subtype.ext h1
      rw [← upperElem_inv, conj_eq_one_iff] at this
      exact hμ (lowerElem_injective (this.trans lowerElem_zero.symm))

    have hL1 : lowerElem (1 : K) ∈ G := by simpa using hinvU 1 hU one_ne_zero
    have hLm1 : lowerElem (-1 : K) ∈ G := by rw [← lowerElem_inv]; exact G.inv_mem hL1
    have hw : upperElem (1 : K) * lowerElem (-1) * upperElem 1 ∈ G :=
      G.mul_mem (G.mul_mem hU hLm1) hU
    have hUL : ∀ t : K, upperElem t ∈ G ↔ lowerElem t ∈ G := by
      intro t
      constructor
      · intro ht
        have := G.mul_mem (G.mul_mem hw ht) (G.inv_mem hw)
        rw [weyl_conj_upperElem, ← lowerElem_inv] at this
        simpa using this
      · intro ht
        have h1 : lowerElem (-t) ∈ G := by rw [← lowerElem_inv]; exact G.inv_mem ht
        rw [← weyl_conj_upperElem] at h1
        have := G.mul_mem (G.mul_mem (G.inv_mem hw) h1) hw
        simpa [mul_assoc] using this

    have hneg : ∀ t : K, upperElem t ∈ G → upperElem (-t) ∈ G := fun t ht => by
      rw [← upperElem_inv]; exact G.inv_mem ht
    have hadd : ∀ a b : K, upperElem a ∈ G → upperElem b ∈ G → upperElem (a + b) ∈ G :=
      fun a b ha hb => by rw [← upperElem_mul]; exact G.mul_mem ha hb
    have hinv : ∀ t : K, upperElem t ∈ G → upperElem t⁻¹ ∈ G := by
      intro t ht
      rcases eq_or_ne t 0 with rfl | ht0
      · rw [_root_.inv_zero]; exact ht
      · exact (hUL _).mpr (hinvU t ht ht0)
    have hsq : ∀ l t : K, upperElem l ∈ G → upperElem t ∈ G → upperElem (l ^ 2 * t) ∈ G := by
      intro l t hl ht
      rcases eq_or_ne l 0 with rfl | hl0
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
          upperElem_zero]; exact G.one_mem
      · have hd : diagElem l hl0 ∈ G := by
          rw [diagElem_eq_word]
          refine G.mul_mem (G.mul_mem (G.mul_mem hl ((hUL _).mp (hneg _ (hinv _ hl)))) hl)
            (G.inv_mem hw)
        have := G.mul_mem (G.mul_mem hd ht) (G.inv_mem hd)
        rwa [diagElem_conj_upperElem] at this
    have hmul : ∀ a b : K, upperElem a ∈ G → upperElem b ∈ G → upperElem (a * b) ∈ G := by
      intro a b ha hb
      have h2ab : upperElem (2 * (a * b)) ∈ G := by
        have e : 2 * (a * b) = (a + b) ^ 2 * 1 + -(a ^ 2 * 1) + -(b ^ 2 * 1) := by ring
        rw [e]
        exact hadd _ _ (hadd _ _ (hsq _ _ (hadd _ _ ha hb) hU) (hneg _ (hsq _ _ ha hU)))
          (hneg _ (hsq _ _ hb hU))

      obtain ⟨k, hk⟩ : ∃ k, p + 1 = 2 * k := by
        rcases hprime.eq_two_or_odd' with h | h
        · exact absurd h hp2
        · obtain ⟨j, hj⟩ := h; exact ⟨j + 1, by omega⟩
      have hpow := G.pow_mem h2ab k
      rw [upperElem_pow] at hpow
      have : (k : K) * (2 * (a * b)) = a * b := by
        have hk' : ((2 * k : ℕ) : K) = 1 := by
          rw [← hk]; push_cast; rw [CharP.cast_eq_zero K p, zero_add]
        push_cast at hk'
        linear_combination (a * b) * hk'
      rwa [this] at hpow

    let F : Subfield K :=
      { carrier := {t | upperElem t ∈ G}
        mul_mem' := fun {a b} ha hb => hmul a b ha hb
        one_mem' := hU
        add_mem' := fun {a b} ha hb => hadd a b ha hb
        zero_mem' := by show upperElem (0 : K) ∈ G; rw [upperElem_zero]; exact G.one_mem
        neg_mem' := fun {t} ht => hneg t ht
        inv_mem' := fun t ht => hinv t ht }
    haveI : Finite F :=
      Finite.of_injective (fun x : F => (⟨upperElem (x : K), x.2⟩ : G))
        (fun a b h => Subtype.ext (upperElem_injective (congrArg Subtype.val h)))
    exact Or.inr ⟨F, inferInstance, fun t => Iff.rfl, fun t => (hUL t).symm⟩

end Main

end P2mDicksonSL2

theorem solution
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G]
    (hU : ModularCurve.upperElem (1 : K) ∈ G)
    (hL : ∃ μ : K, μ ≠ 0 ∧ ModularCurve.lowerElem μ ∈ G) :
    (p = 3 ∧ ∀ t : K, ModularCurve.upperElem t ∈ G → t ^ 3 = t) ∨
    ∃ F : Subfield K, Finite F ∧
      (∀ t : K, ModularCurve.upperElem t ∈ G ↔ t ∈ F) ∧
      (∀ t : K, ModularCurve.lowerElem t ∈ G ↔ t ∈ F) :=
  P2mDicksonSL2.main hp2 G hU hL

end S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite (solution)
