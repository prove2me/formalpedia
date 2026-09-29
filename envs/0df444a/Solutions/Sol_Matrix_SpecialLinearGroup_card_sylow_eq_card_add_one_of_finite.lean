-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/18113531-9b15-54d2-ae3d-52fa49e73480

import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import Theorems.Thm_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite
import Theorems.Thm_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite

set_option autoImplicit false

open Matrix MatrixGroups ModularCurve

namespace P2mDicksonCore

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

def tr (M : 𝕄) : K := M 0 0 + M 1 1

lemma sq_eq (g : 𝕄) : g * g = tr g • g - g.det • (1 : 𝕄) := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma tr_mul_comm (a b : 𝕄) : tr (a * b) = tr (b * a) := by
  simp [tr, Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma tr_conj {a b c : 𝕄} (h : c * a = 1) : tr (a * b * c) = tr b := by
  rw [tr_mul_comm, ← mul_assoc, h, one_mul]

lemma tr_one : tr (1 : 𝕄) = 2 := by simp [tr]; norm_num

lemma tr_neg (a : 𝕄) : tr (-a) = -tr a := by simp [tr]; ring

lemma coe_inv_eq (s : SL(2, K)) : ((s⁻¹ : SL(2, K)) : 𝕄) = tr (s : 𝕄) • (1 : 𝕄) - s := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.eta_fin_two (s : 𝕄)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [tr]

section Tori

variable {H : Type} [Group H] (ρ : H →* SL(2, K))

abbrev mat (h : H) : 𝕄 := ((ρ h : SL(2, K)) : 𝕄)

lemma mat_mul (a b : H) : mat ρ (a * b) = mat ρ a * mat ρ b := by
  simp [mat, map_mul]

lemma mat_one : mat ρ (1 : H) = 1 := by simp [mat]

def Zsub : Subgroup H where
  carrier := {h | mat ρ h = 1 ∨ mat ρ h = -1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, mat, map_mul, Matrix.SpecialLinearGroup.coe_mul] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  one_mem' := by simp [mat]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, mat, map_inv] at ha ⊢
    rw [coe_inv_eq]
    rcases ha with ha | ha
    · left; rw [ha, tr_one]; ext i j; fin_cases i <;> fin_cases j <;> norm_num
    · right; rw [ha, tr_neg, tr_one]; ext i j; fin_cases i <;> fin_cases j <;> norm_num

variable {ρ}

def IsSS (ρ : H →* SL(2, K)) (h : H) : Prop := (tr (mat ρ h)) ^ 2 ≠ 4

abbrev torus (h : H) : Subgroup H := Subgroup.centralizer {h}

lemma mem_torus_iff (h g : H) : g ∈ torus h ↔ g * h = h * g := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact ⟨fun e => e.symm, fun e => e.symm⟩

variable (hρ : Function.Injective ρ)
include hρ

lemma mat_injective : Function.Injective (mat ρ) := fun _ _ h =>
  hρ (Subtype.ext h)

lemma mem_torus_iff_mat (h g : H) : g ∈ torus h ↔ mat ρ g * mat ρ h = mat ρ h * mat ρ g := by
  rw [mem_torus_iff]
  constructor
  · intro e
    have := congrArg (mat ρ) e
    simpa [mat, map_mul] using this
  · intro e
    apply mat_injective hρ
    simpa [mat, map_mul] using e

lemma Zsub_le_torus (h : H) : Zsub ρ ≤ torus h := by
  intro g hg
  rw [mem_torus_iff_mat hρ]
  rcases hg with hg | hg <;> rw [hg] <;> simp

omit hρ in
lemma self_mem_torus (h : H) : h ∈ torus h := (mem_torus_iff h h).mpr rfl

lemma isSS_of_mem_torus [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {g : H}
    (hg : g ∈ torus h) (hgZ : g ∉ Zsub ρ) : IsSS ρ g :=
  ((Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite h2 ρ hρ h hh).2.1
    g hg hgZ).2

lemma card_normalizer_le [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) :
    Nat.card (Subgroup.normalizer (torus h : Set H)) ≤ 2 * Nat.card (torus h) :=
  (Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite h2 ρ hρ h hh).2.2.1

omit hρ in
lemma mat_inv_mul (y : H) : mat ρ y⁻¹ * mat ρ y = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]

lemma Zsub_eq_of_apply {ζ ζ' : H} (hζ : ζ ∈ Zsub ρ) (hζ' : ζ' ∈ Zsub ρ)
    (h : mat ρ ζ 0 0 = mat ρ ζ' 0 0) (h2 : (2 : K) ≠ 0) : ζ = ζ' := by
  apply mat_injective hρ
  rcases hζ with e | e <;> rcases hζ' with e' | e' <;> rw [e, e'] at h ⊢ <;> simp at h ⊢
  · exact absurd (by linear_combination h : (2 : K) = 0) h2
  · exact absurd (by linear_combination -h : (2 : K) = 0) h2

omit hρ in

lemma card_subtype_add_card_subtype_not {α : Type} [Finite α] (q : α → Prop) :
    Nat.card {x // q x} + Nat.card {x // ¬ q x} = Nat.card α := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl q)]

end Tori

section Classes

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)

def IsConjSub (M M' : Subgroup H) : Prop := ∃ s : H, ∀ g : H, g ∈ M' ↔ s⁻¹ * g * s ∈ M

lemma IsConjSub.refl (M : Subgroup H) : IsConjSub M M := ⟨1, fun g => by simp⟩

lemma IsConjSub.symm {M M' : Subgroup H} (h : IsConjSub M M') : IsConjSub M' M := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s⁻¹, fun g => ?_⟩
  rw [hs, inv_inv, show s⁻¹ * (s * g * s⁻¹) * s = g by group]

lemma IsConjSub.trans {M M' M'' : Subgroup H} (h : IsConjSub M M') (h' : IsConjSub M' M'') :
    IsConjSub M M'' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := h'
  refine ⟨t * s, fun g => ?_⟩
  rw [ht, hs, show s⁻¹ * (t⁻¹ * g * t) * s = (t * s)⁻¹ * g * (t * s) by group]

variable (ρ)

def classSet (M : Subgroup H) : Set H := {x | x ∉ Zsub ρ ∧ IsConjSub M (torus x)}

variable {ρ}

lemma mem_classSet_iff (M : Subgroup H) (x : H) :
    x ∈ classSet ρ M ↔ x ∉ Zsub ρ ∧ IsConjSub M (torus x) := Iff.rfl

lemma classSet_eq_of_mem {M M' : Subgroup H} {x : H} (hx : x ∈ classSet ρ M)
    (hx' : x ∈ classSet ρ M') : classSet ρ M = classSet ρ M' := by
  have hMM' : IsConjSub M M' := hx.2.trans hx'.2.symm
  ext y
  rw [mem_classSet_iff, mem_classSet_iff]
  exact ⟨fun h => ⟨h.1, hMM'.symm.trans h.2⟩, fun h => ⟨h.1, hMM'.trans h.2⟩⟩

include hρ in
lemma not_mem_Zsub_of_isSS {x : H} (hx : IsSS ρ x) : x ∉ Zsub ρ := by
  intro h
  apply hx
  rcases h with e | e <;> rw [e]
  · rw [tr_one]; norm_num
  · rw [tr_neg, tr_one]; norm_num

include hρ in
lemma self_mem_classSet {x : H} (hx : IsSS ρ x) : x ∈ classSet ρ (torus x) :=
  ⟨not_mem_Zsub_of_isSS hρ hx, IsConjSub.refl _⟩

include hρ in

lemma isSS_of_mem_classSet [Finite H] (h2' : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {x : H} (hx : x ∈ classSet ρ (torus h)) :
    IsSS ρ x := by
  obtain ⟨hxZ, s, hs⟩ := hx

  have h1 : s * h * s⁻¹ ∈ torus x := (hs _).mpr (by
    rw [show s⁻¹ * (s * h * s⁻¹) * s = h by group]; exact self_mem_torus h)
  have hss : IsSS ρ (s * h * s⁻¹) := by
    change (tr (mat ρ (s * h * s⁻¹))) ^ 2 ≠ 4
    rw [mat_mul, mat_mul, tr_conj (mat_inv_mul s)]; exact hh
  have h2 : x ∈ torus (s * h * s⁻¹) := by
    rw [mem_torus_iff]; exact ((mem_torus_iff x _).mp h1).symm
  exact isSS_of_mem_torus hρ h2' hss h2 hxZ

include hρ in

lemma card_classSet_mul [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) :
    Nat.card (classSet ρ (torus h)) * Nat.card (Subgroup.normalizer (torus h : Set H)) =
      Nat.card H * (Nat.card (torus h) - Nat.card (Zsub ρ)) :=
  (Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite h2 ρ hρ h hh).2.2.2

end Classes

structure NormData {H : Type} [Group H] (ρ : H →* SL(2, K)) {p : ℕ} (P : Sylow p H) : Prop where
  hP : ∀ x : H, x ∈ P ↔ ∃ t : K, ρ x = upperElem t
  exists_ne : ∃ a : K, a ≠ 0 ∧ ∃ u : H, mat ρ u = !![1, a; 0, 1]

section Borel

variable {H : Type} [Group H] {ρ : H →* SL(2, K)}
variable {p : ℕ} {P : Sylow p H} (D : NormData ρ P)

include D in
lemma mat_of_mem_P {x : H} (hx : x ∈ P) : ∃ t : K, mat ρ x = !![1, t; 0, 1] := by
  obtain ⟨t, ht⟩ := (D.hP x).mp hx
  exact ⟨t, by rw [mat, ht, upperElem_coe]⟩

include D in
lemma mem_P_of_mat {x : H} {t : K} (hx : mat ρ x = !![1, t; 0, 1]) : x ∈ P :=
  (D.hP x).mpr ⟨t, Subtype.ext hx⟩

end Borel

section Unipotent

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)
variable {p : ℕ} [Fact p.Prime] [CharP K p] {P : Sylow p H} (D : NormData ρ P)

lemma sq_eq_zero_of_pow_eq_zero {N : 𝕄} {m : ℕ} (hm : N ^ m = 0) : N ^ 2 = 0 := by
  have hCH : N ^ 2 = tr N • N - N.det • (1 : 𝕄) := by rw [pow_two]; exact sq_eq N
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact one_ne_zero hm
  have hdet : N.det = 0 := by
    have : N.det ^ m = 0 := by rw [← Matrix.det_pow, hm, Matrix.det_zero]
    exact pow_eq_zero_iff hm0 |>.mp this
  rw [hdet, zero_smul, sub_zero] at hCH
  have hpow : ∀ k : ℕ, N ^ (k + 1) = (tr N) ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, smul_mul_assoc, ← pow_two, hCH, smul_smul, ← pow_succ]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  rw [hpow k] at hm
  rcases smul_eq_zero.mp hm with htk | hN
  · have ht0 : tr N = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at htk
      · exact pow_eq_zero_iff hk.ne' |>.mp htk
    rw [hCH, ht0, zero_smul]
  · rw [hN, pow_two, mul_zero]

lemma unip_of_pow_eq_one {x : H} {k : ℕ} (hx : x ^ p ^ k = 1) : (mat ρ x - 1) ^ 2 = 0 := by
  have hM : (mat ρ x) ^ p ^ k = 1 := by
    rw [mat, ← Matrix.SpecialLinearGroup.coe_pow, ← map_pow, hx, map_one]; rfl
  have hN : (mat ρ x - 1) ^ p ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right (mat ρ x)), hM, one_pow, sub_self]
  exact sq_eq_zero_of_pow_eq_zero hN

lemma sq_sub_one_apply (M : 𝕄) :
    ((M - 1) ^ 2 : 𝕄) 0 0 = (M 0 0 - 1) * (M 0 0 - 1) + M 0 1 * M 1 0 ∧
    ((M - 1) ^ 2 : 𝕄) 0 1 = (M 0 0 - 1) * M 0 1 + M 0 1 * (M 1 1 - 1) ∧
    ((M - 1) ^ 2 : 𝕄) 1 0 = M 1 0 * (M 0 0 - 1) + (M 1 1 - 1) * M 1 0 ∧
    ((M - 1) ^ 2 : 𝕄) 1 1 = M 1 0 * M 0 1 + (M 1 1 - 1) * (M 1 1 - 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.sub_apply]

lemma tr_of_unip {M : 𝕄} (h : (M - 1) ^ 2 = 0) : tr M = 2 := by
  rw [tr]
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

lemma unip_of_tr {M : 𝕄} (hdet : M.det = 1) (h : tr M = 2) : (M - 1) ^ 2 = 0 := by
  rw [tr] at h
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨h00, h01, h10, h11⟩ := sq_sub_one_apply M
  rw [Matrix.eta_fin_two ((M - 1) ^ 2), h00, h01, h10, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination M 0 0 * h - hdet
  · linear_combination M 0 1 * h
  · linear_combination M 1 0 * h
  · linear_combination M 1 1 * h - hdet

lemma unip_pow {M : 𝕄} (h : (M - 1) ^ 2 = 0) (n : ℕ) : M ^ n = 1 + (n : K) • (M - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, Nat.cast_succ, add_smul, one_smul, smul_mul_assoc]
    have : (M - 1) * M = (M - 1) := by
      have e : (M - 1) * M = (M - 1) * (M - 1) + (M - 1) := by noncomm_ring
      rw [e, ← pow_two, h, zero_add]
    rw [this]; abel

include hρ in

lemma pow_p_eq_one_of_unip {x : H} (h : (mat ρ x - 1) ^ 2 = 0) : x ^ p = 1 := by
  apply mat_injective hρ
  rw [mat, map_pow, Matrix.SpecialLinearGroup.coe_pow, show ((ρ x : SL(2, K)) : 𝕄) = mat ρ x
    from rfl, unip_pow h, CharP.cast_eq_zero, zero_smul, add_zero, mat_one]

lemma eq_upper_of_unip_mul_upper {M : 𝕄} (hM : (M - 1) ^ 2 = 0) {a : K}
    (ha : a ≠ 0) (hMa : (M * !![1, a; 0, 1] - 1) ^ 2 = 0) : M = !![1, M 0 1; 0, 1] := by
  have htr := tr_of_unip hM
  have htr' := tr_of_unip hMa
  simp [tr, Matrix.mul_apply, Fin.sum_univ_two] at htr'
  rw [tr] at htr
  have e10 : M 1 0 = 0 := by
    have : a * M 1 0 = 0 := by linear_combination htr' - htr
    exact (mul_eq_zero.mp this).resolve_left ha

  have h00 := congrFun (congrFun hM 0) 0
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00
  simp [Matrix.sub_apply, e10] at h00
  have e00 : M 0 0 = 1 := by linear_combination h00
  have e11 : M 1 1 = 1 := by linear_combination htr - e00
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [e00, e10, e11]

include hρ D in

lemma sylow_eq_of_mem_inf {Q : Sylow p H} {y : H} (hyP : y ∈ P) (hyQ : y ∈ Q) (hy1 : y ≠ 1) :
    Q = P := by
  obtain ⟨t, ht⟩ := mat_of_mem_P D hyP
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hy1
    apply mat_injective hρ
    rw [ht, mat_one]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hle : (Q : Subgroup H) ≤ P := by
    intro g hg
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨g, hg⟩
    have hgk : g ^ p ^ k = 1 := by
      have := congrArg (fun z : Q => (z : H)) hk; simpa using this
    obtain ⟨k', hk'⟩ := Q.isPGroup' ⟨g * y, Q.mul_mem hg hyQ⟩
    have hgyk : (g * y) ^ p ^ k' = 1 := by
      have := congrArg (fun z : Q => (z : H)) hk'; simpa using this
    have h1 := unip_of_pow_eq_one (ρ := ρ) hgk
    have h2 := unip_of_pow_eq_one (ρ := ρ) hgyk
    rw [mat_mul, ht] at h2
    exact mem_P_of_mat D (eq_upper_of_unip_mul_upper h1 ht0 h2)
  exact Sylow.ext (Q.is_maximal' P.isPGroup' hle).symm

include hρ D in

lemma sylow_eq_of_mem_of_mem [Finite H] {Q Q' : Sylow p H} {y : H} (hyQ : y ∈ Q) (hyQ' : y ∈ Q')
    (hy1 : y ≠ 1) : Q = Q' := by
  haveI : MulAction.IsPretransitive H (Sylow p H) := inferInstance
  obtain ⟨s, rfl⟩ := MulAction.exists_smul_eq H P Q
  have h1 : s⁻¹ * y * s ∈ (P : Subgroup H) := by
    have : y ∈ ((s • P : Sylow p H) : Subgroup H) := hyQ
    rw [Sylow.coe_subgroup_smul] at this
    obtain ⟨u, hu, e⟩ := this
    change s * u * s⁻¹ = y at e
    rw [← e, show s⁻¹ * (s * u * s⁻¹) * s = u by group]; exact hu
  have h2 : s⁻¹ * y * s ∈ ((s⁻¹ • Q' : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]; exact ⟨y, hyQ', by change s⁻¹ * y * s⁻¹⁻¹ = _; rw [inv_inv]⟩
  have h3 : s⁻¹ * y * s ≠ 1 := by
    intro h; apply hy1
    calc y = s * (s⁻¹ * y * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group
  have := sylow_eq_of_mem_inf hρ D h1 h2 h3
  rw [inv_smul_eq_iff] at this
  exact this.symm

include D in
omit [Fact p.Prime] [CharP K p] in

lemma tr_eq_two_of_mem_sylow [Finite H] [Fact p.Prime] {Q : Sylow p H} {y : H} (hy : y ∈ Q) :
    tr (mat ρ y) = 2 := by
  haveI : MulAction.IsPretransitive H (Sylow p H) := inferInstance
  obtain ⟨s, rfl⟩ := MulAction.exists_smul_eq H P Q
  have : y ∈ ((s • P : Sylow p H) : Subgroup H) := hy
  rw [Sylow.coe_subgroup_smul] at this
  obtain ⟨u, hu, e⟩ := this
  change s * u * s⁻¹ = y at e
  obtain ⟨t, ht⟩ := mat_of_mem_P D hu
  rw [← e, mat_mul, mat_mul, tr_conj (mat_inv_mul s), ht]
  simp [tr]; norm_num

include hρ in

lemma tr_sq_of_Zsub_mul {ζ x : H} (hζ : ζ ∈ Zsub ρ) : (tr (mat ρ (ζ * x))) ^ 2 = (tr (mat ρ x)) ^ 2 := by
  rw [mat_mul]
  rcases hζ with e | e <;> rw [e]
  · rw [one_mul]
  · rw [neg_one_mul, tr_neg]; ring

include hρ D in

lemma card_not_isSS [Finite H] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) :
    Nat.card {x : H // ¬ IsSS ρ x} =
      Nat.card (Zsub ρ) * (1 + Nat.card (Sylow p H) * (Nat.card P - 1)) := by
  classical

  let Ψ : Zsub ρ × Option (Σ Q : Sylow p H, {y : Q // y ≠ 1}) → {x : H // ¬ IsSS ρ x} :=
    fun a => match a with
    | (ζ, none) => ⟨ζ, by
        rw [IsSS, not_not]
        rcases ζ.2 with e | e <;> rw [e]
        · rw [tr_one]; norm_num
        · rw [tr_neg, tr_one]; norm_num⟩
    | (ζ, some ⟨Q, y⟩) => ⟨(ζ : H) * y, by
        rw [IsSS, not_not, tr_sq_of_Zsub_mul hρ ζ.2, tr_eq_two_of_mem_sylow D y.1.2]; norm_num⟩
  have hΨ1 : ∀ ζ : Zsub ρ, (Ψ (ζ, none) : H) = ζ := fun ζ => rfl
  have hΨ2 : ∀ (ζ : Zsub ρ) (Q : Sylow p H) (y : {y : Q // y ≠ 1}),
      (Ψ (ζ, some ⟨Q, y⟩) : H) = ζ * y := fun ζ Q y => rfl

  have hsign : ∀ (ζ ζ' : Zsub ρ) (x x' : H), tr (mat ρ x) = 2 → tr (mat ρ x') = 2 →
      (ζ : H) * x = ζ' * x' → ζ = ζ' := by
    intro ζ ζ' x x' hx hx' e
    have := congrArg (fun w => tr (mat ρ w)) e
    simp only [mat_mul] at this
    apply Subtype.ext
    refine Zsub_eq_of_apply hρ ζ.2 ζ'.2 ?_ h2
    rcases ζ.2 with e1 | e1 <;> rcases ζ'.2 with e2 | e2 <;>
      rw [e1, e2] at this ⊢ <;> simp only [one_mul, neg_one_mul, neg_mul, tr_neg, hx, hx'] at this ⊢
    · exfalso; exact h2 (mul_self_eq_zero.mp (by linear_combination this))
    · exfalso; exact h2 (mul_self_eq_zero.mp (by linear_combination -this))
  have hinj : Function.Injective Ψ := by
    rintro ⟨ζ, _ | ⟨Q, y⟩⟩ ⟨ζ', _ | ⟨Q', y'⟩⟩ h <;> have hv := congrArg Subtype.val h
    · rw [hΨ1, hΨ1] at hv
      rw [Subtype.ext hv]
    · exfalso
      rw [hΨ1, hΨ2] at hv
      have hζζ : ζ = ζ' := hsign ζ ζ' 1 y' (by rw [mat_one, tr_one])
        (tr_eq_two_of_mem_sylow D y'.1.2) (by rw [mul_one]; exact hv)
      subst hζζ
      have : ((y'.1 : Q') : H) = 1 := (mul_left_cancel (hv.symm.trans (mul_one _).symm))
      exact y'.2 (Subtype.ext this)
    · exfalso
      rw [hΨ1, hΨ2] at hv
      have hζζ : ζ = ζ' := hsign ζ ζ' y 1 (tr_eq_two_of_mem_sylow D y.1.2)
        (by rw [mat_one, tr_one]) (by rw [mul_one]; exact hv)
      subst hζζ
      have : ((y.1 : Q) : H) = 1 := (mul_left_cancel (hv.trans (mul_one _).symm))
      exact y.2 (Subtype.ext this)
    · rw [hΨ2, hΨ2] at hv
      have hζζ : ζ = ζ' := hsign ζ ζ' y y' (tr_eq_two_of_mem_sylow D y.1.2)
        (tr_eq_two_of_mem_sylow D y'.1.2) hv
      subst hζζ
      have hyy : ((y.1 : Q) : H) = y'.1 := mul_left_cancel hv
      have hQQ : Q = Q' := sylow_eq_of_mem_of_mem hρ D y.1.2 (by rw [hyy]; exact y'.1.2)
        (fun h1 => y.2 (Subtype.ext h1))
      subst hQQ
      have : y = y' := Subtype.ext (Subtype.ext hyy)
      subst this
      rfl
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨x, hx⟩
    rw [IsSS, not_not] at hx
    have hx' : (tr (mat ρ x) - 2) * (tr (mat ρ x) + 2) = 0 := by linear_combination hx
    by_cases hxZ : x ∈ Zsub ρ
    · exact ⟨(⟨x, hxZ⟩, none), rfl⟩
    rcases mul_eq_zero.mp hx' with e | e
    ·
      have htr : tr (mat ρ x) = 2 := by linear_combination e
      have hunip := unip_of_tr (ρ x).2 htr
      have hxp := pow_p_eq_one_of_unip hρ hunip
      have hpg : IsPGroup p (Subgroup.zpowers x) := by
        intro g
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
        refine ⟨1, Subtype.ext ?_⟩
        simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hxp, _root_.one_zpow]
      obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
      have hxQ : x ∈ Q := hQ (Subgroup.mem_zpowers x)
      refine ⟨(⟨1, (Zsub ρ).one_mem⟩, some ⟨Q, ⟨⟨x, hxQ⟩, fun h => hxZ ?_⟩⟩), ?_⟩
      · have : x = 1 := congrArg Subtype.val h
        rw [this]; exact (Zsub ρ).one_mem
      · apply Subtype.ext; rw [hΨ2]; exact one_mul x
    ·
      have htr : tr (mat ρ x) = -2 := by linear_combination e
      have hunip : (-mat ρ x - 1) ^ 2 = 0 := by
        refine unip_of_tr ?_ ?_
        · rw [Matrix.det_neg, (ρ x).2]; norm_num
        · rw [tr_neg, htr]; norm_num
      have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
      have hζ : mat ρ (x ^ p) = -1 := by
        rw [mat, map_pow, Matrix.SpecialLinearGroup.coe_pow, show ((ρ x : SL(2, K)) : 𝕄) = mat ρ x
          from rfl, show mat ρ x = -(-mat ρ x) by rw [neg_neg], neg_pow, hodd.neg_one_pow,
          unip_pow hunip, CharP.cast_eq_zero, zero_smul, add_zero]
        simp
      have hζZ : x ^ p ∈ Zsub ρ := Or.inr hζ
      set y := (x ^ p)⁻¹ * x with hy
      have hmy : mat ρ y = -mat ρ x := by
        rw [hy, mat_mul, mat, map_inv, coe_inv_eq, show ((ρ (x ^ p) : SL(2, K)) : 𝕄) = mat ρ (x ^ p)
          from rfl, hζ, tr_neg, tr_one]
        have : ((-2 : K) • (1 : 𝕄) - -1) = -1 := by
          ext i j; fin_cases i <;> fin_cases j <;> norm_num
        rw [this, neg_one_mul]
      have hyunip : (mat ρ y - 1) ^ 2 = 0 := by rw [hmy]; exact hunip
      have hyp := pow_p_eq_one_of_unip hρ hyunip
      have hpg : IsPGroup p (Subgroup.zpowers y) := by
        intro g
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
        refine ⟨1, Subtype.ext ?_⟩
        simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hyp, _root_.one_zpow]
      obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
      have hyQ : y ∈ Q := hQ (Subgroup.mem_zpowers y)
      have hyZ : y ∉ Zsub ρ := by
        intro h
        apply hxZ
        have : x = x ^ p * y := by rw [hy]; group
        rw [this]; exact (Zsub ρ).mul_mem hζZ h
      refine ⟨(⟨x ^ p, hζZ⟩, some ⟨Q, ⟨⟨y, hyQ⟩, fun h => hyZ ?_⟩⟩), ?_⟩
      · have : y = 1 := congrArg Subtype.val h
        rw [this]; exact (Zsub ρ).one_mem
      · apply Subtype.ext; rw [hΨ2]; change x ^ p * y = x; rw [hy]; group

  rw [← Nat.card_eq_of_bijective Ψ ⟨hinj, hsurj⟩, Nat.card_prod, Finite.card_option]
  congr 1
  rw [add_comm]
  congr 1
  letI : Fintype (Sylow p H) := Fintype.ofFinite _
  rw [Nat.card_sigma]
  have : ∀ Q : Sylow p H, Nat.card {y : Q // y ≠ 1} = Nat.card P - 1 := by
    intro Q
    have h1 : Nat.card {y : Q // y ≠ 1} + 1 = Nat.card Q := by
      rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe (1 : Q))]; rfl
    have h2 : Nat.card Q = Nat.card P := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    omega
  rw [Finset.sum_congr rfl (fun Q _ => this Q), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_eq_nat_card]

end Unipotent

end P2mDicksonCore

namespace P2mDicksonCoreArith

lemma case_cbar_one (n q z S w : ℕ) (hq : 4 ≤ q) (hn : 2 ≤ n) (hz : 0 < z)
    (hS : S + z * (1 + n * (q - 1)) = n * q * z)
    (hw : n * q * z ≤ 4 * w) (hwS : w ≤ S) : False := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hS

  have hS' : S + z = z * n := by nlinarith [hS]
  nlinarith [hS', hw, hwS, hz, hn, hq]

lemma case_cbar_one_empty (n q z : ℕ) (hn : 2 ≤ n) (hz : 0 < z)
    (hS : z * (1 + n * (q - 1)) = n * q * z) : False := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at hS; nlinarith
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hS
  nlinarith

lemma case_eC_one (n q z c S wC w : ℕ) (hq : 4 ≤ q) (hn : 2 ≤ n) (hz : 0 < z) (hzc : 2 * z ≤ c)
    (hS : S + z * (1 + n * (q - 1)) = n * q * c)
    (hwC : wC * c = n * q * c * (c - z))
    (hw : n * q * c ≤ 4 * w) (hsum : wC + w ≤ S) : False := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + z := ⟨c - z, by omega⟩
  simp only [Nat.add_sub_cancel] at hS hwC
  have hc : 0 < c' + z := by omega
  have hwC' : wC = n * (q' + 1) * c' := by
    have : wC * (c' + z) = (n * (q' + 1) * c') * (c' + z) := by rw [hwC]; ring
    exact Nat.eq_of_mul_eq_mul_right hc this
  subst hwC'
  have F2 : z * (n * q') ≤ c' * (n * q') := Nat.mul_le_mul_right _ (by omega : z ≤ c')
  have F3 : z * n ≤ c' * n := Nat.mul_le_mul_right _ (by omega)
  have F4 : 3 * (n * z) ≤ q' * (n * z) := Nat.mul_le_mul_right _ (by omega : 3 ≤ q')
  have F5 : 2 * z ≤ n * z := Nat.mul_le_mul_right _ hn
  nlinarith [hS, hw, hsum, hz, hn, hq, hzc, F2, F3, F4, F5]

lemma case_eC_two_no_third (n q z c S wC w w' : ℕ) (hq : 4 ≤ q) (hn : 2 ≤ n) (hz : 0 < z)
    (hzc : 2 * z ≤ c)
    (hS : S + z * (1 + n * (q - 1)) = n * q * c)
    (hwC : wC * (2 * c) = n * q * c * (c - z))
    (hw : n * q * c ≤ 4 * w) (hw' : n * q * c ≤ 4 * w') (hsum : wC + w + w' ≤ S) : False := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + z := ⟨c - z, by omega⟩
  simp only [Nat.add_sub_cancel] at hS hwC
  have hc : 0 < c' + z := by omega
  have hwC2 : wC * 2 = n * (q' + 1) * c' := by
    have : (wC * 2) * (c' + z) = (n * (q' + 1) * c') * (c' + z) := by
      calc (wC * 2) * (c' + z) = wC * (2 * (c' + z)) := by ring
        _ = _ := by rw [hwC]; ring
    exact Nat.eq_of_mul_eq_mul_right hc this
  have F2 : z * (n * q') ≤ c' * (n * q') := Nat.mul_le_mul_right _ (by omega : z ≤ c')
  have F3 : z * n ≤ c' * n := Nat.mul_le_mul_right _ (by omega)
  have F4 : 3 * (n * z) ≤ q' * (n * z) := Nat.mul_le_mul_right _ (by omega : 3 ≤ q')
  have F5 : 2 * z ≤ n * z := Nat.mul_le_mul_right _ hn
  have F6 : 3 * (n * c') ≤ q' * (n * c') := Nat.mul_le_mul_right _ (by omega : 3 ≤ q')
  nlinarith [hS, hwC2, hw, hw', hsum, hz, hn, hq, hzc, F2, F3, F4, F5, F6]

lemma two_w_eq (n q' z cb₁ S wC w : ℕ) (hn : 1 ≤ n) (hz : 0 < z)
    (hS : S + z * (1 + n * q') = n * (q' + 1) * (z * (cb₁ + 1)))
    (hwC : wC * (2 * (z * (cb₁ + 1))) = n * (q' + 1) * (z * (cb₁ + 1)) * (z * (cb₁ + 1) - z))
    (hsum : wC + w = S) :
    2 * w = z * (n * (q' + 1) * cb₁ + 2 * n - 2) := by
  have hzc : 0 < z * (cb₁ + 1) := Nat.mul_pos hz (Nat.succ_pos _)
  have hsub : z * (cb₁ + 1) - z = z * cb₁ := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hsub] at hwC
  have hwC2 : wC * 2 = n * (q' + 1) * (z * cb₁) := by
    have : (wC * 2) * (z * (cb₁ + 1)) = (n * (q' + 1) * (z * cb₁)) * (z * (cb₁ + 1)) := by
      calc (wC * 2) * (z * (cb₁ + 1)) = wC * (2 * (z * (cb₁ + 1))) := by ring
        _ = _ := by rw [hwC]; ring
    exact Nat.eq_of_mul_eq_mul_right hzc this
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Nat.mul_succ 2 n', ← add_assoc, Nat.add_sub_cancel]
  nlinarith [hS, hwC2, hsum]

lemma case_eC_two_e_one (n q z cb m S wC w : ℕ) (hq : 4 ≤ q) (hn : 2 ≤ n) (hz : 0 < z)
    (hcb : 2 ≤ cb) (hzm : 2 * z ≤ m)
    (hS : S + z * (1 + n * (q - 1)) = n * q * (z * cb))
    (hwC : wC * (2 * (z * cb)) = n * q * (z * cb) * (z * cb - z)) (hsum : wC + w = S)
    (hw : w * m = n * q * (z * cb) * (m - z)) : False := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨cb₁, rfl⟩ : ∃ cb₁, cb = cb₁ + 1 := ⟨cb - 1, by omega⟩
  obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + z := ⟨m - z, by omega⟩
  simp only [Nat.add_sub_cancel] at hS hw
  have h2w := two_w_eq n q' z cb₁ S wC w (by omega) hz hS hwC hsum

  set A := n * (q' + 1) * cb₁ + 2 * n - 2 with hA
  have key : A * (m₁ + z) = 2 * (n * (q' + 1) * (cb₁ + 1) * m₁) := by
    have : (2 * w) * (m₁ + z) = 2 * (n * (q' + 1) * (z * (cb₁ + 1)) * m₁) := by rw [mul_assoc, hw]
    rw [h2w] at this
    have this' : z * (A * (m₁ + z)) = z * (2 * (n * (q' + 1) * (cb₁ + 1) * m₁)) := by
      calc z * (A * (m₁ + z)) = z * A * (m₁ + z) := by ring
        _ = 2 * (n * (q' + 1) * (z * (cb₁ + 1)) * m₁) := this
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left hz this'
  have hm₁ : z ≤ m₁ := by omega
  have hnq : n ≤ n * q' := Nat.le_mul_of_pos_right n (by omega)
  have hA' : A + 4 ≤ n * (q' + 1) * cb₁ + 2 * (n * q') + 2 := by rw [hA]; omega

  have e : A * z = m₁ * (n * (q' + 1) * cb₁ + 2 * (n * q') + 2) := by
    have hAdef : A + 2 = n * (q' + 1) * cb₁ + 2 * n := by rw [hA]; omega
    nlinarith [key, hAdef]
  have : A * z < m₁ * (n * (q' + 1) * cb₁ + 2 * (n * q') + 2) := by
    calc A * z < (A + 4) * z := by nlinarith
      _ ≤ (n * (q' + 1) * cb₁ + 2 * (n * q') + 2) * z := Nat.mul_le_mul_right _ hA'
      _ ≤ (n * (q' + 1) * cb₁ + 2 * (n * q') + 2) * m₁ := Nat.mul_le_mul_left _ hm₁
      _ = _ := by ring
  omega

lemma case_eC_two_e_two (n q z cb m S wC w k : ℕ) (hq : 4 ≤ q) (hn : 2 ≤ n) (hz : 0 < z)
    (hcb : 2 ≤ cb) (hzm : 2 * z ≤ m) (hzdvd : z ∣ m)
    (hS : S + z * (1 + n * (q - 1)) = n * q * (z * cb))
    (hwC : wC * (2 * (z * cb)) = n * q * (z * cb) * (z * cb - z)) (hsum : wC + w = S)
    (hw : w * (2 * m) = n * q * (z * cb) * (m - z)) (hfree : m ∣ z * n)
    (hk : n = 1 + q + k * (q * cb)) : k = 0 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨cb₁, rfl⟩ : ∃ cb₁, cb = cb₁ + 1 := ⟨cb - 1, by omega⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, m = z * (μ + 1) := by
    obtain ⟨j, hj⟩ := hzdvd
    refine ⟨j - 1, ?_⟩
    have : 1 ≤ j := by
      by_contra h0; push Not at h0
      have : j = 0 := by omega
      subst this; omega
    rw [hj]; congr; omega
  subst hμ
  simp only [Nat.add_sub_cancel] at hS
  have h2w := two_w_eq n q' z cb₁ S wC w (by omega) hz hS hwC hsum

  have hsub : z * (μ + 1) - z = z * μ := by rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hsub] at hw
  have key : (n * (q' + 1) * cb₁ + 2 * n - 2) * (μ + 1) = n * (q' + 1) * (cb₁ + 1) * μ := by
    have : (2 * w) * (z * (μ + 1)) = n * (q' + 1) * (z * (cb₁ + 1)) * (z * μ) := by
      calc (2 * w) * (z * (μ + 1)) = w * (2 * (z * (μ + 1))) := by ring
        _ = _ := hw
    rw [h2w] at this
    have hzz : 0 < z * z := Nat.mul_pos hz hz
    have this' : (z * z) * ((n * (q' + 1) * cb₁ + 2 * n - 2) * (μ + 1)) =
        (z * z) * (n * (q' + 1) * (cb₁ + 1) * μ) := by
      calc (z * z) * ((n * (q' + 1) * cb₁ + 2 * n - 2) * (μ + 1))
          = z * (n * (q' + 1) * cb₁ + 2 * n - 2) * (z * (μ + 1)) := by ring
        _ = n * (q' + 1) * (z * (cb₁ + 1)) * (z * μ) := this
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left hzz this'

  have hdvd : μ + 1 ∣ n := by
    have : z * (μ + 1) ∣ z * n := hfree
    exact (Nat.mul_dvd_mul_iff_left hz).mp this
  obtain ⟨r, hr⟩ := hdvd

  obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
  have key2 : r * ((q'' + 1 + 1) * (cb₁ + 1)) = r * (μ + 1) * q'' + 2 := by

    subst hr
    have e2 : (μ + 1) * r * (q'' + 1 + 1) * cb₁ + 2 * ((μ + 1) * r) - 2 =
        (μ + 1) * r * (q'' + 2) * cb₁ + 2 * ((μ + 1) * r) - 2 := by ring_nf
    have hpos : 1 ≤ (μ + 1) * r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp at hn
      · exact Nat.mul_pos (Nat.succ_pos _) hr0
    have hμ1 : 0 < μ + 1 := Nat.succ_pos _
    apply Nat.eq_of_mul_eq_mul_left hμ1
    have e3 : ((μ + 1) * r * (q'' + 1 + 1) * cb₁ + 2 * ((μ + 1) * r) - 2) + 2 =
        (μ + 1) * r * (q'' + 2) * cb₁ + 2 * ((μ + 1) * r) := by omega
    nlinarith [key, e3]
  have hr2 : r ∣ 2 := by
    have : r ∣ r * (μ + 1) * q'' + 2 := by rw [← key2]; exact dvd_mul_right r _
    have h1 : r ∣ r * (μ + 1) * q'' := by rw [mul_assoc]; exact dvd_mul_right r _
    exact (Nat.dvd_add_right h1).mp this
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · rw [hr, mul_zero] at hn; omega
    · exact h
  have hr12 : r = 1 ∨ r = 2 := by
    have := Nat.le_of_dvd (by norm_num) hr2
    interval_cases r
    · left; rfl
    · right; rfl

  by_contra hk0
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  set X := (q'' + 1 + 1) * (cb₁ + 1) with hX
  have hbig : X ≤ k * X := by
    calc X = 1 * X := (one_mul X).symm
      _ ≤ k * X := Nat.mul_le_mul_right _ hk1
  have hnX : X < n := by rw [hk]; omega
  have hq2 : 2 ≤ q'' := by omega
  have hnq : n * 2 ≤ n * q'' := Nat.mul_le_mul_left n hq2
  rcases hr12 with rfl | rfl
  ·
    simp only [one_mul] at key2
    have hnμ : n = μ + 1 := by rw [hr, mul_one]
    rw [← hnμ] at key2

    linarith
  · rw [show 2 * (μ + 1) * q'' = n * q'' by rw [hr]; ring] at key2
    linarith

lemma case_eC_one_empty (n q z c S wC : ℕ) (hn : 2 ≤ n) (hz : 0 < z) (hzc : z ≤ c)
    (hS : S + z * (1 + n * (q - 1)) = n * q * c)
    (hwC : wC * c = n * q * c * (c - z)) (hle : S ≤ wC) : False := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at hS; omega
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + z := ⟨c - z, by omega⟩
  simp only [Nat.add_sub_cancel] at hS hwC
  have hc : 0 < c' + z := by omega
  have hwC' : wC = n * (q' + 1) * c' := by
    have : wC * (c' + z) = (n * (q' + 1) * c') * (c' + z) := by rw [hwC]; ring
    exact Nat.eq_of_mul_eq_mul_right hc this
  subst hwC'
  nlinarith [hS, hle, hz, hn]

lemma case_eC_two_empty (n q z cb S wC : ℕ) (hq : 4 ≤ q) (hn : 2 ≤ n) (hz : 0 < z) (hcb : 2 ≤ cb)
    (hS : S + z * (1 + n * (q - 1)) = n * q * (z * cb))
    (hwC : wC * (2 * (z * cb)) = n * q * (z * cb) * (z * cb - z)) (hle : S ≤ wC) : False := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨cb₁, rfl⟩ : ∃ cb₁, cb = cb₁ + 1 := ⟨cb - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hS
  have hzc : 0 < z * (cb₁ + 1) := Nat.mul_pos hz (Nat.succ_pos _)
  have hsub : z * (cb₁ + 1) - z = z * cb₁ := by rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hsub] at hwC
  have hwC2 : wC * 2 = n * (q' + 1) * (z * cb₁) := by
    have : (wC * 2) * (z * (cb₁ + 1)) = (n * (q' + 1) * (z * cb₁)) * (z * (cb₁ + 1)) := by
      calc (wC * 2) * (z * (cb₁ + 1)) = wC * (2 * (z * (cb₁ + 1))) := by ring
        _ = _ := by rw [hwC]; ring
    exact Nat.eq_of_mul_eq_mul_right hzc this
  have F : 2 * z ≤ n * z := Nat.mul_le_mul_right _ hn
  nlinarith [hS, hle, hwC2, hz, hn, F]

lemma four_mul_ge (T w N m z : ℕ) (hw : w * N = T * (m - z)) (hN : N ≤ 2 * m) (hzm : 2 * z ≤ m)
    (hm : 0 < m) : T ≤ 4 * w := by
  obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + z := ⟨m - z, by omega⟩
  simp only [Nat.add_sub_cancel] at hw
  nlinarith [hw, hN, hzm, hm]

end P2mDicksonCoreArith

namespace P2mDicksonCore

open P2mDicksonCoreArith

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K
variable {H : Type} [Group H] [Finite H] {ρ : H →* SL(2, K)}
variable {p : ℕ} [Fact p.Prime] [CharP K p] {P : Sylow p H}

lemma torus_numerics (hρ : Function.Injective ρ) (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) :
    (Nat.card (Subgroup.normalizer (torus h : Set H)) = Nat.card (torus h) ∨
      Nat.card (Subgroup.normalizer (torus h : Set H)) = 2 * Nat.card (torus h)) ∧
    2 * Nat.card (Zsub ρ) ≤ Nat.card (torus h) := by
  constructor
  · have hle := card_normalizer_le hρ h2 hh
    have hdvd : Nat.card (torus h) ∣ Nat.card (Subgroup.normalizer (torus h : Set H)) :=
      Subgroup.card_dvd_of_le Subgroup.le_normalizer
    obtain ⟨j, hj⟩ := hdvd
    have hm : 0 < Nat.card (torus h) := Nat.card_pos
    rw [hj] at hle ⊢
    have : j ≤ 2 := by nlinarith
    interval_cases j
    · rw [mul_zero] at hj; exact absurd hj Nat.card_pos.ne'
    · left; ring
    · right; ring
  · have hdvd : Nat.card (Zsub ρ) ∣ Nat.card (torus h) := Subgroup.card_dvd_of_le (Zsub_le_torus hρ h)
    obtain ⟨j, hj⟩ := hdvd
    have hne : Nat.card (torus h) ≠ Nat.card (Zsub ρ) := by
      intro he
      have := Subgroup.eq_of_le_of_card_ge (Zsub_le_torus hρ h) he.le
      exact not_mem_Zsub_of_isSS hρ hh (this ▸ self_mem_torus h)
    have hz : 0 < Nat.card (Zsub ρ) := Nat.card_pos
    rw [hj] at hne ⊢
    have : 2 ≤ j := by
      by_contra hj2; push Not at hj2
      interval_cases j
      · rw [mul_zero] at hj; exact absurd hj Nat.card_pos.ne'
      · exact hne (mul_one _)
    nlinarith

lemma card_le_four_mul_card_classSet (hρ : Function.Injective ρ) (h2 : (2 : K) ≠ 0) {h : H}
    (hh : IsSS ρ h) : Nat.card H ≤ 4 * Nat.card (classSet ρ (torus h)) := by
  obtain ⟨hN, hzm⟩ := torus_numerics hρ h2 hh
  refine four_mul_ge (Nat.card H) _ (Nat.card (Subgroup.normalizer (torus h : Set H)))
    (Nat.card (torus h)) (Nat.card (Zsub ρ)) (card_classSet_mul hρ h2 hh) ?_ hzm Nat.card_pos
  rcases hN with e | e <;> rw [e]; omega

set_option maxHeartbeats 4000000 in

theorem card_sylow_eq_of_normData (hρ : Function.Injective ρ) (D : NormData ρ P) (hp2 : p ≠ 2)
    (h2 : (2 : K) ≠ 0) (hq : 3 < Nat.card P) (hn1 : Nat.card (Sylow p H) ≠ 1) :
    Nat.card (Sylow p H) = Nat.card P + 1 := by
  classical

  obtain ⟨hB, hc, hC⟩ := Matrix.SpecialLinearGroup.borel_orbit_structure_of_sylow_eq_upper hp2 ρ
    hρ P D.hP D.exists_ne
  have hzZ : Nat.card {x : H // mat ρ x = 1 ∨ mat ρ x = -1} = Nat.card (Zsub ρ) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  rw [hzZ] at hc hC

  set q := Nat.card P with hqdef
  set n := Nat.card (Sylow p H) with hndef
  set z := Nat.card (Zsub ρ) with hzdef
  set c := Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) => mat ρ x 0 0) with hcdef
  set cb := Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) => (mat ρ x 0 0) ^ 2)
    with hcbdef
  have hz : 0 < z := Nat.card_pos
  have hn2 : 2 ≤ n := by
    have : 0 < n := Nat.card_pos
    omega
  have hq4 : 4 ≤ q := hq
  have hc0 : 0 < c := by
    have h := (Nat.card_pos (α := Subgroup.normalizer (P : Set H)))
    rw [hB] at h
    exact Nat.pos_of_mul_pos_left h
  have hcb1 : 1 ≤ cb := by
    rw [hc] at hc0
    exact Nat.pos_of_mul_pos_left hc0
  have hHB : Nat.card H = n * (q * c) := by
    rw [← hB, hndef, Sylow.card_eq_index_normalizer P, mul_comm, Subgroup.card_mul_index]
  have hzc : z ≤ c := by rw [hc]; nlinarith

  set S := Nat.card {x : H // IsSS ρ x} with hSdef
  have hS : S + z * (1 + n * (q - 1)) = n * q * (z * cb) := by
    have := card_subtype_add_card_subtype_not (fun x : H => IsSS ρ x)
    rw [card_not_isSS hρ D hp2 h2, hHB, hc] at this
    rw [hSdef]; linarith

  set SS : Set H := {x | IsSS ρ x} with hSSdef
  have hSSS : Nat.card SS = S := rfl
  have hsub : ∀ h : H, IsSS ρ h → classSet ρ (torus h) ⊆ SS := fun h hh x hx =>
    isSS_of_mem_classSet hρ h2 hh hx
  have hdisj : ∀ h h' : H, IsSS ρ h' → h' ∉ classSet ρ (torus h) →
      Disjoint (classSet ρ (torus h)) (classSet ρ (torus h')) := by
    intro h h' hh' hn'
    rw [Set.disjoint_left]
    intro x hx hx'
    apply hn'
    rw [classSet_eq_of_mem hx hx']
    exact self_mem_classSet hρ hh'
  have hnc : ∀ h h' : H, IsSS ρ h' → h' ∉ classSet ρ (torus h) →
      ¬ IsConjSub (torus h) (torus h') := fun h h' hh' hn' hconj =>
    hn' ⟨not_mem_Zsub_of_isSS hρ hh', hconj⟩

  have hnc1 : ∀ A : Set H, A ⊆ SS → A.ncard ≤ S := fun A hA => by
    rw [← hSSS, Nat.card_coe_set_eq]; exact Set.ncard_le_ncard hA

  have hcls : ∀ h : H, IsSS ρ h → Nat.card H ≤ 4 * (classSet ρ (torus h)).ncard := fun h hh => by
    rw [← Nat.card_coe_set_eq]; exact card_le_four_mul_card_classSet hρ h2 hh
  have hpick : ∀ A : Set H, A.ncard < S → ∃ h : H, IsSS ρ h ∧ h ∉ A := by
    intro A hA
    by_contra hall
    push Not at hall
    have : SS ⊆ A := fun x hx => hall x hx
    have := Set.ncard_le_ncard this
    rw [← Nat.card_coe_set_eq SS, hSSS] at this
    omega
  by_cases hcb : cb = 1
  ·
    exfalso
    rw [hcb, mul_one] at hS
    by_cases hS0 : S = 0
    · rw [hS0, zero_add] at hS
      exact case_cbar_one_empty n q z hn2 hz hS
    · obtain ⟨h, hh, -⟩ := hpick ∅ (by rw [Set.ncard_empty]; omega)
      exact case_cbar_one n q z S _ hq4 hn2 hz hS
        (by have t := hcls h hh; rw [hHB, hc, hcb] at t; linarith) (hnc1 _ (hsub h hh))
  ·
    have hcb2 : 2 ≤ cb := by omega
    obtain ⟨b, hbB, hbss', hCc, hH5, hfree⟩ := hC hcb
    have hbss : IsSS ρ b := hbss'
    set SC := classSet ρ (torus b) with hSCdef
    set wC := SC.ncard with hwCdef
    have hwC : wC * Nat.card (Subgroup.normalizer (torus b : Set H)) = n * (q * c) * (c - z) := by
      rw [hwCdef, ← Nat.card_coe_set_eq, ← hHB, ← hCc]; exact card_classSet_mul hρ h2 hbss
    obtain ⟨hNC, -⟩ := torus_numerics hρ h2 hbss
    rw [hCc] at hNC
    rcases hNC with hN1 | hN2
    ·
      exfalso
      rw [hN1] at hwC
      by_cases hle : S ≤ wC
      · refine case_eC_one_empty n q z c S wC hn2 hz hzc (by rw [hc]; exact hS) ?_ hle
        rw [hwC]; ring
      · push Not at hle
        obtain ⟨h, hh, hhC⟩ := hpick SC hle
        have hd := hdisj _ _ hh hhC
        have hsum : wC + (classSet ρ (torus h)).ncard ≤ S := by
          rw [hwCdef, ← Set.ncard_union_eq hd]
          exact hnc1 _ (Set.union_subset (hsub _ hbss) (hsub _ hh))
        refine case_eC_one n q z c S wC _ hq4 hn2 hz
          (by rw [hc, mul_comm]; exact Nat.mul_le_mul_left z hcb2) (by rw [hc]; exact hS)
          ?_ (by have t := hcls h hh; rw [hHB] at t; linarith) hsum
        rw [hwC]; ring
    ·
      have hwC2 : wC * (2 * (z * cb)) = n * q * (z * cb) * (z * cb - z) := by
        rw [hN2, hc] at hwC
        calc wC * (2 * (z * cb)) = wC * (2 * (z * cb)) := rfl
          _ = n * (q * (z * cb)) * (z * cb - z) := hwC
          _ = _ := by ring

      have hlt : torus b < Subgroup.normalizer (torus b : Set H) := by
        refine lt_of_le_of_ne Subgroup.le_normalizer ?_
        intro he
        have := congrArg (fun T : Subgroup H => Nat.card T) he
        beta_reduce at this
        rw [hN2, hCc] at this
        have : 0 < c := by rw [← hCc]; exact Nat.card_pos
        omega
      obtain ⟨n₀, hn₀, hn₀C⟩ := SetLike.exists_of_lt hlt
      obtain ⟨k, hk⟩ := hH5 ⟨n₀, hn₀, hn₀C⟩
      by_cases hle : S ≤ wC
      · exfalso
        exact case_eC_two_empty n q z cb S wC hq4 hn2 hz hcb2 hS hwC2 hle
      · push Not at hle
        obtain ⟨h, hh, hhC⟩ := hpick SC hle
        have hd := hdisj _ _ hh hhC
        set Sh := classSet ρ (torus h) with hShdef
        set w := Sh.ncard with hwdef
        set m := Nat.card (torus h) with hmdef
        obtain ⟨hNh, hzm⟩ := torus_numerics hρ h2 hh
        have hw4 : n * q * (z * cb) ≤ 4 * w := by
          have t := hcls h hh; rw [hHB, hc] at t; rw [hwdef]; linarith
        have hwid : w * Nat.card (Subgroup.normalizer (torus h : Set H)) = n * q * (z * cb) * (m - z) := by
          rw [hwdef, ← Nat.card_coe_set_eq, hmdef]
          have t := card_classSet_mul hρ h2 hh
          rw [hHB, hc] at t
          rw [t]; ring

        have hsum : wC + w = S := by
          apply le_antisymm
          · rw [hwCdef, hwdef, ← Set.ncard_union_eq hd]
            exact hnc1 _ (Set.union_subset (hsub _ hbss) (hsub _ hh))
          · by_contra hlt'
            push Not at hlt'
            obtain ⟨h', hh', hh'U⟩ := hpick (SC ∪ Sh) (by
              rw [Set.ncard_union_eq hd]; exact hlt')
            rw [Set.mem_union, not_or] at hh'U
            have hd1 := hdisj _ _ hh' hh'U.1
            have hd2 := hdisj _ _ hh' hh'U.2
            have h3 : wC + w + (classSet ρ (torus h')).ncard ≤ S := by
              rw [hwCdef, hwdef, ← Set.ncard_union_eq hd, ← Set.ncard_union_eq
                (Set.disjoint_union_left.mpr ⟨hd1, hd2⟩)]
              exact hnc1 _ (Set.union_subset (Set.union_subset (hsub _ hbss) (hsub _ hh))
                (hsub _ hh'))
            have hw4' : n * q * (z * cb) ≤ 4 * (classSet ρ (torus h')).ncard := by
              have t := hcls h' hh'; rw [hHB, hc] at t; linarith
            exact case_eC_two_no_third n q z (z * cb) S wC w _ hq4 hn2 hz
              (by rw [mul_comm]; exact Nat.mul_le_mul_left z hcb2) hS hwC2 hw4 hw4' h3

        have hfree' : m ∣ z * n := hfree h hh (hnc _ _ hh hhC)
        have hzdvd : z ∣ m := Subgroup.card_dvd_of_le (Zsub_le_torus hρ h)
        rcases hNh with hN1' | hN2'
        · exfalso
          rw [hN1'] at hwid
          exact case_eC_two_e_one n q z cb m S wC w hq4 hn2 hz hcb2 hzm hS hwC2 hsum hwid
        · rw [hN2'] at hwid
          have hk0 := case_eC_two_e_two n q z cb m S wC w k hq4 hn2 hz hcb2 hzm hzdvd hS hwC2 hsum
            hwid hfree' hk
          rw [hk0] at hk; linarith

section Normalise

variable (hρ : Function.Injective ρ)

omit [Finite H] [Fact p.Prime] [CharP K p] in
lemma funext_fin_two {α : Type} {f g : Fin 2 → α} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i; fin_cases i
  · exact h0
  · exact h1

omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma exists_fixed_vec {M : 𝕄} (h : (M - 1) ^ 2 = 0) : ∃ v : Fin 2 → K, v ≠ 0 ∧ M *ᵥ v = v := by
  have hdet : Matrix.det (M - 1) = 0 := by
    have h2 : Matrix.det (M - 1) ^ 2 = 0 := by rw [← Matrix.det_pow, h, Matrix.det_zero]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine ⟨v, hv, ?_⟩
  have h1 : (M - 1) *ᵥ v = M *ᵥ v - (1 : 𝕄) *ᵥ v := Matrix.sub_mulVec M 1 v
  rw [Matrix.one_mulVec, hMv] at h1
  exact sub_eq_zero.mp h1.symm

omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma conj_unip {M A B : 𝕄} (hAB : A * B = 1) (hBA : B * A = 1) (h : (M - 1) ^ 2 = 0) :
    (A * M * B - 1) ^ 2 = 0 := by
  have key : A * M * B - 1 = A * (M - 1) * B := by rw [mul_sub, sub_mul, mul_one, hAB]
  have hsq : (A * (M - 1) * B) ^ 2 = A * ((M - 1) * (B * A) * (M - 1)) * B := by
    rw [pow_two]; noncomm_ring
  rw [key, hsq, hBA, mul_one, ← pow_two, h, mul_zero, zero_mul]

omit [Finite H] [Fact p.Prime] [CharP K p] in
lemma mulVec_fin_two (M : 𝕄) (x y : K) :
    M *ᵥ ![x, y] = ![M 0 0 * x + M 0 1 * y, M 1 0 * x + M 1 1 * y] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma eq_upper_of_fixes_e0 {Q : 𝕄} (hQ : (Q - 1) ^ 2 = 0) (hfix : Q *ᵥ ![1, 0] = ![1, 0]) :
    Q = !![1, Q 0 1; 0, 1] := by
  rw [mulVec_fin_two] at hfix
  simp only [mul_one, mul_zero, add_zero] at hfix
  have e00 : Q 0 0 = 1 := by simpa using congrFun hfix 0
  have e10 : Q 1 0 = 0 := by simpa using congrFun hfix 1
  have e11 : Q 1 1 = 1 := by
    have := tr_of_unip hQ
    rw [tr, e00] at this
    linear_combination this
  conv_lhs => rw [Matrix.eta_fin_two Q]
  rw [e00, e10, e11]

omit [Finite H] [Fact p.Prime] [CharP K p] in

def conjSL (g : GL (Fin 2) K) : SL(2, K) →* SL(2, K) where
  toFun s := ⟨((g⁻¹ : GL (Fin 2) K) : 𝕄) * s * (g : 𝕄), by
    rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    change ((g⁻¹ : GL (Fin 2) K) : 𝕄) * 1 * (g : 𝕄) = 1
    rw [mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  map_mul' s t := by
    apply Subtype.ext
    change ((g⁻¹ : GL (Fin 2) K) : 𝕄) * (s * t : 𝕄) * (g : 𝕄) =
      ((g⁻¹ : GL (Fin 2) K) : 𝕄) * s * (g : 𝕄) * (((g⁻¹ : GL (Fin 2) K) : 𝕄) * t * (g : 𝕄))
    have : (g : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin 2) K) : 𝕄) * (s * t : 𝕄) * (g : 𝕄)
        = ((g⁻¹ : GL (Fin 2) K) : 𝕄) * s * ((g : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄)) * t * (g : 𝕄) := by
          rw [this]; noncomm_ring
      _ = _ := by noncomm_ring

omit [Finite H] [Fact p.Prime] [CharP K p] in
lemma conjSL_coe (g : GL (Fin 2) K) (s : SL(2, K)) :
    ((conjSL g s : SL(2, K)) : 𝕄) = ((g⁻¹ : GL (Fin 2) K) : 𝕄) * s * (g : 𝕄) := rfl

omit [Finite H] [Fact p.Prime] [CharP K p] in
lemma conjSL_injective (g : GL (Fin 2) K) : Function.Injective (conjSL g) := by
  intro s t h
  have h1 := congrArg (fun u : SL(2, K) => (g : 𝕄) * (u : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄)) h
  simp only [conjSL_coe] at h1
  have hgg : (g : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : ∀ u : 𝕄, (g : 𝕄) * (((g⁻¹ : GL (Fin 2) K) : 𝕄) * u * (g : 𝕄)) *
      ((g⁻¹ : GL (Fin 2) K) : 𝕄) = u := by
    intro u
    calc _ = ((g : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄)) * u * ((g : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄)) := by
          noncomm_ring
      _ = u := by rw [hgg, one_mul, mul_one]
  rw [e, e] at h1
  exact Subtype.ext h1

omit [Finite H] in
include hρ in

theorem exists_normData (P : Sylow p H) (hP1 : ∃ x ∈ P, x ≠ 1) :
    ∃ g : GL (Fin 2) K, NormData ((conjSL g).comp ρ) P := by
  classical

  have hunip : ∀ x ∈ P, (mat ρ x - 1) ^ 2 = 0 := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have : x ^ p ^ k = 1 := by
      have := congrArg (fun z : P => (z : H)) hk; simpa using this
    exact unip_of_pow_eq_one this
  obtain ⟨h₀, hh₀P, hh₀1⟩ := hP1
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vec (hunip h₀ hh₀P)

  obtain ⟨w, hD⟩ : ∃ w : Fin 2 → K, v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv0 (funext_fin_two (by simpa using h0) (by simpa using h1))
      exact ⟨![1, 0], by simp [h0]; exact h1⟩
    · exact ⟨![0, 1], by simp; exact h0⟩
  have hdetg : Matrix.det (!![v 0, w 0; v 1, w 1] : 𝕄) ≠ 0 := by
    rw [Matrix.det_fin_two_of]; intro hc; apply hD; linear_combination hc
  set g : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetg with hgdef
  have hgcoe : (g : 𝕄) = !![v 0, w 0; v 1, w 1] := rfl
  have hginv : ((g⁻¹ : GL (Fin 2) K) : 𝕄) * (g : 𝕄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hginv' : (g : 𝕄) * ((g⁻¹ : GL (Fin 2) K) : 𝕄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hge0 : (g : 𝕄) *ᵥ ![1, 0] = v := by
    rw [hgcoe, mulVec_fin_two]; exact funext_fin_two (by simp) (by simp)
  have hgiv : ((g⁻¹ : GL (Fin 2) K) : 𝕄) *ᵥ v = ![1, 0] := by
    rw [← hge0, Matrix.mulVec_mulVec, hginv, Matrix.one_mulVec]
  refine ⟨g, ?_⟩
  set ρ' : H →* SL(2, K) := (conjSL g).comp ρ with hρ'
  have hmat' : ∀ x : H, mat ρ' x = ((g⁻¹ : GL (Fin 2) K) : 𝕄) * mat ρ x * (g : 𝕄) := fun x => rfl
  have hunip' : ∀ x ∈ P, (mat ρ' x - 1) ^ 2 = 0 := fun x hx => by
    rw [hmat']; exact conj_unip hginv hginv' (hunip x hx)

  have hfix : mat ρ' h₀ *ᵥ ![1, 0] = ![1, 0] := by
    rw [hmat', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hge0, hv, hgiv]
  have hform := eq_upper_of_fixes_e0 (hunip' h₀ hh₀P) hfix
  set a := mat ρ' h₀ 0 1 with ha
  have hρ'inj : Function.Injective ρ' := (conjSL_injective g).comp hρ
  have ha0 : a ≠ 0 := by
    intro h0
    apply hh₀1
    apply mat_injective hρ'inj
    rw [hform, h0, mat_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp

  have hup : ∀ x ∈ P, ∃ t : K, ρ' x = upperElem t := by
    intro x hx
    have h1 := hunip' x hx
    have h2 := hunip' (x * h₀) (P.mul_mem hx hh₀P)
    rw [mat_mul, hform] at h2
    exact ⟨mat ρ' x 0 1, Subtype.ext (eq_upper_of_unip_mul_upper h1 ha0 h2)⟩

  let U : Subgroup H :=
    { carrier := {x | ∃ t : K, ρ' x = upperElem t}
      mul_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, by rw [map_mul, hs, ht, upperElem_mul]⟩
      one_mem' := ⟨0, by rw [map_one, upperElem_zero]⟩
      inv_mem' := by
        rintro x ⟨s, hs⟩
        refine ⟨-s, ?_⟩
        rw [map_inv, hs, inv_eq_iff_mul_eq_one, upperElem_mul, add_neg_cancel, upperElem_zero] }
  have hUp : IsPGroup p U := by
    rintro ⟨x, t, ht⟩
    refine ⟨1, Subtype.ext ?_⟩
    change x ^ p ^ 1 = 1
    rw [pow_one]
    apply hρ'inj
    rw [map_pow, ht, upperElem_pow, CharP.cast_eq_zero, zero_mul, upperElem_zero, map_one]
  have hle : (P : Subgroup H) ≤ U := fun x hx => hup x hx
  have hUeq : U = P := P.is_maximal' hUp hle
  refine ⟨fun x => ?_, ⟨a, ha0, h₀, hform⟩⟩
  constructor
  · exact hup x
  · intro hx
    have : x ∈ U := hx
    rw [hUeq] at this
    exact this

end Normalise

theorem card_sylow_eq (hρ : Function.Injective ρ) (hp2 : p ≠ 2) (P : Sylow p H)
    (hq : 3 < Nat.card P) (hP : Nat.card (Sylow p H) ≠ 1) :
    Nat.card (Sylow p H) = Nat.card P + 1 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  have hP1 : ∃ x ∈ P, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : (P : Subgroup H) = ⊥ := by
      rw [eq_bot_iff]; intro x hx; rw [Subgroup.mem_bot]; exact hall x hx
    have hc : Nat.card P = 1 := by
      rw [show Nat.card P = Nat.card ((P : Subgroup H)) from rfl, this, Subgroup.card_bot]
    omega
  obtain ⟨g, D⟩ := exists_normData hρ P hP1
  exact card_sylow_eq_of_normData ((conjSL_injective g).comp hρ) D hp2 h2 hq hP

end P2mDicksonCore

theorem solution
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G] (P : Sylow p G)
    (hq : 3 < Nat.card P) (hP : Nat.card (Sylow p G) ≠ 1) :
    Nat.card (Sylow p G) = Nat.card P + 1 :=
  P2mDicksonCore.card_sylow_eq (ρ := G.subtype) G.subtype_injective hp2 P hq hP

end S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite (solution)
