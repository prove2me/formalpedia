-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/92778a5f-5725-5c6f-8a46-5ead3b5d7d1e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite

set_option autoImplicit false

open Matrix MatrixGroups

namespace P2mDicksonCore

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

def tr (M : 𝕄) : K := M 0 0 + M 1 1

lemma tr_smul_one_add (x y : K) (g : 𝕄) : tr (x • (1 : 𝕄) + y • g) = 2 * x + y * tr g := by
  simp [tr]; ring

lemma det_smul_one_add (x y : K) (g : 𝕄) :
    (x • (1 : 𝕄) + y • g).det = x ^ 2 + x * y * tr g + y ^ 2 * g.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [tr]; ring

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

lemma tr_smul (c : K) (a : 𝕄) : tr (c • a) = c * tr a := by simp [tr]; ring

def IsScalarMat (g : 𝕄) : Prop := ∃ c : K, g = c • (1 : 𝕄)

lemma isScalarMat_iff (g : 𝕄) : IsScalarMat g ↔ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 0 0 = g 1 1 := by
  constructor
  · rintro ⟨c, rfl⟩; simp
  · rintro ⟨h01, h10, h00⟩
    refine ⟨g 0 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]

lemma eq_smul_one_add_smul_of_entries {m g : 𝕄} {x y : K}
    (h00 : m 0 0 = x + y * g 0 0) (h01 : m 0 1 = y * g 0 1) (h10 : m 1 0 = y * g 1 0)
    (h11 : m 1 1 = x + y * g 1 1) : m = x • (1 : 𝕄) + y • g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

lemma commute_iff {g : 𝕄} (hg : ¬ IsScalarMat g) (m : 𝕄) :
    m * g = g * m ↔ ∃ x y : K, m = x • (1 : 𝕄) + y • g := by
  constructor
  · intro h
    have e := fun i j => congrFun (congrFun h i) j
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    rw [isScalarMat_iff] at hg
    push Not at hg
    by_cases hb : g 0 1 = 0
    · by_cases hc : g 1 0 = 0
      ·
        have hsub : g 0 0 - g 1 1 ≠ 0 := sub_ne_zero.mpr (hg hb hc)
        rw [hb] at e01; rw [hc] at e10
        obtain ⟨y, hy⟩ : ∃ y : K, y = (m 0 0 - m 1 1) / (g 0 0 - g 1 1) := ⟨_, rfl⟩
        refine ⟨m 0 0 - y * g 0 0, y, eq_smul_one_add_smul_of_entries (by ring) ?_ ?_ ?_⟩
        · rw [hb, mul_zero]
          have : m 0 1 * (g 0 0 - g 1 1) = 0 := by linear_combination -e01
          exact (mul_eq_zero.mp this).resolve_right hsub
        · rw [hc, mul_zero]
          have : m 1 0 * (g 0 0 - g 1 1) = 0 := by linear_combination e10
          exact (mul_eq_zero.mp this).resolve_right hsub
        · have : y * (g 0 0 - g 1 1) = m 0 0 - m 1 1 := by rw [hy]; field_simp
          linear_combination this
      ·
        obtain ⟨y, hy⟩ : ∃ y : K, y = m 1 0 / g 1 0 := ⟨_, rfl⟩
        have hy' : y * g 1 0 = m 1 0 := by rw [hy]; field_simp
        refine ⟨m 0 0 - y * g 0 0, y, eq_smul_one_add_smul_of_entries (by ring) ?_ ?_ ?_⟩
        · rw [hb, mul_zero]
          rw [hb] at e11
          have : g 1 0 * m 0 1 = 0 := by linear_combination -e11
          exact (mul_eq_zero.mp this).resolve_left hc
        · exact hy'.symm
        · have : g 1 0 * (m 1 1 - m 0 0 - y * (g 1 1 - g 0 0)) = 0 := by
            linear_combination e10 - (g 1 1 - g 0 0) * hy'
          have := (mul_eq_zero.mp this).resolve_left hc
          linear_combination this
    ·
      obtain ⟨y, hy⟩ : ∃ y : K, y = m 0 1 / g 0 1 := ⟨_, rfl⟩
      have hy' : y * g 0 1 = m 0 1 := by rw [hy]; field_simp
      refine ⟨m 0 0 - y * g 0 0, y, eq_smul_one_add_smul_of_entries (by ring) hy'.symm ?_ ?_⟩
      · have : g 0 1 * (m 1 0 - y * g 1 0) = 0 := by
          linear_combination -e00 - g 1 0 * hy'
        have := (mul_eq_zero.mp this).resolve_left hb
        linear_combination this
      · have : g 0 1 * (m 1 1 - m 0 0 - y * (g 1 1 - g 0 0)) = 0 := by
          linear_combination -e01 - (g 1 1 - g 0 0) * hy'
        have := (mul_eq_zero.mp this).resolve_left hb
        linear_combination this
  · rintro ⟨x, y, rfl⟩
    rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul,
      mul_one]

lemma smul_one_add_eq_of_tr_sq_eq_four {g : 𝕄} (hg : (tr g) ^ 2 ≠ 4) (hdetg : g.det = 1)
    {x y : K} (hdet : (x • (1 : 𝕄) + y • g).det = 1)
    (htr : (tr (x • (1 : 𝕄) + y • g)) ^ 2 = 4) :
    x • (1 : 𝕄) + y • g = 1 ∨ x • (1 : 𝕄) + y • g = -1 := by
  rw [det_smul_one_add, hdetg, mul_one] at hdet
  rw [tr_smul_one_add] at htr
  have hy : y ^ 2 * (4 - (tr g) ^ 2) = 0 := by linear_combination 4 * hdet - htr
  have hy0 : y = 0 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact pow_eq_zero_iff two_ne_zero |>.mp h
    · exact absurd (by linear_combination -h) hg
  subst hy0
  have hx : (x - 1) * (x + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hx with h | h
  · left; rw [sub_eq_zero.mp h]; simp
  · right; rw [eq_neg_of_add_eq_zero_left h]; simp

lemma smul_one_add_eq_of_tr_eq (h2 : (2 : K) ≠ 0) {g : 𝕄} (hg : (tr g) ^ 2 ≠ 4)
    (hdetg : g.det = 1) {x y : K} (hdet : (x • (1 : 𝕄) + y • g).det = 1)
    (htr : tr (x • (1 : 𝕄) + y • g) = tr g) :
    x • (1 : 𝕄) + y • g = g ∨ x • (1 : 𝕄) + y • g = tr g • (1 : 𝕄) - g := by
  rw [det_smul_one_add, hdetg, mul_one] at hdet
  rw [tr_smul_one_add] at htr
  have hy : ((tr g) ^ 2 - 4) * ((y - 1) * (y + 1)) = 0 := by
    linear_combination (2 * x + y * tr g + tr g) * htr - 4 * hdet
  rcases mul_eq_zero.mp hy with h | h
  · exact absurd (by linear_combination h) hg
  rcases mul_eq_zero.mp h with h | h
  · have hy1 : y = 1 := by linear_combination h
    subst hy1
    have hx : x = 0 := by
      have : 2 * x = 0 := by linear_combination htr
      exact (mul_eq_zero.mp this).resolve_left h2
    subst hx; left; simp
  · have hy1 : y = -1 := by linear_combination h
    subst hy1
    have hx : x = tr g := by
      have : 2 * (x - tr g) = 0 := by linear_combination htr
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    subst hx; right; simp [sub_eq_add_neg]

lemma coe_inv_eq (s : SL(2, K)) : ((s⁻¹ : SL(2, K)) : 𝕄) = tr (s : 𝕄) • (1 : 𝕄) - s := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.eta_fin_two (s : 𝕄)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [tr]

lemma not_isScalarMat_of_tr_sq (s : SL(2, K)) (hs : (tr (s : 𝕄)) ^ 2 ≠ 4) :
    ¬ IsScalarMat (s : 𝕄) := by
  rintro ⟨c, hc⟩
  apply hs
  have hdet : (s : 𝕄).det = 1 := s.2
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  rw [hc, tr_smul, tr_one]
  linear_combination (4 : K) * hdet

section Tori

variable {H : Type} [Group H] (ρ : H →* SL(2, K))

abbrev mat (h : H) : 𝕄 := ((ρ h : SL(2, K)) : 𝕄)

lemma mat_mul (a b : H) : mat ρ (a * b) = mat ρ a * mat ρ b := by
  simp [mat, map_mul]

lemma mat_one : mat ρ (1 : H) = 1 := by simp [mat]

lemma mat_conj_mul (x u : H) : mat ρ (x * u * x⁻¹) * mat ρ x = mat ρ x * mat ρ u := by
  rw [← mat_mul, ← mat_mul, show x * u * x⁻¹ * x = x * u by group]

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

lemma mem_Zsub_iff (h : H) : h ∈ Zsub ρ ↔ mat ρ h = 1 ∨ mat ρ h = -1 := Iff.rfl

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

lemma mem_torus_iff_exists {h : H} (hh : IsSS ρ h) (g : H) :
    g ∈ torus h ↔ ∃ x y : K, mat ρ g = x • (1 : 𝕄) + y • mat ρ h := by
  rw [mem_torus_iff_mat hρ, commute_iff (not_isScalarMat_of_tr_sq (ρ h) hh)]

lemma Zsub_le_torus (h : H) : Zsub ρ ≤ torus h := by
  intro g hg
  rw [mem_torus_iff_mat hρ]
  rcases hg with hg | hg <;> rw [hg] <;> simp

omit hρ in
lemma self_mem_torus (h : H) : h ∈ torus h := (mem_torus_iff h h).mpr rfl

lemma isSS_of_mem_torus {h : H} (hh : IsSS ρ h) {g : H} (hg : g ∈ torus h)
    (hgZ : g ∉ Zsub ρ) : IsSS ρ g := by
  intro htr
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hh g).mp hg
  apply hgZ
  rw [mem_Zsub_iff, hxy]
  refine smul_one_add_eq_of_tr_sq_eq_four hh (ρ h).2 ?_ ?_
  · rw [← hxy]; exact (ρ g).2
  · rw [← hxy]; exact htr

lemma torus_eq_of_mem {h : H} (hh : IsSS ρ h) {g : H} (hg : g ∈ torus h)
    (hgZ : g ∉ Zsub ρ) : torus g = torus h := by
  have hgss := isSS_of_mem_torus hρ hh hg hgZ
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hh g).mp hg
  have hy : y ≠ 0 := by
    rintro rfl
    apply hgZ
    rw [mem_Zsub_iff, hxy]
    simp only [zero_smul, add_zero]
    have hdet : (x • (1 : 𝕄)).det = 1 := by
      have := (ρ g).2; rw [show ((ρ g : SL(2, K)) : 𝕄) = mat ρ g from rfl, hxy] at this
      simpa using this
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have : (x - 1) * (x + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.mp this with e | e
    · left; rw [sub_eq_zero.mp e, one_smul]
    · right; rw [eq_neg_of_add_eq_zero_left e]; simp

  have hh' : mat ρ h = (-(x * y⁻¹)) • (1 : 𝕄) + y⁻¹ • mat ρ g := by
    rw [hxy, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hy, one_smul, ← add_assoc,
      ← add_smul]
    ring_nf; simp
  ext k
  rw [mem_torus_iff_exists hρ hgss, mem_torus_iff_exists hρ hh]
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a + b * x, b * y, by rw [hab, hxy, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨a + b * (-(x * y⁻¹)), b * y⁻¹, ?_⟩
    rw [hab, hh', smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

lemma conj_eq_inv_of_mem_normalizer (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {n : H}
    (hn : n ∈ Subgroup.normalizer (torus h : Set H)) (hnT : n ∉ torus h) : n * h * n⁻¹ = h⁻¹ := by

  have hmem : n * h * n⁻¹ ∈ torus h := by
    rw [Subgroup.mem_normalizer_iff] at hn
    exact (hn h).mp (self_mem_torus h)
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hh _).mp hmem
  have hdet : (x • (1 : 𝕄) + y • mat ρ h).det = 1 := by rw [← hxy]; exact (ρ _).2
  have htr : tr (x • (1 : 𝕄) + y • mat ρ h) = tr (mat ρ h) := by
    rw [← hxy]
    simp only [mat, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul]
    refine tr_conj ?_
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  rcases smul_one_add_eq_of_tr_eq h2 hh (ρ h).2 hdet htr with e | e
  · exfalso; apply hnT
    rw [mem_torus_iff]
    have : n * h * n⁻¹ = h := mat_injective hρ (hxy.trans e)
    calc n * h = n * h * n⁻¹ * n := by group
      _ = h * n := by rw [this]
  · apply mat_injective hρ
    rw [hxy, e]
    change _ = ((ρ h⁻¹ : SL(2, K)) : 𝕄)
    rw [map_inv, coe_inv_eq]

lemma inv_mul_mem_torus (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {n₁ n₂ : H}
    (hn₁ : n₁ ∈ Subgroup.normalizer (torus h : Set H)) (hn₁T : n₁ ∉ torus h)
    (hn₂ : n₂ ∈ Subgroup.normalizer (torus h : Set H)) (hn₂T : n₂ ∉ torus h) : n₂⁻¹ * n₁ ∈ torus h := by
  have e₁ := conj_eq_inv_of_mem_normalizer hρ h2 hh hn₁ hn₁T
  have e₂ := conj_eq_inv_of_mem_normalizer hρ h2 hh hn₂ hn₂T
  rw [mem_torus_iff]
  have e₂' : n₂⁻¹ * h⁻¹ * n₂ = h := by
    calc n₂⁻¹ * h⁻¹ * n₂ = n₂⁻¹ * (n₂ * h * n₂⁻¹) * n₂ := by rw [e₂]
      _ = h := by group
  calc n₂⁻¹ * n₁ * h = n₂⁻¹ * (n₁ * h * n₁⁻¹) * n₁ := by group
    _ = n₂⁻¹ * h⁻¹ * n₂ * (n₂⁻¹ * n₁) := by rw [e₁]; group
    _ = h * (n₂⁻¹ * n₁) := by rw [e₂']

lemma card_normalizer_le [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) :
    Nat.card (Subgroup.normalizer (torus h : Set H)) ≤ 2 * Nat.card (torus h) := by
  classical
  by_cases hall : ∀ n : H, n ∈ Subgroup.normalizer (torus h : Set H) → n ∈ torus h
  · have : Subgroup.normalizer (torus h : Set H) = torus h :=
      le_antisymm (fun n hn => hall n hn) Subgroup.le_normalizer
    rw [this]; omega
  · push Not at hall
    obtain ⟨n₀, hn₀, hn₀T⟩ := hall

    let f : (Subgroup.normalizer (torus h : Set H)) → Bool × torus h := fun n =>
      if hn : (n : H) ∈ torus h then (false, ⟨n, hn⟩)
      else (true, ⟨n₀⁻¹ * n, inv_mul_mem_torus hρ h2 hh n.2 hn hn₀ hn₀T⟩)
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : (a : H) ∈ torus h <;> by_cases hb : (b : H) ∈ torus h <;>
        simp only [ha, hb, dite_true, dite_false, Prod.mk.injEq] at hab
      · have h1 := congrArg Subtype.val hab.2
        exact Subtype.ext h1
      · simp at hab
      · simp at hab
      · have h1 := congrArg Subtype.val hab.2
        exact Subtype.ext (mul_left_cancel h1)
    have := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_prod] using this

end Tori

section Tori2

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)

lemma mat_inv_mul (y : H) : mat ρ y⁻¹ * mat ρ y = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
lemma mat_mul_inv (y : H) : mat ρ y * mat ρ y⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]

include hρ in

lemma comm_of_mem_Zsub {ζ : H} (hζ : ζ ∈ Zsub ρ) (h : H) : ζ * h = h * ζ := by
  apply mat_injective hρ
  rw [mat_mul, mat_mul]
  rcases hζ with e | e <;> rw [e] <;> simp

lemma card_subtype_add_card_subtype_not {α : Type} [Finite α] (q : α → Prop) :
    Nat.card {x // q x} + Nat.card {x // ¬ q x} = Nat.card α := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl q)]

lemma mem_torus_conj_iff (w c g : H) : g ∈ torus (w * c * w⁻¹) ↔ w⁻¹ * g * w ∈ torus c := by
  rw [mem_torus_iff, mem_torus_iff]
  constructor
  · intro h
    calc w⁻¹ * g * w * c = w⁻¹ * (g * (w * c * w⁻¹)) * w := by group
      _ = w⁻¹ * ((w * c * w⁻¹) * g) * w := by rw [h]
      _ = c * (w⁻¹ * g * w) := by group
  · intro h
    calc g * (w * c * w⁻¹) = w * ((w⁻¹ * g * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * g * w)) * w⁻¹ := by rw [h]
      _ = w * c * w⁻¹ * g := by group

end Tori2

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

lemma isConjSub_torus_conj (h s : H) : IsConjSub (torus h) (torus (s * h * s⁻¹)) :=
  ⟨s, fun g => mem_torus_conj_iff s h g⟩

lemma IsConjSub.card_eq {M M' : Subgroup H} (h : IsConjSub M M') : Nat.card M = Nat.card M' := by
  obtain ⟨s, hs⟩ := h
  refine Nat.card_congr
    { toFun := fun m => ⟨s * m * s⁻¹, (hs _).mpr (by rw [show s⁻¹ * (s * m * s⁻¹) * s = m by group]; exact m.2)⟩
      invFun := fun m' => ⟨s⁻¹ * m' * s, (hs _).mp m'.2⟩
      left_inv := fun m => Subtype.ext (by simp only; group)
      right_inv := fun m' => Subtype.ext (by simp only; group) }

lemma IsConjSub.normalizer {M M' : Subgroup H} (h : IsConjSub M M') :
    IsConjSub (Subgroup.normalizer (M : Set H)) (Subgroup.normalizer (M' : Set H)) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun n => ?_⟩
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn g
    have := hn (s * g * s⁻¹)
    rw [hs, hs, show s⁻¹ * (s * g * s⁻¹) * s = g by group] at this
    rw [this, show s⁻¹ * (n * (s * g * s⁻¹) * n⁻¹) * s = s⁻¹ * n * s * g * (s⁻¹ * n * s)⁻¹ by group]
  · intro hn g
    rw [hs, hs, hn (s⁻¹ * g * s),
      show s⁻¹ * n * s * (s⁻¹ * g * s) * (s⁻¹ * n * s)⁻¹ = s⁻¹ * (n * g * n⁻¹) * s by group]

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

lemma isSS_of_mem_classSet {h : H} (hh : IsSS ρ h) {x : H} (hx : x ∈ classSet ρ (torus h)) :
    IsSS ρ x := by
  obtain ⟨hxZ, s, hs⟩ := hx

  have h1 : s * h * s⁻¹ ∈ torus x := (hs _).mpr (by
    rw [show s⁻¹ * (s * h * s⁻¹) * s = h by group]; exact self_mem_torus h)
  have hss : IsSS ρ (s * h * s⁻¹) := by
    change (tr (mat ρ (s * h * s⁻¹))) ^ 2 ≠ 4
    rw [mat_mul, mat_mul, tr_conj (mat_inv_mul s)]; exact hh
  have h2 : x ∈ torus (s * h * s⁻¹) := by
    rw [mem_torus_iff]; exact ((mem_torus_iff x _).mp h1).symm
  exact isSS_of_mem_torus hρ hss h2 hxZ

include hρ in

lemma conj_eq_of_mem_Zsub {ζ : H} (hζ : ζ ∈ Zsub ρ) (s : H) : s * ζ * s⁻¹ = ζ := by
  rw [← comm_of_mem_Zsub hρ hζ s, mul_inv_cancel_right]

include hρ in

lemma card_classSet_mul [Finite H] {h : H} (hh : IsSS ρ h) :
    Nat.card (classSet ρ (torus h)) * Nat.card (Subgroup.normalizer (torus h : Set H)) =
      Nat.card H * (Nat.card (torus h) - Nat.card (Zsub ρ)) := by
  classical

  have hΦmem : ∀ (s : H) (m : torus h), (m : H) ∉ Zsub ρ →
      s * m * s⁻¹ ∈ classSet ρ (torus h) := by
    intro s m hm
    refine ⟨?_, ?_⟩
    · intro hZ
      apply hm
      have : (m : H) = s⁻¹ * (s * m * s⁻¹) * s⁻¹⁻¹ := by group
      rw [this, conj_eq_of_mem_Zsub hρ hZ]
      exact hZ
    · have e := torus_eq_of_mem hρ hh m.2 hm
      have := isConjSub_torus_conj (m : H) s
      rw [e] at this
      exact this
  let Φ : H × {m : torus h // (m : H) ∉ Zsub ρ} → classSet ρ (torus h) := fun sm =>
    ⟨sm.1 * sm.2.1 * sm.1⁻¹, hΦmem sm.1 sm.2.1 sm.2.2⟩

  have hfib : ∀ x : classSet ρ (torus h),
      Nat.card {sm // Φ sm = x} = Nat.card (Subgroup.normalizer (torus h : Set H)) := by
    rintro ⟨x, hxZ, s₀, hs₀⟩

    have hm₀ : s₀⁻¹ * x * s₀ ∈ torus h := (hs₀ x).mp (self_mem_torus x)
    have hm₀Z : s₀⁻¹ * x * s₀ ∉ Zsub ρ := by
      intro hZ; apply hxZ
      have : x = s₀ * (s₀⁻¹ * x * s₀) * s₀⁻¹ := by group
      rw [this, conj_eq_of_mem_Zsub hρ hZ]; exact hZ

    have hkey : ∀ (s : H) (m : H), m ∈ torus h → m ∉ Zsub ρ → s * m * s⁻¹ = x →
        s₀⁻¹ * s ∈ Subgroup.normalizer (torus h : Set H) := by
      intro s m hm hmZ hsm
      have hTm : torus m = torus h := torus_eq_of_mem hρ hh hm hmZ

      have hs : ∀ g : H, g ∈ torus x ↔ s⁻¹ * g * s ∈ torus h := by
        intro g; rw [← hsm, mem_torus_conj_iff, hTm]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have e1 : s₀⁻¹ * s * g * (s₀⁻¹ * s)⁻¹ = s₀⁻¹ * (s * g * s⁻¹) * s₀ := by group
      rw [e1, ← hs₀, hs, show s⁻¹ * (s * g * s⁻¹) * s = g by group]
    refine Nat.card_congr
      { toFun := fun sm => ⟨s₀⁻¹ * sm.1.1, hkey sm.1.1 sm.1.2.1 sm.1.2.1.2 sm.1.2.2
          (congrArg Subtype.val sm.2)⟩
        invFun := fun n => ⟨(s₀ * n, ⟨⟨n⁻¹ * (s₀⁻¹ * x * s₀) * n, ?_⟩, ?_⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    ·
      have := n.2
      rw [Subgroup.mem_normalizer_iff''] at this
      exact (this _).mp hm₀
    ·
      intro hZ
      change (n : H)⁻¹ * (s₀⁻¹ * x * s₀) * n ∈ Zsub ρ at hZ
      apply hm₀Z
      have e := conj_eq_of_mem_Zsub hρ hZ n
      rw [show (n : H) * ((n : H)⁻¹ * (s₀⁻¹ * x * s₀) * n) * (n : H)⁻¹ = s₀⁻¹ * x * s₀ by group]
        at e
      rw [e]; exact hZ
    ·
      obtain ⟨n, hn⟩ := n
      apply Subtype.ext
      change s₀ * n * (n⁻¹ * (s₀⁻¹ * x * s₀) * n) * (s₀ * n)⁻¹ = x
      group
    · rintro ⟨⟨s, m, hm⟩, hsm⟩
      have hsm' : s * m * s⁻¹ = x := congrArg Subtype.val hsm
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      refine ⟨by group, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      change (s₀⁻¹ * s)⁻¹ * (s₀⁻¹ * x * s₀) * (s₀⁻¹ * s) = m
      rw [← hsm']; group
    · intro n
      apply Subtype.ext
      change s₀⁻¹ * (s₀ * n) = n
      group

  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv Φ)
  letI : Fintype (classSet ρ (torus h)) := Fintype.ofFinite _
  rw [Nat.card_sigma] at hsig
  simp_rw [hfib] at hsig
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_eq_nat_card, Nat.card_prod]
    at hsig
  rw [hsig]

  have hZ : Nat.card {m : torus h // (m : H) ∈ Zsub ρ} = Nat.card (Zsub ρ) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨m.1, m.2⟩
        invFun := fun ζ => ⟨⟨ζ, Zsub_le_torus hρ h ζ.2⟩, ζ.2⟩
        left_inv := fun m => rfl
        right_inv := fun ζ => rfl }
  have := card_subtype_add_card_subtype_not (fun m : torus h => (m : H) ∈ Zsub ρ)
  rw [hZ] at this
  congr 1
  omega

end Classes

end P2mDicksonCore

open P2mDicksonCore in
theorem solution
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (h : H) (hh : (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4) :
    (∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
      ∃ x y : K, ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        x • (1 : Matrix (Fin 2) (Fin 2) K) + y • ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) ∧
    (∀ g ∈ Subgroup.centralizer ({h} : Set H),
      ¬ (((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
         ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) →
      Subgroup.centralizer ({g} : Set H) = Subgroup.centralizer ({h} : Set H) ∧
      ((((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
        ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4)) ∧
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) ≤
      2 * Nat.card (Subgroup.centralizer ({h} : Set H)) ∧
    Nat.card {x : H // ¬ (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) ∧
      ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({x} : Set H) ↔
        s⁻¹ * g * s ∈ Subgroup.centralizer ({h} : Set H)} *
      Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) =
    Nat.card H * (Nat.card (Subgroup.centralizer ({h} : Set H)) -
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1}) := by
  have hh' : IsSS ρ h := hh
  refine ⟨fun g => mem_torus_iff_exists hρ hh' g, fun g hg hgZ => ?_,
    card_normalizer_le hρ h2 hh', ?_⟩
  · exact ⟨torus_eq_of_mem hρ hh' hg hgZ, isSS_of_mem_torus hρ hh' hg hgZ⟩
  · exact card_classSet_mul hρ hh'

end S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite (solution)
