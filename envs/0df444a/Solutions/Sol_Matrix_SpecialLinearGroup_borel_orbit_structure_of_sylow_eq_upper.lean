-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.borel_orbit_structure_of_sylow_eq_upper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7381b9b1-a48e-547a-9797-b1e73cc3061b

import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import Theorems.Thm_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper

set_option autoImplicit false

open Matrix MatrixGroups ModularCurve

namespace P2mDicksonBorel

variable {K : Type} [Field K]

local notation "𝕄" => Matrix (Fin 2) (Fin 2) K

def tr (M : 𝕄) : K := M 0 0 + M 1 1

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

lemma isSS_of_mem_torus [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {g : H}
    (hg : g ∈ torus h) (hgZ : g ∉ Zsub ρ) : IsSS ρ g :=
  ((Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite h2 ρ hρ h hh).2.1
    g hg hgZ).2

lemma torus_eq_of_mem [Finite H] (h2 : (2 : K) ≠ 0) {h : H} (hh : IsSS ρ h) {g : H}
    (hg : g ∈ torus h) (hgZ : g ∉ Zsub ρ) : torus g = torus h :=
  ((Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite h2 ρ hρ h hh).2.1
    g hg hgZ).1

end Tori

structure NormData {H : Type} [Group H] (ρ : H →* SL(2, K)) {p : ℕ} (P : Sylow p H) : Prop where
  hP : ∀ x : H, x ∈ P ↔ ∃ t : K, ρ x = upperElem t
  exists_ne : ∃ a : K, a ≠ 0 ∧ ∃ u : H, mat ρ u = !![1, a; 0, 1]

section Borel

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)
variable {p : ℕ} {P : Sylow p H} (D : NormData ρ P)

include D in
lemma mat_of_mem_P {x : H} (hx : x ∈ P) : ∃ t : K, mat ρ x = !![1, t; 0, 1] := by
  obtain ⟨t, ht⟩ := (D.hP x).mp hx
  exact ⟨t, by rw [mat, ht, upperElem_coe]⟩

include D in
lemma mem_P_of_mat {x : H} {t : K} (hx : mat ρ x = !![1, t; 0, 1]) : x ∈ P :=
  (D.hP x).mpr ⟨t, Subtype.ext hx⟩

include D in

lemma apply_one_zero_eq_zero_of_mem_normalizer
    {x : H} (hx : x ∈ Subgroup.normalizer (P : Set H)) : mat ρ x 1 0 = 0 := by
  obtain ⟨a, ha, u, hu⟩ := D.exists_ne
  rw [Subgroup.mem_set_normalizer_iff] at hx
  have huP : u ∈ P := mem_P_of_mat D hu
  obtain ⟨a', ha'⟩ := mat_of_mem_P D ((hx u).mp huP)
  have e : mat ρ x * mat ρ u = mat ρ (x * u * x⁻¹) * mat ρ x := (mat_conj_mul ρ x u).symm
  rw [hu, ha'] at e
  have := congrFun (congrFun e 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_one, zero_mul, one_mul, zero_add] at this
  have h : mat ρ x 1 0 * a = 0 := by linear_combination this
  exact (mul_eq_zero.mp h).resolve_right ha

lemma upper_conj_unip (X : 𝕄) (hX : X 1 0 = 0) (hdet : X.det = 1) (t : K) :
    X * !![1, t; 0, 1] = !![1, X 0 0 ^ 2 * t; 0, 1] * X := by
  rw [Matrix.det_fin_two, hX, mul_zero, sub_zero] at hdet
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hX]
  linear_combination -(X 0 0 * t) * hdet

lemma mat_inv_mul (y : H) : mat ρ y⁻¹ * mat ρ y = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
lemma mat_mul_inv (y : H) : mat ρ y * mat ρ y⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]

lemma mat_conj_of_upper {y u : H} (hy : mat ρ y 1 0 = 0) {t : K} (ht : mat ρ u = !![1, t; 0, 1]) :
    mat ρ (y * u * y⁻¹) = !![1, mat ρ y 0 0 ^ 2 * t; 0, 1] := by
  have e := upper_conj_unip (mat ρ y) hy (ρ y).2 t
  rw [← ht] at e
  have e2 : mat ρ (y * u * y⁻¹) * mat ρ y = mat ρ y * mat ρ u := mat_conj_mul ρ y u
  rw [e] at e2
  calc mat ρ (y * u * y⁻¹) = mat ρ (y * u * y⁻¹) * mat ρ y * mat ρ y⁻¹ := by
        rw [mul_assoc (mat ρ (y * u * y⁻¹)) (mat ρ y), mat_mul_inv, mul_one]
    _ = _ := by rw [e2, mul_assoc _ (mat ρ y), mat_mul_inv, mul_one]

include D in

lemma mem_normalizer_of_apply_one_zero
    {x : H} (hx : mat ρ x 1 0 = 0) : x ∈ Subgroup.normalizer (P : Set H) := by
  have key : ∀ y : H, mat ρ y 1 0 = 0 → ∀ u ∈ P, y * u * y⁻¹ ∈ (P : Subgroup H) := by
    intro y hy u hu
    obtain ⟨t, ht⟩ := mat_of_mem_P D hu
    exact mem_P_of_mat D (mat_conj_of_upper hy ht)
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  constructor
  · exact fun hu => key x hx u hu
  · intro h
    have hx' : mat ρ x⁻¹ 1 0 = 0 := by
      simp only [mat, map_inv]
      rw [coe_inv_eq]
      simp [hx]
    have := key x⁻¹ hx' _ h
    simp [mul_assoc] at this
    exact this

include D in

lemma mem_B_iff (x : H) : x ∈ Subgroup.normalizer (P : Set H) ↔ mat ρ x 1 0 = 0 :=
  ⟨apply_one_zero_eq_zero_of_mem_normalizer D, mem_normalizer_of_apply_one_zero D⟩

lemma diag_mul_eq_one_of_upper {X : 𝕄} (hX : X 1 0 = 0) (hdet : X.det = 1) :
    X 0 0 * X 1 1 = 1 := by
  rw [Matrix.det_fin_two, hX, mul_zero, sub_zero] at hdet; exact hdet

noncomputable def chi (D : NormData ρ P) : Subgroup.normalizer (P : Set H) →* Kˣ where
  toFun x := Units.mk0 (mat ρ x 0 0) (by
    have h10 := (mem_B_iff D x).mp x.2
    have := diag_mul_eq_one_of_upper h10 (ρ x).2
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this)
  map_one' := by ext; simp [mat]
  map_mul' x y := by
    ext
    have hy := (mem_B_iff D y).mp y.2
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, mat, map_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [show ((ρ (y : H) : SL(2, K)) : 𝕄) 1 0 = 0 from hy, mul_zero, add_zero]

lemma chi_apply (x : Subgroup.normalizer (P : Set H)) : ((chi D x : Kˣ) : K) = mat ρ x 0 0 := rfl

lemma chi_eq_one_iff (x : Subgroup.normalizer (P : Set H)) : chi D x = 1 ↔ (x : H) ∈ P := by
  have h10 := (mem_B_iff D x).mp x.2
  constructor
  · intro h
    have h00 : mat ρ x 0 0 = 1 := by
      have := congrArg (fun v : Kˣ => (v : K)) h
      simpa [chi_apply] using this
    have h11 : mat ρ x 1 1 = 1 := by
      have := diag_mul_eq_one_of_upper h10 (ρ x).2
      rw [h00, one_mul] at this; exact this
    refine mem_P_of_mat D (t := mat ρ x 0 1) ?_
    have := Matrix.eta_fin_two (mat ρ x); rw [h00, h10, h11] at this; exact this
  · intro h
    obtain ⟨t, ht⟩ := mat_of_mem_P D h
    ext; rw [chi_apply, ht]; simp

include D in
lemma Zsub_le_B : Zsub ρ ≤ Subgroup.normalizer (P : Set H) := by
  intro x hx
  rw [mem_B_iff D]
  rcases hx with h | h <;> rw [h] <;> simp

lemma card_ker_chi : Nat.card (chi D).ker = Nat.card P := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x : Subgroup.normalizer (P : Set H)), (chi_eq_one_iff D _).mp x.2⟩
      invFun := fun y => ⟨⟨y, Subgroup.le_normalizer y.2⟩, (chi_eq_one_iff D _).mpr y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

lemma card_B [Finite H] :
    Nat.card (Subgroup.normalizer (P : Set H)) = Nat.card P * Nat.card (chi D).range := by
  rw [← card_ker_chi D, ← Subgroup.index_ker, Subgroup.card_mul_index]

variable [Fact p.Prime] [CharP K p]

include D in

lemma mat_pow_p_of_apply_eq_neg_one (hp2 : p ≠ 2) {x : H}
    (hxB : x ∈ Subgroup.normalizer (P : Set H)) (hx : mat ρ x 0 0 = -1) :
    mat ρ (x ^ p) = -1 := by
  have h10 := (mem_B_iff D x).mp hxB
  have h11 : mat ρ x 1 1 = -1 := by
    have := diag_mul_eq_one_of_upper h10 (ρ x).2
    rw [hx] at this
    linear_combination -this
  have hform : mat ρ x = -((upperElem (-(mat ρ x 0 1)) : SL(2, K)) : 𝕄) := by
    rw [upperElem_coe]
    have := Matrix.eta_fin_two (mat ρ x)
    rw [hx, h10, h11] at this
    rw [this]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rw [mat, map_pow, Matrix.SpecialLinearGroup.coe_pow, show ((ρ x : SL(2, K)) : 𝕄) = mat ρ x
    from rfl, hform, neg_pow, hodd.neg_one_pow, ← Matrix.SpecialLinearGroup.coe_pow,
    upperElem_pow, CharP.cast_eq_zero, zero_mul, upperElem_zero]
  simp

omit [Fact p.Prime] [CharP K p] in
include hρ in

lemma Zsub_eq_of_apply {ζ ζ' : H} (hζ : ζ ∈ Zsub ρ) (hζ' : ζ' ∈ Zsub ρ)
    (h : mat ρ ζ 0 0 = mat ρ ζ' 0 0) (h2 : (2 : K) ≠ 0) : ζ = ζ' := by
  apply mat_injective hρ
  rcases hζ with e | e <;> rcases hζ' with e' | e' <;> rw [e, e'] at h ⊢ <;> simp at h ⊢
  · exact absurd (by linear_combination h : (2 : K) = 0) h2
  · exact absurd (by linear_combination -h : (2 : K) = 0) h2

include hρ in

lemma card_ker_chiSq [Finite H] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) :
    Nat.card (chi D * chi D).ker = Nat.card (Zsub ρ) * Nat.card P := by
  rw [← Nat.card_prod]
  symm
  have hmemker : ∀ (ζ : Zsub ρ) (v : P),
      (⟨(ζ : H) * v, Subgroup.mul_mem _ (Zsub_le_B D ζ.2) (Subgroup.le_normalizer v.2)⟩ :
        Subgroup.normalizer (P : Set H)) ∈ (chi D * chi D).ker := by
    intro ζ v
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply]
    obtain ⟨t, ht⟩ := mat_of_mem_P D v.2
    ext
    simp only [Units.val_mul, chi_apply, Units.val_one]
    rw [mat_mul, ht]
    rcases ζ.2 with h | h <;> rw [h] <;> simp
  refine Nat.card_eq_of_bijective (fun zu : Zsub ρ × P => (⟨_, hmemker zu.1 zu.2⟩ :
    (chi D * chi D).ker)) ⟨?_, ?_⟩
  ·
    rintro ⟨⟨ζ, hζ⟩, ⟨v, hv⟩⟩ ⟨⟨ζ', hζ'⟩, ⟨v', hv'⟩⟩ h
    have h1 : ζ * v = ζ' * v' := congrArg (fun y : (chi D * chi D).ker =>
      ((y : Subgroup.normalizer (P : Set H)) : H)) h
    obtain ⟨t, ht⟩ := mat_of_mem_P D hv
    obtain ⟨t', ht'⟩ := mat_of_mem_P D hv'
    have hm := congrArg (mat ρ) h1
    rw [mat_mul, mat_mul, ht, ht'] at hm
    have e00 := congrFun (congrFun hm 0) 0
    have hζζ : ζ = ζ' := by
      refine Zsub_eq_of_apply hρ hζ hζ' ?_ h2
      rcases hζ with e | e <;> rcases hζ' with e' | e' <;> rw [e, e'] at e00 ⊢ <;>
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using e00
    subst hζζ
    have := mul_left_cancel h1
    subst this
    rfl
  ·
    rintro ⟨⟨x, hxB⟩, hx⟩
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply] at hx
    have hsq : mat ρ x 0 0 * mat ρ x 0 0 = 1 := by
      have := congrArg (fun v : Kˣ => (v : K)) hx
      simpa [chi_apply] using this
    have h10 := (mem_B_iff D x).mp hxB
    have h11 : mat ρ x 1 1 = mat ρ x 0 0 := by
      have := diag_mul_eq_one_of_upper h10 (ρ x).2
      linear_combination mat ρ x 0 0 * this - mat ρ x 1 1 * hsq
    have hcases : (mat ρ x 0 0 - 1) * (mat ρ x 0 0 + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hcases with e | e
    ·
      have h00 : mat ρ x 0 0 = 1 := by linear_combination e
      have hxP : x ∈ P := by
        refine mem_P_of_mat D (t := mat ρ x 0 1) ?_
        have := Matrix.eta_fin_two (mat ρ x); rw [h00, h10, h11, h00] at this; exact this
      refine ⟨(⟨1, (Zsub ρ).one_mem⟩, ⟨x, hxP⟩), ?_⟩
      apply Subtype.ext; apply Subtype.ext
      change (1 : H) * x = x
      rw [one_mul]
    ·
      have h00 : mat ρ x 0 0 = -1 := by linear_combination e
      have hζ : x ^ p ∈ Zsub ρ := Or.inr (mat_pow_p_of_apply_eq_neg_one D hp2 hxB h00)
      have hv : (x ^ p)⁻¹ * x ∈ P := by
        refine mem_P_of_mat D (t := -(mat ρ x 0 1)) ?_
        rw [mat_mul, show mat ρ (x ^ p)⁻¹ = mat ρ ((x ^ p)⁻¹) from rfl]
        have hi : mat ρ (x ^ p)⁻¹ = -1 := by
          rw [mat, map_inv, coe_inv_eq, show ((ρ (x ^ p) : SL(2, K)) : 𝕄) = mat ρ (x ^ p) from rfl,
            mat_pow_p_of_apply_eq_neg_one D hp2 hxB h00, tr_neg, tr_one]
          ext i j; fin_cases i <;> fin_cases j <;> norm_num
        rw [hi]
        have := Matrix.eta_fin_two (mat ρ x); rw [h00, h10, h11, h00] at this
        rw [this]
        ext i j; fin_cases i <;> fin_cases j <;> simp
      refine ⟨(⟨x ^ p, hζ⟩, ⟨(x ^ p)⁻¹ * x, hv⟩), ?_⟩
      apply Subtype.ext; apply Subtype.ext
      change x ^ p * ((x ^ p)⁻¹ * x) = x
      group

omit [Fact p.Prime] [CharP K p] in

lemma exists_generator_chi [Finite H] (hc : Nat.card (chi D * chi D).range ≠ 1) :
    ∃ b : Subgroup.normalizer (P : Set H), (chi D b) ^ 2 ≠ 1 ∧
      ∀ d : (chi D).range, d ∈ Subgroup.zpowers (⟨chi D b, b, rfl⟩ : (chi D).range) := by
  haveI : Finite (chi D).range :=
    Finite.of_surjective (chi D).rangeRestrict (chi D).rangeRestrict_surjective
  obtain ⟨⟨g, b, rfl⟩, hg⟩ := IsCyclic.exists_generator (α := (chi D).range)
  refine ⟨b, ?_, hg⟩
  intro hsq
  apply hc
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨1, ?_⟩
  rintro ⟨d, x, rfl⟩
  apply Subtype.ext
  change (chi D * chi D) x = 1
  rw [MonoidHom.mul_apply, ← pow_two]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨chi D x, x, rfl⟩)
  have hk' : chi D x = chi D b ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  rw [hk', ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hsq,
    _root_.one_zpow]

omit [Fact p.Prime] [CharP K p] in

lemma isSS_iff_chi_sq_ne_one (x : Subgroup.normalizer (P : Set H)) :
    IsSS ρ (x : H) ↔ (chi D x) ^ 2 ≠ 1 := by
  have h10 := (mem_B_iff D x).mp x.2
  have hd := diag_mul_eq_one_of_upper h10 (ρ x).2
  have hchi : ((chi D x : Kˣ) : K) = mat ρ x 0 0 := chi_apply D x
  rw [IsSS, tr, not_iff_not]
  constructor
  · intro h
    ext
    rw [Units.val_pow_eq_pow_val, hchi, Units.val_one]

    have : (mat ρ x 0 0 - mat ρ x 1 1) ^ 2 = 0 := by linear_combination h - 4 * hd
    have e : mat ρ x 0 0 = mat ρ x 1 1 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp this; linear_combination this
    rw [pow_two]; nth_rewrite 2 [e]; exact hd
  · intro h
    have h' : mat ρ x 0 0 ^ 2 = 1 := by
      have := congrArg (fun v : Kˣ => (v : K)) h
      simpa [hchi] using this
    have e : mat ρ x 1 1 = mat ρ x 0 0 := by
      linear_combination mat ρ x 0 0 * hd - mat ρ x 1 1 * h'
    rw [e]; linear_combination 4 * h'

include hρ D in
omit [Fact p.Prime] [CharP K p] in

lemma torus_le_B {b : H} (hbB : b ∈ Subgroup.normalizer (P : Set H)) (hb : IsSS ρ b) :
    torus b ≤ Subgroup.normalizer (P : Set H) := by
  intro g hg
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hb g).mp hg
  rw [mem_B_iff D, hxy]
  simp [(mem_B_iff D b).mp hbB]

include hρ D in
omit [Fact p.Prime] [CharP K p] in

lemma torus_inf_P_eq_bot {b : H} (hbB : b ∈ Subgroup.normalizer (P : Set H)) (hb : IsSS ρ b) :
    ∀ g ∈ torus b, g ∈ P → g = 1 := by
  intro g hg hgP
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hb g).mp hg
  obtain ⟨t, ht⟩ := mat_of_mem_P D hgP
  have h10 := (mem_B_iff D b).mp hbB
  have hd := diag_mul_eq_one_of_upper h10 (ρ b).2
  have e00 := congrFun (congrFun (ht.symm.trans hxy) 0) 0
  have e11 := congrFun (congrFun (ht.symm.trans hxy) 1) 1
  have e01 := congrFun (congrFun (ht.symm.trans hxy) 0) 1
  simp at e00 e11 e01

  have hne : mat ρ b 0 0 - mat ρ b 1 1 ≠ 0 := by
    intro h0
    apply hb
    rw [tr]
    have : mat ρ b 1 1 = mat ρ b 0 0 := by linear_combination -h0
    rw [this] at hd ⊢
    linear_combination 4 * hd
  have hy : y = 0 := by
    have : y * (mat ρ b 0 0 - mat ρ b 1 1) = 0 := by linear_combination -e00 + e11
    exact (mul_eq_zero.mp this).resolve_right hne
  rw [hy] at e01
  simp at e01
  apply mat_injective hρ
  rw [ht, e01, mat_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

include hρ in
omit [Fact p.Prime] [CharP K p] in

lemma card_torus_eq [Finite H] {b : Subgroup.normalizer (P : Set H)} (hb : (chi D b) ^ 2 ≠ 1)
    (hgen : ∀ d : (chi D).range, d ∈ Subgroup.zpowers (⟨chi D b, b, rfl⟩ : (chi D).range)) :
    Nat.card (torus (b : H)) = Nat.card (chi D).range := by
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  have hle := torus_le_B hρ D b.2 hbss
  refine Nat.card_eq_of_bijective
    (fun g : torus (b : H) => (⟨chi D ⟨g, hle g.2⟩, _, rfl⟩ : (chi D).range)) ⟨?_, ?_⟩
  · intro g g' h
    have h1 : chi D ⟨g, hle g.2⟩ = chi D ⟨g', hle g'.2⟩ := congrArg Subtype.val h
    have : chi D (⟨g, hle g.2⟩ * ⟨g', hle g'.2⟩⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [chi_eq_one_iff D] at this
    have hmem : (g : H) * (g' : H)⁻¹ ∈ torus (b : H) := Subgroup.mul_mem _ g.2 (Subgroup.inv_mem _ g'.2)
    have := torus_inf_P_eq_bot hρ D b.2 hbss _ hmem this
    exact Subtype.ext (mul_inv_eq_one.mp this)
  · rintro ⟨d, hd⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨d, hd⟩)
    refine ⟨⟨(b : H) ^ k, Subgroup.zpow_mem _ (self_mem_torus (b : H)) k⟩, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow] at this
    change chi D ⟨(b : H) ^ k, _⟩ = d
    rw [← this, ← map_zpow]
    rfl

include hρ D in
omit [Fact p.Prime] [CharP K p] in

lemma eq_one_of_mem_normalizer_torus_of_mem_P {b : H} (hbB : b ∈ Subgroup.normalizer (P : Set H))
    (hb : IsSS ρ b) {w : H} (hw : w ∈ Subgroup.normalizer (torus b : Set H)) (hwP : w ∈ P) :
    w = 1 := by

  have h1 : w * b * w⁻¹ ∈ torus b := by
    rw [Subgroup.mem_normalizer_iff] at hw
    exact (hw b).mp (self_mem_torus b)
  have h2 : w * b * w⁻¹ * b⁻¹ ∈ torus b := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (self_mem_torus b))
  have h3 : w * b * w⁻¹ * b⁻¹ ∈ P := by
    have hb' := hbB
    rw [Subgroup.mem_set_normalizer_iff] at hb'
    have : b * w⁻¹ * b⁻¹ ∈ (P : Set H) := (hb' w⁻¹).mp (Subgroup.inv_mem _ hwP)
    have := Subgroup.mul_mem _ hwP this
    simp [mul_assoc] at this ⊢
    exact this
  have h4 := torus_inf_P_eq_bot hρ D hbB hb _ h2 h3

  have h5 : w ∈ torus b := by
    rw [mem_torus_iff]
    calc w * b = w * b * w⁻¹ * b⁻¹ * (b * w) := by group
      _ = b * w := by rw [h4, one_mul]
  exact torus_inf_P_eq_bot hρ D hbB hb _ h5 hwP

omit [Fact p.Prime] [CharP K p] in

lemma card_subtype_add_card_subtype_not {α : Type} [Finite α] (q : α → Prop) :
    Nat.card {x // q x} + Nat.card {x // ¬ q x} = Nat.card α := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl q)]

omit [Fact p.Prime] [CharP K p] in

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

include hρ in

lemma exists_conj_mem_torus [Finite H] (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
    {b : Subgroup.normalizer (P : Set H)} (hb : (chi D b) ^ 2 ≠ 1)
    (hgen : ∀ d : (chi D).range, d ∈ Subgroup.zpowers (⟨chi D b, b, rfl⟩ : (chi D).range))
    {g : H} (hgB : g ∈ Subgroup.normalizer (P : Set H)) (hg : IsSS ρ g) :
    ∃ v ∈ P, ∃ c ∈ torus (b : H), c ∉ Zsub ρ ∧ g = v * c * v⁻¹ := by
  classical
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  have hle := torus_le_B hρ D b.2 hbss

  let Φ : P × {c : torus (b : H) // (c : H) ∉ Zsub ρ} →
      {g : Subgroup.normalizer (P : Set H) // IsSS ρ (g : H)} := fun vc =>
    ⟨⟨(vc.1 : H) * vc.2.1 * (vc.1 : H)⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.le_normalizer vc.1.2) (hle vc.2.1.2)) (Subgroup.inv_mem _
      (Subgroup.le_normalizer vc.1.2))⟩, by
        have hc : IsSS ρ (vc.2.1 : H) := isSS_of_mem_torus hρ h2 hbss vc.2.1.2 vc.2.2
        change (tr (mat ρ ((vc.1 : H) * vc.2.1 * (vc.1 : H)⁻¹))) ^ 2 ≠ 4
        rw [mat_mul, mat_mul, tr_conj (mat_inv_mul (vc.1 : H))]
        exact hc⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨v, c, hc⟩ ⟨v', c', hc'⟩ h
    have h1 : (v : H) * c * (v : H)⁻¹ = (v' : H) * c' * (v' : H)⁻¹ :=
      congrArg (fun y : {g : Subgroup.normalizer (P : Set H) // IsSS ρ (g : H)} => ((y.1 : _) : H)) h

    set w : H := (v' : H)⁻¹ * v with hw
    have hwc : w * c * w⁻¹ = c' := by
      rw [hw]
      calc (v' : H)⁻¹ * v * c * ((v' : H)⁻¹ * v)⁻¹ = (v' : H)⁻¹ * ((v : H) * c * (v : H)⁻¹) * v' := by group
        _ = c' := by rw [h1]; group
    have hTc : torus (c : H) = torus (b : H) := torus_eq_of_mem hρ h2 hbss c.2 hc
    have hTc' : torus (c' : H) = torus (b : H) := torus_eq_of_mem hρ h2 hbss c'.2 hc'
    have hwN : w ∈ Subgroup.normalizer (torus (b : H) : Set H) := by
      have e1 : torus (b : H) = torus (w * c * w⁻¹) := by rw [hwc, hTc']
      have key : ∀ g : H, w * g * w⁻¹ ∈ torus (b : H) ↔ g ∈ torus (b : H) := by
        intro g
        have := mem_torus_conj_iff w (c : H) (w * g * w⁻¹)
        rw [← e1, show w⁻¹ * (w * g * w⁻¹) * w = g by group, hTc] at this
        exact this
      exact Subgroup.mem_normalizer_iff.mpr (fun g => (key g).symm)
    have hwP : w ∈ P := Subgroup.mul_mem _ (Subgroup.inv_mem _ v'.2) v.2
    have hw1 : w = 1 := eq_one_of_mem_normalizer_torus_of_mem_P hρ D b.2 hbss hwN hwP
    have hvv : v = v' := by
      apply Subtype.ext
      have : (v' : H)⁻¹ * v = 1 := hw1
      exact (inv_mul_eq_one.mp this).symm
    subst hvv
    have hcc : (c : H) = c' := by
      have := h1
      rwa [mul_left_inj, mul_right_inj] at this
    have : c = c' := Subtype.ext hcc
    subst this
    rfl

  have hcardZ : Nat.card {c : torus (b : H) // (c : H) ∈ Zsub ρ} = Nat.card (Zsub ρ) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨c.1, c.2⟩
        invFun := fun ζ => ⟨⟨ζ, Zsub_le_torus hρ (b : H) ζ.2⟩, ζ.2⟩
        left_inv := fun c => rfl
        right_inv := fun ζ => rfl }
  have hcard1 : Nat.card (P × {c : torus (b : H) // (c : H) ∉ Zsub ρ}) + Nat.card P * Nat.card (Zsub ρ)
      = Nat.card P * Nat.card (torus (b : H)) := by
    rw [Nat.card_prod, ← hcardZ, ← mul_add, add_comm,
      card_subtype_add_card_subtype_not (fun c : torus (b : H) => (c : H) ∈ Zsub ρ)]
  have hcardker : Nat.card {g : Subgroup.normalizer (P : Set H) // ¬ IsSS ρ (g : H)}
      = Nat.card (Zsub ρ) * Nat.card P := by
    rw [← card_ker_chiSq hρ D hp2 h2]
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1, by
          have := g.2; rw [isSS_iff_chi_sq_ne_one D, not_not] at this
          rw [MonoidHom.mem_ker, MonoidHom.mul_apply, ← pow_two, this]⟩
        invFun := fun g => ⟨g.1, by
          rw [isSS_iff_chi_sq_ne_one D, not_not]
          have := g.2; rw [MonoidHom.mem_ker, MonoidHom.mul_apply, ← pow_two] at this
          exact this⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have hcard2 : Nat.card {g : Subgroup.normalizer (P : Set H) // IsSS ρ (g : H)}
      + Nat.card (Zsub ρ) * Nat.card P = Nat.card P * Nat.card (torus (b : H)) := by
    rw [← hcardker, card_subtype_add_card_subtype_not, card_B D, card_torus_eq hρ D hb hgen]
  have hle' : Nat.card {g : Subgroup.normalizer (P : Set H) // IsSS ρ (g : H)} ≤
      Nat.card (P × {c : torus (b : H) // (c : H) ∉ Zsub ρ}) := by
    have := hcard1.trans hcard2.symm
    rw [mul_comm (Nat.card P) (Nat.card (Zsub ρ))] at this
    omega
  have hbij := hΦ.bijective_of_nat_card_le hle'
  obtain ⟨⟨v, c, hc⟩, hvc⟩ := hbij.2 ⟨⟨g, hgB⟩, hg⟩
  refine ⟨v, v.2, c, c.2, hc, ?_⟩
  have := congrArg (fun y : {g : Subgroup.normalizer (P : Set H) // IsSS ρ (g : H)} =>
    ((y.1 : _) : H)) hvc
  exact this.symm

end Borel

section Points

variable {H : Type} [Group H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)
variable {p : ℕ} {P : Sylow p H} (D : NormData ρ P)

def cross (v w : Fin 2 → K) : K := v 0 * w 1 - v 1 * w 0

def vecOf (ρ : H →* SL(2, K)) (s : H) : Fin 2 → K := ![mat ρ s 0 0, mat ρ s 1 0]

lemma mulVec_fin_two (M : 𝕄) (x y : K) :
    M *ᵥ ![x, y] = ![M 0 0 * x + M 0 1 * y, M 1 0 * x + M 1 1 * y] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma mat_conj_apply_one_zero (s g : H) :
    mat ρ (s⁻¹ * g * s) 1 0 = cross (vecOf ρ s) (mat ρ g *ᵥ vecOf ρ s) := by
  have e : mat ρ (s⁻¹ * g * s) = Matrix.adjugate (mat ρ s) * mat ρ g * mat ρ s := by
    rw [mat_mul, mat_mul, mat, map_inv, Matrix.SpecialLinearGroup.coe_inv]
  rw [e, Matrix.adjugate_fin_two, vecOf, mulVec_fin_two, cross]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

lemma mat_inv_mul_apply_one_zero (s s' : H) :
    mat ρ (s⁻¹ * s') 1 0 = cross (vecOf ρ s) (vecOf ρ s') := by
  have e : mat ρ (s⁻¹ * s') = Matrix.adjugate (mat ρ s) * mat ρ s' := by
    rw [mat_mul, mat, map_inv, Matrix.SpecialLinearGroup.coe_inv]
  rw [e, Matrix.adjugate_fin_two, vecOf, vecOf, cross]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

include D in

lemma smul_smul_eq_iff (g s : H) :
    g • (s • P) = s • P ↔ cross (vecOf ρ s) (mat ρ g *ᵥ vecOf ρ s) = 0 := by
  rw [← mat_conj_apply_one_zero, ← mem_B_iff D, ← Sylow.smul_eq_iff_mem_normalizer, mul_smul,
    mul_smul, inv_smul_eq_iff]

include D in
lemma smul_eq_iff_apply_one_zero (s : H) : s • P = P ↔ mat ρ s 1 0 = 0 := by
  rw [Sylow.smul_eq_iff_mem_normalizer, mem_B_iff D]

def eigVec (ρ : H →* SL(2, K)) (b : H) : Fin 2 → K := ![mat ρ b 0 1, mat ρ b 1 1 - mat ρ b 0 0]

lemma cross_mulVec_of_upper {b : H} (hb : mat ρ b 1 0 = 0) (v : Fin 2 → K) :
    cross v (mat ρ b *ᵥ v) = v 1 * cross v (eigVec ρ b) := by
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hv, mulVec_fin_two]
  simp [cross, eigVec, hb]; ring

lemma exists_smul_of_cross_eq_zero {v w : Fin 2 → K} (hw : w 1 ≠ 0) (h : cross v w = 0) :
    ∃ κ : K, v = κ • w := by
  refine ⟨v 1 / w 1, ?_⟩
  funext i; fin_cases i <;> simp
  · rw [cross] at h; field_simp; linear_combination h
  · field_simp

lemma cross_smul_left (κ : K) (v w : Fin 2 → K) : cross (κ • v) w = κ * cross v w := by
  simp [cross]; ring

lemma cross_smul_right (κ : K) (v w : Fin 2 → K) : cross v (κ • w) = κ * cross v w := by
  simp [cross]; ring

lemma cross_self (v : Fin 2 → K) : cross v v = 0 := by simp [cross]; ring

lemma eigVec_one_ne_zero {b : H} (hbB : mat ρ b 1 0 = 0) (hb : IsSS ρ b) : eigVec ρ b 1 ≠ 0 := by
  intro h0
  simp [eigVec] at h0
  apply hb
  have hd := diag_mul_eq_one_of_upper hbB (ρ b).2
  rw [tr]
  have e : mat ρ b 1 1 = mat ρ b 0 0 := by linear_combination h0
  rw [e] at hd ⊢
  linear_combination 4 * hd

include hρ D in

lemma torus_le_stab {b s : H} (hbB : b ∈ Subgroup.normalizer (P : Set H)) (hb : IsSS ρ b)
    (hs : mat ρ s 1 0 ≠ 0) (hbs : b • (s • P) = s • P) {t : H} (ht : t ∈ torus b) :
    t • (s • P) = s • P := by
  have hb10 := (mem_B_iff D b).mp hbB
  rw [smul_smul_eq_iff D] at hbs ⊢
  rw [cross_mulVec_of_upper hb10] at hbs
  have hvs1 : vecOf ρ s 1 ≠ 0 := by simpa [vecOf] using hs
  have hcr : cross (vecOf ρ s) (eigVec ρ b) = 0 := (mul_eq_zero.mp hbs).resolve_left hvs1
  obtain ⟨κ, hκ⟩ := exists_smul_of_cross_eq_zero (eigVec_one_ne_zero hb10 hb) hcr
  obtain ⟨x, y, hxy⟩ := (mem_torus_iff_exists hρ hb t).mp ht
  rw [hxy, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, cross,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have h2 : cross (vecOf ρ s) (mat ρ b *ᵥ vecOf ρ s) = 0 := by
    rw [cross_mulVec_of_upper hb10, hcr, mul_zero]
  rw [cross] at h2
  linear_combination y * h2

include D in

lemma smul_eq_smul_of_stab {b s s' : H} (hbB : b ∈ Subgroup.normalizer (P : Set H))
    (hb : IsSS ρ b) (hs : mat ρ s 1 0 ≠ 0) (hs' : mat ρ s' 1 0 ≠ 0)
    (hbs : b • (s • P) = s • P) (hbs' : b • (s' • P) = s' • P) : s' • P = s • P := by
  have hb10 := (mem_B_iff D b).mp hbB
  rw [smul_smul_eq_iff D, cross_mulVec_of_upper hb10] at hbs hbs'
  have hvs1 : vecOf ρ s 1 ≠ 0 := by simpa [vecOf] using hs
  have hvs1' : vecOf ρ s' 1 ≠ 0 := by simpa [vecOf] using hs'
  have hne := eigVec_one_ne_zero hb10 hb
  obtain ⟨κ, hκ⟩ := exists_smul_of_cross_eq_zero hne ((mul_eq_zero.mp hbs).resolve_left hvs1)
  obtain ⟨κ', hκ'⟩ := exists_smul_of_cross_eq_zero hne ((mul_eq_zero.mp hbs').resolve_left hvs1')

  rw [← inv_smul_eq_iff, ← mul_smul, smul_eq_iff_apply_one_zero D, mat_inv_mul_apply_one_zero,
    hκ, hκ', cross_smul_left, cross_smul_right, cross_self, mul_zero, mul_zero]

include D in

lemma mem_Zsub_of_stab {g s : H} (hgB : g ∈ Subgroup.normalizer (P : Set H)) (hg : ¬ IsSS ρ g)
    (hs : mat ρ s 1 0 ≠ 0) (hgs : g • (s • P) = s • P) : g ∈ Zsub ρ := by
  have h10 := (mem_B_iff D g).mp hgB
  have hd := diag_mul_eq_one_of_upper h10 (ρ g).2
  rw [IsSS, not_not, tr] at hg
  have hαδ : mat ρ g 0 0 = mat ρ g 1 1 := by
    have : (mat ρ g 0 0 - mat ρ g 1 1) ^ 2 = 0 := by linear_combination hg - 4 * hd
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    linear_combination this
  rw [smul_smul_eq_iff D, cross_mulVec_of_upper h10] at hgs
  have hvs1 : vecOf ρ s 1 ≠ 0 := by simpa [vecOf] using hs
  have hcr := (mul_eq_zero.mp hgs).resolve_left hvs1
  simp only [cross, eigVec, hαδ, sub_self, Matrix.cons_val_one, Matrix.cons_val_zero,
    mul_zero, zero_sub, neg_eq_zero, Matrix.cons_val_fin_one] at hcr
  have hβ : mat ρ g 0 1 = 0 := (mul_eq_zero.mp hcr).resolve_left hvs1
  rw [hαδ] at hd
  have hcases : (mat ρ g 1 1 - 1) * (mat ρ g 1 1 + 1) = 0 := by linear_combination hd
  rw [mem_Zsub_iff, Matrix.eta_fin_two (mat ρ g), h10, hβ, hαδ]
  rcases mul_eq_zero.mp hcases with e | e
  · left; rw [show mat ρ g 1 1 = 1 by linear_combination e]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · right; rw [show mat ρ g 1 1 = -1 by linear_combination e]
    ext i j; fin_cases i <;> fin_cases j <;> simp

include hρ in

lemma comm_of_mem_Zsub {ζ : H} (hζ : ζ ∈ Zsub ρ) (h : H) : ζ * h = h * ζ := by
  apply mat_injective hρ
  rw [mat_mul, mat_mul]
  rcases hζ with e | e <;> rw [e] <;> simp

include hρ in

lemma smul_eq_of_mem_Zsub {ζ : H} (hζ : ζ ∈ Zsub ρ) (Q : Sylow p H) : ζ • Q = Q := by
  rw [Sylow.smul_eq_iff_mem_normalizer, Subgroup.mem_set_normalizer_iff]
  intro h
  rw [comm_of_mem_Zsub hρ hζ h, mul_inv_cancel_right]

include hρ D in

lemma eq_one_of_mem_Zsub_of_mem_P {ζ : H} (hζ : ζ ∈ Zsub ρ) (hζP : ζ ∈ P) (h2 : (2 : K) ≠ 0) :
    ζ = 1 := by
  obtain ⟨t, ht⟩ := mat_of_mem_P D hζP
  apply mat_injective hρ
  rw [mat_one]
  rcases hζ with e | e
  · exact e
  · exfalso
    have := congrFun (congrFun (e.symm.trans ht) 0) 0
    simp at this
    exact h2 (by linear_combination -this)

end Points

section OrbitCount

variable {H : Type} [Group H] [Finite H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)
variable {p : ℕ} [Fact p.Prime] [CharP K p] {P : Sylow p H} (D : NormData ρ P)
variable (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
variable {b : Subgroup.normalizer (P : Set H)} (hb : (chi D b) ^ 2 ≠ 1)
  (hgen : ∀ d : (chi D).range, d ∈ Subgroup.zpowers (⟨chi D b, b, rfl⟩ : (chi D).range))

omit [Finite H] [Fact p.Prime] [CharP K p] in
include D in
lemma not_isSS_of_mem_P {x : H} (hx : x ∈ P) : ¬ IsSS ρ x := by
  obtain ⟨t, ht⟩ := mat_of_mem_P D hx
  rw [IsSS, not_not, tr, ht]; simp; norm_num

include hρ hb hgen in
omit [Fact p.Prime] [CharP K p] in

lemma exists_eq_mul_of_mem_B {x : H} (hx : x ∈ Subgroup.normalizer (P : Set H)) :
    ∃ u ∈ P, ∃ c ∈ torus (b : H), x = u * c := by
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  have hle := torus_le_B hρ D b.2 hbss
  let Φ : P × torus (b : H) → Subgroup.normalizer (P : Set H) := fun uc =>
    ⟨(uc.1 : H) * uc.2, Subgroup.mul_mem _ (Subgroup.le_normalizer uc.1.2) (hle uc.2.2)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨u, c⟩ ⟨u', c'⟩ h
    have h1 : (u : H) * c = u' * c' := congrArg (fun y : Subgroup.normalizer (P : Set H) => (y : H)) h

    have hmem : (u' : H)⁻¹ * u ∈ torus (b : H) := by
      have : (u' : H)⁻¹ * u = c' * (c : H)⁻¹ := by
        calc (u' : H)⁻¹ * u = (u' : H)⁻¹ * (u * c) * (c : H)⁻¹ := by group
          _ = c' * (c : H)⁻¹ := by rw [h1]; group
      rw [this]; exact Subgroup.mul_mem _ c'.2 (Subgroup.inv_mem _ c.2)
    have hP' : (u' : H)⁻¹ * u ∈ P := Subgroup.mul_mem _ (Subgroup.inv_mem _ u'.2) u.2
    have h3 := torus_inf_P_eq_bot hρ D b.2 hbss _ hmem hP'
    have huu : u = u' := Subtype.ext (inv_mul_eq_one.mp h3).symm
    subst huu
    have : (c : H) = c' := mul_left_cancel h1
    rw [Subtype.ext this]
  have hcard : Nat.card (Subgroup.normalizer (P : Set H)) ≤ Nat.card (P × torus (b : H)) := by
    rw [Nat.card_prod, card_B D, card_torus_eq hρ D hb hgen]
  obtain ⟨⟨u, c⟩, huc⟩ := (hΦ.bijective_of_nat_card_le hcard).2 ⟨x, hx⟩
  exact ⟨u, u.2, c, c.2, (congrArg (fun y : Subgroup.normalizer (P : Set H) => (y : H)) huc).symm⟩

include hρ hb hgen in
omit [Fact p.Prime] [CharP K p] in

lemma not_mem_B_of_mem_normalizer_torus {n₀ : H}
    (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H)) (hn₀C : n₀ ∉ torus (b : H)) :
    n₀ ∉ Subgroup.normalizer (P : Set H) := by
  intro hn₀B
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  obtain ⟨u, hu, c, hc, rfl⟩ := exists_eq_mul_of_mem_B hρ D hb hgen hn₀B
  have huN : u ∈ Subgroup.normalizer (torus (b : H) : Set H) := by
    have : u = u * c * c⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hn₀ (Subgroup.inv_mem _ (Subgroup.le_normalizer hc))
  have := eq_one_of_mem_normalizer_torus_of_mem_P hρ D b.2 hbss huN hu
  subst this
  exact hn₀C (by rw [one_mul]; exact hc)

include hρ D in
omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma torus_smul_eq {n₀ : H} (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H))
    (hbss : IsSS ρ (b : H)) {c : H} (hc : c ∈ torus (b : H)) : c • (n₀ • P) = n₀ • P := by
  have hc' : n₀⁻¹ * c * n₀ ∈ torus (b : H) := by
    rw [Subgroup.mem_normalizer_iff''] at hn₀
    exact (hn₀ c).mp hc
  have hB : n₀⁻¹ * c * n₀ ∈ Subgroup.normalizer (P : Set H) := torus_le_B hρ D b.2 hbss hc'
  rw [← Sylow.smul_eq_iff_mem_normalizer] at hB
  calc c • (n₀ • P) = n₀ • ((n₀⁻¹ * c * n₀) • P) := by
        rw [← mul_smul, ← mul_smul, show n₀ * (n₀⁻¹ * c * n₀) = c * n₀ by group]
    _ = n₀ • P := by rw [hB]

include D in
omit [Finite H] [Fact p.Prime] [CharP K p] in
lemma apply_one_zero_ne_zero_of_smul_ne {s : H} (hs : s • P ≠ P) : mat ρ s 1 0 ≠ 0 := by
  intro h; exact hs ((smul_eq_iff_apply_one_zero D s).mpr h)

include hρ hp2 h2 hb hgen in

lemma exists_eq_smul_of_stab {n₀ : H} (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H))
    (hn₀C : n₀ ∉ torus (b : H)) {Q : Sylow p H} (hQ : Q ≠ P)
    {g : H} (hgB : g ∈ Subgroup.normalizer (P : Set H)) (hg : IsSS ρ g) (hgQ : g • Q = Q) :
    ∃ u ∈ P, Q = u • (n₀ • P) := by
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  haveI : MulAction.IsPretransitive H (Sylow p H) := inferInstance
  obtain ⟨s, rfl⟩ := MulAction.exists_smul_eq H P Q
  have hs : mat ρ s 1 0 ≠ 0 := apply_one_zero_ne_zero_of_smul_ne D hQ
  obtain ⟨u, hu, c, hc, hcZ, rfl⟩ := exists_conj_mem_torus hρ D hp2 h2 hb hgen hgB hg
  have hcss : IsSS ρ c := isSS_of_mem_torus hρ h2 hbss hc hcZ
  have hcB : c ∈ Subgroup.normalizer (P : Set H) := torus_le_B hρ D b.2 hbss hc
  have hTc : torus c = torus (b : H) := torus_eq_of_mem hρ h2 hbss hc hcZ

  have h1 : c • ((u⁻¹ * s) • P) = (u⁻¹ * s) • P := by
    have e : (u⁻¹ * (u * c * u⁻¹) * u) • ((u⁻¹ * s) • P) = (u⁻¹ * s) • P := by
      rw [mul_smul u⁻¹ s, ← mul_smul, show u⁻¹ * (u * c * u⁻¹) * u * u⁻¹ = u⁻¹ * (u * c * u⁻¹)
        by group, mul_smul, hgQ]
    rwa [show u⁻¹ * (u * c * u⁻¹) * u = c by group] at e
  have hus : mat ρ (u⁻¹ * s) 1 0 ≠ 0 := by
    apply apply_one_zero_ne_zero_of_smul_ne D
    intro h
    rw [mul_smul, inv_smul_eq_iff] at h
    have : u • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hu)
    exact hQ (h.trans this)

  have h3 : (b : H) • ((u⁻¹ * s) • P) = (u⁻¹ * s) • P :=
    torus_le_stab hρ D hcB hcss hus h1 (by rw [hTc]; exact self_mem_torus (b : H))
  have h4 : (b : H) • (n₀ • P) = n₀ • P := torus_smul_eq hρ D hn₀ hbss (self_mem_torus (b : H))
  have hn₀B := not_mem_B_of_mem_normalizer_torus hρ D hb hgen hn₀ hn₀C
  have hn₀' : mat ρ n₀ 1 0 ≠ 0 := fun h => hn₀B ((mem_B_iff D n₀).mpr h)
  have h5 := smul_eq_smul_of_stab D b.2 hbss hn₀' hus h4 h3
  refine ⟨u, hu, ?_⟩
  rw [← h5, ← mul_smul, mul_inv_cancel_left]

omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma card_subgroupOf_eq {T : Subgroup H} (hT : T ≤ Subgroup.normalizer (P : Set H)) :
    Nat.card (T.subgroupOf (Subgroup.normalizer (P : Set H))) = Nat.card T :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv

include hρ hp2 h2 hb hgen in

lemma card_stabilizer_orbit {n₀ : H} (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H))
    (hn₀C : n₀ ∉ torus (b : H)) (β : Subgroup.normalizer (P : Set H)) :
    Nat.card (MulAction.stabilizer (Subgroup.normalizer (P : Set H)) (β • n₀ • P)) =
      Nat.card (chi D).range := by
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.card_map_of_injective
    (MulAut.conj β).injective]
  apply le_antisymm
  ·
    haveI : Finite (chi D).range :=
      Finite.of_surjective (chi D).rangeRestrict (chi D).rangeRestrict_surjective
    refine Nat.card_le_card_of_injective (fun x => (⟨chi D x.1, x.1, rfl⟩ : (chi D).range)) ?_
    intro x y hxy
    have h1 : chi D x.1 = chi D y.1 := congrArg Subtype.val hxy
    have hker : chi D (x.1 * (y.1)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [chi_eq_one_iff D] at hker
    have hstab : (x.1 * (y.1)⁻¹) • (n₀ • P) = n₀ • P := (MulAction.stabilizer _ (n₀ • P)).mul_mem x.2
      ((MulAction.stabilizer _ (n₀ • P)).inv_mem y.2)
    have hn₀B := not_mem_B_of_mem_normalizer_torus hρ D hb hgen hn₀ hn₀C
    have hn₀' : mat ρ n₀ 1 0 ≠ 0 := fun h => hn₀B ((mem_B_iff D n₀).mpr h)
    have hZ := mem_Zsub_of_stab D (x.1 * (y.1)⁻¹).2 (not_isSS_of_mem_P D hker) hn₀' hstab
    have h1' := eq_one_of_mem_Zsub_of_mem_P hρ D hZ hker h2
    apply Subtype.ext
    have : x.1 * (y.1)⁻¹ = 1 := Subtype.ext h1'
    exact mul_inv_eq_one.mp this
  ·
    rw [← card_torus_eq hρ D hb hgen, ← card_subgroupOf_eq (torus_le_B hρ D b.2 hbss)]
    apply Subgroup.card_le_of_le
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact torus_smul_eq hρ D hn₀ hbss hx

include hρ hp2 h2 hb hgen in

lemma card_stabilizer_free {n₀ : H} (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H))
    (hn₀C : n₀ ∉ torus (b : H)) {Q : Sylow p H} (hQ : Q ≠ P)
    (hQ' : ∀ u ∈ P, Q ≠ u • (n₀ • P)) :
    Nat.card (MulAction.stabilizer (Subgroup.normalizer (P : Set H)) Q) = Nat.card (Zsub ρ) := by
  rw [← card_subgroupOf_eq (Zsub_le_B D)]
  congr 1
  apply congrArg
  ext x
  rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
  constructor
  · intro hx
    haveI : MulAction.IsPretransitive H (Sylow p H) := inferInstance
    obtain ⟨s, rfl⟩ := MulAction.exists_smul_eq H P Q
    have hs : mat ρ s 1 0 ≠ 0 := apply_one_zero_ne_zero_of_smul_ne D hQ
    by_cases hss : IsSS ρ (x : H)
    · exfalso
      obtain ⟨u, hu, e⟩ := exists_eq_smul_of_stab hρ D hp2 h2 hb hgen hn₀ hn₀C hQ x.2 hss hx
      exact hQ' u hu e
    · exact mem_Zsub_of_stab D x.2 hss hs hx
  · intro hx
    exact smul_eq_of_mem_Zsub hρ hx Q

include hρ hp2 h2 in

lemma card_range_chi_eq :
    Nat.card (chi D).range = Nat.card (Zsub ρ) * Nat.card (chi D * chi D).range := by
  have h1 := card_B D
  have h2' : Nat.card (Subgroup.normalizer (P : Set H)) =
      Nat.card (chi D * chi D).ker * Nat.card (chi D * chi D).range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [card_ker_chiSq hρ D hp2 h2] at h2'
  have hq : 0 < Nat.card P := Nat.card_pos
  have : Nat.card P * Nat.card (chi D).range =
      Nat.card P * (Nat.card (Zsub ρ) * Nat.card (chi D * chi D).range) := by
    rw [← h1, h2']; ring
  exact Nat.eq_of_mul_eq_mul_left hq this

include hρ hp2 h2 hb hgen in

lemma exists_card_sylow_eq {n₀ : H} (hn₀ : n₀ ∈ Subgroup.normalizer (torus (b : H) : Set H))
    (hn₀C : n₀ ∉ torus (b : H)) :
    ∃ k : ℕ, Nat.card (Sylow p H) =
      1 + Nat.card P + k * (Nat.card P * Nat.card (chi D * chi D).range) := by
  classical

  set B := Subgroup.normalizer (P : Set H) with hB
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype (Sylow p H) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbitRel.Quotient B (Sylow p H)) := Fintype.ofFinite _
  letI : ∀ Q : Sylow p H, Fintype (MulAction.stabilizer B Q) := fun Q => Fintype.ofFinite _
  have hformula := MulAction.card_eq_sum_card_group_div_card_stabilizer B (Sylow p H)
  let Ω := MulAction.orbitRel.Quotient B (Sylow p H)
  set f : Ω → ℕ := fun ω => Fintype.card B / Fintype.card (MulAction.stabilizer B ω.out) with hf

  set Q₀ : Sylow p H := n₀ • P with hQ₀
  let ω₁ : Ω := Quotient.mk'' P
  let ω₂ : Ω := Quotient.mk'' Q₀
  have hn₀B := not_mem_B_of_mem_normalizer_torus hρ D hb hgen hn₀ hn₀C
  have hQ₀P : Q₀ ≠ P := by
    intro h
    exact hn₀B (Sylow.smul_eq_iff_mem_normalizer.mp h)
  have hout : ∀ ω : Ω, ∃ β : B, β • ω.out = ω.out ∧
      (Quotient.mk'' ω.out : Ω) = ω := fun ω => ⟨1, one_smul _ _, Quotient.out_eq' ω⟩
  have hmem : ∀ (Q : Sylow p H) (ω : Ω), (Quotient.mk'' Q : Ω) = ω → ∃ β : B, ω.out = β • Q := by
    intro Q ω h
    have : (Quotient.mk'' ω.out : Ω) = Quotient.mk'' Q := (Quotient.out_eq' ω).trans h.symm
    have := Quotient.exact' this
    rw [MulAction.orbitRel_apply] at this
    obtain ⟨β, hβ⟩ := this
    exact ⟨β, hβ.symm⟩
  have hBfix : ∀ β : B, β • P = P := fun β =>
    Sylow.smul_eq_iff_mem_normalizer.mpr β.2
  have hω₁₂ : ω₁ ≠ ω₂ := by
    intro h
    obtain ⟨β, hβ⟩ := hmem Q₀ ω₁ h.symm
    obtain ⟨β', hβ'⟩ := hmem P ω₁ rfl
    apply hQ₀P
    have : (β : B) • Q₀ = β' • P := hβ.symm.trans hβ'
    rw [hBfix β'] at this
    calc Q₀ = β⁻¹ • (β • Q₀) := by rw [inv_smul_smul]
      _ = P := by rw [this]; exact hBfix β⁻¹

  have hcardB : Fintype.card B = Nat.card P * Nat.card (chi D).range := by
    rw [Fintype.card_eq_nat_card]; exact card_B D
  have hc : Nat.card (chi D).range = Nat.card (Zsub ρ) * Nat.card (chi D * chi D).range :=
    card_range_chi_eq hρ D hp2 h2
  have hz : 0 < Nat.card (Zsub ρ) := Nat.card_pos
  have hcpos : 0 < Nat.card (chi D).range := Nat.card_pos
  have hf₁ : f ω₁ = 1 := by
    obtain ⟨β, hβ⟩ := hmem P ω₁ rfl
    rw [hBfix] at hβ
    have htop : MulAction.stabilizer B P = ⊤ := by
      rw [eq_top_iff]; intro β' _; exact hBfix β'
    simp only [hf]
    rw [hβ, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, htop, Subgroup.card_top]
    exact Nat.div_self Nat.card_pos
  have hf₂ : f ω₂ = Nat.card P := by
    obtain ⟨β, hβ⟩ := hmem Q₀ ω₂ rfl
    simp only [hf]
    rw [hβ, hcardB, Fintype.card_eq_nat_card, hQ₀,
      card_stabilizer_orbit hρ D hp2 h2 hb hgen hn₀ hn₀C β]
    exact Nat.mul_div_cancel _ hcpos
  have hf₃ : ∀ ω ∈ (Finset.univ.erase ω₁).erase ω₂,
      f ω = Nat.card P * Nat.card (chi D * chi D).range := by
    intro ω hω
    rw [Finset.mem_erase, Finset.mem_erase] at hω
    obtain ⟨hω₂, hω₁, -⟩ := hω
    have hP' : ω.out ≠ P := by
      intro h; apply hω₁
      rw [← Quotient.out_eq' ω, h]
    have hQ' : ∀ u ∈ P, ω.out ≠ u • (n₀ • P) := by
      intro u hu h
      apply hω₂
      rw [← Quotient.out_eq' ω, h]
      apply Quotient.sound'
      rw [MulAction.orbitRel_apply]
      exact ⟨⟨u, Subgroup.le_normalizer hu⟩, rfl⟩
    simp only [hf]
    rw [hcardB, Fintype.card_eq_nat_card, card_stabilizer_free hρ D hp2 h2 hb hgen hn₀ hn₀C hP' hQ',
      hc, ← mul_assoc, mul_comm (Nat.card P) (Nat.card (Zsub ρ)), mul_assoc]
    exact Nat.mul_div_cancel_left _ hz
  refine ⟨((Finset.univ.erase ω₁).erase ω₂).card, ?_⟩
  rw [← Nat.card_eq_fintype_card] at hformula
  rw [hformula, ← Finset.add_sum_erase _ f (Finset.mem_univ ω₁),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨hω₁₂.symm, Finset.mem_univ ω₂⟩), hf₁, hf₂,
    Finset.sum_const_nat hf₃, add_assoc]

end OrbitCount

section ConjSub

variable {H : Type} [Group H] {ρ : H →* SL(2, K)}

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

end ConjSub

section Free

variable {H : Type} [Group H] [Finite H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)
variable {p : ℕ} [Fact p.Prime] [CharP K p] {P : Sylow p H} (D : NormData ρ P)
variable (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0)
variable {b : Subgroup.normalizer (P : Set H)} (hb : (chi D b) ^ 2 ≠ 1)
  (hgen : ∀ d : (chi D).range, d ∈ Subgroup.zpowers (⟨chi D b, b, rfl⟩ : (chi D).range))

include hρ hp2 h2 hb hgen in

lemma mem_Zsub_of_smul_eq_of_not_isConjSub {h : H} (hh : IsSS ρ h)
    (hnc : ¬ IsConjSub (torus (b : H)) (torus h)) {g : H} (hg : g ∈ torus h)
    {Q : Sylow p H} (hgQ : g • Q = Q) : g ∈ Zsub ρ := by
  by_contra hgZ
  have hbss : IsSS ρ (b : H) := (isSS_iff_chi_sq_ne_one D b).mpr hb
  haveI : MulAction.IsPretransitive H (Sylow p H) := inferInstance
  obtain ⟨s, rfl⟩ := MulAction.exists_smul_eq H P Q
  have hgss : IsSS ρ g := isSS_of_mem_torus hρ h2 hh hg hgZ

  have h1 : (s⁻¹ * g * s) • P = P := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff]; exact hgQ
  have hB : s⁻¹ * g * s ∈ Subgroup.normalizer (P : Set H) := Sylow.smul_eq_iff_mem_normalizer.mp h1
  have hss : IsSS ρ (s⁻¹ * g * s) := by
    change (tr (mat ρ (s⁻¹ * g * s))) ^ 2 ≠ 4
    rw [mat_mul, mat_mul, tr_conj (by rw [← mat_mul, mul_inv_cancel, mat_one] :
      mat ρ s * mat ρ s⁻¹ = 1)]
    exact hgss
  obtain ⟨u, hu, c, hc, hcZ, e⟩ := exists_conj_mem_torus hρ D hp2 h2 hb hgen hB hss
  apply hnc

  have hTc : torus c = torus (b : H) := torus_eq_of_mem hρ h2 hbss hc hcZ
  have hTg : torus g = torus h := torus_eq_of_mem hρ h2 hh hg hgZ
  have i1 : IsConjSub (torus (b : H)) (torus (s⁻¹ * g * s)) := by
    rw [e, ← hTc]; exact isConjSub_torus_conj c u
  have i2 : IsConjSub (torus g) (torus (s⁻¹ * g * s)) := by
    have := isConjSub_torus_conj g s⁻¹
    rwa [inv_inv] at this
  rw [← hTg]
  exact i1.trans i2.symm

include hρ hp2 h2 hb hgen in

lemma card_torus_dvd {h : H} (hh : IsSS ρ h) (hnc : ¬ IsConjSub (torus (b : H)) (torus h)) :
    Nat.card (torus h) ∣ Nat.card (Zsub ρ) * Nat.card (Sylow p H) := by
  classical
  set T := torus h with hT
  letI : Fintype T := Fintype.ofFinite T
  letI : Fintype (Sylow p H) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbitRel.Quotient T (Sylow p H)) := Fintype.ofFinite _
  letI : ∀ Q : Sylow p H, Fintype (MulAction.stabilizer T Q) := fun Q => Fintype.ofFinite _
  have hformula := MulAction.card_eq_sum_card_group_div_card_stabilizer T (Sylow p H)
  have hstab : ∀ Q : Sylow p H, Nat.card (MulAction.stabilizer T Q) = Nat.card (Zsub ρ) := by
    intro Q
    have hZle : Zsub ρ ≤ T := Zsub_le_torus hρ h
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]
    congr 1; apply congrArg
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hg => mem_Zsub_of_smul_eq_of_not_isConjSub hρ D hp2 h2 hb hgen hh hnc g.2 hg,
      fun hg => smul_eq_of_mem_Zsub hρ hg Q⟩
  have hzT : Nat.card (Zsub ρ) ∣ Nat.card T := Subgroup.card_dvd_of_le (Zsub_le_torus hρ h)
  obtain ⟨k, hk⟩ := hzT
  have hz : 0 < Nat.card (Zsub ρ) := Nat.card_pos
  have hterm : ∀ ω : MulAction.orbitRel.Quotient T (Sylow p H),
      Fintype.card T / Fintype.card (MulAction.stabilizer T ω.out) = k := by
    intro ω
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hstab, hk]
    exact Nat.mul_div_cancel_left k hz
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.sum_const, smul_eq_mul,
    Fintype.card_eq_nat_card] at hformula
  rw [hformula, hk]
  exact ⟨(Finset.univ : Finset (MulAction.orbitRel.Quotient T (Sylow p H))).card, by ring⟩

end Free

section Export

variable {H : Type} [Group H] [Finite H] {ρ : H →* SL(2, K)} (hρ : Function.Injective ρ)
variable {p : ℕ} [Fact p.Prime] [CharP K p] {P : Sylow p H} (D : NormData ρ P)

omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma card_range_chi_eq_card_setRange :
    Nat.card (chi D).range =
      Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) => mat ρ x 0 0) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨(u.1 : K), by
        obtain ⟨x, hx⟩ := u.2
        exact ⟨x, by rw [← hx]; rfl⟩⟩
      invFun := fun a => ⟨Units.mk0 a.1 (by
          obtain ⟨x, hx⟩ := a.2
          rw [← hx]; exact (chi D x).ne_zero), by
        obtain ⟨x, hx⟩ := a.2
        exact ⟨x, Units.ext (by rw [Units.val_mk0, ← hx]; rfl)⟩⟩
      left_inv := fun u => Subtype.ext (Units.ext rfl)
      right_inv := fun a => rfl }

omit [Finite H] [Fact p.Prime] [CharP K p] in

lemma card_range_chiSq_eq_card_setRange :
    Nat.card (chi D * chi D).range =
      Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) => (mat ρ x 0 0) ^ 2) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨(u.1 : K), by
        obtain ⟨x, hx⟩ := u.2
        refine ⟨x, ?_⟩
        show mat ρ x 0 0 ^ 2 = _
        rw [← hx, MonoidHom.mul_apply, Units.val_mul, chi_apply, pow_two]⟩
      invFun := fun a => ⟨Units.mk0 a.1 (by
          obtain ⟨x, hx⟩ := a.2
          have hx' : mat ρ x 0 0 ^ 2 = a.1 := hx
          rw [← hx']; exact pow_ne_zero _ (chi D x).ne_zero), by
        obtain ⟨x, hx⟩ := a.2
        have hx' : mat ρ x 0 0 ^ 2 = a.1 := hx
        exact ⟨x, Units.ext (by
          rw [Units.val_mk0, ← hx', MonoidHom.mul_apply, Units.val_mul, chi_apply, pow_two])⟩⟩
      left_inv := fun u => Subtype.ext (Units.ext rfl)
      right_inv := fun a => rfl }

end Export

end P2mDicksonBorel

open P2mDicksonBorel in
theorem solution
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (P : Sylow p H) (hP : ∀ x : H, x ∈ P ↔ ∃ t : K, ρ x = ModularCurve.upperElem t)
    (hne : ∃ a : K, a ≠ 0 ∧ ∃ u : H,
      ((ρ u : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1]) :
    Nat.card (Subgroup.normalizer (P : Set H)) =
      Nat.card P * Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
    Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) =
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
          ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1} *
        Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
          (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ∧
    (Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
        (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2) ≠ 1 →
      ∃ b : H, b ∈ Subgroup.normalizer (P : Set H) ∧
        (((ρ b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
          ((ρ b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 ∧
        Nat.card (Subgroup.centralizer ({b} : Set H)) =
          Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
            ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
        ((∃ n₀ : H, n₀ ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set H) : Set H) ∧
            n₀ ∉ Subgroup.centralizer ({b} : Set H)) →
          ∃ k : ℕ, Nat.card (Sylow p H) = 1 + Nat.card P + k * (Nat.card P *
            Nat.card (Set.range fun x : Subgroup.normalizer (P : Set H) =>
              (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0) ^ 2))) ∧
        (∀ h : H, (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
            ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4 →
          (¬ ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
              s⁻¹ * g * s ∈ Subgroup.centralizer ({b} : Set H)) →
          Nat.card (Subgroup.centralizer ({h} : Set H)) ∣
            Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
              ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1} * Nat.card (Sylow p H))) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  have D : NormData ρ P := ⟨hP, hne⟩
  rw [← card_range_chi_eq_card_setRange D, ← card_range_chiSq_eq_card_setRange D]
  refine ⟨card_B D, card_range_chi_eq hρ D hp2 h2, fun hcb => ?_⟩
  obtain ⟨b, hb, hgen⟩ := exists_generator_chi D hcb
  refine ⟨b, b.2, (isSS_iff_chi_sq_ne_one D b).mpr hb, card_torus_eq hρ D hb hgen, ?_, ?_⟩
  · rintro ⟨n₀, hn₀, hn₀C⟩
    exact exists_card_sylow_eq hρ D hp2 h2 hb hgen hn₀ hn₀C
  · intro h hh hnc
    exact card_torus_dvd hρ D hp2 h2 hb hgen hh hnc

end S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_borel_orbit_structure_of_sylow_eq_upper (solution)
