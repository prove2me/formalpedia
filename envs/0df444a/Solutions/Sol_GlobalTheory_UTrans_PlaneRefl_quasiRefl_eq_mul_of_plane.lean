-- Prove2me | solution 1 for GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:37.655467+00:00
-- url     : https://prove2.me/submissions/5ef25748-4dbb-4e4f-9717-6984ef7f24b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpecialUnitaryHyperbolicPlaneMemTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPla
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_conj
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mulVec
import Theorems.Thm_GlobalTheory_UTrans_Model_hf_add_smul_left
import Theorems.Thm_GlobalTheory_UTrans_Model_hf_add_smul_right
import Theorems.Thm_GlobalTheory_UTrans_Model_hf_conj
import Theorems.Thm_GlobalTheory_UTrans_Model_tv_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
namespace GlobalTheory.UTrans.PlaneRefl
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_zero' {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (w : Fin n → E) : _root_.GlobalTheory.UTrans.tv σ G w 0 = 1 := by
  unfold _root_.GlobalTheory.UTrans.tv
  ext i j
  simp
open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma quasiReflection_eq_transvectionGen_mul_shifted {E : Type} [Field E] [CharZero E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hinv : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (x z : Fin n → E) (a u : E) (hzz : _root_.GlobalTheory.UTrans.hf σ G z z = 0)
    (hxz : _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0) (hxx : _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0)
    (hyy : _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0) (hu : u * σ u = 1)
    (hu1 : u ≠ 1)
    (hD : u * σ a * _root_.GlobalTheory.UTrans.hf σ G x z + a * σ (_root_.GlobalTheory.UTrans.hf σ G x z) ≠ 0) :
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by
  set β := _root_.GlobalTheory.UTrans.hf σ G x z with hβ
  set α := _root_.GlobalTheory.UTrans.hf σ G x x with hα
  have hzx : _root_.GlobalTheory.UTrans.hf σ G z x = σ β := by
    rw [hβ, _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG]
  have hαr : σ α = α := by rw [hα, _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG]
  have hα' : _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) = α + σ a * β + a * σ β := by
    rw [_root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right,
      _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, hzz, hzx]
    ring
  rw [hα'] at hyy ⊢
  clear_value α β
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  have hsu : σ u = u⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.2 hu1
  have hsβ : σ β ≠ 0 := fun h => hxz (by rw [← hinv β, h, map_zero])
  obtain ⟨D, hDdef⟩ : ∃ D, D = u * σ a * β + a * σ β := ⟨_, rfl⟩
  rw [← hDdef] at hD
  obtain ⟨N, hN⟩ : ∃ N, N = β * σ β := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = -(σ a * β + a * σ β) * u * α / (D * (u - 1) * N) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (u * α * (σ a * β + a * σ β) - (u - 1) ^ 2 * (σ a * β) * (a * σ β)) /
      (D * (u - 1) * N) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = -(D * α / ((α + σ a * β + a * σ β) * (u - 1) * N)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (u - 1) / α := ⟨_, rfl⟩
  have hσc : σ c = (u⁻¹ - 1) / α := by rw [hc, map_div₀, map_sub, map_one, hsu, hαr]
  have hyy2 : α + a * σ β + σ a * β ≠ 0 := by rw [add_assoc, add_comm (a * σ β), ← add_assoc]; exact hyy
  have hN0 : N ≠ 0 := by rw [hN]; exact mul_ne_zero hxz hsβ
  have hσD : σ D = D / u := by
    rw [hDdef]
    simp only [map_add, map_mul, hinv, hsu]
    field_simp
    ring
  have hσN : σ N = N := by rw [hN]; simp only [map_mul, hinv]; ring
  have trA : A + σ A = 0 := by
    rw [hA]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add, map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  have trB : B + σ B = 0 := by
    rw [hB]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add, map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  have trR : R + σ R = 0 := by
    rw [hR]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add, map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  obtain ⟨w, hw⟩ : ∃ w, w = z + (c * σ β) • x := ⟨_, rfl⟩
  have hww : _root_.GlobalTheory.UTrans.hf σ G w w = 0 := by
    rw [hw, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right,
      _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, hzz, hzx, map_mul, hσc, hinv, ← hβ, ← hα]
    rw [hc]
    field_simp
    ring
  refine ⟨_root_.GlobalTheory.UTrans.tv σ G z A * _root_.GlobalTheory.UTrans.tv σ G w R *
      _root_.GlobalTheory.UTrans.tv σ G z B, ?_, ?_⟩
  · unfold _root_.GlobalTheory.UTrans.TvGen
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact Submonoid.subset_closure ⟨z, A, hzz, trA, rfl⟩
    · exact Submonoid.subset_closure ⟨w, R, hww, trR, rfl⟩
    · exact Submonoid.subset_closure ⟨z, B, hzz, trB, rfl⟩
  rw [← hc]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [_root_.GlobalTheory.UTrans.Model.tv_mulVec]
  subst hw
  simp only [_root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right]
  simp only [hzz, hzx, ← hβ, ← hα]
  simp only [map_mul, hσc, hinv]
  generalize _root_.GlobalTheory.UTrans.hf σ G v x = p at *
  generalize _root_.GlobalTheory.UTrans.hf σ G v z = q at *
  subst hA hB hR hc hDdef hN
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_isometry {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hinv : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (w : Fin n → E) (t : E)
    (ht : t + σ t + t * σ t * _root_.GlobalTheory.UTrans.hf σ G w w = 0) (v v' : Fin n → E) :
    _root_.GlobalTheory.UTrans.hf σ G ((_root_.GlobalTheory.UTrans.tv σ G w t).mulVec v)
      ((_root_.GlobalTheory.UTrans.tv σ G w t).mulVec v') = _root_.GlobalTheory.UTrans.hf σ G v v' := by
  simp only [_root_.GlobalTheory.UTrans.Model.tv_mulVec, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left,
    _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, map_mul]
  rw [_root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG v' w]
  linear_combination (_root_.GlobalTheory.UTrans.hf σ G v w * _root_.GlobalTheory.UTrans.hf σ G w v') * ht
open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma isometry_mul_transvection {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G (g.mulVec v) (g.mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w) (w : Fin n → E) (t : E) :
    g * _root_.GlobalTheory.UTrans.tv σ G w t = _root_.GlobalTheory.UTrans.tv σ G (g.mulVec w) t * g := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UTrans.Model.tv_mulVec, hg,
    Matrix.mulVec_add, Matrix.mulVec_smul]
open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_mul_isotropic {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (w : Fin n → E) (hw : _root_.GlobalTheory.UTrans.hf σ G w w = 0)
    (s t : E) : _root_.GlobalTheory.UTrans.tv σ G w s * _root_.GlobalTheory.UTrans.tv σ G w t =
      _root_.GlobalTheory.UTrans.tv σ G w (s + t) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UTrans.Model.tv_mulVec,
    _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, hw]
  rw [add_assoc, ← add_smul]
  congr 2
  ring
end GlobalTheory.UTrans.PlaneRefl
end

set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.PlaneRefl
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
namespace GlobalTheory.UTrans.PlaneRefl
namespace _root_.GlobalTheory.UTrans.PlaneRefl
theorem _root_.solution : ∀ (E : Type) [Field E] [CharZero E]
    (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm σ G →
    ∀ (x z : Fin n → E) (a u : E), _root_.GlobalTheory.UTrans.hf σ G z z = 0 →
    _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0 → _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0 →
    _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 →
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by
  intro E _ _ n σ G hH x z a u hzz hxz hxx hyy hu
  obtain ⟨hinv, hne, hG, -⟩ := hH
  by_cases hu1 : u = 1
  · subst hu1
    refine ⟨1, one_mem _, ?_⟩
    simp only [sub_self, zero_div, transvection_zero', one_mul]
  by_cases hD : u * σ a * _root_.GlobalTheory.UTrans.hf σ G x z +
      a * σ (_root_.GlobalTheory.UTrans.hf σ G x z) ≠ 0
  · exact quasiReflection_eq_transvectionGen_mul_shifted σ G hinv hG x z a u hzz hxz hxx hyy hu hu1 hD
  push_neg at hD
  obtain ⟨e, he⟩ := hne
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = e - σ e := ⟨_, rfl⟩
  have hσω : σ ω = -ω := by rw [hωdef, map_sub, hinv]; ring
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact sub_ne_zero.2 (Ne.symm he)
  set β := _root_.GlobalTheory.UTrans.hf σ G x z with hβ
  set y := x + a • z with hy
  set E₁ := _root_.GlobalTheory.UTrans.tv σ G z ω with hE₁
  set E₂ := _root_.GlobalTheory.UTrans.tv σ G z (-ω) with hE₂
  have hEiso : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G (E₁.mulVec v) (E₁.mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w :=
    transvection_isometry σ G hinv hG z ω (by rw [hσω, hzz]; ring)
  have hy1 : E₁.mulVec y = x + (a + ω * β) • z := by
    rw [hE₁, _root_.GlobalTheory.UTrans.Model.tv_mulVec, hy, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, hzz,
      ← hβ, add_smul, add_assoc]
    congr 2
    ring_nf
  have hnorm : _root_.GlobalTheory.UTrans.hf σ G (x + (a + ω * β) • z) (x + (a + ω * β) • z) =
      _root_.GlobalTheory.UTrans.hf σ G y y := by rw [← hy1, hEiso]
  have hD1 : u * σ (a + ω * β) * β + (a + ω * β) * σ β ≠ 0 := by
    have e1 : u * σ (a + ω * β) * β + (a + ω * β) * σ β = ω * β * σ β * (1 - u) := by
      rw [map_add, map_mul, hσω]
      linear_combination hD
    rw [e1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hω0 hxz) ?_) (sub_ne_zero.2 (Ne.symm hu1))
    intro h; exact hxz (by rw [← hinv β, h, map_zero])
  obtain ⟨m₁, hm₁, h₁⟩ := quasiReflection_eq_transvectionGen_mul_shifted σ G hinv hG x z (a + ω * β) u hzz hxz hxx
    (by rw [hnorm]; exact hyy) hu hu1 hD1
  rw [hnorm] at h₁
  set c' := (u - 1) / _root_.GlobalTheory.UTrans.hf σ G y y with hc'
  have hyr : σ (_root_.GlobalTheory.UTrans.hf σ G y y) = _root_.GlobalTheory.UTrans.hf σ G y y :=
    _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG y y
  have hτiso : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G
      ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec v) ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w := by
    refine transvection_isometry σ G hinv hG y c' ?_
    rw [hc', map_div₀, map_sub, map_one, hyr]
    field_simp
    linear_combination hu
  have hc1 : E₁ * _root_.GlobalTheory.UTrans.tv σ G y c' = _root_.GlobalTheory.UTrans.tv σ G (x + (a + ω * β) • z) c' * E₁ := by
    rw [isometry_mul_transvection σ G E₁ hEiso, hy1]
  have hEE : E₁ * E₂ = 1 := by
    rw [hE₁, hE₂, transvection_mul_isotropic σ G z hzz, add_neg_cancel, transvection_zero']
  have hc2 : _root_.GlobalTheory.UTrans.tv σ G y c' * E₂ =
      _root_.GlobalTheory.UTrans.tv σ G ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec z) (-ω) *
        _root_.GlobalTheory.UTrans.tv σ G y c' := by
    rw [hE₂, isometry_mul_transvection σ G _ hτiso]
  refine ⟨m₁ * E₁ * _root_.GlobalTheory.UTrans.tv σ G ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec z) (-ω), ?_, ?_⟩
  · refine mul_mem (mul_mem hm₁ ?_) ?_
    · unfold _root_.GlobalTheory.UTrans.TvGen
      exact Submonoid.subset_closure ⟨z, ω, hzz, by rw [hσω]; ring, rfl⟩
    · unfold _root_.GlobalTheory.UTrans.TvGen
      exact Submonoid.subset_closure ⟨_, -ω, by rw [hτiso, hzz], by rw [map_neg, hσω]; ring, rfl⟩
  · have key : _root_.GlobalTheory.UTrans.tv σ G (x + (a + ω * β) • z) c' =
        E₁ * _root_.GlobalTheory.UTrans.tv σ G y c' * E₂ := by
      rw [hc1, mul_assoc, hEE, mul_one]
    rw [h₁, key, mul_assoc E₁, hc2]
    simp only [mul_assoc]
end _root_.GlobalTheory.UTrans.PlaneRefl
end GlobalTheory.UTrans.PlaneRefl
