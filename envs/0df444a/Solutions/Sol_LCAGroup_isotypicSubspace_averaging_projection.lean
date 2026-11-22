-- Prove2me | solution 1 for LCAGroup.isotypicSubspace_averaging_projection
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:55:16.866433+00:00
-- url     : https://prove2.me/submissions/044c1dd3-8623-47cd-8a0b-073011472638

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace

open MeasureTheory

set_option autoImplicit false

namespace Sol_LCAGroup_isotypicSubspace_averaging_projection

open LCAGroup

set_option linter.unusedSectionVars false
open scoped InnerProductSpace ComplexConjugate

variable {K : Type*} [CommGroup K] [TopologicalSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a unitary representation, the adjoint of `π k` is `π k⁻¹`. -/
lemma inner_map_eq (π : K →* (H →L[ℂ] H)) (hπ_unitary : ∀ k, π k ∈ unitary (H →L[ℂ] H))
    (k : K) (w v : H) : ⟪w, π k v⟫_ℂ = ⟪π k⁻¹ w, v⟫_ℂ := by
  have hstar : star (π k) = π k⁻¹ := by
    have h1 : star (π k) * π k = 1 := Unitary.star_mul_self_of_mem (hπ_unitary k)
    calc star (π k) = star (π k) * (π k * π k⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = (star (π k) * π k) * π k⁻¹ := by rw [mul_assoc]
      _ = π k⁻¹ := by rw [h1, one_mul]
  rw [← hstar, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma coe_inv_apply (ω : PontryaginDual K) (k : K) : ((ω k⁻¹ : Circle) : ℂ) = conj (ω k : ℂ) := by
  rw [map_inv, Circle.coe_inv_eq_conj]

lemma conj_mul_self (ω : PontryaginDual K) (k : K) : conj (ω k : ℂ) * (ω k : ℂ) = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

lemma mul_inv_apply (ω : PontryaginDual K) (k : K) : (ω k : ℂ) * (ω k⁻¹ : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel, map_one, Circle.coe_one]

/-- The key identity: `⟪w, v - conj(ω k) π(k) v⟫ = ⟪w - ω(k) π(k⁻¹) w, v⟫`. -/
lemma inner_coinv (π : K →* (H →L[ℂ] H)) (hπ_unitary : ∀ k, π k ∈ unitary (H →L[ℂ] H))
    (ω : PontryaginDual K) (k : K) (w v : H) :
    ⟪w, v - (conj (ω k : ℂ)) • π k v⟫_ℂ = ⟪w - (ω k : ℂ) • π k⁻¹ w, v⟫_ℂ := by
  rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
    inner_map_eq π hπ_unitary]

/-- Membership in the isotypic subspace, in the form `w = ω(k) π(k⁻¹) w`. -/
lemma mem_iso_iff (π : K →* (H →L[ℂ] H)) (ω : PontryaginDual K) (w : H) :
    w ∈ isotypicSubspace π (fun k => (ω k : ℂ)) ↔ ∀ k, w = (ω k : ℂ) • π k⁻¹ w := by
  rw [mem_isotypicSubspace]
  constructor
  · intro hw k
    rw [hw k⁻¹, smul_smul, mul_inv_apply, one_smul]
  · intro hw k
    have h := hw k⁻¹
    rw [inv_inv] at h
    conv_rhs => rw [h]
    rw [smul_smul, mul_inv_apply, one_smul]

end Sol_LCAGroup_isotypicSubspace_averaging_projection

open Sol_LCAGroup_isotypicSubspace_averaging_projection
open scoped InnerProductSpace ComplexConjugate

theorem solution
    (K : Type*) [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H)) (hπ_unitary : ∀ k, π k ∈ unitary (H →L[ℂ] H))
    (hπ_cont : ∀ v : H, Continuous fun k => π k v) (ω : PontryaginDual K) :
    (∀ v : H, ((μ.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ω k : ℂ)) • π k v ∂μ) ∈
        LCAGroup.isotypicSubspace π fun k => (ω k : ℂ)) ∧
      (∀ v : H, (v - (μ.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ω k : ℂ)) • π k v ∂μ) ∈
        (LCAGroup.isotypicSubspace π fun k => (ω k : ℂ))ᗮ) ∧
      (LCAGroup.isotypicSubspace π fun k => (ω k : ℂ))ᗮ =
        (Submodule.span ℂ
          {u : H | ∃ (v : H) (k : K), u = v - (starRingEnd ℂ (ω k : ℂ)) • π k v}).topologicalClosure := by
  have hωc : Continuous fun k => (ω k : ℂ) :=
    continuous_subtype_val.comp ω.continuous
  have hcont : ∀ v : H, Continuous fun k => (starRingEnd ℂ (ω k : ℂ)) • π k v := fun v =>
    (Complex.continuous_conj.comp hωc).smul (hπ_cont v)
  have hint : ∀ v : H, Integrable (fun k => (starRingEnd ℂ (ω k : ℂ)) • π k v) μ := fun v =>
    integrableOn_univ.1 ((hcont v).continuousOn.integrableOn_compact isCompact_univ)
  have hμ : μ.real Set.univ ≠ 0 := measureReal_univ_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    intro v
    rw [LCAGroup.mem_isotypicSubspace]
    intro h
    set c : ℝ := (μ.real Set.univ)⁻¹
    rw [ContinuousLinearMap.map_smul_of_tower, ← ContinuousLinearMap.integral_comp_comm _ (hint v)]
    have h1 : (fun k => π h ((starRingEnd ℂ (ω k : ℂ)) • π k v)) =
        fun k => (fun x => (starRingEnd ℂ (ω (h⁻¹ * x) : ℂ)) • π x v) (h * k) := by
      funext k
      simp only [inv_mul_cancel_left, map_mul, ContinuousLinearMap.map_smul,
        mul_apply_eq_comp]
    rw [h1, integral_mul_left_eq_self (fun x => (starRingEnd ℂ (ω (h⁻¹ * x) : ℂ)) • π x v) h]
    have h2 : (fun x => (starRingEnd ℂ (ω (h⁻¹ * x) : ℂ)) • π x v) =
        fun x => (ω h : ℂ) • ((starRingEnd ℂ (ω x : ℂ)) • π x v) := by
      funext x
      rw [smul_smul, map_mul, Circle.coe_mul, map_mul, coe_inv_apply, Complex.conj_conj]
    rw [h2, integral_smul, smul_comm]
  · -- part 2
    intro v
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [LCAGroup.mem_isotypicSubspace] at hw
    rw [inner_sub_right, ← Complex.coe_smul, inner_smul_right, ← integral_inner (hint v)]
    have h3 : (fun k => ⟪w, (starRingEnd ℂ (ω k : ℂ)) • π k v⟫_ℂ) = fun _ => ⟪w, v⟫_ℂ := by
      funext k
      rw [inner_smul_right, inner_map_eq π hπ_unitary, hw k⁻¹, inner_smul_left, coe_inv_apply,
        Complex.conj_conj, ← mul_assoc, conj_mul_self, one_mul]
    rw [h3, integral_const, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hμ, Complex.ofReal_one, one_mul, sub_self]
  · -- part 3
    have key : LCAGroup.isotypicSubspace (fun k => π k) (fun k => (ω k : ℂ)) =
        (Submodule.span ℂ
          {u : H | ∃ (v : H) (k : K), u = v - (starRingEnd ℂ (ω k : ℂ)) • π k v})ᗮ := by
      ext w
      rw [mem_iso_iff, Submodule.mem_orthogonal]
      constructor
      · intro hw u hu
        have hle : Submodule.span ℂ
            {u : H | ∃ (v : H) (k : K), u = v - (starRingEnd ℂ (ω k : ℂ)) • π k v} ≤
            (ℂ ∙ w)ᗮ := by
          rw [Submodule.span_le]
          rintro _ ⟨v, k, rfl⟩
          rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left,
            inner_eq_zero_symm, inner_coinv π hπ_unitary, ← hw k, sub_self, inner_zero_left]
        exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 (hle hu)
      · intro hw k
        have h4 : ∀ v : H, ⟪w - (ω k : ℂ) • π k⁻¹ w, v⟫_ℂ = 0 := by
          intro v
          rw [← inner_coinv π hπ_unitary, inner_eq_zero_symm]
          exact hw _ (Submodule.subset_span ⟨v, k, rfl⟩)
        have h5 := h4 (w - (ω k : ℂ) • π k⁻¹ w)
        rw [inner_self_eq_zero, sub_eq_zero] at h5
        exact h5
    rw [key, Submodule.orthogonal_orthogonal_eq_closure]
