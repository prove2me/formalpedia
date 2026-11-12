-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:53:40.482861+00:00
-- url     : https://prove2.me/submissions/e9f269fc-7b10-4e65-a2e8-803cb23bb1cd

import Mathlib

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Polynomial



lemma exists_interval_avoiding {a b : ℝ} (hab : a < b) {T : Set ℝ} (hT : T.Finite) :
    ∃ t ∈ Ioo a b, t ∉ T := by
  by_contra hn
  push Not at hn
  exact (Set.Ioo_infinite hab) (hT.subset hn)

lemma finite_affine_preimage {T : Set ℝ} (hT : T.Finite) {a b : ℝ} (ha : a ≠ 0) :
    ( (fun t : ℝ => a * t + b) ⁻¹' T).Finite := by
  apply hT.preimage
  intro x hx y hy he
  exact mul_left_cancel₀ ha (by linarith)



lemma choose_three_avoiding_oai {T : Set ℝ} (hT : T.Finite)
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (h₀ : a₀ < b₀) (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
    ∃ t₀ ∈ Ioo a₀ b₀, ∃ t₁ ∈ Ioo a₁ b₁, ∃ t₂ ∈ Ioo a₂ b₂,
      t₀ ∉ T ∧ t₁ ∉ T ∧ t₂ ∉ T ∧ (t₀ + 2*t₁)/3 ∉ T ∧ 2*t₁-t₀ ∉ T ∧
      (t₀ + 4*t₂)/5 ∉ T ∧ (4*t₂-t₀)/3 ∉ T ∧ (t₁ + 2*t₂)/3 ∉ T ∧ 2*t₂-t₁ ∉ T := by
  obtain ⟨t₀, ht₀, hn₀⟩ := exists_interval_avoiding h₀ hT
  let T₁ := T ∪ ((fun t : ℝ => (2/3)*t + t₀/3) ⁻¹' T) ∪
    ((fun t : ℝ => 2*t + (-t₀)) ⁻¹' T)
  have hT₁ : T₁.Finite := (hT.union (finite_affine_preimage hT (by norm_num))).union
    (finite_affine_preimage hT (by norm_num))
  obtain ⟨t₁, ht₁, hn₁⟩ := exists_interval_avoiding h₁ hT₁
  have hn₁a : t₁ ∉ T := fun hh => hn₁ (Or.inl (Or.inl hh))
  have hn₁b : (t₀ + 2*t₁)/3 ∉ T := by
    intro hh
    apply hn₁
    left; right
    change (2/3)*t₁ + t₀/3 ∈ T
    convert hh using 1 <;> first | rfl | ring
  have hn₁c : 2*t₁-t₀ ∉ T := by
    intro hh
    apply hn₁
    right
    change 2*t₁ + (-t₀) ∈ T
    simpa only [sub_eq_add_neg] using hh
  let T₂ := T ∪ ((fun t : ℝ => (4/5)*t + t₀/5) ⁻¹' T) ∪
    ((fun t : ℝ => (4/3)*t + (-t₀/3)) ⁻¹' T) ∪
    ((fun t : ℝ => (2/3)*t + t₁/3) ⁻¹' T) ∪
    ((fun t : ℝ => 2*t + (-t₁)) ⁻¹' T)
  have hT₂ : T₂.Finite := (((hT.union (finite_affine_preimage hT (by norm_num))).union
    (finite_affine_preimage hT (by norm_num))).union
    (finite_affine_preimage hT (by norm_num))).union (finite_affine_preimage hT (by norm_num))
  obtain ⟨t₂, ht₂, hn₂⟩ := exists_interval_avoiding h₂ hT₂
  have hn₂a : t₂ ∉ T := fun hh => hn₂ (Or.inl (Or.inl (Or.inl (Or.inl hh))))
  have hn₂b : (t₀ + 4*t₂)/5 ∉ T := by
    intro hh
    apply hn₂
    left; left; left; right
    change (4/5)*t₂ + t₀/5 ∈ T
    convert hh using 1 <;> first | rfl | ring
  have hn₂c : (4*t₂-t₀)/3 ∉ T := by
    intro hh
    apply hn₂
    left; left; right
    change (4/3)*t₂ + (-t₀/3) ∈ T
    convert hh using 1 <;> first | rfl | ring
  have hn₂d : (t₁ + 2*t₂)/3 ∉ T := by
    intro hh
    apply hn₂
    left; right
    change (2/3)*t₂ + t₁/3 ∈ T
    convert hh using 1 <;> first | rfl | ring
  have hn₂e : 2*t₂-t₁ ∉ T := by
    intro hh
    apply hn₂
    right
    change 2*t₂ + (-t₁) ∈ T
    simpa only [sub_eq_add_neg] using hh
  exact ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, hn₀, hn₁a, hn₂a, hn₁b, hn₁c,
    hn₂b, hn₂c, hn₂d, hn₂e⟩




end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding_oai := @OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding_oai
