-- Prove2me | solution 1 for NormalizedWeakGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:13:55.001915+00:00
-- url     : https://prove2.me/submissions/368a88b8-deba-4b9e-ab3c-b24aac31a715

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_PHigherOrder_NormalizedWeakGradient
import Theorems.Thm_AffineTestFunctionPullback
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane)
    (x₀ : Plane) (r M c : ℝ) (hr : 0 < r) (h : IsPHarm p Ω u g) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ {x : Plane | x₀ + r • x ∈ Ω} →
      ∫ x in {x : Plane | x₀ + r • x ∈ Ω}, ((u (x₀ + r • x) - c) / M) • gradient φ x
        = - ∫ x in {x : Plane | x₀ + r • x ∈ Ω}, φ x • ((r / M) • g (x₀ + r • x)) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  -- `T x = x₀ + r • x` and its inverse, and vanishing off the topological support.
  have hST : ∀ x : Plane, r⁻¹ • ((x₀ + r • x) - x₀) = x := by
    intro x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hrne, one_smul]
  obtain ⟨hval0, hgrad0⟩ := VanishingOffTsupport
  -- The whole-space affine change of variables, with its dilation Jacobian.
  have hcovP : ∀ F : Plane → Plane, ∫ x : Plane, F (x₀ + r • x)
      = |((r ^ (Module.finrank ℝ Plane))⁻¹)| • ∫ y : Plane, F y := by
    intro F
    rw [MeasureTheory.Measure.integral_comp_smul MeasureTheory.volume
      (fun y => F (x₀ + y)) r, MeasureTheory.integral_add_left_eq_self F x₀]
  -- The test-function correspondence under the affine substitution, and the chain rule.
  have hpsi := AffineTestFunctionPullback x₀ r hr Ω
  intro φ hφ hφc hφsub
  obtain ⟨hψC, hψcs, hψsub, hψgrad⟩ := hpsi φ hφ hφc hφsub
  set ψ : Plane → ℝ := fun y : Plane => φ (r⁻¹ • (y - x₀)) with hψdef
  have hψT : ∀ x : Plane, ψ (x₀ + r • x) = φ x := by
    intro x
    simp only [hψdef]
    rw [hST x]
  have hψC1 : ContDiff ℝ 1 ψ := hψC.of_le (by simp)
  have hDψcont : Continuous fun y : Plane => gradient ψ y :=
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous).comp
      (hψC1.continuous_fderiv one_ne_zero)
  have hDψcs : HasCompactSupport fun y : Plane => gradient ψ y :=
    (hψcs.fderiv ℝ).comp_left
      (g := fun L : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm L) (by simp)
  have hBint : MeasureTheory.Integrable fun y : Plane => gradient ψ y :=
    hDψcont.integrable_of_hasCompactSupport hDψcs
  have hBzero : ∫ y : Plane, gradient ψ y = 0 :=
    TestFunctionGradientIntegral ψ hψC1 hψcs
  have hAint : MeasureTheory.Integrable fun y : Plane => u y • gradient ψ y := by
    have hsupp : Function.support (fun y : Plane => u y • gradient ψ y) ⊆ tsupport ψ := by
      intro y hy
      by_contra hc
      exact hy (by simp [hgrad0 ψ y hc])
    rw [← Set.indicator_eq_self.mpr hsupp,
      MeasureTheory.integrable_indicator_iff hψcs.measurableSet]
    exact ContinuousOn.integrableOn_compact hψcs
      ((h.contU.mono hψsub).smul hDψcont.continuousOn)
  have hL1 : ∫ x in {x : Plane | x₀ + r • x ∈ Ω},
        ((u (x₀ + r • x) - c) / M) • gradient φ x
      = ∫ x : Plane, ((u (x₀ + r • x) - c) / M) • gradient φ x := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [hgrad0 φ x fun hcc => hx (hφsub hcc), smul_zero]
  have hR1 : ∫ x in {x : Plane | x₀ + r • x ∈ Ω}, φ x • ((r / M) • g (x₀ + r • x))
      = ∫ x : Plane, φ x • ((r / M) • g (x₀ + r • x)) := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    rw [hval0 φ x fun hcc => hx (hφsub hcc), zero_smul]
  have hA2 : ∫ y in Ω, u y • gradient ψ y = ∫ y : Plane, u y • gradient ψ y := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [hgrad0 ψ y fun hcc => hy (hψsub hcc), smul_zero]
  have hC2 : ∫ y in Ω, ψ y • g y = ∫ y : Plane, ψ y • g y := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [hval0 ψ y fun hcc => hy (hψsub hcc), zero_smul]
  have hkey : ∫ y : Plane, u y • gradient ψ y = - ∫ y : Plane, ψ y • g y := by
    rw [← hA2, ← hC2]
    exact h.weakGrad ψ hψC hψcs hψsub
  have hsplit : ∫ y : Plane, (u y • gradient ψ y - c • gradient ψ y)
      = ∫ y : Plane, u y • gradient ψ y := by
    have hBcint : MeasureTheory.Integrable fun y : Plane => c • gradient ψ y :=
      MeasureTheory.Integrable.smul c hBint
    rw [MeasureTheory.integral_sub hAint hBcint,
      MeasureTheory.integral_smul, hBzero, smul_zero, sub_zero]
  have hF1 : ∀ x : Plane, ((u (x₀ + r • x) - c) / M) • gradient φ x
      = (r / M) • (u (x₀ + r • x) • gradient ψ (x₀ + r • x)
          - c • gradient ψ (x₀ + r • x)) := by
    intro x
    rw [hψgrad x]
    module
  have hF2 : ∀ x : Plane, φ x • ((r / M) • g (x₀ + r • x))
      = (r / M) • (ψ (x₀ + r • x) • g (x₀ + r • x)) := by
    intro x
    rw [← hψT x]
    module
  rw [hL1, hR1]
  calc ∫ x : Plane, ((u (x₀ + r • x) - c) / M) • gradient φ x
      = ∫ x : Plane, (r / M) • (u (x₀ + r • x) • gradient ψ (x₀ + r • x)
          - c • gradient ψ (x₀ + r • x)) := by simp only [hF1]
    _ = (r / M) • ∫ x : Plane, (u (x₀ + r • x) • gradient ψ (x₀ + r • x)
          - c • gradient ψ (x₀ + r • x)) := MeasureTheory.integral_smul _ _
    _ = (r / M) • (|((r ^ (Module.finrank ℝ Plane))⁻¹)|
          • ∫ y : Plane, (u y • gradient ψ y - c • gradient ψ y)) := by
          rw [hcovP (fun y => u y • gradient ψ y - c • gradient ψ y)]
    _ = (r / M) • (|((r ^ (Module.finrank ℝ Plane))⁻¹)|
          • ∫ y : Plane, u y • gradient ψ y) := by rw [hsplit]
    _ = - ((r / M) • (|((r ^ (Module.finrank ℝ Plane))⁻¹)|
          • ∫ y : Plane, ψ y • g y)) := by rw [hkey]; simp
    _ = - ((r / M) • ∫ x : Plane, ψ (x₀ + r • x) • g (x₀ + r • x)) := by
          rw [hcovP (fun y => ψ y • g y)]
    _ = - ∫ x : Plane, (r / M) • (ψ (x₀ + r • x) • g (x₀ + r • x)) := by
          rw [MeasureTheory.integral_smul]
    _ = - ∫ x : Plane, φ x • ((r / M) • g (x₀ + r • x)) := by simp only [hF2]
