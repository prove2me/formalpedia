-- Prove2me | solution 1 for HryniewiczCriterion.exists_unit_pole_off_surface_and_loop
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T09:47:31.995982+00:00
-- url     : https://prove2.me/submissions/dbc0997b-8a71-4f87-9967-9c8a28d7a629

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open HryniewiczCriterion
open MeasureTheory Set

/-!
# A unit pole missing a differentiable surface and a loop

Both cones `{c • f v}` and `{c • g s}` are images of a null hyperplane under maps
differentiable on it, hence null; normalize a point off them.
-/


noncomputable section

namespace HryniewiczCriterion

lemma td_hyperplane_null : volume {p : R4 | p 3 = 0} = 0 := by
  let S : Submodule ℝ R4 := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3)
  have hS : (S : Set R4) = {p : R4 | p 3 = 0} := by
    ext p; simp [S]
  rw [← hS]
  refine Measure.addHaar_submodule volume S ?_
  intro htop
  have h : (Pi.single 3 1 : R4) ∈ S := htop ▸ Submodule.mem_top
  simp [S] at h

lemma td_dot4_self_nonneg (u : R4) : 0 ≤ dot4 u u := by
  simp only [dot4, Fin.sum_univ_four]
  nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1), mul_self_nonneg (u 2),
    mul_self_nonneg (u 3)]

lemma td_dot4_self_pos {u : R4} (hu : u ≠ 0) : 0 < dot4 u u := by
  rcases (td_dot4_self_nonneg u).lt_or_eq with h | h
  · exact h
  · exfalso; apply hu
    have h0 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 0 := by
      have := h.symm; simp only [dot4, Fin.sum_univ_four] at this; nlinarith
    funext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2),
      sq_nonneg (u 3)]

lemma td_euclidNorm_pos {u : R4} (hu : u ≠ 0) : 0 < euclidNorm u :=
  Real.sqrt_pos.2 (td_dot4_self_pos hu)

lemma td_euclidNorm_smul (c : ℝ) (v : R4) : euclidNorm (c • v) = |c| * euclidNorm v := by
  have h : dot4 (c • v) (c • v) = c ^ 2 * dot4 v v := by
    simp only [dot4, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]; ring
  rw [euclidNorm, euclidNorm, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The cone `{c • f v : v ∈ U}` over a surface differentiable on `U` is null. -/
lemma td_cone_null (f : Plane → R4) (U : Set Plane) (hf : DifferentiableOn ℝ f U) :
    volume {M : R4 | ∃ (c : ℝ), ∃ v ∈ U, M = c • f v} = 0 := by
  set F : R4 → R4 := fun p => p 2 • f ![p 0, p 1]
  set S : Set R4 := {p : R4 | p 3 = 0 ∧ (![p 0, p 1] : Plane) ∈ U}
  have hsub : {M : R4 | ∃ (c : ℝ), ∃ v ∈ U, M = c • f v} ⊆ F '' S := by
    rintro M ⟨c, v, hv, rfl⟩
    have hv' : (![v 0, v 1] : Plane) = v := by ext i; fin_cases i <;> rfl
    refine ⟨![v 0, v 1, c, 0], ⟨by simp, by simpa using hv'.symm ▸ hv⟩, ?_⟩
    simp [F, hv']
  have hl : Differentiable ℝ (fun p : R4 => (![p 0, p 1] : Plane)) := by
    rw [differentiable_pi]; intro i; fin_cases i <;> simp <;> fun_prop
  have hF : DifferentiableOn ℝ F S := by
    intro p hp
    have h1 : DifferentiableWithinAt ℝ (fun p : R4 => f ![p 0, p 1]) S p :=
      (hf _ hp.2).comp p (hl p).differentiableWithinAt (fun q hq => hq.2)
    exact (differentiableAt_apply 2 p).differentiableWithinAt.smul h1
  have hS : volume S = 0 := measure_mono_null (fun p hp => hp.1) td_hyperplane_null
  exact measure_mono_null hsub (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF hS)

/-- A unit pole missing the unit points of `f(U)` and a loop. -/
theorem td_exists_pole (f : Plane → R4) (U : Set Plane) (hf : DifferentiableOn ℝ f U)
    (g : ℝ → R4) (hg : Differentiable ℝ g) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ v ∈ U, euclidNorm (f v) = 1 → f v ≠ N) ∧
      ∀ s, euclidNorm (g s) = 1 → g s ≠ N := by
  set g' : Plane → R4 := fun v => g (v 0)
  have hg' : DifferentiableOn ℝ g' univ := fun v _ =>
    ((hg (v 0)).comp v (differentiableAt_apply 0 v)).differentiableWithinAt
  set bad := {M : R4 | ∃ (c : ℝ), ∃ v ∈ U, M = c • f v} ∪
    {M : R4 | ∃ (c : ℝ), ∃ v ∈ (univ : Set Plane), M = c • g' v}
  have hU : volume bad = 0 :=
    measure_union_null (td_cone_null f U hf) (td_cone_null g' univ hg')
  have hne : (badᶜ).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hpos := isOpen_univ.measure_pos (volume : Measure R4) univ_nonempty
    rw [← hemp, hU] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨M, hM⟩ := hne
  have hM1 : ∀ (c : ℝ), ∀ v ∈ U, M ≠ c • f v := fun c v hv he => hM (Or.inl ⟨c, v, hv, he⟩)
  have hM2 : ∀ (c : ℝ) s, M ≠ c • g s := fun c s he =>
    hM (Or.inr ⟨c, fun _ => s, mem_univ _, by simpa [g'] using he⟩)
  have hM0 : M ≠ 0 := fun h0 => hM2 0 0 (by simp [h0])
  have hp := td_euclidNorm_pos hM0
  have hMN : M = euclidNorm M • ((euclidNorm M)⁻¹ • M) := by
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  refine ⟨(euclidNorm M)⁻¹ • M, ?_, ?_, ?_⟩
  · rw [td_euclidNorm_smul, abs_inv, abs_of_pos hp, inv_mul_cancel₀ hp.ne']
  · intro v hv _ he
    exact hM1 (euclidNorm M) v hv (he ▸ hMN)
  · intro s _ he
    exact hM2 (euclidNorm M) s (he ▸ hMN)

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (f : Plane → R4) (U : Set Plane) (hf : DifferentiableOn ℝ f U)
    (g : ℝ → R4) (hg : Differentiable ℝ g) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ v ∈ U, euclidNorm (f v) = 1 → f v ≠ N) ∧
      ∀ s, euclidNorm (g s) = 1 → g s ≠ N :=
  HryniewiczCriterion.td_exists_pole f U hf g hg
