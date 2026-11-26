-- Prove2me | solution 1 for Malliavin.inner_permL_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:01.289253+00:00
-- url     : https://prove2.me/submissions/936379b7-0acd-455e-b19f-740abbe6a072

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_coeFn_permL
attribute [local simp] Malliavin.mem_symmetricSubmodule

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace Malliavin
theorem _root_.solution (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    inner ℝ (permL E (μ := μ) n 2 σ f) g = inner ℝ f (permL E (μ := μ) n 2 σ⁻¹ g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hemb : MeasurableEmbedding (fun t : Fin n → T => t ∘ ⇑(σ⁻¹)) :=
    (MeasurableEquiv.arrowCongr' (σ⁻¹).symm (MeasurableEquiv.refl T)).measurableEmbedding
  have hcov := (measurePreserving_comp_perm μ n σ⁻¹).integral_comp hemb
    (fun t : Fin n → T => inner ℝ (f (t ∘ σ)) (g t))
  calc ∫ t, inner ℝ ((permL E (μ := μ) n 2 σ f) t) (g t) ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t, inner ℝ (f (t ∘ σ)) (g t) ∂(Measure.pi fun _ : Fin n => μ) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_permL (E := E) (μ := μ) n 2 σ f] with t ht
        rw [ht]
        rfl
    _ = ∫ u, inner ℝ (f ((u ∘ ⇑(σ⁻¹)) ∘ σ)) (g (u ∘ ⇑(σ⁻¹)))
          ∂(Measure.pi fun _ : Fin n => μ) := hcov.symm
    _ = ∫ u, inner ℝ (f u) ((permL E (μ := μ) n 2 σ⁻¹ g) u) ∂(Measure.pi fun _ : Fin n => μ) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_permL (E := E) (μ := μ) n 2 σ⁻¹ g] with u hu
        have hu' : (u ∘ ⇑(σ⁻¹)) ∘ ⇑σ = u := by
          ext i
          simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
        rw [hu, hu']
        rfl
end Malliavin
