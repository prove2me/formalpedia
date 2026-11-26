-- Prove2me | solution 1 for Malliavin.symmetrize_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:37.15073+00:00
-- url     : https://prove2.me/submissions/8c077ffa-2ed6-438d-ba3a-34a8bc7f8c71

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}
namespace Malliavin
theorem _root_.solution {n : ℕ} {f g : (Fin n → T) → E}
    (h : f =ᵐ[Measure.pi fun _ : Fin n => μ] g) :
    symmetrize n f =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n g := by
  have hσ : ∀ σ : Equiv.Perm (Fin n),
      (f ∘ fun t : Fin n → T => t ∘ σ) =ᵐ[Measure.pi fun _ : Fin n => μ]
        (g ∘ fun t : Fin n → T => t ∘ σ) :=
    fun σ => (measurePreserving_comp_perm μ n σ).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [Filter.eventually_all.2 hσ] with t ht
  simp only [symmetrize_apply]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => ht σ
end Malliavin
