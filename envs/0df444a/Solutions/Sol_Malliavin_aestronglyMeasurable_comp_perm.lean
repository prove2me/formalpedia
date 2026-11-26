-- Prove2me | solution 1 for Malliavin.aestronglyMeasurable_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:32.224432+00:00
-- url     : https://prove2.me/submissions/be8f26c0-ec5e-4d1b-a588-1676860f85db

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}
omit [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin n => μ)) (σ : Equiv.Perm (Fin n)) :
    AEStronglyMeasurable (f ∘ fun t : Fin n → T => t ∘ σ) (Measure.pi fun _ : Fin n => μ) :=
  hf.comp_quasiMeasurePreserving (measurePreserving_comp_perm μ n σ).quasiMeasurePreserving
end Malliavin
