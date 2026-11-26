-- Prove2me | solution 1 for Malliavin.memLp_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:21.076969+00:00
-- url     : https://prove2.me/submissions/a0f167cd-8c64-4c0c-94ca-59d515762402

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
import Theorems.Thm_Malliavin_symmetrize_eq_smul_sum

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
theorem _root_.solution {n : ℕ} {f : (Fin n → T) → E} {p : ℝ≥0∞}
    (hf : MemLp f p (Measure.pi fun _ : Fin n => μ)) :
    MemLp (symmetrize n f) p (Measure.pi fun _ : Fin n => μ) := by
  rw [symmetrize_eq_smul_sum]
  exact (memLp_finsetSum' _ fun σ _ =>
    hf.comp_measurePreserving (measurePreserving_comp_perm μ n σ)).const_smul _
end Malliavin
