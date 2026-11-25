-- Prove2me | solution 1 for Newton.lp_duality_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:35:09.631324+00:00
-- url     : https://prove2.me/submissions/7d346ca2-c820-420e-af1b-3d1de018f484

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_holder_inequality


set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞) (_hp : 1 < p) (_hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f g : α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  have h_holder :=
    holder_inequality (μ := μ) (p := p) (q := q) hpq (f := f) (g := g) hf hg
  have h_abs_bound : ∫ x, |f x * g x| ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
    simpa [Real.norm_eq_abs, abs_mul] using h_holder.2
  exact (abs_integral_le_integral_abs (μ := μ) (f := fun x => f x * g x)).trans h_abs_bound
end Newton
