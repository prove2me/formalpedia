-- Prove2me | solution 1 for Newton.eLpNorm_toReal_pos_of_ae_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:13.585594+00:00
-- url     : https://prove2.me/submissions/f04d49c4-7d48-4508-b649-55302685f27a

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder

set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
namespace Newton
theorem _root_.solution
    (p : ℝ≥0∞) (hp : 1 < p) (f : α → ℝ) (hf : MemLp f p μ)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hμ_pos : μ Set.univ ≠ 0) :
    0 < (eLpNorm f p μ).toReal := by
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt <| (zero_lt_one.trans hp)
  have h_nonneg : 0 ≤ (eLpNorm f p μ).toReal := ENNReal.toReal_nonneg
  have h_ne : (eLpNorm f p μ).toReal ≠ 0 := by
    intro hzero
    have hnorm_ne_top : eLpNorm f p μ ≠ ∞ := ne_of_lt hf.2
    have hzero_cases := (ENNReal.toReal_eq_zero_iff (eLpNorm f p μ)).mp hzero
    have hnorm_zero : eLpNorm f p μ = 0 := by
      rcases hzero_cases with hzero' | htop
      · exact hzero'
      · exact (hnorm_ne_top htop).elim
    have hf_zero : f =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff (μ := μ) (f := f) (p := p) hf.1 hp_ne_zero).1 hnorm_zero
    have hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0 :=
      hf_pos.mono fun x hx => ne_of_gt hx
    have hf_false : (∀ᵐ x ∂μ, False) :=
      (hf_ne_zero.and hf_zero).mono fun x hx => (hx.1 hx.2)
    have hf_false' : μ Set.univ = 0 := by
      have : μ {x | ¬False} = 0 := ae_iff.mp hf_false
      simp only [not_false_eq_true, Set.setOf_true] at this
      exact this
    exact (hμ_pos hf_false')
  exact lt_of_le_of_ne h_nonneg (by simpa [eq_comm] using h_ne)
end Newton
