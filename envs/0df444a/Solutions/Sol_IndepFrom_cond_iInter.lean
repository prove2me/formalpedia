-- Prove2me | solution 1 for IndepFrom.cond_iInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:51.638173+00:00
-- url     : https://prove2.me/submissions/0683cb7b-833e-4ddf-91e8-b6fbbe63dea3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_IndepFrom_prob_inter_iInter

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
variable [IsProbabilityMeasure P]
namespace IndepFrom
theorem _root_.solution [Countable ι] (h : IndepFrom s t P)
    {A : ι → Set Ω} (hs : MeasurableSet s) (ht : ∀ i, A i ∈ t ∨ (A i)ᶜ ∈ t)
    (ht₀ : P (⋂ i, A i) ≠ 0) :
    P[s | ⋂ i, A i] = P s := by
  rw [cond_apply' hs, Set.inter_comm, h.prob_inter_iInter ht, mul_left_comm,
    ENNReal.inv_mul_cancel ht₀ (by simp), mul_one]
end IndepFrom
