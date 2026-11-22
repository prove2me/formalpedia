-- Prove2me | solution 1 for IndepFrom.cond_sInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:12.410184+00:00
-- url     : https://prove2.me/submissions/b117bf34-bd80-4579-917d-d086fc63826c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_IndepFrom_cond_biInter

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
variable [IsProbabilityMeasure P]
namespace IndepFrom
theorem _root_.solution (h : IndepFrom s t P) (hs : MeasurableSet s)
    (ht' : t'.Countable) (ht : ∀ i ∈ t', i ∈ t ∨ iᶜ ∈ t) (ht₀ : P (⋂₀ t') ≠ 0) :
    P[s | ⋂₀ t'] = P s := by
  rw [Set.sInter_eq_biInter] at ht₀ ⊢
  exact h.cond_biInter ht' hs ht (by simpa using ht₀)
end IndepFrom
