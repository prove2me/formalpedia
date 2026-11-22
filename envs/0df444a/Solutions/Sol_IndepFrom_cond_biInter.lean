-- Prove2me | solution 1 for IndepFrom.cond_biInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:48.95627+00:00
-- url     : https://prove2.me/submissions/b736de3d-e9a9-485d-aa7d-300b953d1694

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_IndepFrom_cond_iInter

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
variable [IsProbabilityMeasure P]
namespace IndepFrom
theorem _root_.solution (h : IndepFrom s t P) {C : Set ι}
    {A : ι → Set Ω} (hC : C.Countable) (hs : MeasurableSet s) (ht : ∀ i ∈ C, A i ∈ t ∨ (A i)ᶜ ∈ t)
    (ht₀ : P (⋂ i ∈ C, A i) ≠ 0) :
    P[s | ⋂ i ∈ C, A i] = P s := by
  have : Countable C := by simpa
  simpa using h.cond_iInter (ι := C) (A := A ∘ Subtype.val) hs (by simpa) (by simpa)
end IndepFrom
