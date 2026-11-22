-- Prove2me | solution 1 for IndepFrom.prob_inter_biInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:37:19.766882+00:00
-- url     : https://prove2.me/submissions/640fb778-9d83-43c7-bae7-97c471849bfc

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
namespace IndepFrom
theorem _root_.solution (h : IndepFrom s t P) {C : Set ι} {A : ι → Set Ω}
    (hC : C.Countable) (ht : ∀ i ∈ C, A i ∈ t ∨ (A i)ᶜ ∈ t) :
    P (s ∩ ⋂ i ∈ C, A i) = P s * P (⋂ i ∈ C, A i) := by
  have : Countable C := by simpa
  simpa using h.prob_inter_iInter (ι := C) (A := A ∘ Subtype.val) (by simpa)
end IndepFrom
