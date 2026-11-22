-- Prove2me | solution 1 for IndepFrom.prob_inter_iInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:42.252203+00:00
-- url     : https://prove2.me/submissions/66abc38e-b075-4254-a941-95cbd1031986

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
namespace IndepFrom
theorem _root_.solution [Countable ι] (h : IndepFrom s t P) {A : ι → Set Ω}
    (ht : ∀ i, A i ∈ t ∨ (A i)ᶜ ∈ t) : P (s ∩ ⋂ i, A i) = P s * P (⋂ i, A i) := by
  rw [IndepFrom, Indep_iff] at h
  rw [h]
  · exact .basic _ (by simp)
  apply MeasurableSet.iInter
  intro i
  obtain h | h := ht i
  · exact .basic _ h
  · exact .of_compl (.basic _ h)
end IndepFrom
