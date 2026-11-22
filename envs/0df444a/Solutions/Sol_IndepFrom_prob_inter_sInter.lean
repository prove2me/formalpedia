-- Prove2me | solution 1 for IndepFrom.prob_inter_sInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:11.917862+00:00
-- url     : https://prove2.me/submissions/104ca60e-b421-4794-a939-d08068a253f1

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_IndepFrom_prob_inter_biInter

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
namespace IndepFrom
theorem _root_.solution (h : IndepFrom s t P) (ht' : t'.Countable)
    (ht : ∀ i ∈ t', i ∈ t ∨ iᶜ ∈ t) : P (s ∩ ⋂₀ t') = P s * P (⋂₀ t') := by
  rw [Set.sInter_eq_biInter]
  exact h.prob_inter_biInter ht' ht
end IndepFrom
