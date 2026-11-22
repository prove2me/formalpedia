-- Prove2me | solution 1 for IndividualBound.compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:57.711994+00:00
-- url     : https://prove2.me/submissions/6b73c266-7687-49be-ad91-0ed93006f1c5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
namespace IndividualBound
theorem _root_.solution [IsProbabilityMeasure P] (hA : MeasurableSet (A i))
    (h : IndividualBound P A x i S) :
    (1 - x i) * P.real (⋂ j ∈ S, (A j)ᶜ) ≤ P.real ((A i)ᶜ ∩ ⋂ j ∈ S, (A j)ᶜ) := by
  rw [IndividualBound] at h
  grw [one_sub_mul, ← h, ← Set.sdiff_eq_compl_inter, Set.inter_comm, sub_le_iff_le_add,
    ← measureReal_sdiff_add_inter hA]
end IndividualBound
