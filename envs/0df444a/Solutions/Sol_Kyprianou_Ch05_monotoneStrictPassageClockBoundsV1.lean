-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneStrictPassageClockBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:49:53.611913+00:00
-- url     : https://prove2.me/submissions/feff7159-54cc-426b-8bb0-05351c60e42a

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
theorem solution
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (t : NNReal) :
    ((T < (t : ENNReal)) → x < f t) ∧
    (0 < t → x < f t → T ≤ (t : ENNReal)) := by
  constructor
  · intro ht
    rw [hT] at ht
    obtain ⟨a,ha,hat⟩ := sInf_lt_iff.mp ht
    obtain ⟨u,hu,rfl⟩ := ha
    exact hu.2.trans_le (hm (ENNReal.coe_lt_coe.mp hat).le)
  · intro ht hf
    rw [hT]
    exact sInf_le ⟨t,⟨ht,hf⟩,rfl⟩
