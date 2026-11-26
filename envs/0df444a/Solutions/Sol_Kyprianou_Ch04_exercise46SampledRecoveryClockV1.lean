-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46SampledRecoveryClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:43:09.341386+00:00
-- url     : https://prove2.me/submissions/aa978c61-4d14-415e-9a78-dd759afb475c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryGateV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (D : Set NNReal) (hD : D.Countable) :
    IsStoppingTime G.rightCont (fun w =>
      ⨅ r ∈ D, if A w < (r : WithTop NNReal) ∧ (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤) := by
  classical
  apply IsStoppingTime.biInf hD
  intro r hr t
  let E : Set Omega := {w | A w < (r : WithTop NNReal) ∧
    (((A w).untopD 0 : NNReal) : Real) < L.X r w}
  have hE : MeasurableSet[G.rightCont r] E :=
    Kyprianou.Ch04.exercise46RecoveryGateV1 P G L A hA r
  by_cases hrt : r ≤ t
  · have he : {w | (if A w < (r : WithTop NNReal) ∧
          (((A w).untopD 0 : NNReal) : Real) < L.X r w then (r : WithTop NNReal) else ⊤) ≤
          (t : WithTop NNReal)} = E := by
      ext w
      change (if w ∈ E then (r : WithTop NNReal) else ⊤) ≤
        (t : WithTop NNReal) ↔ w ∈ E
      by_cases hw : w ∈ E
      · simp only [if_pos hw, hw, iff_true]
        exact WithTop.coe_le_coe.mpr hrt
      · simp only [if_neg hw, hw, iff_false]
        exact not_le_of_gt (WithTop.coe_lt_top t)
    rw [he]
    exact G.rightCont.mono hrt E hE
  · have he : {w | (if A w < (r : WithTop NNReal) ∧
          (((A w).untopD 0 : NNReal) : Real) < L.X r w then (r : WithTop NNReal) else ⊤) ≤
          (t : WithTop NNReal)} = ∅ := by
      ext w
      change (if w ∈ E then (r : WithTop NNReal) else ⊤) ≤
        (t : WithTop NNReal) ↔ w ∈ (∅ : Set Omega)
      by_cases hw : w ∈ E
      · simp only [if_pos hw, mem_empty_iff_false, iff_false]
        exact fun h => hrt (WithTop.coe_le_coe.mp h)
      · simp only [if_neg hw, mem_empty_iff_false, iff_false]
        exact not_le_of_gt (WithTop.coe_lt_top t)
    rw [he]
    exact @MeasurableSet.empty Omega (G.rightCont t)
