-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46SampledRecoveryEqualsFullV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:30:02.3621+00:00
-- url     : https://prove2.me/submissions/2fe0e148-8993-484d-9459-10fad4fead7d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46DenseRightCrossingWitnessV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (D : Set NNReal) (hD : Dense D)
    (f : NNReal → Real) (hR : ∀ t, ContinuousWithinAt f (Ici t) t)
    (a : WithTop NNReal) (H : Real) :
    (⨅ r ∈ D, if a < (r : WithTop NNReal) ∧ H < f r then
      (r : WithTop NNReal) else ⊤) =
      (⨅ r : NNReal, if a < (r : WithTop NNReal) ∧ H < f r then
        (r : WithTop NNReal) else ⊤) := by
  classical
  let R : WithTop NNReal := ⨅ r ∈ D, if a < (r : WithTop NNReal) ∧
    H < f r then (r : WithTop NNReal) else ⊤
  let Q : WithTop NNReal := ⨅ r : NNReal, if a < (r : WithTop NNReal) ∧
    H < f r then (r : WithTop NNReal) else ⊤
  change R = Q
  apply le_antisymm
  · apply le_iInf
    intro s
    by_cases hs : a < (s : WithTop NNReal) ∧ H < f s
    · rw [if_pos hs]
      by_contra hn
      have hlt : (s : WithTop NNReal) < R := lt_of_not_ge hn
      obtain ⟨v, hsv, hvR⟩ := exists_between hlt
      have hv : v ≠ ⊤ := ne_of_lt (hvR.trans_le le_top)
      let t : NNReal := v.untopD 0
      have ht : (t : WithTop NNReal) = v :=
        WithTop.coe_untop₀_of_ne_top (by simpa using hv)
      have hst : s < t := WithTop.coe_lt_coe.mp (ht ▸ hsv)
      obtain ⟨r, hr, hsr, hrt, hfr⟩ :=
        Kyprianou.Ch04.exercise46DenseRightCrossingWitnessV1 D hD f s t hst (hR s) H hs.2
      have hgate : a < (r : WithTop NNReal) ∧ H < f r :=
        ⟨hs.1.trans (WithTop.coe_lt_coe.mpr hsr), hfr⟩
      have hle : R ≤ (r : WithTop NNReal) := by
        dsimp only [R]
        exact iInf_le_of_le r (iInf_le_of_le hr (by rw [if_pos hgate]))
      have hrv : (r : WithTop NNReal) < v := ht ▸ WithTop.coe_lt_coe.mpr hrt
      exact (not_lt_of_ge hle) (hrv.trans hvR)
    · rw [if_neg hs]
      exact le_top
  · exact le_iInf (fun r => le_iInf (fun _ => iInf_le _ r))
