-- Prove2me | solution 1 for Kyprianou.Ch03.rawRightGermPastFutureLatticeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:32:51.934806+00:00
-- url     : https://prove2.me/submissions/e5d4752e-af61-4da8-96de-47589072812d

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Raw filtration inclusions using the full future increment path. -/
theorem solution {Omega : Type} (X : NNReal → Omega → Real) (t : NNReal) :
    PerfCorrMSQ.natFiltr X t ≤ (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ∧
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X (t + u) ω - X t ω) inferInstance ∧
    PerfCorrMSQ.natFiltr X t ⊔
        MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X (t + u) ω - X t ω) inferInstance ≤
      MeasurableSpace.comap (fun ω : Omega => fun u : NNReal => X u ω) inferInstance := by
  simp only [MeasurableSpace.comap_process_pi]
  let C (r : NNReal) := MeasurableSpace.comap (X r) inferInstance
  let D (u : NNReal) := MeasurableSpace.comap (fun ω => X (t + u) ω - X t ω) inferInstance
  let m := PerfCorrMSQ.natFiltr X t
  let j := m ⊔ iSup D
  let f := iSup C
  change m ≤ (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ∧
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤ j ∧ j ≤ f
  have hm (r : NNReal) (hr : r ≤ t) : C r ≤ m :=
    le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hX (r : NNReal) : @Measurable Omega Real f inferInstance (X r) :=
    measurable_iff_comap_le.mpr (le_iSup C r)
  refine ⟨le_iInf fun s => le_iInf fun hs => ?_, ?_, ?_⟩
  · exact iSup_le fun r => iSup_le fun hr =>
      le_iSup_of_le r (le_iSup_of_le (hr.trans hs.le) le_rfl)
  · refine (iInf_le_of_le (t + 1) (iInf_le _ (lt_add_of_pos_right _ zero_lt_one))).trans ?_
    refine iSup_le fun r => iSup_le fun _ => ?_
    by_cases hr : r ≤ t
    · exact (hm r hr).trans le_sup_left
    · have ha : @Measurable Omega Real j inferInstance
          (fun ω => X (t + (r - t)) ω - X t ω) :=
        measurable_iff_comap_le.mpr ((le_iSup D (r - t)).trans le_sup_right)
      have hb : @Measurable Omega Real j inferInstance (X t) :=
        measurable_iff_comap_le.mpr ((hm t le_rfl).trans le_sup_left)
      have heq : ((fun ω => X (t + (r - t)) ω - X t ω) + X t) = X r := by
        funext ω
        simp only [Pi.add_apply, add_tsub_cancel_of_le (le_of_not_ge hr), sub_add_cancel]
      simpa only [heq] using (ha.add hb).comap_le
  · exact sup_le (iSup_le fun r => iSup_le fun _ => le_iSup C r)
      (iSup_le fun u => ((hX (t + u)).sub (hX t)).comap_le)
