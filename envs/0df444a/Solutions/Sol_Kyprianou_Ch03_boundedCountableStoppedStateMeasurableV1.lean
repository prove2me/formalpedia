-- Prove2me | solution 1 for Kyprianou.Ch03.boundedCountableStoppedStateMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:17:51.148831+00:00
-- url     : https://prove2.me/submissions/d9987065-fd97-4fd9-b59e-a157de27a94b

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableFibreMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (Z : NNReal → Omega → ℝ) (hAdapt : Adapted F Z)
    (g : Omega → NNReal)
    (hg : IsStoppingTime F (fun w => (g w : WithTop NNReal)))
    (hc : (Set.range (fun w => (g w : WithTop NNReal))).Countable)
    (s : NNReal) (hb : ∀ w, g w ≤ s) :
    Measurable[F s] (fun w => Z (g w) w) := by
  classical
  have hcnt : (Set.range g).Countable := by
    apply (hc.image (fun v : WithTop NNReal => v.untopD 0)).mono
    rintro _ ⟨w,rfl⟩
    exact ⟨(g w : WithTop NNReal),⟨w,rfl⟩,rfl⟩
  have hFib (u : NNReal) : MeasurableSet[F s] {w | g w = u} := by
    by_cases hu : u ≤ s
    · have he : {w : Omega | g w = u} =
          {w : Omega | (g w : WithTop NNReal) = (u : WithTop NNReal)} := by
        ext w
        simp only [Set.mem_setOf_eq, WithTop.coe_inj]
      rw [he]
      exact F.mono hu _ (hg.measurableSet_eq_of_countable_range hc u)
    · have he : {w | g w = u} = ∅ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hu (h ▸ hb w)
      rw [he]
      exact @MeasurableSet.empty Omega (F s)
  have hZ (u : NNReal) : Measurable[F s] (fun w => if u ≤ s then Z u w else 0) := by
    by_cases hu : u ≤ s
    · simpa [hu] using (hAdapt u).mono (F.mono hu) le_rfl
    · simpa only [if_neg hu] using (@measurable_const ℝ Omega inferInstance (F s) 0)
  simpa only [hb,if_true] using
    (@strongMarkovCountableFibreMeasurableV1 Omega NNReal ℝ (F s)
      inferInstance g hcnt hFib _ hZ)
