-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PredictableMarkedCountMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:16:46.796811+00:00
-- url     : https://prove2.me/submissions/3a66da99-c5d9-4ea9-9336-5eaadad4a562

import Mathlib
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isLevyMeasure_iff
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_full_horizon_physical_marked_compensator_equality
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
import Theorems.Thm_Kyprianou_Ch04_exercise46RightContPhysicalMarkedKernelV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (T : NNReal)
    (E : Set (NNReal × Omega)) (hE : MeasurableSet[G.rightCont.predictable] E)
    (hT : ∀ p ∈ E, p.1 ≤ T)
    (B : Set Real) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : Real)) :
    let NX : Omega → Measure (NNReal × Real) := fun w =>
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
        Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    (∫⁻ w, NX w {p | (p.1,w) ∈ E ∧ p.2 ∈ B} ∂P) =
      ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E *
        L.ν B := by
  dsimp only
  obtain ⟨mu, hfin, hclock, hcomp⟩ :=
    avram_twoagentA_original_allnu_full_horizon_physical_marked_compensator_equality L T
  let NX : Omega → Measure (NNReal × Real) := fun w =>
    ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
      Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
      (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
  let K : Omega → @Measure ((NNReal × Omega) × Real)
      (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
        (inferInstance : MeasurableSpace Real)) := fun w =>
    @Measure.map (NNReal × Real) ((NNReal × Omega) × Real) inferInstance
      (@Prod.instMeasurableSpace _ _ G.rightCont.predictable
        (inferInstance : MeasurableSpace Real)) (fun p => ((p.1,w),p.2)) (NX w)
  have hK := Kyprianou.Ch04.exercise46RightContPhysicalMarkedKernelV1 P G L
  letI : MeasurableSpace (NNReal × Omega) := G.rightCont.predictable
  have hR : MeasurableSet (E ×ˢ B) := hE.prod hB
  have hsub : E ×ˢ B ∩ {p : (NNReal × Omega) × Real | p.1.1 ≤ T} =
      E ×ˢ B := inter_eq_left.mpr fun p hp => hT p.1 hp.1
  have he := congrArg (fun m : Measure ((NNReal × Omega) × Real) => m (E ×ˢ B)) hcomp
  change (P.bind K).restrict {p | p.1.1 ≤ T} (E ×ˢ B) =
    (mu.prod (L.ν.restrict (Iio 0))) (E ×ˢ B) at he
  have hlevy : IsLevyMeasure L.ν :=
    IsLevyMeasure.isLevyMeasure_iff.mpr ⟨measure_mono_null
      (by intro x hx; rw [mem_singleton_iff.mp hx]; exact mem_Ici.mpr le_rfl)
      L.ν_Ici, L.ν_integrable⟩
  letI : SigmaFinite L.ν := hlevy.sigmaFinite
  rw [Measure.restrict_apply hR, hsub, Measure.bind_apply hR hK,
    Measure.prod_prod, Measure.restrict_apply hB, inter_eq_left.mpr hNeg,
    hclock E hE] at he
  rw [← he]
  apply lintegral_congr
  intro w
  exact (Measure.map_apply
    ((avram_wave5_02a_joint_original_predictable_mark_lift_measurable G.rightCont).comp
      (measurable_id.prodMk measurable_const)) hR).symm
