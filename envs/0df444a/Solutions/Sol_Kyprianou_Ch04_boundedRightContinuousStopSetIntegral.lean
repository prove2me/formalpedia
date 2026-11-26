-- Prove2me | solution 1 for Kyprianou.Ch04.boundedRightContinuousStopSetIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:53:57.907116+00:00
-- url     : https://prove2.me/submissions/2503b2df-c4d7-443e-8c7a-10743568f7a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_finite_range_stopped_mart_terminal_condexp
import Theorems.Thm_AvramDividend_Classical_avram_ja18_rightcontinuous_clock_composition
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_UI_condexp_family_original_clock_L1_limit
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Bounded optional sampling in set-integral form for a right-continuous martingale. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (J : NNReal → Omega → ℝ) (hM : Martingale J F.rightCont P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => J u w) (Set.Ici t) t)
    (n : ℕ) (tau : Omega → NNReal)
    (ht : IsStoppingTime F.rightCont (fun w => (tau w : WithTop NNReal)))
    (hb : ∀ w, tau w ≤ (n : NNReal)) :
    Integrable (fun w => J (tau w) w) P ∧
      ∀ A : Set Omega, MeasurableSet[ht.measurableSpace] A →
        (∫ w in A, J (tau w) w ∂P) = ∫ w in A, J (n : NNReal) w ∂P := by
  obtain ⟨rho, hStop, hRange, hAbove, hBelow, hConv⟩ :=
    avram_ja18_original_rightcont_upper_grid_stops tau ht n hb
  let V : ℕ → Omega → ℝ := fun k w => J (rho k w) w
  have hCE (k : ℕ) :
      V k =ᵐ[P] condExp (hStop k).measurableSpace P (J (n : NNReal)) := by
    obtain ⟨S,hS⟩ := hRange k
    exact avram_jump6_A_finite_range_stopped_mart_terminal_condexp J
      (fun t => (hM.stronglyAdapted t).measurable) hM.integrable
      (fun s t hst => hM.2 s t hst) n (rho k) (hStop k) (hBelow k) S hS
  have hConvV := avram_ja18_rightcontinuous_clock_composition J tau rho hr hAbove hConv
  obtain ⟨hi,hL1⟩ := avram_jump6_A_UI_condexp_family_original_clock_L1_limit
    (J (n : NNReal)) (hM.integrable _) V (fun k => (hStop k).measurableSpace)
    (fun k => (hStop k).measurableSpace_le) hCE (fun w => J (tau w) w) hConvV
  refine ⟨hi,?_⟩
  intro A hA
  have hI (k : ℕ) : Integrable (V k) P := integrable_condExp.congr (hCE k).symm
  have hE (k : ℕ) : (∫ w in A, V k w ∂P) = ∫ w in A, J (n : NNReal) w ∂P := by
    have hAk := ht.measurableSpace_mono (hStop k)
      (fun w => WithTop.coe_le_coe.mpr (hAbove k w)) A hA
    exact (integral_congr_ae (ae_restrict_of_ae (hCE k))).trans
      (setIntegral_condExp (hStop k).measurableSpace_le (hM.integrable _) hAk)
  have hL := tendsto_setIntegral_of_L1' _ hi.aestronglyMeasurable
    (Eventually.of_forall hI) hL1 A
  exact tendsto_nhds_unique hL (tendsto_const_nhds.congr' (Eventually.of_forall fun k => (hE k).symm))
