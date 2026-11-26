-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstRestartProductLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:08:47.083796+00:00
-- url     : https://prove2.me/submissions/28366321-73df-46a7-84f4-ee7ed0bc1fc5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46StoppedMarkEventV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteRestartLawUnrestrictV1
import Theorems.Thm_Kyprianou_Ch04_exercise46ExtendedStoppedPathLawV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RestrictedFutureProductLawV1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFin : ∀ᵐ w ∂P, A w ≠ ⊤) :
    let a : Omega → NNReal := fun w => (A w).untopD 0
    let J : Omega → Real := fun w =>
      -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w))
    let Z : Omega → (NNReal → Real) := fun w u => L.X (a w + u) w - L.X (a w) w
    let Y : Omega → (NNReal → Real) := fun w u => L.X u w
    P.map (fun w => (J w, Z w)) = (P.map J).prod (P.map Y) := by
  classical
  dsimp only
  letI : IsProbabilityMeasure P := L.isProbability
  let a : Omega → NNReal := fun w => (A w).untopD 0
  let J : Omega → Real := fun w =>
    -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w))
  let Z : Omega → (NNReal → Real) := fun w u => L.X (a w + u) w - L.X (a w) w
  let Y : Omega → (NNReal → Real) := fun w u => L.X u w
  have hAm : Measurable A := hA.measurable'
  have hJ : Measurable J :=
    ((avram_wave4_04a_actual_levy_jumpmark_joint_measurable L).comp
      (((WithTop.measurable_untopD (0 : NNReal)).comp hAm).prodMk measurable_id)).neg
  have hY : Measurable Y :=
    measurable_pi_lambda _ (fun t => (L.adapted t).mono (G.le t) le_rfl)
  obtain ⟨Lr, hX, _, _, _⟩ := avram_wave5_04_source_rightCont_levy_lift L
  have ha (w : Omega) (hw : A w ≠ ⊤) : A w = (a w : WithTop NNReal) :=
    (WithTop.coe_untop₀_of_ne_top (by simpa using hw)).symm
  have hL := Kyprianou.Ch04.exercise46ExtendedStoppedPathLawV1 P G.rightCont Lr A hA a ha
  rw [hX] at hL
  have hLaw (C : Set Real) (hC : MeasurableSet C) :
      AEMeasurable Z P ∧ (P.restrict (J ⁻¹' C)).map Z = P (J ⁻¹' C) • P.map Y := by
    have he (T : NNReal) : MeasurableSet[G.rightCont T]
        (J ⁻¹' C ∩ {w | A w ≤ (T : WithTop NNReal)}) :=
      Kyprianou.Ch04.exercise46StoppedMarkEventV1 P G L A hA C hC T
    exact Kyprianou.Ch04.exercise46FiniteRestartLawUnrestrictV1 P A hFin Z Y
      hL.1 (J ⁻¹' C) (hL.2 _ he)
  exact Kyprianou.Ch04.exercise46RestrictedFutureProductLawV1 P J Z Y hJ
    (hLaw univ MeasurableSet.univ).1 hY (fun C hC => (hLaw C hC).2)
