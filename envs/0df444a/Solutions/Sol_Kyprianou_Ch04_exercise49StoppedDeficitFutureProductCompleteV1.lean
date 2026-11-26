-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49StoppedDeficitFutureProductCompleteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:35:45.526411+00:00
-- url     : https://prove2.me/submissions/d5ac7760-6cf1-4165-89a6-21b9c0b11670

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalFiltrationExistsV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
import Theorems.Thm_Kyprianou_Ch03_completedNaturalStoppedAdaptedEventsV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Strong Markov at strict first passage on the completed probability space. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (τ : Ω → WithTop NNReal)
    (hτ : ∀ w, τ w = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0})
    (hτm : Measurable τ) (f : Ω → NNReal) (hf : Measurable f)
    (he : ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal)) :
    let D : Set Ω := {w | τ w ≠ ⊤}
    let I : Ω → ℝ := fun w => -X (f w) w
    let Y : Ω → (NNReal → ℝ) := fun w u => X (f w + u) w - X (f w) w
    Measure.map (fun w => (I w, Y w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map (fun w u => X u w) P) := by
  classical
  obtain ⟨F, hF⟩ := Kyprianou.Ch03.completedNaturalFiltrationExistsV1 P X hm
  have hAdapt := Kyprianou.Ch03.completedNaturalCoordinateAdaptedV1 P X F hF
  have hRC := Kyprianou.Ch03.completedNaturalLevyFiltrationRightContinuous P X hX F hF
  have hNull (s : NNReal) (N A : Set Ω) (hN : MeasurableSet N)
      (hN0 : P N = 0) (hAN : A ⊆ N) : MeasurableSet[F s] A := by
    rw [hF s]
    let M : MeasurableSpace Ω := MeasurableSpace.generateFrom {B : Set Ω |
      ∃ C : Set Ω, MeasurableSet C ∧ P C = 0 ∧ B ⊆ C}
    have hA : MeasurableSet[M] A :=
      MeasurableSpace.measurableSet_generateFrom ⟨N, hN, hN0, hAN⟩
    exact (le_sup_right : M ≤ PerfCorrMSQ.natFiltr X s ⊔ M) A hA
  have hPath : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun u => X u w) (Ici t) t :=
    Eventually.of_forall fun w t => (hc w t).1
  have hStop : IsStoppingTime F τ := by
    have hEq : τ = fun w => sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ X t w ∈ Iio 0} := by
      funext w
      rw [hτ w]
      congr 1
      ext v
      constructor
      · rintro ⟨t, rfl, _, ht⟩
        exact ⟨t, rfl, ht⟩
      · rintro ⟨t, rfl, ht⟩
        refine ⟨t, rfl, ?_, ht⟩
        by_contra! h
        have ht0 : t = 0 := le_antisymm h bot_le
        simpa [ht0, congrFun hX.start_zero w] using ht
    rw [hEq]
    exact Kyprianou.Ch04.openHitStoppingTimeOfAE P F hRC hNull X hAdapt hPath
      (Iio 0) isOpen_Iio
  let D : Set Ω := {w | τ w ≠ ⊤}
  let I : Ω → ℝ := fun w => -X (f w) w
  let Y : Ω → (NNReal → ℝ) := fun w u => X (f w + u) w - X (f w) w
  let V : Ω → (NNReal → ℝ) := fun w u => X u w
  have hJoint := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    X hm (fun w t => (hc w t).1)
  have hI : Measurable I := (hJoint.comp (hf.prodMk measurable_id)).neg
  have hY : Measurable Y := measurable_pi_iff.mpr fun u =>
    (hJoint.comp ((hf.add measurable_const).prodMk measurable_id)).sub
      (hJoint.comp (hf.prodMk measurable_id))
  have hS := Kyprianou.Ch03.completedNaturalStoppedAdaptedEventsV1 P X F hF
    (fun t w => -X t w) (fun t => (hAdapt t).neg)
    (hPath.mono fun w hw t => (hw t).neg) τ hStop f he univ
    (fun s => by simpa using hStop s)
  have hLaw := (Kyprianou.Ch03.strongMarkovExtendedRestrictedPathV1 P F X hX hF
    (Kyprianou.Ch03.strongMarkovDeterministicRestrictedPathV1 P F X hX hF)
    τ hStop f he).2
  change Measure.map (fun w => (I w, Y w)) (P.restrict D) =
    (Measure.map I (P.restrict D)).prod (Measure.map V P)
  symm
  apply Measure.prod_eq
  intro B C hB hC
  have hcut (s : NNReal) : MeasurableSet[F s]
      (I ⁻¹' B ∩ {w | τ w ≤ (s : WithTop NNReal)}) := by
    change MeasurableSet[F s] ({w | -X (f w) w ∈ B} ∩ {w | τ w ≤ (s : WithTop NNReal)})
    have hh := hS.2 B hB s
    rw [univ_inter] at hh
    exact hh
  have hL := hLaw (I ⁻¹' B) hcut
  change Measure.map Y (P.restrict (I ⁻¹' B ∩ D)) =
    P (I ⁻¹' B ∩ D) • Measure.map V P at hL
  rw [Measure.map_apply (hI.prodMk hY) (hB.prod hC)]
  change P.restrict D (I ⁻¹' B ∩ Y ⁻¹' C) = _
  rw [Measure.map_apply hI hB, Measure.restrict_apply (hI hB)]
  rw [← Measure.restrict_restrict (hI hB)] at hL
  have hval := congrArg (fun m : Measure (NNReal → ℝ) => m C) hL
  rw [Measure.map_apply hY hC, Measure.smul_apply, smul_eq_mul] at hval
  rw [Measure.restrict_apply (hY hC), inter_comm] at hval
  exact hval
