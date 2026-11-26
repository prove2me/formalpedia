-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49GeneralExtendedRestrictedPathV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:39:35.675813+00:00
-- url     : https://prove2.me/submissions/b7324d3a-79fe-42bf-9f14-62b6f58e0de7

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedUpperGridV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridRestrictedLawV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovPathLawOfCommonAELimitsV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hDet : ∀ (s : NNReal) (B : Set Ω), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ)
    (a : Ω → NNReal) (ha : ∀ w, τ w ≠ ⊤ → τ w = (a w : WithTop NNReal)) :
    AEMeasurable (fun w u => X (a w + u) w - X (a w) w) (P.restrict {w | τ w ≠ ⊤}) ∧
    ∀ B : Set Ω, (∀ s : NNReal, MeasurableSet[F s] (B ∩ {w | τ w ≤ (s : WithTop NNReal)})) →
      Measure.map (fun w u => X (a w + u) w - X (a w) w)
        (P.restrict (B ∩ {w | τ w ≠ ⊤})) =
      P (B ∩ {w | τ w ≠ ⊤}) • Measure.map (fun w u => X u w) P := by
  classical
  obtain ⟨T,hCount,hFib,hZero,hT⟩ :=
    Kyprianou.Ch03.strongMarkovExtendedUpperGridV1 F τ hτ a ha
  let D : Set Ω := {w | τ w ≠ ⊤}
  let Y : ℕ → Ω → NNReal → ℝ := fun n w u => X (T n w+u) w-X (T n w) w
  let Z : Ω → NNReal → ℝ := fun w u => X (a w+u) w-X (a w) w
  let ν := Measure.map (fun w u => X u w) P
  have hGrid := fun n => Kyprianou.Ch03.strongMarkovCountableGridRestrictedLawV1 F τ hτ a ha
    P X hm hDet (T n) (hCount n) (hFib n) (hZero n) (fun w hw => (hT w hw).1 n)
  have hConv : ∀ B : Set Ω, MeasurableSet (B ∩ D) →
      ∀ᵐ w ∂P.restrict (B ∩ D), ∀ u : NNReal,
        Tendsto (fun n => Y n w u) atTop (nhds (Z w u)) := by
    intro B hB
    filter_upwards [ae_restrict_mem hB] with w hw u
    obtain ⟨hAbove,hlim⟩ := hT w hw.2
    have h1 : Tendsto (fun n => T n w) atTop (nhdsWithin (a w) (Ici (a w))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall hAbove⟩
    have h2 : Tendsto (fun n => T n w+u) atTop (nhdsWithin (a w+u) (Ici (a w+u))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim.add tendsto_const_nhds,
        Eventually.of_forall fun n => add_le_add_left (hAbove n) u⟩
    exact ((hr w (a w+u)).tendsto.comp h2).sub ((hr w (a w)).tendsto.comp h1)
  have hAll : ∀ B : Set Ω, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w | τ w ≤ (s : WithTop NNReal)})) →
      AEMeasurable Z (P.restrict (B ∩ D)) ∧
      Measure.map Z (P.restrict (B ∩ D)) = P (B ∩ D) • ν := by
    intro B hB
    exact Kyprianou.Ch03.strongMarkovPathLawOfCommonAELimitsV1 (P.restrict (B ∩ D)) Y Z
      (P (B ∩ D) • ν) (fun n => (hGrid n).1)
      (fun n => (hGrid n).2 B hB)
      (hConv B (Kyprianou.Ch03.strongMarkovFiniteStoppedEventMeasV1 F τ hτ B hB))
  refine ⟨?_,fun B hB => (hAll B hB).2⟩
  simpa [D,Z] using (hAll Set.univ (fun s => by simpa using hτ s)).1
