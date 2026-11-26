-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RightContRestrictedLawV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:39:35.881447+00:00
-- url     : https://prove2.me/submissions/3fc9f71a-f006-4d66-9b45-bb0bb51cf6c5

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_strongMarkovPathLawOfCommonAELimitsV1
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
    (s : NNReal) (B : Set Ω) (hB : MeasurableSet[F.rightCont s] B) :
    Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
      P B • Measure.map (fun w u => X u w) P := by
  have hfreq : ∃ᶠ r : NNReal in nhdsWithin s (Ioi s), s < r :=
    Eventually.frequently (eventually_nhdsWithin_of_forall fun _ h => h)
  obtain ⟨T,hT,hgt⟩ := exists_seq_forall_of_frequently hfreq
  rw [tendsto_nhdsWithin_iff] at hT
  let Y : ℕ → Ω → NNReal → ℝ := fun n w u => X (T n+u) w-X (T n) w
  have hBn (n : ℕ) : MeasurableSet[F (T n)] B := by
    apply (show F.rightCont s ≤ F (T n) by
      rw [F.rightCont_eq]
      exact iInf₂_le (T n) (hgt n)) _ hB
  apply (Kyprianou.Ch03.strongMarkovPathLawOfCommonAELimitsV1
    (P.restrict B) Y (fun w u => X (s+u) w-X s w)
    (P B • Measure.map (fun w u => X u w) P)
    (fun n => measurable_pi_iff.mpr fun u => (hm _).sub (hm _))
    (fun n => hDet (T n) B (hBn n)) ?_).2
  apply Eventually.of_forall
  intro w u
  have h1 : Tendsto T atTop (nhdsWithin s (Ici s)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT.1,Eventually.of_forall fun n => (hgt n).le⟩
  have h2 : Tendsto (fun n => T n + u) atTop (nhdsWithin (s+u) (Ici (s+u))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT.1.add tendsto_const_nhds,
      Eventually.of_forall fun n => add_le_add_left (hgt n).le u⟩
  exact ((hr w (s+u)).tendsto.comp h2).sub ((hr w s).tendsto.comp h1)
