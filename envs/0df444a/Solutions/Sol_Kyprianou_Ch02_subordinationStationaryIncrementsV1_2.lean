-- Prove2me | solution 2 for Kyprianou.Ch02.subordinationStationaryIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:11:24.239725+00:00
-- url     : https://prove2.me/submissions/4fb4512f-413e-455e-9488-e5f7ca2cf078

import Theorems.Thm_Kyprianou_Ch02_subordinatedIncrementCharMixtureV1
import Theorems.Thm_Kyprianou_Ch02_levyCharFunTimeMeasurableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P) :
    ProbabilityTheory.HasStationaryIncrements (fun t ω => X (τ t ω) ω) P := by
  intro s h
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => X (τ t ω) ω
  have hst : s ≤ s+h := le_add_of_nonneg_right (by positivity)
  have hm1 := (Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
    P X τ hX hτ hmon hind s (s+h) hst 0).1
  have hm2 := (Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
    P X τ hX hτ hmon hind 0 h (by positivity) 0).1
  refine ⟨hm1, hm2, ?_⟩
  letI : IsProbabilityMeasure (P.map (increment Y s (s+h))) :=
    Measure.isProbabilityMeasure_map hm1
  letI : IsProbabilityMeasure (P.map (increment Y 0 h)) :=
    Measure.isProbabilityMeasure_map hm2
  apply Measure.ext_of_charFun
  funext ξ
  rw [(Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
    P X τ hX hτ hmon hind s (s+h) hst ξ).2,
    (Kyprianou.Ch02.subordinatedIncrementCharMixtureV1
    P X τ hX hτ hmon hind 0 h (by positivity) ξ).2]
  let K : ℝ → ℂ := fun r => charFun (P.map (X r.toNNReal)) ξ
  have hK : Measurable K :=
    (Kyprianou.Ch02.levyCharFunTimeMeasurableV1 P X hX ξ).comp measurable_real_toNNReal
  have he := ((hτ.stationary_increments s h).comp hK).integral_eq
  calc
    _ = ∫ ω, K (increment (fun t ω => (τ t ω : ℝ)) s (s+h) ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hmon] with ω hw
      simp [K, increment, ← NNReal.coe_sub (hw hst)]
    _ = ∫ ω, K (increment (fun t ω => (τ t ω : ℝ)) 0 h ω) ∂P := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hmon] with ω hw
      simp [K, increment, ← NNReal.coe_sub (hw (show 0 ≤ h from bot_le))]
