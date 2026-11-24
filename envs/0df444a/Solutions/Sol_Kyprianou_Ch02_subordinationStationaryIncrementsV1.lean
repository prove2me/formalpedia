-- Prove2me | solution 1 for Kyprianou.Ch02.subordinationStationaryIncrementsV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:03:45.362586+00:00
-- url     : https://prove2.me/submissions/f9ba08f1-740d-4e96-a8b4-06c4df48ddc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_subordinationIncrementTestMixtureV1
import Theorems.Thm_Kyprianou_Ch02_levyTimeTestKernelMeasurableV1
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
  let Y (t : ℝ≥0) (ω : Ω) := X (τ t ω) ω
  let V := increment Y s (s + h)
  let W := increment Y 0 h
  have hs : s ≤ s + h := le_self_add
  have hv : AEMeasurable V P :=
    (Kyprianou.Ch02.subordinationIncrementTestMixtureV1 P X τ hX hτ hmon hind
      s (s + h) hs (fun _ => 0) measurable_const 0 (by simp)).1
  have hw : AEMeasurable W P :=
    (Kyprianou.Ch02.subordinationIncrementTestMixtureV1 P X τ hX hτ hmon hind
      0 h (by positivity) (fun _ => 0) measurable_const 0 (by simp)).1
  refine ⟨hv, hw, ?_⟩
  letI : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hv
  letI : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hw
  apply Measure.ext_of_charFun
  funext ξ
  let H (x : ℝ) := Complex.exp ((ξ : ℂ) * (x : ℂ) * I)
  have hH : Measurable H := by unfold H; fun_prop
  have hC (x : ℝ) : ‖H x‖ ≤ 1 := by simp [H, Complex.norm_exp, mul_re, mul_im]
  rw [charFun_apply_real, charFun_apply_real, integral_map hv hH.aestronglyMeasurable,
    integral_map hw hH.aestronglyMeasurable]
  change (∫ ω, H (Y (s + h) ω - Y s ω) ∂P) =
    ∫ ω, H (Y h ω - Y 0 ω) ∂P
  rw [(Kyprianou.Ch02.subordinationIncrementTestMixtureV1 P X τ hX hτ hmon hind
    s (s + h) hs H hH 1 hC).2,
    (Kyprianou.Ch02.subordinationIncrementTestMixtureV1 P X τ hX hτ hmon hind
      0 h (by positivity) H hH 1 hC).2]
  let K (r : ℝ) := ∫ ω, H (X r.toNNReal ω) ∂P
  have hK : Measurable K := Kyprianou.Ch02.levyTimeTestKernelMeasurableV1 P X hX H hH
  exact ((hτ.stationary_increments s h).comp hK).integral_eq
