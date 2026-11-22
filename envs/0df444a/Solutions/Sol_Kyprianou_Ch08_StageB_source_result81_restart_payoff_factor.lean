-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_restart_payoff_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:00:54.531647+00:00
-- url     : https://prove2.me/submissions/821279b9-cdff-4254-9bb8-f81238fd7070

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_technicalFullMomentExponentExistence_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_restart_payoff_factor

open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem real_ite_decider_eq {p : Prop} {d₁ d₂ : Decidable p} {u v : ℝ} :
    @ite ℝ p d₁ u v = @ite ℝ p d₂ u v :=
  congrArg (fun d => @ite ℝ p d u v) (Subsingleton.elim d₁ d₂)

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    let L := tauMinus (shifted D.X x) 0
    let U := tauPlus (shifted D.X x) a
    let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0
    let restart := fun ω =>
      if U ω < L ω then
        WithTop.recTopCoe 0 (fun t =>
          discountedAt q (t : WithTop ℝ≥0) *
            discountedAt q (tauMinus
              (fun s (_ : Unit) => a + (D.X (t + s) ω - D.X t ω)) 0 ())) (U ω)
      else 0
    Integrable low P ∧ Integrable restart P ∧
      (∫ ω, restart ω ∂P) =
        upBeforeDownExpectation P D.X q x a * downExpectation P D.X q a := by
  intro L U low restart
  obtain ⟨ψ, hψ⟩ := source_technicalFullMomentExponentExistence_v2 Ω P D
  obtain ⟨F, X, hX, _⟩ := source_result81_filtered_avram_model Ω P D ψ hψ.1
  let Lv := tauMinus (shifted X.X x) 0
  let Uv := tauPlus (shifted X.X x) a
  let lowv := fun ω => if Lv ω < Uv ω then discountedAt q (Lv ω) else 0
  let restartv : Ω → ℝ := fun ω =>
    if Uv ω < Lv ω then
      WithTop.recTopCoe (0 : ℝ) (fun t =>
        discountedAt q (t : WithTop ℝ≥0) *
          discountedAt q (tauMinus
            (fun s (_ : Unit) => a + (X.X (t + s) ω - X.X t ω)) 0 ())) (Uv ω)
    else 0
  have hv : Integrable lowv P ∧ Integrable restartv P ∧
      (∫ ω, restartv ω ∂P) =
        upBeforeDownExpectation P X.X q x a * downExpectation P X.X q a :=
    source_result81_avram_restart_payoff_factor Ω P F X q x a hq
  have hl : lowv =ᵐ[P] low := by
    filter_upwards [hX] with ω hω
    simp only [lowv, low, Uv, Lv, U, L, tauMinus, tauPlus, shifted, hω]
  have hr : restartv =ᵐ[P] restart := by
    filter_upwards [hX] with ω hω
    simp only [restartv, restart, Uv, Lv, U, L, tauMinus, tauPlus, shifted, hω] <;>
      exact real_ite_decider_eq
  have hu : upBeforeDownExpectation P X.X q x a = upBeforeDownExpectation P D.X q x a := by
    unfold upBeforeDownExpectation
    apply integral_congr_ae
    filter_upwards [hX] with ω hω
    simp only [tauMinus, tauPlus, shifted, hω]
    exact real_ite_decider_eq
  have hd : downExpectation P X.X q a = downExpectation P D.X q a := by
    unfold downExpectation
    apply integral_congr_ae
    filter_upwards [hX] with ω hω
    simp only [tauMinus, shifted, hω]
  refine ⟨hv.1.congr hl, hv.2.1.congr hr, ?_⟩
  rw [← integral_congr_ae hr, hv.2.2, hu, hd]
