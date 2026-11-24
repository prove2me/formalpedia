-- Prove2me | solution 1 for Kyprianou.Ch03.stableHighIndexUnitIntervalVariationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:34.447663+00:00
-- url     : https://prove2.me/submissions/d0dcaf28-596f-4725-81d4-a8e7ce32e5d7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_stableHighIndexNoIntegerMomentsV1
import Theorems.Thm_Kyprianou_Ch03_stableHighGridExpectationTendstoZeroV1
import Theorems.Thm_Kyprianou_Ch03_stableGridUnboundedFromLaplaceV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

open Kyprianou.Ch03
theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    1 < alpha →
      ∀ᵐ omega ∂P, ∀ M : ℝ,
        ∃ n : ℕ, ∃ times : Fin (n + 1) → NNReal,
          times 0 = 0 ∧ times (Fin.last n) ≤ 1 ∧
          (∀ i : Fin n, times i.castSucc < times i.succ) ∧
          M < ∑ i : Fin n,
            |X (times i.succ) omega - X (times i.castSucc) omega| := by
  intro ha
  have hne : ¬ X 1 =ᵐ[P] 0 := by
    intro h
    apply Kyprianou.Ch03.stableHighIndexNoIntegerMomentsV1 P X hX T hLK alpha c hAlpha hC hGaussian hMeasure hStable ha 2 (by norm_num)
    apply (integrable_const (0 : ℝ)).congr
    filter_upwards [h] with w hw
    change X 1 w = 0 at hw
    simp [hw]
  let G (n : ℕ) (w : Omega) : ℝ := ∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : NNReal) * (((n : NNReal) + 1)⁻¹)) w -
           X ((i.val : NNReal) * (((n : NNReal) + 1)⁻¹)) w|
  have hm (t : NNReal) : AEMeasurable (X t) P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  have hG (n : ℕ) : AEMeasurable (G n) P := by
    dsimp [G]
    let F : Fin (n + 1) → Omega → ℝ := fun i w =>
      |X (((i.val + 1 : ℕ) : NNReal) * (((n : NNReal) + 1)⁻¹)) w -
        X ((i.val : NNReal) * (((n : NNReal) + 1)⁻¹)) w|
    have hf (i : Fin (n + 1)) : AEMeasurable (F i) P :=
      ((hm _).sub (hm _)).abs
    have hh : AEMeasurable (∑ i : Fin (n+1), F i) P :=
      Finset.aemeasurable_sum _ fun i _ => hf i
    convert hh using 1
    funext w
    simp [Finset.sum_apply, F]
  have hnon (n : ℕ) : 0 ≤ᵐ[P] G n := Filter.Eventually.of_forall fun w =>
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hlim : Tendsto (fun n => ∫ w, Real.exp (-G n w) ∂P) atTop (𝓝 0) :=
    Kyprianou.Ch03.stableHighGridExpectationTendstoZeroV1 P X hX alpha ha hne hStable
  filter_upwards [Kyprianou.Ch03.stableGridUnboundedFromLaplaceV1 P G hG hnon hlim] with w hw
  intro M
  obtain ⟨n, hn⟩ := hw M
  let times : Fin (n + 1 + 1) → NNReal := fun i => (i.val : NNReal) * (((n : NNReal) + 1)⁻¹)
  refine ⟨n+1, times, ?_, ?_, ?_, ?_⟩
  · simp [times]
  · simp [times]
  · intro i
    dsimp [times]
    apply mul_lt_mul_of_pos_right _ (by positivity)
    exact_mod_cast Nat.lt_succ_self i.val
  · simpa [times, G] using hn
