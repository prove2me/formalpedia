-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49AllPathDepthWitnessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:39:18.34242+00:00
-- url     : https://prove2.me/submissions/0a68e5a9-7023-4725-aa24-1680d60afb21

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49AllPathExactClockV1
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalDepthMeasV1
import Theorems.Thm_Kyprianou_Ch04_exercise49StoppedDeficitFutureProductV1
import Theorems.Thm_Kyprianou_Ch04_exercise49DepthCDFAndZeroV1
import Theorems.Thm_Kyprianou_Ch04_exercise49DepthSplitAEV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
/-- Assemble the exact clock, path depth and stopped product law. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (X : NNReal → Omega → ℝ)
    (hLevy : IsLevyProcess X P) (hm : ∀ t, Measurable (X t))
    (hc : ∀ omega, IsCadlag (fun t => X t omega))
    (hTendsInfinity : ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) :
    let tau : Real → Omega → WithTop NNReal := fun initial omega =>
      sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ initial + X t omega < 0}
    ∀ (finiteTime : Omega → NNReal), Measurable finiteTime →
      (∀ᵐ omega ∂P, tau 0 omega ≠ ⊤ →
        tau 0 omega = (finiteTime omega : WithTop NNReal)) →
          ∃ (D : Set Omega) (I V W : Omega → ℝ),
            MeasurableSet D ∧ Measurable I ∧ Measurable V ∧ Measurable W ∧
            (P D = P {omega : Omega | tau 0 omega ≠ ⊤}) ∧
            (∀ B : Set Real, MeasurableSet B →
              P (I ⁻¹' B ∩ D) = P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                -(X (finiteTime omega) omega) ∈ B}) ∧
            (∀ x : Real, 0 ≤ x →
              P (V ⁻¹' Set.Iic x) = P {omega : Omega | tau x omega = ⊤}) ∧
            (∀ᵐ omega ∂P.restrict Dᶜ, V omega = 0) ∧
            (∀ᵐ omega ∂P.restrict D, V omega = I omega + W omega) ∧
            Measure.map (fun omega => (I omega, W omega)) (P.restrict D) =
              (Measure.map I (P.restrict D)).prod (Measure.map V P) := by
  dsimp only
  intro finiteTime hf he
  let τ : Omega → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
    ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0}
  obtain ⟨hτ, f, hfm, hfe⟩ := exercise49AllPathExactClockV1 P X hLevy hm hc
  let D : Set Omega := {w | τ w ≠ ⊤}
  let I : Omega → ℝ := fun w => -X (f w) w
  let H : (NNReal → ℝ) → ℝ := fun Y =>
    (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal
  let A : Omega → (NNReal → ℝ) := fun w t => X t w
  let U : Omega → (NNReal → ℝ) := fun w t => X (f w + t) w - X (f w) w
  let V := H ∘ A
  let W := H ∘ U
  have hD : MeasurableSet D := (hτ (measurableSet_singleton ⊤)).compl
  have hH : Measurable H := exercise49RationalDepthMeasV1
  have hA : Measurable A := measurable_pi_iff.mpr hm
  have hj := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    X hm (fun w t => (hc w t).1)
  have hI : Measurable I := (hj.comp (hfm.prodMk measurable_id)).neg
  have hU : Measurable U := measurable_pi_iff.mpr fun t =>
    (hj.comp ((hfm.add measurable_const).prodMk measurable_id)).sub
      (hj.comp (hfm.prodMk measurable_id))
  have hProd := exercise49StoppedDeficitFutureProductV1 P X hLevy hm hc
    τ (fun _ => rfl) hτ f hfm hfe
  have hprodW : Measure.map (fun w => (I w, W w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map V P) := by
    change Measure.map (Prod.map (id : ℝ → ℝ) H ∘ fun w => (I w, U w)) (P.restrict D) = _
    have hmap : Measurable (Prod.map (id : ℝ → ℝ) H) := measurable_fst.prodMk
      (hH.comp measurable_snd)
    rw [← Measure.map_map hmap (hI.prodMk hU)]
    change Measure.map (Prod.map (id : ℝ → ℝ) H) ((P.restrict D).map (fun w => (I w, U w))) = _
    rw [hProd, ← Measure.map_prod_map _ _ measurable_id hH, Measure.map_id,
      Measure.map_map hH hA]
  obtain ⟨hCDF, hZero⟩ := exercise49DepthCDFAndZeroV1 P X hLevy hm hc
    hTendsInfinity τ (fun _ => rfl) hτ f hfm hfe
  have hSplit := exercise49DepthSplitAEV1 P X hLevy hm hc
    hTendsInfinity τ (fun _ => rfl) hτ f hfm hfe
  refine ⟨D, I, V, W, hD, hI, hH.comp hA, hH.comp hU, ?_, ?_, hCDF, ?_,
    hSplit, hprodW⟩
  · simp only [D, τ, zero_add]
  · intro B hB
    apply measure_congr
    filter_upwards [he] with w hw
    change ((-X (f w) w ∈ B) ∧ τ w ≠ ⊤) =
      (sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ 0 + X t w < 0} ≠ ⊤ ∧ -X (finiteTime w) w ∈ B)
    simp only [zero_add] at hw ⊢
    change _ = (τ w ≠ ⊤ ∧ -X (finiteTime w) w ∈ B)
    by_cases ht : τ w = ⊤
    · simp [ht]
    · have hf' : f w = finiteTime w :=
        WithTop.coe_injective ((hfe w ht).symm.trans (hw ht))
      simp [hf', ht]
  · have hEq : Dᶜ = {w | τ w = ⊤} := by
      ext w
      simp [D]
    rw [hEq]
    exact hZero
