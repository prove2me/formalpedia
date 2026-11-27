-- Prove2me | solution 1 for Kyprianou.Ch04.gridMarkedKernelBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:02:36.539879+00:00
-- url     : https://prove2.me/submissions/643ec751-bf42-4c8b-887b-63816ab73a7e

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_nestedGridKernelSquareV1
import Theorems.Thm_Kyprianou_Ch04_cutoffBandEnergiesV1
import Theorems.Thm_Kyprianou_Ch04_integratedKernelBudgetV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Integrate the uniform nested-band budget for arbitrary bounded time weights. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (U V : ℝ → Ω → ℝ) (S : Ω → ℝ)
    (hS : Integrable S P) (hSnn : ∀ᵐ w ∂P, 0 ≤ S w)
    (hLeft : ∀ᵐ w ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ),
      |U s w| ≤ K ∧ |U s w - V s w| ≤ K * Real.sqrt (S w))
    (hEnergy : (∫ w, S w ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    (∫ w, ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ z,
      (z * ((if a < |z| ∧ |z| < 1 then U s w else 0) -
        (if b < |z| ∧ |z| < 1 then V s w else 0)))^2 ∂ν ∂volume ∂P) ≤
      (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  let A : Set ℝ := {z | a < |z| ∧ |z| ≤ b ∧ |z| < 1}
  let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
  let q := (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal
  let Q := (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal
  let H (s z : ℝ) (w : Ω) := z * ((if a < |z| ∧ |z| < 1 then U s w else 0) -
    (if b < |z| ∧ |z| < 1 then V s w else 0))
  obtain ⟨hAb,hBb⟩ := Kyprianou.Ch04.cutoffBandEnergiesV1 ν hν a b ha hab hb
  have hp : ∀ᵐ w ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ∀ z : ℝ,
      (H s z w)^2 ≤ K^2 * (A.indicator (fun z => z^2) z +
        B.indicator (fun z => z^2) z * S w) := by
    filter_upwards [hSnn,hLeft] with w hw hL
    intro s hs z
    have h := Kyprianou.Ch04.nestedGridKernelSquareV1 a b K (Real.sqrt (S w))
      z (U s w) (V s w) hab.le hK (Real.sqrt_nonneg _) (hL s hs).1 (hL s hs).2
    rw [Real.sq_sqrt hw] at h
    change (H s z w)^2 ≤ _ at h
    have hA : A.indicator (fun z => z^2) z =
        (if a < |z| ∧ |z| ≤ b ∧ |z| < 1 then z^2 else 0) := by simp [A,B,Set.indicator_apply]
    have hB : B.indicator (fun z => z^2) z =
        (if b < |z| ∧ |z| < 1 then z^2 else 0) := by simp [A,B,Set.indicator_apply]
    rw [hA,hB]
    convert h using 1 <;> ring
  have hS0 : 0 ≤ ∫ w, S w ∂P := integral_nonneg_of_ae hSnn
  have h := Kyprianou.Ch04.integratedKernelBudgetV1 P ν T H S
    (A.indicator (fun z => z^2)) (B.indicator (fun z => z^2)) hAb.1 hBb.1 hS K hp
  change (∫ w, ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ z, (H s z w)^2 ∂ν ∂volume ∂P) ≤ _
  calc
    _ ≤ K^2 * (T : ℝ) * ((∫ z, A.indicator (fun z => z^2) z ∂ν) +
        (∫ z, B.indicator (fun z => z^2) z ∂ν) * ∫ w, S w ∂P) := h
    _ ≤ K^2 * (T : ℝ) * (q + Q * (4 * (T : ℝ) * q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hAb.2.2
        (mul_le_mul hBb.2.2 hEnergy hS0 ENNReal.toReal_nonneg)) (by positivity)
    _ = _ := by dsimp [q,Q]; ring
