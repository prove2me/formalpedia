-- Prove2me | solution 1 for Malliavin.condExp_timeSection_predictableProjection_pred_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:00.770287+00:00
-- url     : https://prove2.me/submissions/7af96b9d-29c2-46d0-a7a3-0eded901cad6

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_condExp_timeSection_predictableProjection_ae
import Theorems.Thm_Malliavin_filtrationPred_le
import Theorems.Thm_Malliavin_le_filtrationPred

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | filtrationPred 𝓕 t]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hall : ∀ᵐ t ∂nonnegativeLebesgueMeasure, ∀ q ∈ S, q < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 q]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 q] :=
    (ae_ball_iff hSc).mpr fun q _ ↦ condExp_timeSection_predictableProjection_ae 𝓕 U q
  filter_upwards [hall] with t hallt hat
  set X : W → ℝ := fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) with hX
  set Y : W → ℝ := fun ω ↦ U (t, ω) with hY
  -- every strictly earlier level
  have hA : ∀ b : ℝ≥0, b < t → P[X | 𝓕 b] =ᵐ[P] P[Y | 𝓕 b] := by
    intro b hbt
    obtain ⟨q, hqS, hbq, hqt⟩ := hSd.exists_between hbt
    calc P[X | 𝓕 b]
        =ᵐ[P] P[P[X | 𝓕 q] | 𝓕 b] := (condExp_condExp_of_le (𝓕.mono hbq.le) (𝓕.le q)).symm
      _ =ᵐ[P] P[P[Y | 𝓕 q] | 𝓕 b] := condExp_congr_ae (hallt q hqS hqt)
      _ =ᵐ[P] P[Y | 𝓕 b] := condExp_condExp_of_le (𝓕.mono hbq.le) (𝓕.le q)
  -- an increasing exhaustion of the strict past
  set u : ℕ → ℝ≥0 := fun n ↦ t - t / (n + 2) with hu
  have hu_lt : ∀ n, u n < t := fun n ↦ tsub_lt_self hat (by positivity)
  have hu_mono : Monotone u := by
    intro m n hmn
    refine tsub_le_tsub_left ?_ t
    gcongr
  set ℱ : Filtration ℕ ‹MeasurableSpace W› :=
    ⟨fun n ↦ 𝓕 (u n), fun m n hmn ↦ 𝓕.mono (hu_mono hmn), fun n ↦ 𝓕.le _⟩ with hℱ
  have hsup : (⨆ n, ℱ n) = filtrationPred 𝓕 t := by
    refine le_antisymm (iSup_le fun n ↦ le_filtrationPred 𝓕 (hu_lt n)) (iSup₂_le fun s hst ↦ ?_)
    have hts : t - s ≠ 0 := (tsub_pos_of_lt hst).ne'
    obtain ⟨n, hn⟩ := exists_nat_ge (t / (t - s))
    have hle : t / ((n : ℝ≥0) + 2) ≤ t - s := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (pos_of_ne_zero hts)] at hn
      calc t ≤ (n : ℝ≥0) * (t - s) := hn
        _ ≤ ((n : ℝ≥0) + 2) * (t - s) := by gcongr; exact le_self_add
        _ = (t - s) * ((n : ℝ≥0) + 2) := mul_comm _ _
    have hsn : s ≤ u n := by
      rw [hu]
      have := tsub_le_tsub_left hle t
      refine le_trans ?_ this
      rw [tsub_tsub_cancel_of_le hst.le]
    exact le_trans (𝓕.mono hsn) (le_iSup (fun n ↦ ℱ n) n)
  -- Lévy's upward theorem for both conditional expectations
  have hXg : Integrable (P[X | filtrationPred 𝓕 t]) P := integrable_condExp
  have hYg : Integrable (P[Y | filtrationPred 𝓕 t]) P := integrable_condExp
  have hXm : StronglyMeasurable[⨆ n, ℱ n] (P[X | filtrationPred 𝓕 t]) := by
    rw [hsup]
    exact stronglyMeasurable_condExp
  have hYm : StronglyMeasurable[⨆ n, ℱ n] (P[Y | filtrationPred 𝓕 t]) := by
    rw [hsup]
    exact stronglyMeasurable_condExp
  have hXlim := hXg.tendsto_ae_condExp hXm
  have hYlim := hYg.tendsto_ae_condExp hYm
  -- the approximating conditional expectations agree
  have hlevels : ∀ n : ℕ, P[P[X | filtrationPred 𝓕 t] | ℱ n]
      =ᵐ[P] P[P[Y | filtrationPred 𝓕 t] | ℱ n] := by
    intro n
    have h1 : P[P[X | filtrationPred 𝓕 t] | ℱ n] =ᵐ[P] P[X | ℱ n] :=
      condExp_condExp_of_le (hsup ▸ le_iSup (fun n ↦ ℱ n) n) (filtrationPred_le 𝓕 t)
    have h2 : P[P[Y | filtrationPred 𝓕 t] | ℱ n] =ᵐ[P] P[Y | ℱ n] :=
      condExp_condExp_of_le (hsup ▸ le_iSup (fun n ↦ ℱ n) n) (filtrationPred_le 𝓕 t)
    exact h1.trans ((hA (u n) (hu_lt n)).trans h2.symm)
  have hlevels' := ae_all_iff.mpr hlevels
  filter_upwards [hXlim, hYlim, hlevels'] with ω hXω hYω hlω
  refine tendsto_nhds_unique ?_ hYω
  refine hXω.congr fun n ↦ ?_
  exact hlω n
end Malliavin
