-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.condExp_brownian_filtrationPred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:06.615832+00:00
-- url     : https://prove2.me/submissions/859c0499-44c5-4a8e-9070-0d2e1da2d254

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_filtrationPred_le
import Theorems.Thm_Malliavin_le_filtrationPred
import Theorems.Thm_Malliavin_tendsto_brownianLp_exhaustion
import Theorems.Thm_Malliavin_ClarkOconeFamily_condExp_brownian

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace _root_.Malliavin.ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {t : ℝ≥0} (hat : 0 < t) :
    P[B t | filtrationPred 𝓕 t] =ᵐ[P] B t := by
  -- the exhaustion of the strict past
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
  -- Lévy's upward convergence of the conditional expectations
  have hgm : StronglyMeasurable[⨆ n, ℱ n] (P[B t | filtrationPred 𝓕 t]) := by
    rw [hsup]
    exact stronglyMeasurable_condExp
  have hlev := (integrable_condExp (m := filtrationPred 𝓕 t)
    (f := B t) (μ := P)).tendsto_ae_condExp hgm
  have hlevn : ∀ n : ℕ, P[P[B t | filtrationPred 𝓕 t] | ℱ n] =ᵐ[P] B (u n) := by
    intro n
    refine (condExp_condExp_of_le (hsup ▸ le_iSup (fun n ↦ ℱ n) n)
      (filtrationPred_le 𝓕 t)).trans ?_
    exact C.condExp_brownian (hu_lt n).le
  -- `L²` convergence and an almost everywhere convergent subsequence
  have hL2 := tendsto_brownianLp_exhaustion C.isPreBrownian t
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hcoe := ae_all_iff.2 fun n : ℕ ↦ coeFn_brownianLp C.isPreBrownian (u n)
  filter_upwards [hlev, hae, hcoe, coeFn_brownianLp C.isPreBrownian t,
    ae_all_iff.2 hlevn] with ω h1 h2 h3 h4 h5
  -- the two limits agree
  have hleft : Filter.Tendsto (fun k ↦ P[P[B t | filtrationPred 𝓕 t] | ℱ (ns k)] ω)
      Filter.atTop (nhds (P[B t | filtrationPred 𝓕 t] ω)) :=
    h1.comp hns.tendsto_atTop
  have hleft' : Filter.Tendsto (fun k ↦ B (u (ns k)) ω) Filter.atTop
      (nhds (P[B t | filtrationPred 𝓕 t] ω)) :=
    hleft.congr fun k ↦ h5 (ns k)
  have hright : Filter.Tendsto (fun k ↦ B (u (ns k)) ω) Filter.atTop (nhds (B t ω)) := by
    rw [← h4]
    exact h2.congr fun k ↦ h3 (ns k)
  exact tendsto_nhds_unique hleft' hright
end _root_.Malliavin.ClarkOconeFamily
end Malliavin
