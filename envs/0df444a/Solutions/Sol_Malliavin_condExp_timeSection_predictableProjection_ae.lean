-- Prove2me | solution 1 for Malliavin.condExp_timeSection_predictableProjection_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:39.460612+00:00
-- url     : https://prove2.me/submissions/3b0e58e3-fc57-41c0-9ef0-2a5b532f25da

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_pairing_timeSection_predictableProjection_ae
import Theorems.Thm_Malliavin_memLp_timeSection_ae


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
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P) (a : ℝ≥0) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 a]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 a] := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (RandomL2 P)
  have hall : ∀ᵐ t ∂nonnegativeLebesgueMeasure, ∀ g ∈ S, a < t →
      ∫ ω, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω))
        * ((condExpL2 ℝ ℝ (𝓕.le a) g : Lp ℝ 2 P)) ω ∂P = 0 :=
    (ae_ball_iff hSc).mpr fun g _ ↦
      pairing_timeSection_predictableProjection_ae 𝓕 U a (condExpL2 ℝ ℝ (𝓕.le a) g)
  filter_upwards [hall, memLp_timeSection_ae (predictableProjection 𝓕 U : TimeProcessL2 P),
    memLp_timeSection_ae U] with t hallt hQt hUt hat
  -- the `L²` classes of the sections
  set q := hQt.toLp _ with hq
  set u := hUt.toLp _ with hu
  -- the conditional expectation of the difference vanishes, by density
  have hker : condExpL2 ℝ ℝ (𝓕.le a) (q - u) = 0 := by
    have hz : ∀ g ∈ S, ⟪((condExpL2 ℝ ℝ (𝓕.le a) (q - u) : lpMeas ℝ ℝ (𝓕 a) 2 P) :
        Lp ℝ 2 P), g⟫_ℝ = 0 := by
      intro g hg
      rw [inner_condExpL2_left_eq_right]
      have hqu : ((q - u : Lp ℝ 2 P) : W → ℝ) =ᵐ[P]
          fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω) := by
        filter_upwards [Lp.coeFn_sub q u, hQt.coeFn_toLp, hUt.coeFn_toLp] with ω h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
      rw [L2.inner_def]
      have := hallt g hg hat
      rw [← this]
      apply integral_congr_ae
      filter_upwards [hqu] with ω hω
      rw [RCLike.inner_apply, conj_trivial, hω]
      exact mul_comm _ _
    have hzero : ((condExpL2 ℝ ℝ (𝓕.le a) (q - u) : lpMeas ℝ ℝ (𝓕 a) 2 P) : Lp ℝ 2 P) = 0 :=
      hSd.eq_zero_of_inner_left ℝ hz
    exact Subtype.ext hzero
  -- translate into function-valued conditional expectations
  have hQ := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le a) hQt
  have hU := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le a) hUt
  have hsub : condExpL2 ℝ ℝ (𝓕.le a) q = condExpL2 ℝ ℝ (𝓕.le a) u := by
    have := map_sub (condExpL2 ℝ ℝ (𝓕.le a) :
      Lp ℝ 2 P →L[ℝ] lpMeas ℝ ℝ (𝓕 a) 2 P) q u
    rw [hker] at this
    have := sub_eq_zero.mp this.symm
    exact this
  calc P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 a]
      =ᵐ[P] ((condExpL2 ℝ ℝ (𝓕.le a) q : lpMeas ℝ ℝ (𝓕 a) 2 P) : W → ℝ) := hQ.symm
    _ = ((condExpL2 ℝ ℝ (𝓕.le a) u : lpMeas ℝ ℝ (𝓕 a) 2 P) : W → ℝ) := by rw [hsub]
    _ =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 a] := hU
end Malliavin
