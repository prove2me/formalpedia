-- Prove2me | solution 1 for OAI.TriangularHilbert.exists_cubic_approximation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:28:22.132328+00:00
-- url     : https://prove2.me/submissions/89f15537-db2f-4738-a407-236454ab8b6a

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscreteMax

open OAI OAI.TriangularHilbert
universe uα
open MeasureTheory Filter
open scoped Topology ENNReal NNReal


theorem solution (f : ℝ×ℝ → ℂ) (hf : MemLp f 3 volume) :
    ∃ g : ℕ → ℝ×ℝ → ℂ, (∀ n, Continuous (g n) ∧ HasCompactSupport (g n) ∧ MemLp (g n) 3 volume) ∧
      ∃ D : ℝ×ℝ → ℝ, Integrable D ∧ (∀ z, 0 ≤ D z) ∧
        (∀ᵐ z : ℝ×ℝ, (∀ n, ‖g n z‖^3 ≤ D z) ∧ Tendsto (fun n => g n z) atTop (𝓝 (f z))) := by
  have hex : ∀ n : ℕ, ∃ g : ℝ×ℝ → ℂ, HasCompactSupport g ∧ eLpNorm (f - g) 3 volume ≤ (1/2 : ℝ≥0∞)^n ∧
      Continuous g ∧ MemLp g 3 volume := fun n =>
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (by simp)
  choose g hgc hgL hgcont hgm using hex
  set e : ℕ → ℝ×ℝ → ℝ≥0∞ := fun n z => ‖f z - g n z‖ₑ ^ (3:ℝ) with he
  have hem : ∀ n, AEMeasurable (e n) := fun n =>
    ((hf.1.sub (hgm n).1).enorm).pow_const _
  have hI : ∀ n, ∫⁻ z, e n z ≤ (1/2 : ℝ≥0∞)^n := by
    intro n
    have h1 : ∫⁻ z, e n z = eLpNorm (f - g n) 3 volume ^ (3:ℝ) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
        ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)]
      rfl
    rw [h1]
    calc eLpNorm (f - g n) 3 volume ^ (3:ℝ) ≤ ((1/2 : ℝ≥0∞)^n) ^ (3:ℝ) :=
          ENNReal.rpow_le_rpow (hgL n) (by norm_num)
      _ ≤ ((1/2 : ℝ≥0∞)^n) ^ (1:ℝ) := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · exact pow_le_one₀ (by norm_num) (by norm_num)
          · norm_num
      _ = (1/2 : ℝ≥0∞)^n := ENNReal.rpow_one _
  set T : ℝ×ℝ → ℝ≥0∞ := fun z => ∑' n, e n z with hT
  have hTm : AEMeasurable T := AEMeasurable.ennreal_tsum hem
  have hTI : ∫⁻ z, T z ≠ ⊤ := by
    rw [hT, lintegral_tsum hem]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hI)
    rw [ENNReal.tsum_geometric]
    norm_num
  have hTfin := ae_lt_top' hTm hTI
  refine ⟨g, fun n => ⟨hgcont n, hgc n, hgm n⟩, fun z => 4 * ‖f z‖ ^ (3:ℝ) + 4 * (T z).toReal, ?_, ?_, ?_⟩
  · have h1 : Integrable (fun z => ‖f z‖ ^ (3:ℝ)) := by
      have := hf.integrable_norm_rpow (by norm_num) (by norm_num)
      simpa using this
    exact (h1.const_mul 4).add ((integrable_toReal_of_lintegral_ne_top hTm hTI).const_mul 4)
  · intro z; positivity
  · filter_upwards [hTfin] with z hz
    have hz' : T z ≠ ⊤ := hz.ne
    have hconv : ∀ n, (e n z).toReal = ‖f z - g n z‖ ^ (3:ℕ) := by
      intro n
      simp only [he]
      rw [← ENNReal.toReal_rpow, toReal_enorm, ← Real.rpow_natCast]
      norm_num
    refine ⟨fun n => ?_, ?_⟩
    · have hle : (e n z).toReal ≤ (T z).toReal :=
        ENNReal.toReal_mono hz' (ENNReal.le_tsum (f := fun n => e n z) n)
      rw [hconv] at hle
      have hf3 : ‖f z‖ ^ (3:ℝ) = ‖f z‖ ^ (3:ℕ) := by rw [← Real.rpow_natCast]; norm_num
      rw [hf3]
      have ha := norm_nonneg (f z)
      have hb := norm_nonneg (f z - g n z)
      have htri : ‖g n z‖ ≤ ‖f z‖ + ‖f z - g n z‖ := by
        have := norm_sub_le (f z) (f z - g n z)
        simp only [sub_sub_cancel] at this
        exact this
      have h4 : ‖g n z‖ ^ 3 ≤ (‖f z‖ + ‖f z - g n z‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) htri 3
      nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (‖f z‖ - ‖f z - g n z‖))]
    · have h0 : Tendsto (fun n => e n z) atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hz'
      have h1 : Tendsto (fun n => (e n z).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
        rw [ENNReal.toReal_zero] at this
        exact this
      simp_rw [hconv] at h1
      have h2 : Tendsto (fun n => (‖f z - g n z‖ ^ (3:ℕ)) ^ ((3:ℕ)⁻¹ : ℝ)) atTop (𝓝 0) := by
        have := h1.rpow_const (p := ((3:ℕ)⁻¹ : ℝ)) (Or.inr (by norm_num))
        simpa [Real.zero_rpow] using this
      have h3 : Tendsto (fun n => ‖g n z - f z‖) atTop (𝓝 0) := by
        refine h2.congr (fun n => ?_)
        rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num), norm_sub_rev]
      exact tendsto_iff_norm_sub_tendsto_zero.mpr h3

