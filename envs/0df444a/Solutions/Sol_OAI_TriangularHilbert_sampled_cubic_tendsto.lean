-- Prove2me | solution 1 for OAI.TriangularHilbert.sampled_cubic_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:20:07.250983+00:00
-- url     : https://prove2.me/submissions/16f40588-6aa4-4b94-a521-a6b11961a028

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

open OAI OAI.TriangularHilbert
universe uE
open MeasureTheory Filter
open scoped Topology
lemma h43_gp_le {h : ℝ} (hh : 0 < h) (x : ℝ) : gridPoint h x ≤ x := by
  unfold gridPoint gridIndex
  have := Int.floor_le (x/h)
  rw [le_div_iff₀ hh] at this
  linarith

lemma h43_gp_gt {h : ℝ} (hh : 0 < h) (x : ℝ) : x - h < gridPoint h x := by
  unfold gridPoint gridIndex
  have := Int.lt_floor_add_one (x/h)
  rw [div_lt_iff₀ hh] at this
  nlinarith

lemma h43_gp_meas (h : ℝ) : Measurable (gridPoint h) := by
  unfold gridPoint gridIndex
  exact measurable_const.mul (measurable_from_top.comp (Int.measurable_floor.comp (measurable_id.div_const h)))

lemma h43_gp_tendsto {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => gridPoint (h n) x) atTop (𝓝 x) := by
  have h1 : Tendsto (fun n => x - h n) atTop (𝓝 x) := by simpa using (tendsto_const_nhds (x := x)).sub ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
    (fun n => (h43_gp_gt (hh n) x).le) (fun n => h43_gp_le (hh n) x)

theorem solution (f : ℝ×ℝ → ℂ) (hf : Continuous f) {M C : ℝ}
    (hs : BoxSupport f M) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖f (gridSquare (h n) z)‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  set S : Set (ℝ×ℝ) := Set.Icc (-(M+1)) (M+1) ×ˢ Set.Icc (-(M+1)) (M+1) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hSf : volume S ≠ ⊤ := ((isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hgs : ∀ n, Measurable (gridSquare (h n)) := fun n =>
    ((h43_gp_meas _).comp measurable_fst).prodMk ((h43_gp_meas _).comp measurable_snd)
  refine tendsto_integral_of_dominated_convergence (fun z => S.indicator (fun _ => C^3) z) ?_ ?_ ?_ ?_
  · intro n
    exact ((hf.measurable.comp (hgs n)).norm.pow_const 3).aestronglyMeasurable
  · exact (integrableOn_const (C := C^3) hSf enorm_ne_top).integrable_indicator hSm
  · intro n
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hz : f (gridSquare (h n) z) = 0
    · rw [hz, norm_zero]
      have : (0:ℝ)^3 = 0 := by norm_num
      rw [this]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · obtain ⟨h1, h2⟩ := hs _ hz
      have hzS : z ∈ S := by
        simp only [gridSquare] at h1 h2
        have a1 := h43_gp_le (hh n) z.1
        have a2 := h43_gp_gt (hh n) z.1
        have b1 := h43_gp_le (hh n) z.2
        have b2 := h43_gp_gt (hh n) z.2
        have := hh1 n
        rw [abs_le] at h1 h2
        refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rw [Set.indicator_of_mem hzS]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) 3
  · refine Filter.Eventually.of_forall (fun z => ?_)
    have hconv : Tendsto (fun n => gridSquare (h n) z) atTop (𝓝 z) :=
      (h43_gp_tendsto hh ht z.1).prodMk_nhds (h43_gp_tendsto hh ht z.2)
    exact ((hf.tendsto z).comp hconv).norm.pow 3

