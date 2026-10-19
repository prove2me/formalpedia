-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:21:31.11028+00:00
-- url     : https://prove2.me/submissions/19c5ac7b-5e51-473f-b5a7-27bcd21685a4

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
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

theorem solution (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (hK : Measurable K) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ)
    (hcont : ∀ᵐ c : ℝ, ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledKernelOutput B C (h n) K z) atTop (𝓝 (cyclicKernelOutput B C K z)) := by
  set S : Set ℝ := Set.Icc (-(M+1)) (M+1) with hS
  have hSm : MeasurableSet S := measurableSet_Icc
  have hSf : volume S ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  unfold sampledKernelOutput cyclicKernelOutput
  refine tendsto_integral_of_dominated_convergence (fun c => S.indicator (fun _ => CB*CC*L) c) ?_ ?_ ?_ ?_
  · intro n
    unfold sampledIntegrand
    have g := h43_gp_meas (h n)
    refine (Measurable.aestronglyMeasurable ?_)
    refine ((hB.measurable.comp (measurable_const.prodMk g)).mul
      (hC.measurable.comp (g.prodMk measurable_const))).mul ?_
    exact Complex.measurable_ofReal.comp (hK.comp (measurable_const.add g))
  · exact (integrableOn_const (C := CB*CC*L) hSf enorm_ne_top).integrable_indicator hSm
  · intro n
    refine Filter.Eventually.of_forall (fun c => ?_)
    unfold sampledIntegrand
    by_cases hz : B (gridPoint (h n) z.2, gridPoint (h n) c) = 0
    · rw [hz, zero_mul, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · obtain ⟨_, h2⟩ := hs _ hz
      have hcS : c ∈ S := by
        have a1 := h43_gp_le (hh n) c
        have a2 := h43_gp_gt (hh n) c
        have := hh1 n
        rw [abs_le] at h2
        exact ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hcS, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hb (gridPoint (h n) z.2, gridPoint (h n) c)
      have := hc (gridPoint (h n) c, gridPoint (h n) z.1)
      have := hk (gridPoint (h n) z.1 + gridPoint (h n) z.2 + gridPoint (h n) c)
      have := norm_nonneg (B (gridPoint (h n) z.2, gridPoint (h n) c))
      have := norm_nonneg (C (gridPoint (h n) c, gridPoint (h n) z.1))
      have := abs_nonneg (K (gridPoint (h n) z.1 + gridPoint (h n) z.2 + gridPoint (h n) c))
      apply mul_le_mul (mul_le_mul ‹_› ‹_› (by positivity) hCB) ‹_› (by positivity) (by positivity)
  · filter_upwards [hcont] with c hcK
    unfold sampledIntegrand
    have t1 := h43_gp_tendsto hh ht z.1
    have t2 := h43_gp_tendsto hh ht z.2
    have t3 := h43_gp_tendsto hh ht c
    refine (((hB.tendsto _).comp (t2.prodMk_nhds t3)).mul ((hC.tendsto _).comp (t3.prodMk_nhds t1))).mul ?_
    exact (Complex.continuous_ofReal.tendsto _).comp (hcK.tendsto.comp ((t1.add t2).add t3))

