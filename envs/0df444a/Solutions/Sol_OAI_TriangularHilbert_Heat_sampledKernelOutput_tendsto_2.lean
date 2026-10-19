-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:12:48.669776+00:00
-- url     : https://prove2.me/submissions/e4743b22-b5ed-4492-8e9e-4e8e70d6da47

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SampledConvergence.lean:L32-L56
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.TriangularHilbert.GridCell ----
namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma gridCell_mem_iff {h x : ℝ} (hh : 0 < h) (i : ℤ) :
    x ∈ gridCell h i ↔ gridIndex h x = i := by
  unfold gridCell gridIndex
  rw [Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hx.1),
      (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using hx.2)⟩
  · intro hx
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp hx.1,
      by simpa only [mul_comm] using (div_lt_iff₀ hh).mp hx.2⟩

lemma gridPoint_le {h : ℝ} (hh : 0 < h) (x : ℝ) : gridPoint h x ≤ x := by
  exact ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).1

lemma gridPoint_lt_add {h : ℝ} (hh : 0 < h) (x : ℝ) : x < gridPoint h x+h := by
  have hh' := ((gridCell_mem_iff hh (gridIndex h x)).mpr rfl).2
  dsimp [gridCell,gridPoint] at *
  linarith only [hh']

lemma abs_gridPoint_sub_lt {h : ℝ} (hh : 0 < h) (x : ℝ) : |gridPoint h x-x| < h := by
  rw [abs_of_nonpos (sub_nonpos.mpr (gridPoint_le hh x))]
  linarith only [gridPoint_lt_add hh x]

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Quantization ----
namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_gridIndex (h : ℝ) : Measurable (gridIndex h) := by
  exact Int.measurable_floor.comp (measurable_id.div_const h)

lemma measurable_gridPoint (h : ℝ) : Measurable (gridPoint h) := by
  exact measurable_const.mul ((measurable_of_countable (fun i : ℤ => (i:ℝ))).comp (measurable_gridIndex h))

lemma tendsto_gridPoint {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => gridPoint (h n) x) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  exact (show ‖gridPoint (h n) x-x‖ < h n by simpa only [Real.norm_eq_abs] using abs_gridPoint_sub_lt (hh n) x).le

lemma sampled_support {E : Type uE} [Zero E] (f : ℝ×ℝ → E) {h M : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hf : ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M)
    (z : ℝ×ℝ) (hz : f (gridSquare h z) ≠ 0) :
    |z.1| ≤ M+1 ∧ |z.2| ≤ M+1 := by
  have ha := hf _ hz
  have h1 := abs_gridPoint_sub_lt hh z.1
  have h2 := abs_gridPoint_sub_lt hh z.2
  have e1 := abs_add_le (z.1-gridPoint h z.1) (gridPoint h z.1)
  have e2 := abs_add_le (z.2-gridPoint h z.2) (gridPoint h z.2)
  simp only [sub_add_cancel] at e1 e2
  rw [abs_sub_comm] at h1 h2
  dsimp [gridSquare] at ha
  exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledOutput ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma measurable_sampledIntegrand (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) :
    Measurable (fun q : (ℝ×ℝ)×ℝ => sampledIntegrand B C h K q.1 q.2) := by
  have ha : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.1) := (measurable_gridPoint h).comp (measurable_fst.comp measurable_fst)
  have hb : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.1.2) := (measurable_gridPoint h).comp (measurable_snd.comp measurable_fst)
  have hc : Measurable (fun q : (ℝ×ℝ)×ℝ => gridPoint h q.2) := (measurable_gridPoint h).comp measurable_snd
  exact ((hB.comp (hb.prodMk hc)).mul (hC.comp (hc.prodMk ha))).mul
    (Complex.measurable_ofReal.comp (hK.comp ((ha.add hb).add hc)))

lemma sampledIntegrand_support_c (B C : ℝ×ℝ → ℂ) {h M : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hB : BoxSupport B M) (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ)
    (hc : sampledIntegrand B C h K z c ≠ 0) : |c| ≤ M+1 := by
  have hne : B (gridSquare h (z.2,c)) ≠ 0 := fun he => hc (by simp only [sampledIntegrand,gridSquare] at he ⊢; rw [he]; simp)
  exact (sampled_support B hh hh1 hB (z.2,c) hne).2

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SampledConvergence ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma norm_sampledIntegrand_le (B C : ℝ×ℝ → ℂ) {CB CC L : ℝ}
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (K : ℝ → ℝ)
    (hk : ∀ t, |K t| ≤ L) (h : ℝ) (z : ℝ×ℝ) (c : ℝ) :
    ‖sampledIntegrand B C h K z c‖ ≤ CB*CC*L := by
  unfold sampledIntegrand
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) ((norm_nonneg (B 0)).trans (hb 0)))
    (hk _) (abs_nonneg _) (mul_nonneg ((norm_nonneg (B 0)).trans (hb 0)) ((norm_nonneg (C 0)).trans (hc 0)))

lemma sampledIntegrand_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ) (hk : ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledIntegrand B C (h n) K z c) atTop
      (𝓝 (B (z.2,c)*C (c,z.1)*(K (z.1+z.2+c):ℂ))) := by
  have ha := tendsto_gridPoint hh ht z.1
  have hb := tendsto_gridPoint hh ht z.2
  have hc := tendsto_gridPoint hh ht c
  exact (((hB.tendsto _).comp (hb.prodMk_nhds hc)).mul
    ((hC.tendsto _).comp (hc.prodMk_nhds ha))).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hk.tendsto.comp ((ha.add hb).add hc)))

lemma sampledKernelOutput_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (hK : Measurable K) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ)
    (hcont : ∀ᵐ c : ℝ, ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledKernelOutput B C (h n) K z) atTop (𝓝 (cyclicKernelOutput B C K z)) := by
  let b : ℝ → ℝ := (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact ((measurable_sampledIntegrand B C hB.measurable hC.measurable (h n) K hK).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  · intro n
    filter_upwards [] with c
    by_cases he : sampledIntegrand B C (h n) K z c = 0
    · rw [he,norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) _
    · have hmem : c ∈ Set.Icc (-(M+1)) (M+1) := abs_le.mp (sampledIntegrand_support_c B C (hh n) (hh1 n) hs K z c he)
      dsimp only [b]
      rw [Set.indicator_of_mem hmem]
      exact norm_sampledIntegrand_le B C hb hc K hk _ _ _
  · filter_upwards [hcont] with c hct
    exact sampledIntegrand_tendsto B C hB hC hh ht K z c hct

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto := @_root_.OAI.TriangularHilbert.Heat.sampledKernelOutput_tendsto
