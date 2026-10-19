-- Prove2me | solution 2 for OAI.TriangularHilbert.sampled_cubic_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:03:49.027799+00:00
-- url     : https://prove2.me/submissions/f8963293-c55e-423c-a048-7702e2ed966f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/BoundedBox.lean:L32-L52
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.sampled_cubic_tendsto. The node keeps its source
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

lemma measurable_gridSquare (h : ℝ) : Measurable (gridSquare h) :=
  ((measurable_gridPoint h).comp measurable_fst).prodMk ((measurable_gridPoint h).comp measurable_snd)

lemma tendsto_gridPoint {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => gridPoint (h n) x) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  exact (show ‖gridPoint (h n) x-x‖ < h n by simpa only [Real.norm_eq_abs] using abs_gridPoint_sub_lt (hh n) x).le

lemma tendsto_gridSquare {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (z : ℝ×ℝ) :
    Tendsto (fun n => gridSquare (h n) z) atTop (𝓝 z) :=
  (tendsto_gridPoint hh ht z.1).prodMk_nhds (tendsto_gridPoint hh ht z.2)

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

-- ---- from OAI.Analysis.TriangularHilbert.BoundedBox ----
namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma mem_closedBox (M : ℝ) (z : ℝ×ℝ) : z ∈ closedBox M ↔ |z.1| ≤ M ∧ |z.2| ≤ M := by
  simp only [closedBox,Set.mem_prod,Set.mem_Icc,abs_le]
lemma measurableSet_closedBox (M : ℝ) : MeasurableSet (closedBox M) := measurableSet_Icc.prod measurableSet_Icc
lemma isCompact_closedBox (M : ℝ) : IsCompact (closedBox M) := isCompact_Icc.prod isCompact_Icc
lemma volume_closedBox_ne_top (M : ℝ) : volume (closedBox M) ≠ ⊤ := (isCompact_closedBox M).measure_ne_top

lemma sampled_cubic_tendsto (f : ℝ×ℝ → ℂ) (hf : Continuous f) {M C : ℝ}
    (hs : BoxSupport f M) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖f (gridSquare (h n) z)‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  let b : ℝ×ℝ → ℝ := (closedBox (M+1)).indicator (fun _ => C^3)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact (((hf.measurable.comp (measurable_gridSquare (h n))).norm).pow_const 3).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := closedBox (M+1)) (C := C^3)
      (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)
  · intro n
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    by_cases hz : f (gridSquare (h n) z) = 0
    · simp only [hz,norm_zero,zero_pow (by norm_num : 3 ≠ 0),b]
      exact Set.indicator_nonneg (fun _ _ => pow_nonneg hC _) _
    · dsimp only [b]
      rw [Set.indicator_of_mem ((mem_closedBox _ _).mpr (sampled_support f (hh n) (hh1 n) hs z hz))]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) _
  · filter_upwards [] with z
    exact (((hf.tendsto _).comp (tendsto_gridSquare hh ht z)).norm).pow 3
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.sampled_cubic_tendsto := @_root_.OAI.TriangularHilbert.sampled_cubic_tendsto
