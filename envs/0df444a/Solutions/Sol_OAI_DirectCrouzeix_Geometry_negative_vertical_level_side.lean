-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.negative_vertical_level_side
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:14:21.055984+00:00
-- url     : https://prove2.me/submissions/caa319f9-f5d0-4690-9327-79a9fafd2710

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean:L130-L181
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.negative_vertical_level_side. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts

-- ---- from OAI.Analysis.DirectCrouzeix.AnalyticCharts ----
namespace OAI

universe u_133 u_134 u_135

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem negative_vertical_level_side {f : ℂ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0) (hd : fderiv ℝ f 0 Complex.I < 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, f (x:ℂ) = 1) :
    ∃ r > 0, ∀ z ∈ ball (0:ℂ) r, (f z < 1 ↔ 0 < z.im) ∧ (1 < f z ↔ z.im < 0) := by
  have he : ∀ᶠ z in 𝓝 (0:ℂ), DifferentiableAt ℝ f z ∧ fderiv ℝ f z Complex.I < 0 := by
    have hc : ContinuousAt (fun z => fderiv ℝ f z Complex.I) 0 :=
      (hf.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    filter_upwards [hf.eventually (by norm_num),hc.eventually_lt continuousAt_const hd] with z hz hzn
    exact ⟨hz.differentiableAt (by norm_num),hzn⟩
  obtain ⟨d,hd0,hdB⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨e,he0,heB⟩ := Metric.mem_nhds_iff.mp hreal
  let r := min (d/3) e
  have hr : 0 < r := lt_min (by positivity) he0
  have hrd : 3*r ≤ d := by dsimp [r]; have := min_le_left (d/3) e; linarith
  have hre : r ≤ e := min_le_right _ _
  refine ⟨r,hr,?_⟩
  intro z hz
  have hzN : ‖z‖ < r := mem_ball_zero_iff.mp hz
  have hx : |z.re| < r := lt_of_le_of_lt (Complex.abs_re_le_norm z) hzN
  have hy : |z.im| < r := lt_of_le_of_lt (Complex.abs_im_le_norm z) hzN
  have hyI : z.im ∈ Ioo (-r) r := abs_lt.mp hy
  have h0I : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  let v := fun y : ℝ => (z.re:ℂ)+(y:ℂ)*Complex.I
  have hvB (y : ℝ) (hy : y ∈ Ioo (-r) r) : v y ∈ ball (0:ℂ) d := by
    rw [mem_ball_zero_iff]
    calc
      ‖v y‖ ≤ ‖(z.re:ℂ)‖+‖(y:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = |z.re|+|y| := by simp [Complex.norm_real,Real.norm_eq_abs]
      _ < r+r := add_lt_add hx (abs_lt.mpr hy)
      _ < d := by linarith
  have hvd (y : ℝ) : HasDerivAt v Complex.I y := by
    simpa [v] using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I |>.const_add (z.re:ℂ)
  have hder (y : ℝ) (hy : y ∈ Ioo (-r) r) :
      HasDerivAt (fun y => f (v y)) (fderiv ℝ f (v y) Complex.I) y :=
    (hdB (hvB y hy)).1.hasFDerivAt.comp_hasDerivAt y (hvd y)
  have hanti : StrictAntiOn (fun y => f (v y)) (Ioo (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro y hy
      exact (hder y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hder y (interior_subset hy)).deriv]
      exact (hdB (hvB y (interior_subset hy))).2
  have hbase : f (v 0) = 1 := by
    simpa [v] using heB (show z.re ∈ ball (0:ℝ) e from mem_ball_zero_iff.mpr (by simpa [Real.norm_eq_abs] using lt_of_lt_of_le hx hre))
  have hvz : v z.im = z := Complex.re_add_im z
  constructor
  · have hh := hanti.lt_iff_gt hyI h0I
    change (f (v z.im) < f (v 0) ↔ 0 < z.im) at hh
    rwa [hbase,hvz] at hh
  · have hh := hanti.lt_iff_gt h0I hyI
    change (f (v 0) < f (v z.im) ↔ z.im < 0) at hh
    rwa [hbase,hvz] at hh

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.negative_vertical_level_side := @_root_.OAI.DirectCrouzeix.Geometry.negative_vertical_level_side
