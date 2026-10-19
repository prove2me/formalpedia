-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.exists_exponential_outer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:47:44.797999+00:00
-- url     : https://prove2.me/submissions/7d3f64bc-0253-4fa9-833e-9f8f1049d3d2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/OuterApproximation.lean:L59-L122
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.exists_exponential_outer. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Convexity
import Definitions.Def_OAI_Analysis_DirectCrouzeix_OuterApproximation
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_axis_support_bound
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_direction_net_distance
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_exists_axis_net

-- ---- from OAI.Analysis.DirectCrouzeix.ExponentialLevels ----
namespace OAI

universe u_135 u_136 u_137

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

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

theorem expLevel_contDiff (v : ι → ℂ) (b : ι → ℝ) : ContDiff ℝ ⊤ (expLevel v b) := by
  apply ContDiff.sum
  intro i hi
  exact ((innerSL ℝ (v i)).contDiff.add contDiff_const).exp

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_136} [Fintype ι]

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.SupportNets ----
namespace OAI

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

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem le_convexSupport {K : Set ℂ} (hK : IsCompact K) {z : ℂ} (hz : z ∈ K) (ν : ℂ) :
    inner ℝ ν z ≤ convexSupport K ν := by
  apply le_csSup (hK.image ((innerSL ℝ ν).continuous)).bddAbove
  exact mem_image_of_mem _ hz

end DirectCrouzeix.Geometry

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.OuterApproximation ----
namespace OAI

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

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem exists_exponential_outer {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hv : Convex ℝ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Finset ℂ) (v : D → ℂ) (b : D → ℝ),
      (∀ z ∈ K, expLevel v b z < 1) ∧
      IsCompact {z | expLevel v b z ≤ 1} ∧
      (∀ z, expLevel v b z ≤ 1 → ∃ w ∈ K, ‖z-w‖ < ε) := by
  classical
  obtain ⟨M,hM0,hM⟩ := hK.isBounded.exists_pos_norm_le
  let L := 2*(M+1)
  let C := 1+L+M
  have hC : 0 < C := by dsimp [C,L]; linarith
  let δ := min (1/2) (ε/(2*C))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδε : δ*C < ε := by
    have hh : δ ≤ ε/(2*C) := min_le_right _ _
    have hc := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
    nlinarith
  obtain ⟨D,hD,h1,hm1,hI,hmI,hnet⟩ := exists_axis_net hδ
  let N : ℝ := Fintype.card D
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let t := (N+1)/δ
  have ht : 0 < t := div_pos (by linarith) hδ
  have htδ : t*δ = N+1 := div_mul_cancel₀ _ (ne_of_gt hδ)
  let v : D → ℂ := fun ν => t • (ν:ℂ)
  let b : D → ℝ := fun ν => -t*(convexSupport K ν+δ)
  have he (z : ℂ) (ν : D) : inner ℝ (v ν) z+b ν = t*(inner ℝ (ν:ℂ) z-convexSupport K ν-δ) := by
    dsimp only [v,b]
    rw [real_inner_smul_left]
    ring
  have hsumlt : N*Real.exp (-t*δ) < 1 := by
    rw [neg_mul,htδ,Real.exp_neg,mul_inv_lt_iff₀ (Real.exp_pos _),one_mul]
    linarith [Real.add_one_le_exp (N+1)]
  have hinside (z : ℂ) (hz : z ∈ K) : expLevel v b z < 1 := by
    calc
      expLevel v b z ≤ ∑ _ν : D, Real.exp (-t*δ) := by
        apply Finset.sum_le_sum
        intro ν hν
        rw [he]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (le_convexSupport hK hz (ν:ℂ)) (le_of_lt ht)
        nlinarith
      _ = N*Real.exp (-t*δ) := by simp [N]
      _ < 1 := hsumlt
  have hsupport (z : ℂ) (hz : expLevel v b z ≤ 1) (ν : ℂ) (hν : ν ∈ D) :
      inner ℝ ν z ≤ convexSupport K ν+δ := by
    have hh : Real.exp (inner ℝ (v ⟨ν,hν⟩) z+b ⟨ν,hν⟩) ≤ expLevel v b z :=
      Finset.single_le_sum (f := fun i : D => Real.exp (inner ℝ (v i) z+b i))
        (fun i _ => Real.exp_nonneg _) (Finset.mem_univ (⟨ν,hν⟩ : D))
    have hex := (Real.exp_le_one_iff).mp (hh.trans hz)
    rw [he] at hex
    nlinarith
  have hbound (z : ℂ) (hz : expLevel v b z ≤ 1) : ‖z‖ ≤ L := by
    have hh := axis_support_bound hne hM h1 hm1 hI hmI (hsupport z hz)
    dsimp [L]
    linarith
  refine ⟨D,v,b,hinside,?_,?_⟩
  · apply (isCompact_closedBall (0:ℂ) L).of_isClosed_subset
    · exact isClosed_le (expLevel_contDiff v b).continuous continuous_const
    · intro z hz
      exact mem_closedBall_zero_iff.mpr (hbound z hz)
  · intro z hz
    obtain ⟨w,hw,hzw⟩ := direction_net_distance hK hne hv hδ hM hnet (hbound z hz) (hsupport z hz)
    exact ⟨w,hw,lt_of_le_of_lt hzw hδε⟩

end DirectCrouzeix.Geometry

namespace DirectCrouzeix

end DirectCrouzeix

namespace DirectCrouzeix

open Set Filter Metric

end DirectCrouzeix

end

end

end

end

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
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set
open scoped ComplexConjugate Matrix


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.exists_exponential_outer := @_root_.OAI.DirectCrouzeix.Geometry.exists_exponential_outer
