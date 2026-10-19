-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.expLevel_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:20:07.245657+00:00
-- url     : https://prove2.me/submissions/85a4e1c0-26a8-43f8-a597-8e5a92d08cc1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExponentialLevels.lean:L77-L89
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.expLevel_convex. The node keeps its source
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

theorem expLevel_convex (v : ι → ℂ) (b : ι → ℝ) : ConvexOn ℝ univ (expLevel v b) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a c ha hc hac
  have hh (i : ι) := convexOn_exp.2 (show inner ℝ (v i) x+b i ∈ univ from mem_univ _)
    (show inner ℝ (v i) y+b i ∈ univ from mem_univ _) ha hc hac
  have he (i : ι) : inner ℝ (v i) (a • x+c • y)+b i =
      a*(inner ℝ (v i) x+b i)+c*(inner ℝ (v i) y+b i) := by
    simp only [inner_add_right,inner_smul_right]
    have hb := congrArg (fun u : ℝ => u*b i) hac
    nlinarith
  simp only [expLevel,he]
  simpa [smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.expLevel_convex := @_root_.OAI.DirectCrouzeix.Geometry.expLevel_convex
