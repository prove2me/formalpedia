-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.analytic_inverse_chart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:10:10.062715+00:00
-- url     : https://prove2.me/submissions/8b66c541-1f82-4270-8e17-181f7b0236e0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean:L31-L51
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.analytic_inverse_chart. The node keeps its source
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

theorem analytic_inverse_chart {E : Type u_133} {F : Type u_134} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (ha : AnalyticAt ℂ f x) (e : E ≃L[ℂ] F)
    (hd : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ U : OpenPartialHomeomorph E F, (U : E → F) = f ∧ x ∈ U.source ∧
      AnalyticAt ℂ U.symm (f x) := by
  have hsd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← hd.fderiv]
    exact ha.hasStrictFDerivAt
  let U := hsd.toOpenPartialHomeomorph f
  have hU : (U : E → F) = f := hsd.toOpenPartialHomeomorph_coe
  have hx : x ∈ U.source := hsd.mem_toOpenPartialHomeomorph_source
  refine ⟨U,hU,hx,?_⟩
  obtain ⟨p,hp⟩ := ha
  have hc : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm e.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hp.hasFDerivAt.unique hd
  have hpU : HasFPowerSeriesAt U p x := hU ▸ hp
  simpa only [hU] using (U.hasFPowerSeriesAt_symm hx hpU hc).analyticAt

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.analytic_inverse_chart := @_root_.OAI.DirectCrouzeix.Geometry.analytic_inverse_chart
