-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.inverseExterior_frontier_level
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:27:28.825243+00:00
-- url     : https://prove2.me/submissions/fa728d3a-a92a-4f97-8a58-477fb7ae281a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean:L143-L159
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.inverseExterior_frontier_level. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_inverseExterior_isOpen

-- ---- from OAI.Analysis.DirectCrouzeix.InverseExterior ----
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

namespace DirectCrouzeix.Geometry

theorem mem_inverseExterior_iff {f : ℂ → ℝ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ inverseExterior f a ↔ 1 < f (a+w⁻¹) := or_iff_right hw

theorem inverseExterior_frontier_level {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) {a w : ℂ}
    (hw : w ∈ frontier (inverseExterior f a)) : w ≠ 0 ∧ f (a+w⁻¹) = 1 := by
  have hU := inverseExterior_isOpen hf hc a
  have hw' : w ∈ closure (inverseExterior f a) ∧ w ∉ inverseExterior f a := by
    simpa only [frontier,hU.interior_eq,Set.mem_sdiff] using hw
  have hw0 : w ≠ 0 := by intro he; subst w; exact hw'.2 (zero_mem_inverseExterior f a)
  refine ⟨hw0,le_antisymm (le_of_not_gt (fun h => hw'.2 (Or.inr h))) ?_⟩
  by_contra hn
  have hl : f (a+w⁻¹) < 1 := lt_of_not_ge hn
  have hct : ContinuousAt (fun y : ℂ => f (a+y⁻¹)) w :=
    hf.continuousAt.comp (continuousAt_const.add (continuousAt_id.inv₀ hw0))
  have he : {y : ℂ | y ≠ 0 ∧ f (a+y⁻¹) < 1} ∈ 𝓝 w :=
    (continuousAt_id.eventually_ne hw0).and (hct.eventually_lt continuousAt_const hl)
  obtain ⟨y,hy,hyU⟩ := mem_closure_iff_nhds.mp hw'.1 _ he
  have hout := (mem_inverseExterior_iff hy.1).mp hyU
  linarith [hy.2]

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.inverseExterior_frontier_level := @_root_.OAI.DirectCrouzeix.Geometry.inverseExterior_frontier_level
