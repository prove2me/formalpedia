-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.inverseExterior_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:25:33.329146+00:00
-- url     : https://prove2.me/submissions/7e168294-a7b9-4565-8add-dbf3520c4ae9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean:L112-L127
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.inverseExterior_bounded. The node keeps its source
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

theorem inverseExterior_bounded {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : ∃ L > 0, inverseExterior f a ⊆ closedBall 0 L := by
  have hnh : {z | f z < 1} ∈ 𝓝 a := (isOpen_lt hf continuous_const).mem_nhds ha
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨r⁻¹,inv_pos.mpr hr,?_⟩
  intro w hw
  rw [mem_closedBall_zero_iff]
  by_cases hw0 : w = 0
  · subst w; simp [le_of_lt (inv_pos.mpr hr)]
  by_contra hn
  have hwL : r⁻¹ < ‖w‖ := lt_of_not_ge hn
  have hninv : ‖w‖⁻¹ < r := (inv_lt_comm₀ hr (norm_pos_iff.mpr hw0)).mp hwL
  have hball : a+w⁻¹ ∈ ball a r := by simpa [dist_eq_norm,norm_inv] using hninv
  have hh : f (a+w⁻¹) < 1 := hrB hball
  have hout := (mem_inverseExterior_iff hw0).mp hw
  linarith

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.inverseExterior_bounded := @_root_.OAI.DirectCrouzeix.Geometry.inverseExterior_bounded
