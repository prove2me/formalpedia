-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.exists_axis_net
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:34:49.317705+00:00
-- url     : https://prove2.me/submissions/cf5c8937-d79e-46b7-a561-49d7838bcb56

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean:L53-L77
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.exists_axis_net. The node keeps its source
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

theorem exists_axis_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : Finset ℂ, (∀ ν ∈ D, ‖ν‖ = 1) ∧ 1 ∈ D ∧ -1 ∈ D ∧
      Complex.I ∈ D ∧ -Complex.I ∈ D ∧
      (∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ) := by
  classical
  obtain ⟨S,hS⟩ := (isCompact_sphere (0:ℂ) 1).elim_finite_subcover
    (fun ν : sphere (0:ℂ) 1 => ball (ν:ℂ) δ) (fun _ => isOpen_ball) (by
      intro ν hν
      exact mem_iUnion.mpr ⟨⟨ν,hν⟩,mem_ball_self hδ⟩)
  let D := S.image Subtype.val ∪ {1,-1,Complex.I,-Complex.I}
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · intro ν hν
    rcases Finset.mem_union.mp hν with hν | hν
    · obtain ⟨μ,hμ,rfl⟩ := Finset.mem_image.mp hν
      simpa only [mem_sphere,dist_zero_right] using μ.property
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hν
      rcases hν with rfl | rfl | rfl | rfl <;> simp
  · simp [D]
  · simp [D]
  · simp [D]
  · simp [D]
  · intro ν hν
    obtain ⟨μ,hμ,hνμ⟩ := mem_iUnion₂.mp (hS (by simpa only [mem_sphere,dist_zero_right] using hν))
    refine ⟨μ,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨μ,hμ,rfl⟩),?_⟩
    simpa [dist_eq_norm] using hνμ

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.exists_axis_net := @_root_.OAI.DirectCrouzeix.Geometry.exists_axis_net
