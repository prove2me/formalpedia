-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.direction_net_distance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:36:51.355515+00:00
-- url     : https://prove2.me/submissions/d9fdfd8d-a27f-4346-9668-58d494530f35

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean:L96-L139
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.direction_net_distance. The node keeps its source
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

theorem convexSupport_attained {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) (ν : ℂ) :
    ∃ w ∈ K, inner ℝ ν w = convexSupport K ν := by
  exact (hK.image ((innerSL ℝ ν).continuous)).sSup_mem (hne.image _)

theorem direction_net_distance {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {D : Finset ℂ} {δ M L : ℝ} (hδ : 0 < δ)
    (hM : ∀ w ∈ K, ‖w‖ ≤ M)
    (hnet : ∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ)
    {z : ℂ} (hz : ‖z‖ ≤ L)
    (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ∃ w ∈ K, ‖z-w‖ ≤ δ*(1+L+M) := by
  obtain ⟨w,hw,hwmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv z
  have hM0 : 0 ≤ M := (norm_nonneg w).trans (hM w hw)
  have hL0 : 0 ≤ L := (norm_nonneg z).trans hz
  refine ⟨w,hw,?_⟩
  by_cases he : z = w
  · rw [he,sub_self,norm_zero]
    positivity
  have hn : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let ν := (‖z-w‖⁻¹:ℝ) • (z-w)
  have hν : ‖ν‖ = 1 := by simp [ν,ne_of_gt hn]
  obtain ⟨μ,hμ,hνμ⟩ := hnet ν hν
  obtain ⟨u,hu,hsu⟩ := convexSupport_attained hK hne μ
  have hmin : inner ℝ ν (u-w) ≤ 0 := by
    have hh := (norm_eq_iInf_iff_real_inner_le_zero hconv hw).mp hwmin u hu
    dsimp only [ν]
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hn)) hh
  have hzw : inner ℝ ν (z-w) = ‖z-w‖ := by
    dsimp only [ν]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hmain : ‖z-w‖ ≤ inner ℝ ν (z-u) := by
    have heq : z-w = (z-u)+(u-w) := by abel
    rw [← hzw,heq,inner_add_right]
    linarith
  have hμbound : inner ℝ μ (z-u) ≤ δ := by
    rw [inner_sub_right,hsu]
    linarith [hs μ hμ]
  have hnorm : ‖z-u‖ ≤ L+M := (norm_sub_le z u).trans (add_le_add hz (hM u hu))
  have herror : inner ℝ (ν-μ) (z-u) ≤ δ*(L+M) := by
    calc
      inner ℝ (ν-μ) (z-u) ≤ ‖ν-μ‖*‖z-u‖ := real_inner_le_norm _ _
      _ ≤ δ*(L+M) := mul_le_mul (le_of_lt hνμ) hnorm (norm_nonneg _) (le_of_lt hδ)
  have heq : inner ℝ ν (z-u) = inner ℝ μ (z-u)+inner ℝ (ν-μ) (z-u) := by
    rw [inner_sub_left]; ring
  rw [heq] at hmain
  nlinarith

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.direction_net_distance := @_root_.OAI.DirectCrouzeix.Geometry.direction_net_distance
