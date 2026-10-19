-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.axis_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:40:00.442671+00:00
-- url     : https://prove2.me/submissions/4b11b69c-b069-4a4f-bf91-cb20776e44b3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean:L141-L158
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.axis_support_bound. The node keeps its source
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

theorem convexSupport_le {K : Set ℂ} (hne : K.Nonempty) {M : ℝ}
    (hM : ∀ z ∈ K, ‖z‖ ≤ M) {ν : ℂ} (hν : ‖ν‖ = 1) : convexSupport K ν ≤ M := by
  apply csSup_le (hne.image _)
  rintro x ⟨z,hz,rfl⟩
  exact (real_inner_le_norm ν z).trans (by simpa only [hν,one_mul] using hM z hz)

theorem axis_support_bound {K : Set ℂ} (hne : K.Nonempty) {M δ : ℝ}
    (hM : ∀ w ∈ K, ‖w‖ ≤ M) {D : Finset ℂ}
    (h1 : 1 ∈ D) (hm1 : -1 ∈ D) (hI : Complex.I ∈ D) (hmI : -Complex.I ∈ D)
    {z : ℂ} (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ‖z‖ ≤ 2*(M+δ) := by
  have hb (μ : ℂ) (hμ : μ ∈ D) (hμN : ‖μ‖ = 1) : inner ℝ μ z ≤ M+δ :=
    (hs μ hμ).trans (add_le_add_left (convexSupport_le hne hM hμN) δ)
  have hr := hb 1 h1 (by simp)
  have hrr := hb (-1) hm1 (by simp)
  have hi := hb Complex.I hI (by simp)
  have hir := hb (-Complex.I) hmI (by simp)
  simp only [real_inner_eq_re_inner ℂ,RCLike.inner_apply] at hr hrr hi hir
  simp at hr hrr hi hir
  have ha : |z.re| ≤ M+δ := abs_le.mpr ⟨by linarith,hr⟩
  have hb : |z.im| ≤ M+δ := abs_le.mpr ⟨by linarith,hi⟩
  calc
    ‖z‖ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2*(M+δ) := by linarith

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.axis_support_bound := @_root_.OAI.DirectCrouzeix.Geometry.axis_support_bound
