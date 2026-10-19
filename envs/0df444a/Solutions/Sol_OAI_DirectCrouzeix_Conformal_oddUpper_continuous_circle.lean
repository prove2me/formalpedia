-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.oddUpper_continuous_circle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:53:43.297183+00:00
-- url     : https://prove2.me/submissions/43f39514-ddea-4337-8bef-785b8df26500

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean:L133-L157
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.oddUpper_continuous_circle. The node keeps its source
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

-- ---- from OAI.Analysis.DirectCrouzeix.HarmonicReflection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_132

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

theorem oddUpper_continuous_circle {R : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    ContinuousOn (oddUpper u) (sphere 0 R) := by
  classical
  apply ContinuousOn.if
  · intro z hz
    have hfr := Complex.continuous_im.frontier_preimage_subset (Ici (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hfr
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz0
    simp [hc, hzero z hz0]
  · apply hu.mono
    intro z hz
    have hi : 0 ≤ z.im := by
      exact (closure_minimal (by intro w hw; exact hw)
        (isClosed_le continuous_const Complex.continuous_im)) hz.2
    exact ⟨sphere_subset_closedBall hz.1, hi⟩
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    have hi : z.im ≤ 0 := by
      exact (closure_minimal (by intro w hw; exact (le_of_not_ge hw))
        (isClosed_le Complex.continuous_im continuous_const)) hz.2
    exact ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using
      sphere_subset_closedBall hz.1, by simpa only [mem_ofPred_eq, Complex.conj_im, neg_nonneg] using hi⟩

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.oddUpper_continuous_circle := @_root_.OAI.DirectCrouzeix.Conformal.oddUpper_continuous_circle
