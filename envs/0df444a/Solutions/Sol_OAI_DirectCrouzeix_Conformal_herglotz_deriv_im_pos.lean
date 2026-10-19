-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.herglotz_deriv_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:57:56.625442+00:00
-- url     : https://prove2.me/submissions/f09bc5ef-6d73-4150-ad76-076789c0896e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean:L94-L139
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.herglotz_deriv_im_pos. The node keeps its source
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

-- ---- from OAI.Analysis.DirectCrouzeix.HolomorphicReflection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

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

theorem circleAverage_pos_upper {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, 0 ≤ u z) (hp : 0 < u ((R : ℂ) * Complex.I)) :
    0 < Real.circleAverage u 0 R := by
  have hall (θ : ℝ) : circleMap 0 R θ ∈ sphere 0 R := by
    simpa only [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
  have hc : Continuous (fun θ => u (circleMap 0 R θ)) :=
    hu.comp_continuous (continuous_circleMap 0 R) hall
  have hip : 0 < ∫ θ in (0 : ℝ)..2 * Real.pi, u (circleMap 0 R θ) := by
    apply intervalIntegral.integral_pos Real.two_pi_pos hc.continuousOn
    · intro θ _
      exact hn _ (hall θ)
    · refine ⟨Real.pi / 2, ⟨by positivity, by nlinarith [Real.pi_pos]⟩, ?_⟩
      simpa only [circleMap_pi_div_two, zero_add] using hp
  exact mul_pos (inv_pos.mpr Real.two_pi_pos) hip

theorem herglotz_deriv_im_pos {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, u z * z.im ≤ 0)
    (hp : u ((R : ℂ) * Complex.I) < 0) :
    0 < (deriv (herglotzExtension R u) 0).im := by
  let d := fun ζ : ℂ => (2 / ζ) * (u ζ : ℂ)
  have hzne : ∀ ζ ∈ sphere 0 R, ζ ≠ (0 : ℂ) := by
    intro ζ hζ hz
    subst ζ
    exact hR.ne' (by simpa only [mem_sphere, dist_self, eq_comm] using hζ)
  have hd : ContinuousOn d (sphere 0 R) :=
    (continuousOn_const.div continuousOn_id hzne).mul (Complex.continuous_ofReal.comp_continuousOn hu)
  have hder := hasDerivAt_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hu).circleIntegrable hR.le)
    (mem_ball_self hR : (0 : ℂ) ∈ ball 0 R)
  change HasDerivAt (herglotzExtension R u) _ _ at hder
  have hval : deriv (herglotzExtension R u) 0 = Real.circleAverage d 0 R := by
    rw [hder.deriv]
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    have hz : ζ ≠ 0 := hzne ζ (by simpa only [abs_of_pos hR] using hζ)
    dsimp [d]
    simp only [sub_zero]
    congr 1
    field_simp
  have he (ζ : ℂ) : (d ζ).im = -2 * (u ζ * ζ.im) / Complex.normSq ζ := by
    dsimp [d]
    simp [Complex.mul_im, Complex.div_im]
    ring
  have hnon : ∀ ζ ∈ sphere 0 R, 0 ≤ (d ζ).im := by
    intro ζ hζ
    rw [he]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hn ζ hζ))
      (Complex.normSq_nonneg ζ)
  have hpos : 0 < (d ((R : ℂ) * Complex.I)).im := by
    rw [he]
    have him : ((R : ℂ) * Complex.I).im = R := by simp
    rw [him]
    apply div_pos
    · exact mul_pos_of_neg_of_neg (by norm_num) (mul_neg_of_neg_of_pos hp hR)
    · rw [Complex.normSq_pos]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') Complex.I_ne_zero
  rw [hval]
  change 0 < Complex.imCLM (Real.circleAverage d 0 R)
  rw [← Complex.imCLM.circleAverage_comp_comm (hd.circleIntegrable hR.le)]
  exact circleAverage_pos_upper hR.le (Complex.continuous_im.comp_continuousOn hd) hnon hpos

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.herglotz_deriv_im_pos := @_root_.OAI.DirectCrouzeix.Conformal.herglotz_deriv_im_pos
