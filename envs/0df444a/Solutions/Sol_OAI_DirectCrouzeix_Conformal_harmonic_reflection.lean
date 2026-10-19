-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.harmonic_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:56:09.532723+00:00
-- url     : https://prove2.me/submissions/9a92d4ec-def3-4440-ba04-fa991d47aa1f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean:L159-L204
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.harmonic_reflection. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_harmonic_le_boundary
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_oddUpper_continuous_circle
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_poisson_boundary_limit

-- ---- from OAI.Analysis.DirectCrouzeix.PoissonBoundary ----
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

theorem herglotz_analytic {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    AnalyticOnNhd ℂ (herglotzExtension R u) (ball 0 R) := by
  exact (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hu).circleIntegrable hR)).mono
      (by intro z hz; exact hz)

theorem herglotz_re {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {z : ℂ} (hz : z ∈ ball 0 R) :
    (herglotzExtension R u z).re = poissonExtension R u z := by
  have hi : CircleIntegrable
      (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R := by
    exact ((continuousOn_herglotzRieszKernel_sphere hz).mul
      (Complex.continuous_ofReal.comp_continuousOn (by simpa only [abs_of_nonneg hR] using hu))).circleIntegrable'
  change Complex.reCLM (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R) = _
  rw [← Complex.reCLM.circleAverage_comp_comm hi]
  dsimp [poissonExtension]
  congr 1
  ext ζ
  simp [poissonKernel_eq_re_herglotzRieszKernel]

theorem poisson_harmonic {R : ℝ} (hR : 0 ≤ R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    HarmonicOnNhd (poissonExtension R u) (ball 0 R) := by
  intro z hz
  have he : (poissonExtension R u) =ᶠ[𝓝 z]
      (fun w => (herglotzExtension R u w).re) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (herglotz_re hR hu hw).symm
  rw [harmonicAt_congr_nhds he]
  exact ((herglotz_analytic hR hu z hz).harmonicAt.comp_CLM Complex.reCLM)

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.HarmonicReflection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem circleAverage_conj {E : Type u_132} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) :
    Real.circleAverage (fun ζ => f (conj ζ)) 0 R = Real.circleAverage f 0 R := by
  conv_lhs => rw [Real.circleAverage_eq_circleAverage_zero_one]
  conv_rhs => rw [Real.circleAverage_eq_circleAverage_zero_one]
  calc
    Real.circleAverage (fun z => f (conj ((R : ℂ) * z + 0))) 0 1 =
        Real.circleAverage (fun z => f ((R : ℂ) * z⁻¹ + 0)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = 1 := by simpa using hz
      simp [Complex.inv_eq_conj hn]
    _ = Real.circleAverage (fun z => f ((R : ℂ) * z + 0)) 0 1 :=
      Real.circleAverage_zero_one_congr_inv (f := fun z => f ((R : ℂ) * z + 0))

theorem poisson_conj (z ζ : ℂ) :
    poissonKernel 0 (conj z) (conj ζ) = poissonKernel 0 z ζ := by
  simp only [poissonKernel, sub_zero, Complex.norm_conj, ← map_sub]

theorem poisson_odd {R : ℝ} {u : ℂ → ℝ}
    (hu : ∀ ζ, u (conj ζ) = -u ζ) (z : ℂ) :
    poissonExtension R u (conj z) = -poissonExtension R u z := by
  dsimp [poissonExtension]
  rw [← circleAverage_conj (fun ζ => poissonKernel 0 (conj z) ζ * u ζ) R]
  simp_rw [poisson_conj, hu, mul_neg]
  have he (ζ : ℂ) : -(poissonKernel 0 z ζ * u ζ) = (-1 : ℝ) • (poissonKernel 0 z ζ * u ζ) := by simp
  simp_rw [he]
  rw [Real.circleAverage_fun_smul, neg_one_smul]

theorem poisson_real_zero {R : ℝ} {u : ℂ → ℝ}
    (hu : ∀ ζ, u (conj ζ) = -u ζ) {z : ℂ} (hz : z.im = 0) :
    poissonExtension R u z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
  have hh := poisson_odd (R := R) hu z
  rw [hc] at hh
  linarith

theorem poissonClosed_continuous {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) :
    ContinuousOn (poissonClosed R u) (closedBall 0 R) := by
  classical
  unfold poissonClosed
  apply ContinuousOn.if'
  · intro a ha
    have haS : a ∈ sphere 0 R := by
      simpa only [Set.ofPred_mem_eq, frontier_ball (0 : ℂ) hR.ne'] using ha.2
    have haN : a ∉ ball 0 R := fun h => sphere_disjoint_ball.le_bot ⟨haS, h⟩
    simp only [haN, ↓reduceIte]
    exact (poisson_boundary_limit hR hu haS).mono_left (nhdsWithin_mono _ inter_subset_right)
  · intro a ha
    have haS : a ∈ sphere 0 R := by
      simpa only [Set.ofPred_mem_eq, frontier_ball (0 : ℂ) hR.ne'] using ha.2
    have haN : a ∉ ball 0 R := fun h => sphere_disjoint_ball.le_bot ⟨haS, h⟩
    simp only [haN, ↓reduceIte]
    apply (hu a haS).mono
    intro z hz
    exact le_antisymm (mem_closedBall.mp hz.1) (not_lt.mp hz.2)
  · exact (poisson_harmonic hR.le hu).continuousOn.mono inter_subset_right
  · apply hu.mono
    intro z hz
    exact le_antisymm (mem_closedBall.mp hz.1) (not_lt.mp hz.2)

theorem upperBall_open (R : ℝ) : IsOpen (upperBall R) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem upperClosedBall_closed (R : ℝ) : IsClosed (upperClosedBall R) :=
  isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

theorem closure_upperBall_subset (R : ℝ) : closure (upperBall R) ⊆ upperClosedBall R := by
  apply closure_minimal _ (upperClosedBall_closed R)
  intro z hz
  exact ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩

theorem oddUpper_conj {u : ℂ → ℝ} (hzero : ∀ z, z.im = 0 → u z = 0)
    (z : ℂ) : oddUpper u (conj z) = -oddUpper u z := by
  dsimp [oddUpper]
  rw [Complex.conj_conj]
  change (if 0 ≤ -z.im then u (conj z) else -u z) = -(if 0 ≤ z.im then u z else -u (conj z))
  by_cases hz : z.im = 0
  · have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
    simp [hz, hc, hzero z hz]
  · by_cases hh : 0 ≤ z.im
    · have hn : ¬ 0 ≤ -z.im := fun he => hz (by linarith)
      rw [ite_eq_right hn, ite_eq_left hh]
    · rw [ite_eq_left (show 0 ≤ -z.im by linarith), ite_eq_right hh, neg_neg]

theorem harmonic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (upperBall R))
    (huc : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    EqOn (fun z => (herglotzExtension R (oddUpper u) z).re) u (upperBall R) := by
  let v := oddUpper u
  have hvc : ContinuousOn v (sphere 0 R) := oddUpper_continuous_circle huc hzero
  let w := poissonClosed R v
  have hwc := poissonClosed_continuous hR hvc
  have he : EqOn w (poissonExtension R v) (ball 0 R) := by
    intro z hz
    simp [w, poissonClosed, hz]
  have hwh : HarmonicOnNhd w (ball 0 R) := by
    intro z hz
    rw [harmonicAt_congr_nhds (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz))]
    exact poisson_harmonic hR.le hvc z hz
  have hdiff : HarmonicContOnCl (u - w) (upperBall R) := by
    refine ⟨hu.sub (hwh.mono inter_subset_left), ?_⟩
    exact (huc.mono (closure_upperBall_subset R)).sub
      (hwc.mono ((closure_upperBall_subset R).trans inter_subset_left))
  have hbound : EqOn (u - w) 0 (frontier (upperBall R)) := by
    intro z hz
    have hzK := closure_upperBall_subset R hz.1
    have hn : z ∉ upperBall R := by
      simpa only [(upperBall_open R).interior_eq] using hz.2
    by_cases hzB : z ∈ ball 0 R
    · have hz0 : z.im = 0 := le_antisymm (le_of_not_gt (fun hi => hn ⟨hzB, hi⟩)) hzK.2
      have hw0 : w z = 0 := by
        rw [he hzB]
        exact poisson_real_zero (oddUpper_conj hzero) hz0
      simp [hzero z hz0, hw0]
    · have hi : 0 ≤ z.im := hzK.2
      simp [w, poissonClosed, hzB, v, oddUpper, hi]
  have hb : Bornology.IsBounded (upperBall R) := isBounded_ball.subset inter_subset_left
  have hlo := harmonic_le_boundary (upperBall_open R) hb hdiff (M := 0)
    (fun z hz => le_of_eq (hbound hz))
  have hhi := harmonic_le_boundary (upperBall_open R) hb hdiff.neg (M := 0)
    (fun z hz => by simp [hbound hz])
  intro z hz
  change (herglotzExtension R v z).re = u z
  rw [herglotz_re hR.le hvc hz.1, ← he hz.1]
  have ha := hlo z (subset_closure hz)
  have hb := hhi z (subset_closure hz)
  change u z - w z ≤ 0 at ha
  change -(u z - w z) ≤ 0 at hb
  linarith

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.harmonic_reflection := @_root_.OAI.DirectCrouzeix.Conformal.harmonic_reflection
