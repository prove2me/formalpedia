-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.poisson_boundary_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:50:43.223283+00:00
-- url     : https://prove2.me/submissions/b6aae26c-f5d2-4782-9c23-b172d4f05851

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean:L54-L148
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.poisson_boundary_limit. The node keeps its source
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

theorem poisson_continuous_circle {R : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    ContinuousOn (poissonKernel 0 z) (sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere hz)

theorem poisson_nonnegative_circle {R : ℝ} {z ζ : ℂ}
    (hz : z ∈ ball 0 R) (hζ : ζ ∈ sphere 0 R) : 0 ≤ poissonKernel 0 z ζ := by
  have hz' := mem_ball_zero_iff.mp hz
  have hζ' : ‖ζ‖ = R := by simpa using hζ
  dsimp [poissonKernel]
  simp only [sub_zero]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z]

theorem poisson_average_one {R : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    Real.circleAverage (poissonKernel 0 z) 0 R = 1 := by
  simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul, mul_one] using (harmonicContOnCl_const (c := (1 : ℝ))
    (s := ball 0 R)).circleAverage_poissonKernel_smul hz

theorem poisson_boundary_limit {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {p : ℂ} (hp : p ∈ sphere 0 R) :
    Tendsto (poissonExtension R u) (𝓝[ball 0 R] p) (𝓝 (u p)) := by
  have hp' : ‖p‖ = R := by simpa using hp
  have huabs : ContinuousOn (fun ζ => |u ζ - u p|) (sphere 0 R) :=
    (hu.sub continuousOn_const).abs
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn huabs
  have hM0 : 0 ≤ M := (norm_nonneg (|u p - u p|)).trans (hM p hp)
  have hbound : ∀ ζ ∈ sphere 0 R, |u ζ - u p| ≤ M := by
    intro ζ hζ
    simpa only [Real.norm_eq_abs, abs_abs] using hM ζ hζ
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hu p hp) (ε / 2) (half_pos hε)
  let C := 4 * M / δ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnear : ∀ᶠ z in 𝓝[ball 0 R] p, dist z p < δ / 2 :=
    (show ∀ᶠ z in 𝓝 p, dist z p < δ / 2 from ball_mem_nhds p (half_pos hδ)).filter_mono nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z in 𝓝[ball 0 R] p, C * (R ^ 2 - ‖z‖ ^ 2) < ε / 2 := by
    have ht : Tendsto (fun z : ℂ => C * (R ^ 2 - ‖z‖ ^ 2)) (𝓝 p) (𝓝 0) := by
      simpa only [hp', sub_self, mul_zero] using
        ((show Continuous (fun z : ℂ => C * (R ^ 2 - ‖z‖ ^ 2)) from by fun_prop).tendsto p)
    exact (ht.eventually (gt_mem_nhds (half_pos hε))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, hsmall, self_mem_nhdsWithin] with z hz hzs hzU
  have hP : ContinuousOn (poissonKernel 0 z) (sphere 0 R) := by
    simpa only [abs_of_pos hR] using poisson_continuous_circle hzU
  have hn (ζ : ℂ) (hζ : ζ ∈ sphere 0 R) := poisson_nonnegative_circle hzU hζ
  have hL : 0 ≤ R ^ 2 - ‖z‖ ^ 2 := by
    have hh := mem_ball_zero_iff.mp hzU
    nlinarith [norm_nonneg z]
  have hest : ∀ ζ ∈ sphere 0 R,
      poissonKernel 0 z ζ * |u ζ - u p| ≤
        poissonKernel 0 z ζ * (ε / 2) + C * (R ^ 2 - ‖z‖ ^ 2) := by
    intro ζ hζ
    by_cases hclose : dist ζ p < δ
    · have hd' : |u ζ - u p| < ε / 2 := by
        simpa only [Real.dist_eq] using hd hζ hclose
      have hh := mul_le_mul_of_nonneg_left hd'.le (hn ζ hζ)
      have hh' : 0 ≤ C * (R ^ 2 - ‖z‖ ^ 2) := mul_nonneg hC hL
      linarith
    · have hζnorm : ‖ζ‖ = R := by simpa using hζ
      have hdist : δ / 2 ≤ ‖ζ - z‖ := by
        have hh := dist_triangle ζ z p
        rw [dist_eq_norm ζ z] at hh
        linarith [le_of_not_gt hclose]
      have hden : 0 < ‖ζ - z‖ ^ 2 := sq_pos_of_pos ((half_pos hδ).trans_le hdist)
      have hpk : poissonKernel 0 z ζ ≤ 4 * (R ^ 2 - ‖z‖ ^ 2) / δ ^ 2 := by
        dsimp [poissonKernel]
        simp only [sub_zero, hζnorm]
        rw [div_le_div_iff₀ hden (sq_pos_of_pos hδ)]
        have hden' : δ ^ 2 ≤ 4 * ‖ζ - z‖ ^ 2 := by nlinarith
        nlinarith [mul_nonneg hL (sub_nonneg.mpr hden')]
      have hh := mul_le_mul (hbound ζ hζ) hpk (hn ζ hζ) hM0
      have hright : 0 ≤ poissonKernel 0 z ζ * (ε / 2) := mul_nonneg (hn ζ hζ) (half_pos hε).le
      dsimp [C]
      have halg : M * (4 * (R ^ 2 - ‖z‖ ^ 2) / δ ^ 2) =
          4 * M / δ ^ 2 * (R ^ 2 - ‖z‖ ^ 2) := by ring
      rw [mul_comm |u ζ - u p|, halg] at hh
      linarith
  have hi : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * (u ζ - u p)) 0 R :=
    (hP.mul (hu.sub continuousOn_const)).circleIntegrable hR.le
  have heq : poissonExtension R u z - u p =
      Real.circleAverage (fun ζ => poissonKernel 0 z ζ * (u ζ - u p)) 0 R := by
    dsimp [poissonExtension]
    have ht := Real.circleAverage_fun_sub
      (f₁ := fun ζ => poissonKernel 0 z ζ * u ζ)
      (f₂ := fun ζ => poissonKernel 0 z ζ * u p)
      ((hP.mul hu).circleIntegrable hR.le)
      ((hP.mul_const (u p)).circleIntegrable hR.le)
    simp_rw [mul_sub]
    rw [ht]
    congr 1
    simp_rw [mul_comm _ (u p), ← smul_eq_mul]
    rw [Real.circleAverage_fun_smul, poisson_average_one hzU, smul_eq_mul, mul_one]
  rw [Real.dist_eq, heq]
  calc
    |Real.circleAverage (fun ζ => poissonKernel 0 z ζ * (u ζ - u p)) 0 R|
        ≤ Real.circleAverage (fun ζ => |poissonKernel 0 z ζ * (u ζ - u p)|) 0 R :=
      Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage
        (fun ζ => poissonKernel 0 z ζ * (ε / 2) + C * (R ^ 2 - ‖z‖ ^ 2)) 0 R := by
      apply Real.circleAverage_mono hi.abs
        (((hP.mul_const (ε / 2)).add_const _).circleIntegrable hR.le)
      intro ζ hζ
      have hζ' : ζ ∈ sphere 0 R := by simpa only [abs_of_pos hR] using hζ
      change |poissonKernel 0 z ζ * (u ζ - u p)| ≤ _
      rw [abs_mul, abs_of_nonneg (hn ζ hζ')]
      exact hest ζ hζ'
    _ = ε / 2 + C * (R ^ 2 - ‖z‖ ^ 2) := by
      rw [Real.circleAverage_fun_add ((hP.mul_const (ε / 2)).circleIntegrable hR.le)
        (by exact continuousOn_const.circleIntegrable hR.le), Real.circleAverage_const]
      congr 1
      simp_rw [mul_comm _ (ε / 2), ← smul_eq_mul]
      rw [Real.circleAverage_fun_smul, poisson_average_one hzU, smul_eq_mul, mul_one]
    _ < ε := by linarith

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.poisson_boundary_limit := @_root_.OAI.DirectCrouzeix.Conformal.poisson_boundary_limit
