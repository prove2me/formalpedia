-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.holomorphic_reflection_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:00:25.154844+00:00
-- url     : https://prove2.me/submissions/bf7fe6da-ff38-4734-90d2-133a64d0c719

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean:L141-L261
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.holomorphic_reflection_modulus. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_harmonic_reflection
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_herglotz_deriv_im_pos
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_oddUpper_continuous_circle

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

theorem upperBall_open (R : ℝ) : IsOpen (upperBall R) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

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

end Conformal

end DirectCrouzeix

end

end

end

end OAI

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

theorem logModulusUpper_real {f : ℂ → ℂ} {z : ℂ} (hz : z.im = 0) :
    logModulusUpper f z = 0 := by simp [logModulusUpper, hz]

theorem logModulusUpper_continuous {R : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ContinuousOn (logModulusUpper f) (upperClosedBall R) := by
  unfold logModulusUpper
  apply ContinuousOn.if'
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    have ht : Tendsto (fun w => Real.log ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp (hl z hz.1.1 hz0)
    exact ht.mono_left (nhdsWithin_mono _ inter_subset_right)
  · intro z hz
    have hf := Complex.continuous_im.frontier_preimage_subset (Ioi (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hf
    simp only [hz0, lt_self_iff_false, ↓reduceIte]
    exact tendsto_const_nhds
  · apply (hc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hn z hz))).mono
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  · exact continuousOn_const

theorem upperBall_convex (R : ℝ) : Convex ℝ (upperBall R) :=
  (convex_ball (0 : ℂ) R).inter (convex_Ioi (0 : ℝ) |>.linear_preimage Complex.imCLM.toLinearMap)

theorem upperBall_half_radius {R : ℝ} (hR : 0 < R) :
    ((R / 2 : ℝ) : ℂ) * Complex.I ∈ upperBall R := by
  constructor
  · simp only [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hR)]
    linarith
  · simpa using half_pos hR

theorem holomorphic_reflection_modulus {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hb : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, ‖f z‖ < 1)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 R) ∧ EqOn F f (upperBall R) ∧
      (∀ z ∈ ball 0 R, z.im = 0 → ‖F z‖ = 1) ∧ deriv F 0 ≠ 0 ∧
      (∀ z ∈ ball 0 R, ‖F z‖ < 1 ↔ 0 < z.im) := by
  let u := logModulusUpper f
  let v := oddUpper u
  let H := herglotzExtension R v
  have hu0 : ∀ z, z.im = 0 → u z = 0 := fun _ hz => logModulusUpper_real hz
  have huc := logModulusUpper_continuous hf.continuousOn hn hl
  have hvc : ContinuousOn v (sphere 0 R) := oddUpper_continuous_circle huc hu0
  have hH : AnalyticOnNhd ℂ H (ball 0 R) := herglotz_analytic hR.le hvc
  have hu : HarmonicOnNhd u (upperBall R) := by
    intro z hz
    have hzK : z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨ball_subset_closedBall hz.1, hz.2⟩
    have he : u =ᶠ[𝓝 z] (fun w => Real.log ‖f w‖) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz.2] with w hw
      simp only [u, logModulusUpper, hw, ↓reduceIte]
    rw [harmonicAt_congr_nhds he]
    exact (hf z hzK).harmonicAt_log_norm (hn z hzK)
  have hRe := harmonic_reflection hR hu huc hu0
  let k := fun z => f z * Complex.exp (-H z)
  have hk : DifferentiableOn ℂ k (upperBall R) := by
    apply (hf.differentiableOn.mono (by intro z hz; exact ⟨ball_subset_closedBall hz.1, hz.2⟩)).mul
    exact (hH.differentiableOn.mono inter_subset_left).neg.cexp
  have hkn : ∀ z ∈ upperBall R, ‖k z‖ = 1 := by
    intro z hz
    have hRe' : (H z).re = Real.log ‖f z‖ := by
      have hh : (H z).re = u z := hRe hz
      simpa only [u, logModulusUpper, ite_eq_left (show 0 < z.im from hz.2)] using hh
    have hnz := hn z ⟨ball_subset_closedBall hz.1, hz.2⟩
    dsimp [k]
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hRe', Real.exp_neg,
      Real.exp_log (norm_pos_iff.mpr hnz), mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnz)]
  let c : ℂ := ((R / 2 : ℝ) : ℂ) * Complex.I
  have hc : c ∈ upperBall R := upperBall_half_radius hR
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (upperBall_convex R).isPreconnected (upperBall_open R) hk hc
    (show IsMaxOn (norm ∘ k) (upperBall R) c from
      fun z hz => by
        change ‖k z‖ ≤ ‖k c‖
        rw [hkn z hz, hkn c hc])
  refine ⟨fun z => k c * Complex.exp (H z), analyticOnNhd_const.mul hH.cexp, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh : k z = k c := hconst hz
    rw [← hh]
    simp [k, Complex.exp_neg, Complex.exp_ne_zero]
  · intro z hz hz0
    have hHz : (H z).re = 0 := by
      rw [show H z = herglotzExtension R v z from rfl, herglotz_re hR.le hvc hz]
      exact poisson_real_zero (oddUpper_conj hu0) hz0
    rw [norm_mul, hkn c hc, Complex.norm_exp, hHz, Real.exp_zero, mul_one]
  · have hvsign : ∀ z ∈ sphere 0 R, v z * z.im ≤ 0 := by
      intro z hz
      by_cases hi : 0 ≤ z.im
      · by_cases hi0 : z.im = 0
        · simp [hi0]
        · have hip : 0 < z.im := lt_of_le_of_ne hi (Ne.symm hi0)
          have hzK : z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨sphere_subset_closedBall hz, hip⟩
          have huNeg : u z < 0 := by
            simpa only [u, logModulusUpper, ite_eq_left hip] using
              Real.log_neg (norm_pos_iff.mpr (hn z hzK)) (hb z hzK)
          simpa only [v, oddUpper, ite_eq_left hi] using mul_nonpos_of_nonpos_of_nonneg huNeg.le hi
      · have hip : 0 < (conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr (lt_of_not_ge hi)
        have hzK : conj z ∈ closedBall 0 R ∩ {z | 0 < z.im} :=
          ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using sphere_subset_closedBall hz, hip⟩
        have huNeg : u (conj z) < 0 := by
          simpa only [u, logModulusUpper, ite_eq_left hip] using
            Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
        simpa only [v, oddUpper, ite_eq_right hi] using
          mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr huNeg.le) (le_of_not_ge hi)
    have hvpole : v ((R : ℂ) * Complex.I) < 0 := by
      have hip : 0 < ((R : ℂ) * Complex.I).im := by simpa using hR
      have hzK : (R : ℂ) * Complex.I ∈ closedBall 0 R ∩ {z | 0 < z.im} :=
        ⟨by simp [mem_closedBall, abs_of_pos hR], hip⟩
      simpa only [v, oddUpper, ite_eq_left hip.le, u, logModulusUpper, ite_eq_left hip] using
        Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
    have hdpos : 0 < (deriv H 0).im := herglotz_deriv_im_pos hR hvc hvsign hvpole
    have hdne : deriv H 0 ≠ 0 := by intro he; simp [he] at hdpos
    have hkc : k c ≠ 0 := by intro he; simpa [he] using hkn c hc
    have hderF := ((hH 0 (mem_ball_self hR)).differentiableAt.hasDerivAt.cexp).const_mul (k c)
    rw [hderF.deriv]
    exact mul_ne_zero hkc (mul_ne_zero (Complex.exp_ne_zero _) hdne)
  · intro z hz
    change ‖k c * Complex.exp (H z)‖ < 1 ↔ 0 < z.im
    by_cases hi : 0 < z.im
    · have hh : k z = k c := hconst ⟨hz, hi⟩
      have he : k c * Complex.exp (H z) = f z := by
        rw [← hh]
        simp [k, Complex.exp_neg, Complex.exp_ne_zero]
      rw [he]
      exact iff_of_true (hb z ⟨ball_subset_closedBall hz, hi⟩) hi
    · by_cases hi0 : z.im = 0
      · have hHz : (H z).re = 0 := by
          rw [show H z = herglotzExtension R v z from rfl, herglotz_re hR.le hvc hz]
          exact poisson_real_zero (oddUpper_conj hu0) hi0
        simp only [norm_mul, hkn c hc, Complex.norm_exp, hHz, Real.exp_zero, mul_one,
          lt_self_iff_false, hi0]
      · have hic : 0 < (conj z).im := by
          simpa only [Complex.conj_im] using
            (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hi) hi0))
        have hzcb : conj z ∈ ball 0 R := by simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
        have hzK : conj z ∈ closedBall 0 R ∩ {z | 0 < z.im} := ⟨ball_subset_closedBall hzcb, hic⟩
        have hRc : (H (conj z)).re = Real.log ‖f (conj z)‖ := by
          have hh : (H (conj z)).re = u (conj z) := hRe ⟨hzcb, hic⟩
          simpa only [u, logModulusUpper, ite_eq_left hic] using hh
        have ho : (H (conj z)).re = -(H z).re := by
          change (herglotzExtension R v (conj z)).re = -(herglotzExtension R v z).re
          rw [herglotz_re hR.le hvc hzcb, herglotz_re hR.le hvc hz]
          exact poisson_odd (oddUpper_conj hu0) z
        have hpos : 0 < (H z).re := by
          have hnlog := Real.log_neg (norm_pos_iff.mpr (hn _ hzK)) (hb _ hzK)
          linarith
        have hlarge : 1 < ‖k c * Complex.exp (H z)‖ := by
          rw [norm_mul, hkn c hc, one_mul, Complex.norm_exp]
          exact Real.one_lt_exp_iff.mpr hpos
        exact iff_of_false (not_lt_of_ge hlarge.le) hi

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.holomorphic_reflection_modulus := @_root_.OAI.DirectCrouzeix.Conformal.holomorphic_reflection_modulus
