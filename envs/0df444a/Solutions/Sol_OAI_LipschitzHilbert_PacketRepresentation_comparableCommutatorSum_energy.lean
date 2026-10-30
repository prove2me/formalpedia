-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorSum_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:01:49.215988+00:00
-- url     : https://prove2.me/submissions/d433c9d1-1af9-4631-8b61-b04141857b76

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_dyadic_smooth_product_embedding

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteEnergySchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted energy summation for the smooth/dyadic comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_sum_norm_square {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    ‖∑ j, v j‖ ^ 2 ≤ (∑ j, w j) * ∑ j, ‖v j‖ ^ 2 / w j := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := w) (g := fun j => ‖v j‖ ^ 2 / w j) (r := fun j => ‖v j‖)
    (fun j _ => (hw j).le) (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
    (fun j _ => by rw [mul_div_cancel₀ _ (hw j).ne'])
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

theorem weighted_integral_sum_square {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] (μ : Measure Ω)
    (F : ι → Ω → E) (hF : ∀ j, MemLp (F j) 2 μ)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    (∫ x, ‖∑ j, F j x‖ ^ 2 ∂μ) ≤
      (∑ j, w j) * ∑ j, (∫ x, ‖F j x‖ ^ 2 ∂μ) / w j := by
  have hsum : MemLp (fun x => ∑ j, F j x) 2 μ := by
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun j _ => hF j)
  have hint (j : ι) : Integrable (fun x => ‖F j x‖ ^ 2 / w j) μ :=
    ((hF j).integrable_norm_pow (by decide : 2 ≠ 0)).div_const _
  calc
    _ ≤ ∫ x, (∑ j, w j) * ∑ j, ‖F j x‖ ^ 2 / w j ∂μ :=
      integral_mono (hsum.integrable_norm_pow (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun j _ => hint j)).const_mul _)
        (fun x => weighted_sum_norm_square (fun j => F j x) w hw)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact integral_div _ _

theorem finite_energy_schur {Ω ι κ E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [NormedAddCommGroup E]
    (μ : Measure Ω) (F : ι → κ → Ω → E)
    (hF : ∀ i j, MemLp (F i j) 2 μ) (a : ι → κ → ℝ)
    (ha : ∀ i j, 0 < a i j) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, a i j ≤ R) (hcol : ∀ j, ∑ i, a i j ≤ C)
    (hbound : ∀ i j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) ≤ a i j ^ 2 * b j) :
    (∑ i, ∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤ R * C * ∑ j, b j := by
  have hcell (i : ι) (j : κ) :
      (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j ≤ a i j * b j := by
    apply (div_le_iff₀ (ha i j)).mpr
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hbound i j
  have hrowbound (i : ι) : (∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤
      R * ∑ j, a i j * b j := by
    calc
      _ ≤ (∑ j, a i j) * ∑ j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j :=
        weighted_integral_sum_square μ (F i) (hF i) (a i) (ha i)
      _ ≤ (∑ j, a i j) * ∑ j, a i j * b j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hcell i j))
          (Finset.sum_nonneg (fun j _ => (ha i j).le))
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (ha i j).le (hb j)))
  calc
    _ ≤ ∑ i, R * ∑ j, a i j * b j := Finset.sum_le_sum (fun i _ => hrowbound i)
    _ = R * ∑ j, (∑ i, a i j) * b j := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, C * b j := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hb j))) hR
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricScaleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row and column bounds for the actual geometric scale kernel. -/

open scoped BigOperators

noncomputable section

namespace LipschitzHilbert

theorem sum_half_powers_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have heq : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first absolute moment of the retained time kernel is bounded
by twice the largest scale, independently of the number of scales. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_first_absolute_moment_integrable (k : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => |t| *‖k t‖) := by
  simpa only [pow_one,Real.norm_eq_abs] using k.integrable_pow_mul volume 1

theorem scaledTimeKernel_moment1_pointwise (k : ℝ → ℂ) (l t : ℝ) (hl : 0<l) :
    |t| *‖scaledTimeKernel k l t‖=|t/l| *‖k (t/l)‖ := by
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hl.le,abs_div,abs_of_pos hl]
  ring

theorem scaledTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    (∫ t, |t| *‖scaledTimeKernel k l t‖)=l*(∫ t, |t| *‖k t‖) := by
  simp_rw [scaledTimeKernel_moment1_pointwise k l _ hl]
  rw [Measure.integral_comp_div (fun t => |t| *‖k t‖) l,abs_of_pos hl,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularCutoffConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit real annular cutoffs and the low-pass difference underlying
the geometric frequency partition. All supports stay inside fixed bands. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_one (s : ℝ) (hs : |s|≤1) : reassemblyLow s=1 := by
  have hd : s∈Metric.closedBall (0:ℝ) reassemblyLowBump.rIn := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_zero (s : ℝ) (hs : 13/12≤|s|) : reassemblyLow s=0 := by
  have hd : reassemblyLowBump.rOut≤dist s 0 := by
    simpa only [Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.zero_of_le_dist hd,Complex.ofReal_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSquareBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric annular cutoffs have a uniform finite square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_norm (s : ℝ) : ‖reassemblyLow s‖≤1 := by
  rw [reassemblyLow_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg reassemblyLowBump.nonneg]
  exact reassemblyLowBump.le_one

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicSmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine binary low-pass difference for the dyadic commutator
proof, with its scale-independent Fourier square bound. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicDifference_small (x : ℝ) (hx : |x|≤1) : dyadicDifference x=0 := by
  have hh : |x/2|≤1 := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_one x hx,reassemblyLow_one _ hh,sub_self]

theorem dyadicDifference_large (x : ℝ) (hx : 13/6≤|x|) : dyadicDifference x=0 := by
  have hh : 13/12≤|x/2| := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_zero x (by linarith),
    reassemblyLow_zero _ hh,sub_self]

theorem dyadicDifference_norm (x : ℝ) : ‖dyadicDifference x‖≤2 := by
  rw [dyadicDifference_apply]
  exact (norm_sub_le _ _).trans (by linarith [reassemblyLow_norm (x/2),reassemblyLow_norm x])

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineFrequencyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth frequency projections on the line and their finite
square-function bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_fourier (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (lineSchwartzProjection q W hW f)) eta=q (W*eta)*(𝓕 f) eta := by
  simp only [lineSchwartzProjection,FourierTransform.fourier_fourierInv_eq]
  rw [SchwartzMap.smulLeftCLM_apply_apply (dilatedSlopeWindow q W hW).hasTemperateGrowth,
    dilatedSlopeWindow_apply,smul_eq_mul]

theorem lineSchwartzProjection_energy (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW f x‖^2)≤M^2*∫ x, ‖f x‖^2 := by
  rw [←SchwartzMap.integral_norm_sq_fourier (lineSchwartzProjection q W hW f),
    ←SchwartzMap.integral_norm_sq_fourier f,←integral_const_mul]
  apply integral_mono
  · exact ((𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  · exact (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul _
  · intro x
    change ‖(𝓕 (lineSchwartzProjection q W hW f)) x‖^2≤M^2*‖(𝓕 f) x‖^2
    rw [lineSchwartzProjection_fourier,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM (W*x)) 2) (sq_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line Fourier projection is the actual convolution with its
inverse-Fourier kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_eq_convolution (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzProjection q W hW f x=lineConvolution (lineProjectionKernel q W hW) f x := by
  have he : lineSchwartzProjection q W hW f=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext eta
    change (𝓕 (lineSchwartzProjection q W hW f)) eta=
      (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f)) eta
    rw [lineSchwartzProjection_fourier,SchwartzMap.fourier_convolution]
    simp only [SchwartzMap.pairing_apply_apply,lineProjectionKernel,
      FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,ContinuousLinearMap.mul_apply']
  rw [he,SchwartzMap.convolution_apply,convolution_def]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual line projection kernel has the expected physical scale,
including its exact first absolute moment. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_moment1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, |t| *‖lineProjectionKernel q W hW.ne' t‖)=
      W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have he (t : ℝ) : lineProjectionKernel q W hW.ne' t=
      scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W t := by
    rw [lineProjectionKernel_eq_scaled]
    exact scaledSchwartzKernel_apply q W hW t
  simp_rw [he]
  exact scaledTimeKernel_moment1 (𝓕⁻ q) W hW

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact kernel mass, cancellation, and uniform Lipschitz approximation
for the actual line projections. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_integral (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    (∫ t, lineProjectionKernel q W hW t)=q 0 := by
  have he : (𝓕 (lineProjectionKernel q W hW) : SchwartzMap ℝ ℂ) 0=q 0 := by
    simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,mul_zero]
  rw [SchwartzMap.fourier_coe,Real.fourier_eq] at he
  simpa only [inner_zero_right,neg_zero,Real.fourierChar.map_zero_eq_one,one_smul] using he

theorem lineConvolution_centered_bound (K : SchwartzMap ℝ ℂ) (b : ℝ → ℂ)
    (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution K b x-(∫ t, K t)*b x‖≤L*(∫ t, |t| *‖K t‖) := by
  have h1 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb x
  have he : lineConvolution K b x-(∫ t, K t)*b x=
      ∫ t, K t*(b (x-t)-b x) := by
    simp_rw [mul_sub]
    rw [integral_sub h1 (K.integrable.mul_const (b x)),integral_mul_const]
    rfl
  rw [he]
  have hn := norm_integral_le_of_norm_le
    ((schwartz_first_absolute_moment_integrable K).const_mul L)
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b (x-t)-b x)‖≤L*(|t| *‖K t‖) from by
      rw [norm_mul]
      have hh := hLip (x-t) x
      simp only [sub_sub_cancel_left,abs_neg] at hh
      calc
        _ ≤ ‖K t‖*(L*|t|) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by ring))
  simpa only [integral_const_mul] using hn

theorem lineProjection_centered_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') b x-q 0*b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineConvolution_centered_bound (lineProjectionKernel q W hW.ne') b hbm B hb L hLip x
  rw [lineProjectionKernel_integral,lineProjectionKernel_moment1 q W hW] at hh
  simpa only [mul_assoc] using hh

theorem dyadicProjection_lipschitz_bound (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel dyadicDifference W hW.ne') b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineProjection_centered_bound dyadicDifference W hW b hbm B hb L hLip x
  simpa only [dyadicDifference_small 0 (by norm_num),zero_mul,sub_zero] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierKernelFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative first absolute moment from the zeroth and third
L1 derivatives of a Schwartz multiplier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem fourier_schwartzDerivative (r : ℕ) (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (schwartzDerivative r q)) x=
      ((2*Real.pi*Complex.I*(x:ℂ))^r)*(𝓕 q) x := by
  induction r with
  | zero => simp only [schwartzDerivative,pow_zero,one_mul]
  | succ r ih =>
    have hd := congrFun (Real.fourier_deriv (schwartzDerivative r q).integrable
      (schwartzDerivative r q).differentiable
      (SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q)).integrable) x
    change (𝓕 (SchwartzMap.derivCLM ℂ ℂ (schwartzDerivative r q))) x=
      (2*Real.pi*Complex.I*(x:ℂ))* (𝓕 (schwartzDerivative r q)) x at hd
    rw [schwartzDerivative,hd,ih]
    ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded line convolutions have finite local square energy. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    ‖lineConvolution K f x‖≤(∫ t, ‖K t‖)*B := by
  have h := norm_integral_le_of_norm_le (hK.norm.mul_const B)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (x-t)‖≤‖K t‖*B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [lineConvolution,integral_mul_const] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProductSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier spectrum of an actual Schwartz product, including the
ball and annulus bounds needed in the dyadic commutator decomposition. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_fourier_twice (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) x=f (-x) := by
  have he : (𝓕⁻ (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=f := FourierTransform.fourierInv_fourier_eq f
  have hh := congrArg (fun g : SchwartzMap ℝ ℂ => g (-x)) he
  change (𝓕 (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (-(-x))=f (-x) at hh
  simpa only [neg_neg] using hh

theorem lineSchwartzProduct_fourier (f g : SchwartzMap ℝ ℂ) :
    (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ)=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).symm.injective
  change 𝓕⁻ (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ)=
    𝓕⁻ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g))
  rw [FourierTransform.fourierInv_fourier_eq]
  ext x
  change lineSchwartzProduct f g x=
    (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) : SchwartzMap ℝ ℂ) (-x)
  rw [SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',schwartz_fourier_twice,
    neg_neg,lineSchwartzProduct_apply]

theorem lineSchwartzProduct_fourier_zero (f g : SchwartzMap ℝ ℂ) (eta : ℝ)
    (h : ∀ t, (𝓕 f : SchwartzMap ℝ ℂ) t=0 ∨ (𝓕 g : SchwartzMap ℝ ℂ) (eta-t)=0) :
    (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta=0 := by
  rw [lineSchwartzProduct_fourier,SchwartzMap.convolution_apply,convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  change (𝓕 f : SchwartzMap ℝ ℂ) t*(𝓕 g : SchwartzMap ℝ ℂ) (eta-t)=0
  exact (h t).elim (fun hf => by rw [hf,zero_mul]) (fun hg => by rw [hg,mul_zero])

theorem lineSchwartzProduct_band (f g : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hf : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A)
    (hg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B) :
    ∀ eta, (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A+B := by
  intro eta heta
  by_contra hn
  apply heta
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : (𝓕 f : SchwartzMap ℝ ℂ) t=0
  · exact Or.inl ht
  · right
    by_contra hs
    have htri : |eta|≤|t|+|eta-t| := by simpa only [add_sub_cancel] using abs_add_le t (eta-t)
    exact hn (htri.trans (add_le_add (hf t ht) (hg (eta-t) hs)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral separation of the low/high dyadic interaction,
and its exact localization by the fixed commutator cutoff. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicProjection_frequency (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (eta : ℝ) (heta : (𝓕 (lineSchwartzProjection dyadicDifference W hW.ne' f)) eta≠0) :
    1/W≤|eta| ∧ |eta|≤(13/6)/W := by
  have hn : dyadicDifference (W*eta)≠0 := by
    intro hz
    exact heta (by rw [lineSchwartzProjection_fourier,hz,zero_mul])
  have hlo : 1 < |W*eta| := lt_of_not_ge (fun hh => hn (dyadicDifference_small _ hh))
  have hhi : |W*eta|<13/6 := lt_of_not_ge (fun hh => hn (dyadicDifference_large _ hh))
  rw [abs_mul,abs_of_pos hW] at hlo hhi
  exact ⟨(div_le_iff₀ hW).mpr (by linarith), (le_div_iff₀ hW).mpr (by linarith)⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation commutes with the actual smooth line projections,
and a compact Fourier band gives the required Bernstein energy bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_derivative (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (lineSchwartzProjection q W hW f)=
      lineSchwartzProjection q W hW (schwartzDerivative 1 f) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (schwartzDerivative 1 (lineSchwartzProjection q W hW f))) eta=
    (𝓕 (lineSchwartzProjection q W hW (schwartzDerivative 1 f))) eta
  rw [fourier_schwartzDerivative,lineSchwartzProjection_fourier,
    lineSchwartzProjection_fourier,fourier_schwartzDerivative]
  ring

theorem line_bernstein_energy (f : SchwartzMap ℝ ℂ) (R : ℝ)
    (hband : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤R) :
    (∫ x, ‖schwartzDerivative 1 f x‖^2)≤(2*Real.pi*R)^2*(∫ x, ‖f x‖^2) := by
  have hi (g : SchwartzMap ℝ ℂ) : Integrable (fun eta => ‖(𝓕 g : SchwartzMap ℝ ℂ) eta‖^2) :=
    ((𝓕 g : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hp (eta : ℝ) : ‖(𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta‖^2≤
      (2*Real.pi*R)^2*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2 := by
    rw [fourier_schwartzDerivative 1 f eta,pow_one,norm_mul]
    by_cases hf : (𝓕 f : SchwartzMap ℝ ℂ) eta=0
    · simp only [hf,norm_zero,mul_zero,zero_pow (by decide : 2≠0),le_refl]
    · have hc : ‖(2*Real.pi*Complex.I*(eta:ℂ))‖=2*Real.pi*|eta| := by
        simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
      rw [hc,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hband eta hf) (by positivity)) 2
  calc
    _ = ∫ eta, ‖(𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta‖^2 := (SchwartzMap.integral_norm_sq_fourier (schwartzDerivative 1 f)).symm
    _ ≤ ∫ eta, (2*Real.pi*R)^2*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2 := integral_mono (hi _) ((hi f).const_mul _) hp
    _ = _ := by rw [integral_const_mul,SchwartzMap.integral_norm_sq_fourier f]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed zeroth and second decay bounds for the scaled line kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineKernelDecayConstant_nonneg (q : SchwartzMap ℝ ℂ) : 0≤lineKernelDecayConstant q :=
  add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

theorem lineKernelDecay_base (q : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖≤lineKernelDecayConstant q ∧
    |t|^2*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖≤lineKernelDecayConstant q := by
  constructor
  · exact ((𝓕⁻ q : SchwartzMap ℝ ℂ).norm_le_seminorm ℝ t).trans
      (le_add_of_nonneg_right (apply_nonneg _ _))
  · have h := (𝓕⁻ q : SchwartzMap ℝ ℂ).norm_pow_mul_le_seminorm ℝ 2 t
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_add_of_nonneg_left (apply_nonneg _ _))

theorem lineProjectionKernel_norm (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (t : ℝ) :
    ‖lineProjectionKernel q W hW.ne' t‖=W⁻¹*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) (t/W)‖ := by
  rw [lineProjectionKernel_eq_scaled q W hW,scaledSchwartzKernel_apply q W hW]
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hW.le]

theorem lineProjectionKernel_decay (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (t : ℝ) :
    ‖lineProjectionKernel q W hW.ne' t‖≤lineKernelDecayConstant q/W ∧
    |t|^2*‖lineProjectionKernel q W hW.ne' t‖≤lineKernelDecayConstant q*W := by
  rw [lineProjectionKernel_norm q W hW t]
  constructor
  · simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left
      (lineKernelDecay_base q (t/W)).1 (inv_nonneg.mpr hW.le)
  · have h := mul_le_mul_of_nonneg_right (lineKernelDecay_base q (t/W)).2 hW.le
    rw [abs_div,abs_of_pos hW] at h
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineHighLowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation of the high coefficient and Bernstein for the low input
give the actual high/low commutator its geometric scale factor. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_energy (b h : SchwartzMap ℝ ℂ) (B : ℝ)
    (hb : ∀ x, ‖b x‖≤B) :
    (∫ x, ‖lineSchwartzProduct b h x‖^2)≤B^2*(∫ x, ‖h x‖^2) := by
  rw [←integral_const_mul]
  apply integral_mono
    ((lineSchwartzProduct b h).memLp 2 volume |>.integrable_norm_pow (by decide : 2≠0))
    ((h.memLp 2 volume |>.integrable_norm_pow (by decide : 2≠0)).const_mul _)
  intro x
  simp only [lineSchwartzProduct_apply,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)

theorem lineSchwartzCommutator_bounded_energy (m b h : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hb : ∀ x, ‖b x‖≤B) :
    (∫ x, ‖lineSchwartzCommutator m b h x‖^2)≤4*A^2*B^2*(∫ x, ‖h x‖^2) := by
  let U := lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)
  let V := lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h)
  have hi (f : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖f x‖^2) :=
    (f.memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hp (x : ℝ) : ‖U x-V x‖^2≤2*‖U x‖^2+2*‖V x‖^2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (U x) (V x)) 2
    nlinarith [sq_nonneg (‖U x‖-‖V x‖)]
  have hu := (lineSchwartzProduct_energy b _ B hb).trans
    (mul_le_mul_of_nonneg_left (lineSchwartzProjection_energy m 1 (by norm_num) A hm h) (sq_nonneg B))
  have hv := (lineSchwartzProjection_energy m 1 (by norm_num) A hm _).trans
    (mul_le_mul_of_nonneg_left (lineSchwartzProduct_energy b h B hb) (sq_nonneg A))
  calc
    _ ≤ ∫ x, 2*‖U x‖^2+2*‖V x‖^2 :=
      integral_mono (hi _) (((hi U).const_mul 2).add ((hi V).const_mul 2)) hp
    _ = 2*(∫ x, ‖U x‖^2)+2*(∫ x, ‖V x‖^2) := by
      rw [integral_add ((hi U).const_mul 2) ((hi V).const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by dsimp [U,V] at *; nlinarith [hu,hv]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineHighLowSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A gap of five binary scales puts every high/low output in the
same fixed annulus as the high coefficient. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_frequency_of_nonzero (q f : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (eta : ℝ)
    (heta : (𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ) eta≠0) :
    (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 := by
  intro hz
  exact heta (by rw [lineSchwartzProjection_fourier,hz,mul_zero])

theorem schwartzDerivative_frequency_of_nonzero (f : SchwartzMap ℝ ℂ) (eta : ℝ)
    (heta : (𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta≠0) :
    (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 := by
  intro hz
  exact heta (by rw [fourier_schwartzDerivative,hz,mul_zero])

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCommutatorDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact differentiated commutator identity and its low-output
energy estimate, before the comparable-frequency summation. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzDerivative_one_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzDerivative 1 f x=deriv f x := rfl

theorem schwartzDerivative_product (f g : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (lineSchwartzProduct f g)=
      lineSchwartzProduct (schwartzDerivative 1 f) g+
        lineSchwartzProduct f (schwartzDerivative 1 g) := by
  ext x
  simp only [schwartzDerivative_one_apply,lineSchwartzProduct_apply,add_apply]
  change deriv (fun x => f x*g x) x=deriv f x*g x+f x*deriv g x
  exact deriv_mul f.differentiable.differentiableAt g.differentiable.differentiableAt

theorem lineSchwartzCommutator_derivative_identity (m b h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m b (schwartzDerivative 1 h)=
      schwartzDerivative 1 (lineSchwartzCommutator m b h)-
        lineSchwartzProduct (schwartzDerivative 1 b) (lineSchwartzProjection m 1 (by norm_num) h)+
        lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct (schwartzDerivative 1 b) h) := by
  have hlin (f g : SchwartzMap ℝ ℂ) : schwartzDerivative 1 (f-g)=
      schwartzDerivative 1 f-schwartzDerivative 1 g :=
    map_sub (SchwartzMap.derivCLM ℂ ℂ) f g
  have hproj (f g : SchwartzMap ℝ ℂ) : lineSchwartzProjection m 1 (by norm_num) (f+g)=
      lineSchwartzProjection m 1 (by norm_num) f+lineSchwartzProjection m 1 (by norm_num) g :=
    map_add (lineSchwartzProjectionLM m 1 (by norm_num)) f g
  simp only [lineSchwartzCommutator,hlin,schwartzDerivative_product,
    lineSchwartzProjection_derivative,hproj]
  abel

theorem lineSchwartzCommutator_ball (m b h : SchwartzMap ℝ ℂ) (B H : ℝ)
    (hb : ∀ eta, (𝓕 b : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B)
    (hh : ∀ eta, (𝓕 h : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤H) :
    ∀ eta, (𝓕 (lineSchwartzCommutator m b h) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B+H := by
  intro eta heta
  have ht : ∀ eta, (𝓕 (lineSchwartzProjection m 1 (by norm_num) h) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤H := by
    intro eta he
    exact hh eta (lineSchwartzProjection_frequency_of_nonzero m h 1 (by norm_num) eta he)
  have hu := lineSchwartzProduct_band b (lineSchwartzProjection m 1 (by norm_num) h) B H hb ht
  have hv := lineSchwartzProduct_band b h B H hb hh
  by_contra hn
  have hzero1 : (𝓕 (lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)) : SchwartzMap ℝ ℂ) eta=0 :=
    not_ne_iff.mp (fun hx => hn (hu eta hx))
  have hzero2 : (𝓕 (lineSchwartzProduct b h) : SchwartzMap ℝ ℂ) eta=0 :=
    not_ne_iff.mp (fun hx => hn (hv eta hx))
  apply heta
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
    (lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)-
      lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h))) eta=0
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,
    lineSchwartzProjection_fourier,hzero1,hzero2,mul_zero,sub_zero]

theorem projectedCommutator_derivative_energy (m b h : SchwartzMap ℝ ℂ)
    (W V A L : ℝ) (hW : 0<W) (hV : 0<V) (hm : ∀ eta, ‖m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    (∫ x, ‖lineSchwartzProjection dyadicDifference V hV.ne'
      (schwartzDerivative 1 (lineSchwartzCommutator m B h)) x‖^2)≤
      (A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (52*Real.pi/3)*(W/V))^2*(∫ x, ‖h x‖^2) := by
  intro B
  let M := ∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖
  let F := lineSchwartzCommutator m B h
  have hb (x : ℝ) : ‖B x‖≤L*W*M := by
    dsimp [B]
    rw [lineSchwartzProjection_eq_convolution]
    exact dyadicProjection_lipschitz_bound W hW b b.continuous.measurable
      (SchwartzMap.seminorm ℝ 0 0 b) (fun z => b.norm_le_seminorm ℝ z) L hLip x
  have hc := lineSchwartzCommutator_bounded_energy m B h A (L*W*M) hm hb
  have hp := lineSchwartzProjection_energy dyadicDifference V hV.ne' 2 dyadicDifference_norm F
  have hd := line_bernstein_energy (lineSchwartzProjection dyadicDifference V hV.ne' F) ((13/6)/V)
    (fun eta heta => (dyadicProjection_frequency V hV F eta heta).2)
  rw [←lineSchwartzProjection_derivative]
  calc
    _ ≤ (2*Real.pi*((13/6)/V))^2*(∫ x, ‖lineSchwartzProjection dyadicDifference V hV.ne' F x‖^2) := hd
    _ ≤ (2*Real.pi*((13/6)/V))^2*(2^2*(∫ x, ‖F x‖^2)) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ ≤ (2*Real.pi*((13/6)/V))^2*(2^2*(4*A^2*(L*W*M)^2*(∫ x, ‖h x‖^2))) := by
      gcongr
    _ = _ := by dsimp [M]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntGeometricSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric bound used on the two sides of a dyadic crossover. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem int_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    Summable (fun k : ℤ => r^k.natAbs) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  apply Summable.of_nat_of_neg
  · simpa only [Int.natAbs_natCast] using h
  · simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h

theorem int_geometric_tsum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    (∑' k : ℤ, r^k.natAbs)≤2/(1-r) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  have hnat : Summable (fun n : ℕ => r^(n:ℤ).natAbs) := by simpa only [Int.natAbs_natCast] using h
  have hneg : Summable (fun n : ℕ => r^(-n:ℤ).natAbs) := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h
  have heq : (∑' k : ℤ, r^k.natAbs)=(∑' n : ℕ, r^n)+(∑' n : ℕ, r^n)-1 := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_zero,pow_zero] using
      (hnat.tsum_of_nat_of_neg (f:=fun k : ℤ => r^k.natAbs) hneg)
  rw [heq,tsum_geometric_of_abs_lt_one (r:=r)
    (by simpa only [abs_of_nonneg hr] using hr1),div_eq_mul_inv]
  linarith

theorem int_geometric_shift_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, r^(k-a).natAbs)≤2/(1-r) := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), r^k.natAbs)=∑ k∈S, r^(k-a).natAbs :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact ((int_geometric_summable hr hr1).sum_le_tsum _ (fun k _ => pow_nonneg hr k.natAbs)).trans
    (int_geometric_tsum_le hr hr1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineGeometricSchur
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual binary scale ratio is a summable row-and-column kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem lineScaleWeight_pos (i j : ℤ) : 0<lineScaleWeight i j := by
  unfold lineScaleWeight
  positivity

theorem lineScaleWeight_ratio (i j : ℤ) (hij : i≤j) :
    DyadicLineGrid.scale i/DyadicLineGrid.scale j=lineScaleWeight i j := by
  have hn : ((j-i).natAbs:ℤ)=j-i := by omega
  unfold lineScaleWeight DyadicLineGrid.scale
  rw [←zpow_natCast,show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num,inv_zpow,←zpow_neg,hn,neg_sub,
    zpow_sub₀ (by norm_num : (2:ℝ)≠0)]

theorem lineScaleWeight_row (J : Finset ℤ) (i : ℤ) :
    (∑ j∈J, lineScaleWeight i j)≤4 := by
  simpa only [lineScaleWeight,show (2:ℝ)/(1-1/2)=4 by norm_num] using
    (int_geometric_shift_sum_le (r:=(1/2:ℝ)) (by norm_num) (by norm_num) J i)

theorem lineScaleWeight_col (I : Finset ℤ) (j : ℤ) :
    (∑ i∈I, lineScaleWeight i j)≤4 := by
  have he (i : ℤ) : lineScaleWeight i j=lineScaleWeight j i := by
    unfold lineScaleWeight
    rw [←Int.natAbs_neg,neg_sub]
  simpa only [he] using lineScaleWeight_row I j

theorem line_geometric_energy_schur {E : Type*} [NormedAddCommGroup E]
    (I J : Finset ℤ) (F : ℤ → ℤ → ℝ → E)
    (hF : ∀ i∈I, ∀ j∈J, MemLp (F i j) 2 volume)
    (b : ℤ → ℝ) (hb : ∀ j∈J, 0≤b j)
    (hbound : ∀ i∈I, ∀ j∈J, (∫ x, ‖F i j x‖^2)≤(lineScaleWeight i j)^2*b j) :
    (∑ i∈I, ∫ x, ‖∑ j∈J, F i j x‖^2)≤16*∑ j∈J, b j := by
  classical
  have hh := finite_energy_schur (volume : Measure ℝ)
    (fun (i : I) (j : J) => F i.val j.val)
    (fun i j => hF i.val i.property j.val j.property)
    (fun (i : I) (j : J) => lineScaleWeight i.val j.val)
    (fun i j => lineScaleWeight_pos i.val j.val)
    (fun j : J => b j.val) (fun j => hb j.val j.property)
    (R:=4) (C:=4) (by norm_num)
    (fun i => by
      rw [Finset.sum_coe_sort J (fun j => lineScaleWeight i.val j)]
      exact lineScaleWeight_row J i.val)
    (fun j => by
      rw [Finset.sum_coe_sort I (fun i => lineScaleWeight i j.val)]
      exact lineScaleWeight_col I j.val)
    (fun i j => hbound i.val i.property j.val j.property)
  change (∑ i : I, ∫ x, ‖∑ j : J, F i.val j.val x‖^2)≤
    4*4*(∑ j : J, b j.val) at hh
  have he (i : ℤ) : (∫ x, ‖∑ j : J, F i j.val x‖^2)=
      ∫ x, ‖∑ j∈J, F i j x‖^2 := by
    congr 1
    funext x
    rw [Finset.sum_coe_sort J (fun j => F i j x)]
  simp_rw [he] at hh
  rw [Finset.sum_coe_sort I (fun i => ∫ x, ‖∑ j∈J, F i j x‖^2),
    Finset.sum_coe_sort J b] at hh
  norm_num at hh
  exact hh

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableDerivativeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differentiated comparable-frequency commutator has no output
above a fixed multiple of its input frequencies. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lineScaleWeight_symm (i j : ℤ) : lineScaleWeight i j=lineScaleWeight j i := by
  unfold lineScaleWeight
  rw [←Int.natAbs_neg,neg_sub]

theorem bounded_scaleRatio_le_weight (i k : ℤ) (h : scale k/scale i≤128) :
    scale k/scale i≤16384*lineScaleWeight i k := by
  by_cases hki : k ≤ i
  · rw [lineScaleWeight_ratio k i hki,lineScaleWeight_symm k i]
    nlinarith [lineScaleWeight_pos i k]
  · have hik : i≤k := by omega
    have hw : (scale k/scale i)*lineScaleWeight i k=1 := by
      rw [←lineScaleWeight_ratio i k hik]
      field_simp [(scale_pos i).ne',(scale_pos k).ne']
    have hh := mul_le_mul_of_nonneg_right h (lineScaleWeight_pos i k).le
    rw [hw] at hh
    linarith

theorem comparableDerivative_projection_zero (m b h : SchwartzMap ℝ ℂ)
    (W V : ℝ) (hW : 0<W) (hV : 0<V) (hWV : 128*V≤W)
    (hh : ∀ eta, (𝓕 h : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/W) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    lineSchwartzProjection dyadicDifference V hV.ne'
      (schwartzDerivative 1 (lineSchwartzCommutator m B h))=0 := by
  intro B
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection dyadicDifference V hV.ne'
    (schwartzDerivative 1 (lineSchwartzCommutator m B h))) : SchwartzMap ℝ ℂ) eta=(𝓕 (0 : SchwartzMap ℝ ℂ)) eta
  rw [FourierTransform.fourier_zero,zero_apply]
  by_contra hne
  have hd := dyadicProjection_frequency V hV (schwartzDerivative 1 (lineSchwartzCommutator m B h)) eta hne
  have hf := lineSchwartzProjection_frequency_of_nonzero dyadicDifference _ V hV.ne' eta hne
  have hc := schwartzDerivative_frequency_of_nonzero (lineSchwartzCommutator m B h) eta hf
  have hb := dyadicProjection_frequency W hW b
  have hball := lineSchwartzCommutator_ball m B h ((13/6)/W) (64/W)
    (fun x hx => (hb x hx).2) hh eta hc
  have hlo := (div_le_iff₀ hV).mp hd.1
  have hhi := mul_le_mul_of_nonneg_left hball hW.le
  have he : W*((13/6)/W+64/W)=(13/6:ℝ)+64 := by field_simp [hW.ne']
  rw [he] at hhi
  have hg := mul_le_mul_of_nonneg_right hWV (abs_nonneg eta)
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicResolutionSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact telescoping and strong pointwise resolution for the binary
low-pass differences used in the commutator decomposition. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicDifference_telescope (M : ℕ) (x : ℝ) :
    (∑ n∈Finset.range M, dyadicDifference ((2:ℝ)^n*x))=
      reassemblyLow (x/2)-reassemblyLow (((2:ℝ)^M*x)/2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,dyadicDifference_apply,pow_succ]
    have he : (2^M*2*x)/2=(2:ℝ)^M*x := by ring
    rw [he]
    ring

theorem dyadicResolutionSymbol_eq (N : ℕ) (x : ℝ) :
    dyadicResolutionSymbol N x=
      reassemblyLow ((1/2:ℝ)^(N+1)*x)-reassemblyLow ((2:ℝ)^N*x) := by
  unfold dyadicResolutionSymbol
  have he (n : ℕ) : dyadicResolutionScale N n*x=(2:ℝ)^n*((1/2:ℝ)^N*x) := by
    unfold dyadicResolutionScale
    ring
  simp_rw [he]
  rw [dyadicDifference_telescope]
  have hfirst : ((1/2:ℝ)^N*x)/2=(1/2:ℝ)^(N+1)*x := by rw [pow_succ]; ring
  have hcancel : (2:ℝ)^N*(1/2:ℝ)^N=1 := by rw [←mul_pow]; norm_num
  have hlast : ((2:ℝ)^(2*N+1)*((1/2:ℝ)^N*x))/2=(2:ℝ)^N*x := by
    rw [show 2*N+1=N+N+1 by omega,pow_succ,pow_add]
    calc
      _ = ((2:ℝ)^N*(1/2:ℝ)^N)*(2:ℝ)^N*x := by ring
      _ = _ := by rw [hcancel,one_mul]
  rw [hfirst,hlast]

theorem dyadicResolutionSymbol_norm (N : ℕ) (x : ℝ) :
    ‖dyadicResolutionSymbol N x‖≤2 := by
  rw [dyadicResolutionSymbol_eq]
  have h1 := reassemblyLow_norm ((1/2:ℝ)^(N+1)*x)
  have h2 := reassemblyLow_norm ((2:ℝ)^N*x)
  exact (norm_sub_le _ _).trans (by linarith only [h1,h2])

theorem dyadicResolutionSymbol_tendsto (x : ℝ) (hx : x≠0) :
    Tendsto (fun N : ℕ => dyadicResolutionSymbol N x) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun N : ℕ => reassemblyLow ((1/2:ℝ)^(N+1)*x)) atTop (𝓝 1) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const ((1/2:ℝ)*x)
    have hh := reassemblyLow.continuous.continuousAt.tendsto.comp hp
    simpa only [Function.comp_def,zero_mul,pow_succ,mul_assoc,reassemblyLow_one 0 (by norm_num)] using hh
  have hlarge : ∀ᶠ N : ℕ in atTop, reassemblyLow ((2:ℝ)^N*x)=0 := by
    have hp := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const
      (show 0 < |x| from abs_pos.mpr hx)
    filter_upwards [hp.eventually (eventually_ge_atTop (13/12:ℝ))] with N hN
    apply reassemblyLow_zero
    simpa only [abs_mul,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) N)] using hN
  have hz : Tendsto (fun N : ℕ => reassemblyLow ((2:ℝ)^N*x)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hlarge.mono fun _ h => h.symm)
  simpa only [dyadicResolutionSymbol_eq,sub_zero] using hsmall.sub hz

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 resolution by the genuine binary smooth differences. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicSchwartzSum_fourier (N : ℕ) (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (dyadicSchwartzSum N f) : SchwartzMap ℝ ℂ) eta=
      dyadicResolutionSymbol N eta*(𝓕 f) eta := by
  simp only [dyadicSchwartzSum,FourierTransform.fourier_sum,sum_apply,lineSchwartzProjection_fourier,dyadicResolutionSymbol]
  exact (Finset.sum_mul _ _ _).symm

theorem dyadicSchwartzSum_sub_fourier (N : ℕ) (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ) eta=
      (dyadicResolutionSymbol N eta-1)*(𝓕 f) eta := by
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (dyadicSchwartzSum N f-f)) eta=_
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,dyadicSchwartzSum_fourier]
  ring

theorem dyadicSchwartzSum_energy_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∫ x, ‖dyadicSchwartzSum N f x-f x‖^2) atTop (𝓝 0) := by
  have hi : Integrable (fun eta => (9:ℝ)*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2) :=
    (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul 9
  have hh := tendsto_integral_of_dominated_convergence
    (fun eta => (9:ℝ)*‖(𝓕 f : SchwartzMap ℝ ℂ) eta‖^2)
    (F:=fun N eta => ‖(𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ) eta‖^2)
    (f:=fun _ => (0:ℝ))
    (fun N => ((𝓕 (dyadicSchwartzSum N f-f) : SchwartzMap ℝ ℂ).continuous.measurable.norm.pow_const 2).aestronglyMeasurable)
    hi
    (fun N => Filter.Eventually.of_forall fun eta => by
      rw [Real.norm_of_nonneg (sq_nonneg _),dyadicSchwartzSum_sub_fourier,norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have htri := norm_sub_le (dyadicResolutionSymbol N eta) 1
      have hs := dyadicResolutionSymbol_norm N eta
      simp only [norm_one] at htri
      have hn : ‖dyadicResolutionSymbol N eta-1‖≤3 := by linarith
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by norm_num))
    (by
      filter_upwards [volume.ae_ne (0:ℝ)] with eta heta
      have hlim := (((dyadicResolutionSymbol_tendsto eta heta).sub_const 1).mul_const ((𝓕 f) eta)).norm.pow 2
      simpa only [dyadicSchwartzSum_sub_fourier,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2≠0)] using hlim)
  simpa only [SchwartzMap.integral_norm_sq_fourier,sub_apply,integral_zero] using hh

theorem dyadicSchwartzSum_Lp_tendsto (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => (dyadicSchwartzSum N f).toLp 2 volume) atTop (𝓝 (f.toLp 2 volume)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun N : ℕ => dyadicSchwartzSum N f)
    (fun N => (dyadicSchwartzSum N f).memLp 2 volume) f (f.memLp 2 volume)).mpr
  have he (N : ℕ) : eLpNorm ((dyadicSchwartzSum N f : ℝ → ℂ)-(f : ℝ → ℂ)) 2 volume=
      ENNReal.ofReal (Real.sqrt (∫ x, ‖dyadicSchwartzSum N f x-f x‖^2)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (((dyadicSchwartzSum N f).memLp 2 volume).sub (f.memLp 2 volume))]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (dyadicSchwartzSum_energy_tendsto f))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineAnnularSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed annular Fourier overlap controls sums of the actual line
Schwartz functions appearing in the commutator proof. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem line_annular_nonzero_count (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) (eta : ℝ) :
    (I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)).card≤3 := by
  classical
  let A := I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)
  change A.card≤3
  have hsep (j : ℤ) (hj : j∈A) (k : ℤ) (hk : k∈A) (hjk : j+2≤k) : False := by
    have hjb := hband j (Finset.mem_filter.mp hj).1 eta (Finset.mem_filter.mp hj).2
    have hkb := hband k (Finset.mem_filter.mp hk).1 eta (Finset.mem_filter.mp hk).2
    have hp : (2:ℝ)^j*4≤(2:ℝ)^k := by
      calc
        _ = (2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
        _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg eta)
    nlinarith only [hh,hjb.1,hkb.2]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k hk j hj (by omega)
      · by_contra hn
        exact hsep j hj k hk (by omega)
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem line_annular_pointwise_square (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) (eta : ℝ) :
    ‖∑ k∈I, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2≤3*∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
  classical
  let A := I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)
  have he : (∑ k∈I, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta)=∑ k∈A, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkA
    by_contra h
    exact hkA (Finset.mem_filter.mpr ⟨hk,h⟩)
  have hs : (∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2)=∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkA
    have hz : (𝓕 (f k) : SchwartzMap ℝ ℂ) eta=0 := by
      by_contra h
      exact hkA (Finset.mem_filter.mpr ⟨hk,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have hc : (A.card:ℝ)≤3 := by exact_mod_cast line_annular_nonzero_count I f hband eta
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
    (f:=fun _ => (1:ℝ)) (g:=fun k => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) (r:=fun k => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  rw [he]
  calc
    _ ≤ (∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (A.card:ℝ)*(∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) := hcs
    _ ≤ 3*(∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) :=
      mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [hs]

theorem line_annular_sum_energy (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) :
    (∫ x, ‖(∑ k∈I, f k) x‖^2)≤3*∑ k∈I, ∫ x, ‖f k x‖^2 := by
  have hi (k : ℤ) : Integrable (fun eta => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) :=
    ((𝓕 (f k) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∫ eta, ‖(𝓕 (∑ k∈I, f k) : SchwartzMap ℝ ℂ) eta‖^2 :=
      (SchwartzMap.integral_norm_sq_fourier _).symm
    _ ≤ ∫ eta, 3*∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
      apply integral_mono
        (((𝓕 (∑ k∈I, f k) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0))
        ((integrable_finsetSum _ (fun k _ => hi k)).const_mul 3)
      intro eta
      simpa only [FourierTransform.fourier_sum,sum_apply] using line_annular_pointwise_square I f hband eta
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => hi k)]
      simp_rw [SchwartzMap.integral_norm_sq_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDyadicReconstructionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic square bounds control the whole Schwartz function,
using the already proved strong binary resolution. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadicResolutionScale_eq_scale (N n : ℕ) :
    dyadicResolutionScale N n=scale ((n:ℤ)-(N:ℤ)) := by
  simp only [dyadicResolutionScale,scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_natCast]
  rw [one_div,inv_pow]
  ring

theorem dyadicSchwartzSum_eq_window (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    dyadicSchwartzSum N f=∑ k∈dyadicResolutionWindow N,
      lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f := by
  classical
  unfold dyadicSchwartzSum dyadicResolutionWindow
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    simp only [dyadicResolutionScale_eq_scale]
  · intro i _ j _ hij
    change (i:ℤ)-(N:ℤ)=(j:ℤ)-(N:ℤ) at hij
    omega

theorem line_dyadic_reconstruction_energy (f : SchwartzMap ℝ ℂ) (C : ℝ)
    (hC : ∀ I : Finset ℤ, (∑ k∈I, ∫ x, ‖lineSchwartzProjection dyadicDifference
      (scale k) (scale_pos k).ne' f x‖^2)≤C) :
    (∫ x, ‖f x‖^2)≤3*C := by
  have hs (N : ℕ) : (∫ x, ‖dyadicSchwartzSum N f x‖^2)≤3*C := by
    rw [dyadicSchwartzSum_eq_window]
    have ho := line_annular_sum_energy (dyadicResolutionWindow N)
      (fun k => lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f) (by
        intro k _ eta heta
        have hf := dyadicProjection_frequency (scale k) (scale_pos k) f eta heta
        have hlo := (div_le_iff₀ (scale_pos k)).mp hf.1
        have hhi := (le_div_iff₀ (scale_pos k)).mp hf.2
        constructor
        · change 1≤|eta| *scale k at hlo
          dsimp [scale] at hlo
          nlinarith only [hlo]
        · dsimp [scale] at hhi
          nlinarith only [hhi])
    exact ho.trans (mul_le_mul_of_nonneg_left (hC _) (by norm_num))
  have hn (g : SchwartzMap ℝ ℂ) : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
    memLp_toL2_norm_sq volume g (g.memLp 2 volume)
  have hl := (dyadicSchwartzSum_Lp_tendsto f).norm.pow 2
  have hb : ∀ᶠ N : ℕ in atTop, ‖(dyadicSchwartzSum N f).toLp 2 volume‖^2≤3*C :=
    Filter.Eventually.of_forall (fun N => by simpa only [hn] using hs N)
  simpa only [hn] using le_of_tendsto hl hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableDerivativeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative part of the comparable-frequency commutator sums
uniformly, including arbitrarily low output frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem comparableDerivativeSum_energy (I : Finset ℤ) (m b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) (A L : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (hH : ∀ k∈I, ∀ eta, (𝓕 (H k) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    (∫ x, ‖(∑ k∈I, comparableDerivativePiece m b H k) x‖^2)≤
      48*(16384*(A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (52*Real.pi/3)))^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
  let C₀ := A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*(52*Real.pi/3)
  let C := 16384*C₀
  let F := ∑ k∈I, comparableDerivativePiece m b H k
  let P := fun i k => lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne'
    (comparableDerivativePiece m b H k)
  have hpiece (i k : ℤ) (hk : k∈I) : (∫ x, ‖P i k x‖^2)≤
      (lineScaleWeight i k)^2*(C^2*(∫ x, ‖H k x‖^2)) := by
    by_cases hr : scale k/scale i≤128
    · have hc := projectedCommutator_derivative_energy m b (H k) (scale k) (scale i) A L
        (scale_pos k) (scale_pos i) hm hLip
      have hratio := bounded_scaleRatio_le_weight i k hr
      calc
        _ ≤ (C₀*(scale k/scale i))^2*(∫ x, ‖H k x‖^2) := hc
        _ = C₀^2*(scale k/scale i)^2*(∫ x, ‖H k x‖^2) := by ring
        _ ≤ C₀^2*(16384*lineScaleWeight i k)^2*(∫ x, ‖H k x‖^2) := by
          gcongr
          exact div_nonneg (scale_pos k).le (scale_pos i).le
        _ = _ := by dsimp [C]; ring
    · have hlarge : 128*scale i ≤ scale k :=
        (le_div_iff₀ (scale_pos i)).mp (lt_of_not_ge hr).le
      have hz := comparableDerivative_projection_zero m b (H k) (scale k) (scale i)
        (scale_pos k) (scale_pos i) hlarge (hH k hk)
      change (∫ x, ‖lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne'
        (comparableDerivativePiece m b H k) x‖^2)≤_
      simp only [comparableDerivativePiece,hz,zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      positivity
  have hproj (J : Finset ℤ) : (∑ i∈J, ∫ x, ‖lineSchwartzProjection dyadicDifference
      (scale i) (scale_pos i).ne' F x‖^2)≤16*C^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
    have hs := line_geometric_energy_schur J I (fun i k x => P i k x)
      (fun i _ k _ => (P i k).memLp 2 volume)
      (fun k => C^2*(∫ x, ‖H k x‖^2)) (fun k _ => by positivity)
      (fun i _ k hk => hpiece i k hk)
    have he (i : ℤ) : lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne' F=
        ∑ k∈I, P i k := map_sum (lineSchwartzProjectionLM dyadicDifference (scale i) (scale_pos i).ne') _ I
    simp_rw [he,sum_apply]
    simpa only [←Finset.mul_sum,mul_assoc] using hs
  have hh := line_dyadic_reconstruction_energy F (16*C^2*(∑ k∈I, ∫ x, ‖H k x‖^2)) hproj
  apply hh.trans_eq
  dsimp [C,C₀]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicProjectionCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson condition for the actual binary line projections,
first on intervals and then on the nested dyadic line cells. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicCarlesonConstant_pos : 0<dyadicCarlesonConstant := by
  unfold dyadicCarlesonConstant
  positivity

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelAverageBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A kernel with a zeroth and a second decay bound is controlled by
centered interval averages. Finite annular sums retain a uniform constant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem kernel_average_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (hfm : Measurable f) (B : ℝ) (hfb : ∀ x, ‖f x‖≤B)
    (A D R M x : ℝ) (hA : 0≤A) (hD : 0≤D) (hR : 0<R) (hM : 0≤M)
    (hzero : ∀ t, ‖K t‖≤A) (hsecond : ∀ t, |t|^2*‖K t‖≤D)
    (hmean : ∀ r, R ≤ r → (∫ t in Icc (-r) r, ‖f (x-t)‖)≤12*r*M) :
    ‖lineConvolution K f x‖≤12*A*R*M+48*D/R*M := by
  let g := fun t => ‖K t‖*‖f (x-t)‖
  have hg : Integrable g := by
    simpa only [norm_mul] using
      (lineConvolution_integrand_of_bounded K f hK hfm B hfb x).norm
  let r := fun n : ℕ => (2:ℝ)^n*R
  let S := fun n => Icc (-r n) (r n)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hRr (n : ℕ) : R ≤ r n := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hR.le
  have hsucc (n : ℕ) : r (n+1)=2*r n := by dsimp [r]; rw [pow_succ]; ring
  have hmono : Monotone S := by
    intro n m hnm
    have hm : r n ≤ r m := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hnm) hR.le
    intro t ht
    exact ⟨by linarith [ht.1],ht.2.trans hm⟩
  have hbase : (∫ t in S 0, g t)≤12*A*R*M := by
    have hfi : IntegrableOn (fun t => ‖f (x-t)‖) (S 0) := by
      have : IsFiniteMeasure (volume.restrict (S 0)) := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
      exact (MemLp.of_bound (p:=1)
        (hfm.comp (show Measurable (fun t : ℝ => x-t) by fun_prop)).norm.aestronglyMeasurable.restrict B
        (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_of_nonneg (norm_nonneg _),Function.comp_def] using hfb (x-t)))).integrable (by norm_num)
    calc
      _ ≤ ∫ t in S 0, A*‖f (x-t)‖ := integral_mono hg.integrableOn (hfi.const_mul A)
        (fun t => mul_le_mul_of_nonneg_right (hzero t) (norm_nonneg _))
      _ = A*(∫ t in Icc (-R) R, ‖f (x-t)‖) := by simp only [S,r,pow_zero,one_mul,integral_const_mul]
      _ ≤ A*(12*R*M) := mul_le_mul_of_nonneg_left (hmean R le_rfl) hA
      _ = _ := by ring
  have hstep (n : ℕ) : (∫ t in S (n+1)\S n, g t)≤24*D/R*M*(1/2:ℝ)^n := by
    have hfi : IntegrableOn (fun t => ‖f (x-t)‖) (S (n+1)) := by
      have : IsFiniteMeasure (volume.restrict (S (n+1))) := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
      exact (MemLp.of_bound (p:=1)
        (hfm.comp (show Measurable (fun t : ℝ => x-t) by fun_prop)).norm.aestronglyMeasurable.restrict B
        (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_of_nonneg (norm_nonneg _),Function.comp_def] using hfb (x-t)))).integrable (by norm_num)
    have hb (t : ℝ) (ht : t∈S (n+1)\S n) : ‖K t‖≤D/(r n)^2 := by
      have htabs : r n≤|t| := by
        by_contra hh
        apply ht.2
        have hh' := abs_le.mp (le_of_lt (lt_of_not_ge hh))
        exact hh'
      have hp := pow_le_pow_left₀ (hr n).le htabs 2
      apply (le_div_iff₀ (sq_pos_of_pos (hr n))).mpr
      calc
        ‖K t‖*(r n)^2 ≤ ‖K t‖*|t|^2 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ ≤ D := by simpa only [mul_comm] using hsecond t
    calc
      _ ≤ ∫ t in S (n+1)\S n, (D/(r n)^2)*‖f (x-t)‖ := by
        apply integral_mono_ae hg.integrableOn ((hfi.const_mul (D/(r n)^2)).mono_measure (Measure.restrict_mono sdiff_subset le_rfl))
        filter_upwards [ae_restrict_mem (measurableSet_Icc.diff measurableSet_Icc)] with t ht
        exact mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
      _ ≤ ∫ t in S (n+1), (D/(r n)^2)*‖f (x-t)‖ :=
        setIntegral_mono_set (hfi.const_mul _) (Filter.Eventually.of_forall fun _ => by positivity)
          (Filter.Eventually.of_forall sdiff_subset)
      _ = (D/(r n)^2)*(∫ t in S (n+1), ‖f (x-t)‖) := by rw [integral_const_mul]
      _ ≤ (D/(r n)^2)*(12*r (n+1)*M) :=
        mul_le_mul_of_nonneg_left (hmean _ (hRr _)) (by positivity)
      _ = _ := by
        rw [hsucc]
        dsimp [r]
        rw [div_pow,one_pow]
        field_simp
        ring
  have hfinite (n : ℕ) : (∫ t in S n, g t)≤
      12*A*R*M+(24*D/R*M)*(∑ k∈Finset.range n, (1/2:ℝ)^k) := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      have he := integral_inter_add_sdiff (s:=S (n+1)) (t:=S n) measurableSet_Icc hg.integrableOn
      rw [inter_eq_right.mpr (hmono (Nat.le_succ n))] at he
      rw [Finset.sum_range_succ]
      linarith [hstep n]
  have hall (n : ℕ) : (∫ t in S n, g t)≤12*A*R*M+48*D/R*M := by
    have hh := mul_le_mul_of_nonneg_left (sum_half_powers_le_two n)
      (show 0≤24*D/R*M by positivity)
    calc
      _ ≤ 12*A*R*M+(24*D/R*M)*(∑ k∈Finset.range n, (1/2:ℝ)^k) := hfinite n
      _ ≤ 12*A*R*M+(24*D/R*M)*2 := add_le_add le_rfl hh
      _ = _ := by ring
  have hcover : (⋃ n, S n)=(univ : Set ℝ) := by
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
      (eventually_gt_atTop (|t|/R))).exists
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    have ht : |t| ≤ r n := by
      dsimp [r]
      exact le_of_lt ((div_lt_iff₀ hR).mp hn)
    exact abs_le.mp ht
  have hlim := tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hmono
    hg.integrableOn
  rw [hcover] at hlim
  simp only [Measure.restrict_univ] at hlim
  have htotal := le_of_tendsto hlim (Filter.Eventually.of_forall hall)
  exact (norm_integral_le_integral_norm _).trans (by simpa only [g,norm_mul] using htotal)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceThreeGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal three-grid covering lemma for the nested alternating
one-third grids. It supplies the interval comparison in the maximal
kernel estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert.DyadicLineGrid

theorem shift_signed_third (k : ℤ) : shift (k.negOnePow:ℤ) k=1/3 := by
  simp only [shift,←Units.val_mul,Int.units_mul_self,Units.val_one,Int.cast_one]

theorem signed_third_in_range (k : ℤ) : (k.negOnePow:ℤ)∈Finset.Icc (-1) 1 := by
  rw [Finset.mem_Icc]
  exact abs_le.mp (le_of_eq (Int.abs_negOnePow k))

/-- A closed interval of radius less than one sixth of a grid cell
fits in a cell of one of the three fixed nested grids. -/
theorem exists_three_grid_cover (k : ℤ) (c r : ℝ) (_hr : 0 ≤ r)
    (hsmall : 6*r < scale k) :
    ∃ q∈Finset.Icc (-1) 1, ∃ j : ℤ, Icc (c-r) (c+r)⊆cell q k j := by
  let m := index 0 k c
  let a := left 0 k m
  have hc := mem_index_cell 0 k c
  have hright : left 0 k (m+1)=a+scale k := by
    dsimp [a,left,shift]
    push_cast
    ring
  change a ≤ c ∧ c<left 0 k (m+1) at hc
  rw [hright] at hc
  by_cases hleft : a ≤ c-r
  · by_cases hend : c+r<a+scale k
    · refine ⟨0,by simp, m,?_⟩
      intro x hx
      exact ⟨hleft.trans hx.1,hx.2.trans_lt (by simpa only [hright] using hend)⟩
    · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m,?_⟩
      intro x hx
      change left (k.negOnePow:ℤ) k m≤x ∧ x<left (k.negOnePow:ℤ) k (m+1)
      have hl : left (k.negOnePow:ℤ) k m=a+scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      have hu : left (k.negOnePow:ℤ) k (m+1)=a+4*scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      rw [hl,hu]
      constructor <;> linarith [hx.1,hx.2]
  · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m-1,?_⟩
    intro x hx
    change left (k.negOnePow:ℤ) k (m-1)≤x ∧
      x<left (k.negOnePow:ℤ) k (m-1+1)
    have hl : left (k.negOnePow:ℤ) k (m-1)=a-2*scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    have hu : left (k.negOnePow:ℤ) k (m-1+1)=a+scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    rw [hl,hu]
    constructor <;> linarith [hx.1,hx.2]

/-- The covering cell has length at most six times the interval length. -/
theorem exists_comparable_three_grid_cover (c r : ℝ) (hr : 0 < r) :
    ∃ q∈Finset.Icc (-1) 1, ∃ k j : ℤ,
      Icc (c-r) (c+r)⊆cell q k j ∧ scale k≤12*r := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0<12*r by positivity) (by norm_num : (1:ℝ)<2)
  change scale k≤12*r at hlo
  change 12*r < scale (k+1) at hhi
  rw [scale_succ] at hhi
  obtain ⟨q,hq,j,hcell⟩ := exists_three_grid_cover k c r hr.le (by linarith)
  exact ⟨q,hq,k,j,hcell,hlo⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PartitionIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing nonnegative cell estimates over a countable measurable partition. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]

/-- Summable control on partition cells proves global integrability as well
as the global estimate; no integrability of the left side is assumed. -/
theorem integral_le_of_partition (μ : Measure α) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) = Set.univ) (f g : α → ℝ) {C : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hgint : Integrable g μ)
    (hf : ∀ i, IntegrableOn f (s i) μ)
    (hbound : ∀ i, (∫ x in s i, f x ∂μ) ≤ C * ∫ x in s i, g x ∂μ) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C * ∫ x, g x ∂μ := by
  have hgsum : Summable (fun i => ∫ x in s i, g x ∂μ) :=
    (hasSum_integral_iUnion hs hd hgint.integrableOn).summable
  have hfsum : Summable (fun i => ∫ x in s i, f x ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg hf0) hbound (hgsum.mul_left C)
  have hnorm : Summable (fun i => ∫ x in s i, ‖f x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hfsum
  have hfint := integrableOn_iUnion_of_summable_integral_norm hf hnorm
  rw [hcover, integrableOn_univ] at hfint
  have hfi := integral_iUnion hs hd hfint.integrableOn
  have hgi := integral_iUnion hs hd hgint.integrableOn
  rw [hcover, setIntegral_univ] at hfi hgi
  refine ⟨hfint, ?_⟩
  calc
    (∫ x, f x ∂μ) = ∑' i, ∫ x in s i, f x ∂μ := hfi
    _ ≤ ∑' i, C * ∫ x in s i, g x ∂μ := hfsum.tsum_le_tsum hbound (hgsum.mul_left C)
    _ = C * ∑' i, ∫ x in s i, g x ∂μ := tsum_mul_left
    _ = C * ∫ x, g x ∂μ := congrArg (C * ·) hgi.symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleLocalMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

omit [IsFiniteMeasure μ] in
theorem martingale_abs (hF : Martingale F ℱ μ) :
    Submartingale (fun i x => |F i x|) ℱ μ := by
  have heq : (fun i x => |F i x|) = F ⊔ -F := by
    funext i x
    exact abs_eq_max_neg
  rw [heq]
  exact hF.submartingale.sup hF.neg.submartingale

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaximalL2Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The p=2 maximal energy argument. A localized weak-L1 estimate,
layer cake, and Cauchy--Schwarz give the strong L2 constant four. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem maximal_square_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H g : Ω → ℝ) (hH : Measurable H) (hg : Measurable g)
    (hH0 : ∀ x, 0 ≤ H x) (hg0 : ∀ x, 0 ≤ g x)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t*μ {x | t ≤ H x} ≤
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal ((H x)^2) ∂μ) ≤
      2 * ∫⁻ x, ENNReal.ofReal (g x*H x) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hν (t : ℝ) : ν {x | t ≤ H x} =
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ :=
    withDensity_apply _ (measurableSet_le measurable_const hH)
  have hpow := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hH0) hH.aemeasurable (by norm_num : (0:ℝ)<2)
  simp only [Real.rpow_two, show (2:ℝ)-1=1 by norm_num, Real.rpow_one,
    ENNReal.ofReal_ofNat] at hpow
  rw [hpow]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ν {x | t ≤ H x} := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      rw [hν, mul_comm]
      exact hweak t ht
    _ = ∫⁻ x, ENNReal.ofReal (H x) ∂ν :=
      (lintegral_eq_lintegral_meas_le ν (Filter.Eventually.of_forall hH0) hH.aemeasurable).symm
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul μ hg.ennreal_ofReal hH.ennreal_ofReal]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (hg0 x)).symm

theorem maximal_L2_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H g : Ω → ℝ) (hH : Measurable H) (hg : Measurable g)
    (hH0 : ∀ x, 0 ≤ H x) (hg0 : ∀ x, 0 ≤ g x)
    (hH2 : MemLp H 2 μ) (hg2 : MemLp g 2 μ)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t*μ {x | t ≤ H x} ≤
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ) :
    (∫ x, (H x)^2 ∂μ) ≤ 4 * ∫ x, (g x)^2 ∂μ := by
  have hintH := hH2.integrable_sq
  have hintg := hg2.integrable_sq
  have hintprod : Integrable (fun x => g x*H x) μ := hg2.integrable_mul hH2
  have h := maximal_square_lintegral μ H g hH hg hH0 hg0 hweak
  rw [← ofReal_integral_eq_lintegral_ofReal hintH
    (Filter.Eventually.of_forall (fun x => sq_nonneg (H x))),
    ← ofReal_integral_eq_lintegral_ofReal hintprod
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hg0 x) (hH0 x)))] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg (H x))),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => mul_nonneg (hg0 x) (hH0 x)))] at hr
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall hg0)
    (Filter.Eventually.of_forall hH0) (by simpa using hg2) (by simpa using hH2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hposH : 0 ≤ ∫ x, (H x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (H x))
  have hposg : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (g x))
  have hrootH := Real.sq_sqrt hposH
  have hrootg := Real.sq_sqrt hposg
  have hsquare := sq_nonneg (Real.sqrt (∫ x, (H x)^2 ∂μ) -
    2*Real.sqrt (∫ x, (g x)^2 ∂μ))
  nlinarith [Real.sqrt_nonneg (∫ x, (H x)^2 ∂μ), Real.sqrt_nonneg (∫ x, (g x)^2 ∂μ)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleMaximalL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Doob's scalar finite-horizon L2 estimate, with its exact factor four,
for the dyadic averages used in the axis-parallel rectangle count. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem finiteMaxSignal_nonneg {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ finiteMaxSignal F N x := by
  exact (abs_nonneg (F 0 x)).trans (Finset.le_sup' (fun i => |F i x|) (by simp))

theorem finiteMaxSignal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i ≤ N, Measurable (F i)) :
    Measurable (finiteMaxSignal F N) :=
  Finset.measurable_range_sup'' (fun i hi => by
    simpa only [Real.norm_eq_abs] using (hF i hi).norm)

theorem finiteMaxSignal_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i, MemLp (F i) 2 μ) :
    MemLp (finiteMaxSignal F N) 2 μ := by
  induction N with
  | zero =>
    have heq : finiteMaxSignal F 0 = fun x => |F 0 x| := by
      funext x
      simp [finiteMaxSignal]
    rw [heq]
    simpa only [Real.norm_eq_abs] using (hF 0).norm
  | succ N ih =>
    have heq : finiteMaxSignal F (N+1) = (fun x => |F (N+1) x|) ⊔ finiteMaxSignal F N := by
      funext x
      have hh := Finset.sup'_insert (s := Finset.range (N+1)) (H := Finset.nonempty_range_add_one)
        (b := N+1) (f := fun i => |F i x|)
      simpa only [← Finset.range_add_one, finiteMaxSignal, Pi.sup_apply] using hh
    rw [heq]
    have hn : MemLp (fun x => |F (N+1) x|) 2 μ := by
      simpa only [Real.norm_eq_abs] using (hF (N+1)).norm
    exact hn.sup ih

theorem martingale_maximal_L2 {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (F : ℕ → Ω → ℝ)
    (hF : Martingale F ℱ μ) (hF2 : ∀ i, MemLp (F i) 2 μ) (N : ℕ) :
    (∫ x, (finiteMaxSignal F N x)^2 ∂μ) ≤ 4 * ∫ x, (F N x)^2 ∂μ := by
  have hm (i : ℕ) : Measurable (F i) := (hF.stronglyMeasurable i).measurable.le (ℱ.le i)
  have h := maximal_L2_energy μ (finiteMaxSignal F N) (fun x => |F N x|)
    (finiteMaxSignal_measurable F N (fun i _ => hm i)) (by simpa only [Real.norm_eq_abs] using (hm N).norm)
    (finiteMaxSignal_nonneg F N) (fun x => abs_nonneg (F N x))
    (finiteMaxSignal_memLp μ F N hF2) (by simpa only [Real.norm_eq_abs] using (hF2 N).norm) (by
      intro t ht
      let ε : ℝ≥0 := ⟨t,ht.le⟩
      have hw := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
        (ε := ε) N
      rw [← ofReal_integral_eq_lintegral_ofReal (hF.integrable N).abs.integrableOn
        (Filter.Eventually.of_forall (fun x => abs_nonneg (F N x)))]
      have hc : (ε : ℝ≥0∞) = ENNReal.ofReal t := ENNReal.coe_nnreal_eq ε
      rw [hc] at hw
      exact hw)
  simpa only [sq_abs] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual integer-indexed dyadic line averages. The alternating grids are
handled directly, with no alignment premise between a packet and a root. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

theorem lineAverage_martingale (q top j : ℤ) (f : ℝ → ℝ) :
    Martingale (lineAverage q top j f) (lineFiltration q top) (rootMeasure q top j) :=
  martingale_condExp f _ _

theorem lineAverage_memLp (q top j : ℤ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) (n : ℕ) :
    MemLp (lineAverage q top j f n) 2 (rootMeasure q top j) := hf.condExp (by norm_num)

theorem lineAverage_constant (q top j : ℤ) (f : ℝ → ℝ) (n : ℕ) {x y : ℝ}
    (hxy : index q (top-(n:ℤ)) x=index q (top-(n:ℤ)) y) :
    lineAverage q top j f n x=lineAverage q top j f n y :=
  (show StronglyMeasurable[lineFiltration q top n] (lineAverage q top j f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Each conditional expectation equals the literal average on the
actual dyadic cell containing the point. -/
theorem lineAverage_eq_cell_mean (q top j : ℤ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) (n : ℕ) {x : ℝ}
    (hx : x∈cell q top j) :
    lineAverage q top j f n x =
      (∫ y in cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x), f y)/scale (top-(n:ℤ)) := by
  let s := cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x)
  have hsub : s⊆cell q top j := cell_subset_of_intersect (by omega)
    ⟨x,mem_index_cell q (top-(n:ℤ)) x,hx⟩
  have hs : MeasurableSet[lineFiltration q top n] s := by
    change MeasurableSet[lineFiltration q top n] (cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x))
    rw [←index_fiber]
    exact (comap_measurable (index q (top-(n:ℤ)))) (measurableSet_singleton _)
  have hs' : MeasurableSet s := cell_measurable _ _ _
  have hmass : (rootMeasure q top j).real s=scale (top-(n:ℤ)) := by
    rw [measureReal_def,rootMeasure,Measure.restrict_apply hs',inter_eq_left.mpr hsub]
    exact cell_length q (top-(n:ℤ)) (index q (top-(n:ℤ)) x)
  apply (eq_div_iff (scale_pos (top-(n:ℤ))).ne').mpr
  calc
    lineAverage q top j f n x*scale (top-(n:ℤ)) =
        ∫ y in s, lineAverage q top j f n x ∂rootMeasure q top j := by
      rw [setIntegral_const,smul_eq_mul,hmass,mul_comm]
    _ = ∫ y in s, lineAverage q top j f n y ∂rootMeasure q top j := by
      apply setIntegral_congr_fun hs'
      intro y hy
      exact lineAverage_constant q top j f n (index_eq_of_mem hy).symm
    _ = ∫ y in s, f y ∂rootMeasure q top j := setIntegral_condExp ((lineFiltration q top).le n) hf hs
    _ = ∫ y in s, f y := by
      rw [rootMeasure,Measure.restrict_restrict hs',inter_eq_left.mpr hsub]

/-- Doob's bound on a root has a constant independent of the root, grid,
and number of retained scales. -/
theorem lineAverage_maximal_energy (q top j : ℤ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) (N : ℕ) :
    (∫ x, (finiteMaxSignal (lineAverage q top j f) N x)^2 ∂rootMeasure q top j) ≤
      4*∫ x, (f x)^2 ∂rootMeasure q top j := by
  have hmax := martingale_maximal_L2 (rootMeasure q top j) (lineFiltration q top)
    (lineAverage q top j f) (lineAverage_martingale q top j f)
    (fun n => lineAverage_memLp q top j hf n) N
  have hnorm : Integrable (fun x => ‖f x‖^(2:ℝ)) (rootMeasure q top j) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hf.integrable_sq
  have hcond := integral_norm_condExp_rpow_le (μ:=rootMeasure q top j)
    (m:=lineFiltration q top N) (p:=2) (by norm_num) hnorm
  have hcond' : (∫ x, (lineAverage q top j f N x)^2 ∂rootMeasure q top j) ≤
      ∫ x, (f x)^2 ∂rootMeasure q top j := by
    simpa only [lineAverage,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hcond
  exact hmax.trans (mul_le_mul_of_nonneg_left hcond' (by norm_num))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGlobalDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform L² bound for actual dyadic cell averages on the whole line.
The root intervals are glued using their true measurable partition. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem cellMean_measurable (q k : ℤ) (f : ℝ → ℝ) : Measurable (cellMean q k f) :=
  (measurable_of_countable (fun i : ℤ => (∫ y in cell q k i, f y)/scale k)).comp (index_measurable q k)

theorem dyadicMaximal_measurable (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) :
    Measurable (dyadicMaximal q top N f) :=
  finiteMaxSignal_measurable _ _ (fun n _ => cellMean_measurable q (top-(n:ℤ)) f)

theorem dyadicMaximal_nonneg (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    0≤dyadicMaximal q top N f x := finiteMaxSignal_nonneg _ _ _

theorem dyadicMaximal_eq_on_root (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) {x : ℝ} (hx : x∈cell q top j) :
    dyadicMaximal q top N f x=finiteMaxSignal (lineAverage q top j f) N x := by
  have heq : (fun n : ℕ => |cellMean q (top-(n:ℤ)) f x|) =
      (fun n : ℕ => |lineAverage q top j f n x|) := by
    funext n
    rw [lineAverage_eq_cell_mean q top j hf n hx]
    rfl
  exact congrArg (fun g : ℕ → ℝ => (Finset.range (N+1)).sup' Finset.nonempty_range_add_one g) heq

theorem dyadicMaximal_root_memLp (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) :
    MemLp (dyadicMaximal q top N f) 2 (rootMeasure q top j) := by
  have hm := finiteMaxSignal_memLp (rootMeasure q top j) (lineAverage q top j f) N
    (fun n => lineAverage_memLp q top j hf n)
  refine (memLp_congr_ae ?_).mp hm
  change ∀ᵐ x ∂volume.restrict (cell q top j), _
  filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
  exact (dyadicMaximal_eq_on_root q top j N (hf.integrable (by norm_num)) hx).symm

theorem dyadicMaximal_root_energy (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) :
    (∫ x, (dyadicMaximal q top N f x)^2 ∂rootMeasure q top j) ≤
      4*∫ x, (f x)^2 ∂rootMeasure q top j := by
  have heq : ∀ᵐ x ∂rootMeasure q top j,
      (dyadicMaximal q top N f x)^2=(finiteMaxSignal (lineAverage q top j f) N x)^2 := by
    change ∀ᵐ x ∂volume.restrict (cell q top j), _
    filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
    rw [dyadicMaximal_eq_on_root q top j N (hf.integrable (by norm_num)) hx]
  rw [integral_congr_ae heq]
  exact lineAverage_maximal_energy q top j hf N

/-- Actual finite dyadic maximal averages are L² bounded on Lebesgue
measure with constant four in squared norm, uniformly in both cutoffs. -/
theorem dyadicMaximal_energy (q top : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (dyadicMaximal q top N f) 2 volume ∧
    (∫ x, (dyadicMaximal q top N f x)^2) ≤ 4*∫ x, (f x)^2 := by
  have hcover : ⋃ j : ℤ, cell q top j = (univ : Set ℝ) := by
    apply Set.eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨index q top x,mem_index_cell q top x⟩
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (cell q top i) (cell q top j)) :=
    fun _ _ h => cells_disjoint q top h
  have hroot (j : ℤ) : MemLp f 2 (rootMeasure q top j) := hf.restrict _
  have h := integral_le_of_partition volume (cell q top) (cell_measurable q top) hdisj hcover
    (fun x => (dyadicMaximal q top N f x)^2) (fun x => (f x)^2)
    (fun x => sq_nonneg _) hf.integrable_sq
    (fun j => (dyadicMaximal_root_memLp q top j N (hroot j)).integrable_sq)
    (fun j => dyadicMaximal_root_energy q top j N (hroot j))
  exact ⟨(memLp_two_iff_integrable_sq (dyadicMaximal_measurable q top N f).aestronglyMeasurable).mpr h.1,h.2⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMonotoneMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from finite scale cutoffs to a genuine countable maximal
function. The real-valued representative is defined even on the null set
where the extended supremum is infinite. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem maximalSquare_measurable {X : Type*} [MeasurableSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) :
    Measurable (maximalSquare F) :=
  Measurable.iSup (fun n => (hF n).pow_const 2 |>.ennreal_ofReal)

theorem monotoneMaximal_measurable {X : Type*} [MeasurableSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) :
    Measurable (monotoneMaximal F) :=
  (maximalSquare_measurable F hF).ennreal_toReal.sqrt

/-- A nonnegative increasing sequence with a uniform squared-integral
bound has a measurable L² majorant with the same bound. -/
theorem monotoneMaximal_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀ n, Measurable (F n)) (hpos : ∀ n x, 0≤F n x)
    (hmono : Monotone F) (hLp : ∀ n, MemLp (F n) 2 μ)
    (henergy : ∀ n, (∫ x, (F n x)^2 ∂μ)≤C) :
    MemLp (monotoneMaximal F) 2 μ ∧
    (∫ x, (monotoneMaximal F x)^2 ∂μ)≤C ∧
    ∀ᵐ x ∂μ, ∀ n, F n x ≤ monotoneMaximal F x := by
  have hm := maximalSquare_measurable F hF
  have hlin : (∫⁻ x, maximalSquare F x ∂μ)≤ENNReal.ofReal C := by
    change (∫⁻ x, ⨆ n, ENNReal.ofReal ((F n x)^2) ∂μ)≤ENNReal.ofReal C
    rw [lintegral_iSup]
    · apply iSup_le
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal (hLp n).integrable_sq
        (Filter.Eventually.of_forall (fun x => sq_nonneg (F n x)))]
      exact ENNReal.ofReal_le_ofReal (henergy n)
    · exact fun n => (hF n).pow_const 2 |>.ennreal_ofReal
    · intro i j hij x
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hpos i x) (hmono hij x) 2)
  have hfin : (∫⁻ x, maximalSquare F x ∂μ)≠∞ :=
    ne_of_lt (hlin.trans_lt ENNReal.ofReal_lt_top)
  have haefin := ae_lt_top hm hfin
  have hreal := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
  have heq : (fun x => (monotoneMaximal F x)^2) =
      (fun x => (maximalSquare F x).toReal) := by
    funext x
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  refine ⟨(memLp_two_iff_integrable_sq
    (monotoneMaximal_measurable F hF).aestronglyMeasurable).mpr
      (heq.symm ▸ hreal),?_,?_⟩
  · rw [heq,integral_toReal hm.aemeasurable haefin]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    simpa only [ENNReal.toReal_ofReal hC] using h
  · filter_upwards [haefin] with x hx
    intro n
    apply Real.le_sqrt_of_sq_le
    have h := ENNReal.toReal_mono hx.ne (le_iSup (fun n => ENNReal.ofReal ((F n x)^2)) n)
    simpa only [ENNReal.toReal_ofReal (sq_nonneg (F n x))] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStrongDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite rectangular maximal averages on the actual nested line grids.
The constants are uniform in both scale cutoffs. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem abs_cellMean_le_dyadicMaximal (q top : ℤ) (N n : ℕ) (hn : n≤N)
    (f : ℝ → ℝ) (x : ℝ) :
    |cellMean q (top-(n:ℤ)) f x| ≤ dyadicMaximal q top N f x := by
  change |cellMean q (top-(n:ℤ)) f x| ≤
    (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
      (fun i : ℕ => |cellMean q (top-(i:ℤ)) f x|)
  exact Finset.le_sup' (fun i : ℕ => |cellMean q (top-(i:ℤ)) f x|)
    (Finset.mem_range.mpr (show n<N+1 by omega))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAllDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic maximal averages over all integer scales. Uniform finite
estimates give the countable-scale estimate without any scale loss. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem dyadicWindow_mono (q : ℤ) (f : ℝ → ℝ) :
    Monotone (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f) := by
  apply monotone_nat_of_le_succ
  intro N x
  change (Finset.range (2*N+1)).sup' Finset.nonempty_range_add_one
    (fun j : ℕ => |cellMean q ((N:ℤ)-(j:ℤ)) f x|) ≤ _
  apply (Finset.sup'_le_iff _ _).mpr
  intro j hj
  have hj' : j≤2*N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have heq : (N:ℤ)-(j:ℤ)=((N+1:ℕ):ℤ)-((j+1:ℕ):ℤ) := by omega
  change |cellMean q ((N:ℤ)-(j:ℤ)) f x|≤_
  rw [heq]
  exact abs_cellMean_le_dyadicMaximal q (N+1:ℕ) (2*(N+1)) (j+1) (by omega) f x

theorem allDyadicMaximal_measurable (q : ℤ) (f : ℝ → ℝ) :
    Measurable (allDyadicMaximal q f) :=
  monotoneMaximal_measurable _ (fun N => dyadicMaximal_measurable q N (2*N) f)

theorem allDyadicMaximal_nonneg (q : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    0≤allDyadicMaximal q f x := Real.sqrt_nonneg _

theorem cellMean_le_window (q k : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    |cellMean q k f x|≤dyadicMaximal q (k.natAbs:ℤ) (2*k.natAbs) f x := by
  let N := k.natAbs
  let j := ((N:ℤ)-k).toNat
  have hk : -(N:ℤ)≤k ∧ k≤N := by
    dsimp only [N]
    rw [Int.natCast_natAbs]
    exact ⟨neg_abs_le k,le_abs_self k⟩
  have hj : (j:ℤ)=(N:ℤ)-k := Int.toNat_of_nonneg (by omega)
  have hbound : j≤2*N := by omega
  have hscale : (N:ℤ)-(j:ℤ)=k := by omega
  have hcell := abs_cellMean_le_dyadicMaximal q (N:ℤ) (2*N) j hbound f x
  rw [hscale] at hcell
  exact hcell

/-- The genuine dyadic maximal operator is L² bounded, and dominates
all integer-scale averages simultaneously outside a single null set. -/
theorem allDyadicMaximal_energy (q : ℤ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (allDyadicMaximal q f) 2 volume ∧
    (∫ x, (allDyadicMaximal q f x)^2)≤4*∫ x, (f x)^2 ∧
    ∀ᵐ x ∂volume, ∀ k : ℤ, |cellMean q k f x|≤allDyadicMaximal q f x := by
  have h := monotoneMaximal_energy volume
    (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f)
    (4*∫ x, (f x)^2) (mul_nonneg (by norm_num) (integral_nonneg (fun x => sq_nonneg (f x))))
    (fun N => dyadicMaximal_measurable q N (2*N) f)
    (fun N x => dyadicMaximal_nonneg q N (2*N) f x)
    (dyadicWindow_mono q f)
    (fun N => (dyadicMaximal_energy q N (2*N) hf).1)
    (fun N => (dyadicMaximal_energy q N (2*N) hf).2)
  refine ⟨h.1,h.2.1,?_⟩
  filter_upwards [h.2.2] with x hx
  intro k
  exact (cellMean_le_window q k f x).trans (hx k.natAbs)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem gridChoice_card : Fintype.card GridChoice=3 := by
  simp [GridChoice]

theorem threeGridMaximal_nonneg (f : ℝ → ℝ) (x : ℝ) :
    0≤threeGridMaximal f x :=
  Finset.sum_nonneg (fun _ _ => allDyadicMaximal_nonneg _ _ _)

theorem threeGridMaximal_measurable (f : ℝ → ℝ) : Measurable (threeGridMaximal f) :=
  Finset.measurable_sum _ (fun _ _ => allDyadicMaximal_measurable _ _)

theorem allDyadicMaximal_le_three (q : GridChoice) (f : ℝ → ℝ) (x : ℝ) :
    allDyadicMaximal q.val f x≤threeGridMaximal f x :=
  Finset.single_le_sum (fun _ _ => allDyadicMaximal_nonneg _ _ _) (Finset.mem_univ q)

theorem threeGridMaximal_energy {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (threeGridMaximal f) 2 volume ∧
    (∫ x, (threeGridMaximal f x)^2)≤36*∫ x, (f x)^2 := by
  have hq (q : GridChoice) := allDyadicMaximal_energy q.val hf
  have hm : MemLp (threeGridMaximal f) 2 volume :=
    memLp_finsetSum Finset.univ (fun q _ => (hq q).1)
  have he := weighted_integral_sum_square volume
    (fun q : GridChoice => allDyadicMaximal q.val f) (fun q => (hq q).1)
    (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,
    gridChoice_card,nsmul_eq_mul,mul_one] at he
  refine ⟨hm,he.trans ?_⟩
  calc
    _ ≤ 3*∑ q : GridChoice, (4*∫ x, (f x)^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => (hq q).2.1)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; ring

/-- All real intervals containing a point are controlled simultaneously,
not merely an a.e. set chosen separately for each interval. -/
theorem interval_average_le_threeGridMaximal {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hf0 : ∀ x, 0≤f x) :
    ∀ᵐ x ∂volume, ∀ c r : ℝ, 0 < r → x∈Icc (c-r) (c+r) →
      (∫ y in Icc (c-r) (c+r), f y)/(2*r)≤6*threeGridMaximal f x := by
  have hdom : ∀ᵐ x ∂volume, ∀ q : GridChoice, ∀ k : ℤ,
      |cellMean q.val k f x|≤allDyadicMaximal q.val f x :=
    ae_all_iff.mpr (fun q => (allDyadicMaximal_energy q.val hf).2.2)
  filter_upwards [hdom] with x hx
  intro c r hr hxc
  obtain ⟨q,hq,k,j,hsub,hscale⟩ := exists_comparable_three_grid_cover c r hr
  let Q : GridChoice := ⟨q,hq⟩
  have hxcell := hsub hxc
  have hint : IntegrableOn f (cell q k j) :=
    (show MemLp f 2 (rootMeasure q k j) from hf.restrict _).integrable (by norm_num)
  have hI : (∫ y in Icc (c-r) (c+r), f y)≤∫ y in cell q k j, f y :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hsub)
  have heq : (∫ y in cell q k j, f y)=scale k*cellMean q k f x := by
    unfold cellMean
    rw [index_eq_of_mem hxcell]
    field_simp [(scale_pos k).ne']
  have hmean : cellMean q k f x≤threeGridMaximal f x :=
    (le_abs_self _).trans ((hx Q k).trans (allDyadicMaximal_le_three Q f x))
  apply (div_le_iff₀ (by positivity : 0<2*r)).mpr
  calc
    _ ≤ scale k*cellMean q k f x := hI.trans_eq heq
    _ ≤ scale k*threeGridMaximal f x := mul_le_mul_of_nonneg_left hmean (scale_pos k).le
    _ ≤ (12*r)*threeGridMaximal f x :=
      mul_le_mul_of_nonneg_right hscale (threeGridMaximal_nonneg f x)
    _ = _ := by ring

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual low-pass convolution is dominated, uniformly over centers
in a cell, by the existing three-grid maximal function. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem integral_reflected_interval (f : ℝ → ℝ) (x r : ℝ) :
    (∫ t in Icc (-r) r, f (x-t))=∫ z in Icc (x-r) (x+r), f z := by
  rw [←integral_indicator measurableSet_Icc,←integral_indicator measurableSet_Icc]
  have h := integral_sub_left_eq_self ((Icc (x-r) (x+r)).indicator f) volume x
  rw [←h]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : (x-t∈Icc (x-r) (x+r))↔t∈Icc (-r) r := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  by_cases ht : t∈Icc (-r) r
  · simp only [indicator_of_mem ht,indicator_of_mem (he.mpr ht)]
  · simp only [indicator_of_notMem ht,indicator_of_notMem (mt he.mp ht)]

theorem lineProjectionKernel_maximal (q : SchwartzMap ℝ ℂ)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    ∀ᵐ y ∂volume, ∀ W L x : ℝ, ∀ (hW : 0<W), 0≤L → |x-y|≤L →
      ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖≤
        60*lineKernelDecayConstant q*(1+L/W)*threeGridMaximal (fun z => ‖f z‖) y := by
  have hmax := interval_average_le_threeGridMaximal hf.norm (fun _ => norm_nonneg _)
  filter_upwards [hmax] with y hy
  intro W L x hW hL hxy
  let M := threeGridMaximal (fun z => ‖f z‖) y
  have hM : 0≤M := threeGridMaximal_nonneg _ _
  have hR : 0<W+L := by linarith
  have hmean (r : ℝ) (hr : W+L ≤ r) : (∫ t in Icc (-r) r, ‖f (x-t)‖)≤12*r*M := by
    rw [integral_reflected_interval (fun z => ‖f z‖) x r]
    have hrr : 0 < r := hR.trans_le hr
    have hyI : y∈Icc (x-r) (x+r) := by
      obtain ⟨h1,h2⟩ := abs_le.mp hxy
      exact ⟨by linarith,by linarith⟩
    have h := hy x r hrr hyI
    exact (div_le_iff₀ (by positivity : 0<2*r)).mp h |>.trans_eq (by dsimp [M]; ring)
  have hk := kernel_average_bound (lineProjectionKernel q W hW.ne') f
    (lineProjectionKernel q W hW.ne').integrable hfm B hfb
    (lineKernelDecayConstant q/W) (lineKernelDecayConstant q*W) (W+L) M x
    (div_nonneg (lineKernelDecayConstant_nonneg q) hW.le)
    (mul_nonneg (lineKernelDecayConstant_nonneg q) hW.le) hR hM
    (fun t => (lineProjectionKernel_decay q W hW t).1)
    (fun t => (lineProjectionKernel_decay q W hW t).2) hmean
  apply hk.trans
  have hratio : W/(W+L)≤(W+L)/W := by
    apply (div_le_div_iff₀ hR hW).mpr
    nlinarith
  calc
    _ = 12*lineKernelDecayConstant q*((W+L)/W)*M+
        48*lineKernelDecayConstant q*(W/(W+L))*M := by ring
    _ ≤ 12*lineKernelDecayConstant q*((W+L)/W)*M+
        48*lineKernelDecayConstant q*((W+L)/W)*M := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) (lineKernelDecayConstant_nonneg q))) hM)
    _ = _ := by field_simp; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLowpassCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform cellwise bounds for a smooth projection at any fixed ratio
between its physical scale and the cell length. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem lineCellMaximalConstant_nonneg (q : SchwartzMap ℝ ℂ) (ratio : ℝ) (hratio : 0 < ratio) :
    0≤lineCellMaximalConstant q ratio :=
  mul_nonneg (mul_nonneg (by norm_num) (lineKernelDecayConstant_nonneg q)) (by positivity)

theorem cell_abs_sub_le (q k i : ℤ) {x y : ℝ}
    (hx : x∈cell q k i) (hy : y∈cell q k i) : |x-y| ≤ scale k := by
  have hwidth : left q k (i+1)-left q k i=scale k := by
    unfold left
    push_cast
    ring
  exact abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩

theorem lineProjection_cell_maximal (q : SchwartzMap ℝ ℂ) (ratio : ℝ) (hratio : 0 < ratio)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    ∀ᵐ y ∂volume, ∀ grid k i : ℤ, y∈cell grid k i → ∀ x∈cell grid k i,
      ‖lineConvolution (lineProjectionKernel q (ratio*scale k) (mul_pos hratio (scale_pos k)).ne') f x‖≤
        lineCellMaximalConstant q ratio*threeGridMaximal (fun z => ‖f z‖) y := by
  filter_upwards [lineProjectionKernel_maximal q f hfm hf B hfb] with y hy
  intro grid k i hycell x hxcell
  have h := hy (ratio*scale k) (scale k) x (mul_pos hratio (scale_pos k)) (scale_pos k).le
    (cell_abs_sub_le grid k i hxcell hycell)
  have he : scale k/(ratio*scale k)=1/ratio := by field_simp [(scale_pos k).ne']
  simpa only [he,lineCellMaximalConstant] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteSmoothProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson product bound on every finite collection of
actual dyadic cells, with the actual smooth low-pass convolution. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem finite_smooth_product {ι : Type*} [Fintype ι]
    (grid : ℤ) (level pos : ι → ℤ)
    (hinj : ∀ i j, level i=level j → pos i=pos j → i=j)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (ratio : ℝ) (hratio : 0 < ratio) (h : SchwartzMap ℝ ℂ) :
    (∑ i, ∫⁻ x in cell grid (level i) (pos i),
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
        (scale_pos _).ne') f x‖^2)*
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale (level i))
        (mul_pos hratio (scale_pos _)).ne') h x‖^2))≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
  let Q := fun i => cell grid (level i) (pos i)
  let low := fun i => lineConvolution
    (lineProjectionKernel reassemblyLow (ratio*scale (level i)) (mul_pos hratio (scale_pos _)).ne') h
  let E := lineCellMaximalConstant reassemblyLow ratio
  let M := threeGridMaximal (fun x => ‖h x‖)
  let v := fun i => sSup ((fun x => ‖low i x‖) '' Q i)
  have hE : 0≤E := lineCellMaximalConstant_nonneg _ _ hratio
  have hBdd (i : ι) : BddAbove ((fun x => ‖low i x‖) '' Q i) := by
    refine ⟨(∫ t, ‖lineProjectionKernel reassemblyLow (ratio*scale (level i))
      (mul_pos hratio (scale_pos _)).ne' t‖)*SchwartzMap.seminorm ℝ 0 0 h,?_⟩
    rintro _ ⟨x,_,rfl⟩
    exact lineConvolution_bound _ h (lineProjectionKernel _ _ _).integrable _
      (fun x => h.norm_le_seminorm ℝ x) x
  have hne (i : ι) : ((fun x => ‖low i x‖) '' Q i).Nonempty :=
    (cell_nonempty grid (level i) (pos i)).image _
  have hv (i : ι) : 0≤v i := by
    obtain ⟨x,hx⟩ := cell_nonempty grid (level i) (pos i)
    exact (norm_nonneg (low i x)).trans (le_csSup (hBdd i) ⟨x,hx,rfl⟩)
  have hlow (i : ι) (x : ℝ) (hx : x∈Q i) : ‖low i x‖≤v i :=
    le_csSup (hBdd i) ⟨x,hx,rfl⟩
  have hmax := lineProjection_cell_maximal reassemblyLow ratio hratio h h.continuous.measurable
    (h.memLp 2 volume) (SchwartzMap.seminorm ℝ 0 0 h) (fun x => h.norm_le_seminorm ℝ x)
  have hvM (i : ι) : ∀ᵐ x ∂volume.restrict (Q i), v i≤E*M x := by
    filter_upwards [ae_restrict_of_ae hmax,ae_restrict_mem (cell_measurable grid (level i) (pos i))] with x hx hxQ
    apply csSup_le (hne i)
    rintro _ ⟨y,hy,rfl⟩
    exact hx grid (level i) (pos i) hxQ y hy
  have hbound := dyadic_smooth_product_embedding grid level pos hinj f hfm B hB hfb
    low v hv (fun x => E*M x) ((threeGridMaximal_measurable _).const_mul E) hlow hvM
  apply hbound.trans
  have hm := threeGridMaximal_energy (h.memLp 2 volume).norm
  have he : (∫⁻ x, ENNReal.ofReal ((E*M x)^2))=
      ENNReal.ofReal E^2*(∫⁻ x, ENNReal.ofReal (M x^2)) := by
    simp_rw [mul_pow,ENNReal.ofReal_mul (sq_nonneg E),ENNReal.ofReal_pow hE]
    exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [he]
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  rw [←ofReal_integral_eq_lintegral_ofReal hm.1.integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg (M x)))]
  exact ENNReal.ofReal_le_ofReal hm.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothCarlesonEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth Carleson product estimate on every finite frequency
range. The countable spatial partition introduces no constant or cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem smooth_carleson_estimate (I : Finset ℤ)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (ratio : ℝ) (hratio : 0 < ratio) (h : SchwartzMap ℝ ℂ) :
    (∑ k∈I, ∫⁻ x,
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale k)
        (scale_pos _).ne') f x‖^2)*
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale k)
        (mul_pos hratio (scale_pos _)).ne') h x‖^2))≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
  classical
  let w := fun k x =>
    ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale k)
      (scale_pos _).ne') f x‖^2)*
    ENNReal.ofReal (‖lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale k)
      (mul_pos hratio (scale_pos _)).ne') h x‖^2)
  let a := fun p : I×ℤ => ∫⁻ x in cell 0 p.1.val p.2, w p.1.val x
  have hfinite (F : Finset (I×ℤ)) : (∑ p∈F, a p)≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
    have hh := finite_smooth_product 0 (fun p : F => p.val.1.val) (fun p : F => p.val.2)
      (by
        intro p q hp hq
        apply Subtype.ext
        exact Prod.ext (Subtype.ext hp) hq)
      f hfm B hB hfb ratio hratio h
    change (∑ p : F, a p.val)≤_ at hh
    rw [Finset.sum_coe_sort] at hh
    exact hh
  have hall : (∑' p, a p)≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hfinite
  have hpartition (k : ℤ) : (∑' j, ∫⁻ x in cell 0 k j, w k x)=∫⁻ x, w k x := by
    have he : (⋃ j : ℤ, cell 0 k j)=(univ : Set ℝ) := by
      apply Set.eq_univ_of_forall
      intro x
      exact mem_iUnion.mpr ⟨index 0 k x,mem_index_cell 0 k x⟩
    have hh := lintegral_iUnion (μ:=volume) (f:=w k) (cell_measurable 0 k)
      (fun i j hij => cells_disjoint 0 k hij)
    rw [he,Measure.restrict_univ] at hh
    exact hh.symm
  have he : (∑' p, a p)=∑ k∈I, ∫⁻ x, w k x := by
    rw [ENNReal.tsum_prod']
    simp only [a,hpartition,tsum_fintype]
    exact Finset.sum_coe_sort I (fun k => ∫⁻ x, w k x)
  rw [he] at hall
  exact hall

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothCarlesonEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson estimate in real squared L2 energy, for the
actual high/low convolution products. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem smoothDyadicProduct_measurable (f : ℝ → ℂ) (hfm : Measurable f)
    (h : SchwartzMap ℝ ℂ) (ratio : ℝ) (hratio : 0 < ratio) (k : ℤ) :
    Measurable (smoothDyadicProduct f h ratio hratio k) :=
  (lineConvolution_measurable _ (lineProjectionKernel _ _ _).continuous.measurable f hfm).mul
    (lineConvolution_measurable _ (lineProjectionKernel _ _ _).continuous.measurable h h.continuous.measurable)

theorem smoothDyadicProduct_energy_eq (f : ℝ → ℂ) (h : SchwartzMap ℝ ℂ)
    (ratio : ℝ) (hratio : 0 < ratio) (k : ℤ) :
    (∫⁻ x, ENNReal.ofReal (‖smoothDyadicProduct f h ratio hratio k x‖^2))=
      ∫⁻ x, ENNReal.ofReal (‖lineConvolution
        (lineProjectionKernel dyadicDifference (scale k) (scale_pos _).ne') f x‖^2)*
      ENNReal.ofReal (‖lineConvolution
        (lineProjectionKernel reassemblyLow (ratio*scale k) (mul_pos hratio (scale_pos _)).ne') h x‖^2) := by
  apply lintegral_congr
  intro x
  simp only [smoothDyadicProduct,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]

theorem smooth_carleson_energy (I : Finset ℤ)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (ratio : ℝ) (hratio : 0 < ratio) (h : SchwartzMap ℝ ℂ) :
    (∀ k∈I, MemLp (smoothDyadicProduct f h ratio hratio k) 2 volume) ∧
    (∑ k∈I, ∫ x, ‖smoothDyadicProduct f h ratio hratio k x‖^2)≤
      36*dyadicCarlesonConstant*(lineCellMaximalConstant reassemblyLow ratio)^2*B^2*
        (∫ x, ‖h x‖^2) := by
  let E := lineCellMaximalConstant reassemblyLow ratio
  let C := 36*dyadicCarlesonConstant*E^2*B^2*(∫ x, ‖h x‖^2)
  have hE : 0≤E := lineCellMaximalConstant_nonneg _ _ hratio
  have hCb : 0≤dyadicCarlesonConstant*B^2 :=
    mul_nonneg dyadicCarlesonConstant_pos.le (sq_nonneg B)
  have hC : 0≤C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      dyadicCarlesonConstant_pos.le) (sq_nonneg E)) (sq_nonneg B))
      (integral_nonneg (fun _ => sq_nonneg _))
  have hg := smooth_carleson_estimate I f hfm B hB hfb ratio hratio h
  have hrhs : ENNReal.ofReal (dyadicCarlesonConstant*B^2)*ENNReal.ofReal E^2*
      ENNReal.ofReal (36*(∫ x, ‖h x‖^2))=ENNReal.ofReal C := by
    rw [←ENNReal.ofReal_pow hE,←ENNReal.ofReal_mul hCb,
      ←ENNReal.ofReal_mul (mul_nonneg hCb (sq_nonneg E))]
    congr 1
    dsimp [C]
    ring
  change (∑ k∈I, _)≤ENNReal.ofReal (dyadicCarlesonConstant*B^2)*ENNReal.ofReal E^2*
    ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) at hg
  rw [hrhs] at hg
  simp_rw [←smoothDyadicProduct_energy_eq f h ratio hratio] at hg
  have hi (k : ℤ) (hk : k∈I) : Integrable (fun x => ‖smoothDyadicProduct f h ratio hratio k x‖^2) := by
    have hfin : (∫⁻ x, ENNReal.ofReal (‖smoothDyadicProduct f h ratio hratio k x‖^2))≠⊤ :=
      ne_of_lt ((Finset.single_le_sum (fun _ _ => bot_le) hk).trans_lt
        (hg.trans_lt ENNReal.ofReal_lt_top))
    have hm := ((smoothDyadicProduct_measurable f hfm h ratio hratio k).norm.pow_const 2).ennreal_ofReal
    have hh := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh
  constructor
  · intro k hk
    exact (memLp_two_iff_integrable_sq_norm
      (smoothDyadicProduct_measurable f hfm h ratio hratio k).aestronglyMeasurable).mpr (hi k hk)
  · have he : (∑ k∈I, ENNReal.ofReal (∫ x, ‖smoothDyadicProduct f h ratio hratio k x‖^2))=
        ∑ k∈I, ∫⁻ x, ENNReal.ofReal (‖smoothDyadicProduct f h ratio hratio k x‖^2) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact ofReal_integral_eq_lintegral_ofReal (hi k hk) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    rw [←he,←ENNReal.ofReal_sum_of_nonneg (fun k _ => integral_nonneg (fun _ => sq_nonneg _))] at hg
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
    simpa only [ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))] using ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSchwartzPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Self-adjoint low-pass projections and the product pairing used in
the actual smooth Carleson synthesis estimate. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_inner (q : SchwartzMap ℝ ℂ)
    (hq : ∀ eta, conj (q eta)=q eta) (W : ℝ) (hW : W≠0) (f g : SchwartzMap ℝ ℂ) :
    inner ℂ ((lineSchwartzProjection q W hW f).toLp 2 volume) (g.toLp 2 volume)=
      inner ℂ (f.toLp 2 volume) ((lineSchwartzProjection q W hW g).toLp 2 volume) := by
  calc
    _ = ∫ x, inner ℂ (lineSchwartzProjection q W hW f x) (g x) :=
      memLp_inner_integral volume _ _ ((lineSchwartzProjection q W hW f).memLp 2 volume) (g.memLp 2 volume)
    _ = ∫ eta, inner ℂ ((𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ) eta)
        ((𝓕 g : SchwartzMap ℝ ℂ) eta) := (SchwartzMap.integral_inner_fourier_fourier _ _).symm
    _ = ∫ eta, inner ℂ ((𝓕 f : SchwartzMap ℝ ℂ) eta)
        ((𝓕 (lineSchwartzProjection q W hW g) : SchwartzMap ℝ ℂ) eta) := by
      apply integral_congr_ae
      filter_upwards [] with eta
      simp only [lineSchwartzProjection_fourier,RCLike.inner_apply,map_mul,hq]
      ring
    _ = ∫ x, inner ℂ (f x) (lineSchwartzProjection q W hW g x) :=
      SchwartzMap.integral_inner_fourier_fourier _ _
    _ = _ := (memLp_inner_integral volume _ _ (f.memLp 2 volume)
      ((lineSchwartzProjection q W hW g).memLp 2 volume)).symm

theorem reassemblyLow_conj (eta : ℝ) : conj (reassemblyLow eta)=reassemblyLow eta := by
  simp only [reassemblyLow_apply,Complex.conj_ofReal]

theorem lineLowpass_absorb (f : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (hband : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |W*eta|≤1) :
    lineSchwartzProjection reassemblyLow W hW f=f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection reassemblyLow W hW f)) eta=(𝓕 f) eta
  rw [lineSchwartzProjection_fourier]
  by_cases hz : (𝓕 f : SchwartzMap ℝ ℂ) eta=0
  · rw [hz,mul_zero]
  · rw [reassemblyLow_one _ (hband eta hz),one_mul]

theorem lineSchwartzProduct_inner_bound (p g f : SchwartzMap ℝ ℂ) :
    ‖inner ℂ ((lineSchwartzProduct p g).toLp 2 volume) (f.toLp 2 volume)‖≤
      ‖g.toLp 2 volume‖*Real.sqrt (∫ x, ‖lineSchwartzProduct p f x‖^2) := by
  let q : ℝ → ℂ := fun x => conj (p x)*f x
  have hqnorm (x : ℝ) : ‖q x‖=‖lineSchwartzProduct p f x‖ := by
    simp only [q,lineSchwartzProduct_apply,norm_mul,RCLike.norm_conj]
  have hq : MemLp q 2 volume := ((lineSchwartzProduct p f).memLp 2 volume).of_le
    (by dsimp [q]; fun_prop) (Filter.Eventually.of_forall fun x => (hqnorm x).le)
  have he : inner ℂ ((lineSchwartzProduct p g).toLp 2 volume) (f.toLp 2 volume)=
      inner ℂ (g.toLp 2 volume) (hq.toLp q) := by
    calc
      _ = ∫ x, inner ℂ (lineSchwartzProduct p g x) (f x) :=
        memLp_inner_integral volume _ _ ((lineSchwartzProduct p g).memLp 2 volume) (f.memLp 2 volume)
      _ = ∫ x, inner ℂ (g x) (q x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [lineSchwartzProduct_apply,RCLike.inner_apply,map_mul,q]
        ring
      _ = _ := (memLp_inner_integral volume _ _ (g.memLp 2 volume) hq).symm
  have hnorm : ‖hq.toLp q‖=Real.sqrt (∫ x, ‖lineSchwartzProduct p f x‖^2) := by
    have hh := memLp_toL2_norm_sq volume q hq
    simp_rw [hqnorm] at hh
    rw [←hh,Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  simpa only [hnorm] using norm_inner_le_norm (𝕜:=ℂ) (g.toLp 2 volume) (hq.toLp q)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothCarlesonSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Duality turns the proved smooth Carleson analysis bound into the
actual finite paraproduct synthesis bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem smoothCarlesonDualConstant_nonneg : 0 ≤ smoothCarlesonDualConstant := by
  unfold smoothCarlesonDualConstant
  exact mul_nonneg (mul_nonneg (by norm_num) dyadicCarlesonConstant_pos.le) (sq_nonneg _)

theorem dyadicParaproduct_lowpass (b h : SchwartzMap ℝ ℂ) (k : ℤ)
    (hh : ∀ eta, (𝓕 h : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    let p := lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b
    lineSchwartzProjection reassemblyLow ((1/128)*scale k) (by have := scale_pos k; positivity)
      (lineSchwartzProduct p h)=lineSchwartzProduct p h := by
  intro p
  apply lineLowpass_absorb
  intro eta heta
  have hp := dyadicProjection_frequency (scale k) (scale_pos k) b
  have hg := lineSchwartzProduct_band p h ((13/6)/scale k) (64/scale k)
    (fun x hx => (hp x hx).2) hh eta heta
  have hs := (scale_pos k)
  have hu : scale k*|eta|≤13/6+64 := by
    have hmul := mul_le_mul_of_nonneg_left hg hs.le
    field_simp [hs.ne'] at hmul
    nlinarith only [hmul]
  rw [abs_mul,abs_of_pos (by positivity : (0:ℝ)<(1/128)*scale k)]
  nlinarith

theorem smooth_carleson_synthesis (I : Finset ℤ) (b : SchwartzMap ℝ ℂ)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B) (H : ℤ → SchwartzMap ℝ ℂ)
    (hH : ∀ k∈I, ∀ eta, (𝓕 (H k) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    (∫ x, ‖dyadicParaproduct I b H x‖^2)≤
      smoothCarlesonDualConstant*B^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
  let F := dyadicParaproduct I b H
  let P := fun k => lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b
  let Q := fun k => lineSchwartzProjection reassemblyLow ((1/128)*scale k)
    (by have := scale_pos k; positivity) F
  let G := fun k => lineSchwartzProduct (P k) (Q k)
  let D := smoothCarlesonDualConstant*B^2
  let E := ∑ k∈I, ∫ x, ‖H k x‖^2
  have hD : 0≤D := mul_nonneg smoothCarlesonDualConstant_nonneg (sq_nonneg B)
  have hE : 0≤E := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hFnorm : ‖F.toLp 2 volume‖^2=∫ x, ‖F x‖^2 :=
    memLp_toL2_norm_sq volume F (F.memLp 2 volume)
  have hnorm (f : SchwartzMap ℝ ℂ) : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 :=
    memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  have hsumH : (∑ k∈I, ‖(H k).toLp 2 volume‖^2)=E :=
    Finset.sum_congr rfl (fun k _ => hnorm (H k))
  have hG : (∑ k∈I, ‖(G k).toLp 2 volume‖^2)≤D*‖F.toLp 2 volume‖^2 := by
    have hc := (smooth_carleson_energy I b b.continuous.measurable B hB hb (1/128) (by norm_num) F).2
    have he (k : ℤ) (x : ℝ) : G k x=smoothDyadicProduct b F (1/128) (by norm_num) k x := by
      dsimp [G,P,Q]
      simp only [lineSchwartzProduct_apply,lineSchwartzProjection_eq_convolution,smoothDyadicProduct]
    simpa only [hnorm,he,D,smoothCarlesonDualConstant] using hc
  have hpair (k : ℤ) (hk : k∈I) :
      ‖inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume)‖≤
        ‖(H k).toLp 2 volume‖*‖(G k).toLp 2 volume‖ := by
    have habs := dyadicParaproduct_lowpass b (H k) k (hH k hk)
    have hadj := lineSchwartzProjection_inner reassemblyLow reassemblyLow_conj
      ((1/128)*scale k) (by have := scale_pos k; positivity) (lineSchwartzProduct (P k) (H k)) F
    rw [habs] at hadj
    rw [hadj]
    have hp := lineSchwartzProduct_inner_bound (P k) (H k) (Q k)
    rw [←hnorm (G k),Real.sqrt_sq (norm_nonneg _)] at hp
    exact hp
  have hid : inner ℂ (F.toLp 2 volume) (F.toLp 2 volume)=
      ∑ k∈I, inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume) := by
    have he : F.toLp 2 volume=∑ k∈I, (lineSchwartzProduct (P k) (H k)).toLp 2 volume :=
      map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ I
    rw [he]
    exact sum_inner _ _ _
  have hbound : ‖F.toLp 2 volume‖^2≤Real.sqrt E*Real.sqrt (D*‖F.toLp 2 volume‖^2) := by
    calc
      _ = ‖inner ℂ (F.toLp 2 volume) (F.toLp 2 volume)‖ := by
        simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
      _ = ‖∑ k∈I, inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume)‖ := congrArg norm hid
      _ ≤ ∑ k∈I, ‖inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume)‖ := norm_sum_le _ _
      _ ≤ ∑ k∈I, ‖(H k).toLp 2 volume‖*‖(G k).toLp 2 volume‖ := Finset.sum_le_sum hpair
      _ ≤ Real.sqrt (∑ k∈I, ‖(H k).toLp 2 volume‖^2)*Real.sqrt (∑ k∈I, ‖(G k).toLp 2 volume‖^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt I _ _
      _ ≤ _ := by
        rw [←hsumH]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG)
          (Real.sqrt_nonneg (∑ k∈I, ‖(H k).toLp 2 volume‖^2))
  rw [Real.sqrt_mul hD,Real.sqrt_sq (norm_nonneg _)] at hbound
  have hfinal : ‖F.toLp 2 volume‖^2≤D*E := by
    by_cases hz : ‖F.toLp 2 volume‖=0
    · rw [hz]; simpa only [zero_pow (by decide : 2≠0)] using mul_nonneg hD hE
    · have hpos : 0<‖F.toLp 2 volume‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hn : ‖F.toLp 2 volume‖≤Real.sqrt E*Real.sqrt D := by
        apply (mul_le_mul_iff_right₀ hpos).mp
        nlinarith only [hbound]
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      simpa only [mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hD,mul_comm] using hs
  simpa only [hFnorm,D,E,mul_assoc] using hfinal

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableCommutatorSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full comparable-frequency contribution, with its two product
terms estimated by actual smooth Carleson synthesis. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem schwartzDerivative_lipschitz_bound (b : SchwartzMap ℝ ℂ) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) : 0≤L ∧ ∀ x, ‖schwartzDerivative 1 b x‖≤L := by
  have hL : 0≤L := by
    have hh := hLip 1 0
    norm_num at hh
    exact (norm_nonneg _).trans hh
  refine ⟨hL,fun x => ?_⟩
  change ‖deriv b x‖≤L
  exact norm_deriv_le_of_lip' hL (Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using hLip y x)

theorem lineSchwartz_three_energy (f g h : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(f-g+h) x‖^2)≤3*((∫ x, ‖f x‖^2)+(∫ x, ‖g x‖^2)+(∫ x, ‖h x‖^2)) := by
  have hi (p : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖p x‖^2) :=
    (p.memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ ≤ ∫ x, 3*(‖f x‖^2+‖g x‖^2+‖h x‖^2) := by
      apply integral_mono (hi _) (((hi f).add (hi g)).add (hi h) |>.const_mul 3)
      intro x
      simp only [add_apply,sub_apply]
      change ‖f x-g x+h x‖^2≤3*(‖f x‖^2+‖g x‖^2+‖h x‖^2)
      have ht : ‖f x-g x+h x‖≤‖f x‖+‖g x‖+‖h x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖f x‖-‖g x‖),sq_nonneg (‖f x‖-‖h x‖),sq_nonneg (‖g x‖-‖h x‖)]
    _ = _ := by
      rw [integral_const_mul,
        integral_add (f:=fun x => ‖f x‖^2+‖g x‖^2) (g:=fun x => ‖h x‖^2) ((hi f).add (hi g)) (hi h),
        integral_add (hi f) (hi g)]

theorem lineSchwartzProjection_sum {ι : Type*} (I : Finset ι)
    (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) (f : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzProjection q W hW (∑ i∈I, f i)=∑ i∈I, lineSchwartzProjection q W hW (f i) :=
  map_sum (lineSchwartzProjectionLM q W hW) f I

theorem comparableCommutatorSum_energy_oai (I : Finset ℤ) (m b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) (A L : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|)
    (hH : ∀ k∈I, ∀ eta, (𝓕 (H k) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    (∫ x, ‖(∑ k∈I, lineSchwartzCommutator m
      (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b)
      (schwartzDerivative 1 (H k))) x‖^2)≤
        comparableCommutatorConstant*A^2*L^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
  let T := lineSchwartzProjection m 1 (by norm_num)
  let d := schwartzDerivative 1 b
  let U := ∑ k∈I, comparableDerivativePiece m b H k
  let V := dyadicParaproduct I d (fun k => T (H k))
  let Z := T (dyadicParaproduct I d H)
  let E := ∑ k∈I, ∫ x, ‖H k x‖^2
  obtain ⟨hL,hdb⟩ := schwartzDerivative_lipschitz_bound b L hLip
  have hTH (k : ℤ) (hk : k∈I) (eta : ℝ)
      (heta : (𝓕 (T (H k)) : SchwartzMap ℝ ℂ) eta≠0) : |eta|≤64/scale k :=
    hH k hk eta (lineSchwartzProjection_frequency_of_nonzero m (H k) 1 (by norm_num) eta heta)
  have hTE : (∑ k∈I, ∫ x, ‖T (H k) x‖^2)≤A^2*E := by
    calc
      _ ≤ ∑ k∈I, A^2*(∫ x, ‖H k x‖^2) :=
        Finset.sum_le_sum (fun k _ => lineSchwartzProjection_energy m 1 (by norm_num) A hm (H k))
      _ = _ := (Finset.mul_sum I _ _).symm
  have hV : (∫ x, ‖V x‖^2) ≤ smoothCarlesonDualConstant*L^2*(A^2*E) :=
    (smooth_carleson_synthesis I d L hL hdb (fun k => T (H k)) hTH).trans
      (mul_le_mul_of_nonneg_left hTE (mul_nonneg smoothCarlesonDualConstant_nonneg (sq_nonneg L)))
  have hZ : (∫ x, ‖Z x‖^2)≤A^2*(smoothCarlesonDualConstant*L^2*E) :=
    (lineSchwartzProjection_energy m 1 (by norm_num) A hm _).trans
      (mul_le_mul_of_nonneg_left (smooth_carleson_synthesis I d L hL hdb H hH) (sq_nonneg A))
  have hU := comparableDerivativeSum_energy I m b H A L hm hLip hH
  have he : (∑ k∈I, lineSchwartzCommutator m
      (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b)
      (schwartzDerivative 1 (H k)))=U-V+Z := by
    simp_rw [lineSchwartzCommutator_derivative_identity,lineSchwartzProjection_derivative]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [←lineSchwartzProjection_sum]
    rfl
  rw [he]
  calc
    _ ≤ 3*((∫ x, ‖U x‖^2)+(∫ x, ‖V x‖^2)+(∫ x, ‖Z x‖^2)) := lineSchwartz_three_energy U V Z
    _ ≤ 3*(48*(16384*(A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (52*Real.pi/3)))^2*E+smoothCarlesonDualConstant*L^2*(A^2*E)+
        A^2*(smoothCarlesonDualConstant*L^2*E)) := by
      gcongr
    _ = _ := by dsimp [comparableCommutatorConstant,E]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorSum_energy_oai := @OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorSum_energy_oai
