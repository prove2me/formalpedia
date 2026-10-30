-- Prove2me | solution 1 for OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:38:28.860671+00:00
-- url     : https://prove2.me/submissions/f41ae93e-323c-4181-bc79-f98f12de352e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_annularPVPartial_bound
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_conditional_variable_slope_truncation

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlaneCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure-preserving bridge from the manuscript's real coordinate
pairs to the Euclidean plane used by the published maximal estimate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem planeCoordinates_measurePreserving :
    MeasurePreserving planeCoordinates (volume.prod volume) volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (measurePreserving_finTwoArrow (volume : Measure ℝ)).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier inversion on the actual product plane, and the frozen
multiplier identity for every planar Schwartz input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

theorem planarFourier_integrable (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (planarFourier f) (volume.prod volume) := by
  have h : Integrable (planarFourierSchwartz f : ℝ×ℝ → ℂ) (volume.prod volume) :=
    (planarFourierSchwartz f).integrable
  simpa only [funext (planarFourierSchwartz_apply f)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact modulated convolution kernels for the fixed vertical bin
profiles, with a uniform L1 norm at every width and carrier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem modulatedTimeKernel_fourier (K : ℝ → ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (modulatedTimeKernel K W center) eta=𝓕 K (W*(eta-center)) := by
  rw [←scaledTimeKernel_fourier K W hW (eta-center)]
  rw [Real.fourier_eq,Real.fourier_eq]
  simp only [Real.inner_apply,modulatedTimeKernel]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [←mul_smul,←Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

theorem modulatedTimeKernel_norm (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    ‖modulatedTimeKernel K W center t‖=W⁻¹*‖K (t/W)‖ := by
  rw [modulatedTimeKernel,Circle.norm_smul,scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hW.le]

theorem modulatedTimeKernel_l1 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, ‖modulatedTimeKernel K W center t‖)=∫ t, ‖K t‖ := by
  simp_rw [modulatedTimeKernel_norm K W center _ hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖K t‖) W,
    abs_of_pos hW,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem verticalProfileKernel_fourier (q : SchwartzMap ℝ ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (verticalProfileKernel q W center) eta=q (W*(eta-center)) := by
  rw [verticalProfileKernel,modulatedTimeKernel_fourier _ W center eta hW]
  have h : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q := fourier_fourierInv_eq q
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (W*(eta-center))) h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
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

theorem finiteTimeKernel_measurable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) :
    Measurable (finiteTimeKernel k N topLength) := by
  unfold finiteTimeKernel scaledTimeKernel
  fun_prop

theorem finiteTimeKernel_integrable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) : Integrable (finiteTimeKernel k N topLength) := by
  exact integrable_finsetSum _ (fun j _ => scaledTimeKernel_integrable k k.integrable _
    (ne_of_gt (div_pos htop (pow_pos (by norm_num) j.val))))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarFrequencyPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separated frequency factors are Fourier transforms of actual
Schwartz convolution kernels. Thus the lattice average uses actual packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverseSchwartz_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz F x=planarInverse F x := by
  rw [← planarFourier_inversion (planarInverseSchwartz F) x]
  congr 1
  funext omega
  exact planarInverseSchwartz_fourier F omega

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalInverseMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse-frequency representation of vertical convolution. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem vertical_inverse_multiplier (k : ℝ → ℂ) (F : ℝ×ℝ → ℂ)
    (hk : Integrable k) (hF : Integrable F planeMeasure)
    (x : ℝ×ℝ) :
    verticalConvolution k (planarInverse F) x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) ∂planeMeasure := by
  let phase := fun (t : ℝ) (omega : ℝ×ℝ) =>
    x.1*omega.1+(x.2-t)*omega.2
  let H := fun p : ℝ×(ℝ×ℝ) =>
    (k p.1*F p.2)*(Real.fourierChar (phase p.1 p.2):ℂ)
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (hk.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ×(ℝ×ℝ) =>
        (Real.fourierChar (phase p.1 p.2) : ℂ)) by dsimp [phase]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      exact le_of_eq (Circle.norm_coe _)
  have hleft (t : ℝ) : k t*planarInverse F (x.1,x.2-t) =
      ∫ omega, H (t,omega) ∂planeMeasure := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    change k t*((Real.fourierChar (phase t omega):ℂ)*F omega)=_
    dsimp only [H]
    ring
  have hright (omega : ℝ×ℝ) : (∫ t, H (t,omega)) =
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.2)*F omega) := by
    rw [Real.fourier_eq]
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    have hp : phase t omega=(x.1*omega.1+x.2*omega.2)+(-(t*(omega.2))) := by
      dsimp [phase]
      ring
    rw [hp, Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  calc
    _ = ∫ t, ∫ omega, H (t,omega) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ omega, (∫ t, H (t,omega) ∂volume) ∂planeMeasure := integral_integral_swap hH
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)


theorem schwartz_vertical_multiplier (K : ℝ → ℂ) (hK : Integrable K)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K f z=
      planarInverse (fun omega => 𝓕 K omega.2*planarFourier f omega) z := by
  have h := vertical_inverse_multiplier K (planarFourier f) hK (planarFourier_integrable f) z
  simpa only [funext (planarFourier_inversion f),planarInverse] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzVerticalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical frequency cutoffs preserve the actual planar Schwartz class. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_eq_convolution (q : SchwartzMap ℝ ℂ) (W center : ℝ)
    (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    schwartzVerticalProjection q W center f z=
      verticalConvolution (verticalProfileKernel q W center) f z := by
  rw [schwartz_vertical_multiplier (verticalProfileKernel q W center)
    (modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW)]
  simp_rw [verticalProfileKernel_fourier q W center _ hW]
  rw [schwartzVerticalProjection,planarInverseSchwartz_apply]
  congr 1
  funext omega
  rw [SchwartzMap.smulLeftCLM_apply_apply (verticalProfile_temperate q W center),
    planarFourierSchwartz_apply,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeErrorEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized integrable envelope for the two endpoint errors in a
sharp time truncation. Its integral is independent of its radius. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem timeErrorEnvelope_nonneg (r t : ℝ) (hr : 0 < r) : 0≤timeErrorEnvelope r t := by
  unfold timeErrorEnvelope
  positivity

theorem timeErrorEnvelope_eq (r t : ℝ) (hr : 0 < r) :
    timeErrorEnvelope r t=r⁻¹*lineEnvelope 0 r 1 t := by
  unfold timeErrorEnvelope lineEnvelope
  simp only [sub_zero,pow_one]
  have hden : r^2+t^2≠0 := ne_of_gt (by positivity)
  have hden' : 1+(t/r)^2≠0 := ne_of_gt (by positivity)
  field_simp

theorem timeErrorEnvelope_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (timeErrorEnvelope r) := by
  have h := (integrable_lineEnvelope_one 0 r hr).const_mul r⁻¹
  simpa only [←timeErrorEnvelope_eq r _ hr] using h

theorem timeErrorEnvelope_integral (r : ℝ) (hr : 0 < r) :
    (∫ t, timeErrorEnvelope r t)=Real.pi := by
  simp_rw [timeErrorEnvelope_eq r _ hr]
  rw [integral_const_mul,integral_lineEnvelope_one 0 r hr]
  field_simp

theorem timeErrorEnvelope_small (r t : ℝ) (hr : 0 < r) (ht : |t| ≤ r) :
    r⁻¹≤2*timeErrorEnvelope r t := by
  have ht2 : t^2 ≤ r^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ (abs_nonneg t) ht 2]
  have hd : 0 < r^2+t^2 := by positivity
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hd).2
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hr).2
  nlinarith

theorem timeErrorEnvelope_large (r t : ℝ) (hr : 0 < r) (ht : r≤|t|) :
    r/t^2≤2*timeErrorEnvelope r t := by
  have ht2 : r^2≤t^2 := by nlinarith [sq_abs t,pow_le_pow_left₀ hr.le ht 2]
  have hd : 0 < r^2+t^2 := by positivity
  have htpos : 0<t^2 := lt_of_lt_of_le (sq_pos_of_pos hr) ht2
  unfold timeErrorEnvelope
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ htpos hd).2
  nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicKernelTelescoping
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact telescoping identity behind the finite Hilbert time-kernel
decomposition. The cutoff profile will be constructed independently. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finiteTimeKernel_telescope (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) :
    (t : ℂ)*finiteTimeKernel k N topLength t=
      a ((2:ℝ)^N*t/(2*topLength))-a (t/(2*topLength)) := by
  have hterm (j : Fin N) : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
      a ((2:ℝ)^(j.val+1)*t/(2*topLength))-a ((2:ℝ)^j.val*t/(2*topLength)) := by
    have hl : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
    have heq : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
        ((t/(topLength/(2:ℝ)^j.val) : ℝ) : ℂ)*k (t/(topLength/(2:ℝ)^j.val)) := by
      unfold scaledTimeKernel
      push_cast
      ring
    rw [heq,hprofile]
    have harg : t/(topLength/(2:ℝ)^j.val)=(2:ℝ)^(j.val+1)*t/(2*topLength) := by
      rw [pow_succ]
      field_simp
    have hhalf : (t/(topLength/(2:ℝ)^j.val))/2=(2:ℝ)^j.val*t/(2*topLength) := by
      field_simp
    rw [harg]
    congr 1
    rw [←harg,hhalf]
  unfold finiteTimeKernel
  rw [Finset.mul_sum]
  simp_rw [hterm]
  change (∑ j : Fin N, (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) j.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) N]
  simpa only [pow_zero,one_mul] using
    Finset.sum_range_sub (fun n : ℕ => a ((2:ℝ)^n*t/(2*topLength))) N

theorem finiteTimeKernel_eq_profileDifference (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) (ht : t≠0) :
    finiteTimeKernel k N topLength t=
      profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t := by
  have h := finiteTimeKernel_telescope k a hprofile N topLength htop t
  have harg : t/(2*topLength/(2:ℝ)^N)=(2:ℝ)^N*t/(2*topLength) := by field_simp
  unfold profileKernelDifference
  rw [harg]
  apply (eq_div_iff (by exact_mod_cast ht : (t:ℂ)≠0)).2
  simpa only [mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint envelopes control sharp truncation versus a telescoped
kernel. The profile conditions are local construction obligations. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem profile_far_bound (a : ℝ → ℂ) (D : ℝ)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r t : ℝ) (hr : 0 < r) (ht : t≠0) :
    ‖a (t/r)‖≤D*r/|t| := by
  have hf : ‖a (t/r)‖*|t|/r≤D := by
    simpa only [abs_div,abs_of_pos hr,div_mul_eq_mul_div,mul_comm] using hfar (t/r)
  apply (le_div_iff₀ (abs_pos.mpr ht)).2
  exact (div_le_iff₀ hr).1 hf

theorem sharpKernelComparison_pointwise (a : ℝ → ℂ) (D : ℝ) (hD : 0≤D)
    (hnear : ∀ s, ‖a s+1‖≤D*|s|) (hfar : ∀ s, |s| *‖a s‖≤D)
    (r R : ℝ) (hr : 0 < r) (hrR : r≤R) (t : ℝ) :
    ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖≤
      4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) := by
  have hR : 0<R := hr.trans_le hrR
  have hqr := timeErrorEnvelope_nonneg r t hr
  have hqR := timeErrorEnvelope_nonneg R t hR
  by_cases ht0 : t=0
  · subst t
    have hs : ¬(r < |(0:ℝ)| ∧ |(0:ℝ)| < R) := by simp [not_lt_of_ge hr.le]
    simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,
      Complex.ofReal_zero,div_zero,sub_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hD) (add_nonneg hqr hqR)
  have ht : 0 < |t| := abs_pos.mpr ht0
  have hnear_r : ‖a (t/r)+1‖≤D*(|t|/r) := by
    simpa only [abs_div,abs_of_pos hr] using hnear (t/r)
  have hnear_R : ‖a (t/R)+1‖≤D*(|t|/R) := by
    simpa only [abs_div,abs_of_pos hR] using hnear (t/R)
  have hfar_r := profile_far_bound a D hfar r t hr ht0
  have hfar_R := profile_far_bound a D hfar R t hR ht0
  by_cases hlo : |t| ≤ r
  · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; linarith [h.1]
    have hnum : ‖a (t/r)-a (t/R)‖≤2*D*|t|/r := by
      have hn := norm_sub_le (a (t/r)+1) (a (t/R)+1)
      have hdiff : (a (t/r)+1)-(a (t/R)+1)=a (t/r)-a (t/R) := by ring
      rw [hdiff] at hn
      have hdiv := div_le_div_of_nonneg_left ht.le hr hrR
      calc
        _ ≤ D*(|t|/r)+D*(|t|/r) := hn.trans
          (add_le_add hnear_r (hnear_R.trans (mul_le_mul_of_nonneg_left hdiv hD)))
        _ = _ := by ring
    calc
      _ = ‖a (t/r)-a (t/R)‖/|t| := by
        simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
          norm_div,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ (2*D*|t|/r)/|t| := div_le_div_of_nonneg_right hnum ht.le
      _ = 2*D*r⁻¹ := by field_simp
      _ ≤ 4*D*timeErrorEnvelope r t := by
        have h := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small r t hr hlo) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
        nlinarith only [h]
      _ ≤ _ := by nlinarith only [mul_nonneg hD hqR]
  · have htr : r < |t| := lt_of_not_ge hlo
    by_cases hhi : |t| < R
    · have hnum : ‖1-a (t/r)+a (t/R)‖≤D*r/|t|+D*(|t|/R) := by
        have heq : (1:ℂ)-a (t/r)+a (t/R)=(-a (t/r))+(a (t/R)+1) := by ring
        rw [heq]
        exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hfar_r) hnear_R)
      have hform : sharpTimeKernel r R t-profileKernelDifference a r R t=
          ((1:ℂ)-a (t/r)+a (t/R))/(t : ℂ) := by
        have hs : r < |t| ∧ |t| < R := ⟨htr,hhi⟩
        simp only [sharpTimeKernel,ite_eq_left hs,profileKernelDifference]
        field_simp
        ring
      calc
        _ = ‖1-a (t/r)+a (t/R)‖/|t| := by rw [hform,norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (D*r/|t|+D*(|t|/R))/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = D*(r/t^2)+D*R⁻¹ := by rw [←sq_abs t]; field_simp
        _ ≤ 2*D*timeErrorEnvelope r t+2*D*timeErrorEnvelope R t := by
          have hrb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_large r t hr htr.le) hD
          have hRb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small R t hR hhi.le) hD
          nlinarith only [hrb,hRb]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr,mul_nonneg hD hqR]
    · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; exact hhi h.2
      have hnum : ‖a (t/r)-a (t/R)‖≤2*D*R/|t| := by
        have h := (norm_sub_le _ _).trans (add_le_add hfar_r hfar_R)
        have hmon := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrR hD) ht.le
        calc
          _ ≤ D*R/|t|+D*R/|t| := h.trans (add_le_add hmon (le_refl _))
          _ = _ := by ring
      calc
        _ = ‖a (t/r)-a (t/R)‖/|t| := by
          simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
            norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (2*D*R/|t|)/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = 2*D*(R/t^2) := by rw [←sq_abs t]; field_simp
        _ ≤ 4*D*timeErrorEnvelope R t := by
          have h := mul_le_mul_of_nonneg_left
            (timeErrorEnvelope_large R t hR (le_of_not_gt hhi)) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
          nlinarith only [h]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr]

end LipschitzHilbert.PacketRepresentation

namespace LipschitzHilbert.PacketRepresentation

theorem sharpKernelComparison_integral (a : ℝ → ℂ) (ha : Measurable a)
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r R : ℝ) (hr : 0 < r) (hrR : r≤R) :
    Integrable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖)≤8*Real.pi*D := by
  have hR := hr.trans_le hrR
  have hi := ((timeErrorEnvelope_integrable r hr).add
    (timeErrorEnvelope_integrable R hR)).const_mul (4*D)
  have hm : Measurable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) := by
    apply (sharpTimeKernel_measurable r R).sub
    unfold profileKernelDifference
    exact ((ha.comp (by fun_prop)).sub (ha.comp (by fun_prop))).div (by fun_prop)
  have hb (t : ℝ) := sharpKernelComparison_pointwise a D hD hnear hfar r R hr hrR t
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) :=
      integral_mono he.norm hi hb
    _ = 8*Real.pi*D := by
      rw [integral_const_mul,integral_add (timeErrorEnvelope_integrable r hr)
        (timeErrorEnvelope_integrable R hR),timeErrorEnvelope_integral r hr,
        timeErrorEnvelope_integral R hR]
      ring

theorem finiteTimeKernel_sharp_integral (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (ha : Measurable a) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (N : ℕ) (topLength : ℝ) (htop : 0<topLength) :
    Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) ∧
    (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t‖)≤8*Real.pi*D := by
  have hr : 0<2*topLength/(2:ℝ)^N := by positivity
  have hrR : 2*topLength/(2:ℝ)^N≤2*topLength := by
    apply div_le_self (by positivity)
    exact one_le_pow₀ (by norm_num)
  have heq : (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) =ᵐ[volume]
      (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    rw [finiteTimeKernel_eq_profileDifference k a hprofile N topLength htop t ht]
  obtain ⟨hi,hbound⟩ := sharpKernelComparison_integral a ha D hD hnear hfar _ _ hr hrR
  refine ⟨hi.congr heq.symm,?_⟩
  calc
    _ = ∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t‖ :=
      integral_congr_ae (heq.mono fun _ h => congrArg norm h)
    _ ≤ _ := hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FrozenDirection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frozen-direction sampling

The sampling maps and positive-time representation of the short Hilbert transform
in §1 of *A uniform Hilbert transform estimate for Lipschitz directions*.
The direction in these definitions is evaluated at the output point.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace LipschitzHilbert

theorem sample_rescale {L : ℝ} (hL : L ≠ 0)
    (v : DirectionPlane → DirectionPlane) (t : ℝ) (x : DirectionPlane) :
    sample (rescaleField L v) (L * t) (L • x) = L • sample v t x := by
  simp [sample, rescaleField, smul_sub, smul_smul, hL]

theorem rescaleField_unit {L : ℝ} (v : DirectionPlane → DirectionPlane)
    (hv : ∀ x, ‖v x‖ = 1) : ∀ x, ‖rescaleField L v x‖ = 1 :=
  fun x => hv (L⁻¹ • x)

/-- Dilation intertwines the two hard truncation endpoints exactly. -/
theorem shortTransform_rescale {L : ℝ} (hL : L ≠ 0)
    (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) :
    shortTransform (rescaleField L v) (L * ε) (L * a) (rescaleFunction L f) (L • x) =
      shortTransform v ε a f x := by
  let g : ℝ → ℂ := fun s => s⁻¹ •
    (rescaleFunction L f (sample (rescaleField L v) s (L • x)) -
      rescaleFunction L f (sample (rescaleField L v) (-s) (L • x)))
  have hg (t : ℝ) : g (L * t) = L⁻¹ •
      (t⁻¹ • (f (sample v t x) - f (sample v (-t) x))) := by
    dsimp [g]
    rw [show -(L * t) = L * (-t) by ring, sample_rescale hL,
      sample_rescale hL]
    simp [rescaleFunction, smul_smul, hL, mul_inv_rev, mul_comm, mul_assoc]
  change (∫ s in L * ε..L * a, g s) = _
  rw [← intervalIntegral.smul_integral_comp_mul_left g L]
  simp_rw [hg]
  rw [intervalIntegral.integral_smul, smul_smul, mul_inv_cancel₀ hL, one_smul]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_UnitDirectionCharts
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite collection of orthogonal charts for a unit direction field.
The clipped slope is defined on the whole plane. On its orientation patch
it agrees exactly with the ratio of the two coordinates. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LipschitzHilbert

theorem horizontalUnit_norm : ‖horizontalUnit‖ = 1 := by
  simp [horizontalUnit, PiLp.norm_single]

theorem directionChart_center (d : Plane) (hd : ‖d‖=1) :
    directionChart d d = horizontalUnit :=
  Submodule.reflection_sub (hd.trans horizontalUnit_norm.symm)

theorem chartField_lipschitz (d : Plane) {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) : LipschitzWith K (chartField d v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [chartField, LinearIsometryEquiv.dist_map] using
    hv.dist_le_mul ((directionChart d).symm x) ((directionChart d).symm y)

theorem chartField_unit (d : Plane) {v : Plane → Plane} (hv : ∀ x, ‖v x‖=1) :
    ∀ x, ‖chartField d v x‖=1 := by
  intro x
  simpa only [chartField, LinearIsometryEquiv.norm_map] using hv ((directionChart d).symm x)

theorem coordinate_lipschitz {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (i : Fin 2) : LipschitzWith K (fun x => v x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (PiLp.dist_apply_le (v x) (v y) i).trans (hv.dist_le_mul x y)

theorem ratio_dist_bound {a b c d : ℝ} (hb : 1/2≤b) (hd : 1/2≤d)
    (hc : |c|≤1) : |a/b-c/d|≤2*|a-c|+4*|b-d| := by
  have hb0 : 0<b := by linarith
  have hd0 : 0<d := by linarith
  calc
    |a/b-c/d| = |(a-c)/b+c*(d-b)/(b*d)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(a-c)/b|+|c*(d-b)/(b*d)| := abs_add_le _ _
    _ = |a-c|/b+|c| *|b-d|/(b*d) := by
      rw [abs_div, abs_div, abs_mul, abs_mul, abs_sub_comm d b,
        abs_of_pos hb0, abs_of_pos hd0]
    _ ≤ 2*|a-c|+4*|b-d| := by
      apply add_le_add
      · apply (div_le_iff₀ hb0).mpr
        nlinarith [abs_nonneg (a-c)]
      · apply (div_le_iff₀ (mul_pos hb0 hd0)).mpr
        have hbd : 1/4≤b*d := by nlinarith
        nlinarith [abs_nonneg (b-d), mul_le_mul_of_nonneg_right hc (abs_nonneg (b-d))]

theorem rawChartSlope_lipschitz {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hunit : ∀ x, ‖v x‖=1) :
    LipschitzWith (6*K) (rawChartSlope v) := by
  have hden := (coordinate_lipschitz hv 0).const_max (1/2)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc : |v y 1|≤1 := by
    simpa only [Real.norm_eq_abs, hunit y] using PiLp.norm_apply_le (v y) (1 : Fin 2)
  have hb := ratio_dist_bound (a := v x 1) (le_max_left (1/2) (v x 0))
    (le_max_left (1/2) (v y 0)) hc
  have h1 := (coordinate_lipschitz hv 1).dist_le_mul x y
  have h0 := hden.dist_le_mul x y
  simp only [Real.dist_eq] at h1 h0 ⊢
  change |rawChartSlope v x-rawChartSlope v y|≤_
  change |v x 1 / chartDenominator v x-v y 1 / chartDenominator v y|≤_ at hb
  simp only [chartDenominator] at hb ⊢
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  dsimp [rawChartSlope, chartDenominator]
  nlinarith

theorem clippedChartSlope_lipschitz {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hunit : ∀ x, ‖v x‖=1) :
    LipschitzWith (6*K) (clippedChartSlope v) :=
  ((rawChartSlope_lipschitz hv hunit).const_min (1/4)).const_max (-(1/4))

theorem clippedChartSlope_abs (v : Plane → Plane) (x : Plane) :
    |clippedChartSlope v x|≤1/4 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem chart_coordinates {d : Plane} (hd : ‖d‖=1) {q : Plane}
    (hq : dist q d<1/10) :
    9/10<(directionChart d q) 0 ∧ |(directionChart d q) 1|<1/10 := by
  have hc : dist (directionChart d q) horizontalUnit<1/10 := by
    rw [←directionChart_center d hd, LinearIsometryEquiv.dist_map]
    exact hq
  have h0 := (PiLp.dist_apply_le (directionChart d q) horizontalUnit (0 : Fin 2)).trans_lt hc
  have h1 := (PiLp.dist_apply_le (directionChart d q) horizontalUnit (1 : Fin 2)).trans_lt hc
  simp [horizontalUnit, Real.dist_eq] at h0 h1
  norm_num at h0 h1
  exact ⟨by linarith [(abs_lt.mp h0).1], h1⟩

theorem clippedChartSlope_eq_ratio {v : Plane → Plane} {x : Plane}
    (h0 : 9/10<v x 0) (h1 : |v x 1|<1/10) :
    clippedChartSlope v x=v x 1/v x 0 := by
  have hv : 0<v x 0 := by linarith
  have hr : |v x 1/v x 0|≤1/4 := by
    rw [abs_div, abs_of_pos hv, div_le_iff₀ hv]
    linarith
  simp only [clippedChartSlope,rawChartSlope,chartDenominator,
    max_eq_right (by linarith : (1:ℝ)/2≤v x 0),
    min_eq_right (abs_le.mp hr).2, max_eq_right (abs_le.mp hr).1]

theorem exists_finite_direction_charts :
    ∃ D : Finset Plane, (∀ d∈D, ‖d‖=1) ∧
      ∀ q : Plane, ‖q‖=1 → ∃ d∈D, dist q d<1/10 := by
  obtain ⟨s, hs, hfin, hcover⟩ :=
    (isCompact_sphere (0 : Plane) 1).finite_cover_balls (by norm_num : (0:ℝ)<1/10)
  classical
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro d hd
    simpa only [Metric.mem_sphere, dist_zero_right] using hs (hfin.mem_toFinset.mp hd)
  · intro q hq
    have hm := hcover (show q∈Metric.sphere (0 : Plane) 1 by simpa using hq)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hm
    obtain ⟨d, hd, hdist⟩ := hm
    exact ⟨d, hfin.mem_toFinset.mpr hd, hdist⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DirectionChartSampling
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact changes of coordinates and time in the directional integral. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem sample_chart (d : Plane) (v : Plane → Plane) (t : ℝ) (x : Plane) :
    sample (chartField d v) t (directionChart d x)=directionChart d (sample v t x) := by
  simp only [sample,chartField,LinearIsometryEquiv.symm_apply_apply,map_sub,map_smul]

theorem shortTransform_chart (d : Plane) (v : Plane → Plane) (epsilon R : ℝ)
    (f : Plane → ℂ) (x : Plane) :
    shortTransform (chartField d v) epsilon R (f ∘ (directionChart d).symm)
      (directionChart d x)=shortTransform v epsilon R f x := by
  unfold shortTransform
  apply intervalIntegral.integral_congr
  intro t _
  simp only [sample_chart,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply]

theorem sample_as_slope (v : Plane → Plane) (x : Plane) (t : ℝ)
    (h0 : v x 0≠0) :
    planeCoordinates.symm (sample v t x)=
      PacketRepresentation.productSlopeSample
        (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0)
        (t*v x 0) (planeCoordinates.symm x) := by
  apply Prod.ext
  · rfl
  · simp only [PacketRepresentation.productSlopeSample, MeasurableEquiv.apply_symm_apply]
    change x 1-t*v x 1=x 1-(t*v x 0)*(v x 1/v x 0)
    field_simp

theorem shortTransform_as_slope (v : Plane → Plane) (x : Plane)
    (epsilon R : ℝ) (f : Plane → ℂ) (h0 : v x 0≠0) :
    shortTransform v epsilon R f x=
      PacketRepresentation.productSymmetricTruncation
        (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0)
        (epsilon*v x 0) (R*v x 0) (f ∘ planeCoordinates) (planeCoordinates.symm x) := by
  let g := fun s : ℝ => s⁻¹ •
    ((f ∘ planeCoordinates) (PacketRepresentation.productSlopeSample
      (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0) s (planeCoordinates.symm x))-
     (f ∘ planeCoordinates) (PacketRepresentation.productSlopeSample
      (fun z => v (planeCoordinates z) 1/v (planeCoordinates z) 0) (-s) (planeCoordinates.symm x)))
  have hg (t : ℝ) : g (t*v x 0)=(v x 0)⁻¹ •
      (t⁻¹ • (f (sample v t x)-f (sample v (-t) x))) := by
    dsimp only [g]
    rw [←sample_as_slope v x t h0,show -(t*v x 0)=(-t)*v x 0 by ring,
      ←sample_as_slope v x (-t) h0]
    simp only [Function.comp_apply,MeasurableEquiv.apply_symm_apply,mul_inv_rev,smul_smul]
  change _=∫ s in epsilon*v x 0..R*v x 0, g s
  rw [←intervalIntegral.smul_integral_comp_mul_right g (v x 0)]
  simp_rw [hg]
  rw [intervalIntegral.integral_smul,smul_smul,mul_inv_cancel₀ h0,one_smul]
  rfl

end LipschitzHilbert

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ChartPullback
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal chart and product coordinates preserve the input L2
norm. The slope and endpoint factors satisfy global quantitative bounds. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LipschitzHilbert

theorem chartCoordinateMap_measurePreserving (d : Plane) :
    MeasurePreserving (chartCoordinateMap d) (volume.prod volume) volume :=
  (directionChart d).symm.measurePreserving.comp planeCoordinates_measurePreserving

theorem chartSchwartz_norm (d : Plane) (f : SchwartzMap Plane ℂ) :
    ‖(chartSchwartz d f).toLp 2 (volume.prod volume)‖=‖f.toLp 2 volume‖ := by
  simp only [SchwartzMap.toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_comp_measurePreserving (f.memLp 2 volume).aestronglyMeasurable
    (chartCoordinateMap_measurePreserving d)

theorem chartInverse_measurePreserving (d : Plane) :
    MeasurePreserving (fun x => planeCoordinates.symm (directionChart d x))
      volume (volume.prod volume) :=
  planeCoordinates_measurePreserving.symm.comp (directionChart d).measurePreserving

theorem chartDenominator_bounds (v : Plane → Plane) (hv : ∀ x, ‖v x‖=1) (x : Plane) :
    1/2 ≤ chartDenominator v x ∧ chartDenominator v x≤1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have hc : |v x 0|≤1 := by
    simpa only [Real.norm_eq_abs,hv x] using PiLp.norm_apply_le (v x) (0 : Fin 2)
  exact (le_abs_self _).trans hc

theorem clippedChartSlope_small_lipschitz (v : Plane → Plane)
    (hv : LipschitzWith (1/100) v) (hunit : ∀ x, ‖v x‖=1) :
    LipschitzWith 1 (clippedChartSlope v) :=
  (clippedChartSlope_lipschitz hv hunit).weaken (by
    exact_mod_cast (show (6:ℝ)*(1/100)≤1 by norm_num))

theorem chartDenominator_measurable (v : Plane → Plane) {K : ℝ≥0}
    (hv : LipschitzWith K v) : Measurable (chartDenominator v) :=
  ((coordinate_lipschitz hv 0).const_max (1/2)).continuous.measurable

theorem shortTransform_clippedChart (v : Plane → Plane) (x : Plane)
    (epsilon R : ℝ) (f : Plane → ℂ) (h0 : 9/10<v x 0) (h1 : |v x 1|<1/10) :
    shortTransform v epsilon R f x=
      PacketRepresentation.productSymmetricTruncation
        (fun z => clippedChartSlope v (planeCoordinates z))
        (epsilon*chartDenominator v x) (R*chartDenominator v x)
        (f ∘ planeCoordinates) (planeCoordinates.symm x) := by
  have hs := clippedChartSlope_eq_ratio h0 h1
  have hd : chartDenominator v x=v x 0 := max_eq_right (by linarith)
  rw [shortTransform_as_slope v x epsilon R f (by linarith),hd]
  simp only [PacketRepresentation.productSymmetricTruncation,
    PacketRepresentation.productSlopeSample,MeasurableEquiv.apply_symm_apply,hs]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed normalization of the original vertical cutoff controls its
L1, L2 and uniform sizes without changing its frequency band or strip. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProjectionCost_pos (p : SchwartzMap ℝ ℂ) : 0<verticalProjectionCost p := by
  unfold verticalProjectionCost
  have h : 0≤∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖ := integral_nonneg fun _ => norm_nonneg _
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalL2Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vertical Schwartz multiplier extends to L2. This
preliminary bound supplies continuity for restricted-test approximation. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSchwartzToL2_norm (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖verticalSchwartzToL2 p w f‖≤verticalProjectionCost p*‖f.toLp 2 planeMeasure‖ := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have he := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  have hid : verticalConvolution K f=schwartzVerticalProjection p w 0 f := by
    funext z
    exact (schwartzVerticalProjection_eq_convolution p w 0 hw f z).symm
  have hmass : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  rw [hid,hmass] at he
  have hout := memLp_toL2_norm_sq planeMeasure (schwartzVerticalProjection p w 0 f)
    ((schwartzVerticalProjection p w 0 f).memLp 2 planeMeasure)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖verticalSchwartzToL2 p w f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : A≤verticalProjectionCost p := by
    change A≤1+A
    linarith only [hA]
  have hsquare : ‖verticalSchwartzToL2 p w f‖^2≤
      (verticalProjectionCost p*‖f.toLp 2 planeMeasure‖)^2 := by
    apply he.trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAC 2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (verticalProjectionCost_pos p).le (norm_nonneg _))).1 hsquare

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed smooth annular Hilbert multiplier and its cutoff derivative.
All profiles are constructed, rather than supplied as analytic inputs. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSmoothSign_pos (x : ℝ) (hx : 1/2≤x) : hilbertSmoothSign x=1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.one_of_one_le (show 1≤2*x+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show 1-2*x≤0 by linarith)]

theorem hilbertSmoothSign_neg (x : ℝ) (hx : x≤-(1/2)) : hilbertSmoothSign x= -1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.zero_of_nonpos (show 2*x+1≤0 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤1-2*x by linarith)]

theorem hilbertSmoothSign_range (x : ℝ) : -1≤hilbertSmoothSign x ∧ hilbertSmoothSign x≤1 := by
  unfold hilbertSmoothSign
  constructor <;> linarith [Real.smoothTransition.nonneg (2*x+1),
    Real.smoothTransition.le_one (2*x+1),Real.smoothTransition.nonneg (1-2*x),
    Real.smoothTransition.le_one (1-2*x)]

theorem hilbertSmoothSign_deriv_zero (x : ℝ) (hx : 1/2≤|x|) :
    deriv hilbertSmoothSign x=0 := by
  rcases le_abs.mp hx with hx | hx
  · apply IsLocalMax.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_pos x hx]
    exact (hilbertSmoothSign_range y).2
  · apply IsLocalMin.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_neg x (by linarith)]
    exact (hilbertSmoothSign_range y).1

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the actual annular multiplier gives a dyadic difference
of a single compactly supported smooth profile. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_deriv_plateau (x : ℝ) : deriv hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x))=0 := by
  by_cases hx : |x|≤1/2
  · have hx1 : |x|≤1 := by linarith
    have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x hx1,verticalBinPlateauReal_one (2*x) hx2]
    ring
  · rw [hilbertSmoothSign_deriv_zero x (le_of_lt (lt_of_not_ge hx)),zero_mul]

theorem hilbertSign_dilation_deriv (x : ℝ) :
    hilbertSmoothSign x*deriv verticalBinPlateauReal (2*x)=
      hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x) := by
  by_cases hx : |x|≤1/2
  · have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_deriv_zero (2*x) (Or.inl hx2)]
    ring
  · have hxabs : 1/2≤|x| := le_of_lt (lt_of_not_ge hx)
    rcases le_abs.mp hxabs with hp | hn
    · rw [hilbertSmoothSign_pos x hp,hilbertSmoothSign_pos (2*x) (by linarith)]
    · rw [hilbertSmoothSign_neg x (by linarith),hilbertSmoothSign_neg (2*x) (by linarith)]

theorem hilbertAnnularSymbol_hasDerivAt (x : ℝ) :
    HasDerivAt hilbertAnnularSymbol
      (-(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x))) x := by
  have hs := ((contDiff_infty_iff_deriv.mp hilbertSmoothSign_smooth).1 x).hasDerivAt
  have hc (s : ℝ) := ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 s).hasDerivAt
  have hc2 := (hc (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hd := (hs.mul ((hc x).sub hc2)).ofReal_comp.const_mul (-(Real.pi:ℂ)*Complex.I)
  refine hd.congr_deriv ?_
  · symm
    change -(Real.pi:ℂ)*Complex.I*
      (↑(hilbertSmoothSign x*deriv verticalBinPlateauReal x)-
        2*↑(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x))) = _
    simp only [Pi.sub_apply,Function.comp_apply]
    rw [hilbertSign_deriv_plateau,zero_add]
    have heq : hilbertSmoothSign x*(deriv verticalBinPlateauReal x-
        deriv verticalBinPlateauReal (2*x)*(2*1))=
        hilbertSmoothSign x*deriv verticalBinPlateauReal x-
          2*(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x)) := by
      rw [←hilbertSign_dilation_deriv]
      ring
    rw [heq]
    push_cast
    ring

theorem hilbertAnnularSymbol_deriv (x : ℝ) :
    deriv hilbertAnnularSymbol x=
      -(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x)) :=
  (hilbertAnnularSymbol_hasDerivAt x).deriv

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertCutoffNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact derivative profile has integral minus two, fixing the
normalization of the physical telescoping profile at the origin. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertCutoffDerivative_nonneg_arg (x : ℝ) (hx : 0≤x) :
    hilbertCutoffDerivative x=((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : 1/2≤x
  · rw [hilbertSmoothSign_pos x h,one_mul]
  · have ha : |x|≤1 := by rw [abs_of_nonneg hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero]

theorem hilbertCutoffDerivative_nonpos_arg (x : ℝ) (hx : x≤0) :
    hilbertCutoffDerivative x= -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
  change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=_
  by_cases h : x≤-(1/2)
  · rw [hilbertSmoothSign_neg x h,neg_one_mul,Complex.ofReal_neg]
  · have ha : |x|≤1 := by rw [abs_of_nonpos hx]; linarith
    rw [verticalBinPlateauReal_deriv_zero x (Or.inl ha),mul_zero,Complex.ofReal_zero,neg_zero]

theorem hilbertCutoffDerivative_integral : (∫ x, hilbertCutoffDerivative x)=(-2:ℂ) := by
  have hc : Continuous (fun x => ((deriv verticalBinPlateauReal x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).2.continuous
  have hd (x : ℝ) : HasDerivAt verticalBinPlateau ((deriv verticalBinPlateauReal x : ℝ) : ℂ) x := by
    exact ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 x).hasDerivAt.ofReal_comp
  have hpos : (∫ x in (0:ℝ)..3, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (0:ℝ)..3, ((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤3)] at hx
        exact hilbertCutoffDerivative_nonneg_arg x hx.1
      _ = verticalBinPlateau 3-verticalBinPlateau 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (3:ℝ)=0 := by
          change (verticalBinPlateauReal 3:ℂ)=0
          rw [verticalBinPlateauReal_zero 3 (Or.inr (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),zero_sub]
  have hneg : (∫ x in (-3:ℝ)..0, hilbertCutoffDerivative x)=(-1:ℂ) := by
    calc
      _ = ∫ x in (-3:ℝ)..0, -((deriv verticalBinPlateauReal x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-3:ℝ)≤0)] at hx
        exact hilbertCutoffDerivative_nonpos_arg x hx.2
      _ = -(verticalBinPlateau 0-verticalBinPlateau (-3)) := by
        rw [intervalIntegral.integral_neg]
        congr 1
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)
      _ = -1 := by
        have h3 : verticalBinPlateau (-3:ℝ)=0 := by
          change (verticalBinPlateauReal (-3):ℂ)=0
          rw [verticalBinPlateauReal_zero (-3) (Or.inl (by norm_num)),Complex.ofReal_zero]
        rw [h3,verticalBinPlateau_one 0 (by norm_num),sub_zero]
  have hsupport : Function.support hilbertCutoffDerivative ⊆ Ioc (-3:ℝ) 3 := by
    intro x hx
    have ha : |x|<2 := by
      by_contra hn
      have hz := verticalBinPlateauReal_deriv_zero x (Or.inr (le_of_not_gt hn))
      apply hx
      change ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)=0
      rw [hz,mul_zero,Complex.ofReal_zero]
    have hb := abs_lt.mp ha
    constructor <;> linarith
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hsupport,
    ←intervalIntegral.integral_add_adjacent_intervals
      (hilbertCutoffDerivative.continuous.intervalIntegrable (-3) 0)
      (hilbertCutoffDerivative.continuous.intervalIntegrable 0 3),hneg,hpos]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint assumptions in the sharp truncation comparison follow
from Schwartz regularity and the single normalization value at zero. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzProfile_bounds (a : SchwartzMap ℝ ℂ) (ha : a 0= -1) :
    ∃ D : ℝ, 0≤D ∧ (∀ s, ‖a s+1‖≤D*|s|) ∧ (∀ s, |s| *‖a s‖≤D) := by
  let D := SchwartzMap.seminorm ℝ 0 1 a+SchwartzMap.seminorm ℝ 1 0 a
  have h0 : 0≤SchwartzMap.seminorm ℝ 0 1 a := apply_nonneg _ _
  have h1 : 0≤SchwartzMap.seminorm ℝ 1 0 a := apply_nonneg _ _
  have hd (x : ℝ) : ‖deriv a x‖≤SchwartzMap.seminorm ℝ 0 1 a := by
    simpa only [pow_zero,one_mul,iteratedDeriv_one] using a.le_seminorm' ℝ 0 1 x
  refine ⟨D,add_nonneg h0 h1,?_,?_⟩
  · intro s
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x∈(Set.univ : Set ℝ)) => a.differentiableAt)
      (fun x (_ : x∈(Set.univ : Set ℝ)) => hd x) (Set.mem_univ (0:ℝ)) (Set.mem_univ s)
    rw [ha,sub_neg_eq_add,sub_zero,Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h1) (abs_nonneg s))
  · intro s
    have h := a.norm_pow_mul_le_seminorm ℝ 1 s
    simp only [pow_one,Real.norm_eq_abs] at h
    exact h.trans (le_add_of_nonneg_left h0)

theorem schwartzFiniteTimeKernel_sharp_integral (k a : SchwartzMap ℝ ℂ)
    (ha : a 0= -1) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2)) :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel k N topLength t‖)≤B := by
  obtain ⟨D,hD,hnear,hfar⟩ := schwartzProfile_bounds a ha
  refine ⟨8*Real.pi*D,by positivity,?_⟩
  intro N topLength htop
  exact finiteTimeKernel_sharp_integral k a a.continuous.measurable hprofile
    D hD hnear hfar N topLength htop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertTimeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual annular inverse Fourier kernel telescopes to a normalized
Schwartz profile. This gives a uniform sharp truncation comparison. -/
noncomputable section
open MeasureTheory FourierTransform LineDeriv
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeProfile_zero : hilbertTimeProfile 0= -1 := by
  change (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) 0= -1
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
  simp only [inner_zero_right,Real.fourierChar.map_zero_eq_one,one_smul]
  rw [hilbertCutoffDerivative_integral]
  norm_num

theorem schwartzDilation_fourierInv (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    (𝓕⁻ (schwartzDilation f r hr.ne') : SchwartzMap ℝ ℂ) t=
      (r⁻¹:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) (t/r) := by
  simp only [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg]
  rw [←SchwartzMap.fourier_coe,schwartzDilation_fourier]
  rw [abs_of_pos (inv_pos.mpr hr),Complex.real_smul,neg_div]
  simp only [Complex.ofReal_inv,SchwartzMap.fourier_coe]

theorem schwartz_fourierInv_deriv (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (𝓕⁻ (SchwartzMap.derivCLM ℂ ℂ f) : SchwartzMap ℝ ℂ) t=
      -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ f : SchwartzMap ℝ ℂ) t := by
  have heq : SchwartzMap.derivCLM ℂ ℂ f=∂_{(1:ℝ)} f := by
    ext x
    rw [SchwartzMap.derivCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [heq,SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply,Real.inner_apply,mul_one,smul_eq_mul]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (show (fun x : ℝ => x).HasTemperateGrowth from by fun_prop)]
  simp only [Complex.real_smul]
  ring

theorem hilbertTimeKernel_profile (t : ℝ) :
    (t:ℂ)*hilbertTimeKernel t=hilbertTimeProfile t-hilbertTimeProfile (t/2) := by
  have hd : SchwartzMap.derivCLM ℂ ℂ hilbertAnnularSymbol=
      (-(Real.pi:ℂ)*Complex.I) • (hilbertCutoffDerivative-
        (2:ℂ) • schwartzDilation hilbertCutoffDerivative 2 (by norm_num)) := by
    ext x
    simp only [SchwartzMap.derivCLM_apply,smul_apply,sub_apply,smul_eq_mul,
      schwartzDilation_apply]
    exact hilbertAnnularSymbol_deriv x
  have h := schwartz_fourierInv_deriv hilbertAnnularSymbol t
  rw [hd] at h
  simp only [sub_eq_add_neg,fourierInv_add,fourierInv_neg,fourierInv_smul,
    smul_apply,add_apply,neg_apply,smul_eq_mul] at h
  rw [schwartzDilation_fourierInv hilbertCutoffDerivative 2 (by norm_num) t] at h
  change (t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t=
    (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) t-
      (1/2:ℂ)*(𝓕⁻ hilbertCutoffDerivative : SchwartzMap ℝ ℂ) (t/2)
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (-2:ℂ)≠0) hp) Complex.I_ne_zero))
  calc
    _ = -(2*Real.pi*Complex.I)*(t:ℂ)*(𝓕⁻ hilbertAnnularSymbol : SchwartzMap ℝ ℂ) t := by ring
    _ = _ := h.symm
    _ = _ := by push_cast; ring

theorem hilbertTimeKernel_sharp_integral :
    ∃ B : ℝ, 0≤B ∧ ∀ (N : ℕ) (topLength : ℝ), 0<topLength →
      Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t) ∧
      (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        finiteTimeKernel hilbertTimeKernel N topLength t‖)≤B :=
  schwartzFiniteTimeKernel_sharp_integral hilbertTimeKernel hilbertTimeProfile
    hilbertTimeProfile_zero hilbertTimeKernel_profile

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TimeEndpointComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A factor-two change of the inner time endpoint costs a fixed L1
constant. Every positive inner endpoint has such a dyadic representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_lower (r s R t : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖≤3*timeErrorEnvelope r t := by
  have hq := timeErrorEnvelope_nonneg r t hr
  by_cases hs : s< |t|
  · have hr' : r< |t| := hrs.trans_lt hs
    simp only [sharpTimeKernel,hr',hs,true_and,sub_self,norm_zero]
    positivity
  · by_cases hr' : r< |t|
    · by_cases hR : |t|<R
      · have ht : 0< |t| := hr.trans hr'
        have ht2 : |t|≤2*r := (le_of_not_gt hs).trans hsr
        have hd : 0 < r^2+t^2 := by positivity
        have hpoly : r^2+t^2≤3*r*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr hr'.le) (sub_nonneg.mpr ht2)]
        have hcond1 : r< |t| ∧ |t|<R := ⟨hr',hR⟩
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
        simp only [sharpTimeKernel,ite_eq_left hcond1,ite_eq_right hcond2,sub_zero,
          norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hR h.2
        have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hR h.2
        simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
        positivity
    · have hcond1 : ¬(r< |t| ∧ |t|<R) := fun h => hr' h.1
      have hcond2 : ¬(s< |t| ∧ |t|<R) := fun h => hs h.1
      simp only [sharpTimeKernel,ite_eq_right hcond1,ite_eq_right hcond2,sub_self,norm_zero]
      positivity

theorem sharpTimeKernel_close_lower_integral (r s R : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hsr : s≤2*r) :
    Integrable (fun t => sharpTimeKernel r R t-sharpTimeKernel s R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-sharpTimeKernel s R t‖)≤3*Real.pi := by
  have hm := (sharpTimeKernel_measurable r R).sub (sharpTimeKernel_measurable s R)
  have hi := (timeErrorEnvelope_integrable r hr).const_mul 3
  have hb (t) := sharpTimeKernel_close_lower r s R t hr hrs hsr
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 3*timeErrorEnvelope r t := integral_mono he.norm hi hb
    _ = 3*Real.pi := by rw [integral_const_mul,timeErrorEnvelope_integral r hr]

theorem exists_dyadic_time_endpoint (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) :
    ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon := by
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ he).2 (by simpa using heR))
    (by norm_num : (1:ℝ)<2)
  refine ⟨N,?_,?_⟩
  · apply (le_div_iff₀ (pow_pos (by norm_num) N)).2
    simpa only [mul_comm] using (le_div_iff₀ he).1 hlo
  · apply (div_lt_iff₀ (pow_pos (by norm_num) N)).2
    have h := (div_lt_iff₀ he).1 hhi
    rw [pow_succ] at h
    nlinarith only [h]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertArbitraryEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Hilbert decomposition applies to every positive inner
truncation, with a nearby dyadic endpoint and a uniform error. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeKernel_arbitrary_endpoint :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
        Integrable (fun t => sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t) ∧
        (∫ t, ‖sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t‖)≤B := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_sharp_integral
  refine ⟨3*Real.pi+B,by positivity,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_dyadic_time_endpoint epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  have hc := sharpTimeKernel_close_lower_integral epsilon (R/(2:ℝ)^N) R he hlo hhi.le
  have hk := hkernel N (R/2) (by positivity)
  rw [show 2*(R/2)=R by ring] at hk
  let A := fun t => sharpTimeKernel epsilon R t-sharpTimeKernel (R/(2:ℝ)^N) R t
  let C := fun t => sharpTimeKernel (R/(2:ℝ)^N) R t-
    finiteTimeKernel hilbertTimeKernel N (R/2) t
  have hi : Integrable (fun t => sharpTimeKernel epsilon R t-
      finiteTimeKernel hilbertTimeKernel N (R/2) t) := by
    apply (hc.1.add hk.1).congr
    filter_upwards [] with t
    dsimp
    ring
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ‖A t‖+‖C t‖ := by
      apply integral_mono hi.norm (hc.1.norm.add hk.1.norm)
      intro t
      have heq : sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t=
          A t+C t := by dsimp [A,C]; ring
      change ‖sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t‖≤
        ‖A t‖+‖C t‖
      rw [heq]
      exact norm_add_le _ _
    _ = (∫ t, ‖A t‖)+(∫ t, ‖C t‖) := integral_add hc.1.norm hk.1.norm
    _ ≤ 3*Real.pi+B := add_le_add hc.2 hk.2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ReflectedBandProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Negative vertical bands are conjugates of positive vertical bands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_conj (epsilon R t : ℝ) :
    conj (sharpTimeKernel epsilon R t)=sharpTimeKernel epsilon R t := by
  unfold sharpTimeKernel
  split_ifs <;> simp

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NarrowBandCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed nonzero, real and even narrow cutoff for the
p=2 band-to-full reduction. Its positive part is in [1,101/100]. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem narrowBandPositive_support (s : ℝ) (hs : narrowBandPositive s≠0) :
    1 ≤ s ∧ s≤101/100 := by
  have hn : narrowBandBump s≠0 := by
    intro h
    exact hs (by simp only [narrowBandPositive_apply,h,Complex.ofReal_zero])
  have hm : s∈Function.support narrowBandBump := hn
  rw [narrowBandBump.support_eq] at hm
  have hd : |s-201/200|<1/400 := by
    simpa only [Metric.mem_ball,Real.dist_eq,narrowBandBump] using hm
  exact ⟨by linarith [(abs_lt.mp hd).1],by linarith [(abs_lt.mp hd).2]⟩

theorem narrowBandPositive_real (s : ℝ) : star (narrowBandPositive s)=narrowBandPositive s := by
  simp only [narrowBandPositive_apply,Complex.star_def,Complex.conj_ofReal]

@[simp] theorem narrowBandProfile_apply (s : ℝ) :
    narrowBandProfile s=narrowBandPositive s+narrowBandPositive (-s) := by
  simp only [narrowBandProfile,add_apply,conjugateReflectedCutoff_apply]
  change narrowBandPositive s+star (narrowBandPositive (-s))=_
  rw [narrowBandPositive_real]

theorem narrowBandProfile_even (s : ℝ) : narrowBandProfile (-s)=narrowBandProfile s := by
  simp only [narrowBandProfile_apply,neg_neg,add_comm]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTransformMeasurable
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial measurability for positive inner cutoffs and the symmetric
principal value. Continuity of the direction field suffices; its value
is frozen at each output point throughout the time integration. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

theorem shortTransform_continuous
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Continuous f)
    {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) :
    Continuous (shortTransform v ε a f) := by
  let kernel := fun (x : DirectionPlane) (t : ℝ) =>
    (max ε t)⁻¹ • (f (sample v t x)-f (sample v (-t) x))
  have hk : Continuous kernel.uncurry := by
    have hn : Continuous (fun z : DirectionPlane×ℝ => (max ε z.2)⁻¹) :=
      (continuous_const.max continuous_snd).inv₀ (fun z =>
        (hε.trans_le (le_max_left ε z.2)).ne')
    have hs : Continuous (fun z : DirectionPlane×ℝ => sample v z.2 z.1) := by
      exact continuous_fst.sub (continuous_snd.smul (hv.comp continuous_fst))
    have hneg : Continuous (fun z : DirectionPlane×ℝ => sample v (-z.2) z.1) := by
      exact continuous_fst.sub (continuous_snd.neg.smul (hv.comp continuous_fst))
    exact hn.smul ((hf.comp hs).sub (hf.comp hneg))
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hk ε a
  have heq : shortTransform v ε a f = (fun x => ∫ t in ε..a, kernel x t) := by
    funext x
    unfold shortTransform
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hεa] at ht
    dsimp only [kernel]
    rw [max_eq_right ht.1]
  rw [heq]
  exact hc

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FiniteOutputCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of output points permits summing operator bounds.
No disjointness or regularity of the choice of a covering index is needed. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem eLpNorm_le_sum_of_pointwise_choice {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (F : X → ℂ) (G : I → X → ℂ)
    (hF : AEStronglyMeasurable F μ) (hG : ∀ i∈s, AEStronglyMeasurable (G i) μ)
    (hcover : ∀ x, ∃ i∈s, F x=G i x) :
    eLpNorm F 2 μ≤∑ i∈s, eLpNorm (G i) 2 μ := by
  have hp (x : X) : ‖F x‖≤‖∑ i∈s, ‖G i x‖‖ := by
    obtain ⟨i, hi, heq⟩ := hcover x
    rw [heq,Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg (G j x))]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (G j x)) hi
  calc
    _ ≤ eLpNorm (∑ i∈s, fun x => ‖G i x‖) 2 μ :=
      eLpNorm_mono (by simpa only [Finset.sum_apply] using hp)
    _ ≤ ∑ i∈s, eLpNorm (fun x => ‖G i x‖) 2 μ := eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)
    _ = _ := Finset.sum_congr rfl (fun i hi => eLpNorm_norm (G i))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ConditionalUnitDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform L2 truncation bounds for unit vector fields with a fixed small
Lipschitz constant, obtained by the finite orthogonal direction cover. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem chartTruncation_eq (d : Plane) (hd : ‖d‖=1) (v : Plane → Plane)
    (epsilon R : ℝ) (f : SchwartzMap Plane ℂ) (x : Plane) (hx : dist (v x) d<1/10) :
    chartTruncation d v epsilon R f x=shortTransform v epsilon R f x := by
  have hc := chart_coordinates hd hx
  have hfield : chartField d v (directionChart d x)=directionChart d (v x) := by
    simp only [chartField,LinearIsometryEquiv.symm_apply_apply]
  have h := shortTransform_clippedChart (chartField d v) (directionChart d x) epsilon R
    (f ∘ (directionChart d).symm) (by rw [hfield]; exact hc.1) (by rw [hfield]; exact hc.2)
  rw [shortTransform_chart] at h
  have hfun : (chartSchwartz d f : (ℝ×ℝ) → ℂ)=(f ∘ (directionChart d).symm) ∘ planeCoordinates := by
    funext z
    exact chartSchwartz_apply d f z
  simpa only [chartTruncation,MeasurableEquiv.apply_symm_apply,hfun] using h.symm

theorem chartTruncation_bound (C : ℝ)
    (hbound : ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
      ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
      ∀ (a : (ℝ×ℝ) → ℝ), Measurable a → (∀ z, 1/2≤a z) → (∀ z, a z≤1) →
      ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
          (epsilon*a z) (R*a z) f z) 2 planeMeasure ∧
        eLpNorm (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
          (epsilon*a z) (R*a z) f z) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖))
    (d : Plane) (v : Plane → Plane) (hv : LipschitzWith (1/100) v)
    (hunit : ∀ x, ‖v x‖=1) (epsilon R : ℝ) (he : 0<epsilon)
    (heR : epsilon≤R) (hR : R≤1/10000) (f : SchwartzMap Plane ℂ) :
    MemLp (chartTruncation d v epsilon R f) 2 volume ∧
      eLpNorm (chartTruncation d v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  let w := chartField d v
  have hw : LipschitzWith (1/100) w := chartField_lipschitz d hv
  have hwu : ∀ x, ‖w x‖=1 := chartField_unit d hunit
  let a := fun z => chartDenominator w (planeCoordinates z)
  obtain ⟨hm, hb⟩ := hbound epsilon R he heR hR (clippedChartSlope w)
    (clippedChartSlope_small_lipschitz w hw hwu) (clippedChartSlope_abs w)
    a ((chartDenominator_measurable w hw).comp planeCoordinates.measurable)
    (fun z => (chartDenominator_bounds w hwu _).1)
    (fun z => (chartDenominator_bounds w hwu _).2) (chartSchwartz d f)
  have hmp := chartInverse_measurePreserving d
  refine ⟨hm.comp_measurePreserving hmp,?_⟩
  change eLpNorm ((fun z => productSymmetricTruncation
      (fun z => clippedChartSlope w (planeCoordinates z)) (epsilon*a z) (R*a z)
      (chartSchwartz d f) z) ∘ (fun x => planeCoordinates.symm (directionChart d x))) 2 volume≤_
  rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hmp]
  simpa only [planeMeasure,chartSchwartz_norm] using hb

theorem conditional_unit_small_lipschitz (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
    ∀ (v : Plane → Plane), LipschitzWith (1/100) v → (∀ x, ‖v x‖=1) →
    ∀ f : SchwartzMap Plane ℂ,
      eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  classical
  obtain ⟨C,hC,hbound⟩ := conditional_variable_slope_truncation hVariation hLL hH hReassembly
  obtain ⟨D,hDu,hDcover⟩ := exists_finite_direction_charts
  have hDne : D.Nonempty := by
    obtain ⟨d,hd,_⟩ := hDcover horizontalUnit horizontalUnit_norm
    exact ⟨d,hd⟩
  refine ⟨D.card*C,by positivity,?_⟩
  intro epsilon R he heR hR v hv hunit f
  have hb (d : Plane) := chartTruncation_bound C hbound d v hv hunit epsilon R he heR hR f
  have hcover (x : Plane) : ∃ d∈D, shortTransform v epsilon R f x=chartTruncation d v epsilon R f x := by
    obtain ⟨d,hd,hdist⟩ := hDcover (v x) (hunit x)
    exact ⟨d,hd,(chartTruncation_eq d (hDu d hd) v epsilon R f x hdist).symm⟩
  have hm : AEStronglyMeasurable (shortTransform v epsilon R f) volume :=
    (shortTransform_continuous hv.continuous f.continuous he heR).aestronglyMeasurable
  calc
    _ ≤ ∑ d∈D, eLpNorm (chartTruncation d v epsilon R f) 2 volume :=
      eLpNorm_le_sum_of_pointwise_choice volume D _ _ hm (fun d _ => (hb d).1.aestronglyMeasurable) hcover
    _ ≤ ∑ _d∈D, ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
      Finset.sum_le_sum (fun d _ => (hb d).2)
    _ = ENNReal.ofReal ((D.card*C)*‖f.toLp 2 volume‖) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DirectionDilation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal-Lipschitz dilation and its exact L2 scaling in the plane. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem toLp_norm_comp_smul (f : Plane → ℂ) (hf : Continuous f) (hm : MemLp f 2 volume)
    (L : ℝ) (hL : 0<L) :
    ‖((memLp_two_comp_smul_iff f hf L hL.ne').mpr hm).toLp (fun x => f (L • x))‖=
      L⁻¹*‖hm.toLp f‖ := by
  have hmg := (memLp_two_comp_smul_iff f hf L hL.ne').mpr hm
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,memLp_toL2_norm_sq volume _ hmg,memLp_toL2_norm_sq volume f hm,
    Measure.integral_comp_smul volume (fun x => ‖f x‖^2) L]
  simp only [Plane,finrank_euclideanSpace, Fintype.card_fin,smul_eq_mul]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hL 2))]
  ring

theorem rescaleSchwartz_norm (L : ℝ) (hL : 0<L) (f : SchwartzMap Plane ℂ) :
    ‖(rescaleSchwartz L hL.ne' f).toLp 2 volume‖=L*‖f.toLp 2 volume‖ := by
  have h := toLp_norm_comp_smul f f.continuous (f.memLp 2 volume) L⁻¹ (inv_pos.mpr hL)
  have hfun : (rescaleSchwartz L hL.ne' f : Plane → ℂ)=(fun x => f (L⁻¹ • x)) := by
    funext x
    rfl
  rw [Lp.norm_toLp] at h
  rw [SchwartzMap.norm_toLp]
  rw [hfun]
  simpa only [inv_inv,Lp.norm_toLp,SchwartzMap.norm_toLp] using h

theorem rescaleField_lipschitz_small {K : ℝ≥0} (hK : 0<K)
    {v : Plane → Plane} (hv : LipschitzWith K v) :
    LipschitzWith (1/100) (rescaleField (100*(K:ℝ)) v) := by
  have hKreal : 0<(K:ℝ) := hK
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rescaleField (100*(K:ℝ)) v x) (rescaleField (100*(K:ℝ)) v y) ≤
        (K:ℝ)*dist ((100*(K:ℝ))⁻¹ • x) ((100*(K:ℝ))⁻¹ • y) := hv.dist_le_mul _ _
    _ = ((1/100 : ℝ≥0):ℝ)*dist x y := by
      rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity))]
      norm_num only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      field_simp

theorem shortTransform_dilation (L : ℝ) (hL : L≠0) (v : Plane → Plane)
    (epsilon R : ℝ) (f : SchwartzMap Plane ℂ) :
    shortTransform (rescaleField L v) (L*epsilon) (L*R) (rescaleSchwartz L hL f)=
      fun x => shortTransform v epsilon R f (L⁻¹ • x) := by
  have hfun : (rescaleSchwartz L hL f : Plane → ℂ)=rescaleFunction L f := by
    funext x
    rfl
  rw [hfun]
  funext x
  have h := shortTransform_rescale hL v epsilon R f (L⁻¹ • x)
  simpa only [smul_smul,mul_inv_cancel₀ hL,one_smul] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ConditionalUniformTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform sharp-truncation estimate at reciprocal Lipschitz scale.
The explicit radius is deliberately smaller than the allowed absolute
radius; the operator constant is independent of both cutoffs and the field. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem conditional_uniform_truncation (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  obtain ⟨C,hC,hbound⟩ := conditional_unit_small_lipschitz hVariation hLL hH hReassembly
  refine ⟨C,hC,?_⟩
  intro K hK epsilon R he heR hR v hv hunit f
  have hKr : 0<(K:ℝ) := hK
  let L : ℝ := 100*(K:ℝ)
  have hL : 0<L := by positivity
  have hLR : L*R≤1/10000 := by
    have h := (le_div_iff₀ (by positivity : 0<1000000*(K:ℝ))).mp hR
    dsimp only [L]
    nlinarith
  have hbd := hbound (L*epsilon) (L*R) (mul_pos hL he)
    (mul_le_mul_of_nonneg_left heR hL.le) hLR (rescaleField L v)
    (rescaleField_lipschitz_small hK hv) (rescaleField_unit v hunit)
    (rescaleSchwartz L hL.ne' f)
  rw [shortTransform_dilation L hL.ne' v epsilon R f] at hbd
  have hfcont : Continuous (shortTransform v epsilon R f) :=
    shortTransform_continuous hv.continuous f.continuous he heR
  have hmg : MemLp (fun x => shortTransform v epsilon R f (L⁻¹ • x)) 2 volume :=
    ⟨(hfcont.comp (continuous_const_smul L⁻¹)).aestronglyMeasurable,hbd.trans_lt (by simp)⟩
  have hmf : MemLp (shortTransform v epsilon R f) 2 volume :=
    (memLp_two_comp_smul_iff _ hfcont L⁻¹ (inv_ne_zero hL.ne')).mp hmg
  have hs := toLp_norm_comp_smul _ hfcont hmf L⁻¹ (inv_pos.mpr hL)
  rw [inv_inv] at hs
  have hn := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbd
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _)),rescaleSchwartz_norm L hL f] at hn
  have hn' : ‖hmg.toLp (fun x => shortTransform v epsilon R f (L⁻¹ • x))‖≤
      C*(L*‖f.toLp 2 volume‖) := by
    rw [Lp.norm_toLp]
    exact hn
  rw [hs] at hn'
  have hnorm : ‖hmf.toLp (shortTransform v epsilon R f)‖≤C*‖f.toLp 2 volume‖ := by
    nlinarith
  rw [←Lp.enorm_toLp hmf,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hnorm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CubicDualityEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar exponent calculation in the three-halves dual estimate. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem cubic_duality_estimate (F J E : ℝ) (hF : 0≤F) (hJ : 0≤J) (hE : 0≤E)
    (h : J≤F^(2/3:ℝ)*(E*J)^(1/3:ℝ)) : J≤(E+1)^(3/2:ℝ)*F := by
  have hcube := pow_le_pow_left₀ hJ h 3
  have hFp : (F^(2/3:ℝ))^3=F^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hF]
    norm_num
  have hEJp : ((E*J)^(1/3:ℝ))^3=E*J := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (mul_nonneg hE hJ)]
    norm_num
  rw [mul_pow,hFp,hEJp] at hcube
  by_cases hz : J=0
  · rw [hz]
    positivity
  have hJp : 0<J := lt_of_le_of_ne hJ (Ne.symm hz)
  have hs : J^2≤E*F^2 := by
    by_contra hn
    have hp : 0<J*(J^2-E*F^2) := mul_pos hJp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [hcube]
  have hcoef : E≤(E+1)^3 := by nlinarith [sq_nonneg E,pow_nonneg hE 3]
  have hpower : ((E+1)^(3/2:ℝ)*F)^2=(E+1)^3*F^2 := by
    rw [mul_pow,←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0≤E+1)]
    norm_num
  apply (sq_le_sq₀ hJ (by positivity : 0≤(E+1)^(3/2:ℝ)*F)).mp
  rw [hpower]
  exact hs.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg F))

end LipschitzHilbert.PacketRepresentation

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NarrowWindowNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each nonzero frequency has a compact smooth neighborhood on which a
positive dilation of the fixed narrow multiplier is exactly one. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem narrowBandProfile_eventually_one :
    (fun y : ℝ => narrowBandProfile y) =ᶠ[𝓝 (201/200:ℝ)] 1 := by
  filter_upwards [narrowBandBump.eventuallyEq_one,
    eventually_gt_nhds (show (0:ℝ)<201/200 by norm_num)] with y hy hpos
  have hz : narrowBandPositive (-y)=0 := by
    by_contra hn
    have hh := (narrowBandPositive_support (-y) hn).1
    linarith
  simp only [narrowBandProfile_apply,narrowBandPositive_apply] at hz ⊢
  rw [hy,hz]
  simp

theorem narrowBandProfile_eventually_one_abs (x : ℝ)
    (hx : |x|=(201/200:ℝ)) :
    (fun y : ℝ => narrowBandProfile y) =ᶠ[𝓝 x] 1 := by
  by_cases hp : 0≤x
  · have he : x=(201/200:ℝ) := by simpa only [abs_of_nonneg hp] using hx
    rw [he]
    exact narrowBandProfile_eventually_one
  · have he : -x=(201/200:ℝ) := by simpa only [abs_of_neg (lt_of_not_ge hp)] using hx
    have ht : Tendsto (fun y : ℝ => -y) (𝓝 x) (𝓝 (201/200:ℝ)) := by
      rw [←he]
      exact continuous_neg.continuousAt.tendsto
    filter_upwards [ht.eventually narrowBandProfile_eventually_one] with y hy
    simpa only [narrowBandProfile_even,Pi.one_apply] using hy

theorem exists_narrow_window (x : ℝ) (hx : x≠0) :
    ∃ w : ℝ, 0<w ∧ ∃ b : ContDiffBump x,
      ∀ y : ℝ, narrowBandProfile (w*y)*(b y:ℂ)=(b y:ℂ) := by
  let w : ℝ := (201/200)/|x|
  have hw : 0<w := div_pos (by norm_num) (abs_pos.mpr hx)
  have hxw : |w*x|=(201/200:ℝ) := by
    rw [abs_mul,abs_of_pos hw]
    dsimp [w]
    exact div_mul_cancel₀ _ (abs_pos.mpr hx).ne'
  have ht : Tendsto (fun y : ℝ => w*y) (𝓝 x) (𝓝 (w*x)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto
  have hn : {y : ℝ | narrowBandProfile (w*y)=1}∈𝓝 x :=
    ht.eventually (narrowBandProfile_eventually_one_abs (w*x) hxw)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let b : ContDiffBump x :=
    { rIn := r/4
      rOut := r/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨w,hw,b,?_⟩
  intro y
  by_cases hz : b y=0
  · simp only [hz,Complex.ofReal_zero,mul_zero]
  · have hy : y∈Metric.ball x r := by
      have hm : y∈Function.support b := hz
      rw [b.support_eq] at hm
      change dist y x < r/2 at hm
      change dist y x < r
      linarith
    rw [hsub hy,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteNarrowPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smooth partition over any compact set avoiding zero. Every
piece is absorbed by a positive dilation of the fixed narrow cutoff. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

private theorem sum_sub_mul (b : ℂ) (l : List ℂ) :
    (l.map (fun z => z-b*z)).sum=(1-b)*l.sum := by
  induction l with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem narrowPartition_sum_cons (b : NarrowWindow) (bs : List NarrowWindow) (x : ℝ) :
    ((narrowPartition (b::bs)).map (fun q => q.2 x)).sum=
      b.2 x+(1-b.2 x)*((narrowPartition bs).map (fun q => q.2 x)).sum := by
  simp only [narrowPartition,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
    sub_apply,lineSchwartzProduct_apply]
  have h := sum_sub_mul (b.2 x) ((narrowPartition bs).map (fun q => q.2 x))
  simp only [List.map_map,Function.comp_def] at h
  exact congrArg (fun z : ℂ => b.2 x+z) h

theorem narrowPartition_sum_of_one (l : List NarrowWindow) (x : ℝ)
    (h : ∃ b∈l, b.2 x=1) :
    ((narrowPartition l).map (fun q => q.2 x)).sum=1 := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rw [narrowPartition_sum_cons]
    rcases h with ⟨q,hq,hval⟩
    rcases List.mem_cons.mp hq with rfl|hq
    · rw [hval]; ring
    · rw [ih ⟨q,hq,hval⟩]; ring

theorem narrowPartition_absorb (l : List NarrowWindow)
    (h : ∀ b∈l, 0<b.1 ∧ ∀ x, narrowBandProfile (b.1*x)*b.2 x=b.2 x) :
    ∀ q∈narrowPartition l, 0<q.1 ∧ ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x := by
  induction l with
  | nil => simp [narrowPartition]
  | cons b bs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact h q (List.mem_cons_self)
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
      have hp' := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) p hp
      refine ⟨hp'.1,fun x => ?_⟩
      simp only [sub_apply,lineSchwartzProduct_apply]
      calc
        _ = narrowBandProfile (p.1*x)*p.2 x-
          b.2 x*(narrowBandProfile (p.1*x)*p.2 x) := by ring
        _ = _ := by rw [hp'.2]

theorem exists_finite_narrow_partition (K : Set ℝ) (hK : IsCompact K)
    (hzero : ∀ x∈K, x≠0) :
    ∃ l : List NarrowWindow,
      (∀ q∈l, 0<q.1 ∧ ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x) ∧
      ∀ x∈K, (l.map (fun q => q.2 x)).sum=1 := by
  classical
  have hex (x : K) := exists_narrow_window x.1 (hzero x.1 x.2)
  choose w hw b hb using hex
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball x.1 (b x).rIn) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (b ⟨x,hx⟩).rIn_pos⟩)
  let original : List NarrowWindow := s.toList.map (fun x =>
    (w x,((b x).hasCompactSupport.toSchwartzMap (b x).contDiff).postcompCLM
      Complex.ofRealCLM))
  refine ⟨narrowPartition original,narrowPartition_absorb original ?_,?_⟩
  · intro q hq
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hq
    exact ⟨hw x,hb x⟩
  · intro x hx
    apply narrowPartition_sum_of_one
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine ⟨_,List.mem_map.mpr ⟨y,Finset.mem_toList.mpr hy,rfl⟩,?_⟩
    change ((b y) x:ℂ)=1
    rw [(b y).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)]
    exact Complex.ofReal_one

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

theorem lineConvolution_sub_of_bounded (K f g : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (hgm : Measurable g)
    (Bf Bg : ℝ) (hf : ∀ x, ‖f x‖≤Bf) (hg : ∀ x, ‖g x‖≤Bg) :
    lineConvolution K (f-g)=lineConvolution K f-lineConvolution K g := by
  funext x
  unfold lineConvolution
  simp only [Pi.sub_apply,mul_sub]
  exact integral_sub (lineConvolution_integrand_of_bounded K f hK hfm Bf hf x)
    (lineConvolution_integrand_of_bounded K g hK hgm Bg hg x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fourth-power Young bound for an integrable line kernel and a
Schwartz input, with its exact L1 kernel constant. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_fourth_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        ((f.memLp 4 volume).integrable_norm_pow (by decide))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^4‖)=‖K t‖*(∫ z, ‖f z‖^4) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        norm_pow,norm_norm]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^4) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_fourth_pointwise (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖lineConvolution K f x‖^4≤(∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
  have hi (n : ℕ) : Integrable (fun t => ‖K t‖*‖f (x-t)‖^n) := by
    apply (hK.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0 f)^n)).mono'
      (by fun_prop)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity : 0≤‖K t‖*‖f (x-t)‖^n)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ f (x-t)) n)
      (norm_nonneg _)
  have hfirst := lineConvolution_pointwise_energy K hK hKm f f.continuous.measurable x (hi 2)
  have hfourth : Integrable (fun t => ‖K t‖*(‖f (x-t)‖^2)^2) := by
    simpa only [←pow_mul] using hi 4
  have hsecond := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (x-t)‖^2) hKm.norm (by fun_prop) (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _) hK.norm hfourth).2
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  calc
    ‖lineConvolution K f x‖^4 = (‖lineConvolution K f x‖^2)^2 := by ring
    _ ≤ ((∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (x-t)‖^2))^2 := hs
    _ = (∫ t, ‖K t‖)^2*(∫ t, ‖K t‖*‖f (x-t)‖^2)^2 := mul_pow _ _ _
    _ ≤ (∫ t, ‖K t‖)^2*((∫ t, ‖K t‖)*(∫ t, ‖K t‖*(‖f (x-t)‖^2)^2)) :=
      mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
    _ = _ := by simp only [←pow_mul]; ring

theorem lineConvolution_fourth_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖lineConvolution K f x‖^4) ∧
      (∫ x, ‖lineConvolution K f x‖^4)≤(∫ t, ‖K t‖)^4*(∫ x, ‖f x‖^4) := by
  have hj := lineConvolution_fourth_joint_integrable K hK hKm f
  have hm := lineConvolution_measurable K hKm f f.continuous.measurable
  have hd : Integrable (fun x => (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4)) :=
    hj.integral_prod_right.const_mul _
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^4) := by
    apply hd.mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (by positivity : 0≤‖lineConvolution K f x‖^4)]
    exact lineConvolution_fourth_pointwise K hK hKm f x
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) :=
      integral_mono hi hd (lineConvolution_fourth_pointwise K hK hKm f)
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_integral_swap (f:=fun (x t : ℝ) => ‖K t‖*‖f (x-t)‖^4) hj.swap]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun x => ‖f x‖^4)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionL4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line convolution fourth-power estimate for measurable L4 inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem memLp_fourth_iff (f : ℝ → ℂ) (hfm : AEStronglyMeasurable f volume) :
    MemLp f 4 volume ↔ Integrable (fun x => ‖f x‖^4) := by
  simpa using (integrable_norm_rpow_iff (p:=4) hfm (by norm_num) (by norm_num)).symm

theorem memLp_toL4_norm_pow (f : ℝ → ℂ) (hf : MemLp f 4 volume) :
    ‖hf.toLp f‖^4=∫ x, ‖f x‖^4 := by
  rw [Lp.norm_toLp,toReal_eLpNorm hf.aestronglyMeasurable,lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

theorem lineConvolution_fourth_joint (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 4 volume) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 4≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^4‖)=‖K t‖*(∫ z, ‖f z‖^4) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),norm_pow,norm_norm]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^4) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_fourth_at (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (x : ℝ)
    (hi : Integrable (fun t => ‖K t‖*‖f (x-t)‖^4)) :
    ‖lineConvolution K f x‖^4≤(∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
  have hfourth : Integrable (fun t => ‖K t‖*(‖f (x-t)‖^2)^2) := by
    simpa only [←pow_mul] using hi
  have hsecond := weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (x-t)‖^2) hKm.norm (by fun_prop) (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _) hK.norm hfourth
  have hfirst := lineConvolution_pointwise_energy K hK hKm f hfm x hsecond.1
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  calc
    ‖lineConvolution K f x‖^4 = (‖lineConvolution K f x‖^2)^2 := by ring
    _ ≤ ((∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (x-t)‖^2))^2 := hs
    _ = (∫ t, ‖K t‖)^2*(∫ t, ‖K t‖*‖f (x-t)‖^2)^2 := mul_pow _ _ _
    _ ≤ (∫ t, ‖K t‖)^2*((∫ t, ‖K t‖)*(∫ t, ‖K t‖*(‖f (x-t)‖^2)^2)) :=
      mul_le_mul_of_nonneg_left hsecond.2 (sq_nonneg _)
    _ = _ := by simp only [←pow_mul]; ring

theorem lineConvolution_L4_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 4 volume) :
    MemLp (lineConvolution K f) 4 volume ∧
      (∫ x, ‖lineConvolution K f x‖^4)≤(∫ t, ‖K t‖)^4*(∫ x, ‖f x‖^4) := by
  have hj := lineConvolution_fourth_joint K f hK hKm hfm hf
  have hm := lineConvolution_measurable K hKm f hfm
  have hd : Integrable (fun x => (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4)) :=
    hj.integral_prod_right.const_mul _
  have hp : ∀ᵐ x ∂volume, ‖lineConvolution K f x‖^4≤
      (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
    filter_upwards [hj.prod_left_ae] with x hx
    exact lineConvolution_fourth_at K f hK hKm hfm x hx
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^4) := by
    apply hd.mono' (by fun_prop)
    filter_upwards [hp] with x hx
    rwa [Real.norm_of_nonneg (by positivity : 0≤‖lineConvolution K f x‖^4)]
  refine ⟨(memLp_fourth_iff _ hm.aestronglyMeasurable).2 hi,?_⟩
  calc
    _ ≤ ∫ x, (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := integral_mono_ae hi hd hp
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_integral_swap (f:=fun (x t : ℝ) => ‖K t‖*‖f (x-t)‖^4) hj.swap]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun x => ‖f x‖^4)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HalfPowerDualTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit dual test for exponent three-halves, with its second,
fourth and third moments. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem halfPowerDualTest_measurable (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (halfPowerDualTest g) := by unfold halfPowerDualTest; fun_prop

theorem halfPowerDualTest_norm (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖=‖g x‖^(1/2:ℝ) := by
  by_cases hz : g x=0
  · simp [halfPowerDualTest,hz]
  have hp : 0<‖g x‖ := norm_pos_iff.mpr hz
  rw [halfPowerDualTest,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  conv_lhs => rhs; rw [←Real.rpow_one ‖g x‖]
  rw [←Real.rpow_add hp]
  norm_num

theorem halfPowerDualTest_norm_sq (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^2=‖g x‖ := by
  rw [halfPowerDualTest_norm,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem halfPowerDualTest_norm_fourth (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^4=‖g x‖^2 := by
  rw [show (4:ℕ)=2*2 by decide,pow_mul,halfPowerDualTest_norm_sq]

theorem halfPowerDualTest_norm_cube (g : ℝ → ℂ) (x : ℝ) :
    ‖halfPowerDualTest g x‖^3=‖g x‖^(3/2:ℝ) := by
  rw [halfPowerDualTest_norm,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem halfPowerDualTest_pair (g : ℝ → ℂ) (x : ℝ) :
    g x*conj (halfPowerDualTest g x)=((‖g x‖^(3/2:ℝ):ℝ):ℂ) := by
  by_cases hz : g x=0
  · simp [halfPowerDualTest,hz]
  have hp : 0<‖g x‖ := norm_pos_iff.mpr hz
  simp only [halfPowerDualTest,map_mul,Complex.conj_ofReal]
  calc
    _ = ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*(g x*conj (g x)) := by ring
    _ = ((‖g x‖^(-(1/2):ℝ):ℝ):ℂ)*(‖g x‖:ℂ)^2 := by rw [Complex.mul_conj']
    _ = ((‖g x‖^(3/2:ℝ):ℝ):ℂ) := by
      rw [←Complex.ofReal_pow,←Complex.ofReal_mul,←Real.rpow_natCast,←Real.rpow_add hp]
      norm_num

theorem halfPowerDualTest_memLp (g : ℝ → ℂ) (hgm : Measurable g)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    MemLp (halfPowerDualTest g) 2 volume ∧ MemLp (halfPowerDualTest g) 4 volume := by
  have hm := halfPowerDualTest_measurable g hgm
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    simpa only [halfPowerDualTest_norm_sq] using hg1.norm
  · apply (memLp_fourth_iff _ hm.aestronglyMeasurable).2
    simpa only [halfPowerDualTest_norm_fourth] using hg2.integrable_norm_pow (by decide : 2≠0)

theorem halfPowerDualTest_bound (g : ℝ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖≤B) :
    ∀ x, ‖halfPowerDualTest g x‖≤B+1 := by
  have hBp : 0≤B := (norm_nonneg _).trans (hB 0)
  intro x
  have hs : ‖halfPowerDualTest g x‖^2≤B := by rw [halfPowerDualTest_norm_sq]; exact hB x
  nlinarith [norm_nonneg (halfPowerDualTest g x),sq_nonneg B]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HardyPairL4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An elementary fourth-power bound for the difference of positive and
negative frequency Schwartz functions. The proof uses only Plancherel,
frequency support of products, and a scalar quadratic inequality. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_positive (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, eta≤0 → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    ∀ eta, eta≤0 → (𝓕 (lineSchwartzProduct a b) : SchwartzMap ℝ ℂ) eta=0 := by
  intro eta he
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : t≤0
  · exact Or.inl (ha t ht)
  · exact Or.inr (hb (eta-t) (by linarith))

theorem lineSchwartzProduct_negative (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, 0≤eta → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    ∀ eta, 0≤eta → (𝓕 (lineSchwartzProduct a b) : SchwartzMap ℝ ℂ) eta=0 := by
  intro eta he
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : 0≤t
  · exact Or.inl (ha t ht)
  · exact Or.inr (hb (eta-t) (by linarith))

theorem schwartz_disjoint_energy_add_sub (a b : SchwartzMap ℝ ℂ)
    (h : ∀ eta, (𝓕 a : SchwartzMap ℝ ℂ) eta=0 ∨ (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    (∫ x, ‖(a+b) x‖^2)=(∫ x, ‖(a-b) x‖^2) := by
  rw [←SchwartzMap.integral_norm_sq_fourier (a+b),
    ←SchwartzMap.integral_norm_sq_fourier (a-b)]
  apply integral_congr_ae
  filter_upwards [] with eta
  simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
    add_apply,neg_apply]
  rcases h eta with ha | hb
  · rw [ha,zero_add,zero_add,norm_neg]
  · rw [hb,add_zero,neg_zero,add_zero]

theorem hardyPair_fourth_power (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    (∫ x, ‖(a-b) x‖^4)≤68*(∫ x, ‖(a+b) x‖^4) := by
  let f := a+b
  let g := a-b
  let H := lineSchwartzProduct a a+lineSchwartzProduct b b
  let Q := lineSchwartzProduct a a-lineSchwartzProduct b b
  have horth : (∫ x, ‖H x‖^2)=(∫ x, ‖Q x‖^2) := by
    apply schwartz_disjoint_energy_add_sub
    intro eta
    by_cases he : eta≤0
    · exact Or.inl (lineSchwartzProduct_positive a a ha ha eta he)
    · exact Or.inr (lineSchwartzProduct_negative b b hb hb eta (by linarith))
  have hidentity (x : ℝ) : g x*g x=2*H x-f x*f x := by
    simp only [f,g,H,add_apply,sub_apply,lineSchwartzProduct_apply]
    ring
  have hQ (x : ℝ) : Q x=f x*g x := by
    simp only [Q,f,g,add_apply,sub_apply,lineSchwartzProduct_apply]
    ring
  have hpoint (x : ℝ) : ‖g x‖^4≤8*‖H x‖^2+2*‖f x‖^4 := by
    have hn := norm_sub_le (2*H x) (f x*f x)
    rw [←hidentity,norm_mul,norm_mul,norm_mul] at hn
    norm_num at hn
    have hs := sq_nonneg (2*‖H x‖-‖f x‖^2)
    nlinarith [sq_nonneg (‖g x‖^2-(2*‖H x‖+‖f x‖^2))]
  have hQpoint (x : ℝ) : ‖Q x‖^2≤(1/16:ℝ)*‖g x‖^4+4*‖f x‖^4 := by
    rw [hQ,norm_mul,mul_pow]
    nlinarith [sq_nonneg (‖g x‖^2/4-2*‖f x‖^2)]
  have hf : Integrable (fun x => ‖f x‖^4) :=
    (f.memLp 4 volume).integrable_norm_pow (by decide)
  have hg : Integrable (fun x => ‖g x‖^4) :=
    (g.memLp 4 volume).integrable_norm_pow (by decide)
  have hH : Integrable (fun x => ‖H x‖^2) :=
    (H.memLp 2 volume).integrable_norm_pow (by decide)
  have hQi : Integrable (fun x => ‖Q x‖^2) :=
    (Q.memLp 2 volume).integrable_norm_pow (by decide)
  have hi := integral_mono hg ((hH.const_mul 8).add (hf.const_mul 2)) hpoint
  have hqi := integral_mono hQi ((hg.const_mul (1/16)).add (hf.const_mul 4)) hQpoint
  simp only [Pi.add_apply] at hi hqi
  rw [integral_add (hH.const_mul 8) (hf.const_mul 2),integral_const_mul,integral_const_mul,
    horth] at hi
  rw [integral_add (hg.const_mul (1/16)) (hf.const_mul 4),integral_const_mul,
    integral_const_mul] at hqi
  change (∫ x, ‖g x‖^4)≤68*(∫ x, ‖f x‖^4)
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertFiniteSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth finite Hilbert multiplier has a uniform bound obtained
from an exact telescoping identity, independently of the scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertFrequencySign_pos_mul (a x : ℝ) (ha : 0<a) :
    hilbertFrequencySign (a*x)=hilbertFrequencySign x := by
  unfold hilbertFrequencySign
  by_cases hx : 0≤x
  · rw [ite_eq_left hx,ite_eq_left (mul_nonneg ha.le hx)]
  · rw [ite_eq_right hx,ite_eq_right (not_le.mpr (mul_neg_of_pos_of_neg ha (lt_of_not_ge hx)))]

theorem hilbertAnnularSymbol_sign (x : ℝ) :
    hilbertAnnularSymbol x=-(Real.pi:ℂ)*Complex.I*
      (hilbertFrequencySign x*(verticalBinPlateau x-verticalBinPlateau (2*x))) := by
  change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=_
  by_cases hs : |x|≤1/2
  · have h1 : |x|≤1 := by linarith
    have h2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x h1,verticalBinPlateauReal_one (2*x) h2,
      verticalBinPlateau_one x h1,verticalBinPlateau_one (2*x) h2]
    simp
  · have hne : x≠0 := by intro hz; subst x; norm_num at hs
    by_cases hp : 0<x
    · have hx : 1/2≤x := by rw [abs_of_pos hp] at hs; linarith
      rw [hilbertSmoothSign_pos x hx,hilbertFrequencySign,ite_eq_left hp.le]
      simp only [one_mul,Complex.ofReal_sub]
      rfl
    · have hx : x≤-(1/2) := by rw [abs_of_nonpos (le_of_not_gt hp)] at hs; linarith
      rw [hilbertSmoothSign_neg x hx,hilbertFrequencySign,ite_eq_right (by linarith)]
      simp only [neg_one_mul,Complex.ofReal_neg,Complex.ofReal_sub]
      rfl

theorem hilbertFiniteSymbol_apply (N : ℕ) (L : ℝ) (hL : 0<L) (eta : ℝ) :
    hilbertFiniteSymbol N L hL eta=-(Real.pi:ℂ)*Complex.I*hilbertFrequencySign eta*
      (verticalBinPlateau ((2*L)/(2:ℝ)^N*eta)-verticalBinPlateau ((2*L)*eta)) := by
  have hterm (j : ℕ) : hilbertAnnularSymbol (L/(2:ℝ)^j*eta)=
      (-(Real.pi:ℂ)*Complex.I*hilbertFrequencySign eta)*
      (verticalBinPlateau ((2*L)/(2:ℝ)^(j+1)*eta)-verticalBinPlateau ((2*L)/(2:ℝ)^j*eta)) := by
    rw [hilbertAnnularSymbol_sign]
    have hp : 0<L/(2:ℝ)^j := div_pos hL (pow_pos (by norm_num) j)
    have hsign : hilbertFrequencySign (L/(2:ℝ)^j*eta)=hilbertFrequencySign eta :=
      hilbertFrequencySign_pos_mul _ _ hp
    have h1 : L/(2:ℝ)^j*eta=(2*L)/(2:ℝ)^(j+1)*eta := by rw [pow_succ]; field_simp
    have h2 : 2*(L/(2:ℝ)^j*eta)=(2*L)/(2:ℝ)^j*eta := by ring
    rw [hsign,h1]
    rw [←h1,h2]
    ring
  simp only [hilbertFiniteSymbol,sum_apply,dilatedSlopeWindow_apply,hterm]
  rw [←Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    verticalBinPlateau ((2*L)/(2:ℝ)^(j+1)*eta)-verticalBinPlateau ((2*L)/(2:ℝ)^j*eta)) N]
  rw [Finset.sum_range_sub (fun j : ℕ =>
    verticalBinPlateau ((2*L)/(2:ℝ)^j*eta))]
  simp only [pow_zero,div_one]

theorem hilbertFiniteSymbol_norm (N : ℕ) (L : ℝ) (hL : 0<L) (eta : ℝ) :
    ‖hilbertFiniteSymbol N L hL eta‖≤Real.pi := by
  rw [hilbertFiniteSymbol_apply]
  have hdiff : ‖verticalBinPlateau ((2*L)/(2:ℝ)^N*eta)-verticalBinPlateau ((2*L)*eta)‖≤1 := by
    change ‖((verticalBinPlateauReal ((2*L)/(2:ℝ)^N*eta):ℂ)-
      (verticalBinPlateauReal ((2*L)*eta):ℂ))‖≤1
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have h1 := verticalBinPlateauReal_range ((2*L)/(2:ℝ)^N*eta)
    have h2 := verticalBinPlateauReal_range ((2*L)*eta)
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  have hsign : ‖hilbertFrequencySign eta‖≤1 := by
    unfold hilbertFrequencySign
    split_ifs <;> norm_num
  simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I,mul_one]
  exact (mul_le_mul_of_nonneg_left hdiff (mul_nonneg Real.pi_pos.le (norm_nonneg _))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsign Real.pi_pos.le)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertFiniteL2
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform L2 bounds for the actual finite smooth Hilbert convolutions. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_unit (q : SchwartzMap ℝ ℂ) :
    lineProjectionKernel q 1 (by norm_num)=𝓕⁻ q := by
  unfold lineProjectionKernel
  congr 1
  ext x
  simp only [dilatedSlopeWindow_apply,one_mul]

theorem hilbertFinite_kernel (N : ℕ) (L : ℝ) (hL : 0<L) (x : ℝ) :
    lineProjectionKernel (hilbertFiniteSymbol N L hL) 1 (by norm_num) x=
      finiteTimeKernel hilbertTimeKernel N L x := by
  have he : lineProjectionKernel (hilbertFiniteSymbol N L hL) 1 (by norm_num)=
      ∑ j : Fin N, lineProjectionKernel hilbertAnnularSymbol (L/(2:ℝ)^j.val)
        (ne_of_gt (div_pos hL (pow_pos (by norm_num) j.val))) := by
    rw [lineProjectionKernel_unit,hilbertFiniteSymbol,FourierTransform.fourierInv_sum]
    rfl
  rw [he]
  simp only [sum_apply,finiteTimeKernel]
  apply Finset.sum_congr rfl
  intro j _
  rw [lineProjectionKernel_eq_scaled _ _ (div_pos hL (pow_pos (by norm_num) j.val)),
    scaledSchwartzKernel_apply]
  rfl

theorem hilbertFinite_L2 (N : ℕ) (L : ℝ) (hL : 0<L) (f : SchwartzMap ℝ ℂ) :
    MemLp (lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f) 2 volume ∧
      (∫ x, ‖lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x‖^2)≤
        Real.pi^2*(∫ x, ‖f x‖^2) := by
  have he : lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f=
      lineSchwartzProjection (hilbertFiniteSymbol N L hL) 1 (by norm_num) f := by
    funext x
    rw [lineSchwartzProjection_eq_convolution]
    simp only [lineConvolution,hilbertFinite_kernel]
  rw [he]
  exact ⟨(lineSchwartzProjection _ _ _ f).memLp 2 volume,
    lineSchwartzProjection_energy _ 1 (by norm_num) Real.pi (hilbertFiniteSymbol_norm N L hL) f⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertSignFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fourth-power bound for the sign multiplier on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_fourth_power (f g : SchwartzMap ℝ ℂ)
    (hzero : (𝓕 f : SchwartzMap ℝ ℂ) 0=0)
    (hfg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta=
      hilbertFrequencySign eta*(𝓕 f : SchwartzMap ℝ ℂ) eta) :
    (∫ x, ‖g x‖^4)≤68*(∫ x, ‖f x‖^4) := by
  let a : SchwartzMap ℝ ℂ := (1/2:ℂ) • (f+g)
  let b : SchwartzMap ℝ ℂ := (1/2:ℂ) • (f-g)
  have ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0 := by
    intro eta he
    change (𝓕 ((1/2:ℂ) • (f+g)) : SchwartzMap ℝ ℂ) eta=0
    simp only [FourierTransform.fourier_smul,FourierTransform.fourier_add,smul_apply,
      add_apply,smul_eq_mul,hfg]
    rcases he.eq_or_lt with hz | hn
    · subst eta
      rw [hzero,mul_zero,add_zero,mul_zero]
    · rw [hilbertFrequencySign,ite_eq_right (by linarith)]
      ring
  have hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0 := by
    intro eta he
    change (𝓕 ((1/2:ℂ) • (f-g)) : SchwartzMap ℝ ℂ) eta=0
    simp only [sub_eq_add_neg,FourierTransform.fourier_smul,FourierTransform.fourier_add,
      FourierTransform.fourier_neg,smul_apply,add_apply,neg_apply,smul_eq_mul,hfg]
    rw [hilbertFrequencySign,ite_eq_left he]
    ring
  have hab : a+b=f := by
    ext x
    simp only [a,b,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  have hdiff : a-b=g := by
    ext x
    simp only [a,b,add_apply,sub_apply,smul_apply,smul_eq_mul]
    ring
  have hh := hardyPair_fourth_power a b ha hb
  rwa [hab,hdiff] at hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPartitionIdentities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive and negative annular cutoffs reconstruct the actual
low-pass difference, whose finite geometric sums telescope exactly. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyDifference_step (n : ℕ) (s : ℝ) :
    reassemblyDifference ((3/2:ℝ)^n*s)=
      reassemblyLow ((16/27)*((3/2:ℝ)^n*s))-
        reassemblyLow ((16/27)*((3/2:ℝ)^(n+1)*s)) := by
  unfold reassemblyDifference
  congr 2
  rw [pow_succ]
  ring

theorem reassemblyDifference_telescope (N : ℕ) (s : ℝ) :
    (∑ n∈Finset.range N, reassemblyDifference ((3/2:ℝ)^n*s))=
      reassemblyLow ((16/27)*s)-reassemblyLow ((16/27)*((3/2:ℝ)^N*s)) := by
  induction N with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,pow_zero,one_mul,sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,reassemblyDifference_step]
    ring

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

theorem lineProjectionKernel_norm (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (t : ℝ) :
    ‖lineProjectionKernel q W hW.ne' t‖=W⁻¹*‖(𝓕⁻ q : SchwartzMap ℝ ℂ) (t/W)‖ := by
  rw [lineProjectionKernel_eq_scaled q W hW,scaledSchwartzKernel_apply q W hW]
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hW.le]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth line projection preserves a Lipschitz bound uniformly in its
scale, up to the fixed kernel L1 norm. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_l1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, ‖lineProjectionKernel q W hW.ne' t‖)=∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖ := by
  simp_rw [lineProjectionKernel_norm q W hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) W,
    abs_of_pos hW,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-power estimates for one or two scaled smooth cutoffs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem norm_add_fourth_le (x y : ℂ) : ‖x+y‖^4≤8*(‖x‖^4+‖y‖^4) := by
  calc
    _ ≤ (‖x‖+‖y‖)^4 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 4
    _ ≤ _ := by simpa only [show (4:ℕ)-1=3 from rfl,show (2:ℝ)^3=8 by norm_num] using
      add_pow_le (norm_nonneg x) (norm_nonneg y) 4

theorem norm_sub_fourth_le (x y : ℂ) : ‖x-y‖^4≤8*(‖x‖^4+‖y‖^4) := by
  simpa only [sub_eq_add_neg,norm_neg] using norm_add_fourth_le x (-y)

theorem lineSchwartzProjection_fourth (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW.ne' f x‖^4)≤
      (∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^4*(∫ x, ‖f x‖^4) := by
  have hh := (lineConvolution_fourth_bound (lineProjectionKernel q W hW.ne')
    (lineProjectionKernel q W hW.ne').integrable
    (lineProjectionKernel q W hW.ne').continuous.measurable f).2
  simp_rw [←lineSchwartzProjection_eq_convolution q W hW.ne' f] at hh
  rwa [lineProjectionKernel_l1 q W hW] at hh

theorem lineSchwartzProjection_difference_fourth (q : SchwartzMap ℝ ℂ)
    (A B : ℝ) (hA : 0<A) (hB : 0<B) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖(lineSchwartzProjection q A hA.ne' f-
      lineSchwartzProjection q B hB.ne' f) x‖^4)≤
      16*(∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^4*(∫ x, ‖f x‖^4) := by
  let u := lineSchwartzProjection q A hA.ne' f
  let v := lineSchwartzProjection q B hB.ne' f
  have hu : Integrable (fun x => ‖u x‖^4) := (u.memLp 4 volume).integrable_norm_pow (by decide)
  have hv : Integrable (fun x => ‖v x‖^4) := (v.memLp 4 volume).integrable_norm_pow (by decide)
  have hd : Integrable (fun x => ‖(u-v) x‖^4) := ((u-v).memLp 4 volume).integrable_norm_pow (by decide)
  have hh := integral_mono hd ((hu.add hv).const_mul 8) (fun x => norm_sub_fourth_le (u x) (v x))
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hu hv] at hh
  have ha := lineSchwartzProjection_fourth q A hA f
  have hb := lineSchwartzProjection_fourth q B hB f
  change (∫ x, ‖(u-v) x‖^4)≤_
  change (∫ x, ‖u x‖^4)≤_ at ha
  change (∫ x, ‖v x‖^4)≤_ at hb
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertFiniteFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fourth-power bounds for the finite smooth Hilbert kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertFinite_fourth (N : ℕ) (L : ℝ) (hL : 0<L) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x‖^4)≤
      (68*16*Real.pi^4*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4)*
        (∫ x, ‖f x‖^4) := by
  let A := (2*L)/(2:ℝ)^N
  let B := 2*L
  have hA : 0<A := div_pos (mul_pos (by norm_num) hL) (pow_pos (by norm_num) N)
  have hB : 0<B := mul_pos (by norm_num) hL
  let u := lineSchwartzProjection verticalBinPlateau A hA.ne' f-
    lineSchwartzProjection verticalBinPlateau B hB.ne' f
  let H := lineSchwartzProjection (hilbertFiniteSymbol N L hL) 1 (by norm_num) f
  let k : ℂ := -(Real.pi:ℂ)*Complex.I
  have hk : k≠0 := mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let v := k⁻¹ • H
  have hu (eta : ℝ) : (𝓕 u : SchwartzMap ℝ ℂ) eta=
      (verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta := by
    change (𝓕 (lineSchwartzProjection verticalBinPlateau A hA.ne' f-
      lineSchwartzProjection verticalBinPlateau B hB.ne' f) : SchwartzMap ℝ ℂ) eta=_
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
      add_apply,neg_apply,lineSchwartzProjection_fourier]
    ring
  have huzero : (𝓕 u : SchwartzMap ℝ ℂ) 0=0 := by rw [hu]; simp
  have hv (eta : ℝ) : (𝓕 v : SchwartzMap ℝ ℂ) eta=
      hilbertFrequencySign eta*(𝓕 u : SchwartzMap ℝ ℂ) eta := by
    change (𝓕 (k⁻¹ • H) : SchwartzMap ℝ ℂ) eta=_
    rw [FourierTransform.fourier_smul,smul_apply]
    change k⁻¹*(𝓕 H : SchwartzMap ℝ ℂ) eta=_
    rw [lineSchwartzProjection_fourier,one_mul,hilbertFiniteSymbol_apply,hu]
    change k⁻¹*(k*hilbertFrequencySign eta*
      (verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta)=_
    calc
      _ = (k⁻¹*k)*(hilbertFrequencySign eta*
        ((verticalBinPlateau (A*eta)-verticalBinPlateau (B*eta))*(𝓕 f : SchwartzMap ℝ ℂ) eta)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hk,one_mul]
  have hv4 := hilbertSign_fourth_power u v huzero hv
  have hu4 := lineSchwartzProjection_difference_fourth verticalBinPlateau A B hA hB f
  have hH : H=k • v := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hk,one_smul]
  have hkn : ‖k‖=Real.pi := by
    simp only [k,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_I,mul_one]
  have heq (x : ℝ) : lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x=H x := by
    dsimp [H]
    rw [lineSchwartzProjection_eq_convolution]
    simp only [lineConvolution,hilbertFinite_kernel]
  simp_rw [heq,hH,smul_apply,norm_smul,hkn,mul_pow]
  rw [integral_const_mul]
  change (∫ x, ‖u x‖^4)≤_ at hu4
  have hp : 0≤Real.pi^4 := pow_nonneg Real.pi_pos.le 4
  calc
    _ ≤ Real.pi^4*(68*(∫ x, ‖u x‖^4)) := mul_le_mul_of_nonneg_left hv4 hp
    _ ≤ Real.pi^4*(68*(16*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4*
        (∫ x, ‖f x‖^4))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hu4 (by norm_num)) hp
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform fourth-power estimate for the actual sharp truncations. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_uniform_fourth : ∃ D : ℝ, 0≤D ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^4) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^4)≤D*(∫ x, ‖f x‖^4) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  let D := 68*16*Real.pi^4*(∫ t, ‖(𝓕⁻ verticalBinPlateau : SchwartzMap ℝ ℂ) t‖)^4
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨8*(B^4+D),by positivity,?_⟩
  intro r R hr hrR f
  have hhalf : 0<R/2 := by linarith
  obtain ⟨N,_,_,hEi,hEb⟩ := hkernel r R hr hrR
  let K := sharpTimeKernel r R
  let J := finiteTimeKernel hilbertTimeKernel N (R/2)
  let E := fun t => K t-J t
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hJi : Integrable J := finiteTimeKernel_integrable _ N (R/2) hhalf
  have hEm : Measurable E := (sharpTimeKernel_measurable r R).sub
    (finiteTimeKernel_measurable _ N (R/2))
  have he := lineConvolution_fourth_bound E hEi hEm f
  have hj := lineConvolution_fourth_bound J hJi (finiteTimeKernel_measurable _ _ _) f
  have heBound : (∫ x, ‖lineConvolution E f x‖^4)≤B^4*(∫ x, ‖f x‖^4) :=
    he.2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) hEb 4)
      (integral_nonneg fun _ => by positivity))
  have hjBound : (∫ x, ‖lineConvolution J f x‖^4)≤D*(∫ x, ‖f x‖^4) :=
    hilbertFinite_fourth N (R/2) hhalf f
  have heq (x : ℝ) : oneDimensionalTruncatedHilbert r R f x=
      lineConvolution E f x+lineConvolution J f x := by
    have hsub : lineConvolution E f x=lineConvolution K f x-lineConvolution J f x := by
      change (∫ t, (K t-J t)*f (x-t))=_
      simp_rw [sub_mul]
      exact integral_sub
        (lineConvolution_integrand_of_bounded K f hKi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
        (lineConvolution_integrand_of_bounded J f hJi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
    change lineConvolution K f x=_
    rw [hsub,sub_add_cancel]
  have hm : Measurable (oneDimensionalTruncatedHilbert r R f) :=
    lineConvolution_measurable K (sharpTimeKernel_measurable r R) f f.continuous.measurable
  have hd := (he.1.add hj.1).const_mul 8
  have hp (x : ℝ) : ‖oneDimensionalTruncatedHilbert r R f x‖^4≤
      8*(‖lineConvolution E f x‖^4+‖lineConvolution J f x‖^4) := by
    rw [heq]
    exact norm_add_fourth_le _ _
  have hi : Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^4) := by
    apply hd.mono' (hm.norm.pow_const 4).aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Pi.add_apply,Real.norm_of_nonneg (by positivity : 0≤‖oneDimensionalTruncatedHilbert r R f x‖^4)] using hp x
  refine ⟨hi,?_⟩
  have hh := integral_mono hi hd hp
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add he.1 hj.1] at hh
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform L2 estimate for all finite sharp one-dimensional Hilbert
truncations. This is a proved foundation for the remaining Lp input. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

private theorem energy_eLpNorm_bound (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (f : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0≤C)
    (he : (∫ x, ‖g x‖^2)≤C^2*(∫ x, ‖f x‖^2)) :
    eLpNorm g 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  have hout := memLp_toL2_norm_sq volume g hg
  have hin := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖f.toLp 2 volume‖^2=_ at hin
  rw [←hout,←hin] at he
  have hn : ‖hg.toLp g‖≤C*‖f.toLp 2 volume‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
      (by simpa only [mul_pow] using he)
  rw [←Lp.enorm_toLp hg,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem sharpHilbert_uniform_L2 : ∃ C : ℝ, 0<C ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      MemLp (oneDimensionalTruncatedHilbert r R f) 2 volume ∧
      eLpNorm (oneDimensionalTruncatedHilbert r R f) 2 volume≤
        ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  refine ⟨B+Real.pi,by linarith [Real.pi_pos],?_⟩
  intro r R hr hrR f
  have hR : 0<R := hr.trans_le hrR
  have hhalf : 0<R/2 := by positivity
  obtain ⟨N,_,_,hEi,hEb⟩ := hkernel r R hr hrR
  let K := sharpTimeKernel r R
  let J := finiteTimeKernel hilbertTimeKernel N (R/2)
  let E := fun t => K t-J t
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hJi : Integrable J := finiteTimeKernel_integrable _ N (R/2) hhalf
  have hEm : Measurable E := (sharpTimeKernel_measurable r R).sub
    (finiteTimeKernel_measurable _ N (R/2))
  have herror := lineConvolution_energy_bound E hEi hEm f f.continuous.measurable (f.memLp 2 volume)
  have hEb' : (∫ t, ‖E t‖)^2≤B^2 := pow_le_pow_left₀
    (integral_nonneg fun _ => norm_nonneg _) hEb 2
  have herrorBound := energy_eLpNorm_bound (lineConvolution E f) herror.1 f B hB
    (herror.2.trans (mul_le_mul_of_nonneg_right hEb' (integral_nonneg fun _ => sq_nonneg _)))
  have hsmooth := hilbertFinite_L2 N (R/2) hhalf f
  have hsmoothBound := energy_eLpNorm_bound (lineConvolution J f) hsmooth.1 f Real.pi
    Real.pi_pos.le hsmooth.2
  have heq : oneDimensionalTruncatedHilbert r R f=lineConvolution E f+lineConvolution J f := by
    funext x
    have hsub : lineConvolution E f x=lineConvolution K f x-lineConvolution J f x := by
      change (∫ t, (K t-J t)*f (x-t))=_
      simp_rw [sub_mul]
      exact integral_sub
        (lineConvolution_integrand_of_bounded K f hKi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
        (lineConvolution_integrand_of_bounded J f hJi f.continuous.measurable
          (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x)
    change lineConvolution K f x=_
    rw [Pi.add_apply,hsub,sub_add_cancel]
  rw [heq]
  refine ⟨herror.1.add hsmooth.1,?_⟩
  calc
    _ ≤ eLpNorm (lineConvolution E f) 2 volume+eLpNorm (lineConvolution J f) 2 volume :=
      eLpNorm_add_le herror.1.aestronglyMeasurable hsmooth.1.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (B*‖f.toLp 2 volume‖)+ENNReal.ofReal (Real.pi*‖f.toLp 2 volume‖) :=
      add_le_add herrorBound hsmoothBound
    _ = _ := by
      rw [←ENNReal.ofReal_add (mul_nonneg hB (norm_nonneg _))
        (mul_nonneg Real.pi_pos.le (norm_nonneg _))]
      congr 1
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LayerEnergyMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two layer integrals needed to interpolate the second and fourth
moments to the third moment. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem highLayerEnergy_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ t in Ioi 0, highLayerEnergy f t)=∫⁻ x, ENNReal.ofReal (‖f x‖^3) := by
  unfold highLayerEnergy
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro x
    have he : (fun t : ℝ => if t≤‖f x‖ then ENNReal.ofReal (‖f x‖^2) else 0)=
        (Iic ‖f x‖).indicator (fun _ => ENNReal.ofReal (‖f x‖^2)) := by
      funext t
      simp only [Set.indicator,mem_Iic]
    rw [he,lintegral_indicator measurableSet_Iic,lintegral_const]
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rw [Measure.restrict_apply measurableSet_Iic]
    have hset : Iic ‖f x‖∩Ioi (0:ℝ)=Ioc 0 ‖f x‖ := by ext t; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto
    rw [hset,Real.volume_Ioc,sub_zero,←ENNReal.ofReal_mul (by positivity)]
    congr 1
  · exact ((hf.comp measurable_snd).norm.pow_const 2).ennreal_ofReal.ite
      (measurableSet_le measurable_fst (hf.comp measurable_snd).norm) measurable_const |>.aemeasurable

theorem lowLayer_scalar_integral (a : ℝ) (ha : 0≤a) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^(-2:ℝ))*
      (if a<t then ENNReal.ofReal (a^4) else 0))=ENNReal.ofReal (a^3) := by
  by_cases hz : a=0
  · subst a
    simp
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
  have he : (fun t : ℝ => ENNReal.ofReal (t^(-2:ℝ))*
      (if a<t then ENNReal.ofReal (a^4) else 0))=
      (Ioi a).indicator (fun t => ENNReal.ofReal (t^(-2:ℝ))*ENNReal.ofReal (a^4)) := by
    funext t
    by_cases ht : a<t <;> simp [ht]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  rw [inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hint : IntegrableOn (fun t : ℝ => t^(-2:ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hap
  have hnonneg : 0≤ᵐ[volume.restrict (Ioi a)] (fun t : ℝ => t^(-2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hap.trans ht).le _
  rw [←ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hap]
  norm_num
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  exact Real.rpow_neg_one a ▸ inv_mul_cancel₀ hz

theorem lowLayerEnergy_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t)=
      ∫⁻ x, ENNReal.ofReal (‖f x‖^3) := by
  unfold lowLayerEnergy
  simp_rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap]
  · exact lintegral_congr fun x => lowLayer_scalar_integral ‖f x‖ (norm_nonneg _)
  · have hm : Measurable (fun p : ℝ×ℝ => if ‖f p.2‖<p.1 then ENNReal.ofReal (‖f p.2‖^4) else 0) :=
      ((hf.comp measurable_snd).norm.pow_const 4).ennreal_ofReal.ite
        (measurableSet_lt (hf.comp measurable_snd).norm measurable_fst) measurable_const
    exact ((measurable_fst.pow_const (-2:ℝ)).ennreal_ofReal.mul hm).aemeasurable

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedConvolutionL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a Schwartz L2 convolution bound to bounded measurable
L2 inputs, using density and the actual convolution difference. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation
local instance instTwoAtLeastOne : Fact (1≤(2:ℝ≥0∞)) := ⟨by norm_num⟩

theorem toL2_norm_le_of_integral (f g : ℝ → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (C : ℝ) (hC : 0≤C)
    (h : (∫ x, ‖g x‖^2)≤C^2*(∫ x, ‖f x‖^2)) :
    ‖hg.toLp g‖≤C*‖hf.toLp f‖ := by
  rw [←memLp_toL2_norm_sq volume g hg,←memLp_toL2_norm_sq volume f hf] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg (hg.toLp g)) (mul_nonneg hC (norm_nonneg (hf.toLp f)))
    (by decide : (2:ℕ)≠0)).mp (by simpa only [mul_pow] using h)

theorem boundedConvolution_L2_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hcf : MemLp (lineConvolution K f) 2 volume) (hcg : MemLp (lineConvolution K g) 2 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_energy_bound K hK hKm (f-g) (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have hn := toL2_norm_le_of_integral (f-g) (lineConvolution K f-lineConvolution K g)
    (hf.sub hg) (hcf.sub hcg) _ (integral_nonneg fun _ => norm_nonneg _) he
  rwa [hf.toLp_sub hg,hcf.toLp_sub hcg] at hn

theorem boundedConvolution_L2_of_schwartz (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (C : ℝ) (hC : 0≤C)
    (hsch : ∀ g : SchwartzMap ℝ ℂ,
      (∫ x, ‖lineConvolution K g x‖^2)≤C^2*(∫ x, ‖g x‖^2))
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    (∫ x, ‖lineConvolution K f x‖^2)≤C^2*(∫ x, ‖f x‖^2) := by
  let L := ∫ t, ‖K t‖
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  let hcf := (lineConvolution_energy_bound K hK hKm f hfm hf).1
  let xf := hf.toLp f
  let yf := hcf.toLp (lineConvolution K f)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  have hnorm : ‖yf‖≤C*‖xf‖ := by
    by_contra hn
    have hgap : 0<‖yf‖-C*‖xf‖ := by linarith
    let eps := (‖yf‖-C*‖xf‖)/(2*(C+L+1))
    have heps : 0<eps := div_pos hgap (by positivity)
    obtain ⟨g,hg⟩ := hd.exists_dist_lt xf heps
    let hcg := (lineConvolution_energy_bound K hK hKm g g.continuous.measurable (g.memLp 2 volume)).1
    let yg := hcg.toLp (lineConvolution K g)
    have hgBound : ‖yg‖≤C*‖g.toLp 2 volume‖ :=
      toL2_norm_le_of_integral g _ (g.memLp 2 volume) hcg C hC (hsch g)
    have hdiff : ‖yf-yg‖≤L*‖xf-g.toLp 2 volume‖ :=
      boundedConvolution_L2_difference K f g hK hKm hfm g.continuous.measurable
        hf (g.memLp 2 volume) hcf hcg B (SchwartzMap.seminorm ℝ 0 0 g)
        hfb (fun x => SchwartzMap.norm_le_seminorm ℝ g x)
    have htri : ‖yf‖≤‖yf-yg‖+‖yg‖ := by
      simpa only [sub_add_cancel] using norm_add_le (yf-yg) yg
    have hgin : ‖g.toLp 2 volume‖≤‖xf‖+‖xf-g.toLp 2 volume‖ := by
      have hh := norm_add_le (g.toLp 2 volume-xf) xf
      rw [sub_add_cancel,norm_sub_rev] at hh
      linarith
    have htot : ‖yf‖≤C*‖xf‖+(C+L)*‖xf-g.toLp 2 volume‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hgin hC]
    have hdist : ‖xf-g.toLp 2 volume‖<eps := by simpa only [dist_eq_norm] using hg
    have hsmall : (C+L)*‖xf-g.toLp 2 volume‖<(C+L+1)*eps := by
      calc
        _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hdist.le (add_nonneg hC hL)
        _ < _ := by nlinarith
    have heq : (C+L+1)*eps=(‖yf‖-C*‖xf‖)/2 := by
      dsimp [eps]
      field_simp [show C+L+1≠0 by positivity]
    rw [heq] at hsmall
    linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow,memLp_toL2_norm_sq volume f hf,memLp_toL2_norm_sq volume _ hcf] at hp
  exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedConvolutionL4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a Schwartz L4 convolution bound to bounded measurable
L4 inputs, using density and the actual convolution difference. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation
local instance instFourAtLeastOne : Fact (1≤(4:ℝ≥0∞)) := ⟨by norm_num⟩

theorem toL4_norm_le_of_integral (f g : ℝ → ℂ)
    (hf : MemLp f 4 volume) (hg : MemLp g 4 volume) (C : ℝ) (hC : 0≤C)
    (h : (∫ x, ‖g x‖^4)≤C^4*(∫ x, ‖f x‖^4)) :
    ‖hg.toLp g‖≤C*‖hf.toLp f‖ := by
  rw [←memLp_toL4_norm_pow g hg,←memLp_toL4_norm_pow f hf] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg (hg.toLp g)) (mul_nonneg hC (norm_nonneg (hf.toLp f)))
    (by decide : (4:ℕ)≠0)).mp (by simpa only [mul_pow] using h)

theorem lineConvolution_L4_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 4 volume) (hg : MemLp g 4 volume)
    (hcf : MemLp (lineConvolution K f) 4 volume) (hcg : MemLp (lineConvolution K g) 4 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_L4_bound K (f-g) hK hKm (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have hn := toL4_norm_le_of_integral (f-g) (lineConvolution K f-lineConvolution K g)
    (hf.sub hg) (hcf.sub hcg) _ (integral_nonneg fun _ => norm_nonneg _) he
  rwa [hf.toLp_sub hg,hcf.toLp_sub hcg] at hn

theorem boundedConvolution_L4_of_schwartz (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (C : ℝ) (hC : 0≤C)
    (hsch : ∀ g : SchwartzMap ℝ ℂ,
      (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4))
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 4 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    (∫ x, ‖lineConvolution K f x‖^4)≤C^4*(∫ x, ‖f x‖^4) := by
  let L := ∫ t, ‖K t‖
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  let hcf := (lineConvolution_L4_bound K f hK hKm hfm hf).1
  let xf := hf.toLp f
  let yf := hcf.toLp (lineConvolution K f)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 4 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (4:ℝ≥0∞)≠⊤)
  have hnorm : ‖yf‖≤C*‖xf‖ := by
    by_contra hn
    have hgap : 0<‖yf‖-C*‖xf‖ := by linarith
    let eps := (‖yf‖-C*‖xf‖)/(2*(C+L+1))
    have heps : 0<eps := div_pos hgap (by positivity)
    obtain ⟨g,hg⟩ := hd.exists_dist_lt xf heps
    let hcg := (lineConvolution_L4_bound K g hK hKm g.continuous.measurable (g.memLp 4 volume)).1
    let yg := hcg.toLp (lineConvolution K g)
    have hgBound : ‖yg‖≤C*‖g.toLp 4 volume‖ :=
      toL4_norm_le_of_integral g _ (g.memLp 4 volume) hcg C hC (hsch g)
    have hdiff : ‖yf-yg‖≤L*‖xf-g.toLp 4 volume‖ :=
      lineConvolution_L4_difference K f g hK hKm hfm g.continuous.measurable
        hf (g.memLp 4 volume) hcf hcg B (SchwartzMap.seminorm ℝ 0 0 g)
        hfb (fun x => SchwartzMap.norm_le_seminorm ℝ g x)
    have htri : ‖yf‖≤‖yf-yg‖+‖yg‖ := by
      simpa only [sub_add_cancel] using norm_add_le (yf-yg) yg
    have hgin : ‖g.toLp 4 volume‖≤‖xf‖+‖xf-g.toLp 4 volume‖ := by
      have hh := norm_add_le (g.toLp 4 volume-xf) xf
      rw [sub_add_cancel,norm_sub_rev] at hh
      linarith
    have htot : ‖yf‖≤C*‖xf‖+(C+L)*‖xf-g.toLp 4 volume‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hgin hC]
    have hdist : ‖xf-g.toLp 4 volume‖<eps := by simpa only [dist_eq_norm] using hg
    have hsmall : (C+L)*‖xf-g.toLp 4 volume‖<(C+L+1)*eps := by
      calc
        _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hdist.le (add_nonneg hC hL)
        _ < _ := by nlinarith
    have heq : (C+L+1)*eps=(‖yf‖-C*‖xf‖)/2 := by
      dsimp [eps]
      field_simp [show C+L+1≠0 by positivity]
    rw [heq] at hsmall
    linarith
  have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  rw [mul_pow,memLp_toL4_norm_pow f hf,memLp_toL4_norm_pow _ hcf] at hp
  exact hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionPowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Markov estimates and the actual large/small amplitude splitting used
for interpolation of line convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem normPower_tail (g : ℝ → ℂ) (hgm : Measurable g) (n : ℕ)
    (t : ℝ) (ht : 0<t) :
    volume {x | t≤‖g x‖}≤ENNReal.ofReal (t⁻¹)^n*(∫⁻ x, ENNReal.ofReal (‖g x‖^n)) := by
  have hinc : {x | t≤‖g x‖}⊆{x | ENNReal.ofReal (t^n)≤ENNReal.ofReal (‖g x‖^n)} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le hx n)
  have hpos : ENNReal.ofReal (t^n)≠0 := by positivity
  have hh := meas_ge_le_lintegral_div (μ:=volume)
    ((hgm.norm.pow_const n).ennreal_ofReal.aemeasurable) hpos ENNReal.ofReal_ne_top
  calc
    _ ≤ volume {x | ENNReal.ofReal (t^n)≤ENNReal.ofReal (‖g x‖^n)} := measure_mono hinc
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖g x‖^n))/ENNReal.ofReal (t^n) := hh
    _ = _ := by
      rw [ENNReal.ofReal_pow ht.le,div_eq_mul_inv,ENNReal.inv_pow,
        ←ENNReal.ofReal_inv_of_pos ht,mul_comm]

theorem highAmplitude_measurable (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Measurable (highAmplitude f t) := hf.indicator (measurableSet_le measurable_const hf.norm)

theorem lowAmplitude_measurable (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Measurable (lowAmplitude f t) := hf.indicator (measurableSet_lt hf.norm measurable_const)

theorem amplitude_sum (f : ℝ → ℂ) (t x : ℝ) : highAmplitude f t x+lowAmplitude f t x=f x := by
  classical
  unfold highAmplitude lowAmplitude
  by_cases hx : t≤‖f x‖ <;> simp [hx,not_lt.mpr,lt_of_not_ge]

theorem amplitude_bound (f : ℝ → ℂ) (t x : ℝ) :
    ‖highAmplitude f t x‖≤‖f x‖ ∧ ‖lowAmplitude f t x‖≤‖f x‖ := by
  classical
  unfold highAmplitude lowAmplitude
  constructor <;> exact norm_indicator_le_norm_self f x

theorem convolution_amplitude_sum (K f : ℝ → ℂ) (hK : Integrable K)
    (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (t x : ℝ) :
    lineConvolution K f x=lineConvolution K (highAmplitude f t) x+
      lineConvolution K (lowAmplitude f t) x := by
  have hh := lineConvolution_integrand_of_bounded K (highAmplitude f t) hK
    (highAmplitude_measurable f hf t) B (fun x => (amplitude_bound f t x).1.trans (hB x)) x
  have hl := lineConvolution_integrand_of_bounded K (lowAmplitude f t) hK
    (lowAmplitude_measurable f hf t) B (fun x => (amplitude_bound f t x).2.trans (hB x)) x
  rw [lineConvolution,lineConvolution,lineConvolution,←integral_add hh hl]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [←mul_add,amplitude_sum]

theorem highAmplitude_power (f : ℝ → ℂ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖highAmplitude f t x‖^2))=highLayerEnergy f t := by
  classical
  apply lintegral_congr
  intro x
  unfold highAmplitude
  by_cases hx : t≤‖f x‖ <;> simp [hx]

theorem lowAmplitude_power (f : ℝ → ℂ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖lowAmplitude f t x‖^4))=lowLayerEnergy f t := by
  classical
  apply lintegral_congr
  intro x
  unfold lowAmplitude
  by_cases hx : ‖f x‖<t <;> simp [hx]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionLayerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distribution estimate for interpolation between uniform second
and fourth convolution moments. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem normPower_lintegral_le_of_integral (f g : ℝ → ℂ) (n : ℕ)
    (hf : Integrable (fun x => ‖f x‖^n)) (hg : Integrable (fun x => ‖g x‖^n))
    (A : ℝ) (hA : 0≤A) (h : (∫ x, ‖g x‖^n)≤A*(∫ x, ‖f x‖^n)) :
    (∫⁻ x, ENNReal.ofReal (‖g x‖^n))≤ENNReal.ofReal A*(∫⁻ x, ENNReal.ofReal (‖f x‖^n)) := by
  rw [←ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun x => by positivity),
    ←ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun x => by positivity),
    ←ENNReal.ofReal_mul hA]
  exact ENNReal.ofReal_le_ofReal h

theorem convolution_layer_tail (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4))
    (t : ℝ) (ht : 0<t) :
    ENNReal.ofReal (t^2)*volume {x | t≤‖lineConvolution K f x‖}≤
      ENNReal.ofReal (4*A^2)*highLayerEnergy f t+
      ENNReal.ofReal (16*C^4)*(ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t) := by
  let fh := highAmplitude f t
  let fl := lowAmplitude f t
  have hhm : Measurable fh := highAmplitude_measurable f hf t
  have hlm : Measurable fl := lowAmplitude_measurable f hf t
  have hh2 : MemLp fh 2 volume := hf2.indicator (measurableSet_le measurable_const hf.norm)
  have hl4 : MemLp fl 4 volume := hf4.indicator (measurableSet_lt hf.norm measurable_const)
  have hhb (x : ℝ) : ‖fh x‖≤M := (amplitude_bound f t x).1.trans (hM x)
  have hlb (x : ℝ) : ‖fl x‖≤M := (amplitude_bound f t x).2.trans (hM x)
  have hhOut := (lineConvolution_energy_bound K hK hKm fh hhm hh2).1
  have hlOut := (lineConvolution_L4_bound K fl hK hKm hlm hl4).1
  have eh := normPower_lintegral_le_of_integral fh (lineConvolution K fh) 2
    (hh2.integrable_norm_pow (by decide)) (hhOut.integrable_norm_pow (by decide))
    (A^2) (sq_nonneg A) (boundedConvolution_L2_of_schwartz K hK hKm A hA h2 fh hhm hh2 M hhb)
  have el := normPower_lintegral_le_of_integral fl (lineConvolution K fl) 4
    (hl4.integrable_norm_pow (by decide)) (hlOut.integrable_norm_pow (by decide))
    (C^4) (by positivity) (boundedConvolution_L4_of_schwartz K hK hKm C hC h4 fl hlm hl4 M hlb)
  rw [highAmplitude_power] at eh
  rw [lowAmplitude_power] at el
  have hhTail := (normPower_tail (lineConvolution K fh) (lineConvolution_measurable K hKm fh hhm)
    2 (t/2) (by positivity)).trans (mul_le_mul_right eh _)
  have hlTail := (normPower_tail (lineConvolution K fl) (lineConvolution_measurable K hKm fl hlm)
    4 (t/2) (by positivity)).trans (mul_le_mul_right el _)
  have hset : {x | t≤‖lineConvolution K f x‖}⊆
      {x | t/2≤‖lineConvolution K fh x‖}∪{x | t/2≤‖lineConvolution K fl x‖} := by
    intro x hx
    change t≤‖lineConvolution K f x‖ at hx
    rw [convolution_amplitude_sum K f hK hf M hM t x] at hx
    by_contra hn
    simp only [mem_union,mem_ofPred_eq,not_or,not_le] at hn
    have htri := norm_add_le (lineConvolution K fh x) (lineConvolution K fl x)
    linarith
  have htail := (measure_mono hset).trans (measure_union_le (μ:=volume) _ _)
  have hc2 : ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2))=
      ENNReal.ofReal (4*A^2) := by
    rw [←ENNReal.ofReal_pow (by positivity),←ENNReal.ofReal_mul (by positivity),
      ←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp; ring
  have hc4 : ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4))=
      ENNReal.ofReal (16*C^4)*ENNReal.ofReal (t^(-2:ℝ)) := by
    rw [←ENNReal.ofReal_pow (by positivity),←ENNReal.ofReal_mul (by positivity),
      ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg ht.le,Real.rpow_two]
    field_simp; ring
  calc
    _ ≤ ENNReal.ofReal (t^2)*(volume {x | t/2≤‖lineConvolution K fh x‖}+
        volume {x | t/2≤‖lineConvolution K fl x‖}) := mul_le_mul_right htail _
    _ ≤ ENNReal.ofReal (t^2)*
        ((ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2))*highLayerEnergy f t+
        (ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4))*lowLayerEnergy f t) := by
      exact mul_le_mul_right (add_le_add (by simpa only [mul_assoc] using hhTail)
        (by simpa only [mul_assoc] using hlTail)) _
    _ = (ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2)))*highLayerEnergy f t+
        (ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4)))*lowLayerEnergy f t := by ring
    _ = _ := by rw [hc2,hc4,mul_assoc]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real interpolation at exponent three for bounded measurable inputs.
The proof integrates the two amplitude-dependent Markov bounds. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem highLayerEnergy_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (highLayerEnergy f) := by
  have hm : Measurable (fun p : ℝ×ℝ => if p.1≤‖f p.2‖ then ENNReal.ofReal (‖f p.2‖^2) else 0) :=
    ((hf.comp measurable_snd).norm.pow_const 2).ennreal_ofReal.ite
      (measurableSet_le measurable_fst (hf.comp measurable_snd).norm) measurable_const
  exact hm.lintegral_prod_right'

theorem lowLayerEnergy_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (lowLayerEnergy f) := by
  have hm : Measurable (fun p : ℝ×ℝ => if ‖f p.2‖<p.1 then ENNReal.ofReal (‖f p.2‖^4) else 0) :=
    ((hf.comp measurable_snd).norm.pow_const 4).ennreal_ofReal.ite
      (measurableSet_lt (hf.comp measurable_snd).norm measurable_fst) measurable_const
  exact hm.lintegral_prod_right'

theorem convolution_third_lintegral (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4)) :
    (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))≤
      ENNReal.ofReal (3*(4*A^2+16*C^4))*(∫⁻ x, ENNReal.ofReal (‖f x‖^3)) := by
  have hm := lineConvolution_measurable K hKm f hf
  have hlc : (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))=
      ENNReal.ofReal 3*(∫⁻ t in Ioi 0,
        ENNReal.ofReal (t^2)*volume {x | t≤‖lineConvolution K f x‖}) := by
    have hh := lintegral_rpow_eq_lintegral_meas_le_mul volume
        (Filter.Eventually.of_forall fun x => norm_nonneg (lineConvolution K f x))
        hm.norm.aemeasurable (by norm_num : 0<(3:ℝ))
    simp only [show (3:ℝ)-1=2 by norm_num,Real.rpow_ofNat] at hh
    rw [hh]
    congr 1
    apply lintegral_congr
    intro t
    rw [mul_comm]
  have hhigh := highLayerEnergy_measurable f hf
  have hlow := lowLayerEnergy_measurable f hf
  have hdom := lintegral_mono_ae (μ:=volume.restrict (Ioi (0:ℝ))) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact convolution_layer_tail K f hK hKm hf hf2 hf4 M hM A C hA hC h2 h4 t ht)
  rw [hlc]
  calc
    _ ≤ ENNReal.ofReal 3*(∫⁻ t in Ioi 0,
        ENNReal.ofReal (4*A^2)*highLayerEnergy f t+
        ENNReal.ofReal (16*C^4)*(ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t)) :=
      mul_le_mul_right hdom _
    _ = ENNReal.ofReal 3*(ENNReal.ofReal (4*A^2)*(∫⁻ x, ENNReal.ofReal (‖f x‖^3))+
        ENNReal.ofReal (16*C^4)*(∫⁻ x, ENNReal.ofReal (‖f x‖^3))) := by
      rw [lintegral_add_left (hhigh.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        highLayerEnergy_integral f hf,lowLayerEnergy_integral f hf]
    _ = _ := by
      rw [←add_mul,←mul_assoc,←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num)]

theorem memLp_two_four_integrable_cube (f : ℝ → ℂ) (hf : Measurable f)
    (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume) :
    Integrable (fun x => ‖f x‖^3) := by
  apply ((hf2.integrable_norm_pow (by decide : 2≠0)).add
    (hf4.integrable_norm_pow (by decide : 4≠0))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity : 0≤‖f x‖^3)]
  change ‖f x‖^3≤‖f x‖^2+‖f x‖^4
  nlinarith [sq_nonneg (‖f x‖-1),sq_nonneg (‖f x‖*(‖f x‖-1))]

theorem convolution_third_bound (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4)) :
    Integrable (fun x => ‖lineConvolution K f x‖^3) ∧
      (∫ x, ‖lineConvolution K f x‖^3)≤(3*(4*A^2+16*C^4))*(∫ x, ‖f x‖^3) := by
  have hlin := convolution_third_lintegral K f hK hKm hf hf2 hf4 M hM A C hA hC h2 h4
  have hfi := memLp_two_four_integrable_cube f hf hf2 hf4
  have hfinite := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => show 0≤‖f x‖^3 by positivity)).mp hfi.2
  have hfinal : (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))<⊤ :=
    hlin.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^3) := by
    refine ⟨(lineConvolution_measurable K hKm f hf).norm.pow_const 3 |>.aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)).mpr hfinal
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity),
    ←ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun x => by positivity),
    ←ENNReal.ofReal_mul (by positivity)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlin

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third-moment bound, including bounded measurable inputs needed
as explicit dual test functions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_two_four_constants : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^2)≤A^2*(∫ x, ‖f x‖^2) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^4)≤C^4*(∫ x, ‖f x‖^4) := by
  obtain ⟨A,hA,hTwo⟩ := sharpHilbert_uniform_L2
  obtain ⟨D,hD,hFour⟩ := sharpHilbert_uniform_fourth
  have hDle : D≤(D+1)^4 := by
    nlinarith [sq_nonneg D,pow_nonneg hD 3,pow_nonneg hD 4]
  refine ⟨A,D+1,hA,by positivity,?_⟩
  intro r R hr hrR f
  have h2 := hTwo r R hr hrR f
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2.2
  rw [←Lp.norm_toLp _ h2.1,ENNReal.toReal_ofReal (mul_nonneg hA.le (norm_nonneg _))] at hn
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,memLp_toL2_norm_sq volume _ h2.1] at hp
  have hfe : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [hfe] at hp
  exact ⟨hp,(hFour r R hr hrR f).2.trans
    (mul_le_mul_of_nonneg_right hDle (integral_nonneg fun x => by positivity))⟩

theorem sharpHilbert_uniform_third_bounded : ∃ E : ℝ, 0≤E ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : ℝ → ℂ, Measurable f →
      MemLp f 2 volume → MemLp f 4 volume →
      ∀ M : ℝ, (∀ x, ‖f x‖≤M) →
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^3) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^3)≤E*(∫ x, ‖f x‖^3) := by
  obtain ⟨A,C,hA,hC,hb⟩ := sharpHilbert_two_four_constants
  refine ⟨3*(4*A^2+16*C^4),by positivity,?_⟩
  intro r R hr hrR f hfm hf2 hf4 M hM
  exact convolution_third_bound (sharpTimeKernel r R) f
    (sharpTimeKernel_integrable r R hr (hr.trans_le hrR)) (sharpTimeKernel_measurable r R)
    hfm hf2 hf4 M hM A C hA.le hC.le
    (fun g => (hb r R hr hrR g).1) (fun g => (hb r R hr hrR g).2)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution duality for an integrable input and a bounded test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_pairing (K f g : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hf : Integrable f) (hfm : Measurable f)
    (hgm : Measurable g) (B : ℝ) (hgb : ∀ x, ‖g x‖≤B) :
    (∫ x, lineConvolution K f x*g x)=(∫ x, f x*reverseLineConvolution K g x) := by
  have hbase : Integrable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  have hJ : Integrable (fun p : ℝ×ℝ => (K p.2*f (p.1-p.2))*g p.1) := by
    apply (hbase.norm.mul_const B).mono' (by fun_prop)
    filter_upwards [] with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg _)
  have hbase' : Integrable (fun p : ℝ×ℝ => ‖f p.1‖*‖K p.2‖) := hf.norm.mul_prod hK.norm
  have hJ' : Integrable (fun p : ℝ×ℝ => (K p.2*f p.1)*g (p.1+p.2)) := by
    apply (hbase'.mul_const B).mono' (by fun_prop)
    filter_upwards [] with p
    simp only [norm_mul]
    calc
      _ ≤ (‖K p.2‖*‖f p.1‖)*B := mul_le_mul_of_nonneg_left (hgb _) (by positivity)
      _ = _ := by ring
  calc
    _ = ∫ x, ∫ t, (K t*f (x-t))*g x := by simp_rw [lineConvolution,integral_mul_const]
    _ = ∫ t, ∫ x, (K t*f (x-t))*g x := integral_integral_swap hJ
    _ = ∫ t, ∫ y, (K t*f y)*g (y+t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x : ℝ => (K t*f (x-t))*g x) t).symm
    _ = ∫ y, ∫ t, (K t*f y)*g (y+t) := (integral_integral_swap hJ').symm
    _ = _ := by
      have he (y t : ℝ) : (K t*f y)*g (y+t)=f y*(K t*g (y+t)) := by ring
      simp_rw [he,integral_const_mul]
      rfl

theorem reverseLineConvolution_conj (K g : ℝ → ℂ)
    (hodd : ∀ t, K (-t)= -K t) (hreal : ∀ t, conj (K t)=K t) (x : ℝ) :
    reverseLineConvolution K (fun y => conj (g y)) x= -conj (lineConvolution K g x) := by
  unfold reverseLineConvolution lineConvolution
  rw [←integral_neg_eq_self (fun t : ℝ => K t*conj (g (x+t)))]
  simp only [hodd,neg_mul,←sub_eq_add_neg]
  rw [integral_neg,←integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [map_mul,hreal]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ConvolutionBasicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and a uniform pointwise bound for convolution of an
integrable kernel with a Schwartz function. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_integrable (K f : ℝ → ℂ) (hK : Integrable K) (hf : Integrable f) :
    Integrable (lineConvolution K f) := by
  have hj : Integrable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  exact hj.integral_prod_left

theorem lineConvolution_bound_basic (K f : ℝ → ℂ) (hK : Integrable K)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (x : ℝ) :
    ‖lineConvolution K f x‖≤(∫ t, ‖K t‖)*B := by
  have hh := norm_integral_le_of_norm_le (hK.norm.mul_const B)
    (Filter.Eventually.of_forall fun t => show ‖K t*f (x-t)‖≤‖K t‖*B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _))
  rw [integral_mul_const] at hh
  exact hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpHilbertThreeHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform three-halves estimates by the explicit dual test and the
proved third-moment bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_odd (r R t : ℝ) : sharpTimeKernel r R (-t)= -sharpTimeKernel r R t := by
  unfold sharpTimeKernel
  simp only [abs_neg]
  split_ifs <;> simp

theorem sharpHilbert_uniform_three_halves : ∃ C : ℝ, 0<C ∧
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^(3/2:ℝ)) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^(3/2:ℝ))≤
        C^(3/2:ℝ)*(∫ x, ‖f x‖^(3/2:ℝ)) := by
  obtain ⟨E,hE,hThird⟩ := sharpHilbert_uniform_third_bounded
  obtain ⟨A,hA,hTwo⟩ := sharpHilbert_uniform_L2
  refine ⟨E+1,by positivity,?_⟩
  intro r R hr hrR f
  let K := sharpTimeKernel r R
  have hKi : Integrable K := sharpTimeKernel_integrable r R hr (hr.trans_le hrR)
  have hKm : Measurable K := sharpTimeKernel_measurable r R
  let g := oneDimensionalTruncatedHilbert r R f
  have hgm : Measurable g := lineConvolution_measurable K hKm f f.continuous.measurable
  have hg1 : Integrable g := lineConvolution_integrable K f hKi f.integrable
  have hg2 : MemLp g 2 volume := (hTwo r R hr hrR f).1
  let B := (∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f
  have hgb (x : ℝ) : ‖g x‖≤B := lineConvolution_bound_basic K f hKi
    (SchwartzMap.seminorm ℝ 0 0 f) (fun y => SchwartzMap.norm_le_seminorm ℝ f y) x
  let h := halfPowerDualTest g
  have hhm : Measurable h := halfPowerDualTest_measurable g hgm
  have hhp := halfPowerDualTest_memLp g hgm hg1 hg2
  have hhb (x : ℝ) : ‖h x‖≤B+1 := halfPowerDualTest_bound g B hgb x
  have hh3 : Integrable (fun x => ‖h x‖^3) := memLp_two_four_integrable_cube h hhm hhp.1 hhp.2
  have hgi : Integrable (fun x => ‖g x‖^(3/2:ℝ)) := by
    simpa only [h,halfPowerDualTest_norm_cube] using hh3
  let J := ∫ x, ‖g x‖^(3/2:ℝ)
  let F := ∫ x, ‖f x‖^(3/2:ℝ)
  have hJ : 0≤J := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hF : 0≤F := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  let v := oneDimensionalTruncatedHilbert r R h
  have hvm : Measurable v := lineConvolution_measurable K hKm h hhm
  have hvBound := hThird r R hr hrR h hhm hhp.1 hhp.2 (B+1) hhb
  have hv3 : MemLp v (ENNReal.ofReal (3:ℝ)) volume := by
    have hh : MemLp v 3 volume := (integrable_norm_rpow_iff hvm.aestronglyMeasurable
      (by norm_num : (3:ℝ≥0∞)≠0) (by norm_num)).mp (by simpa using hvBound.1)
    simpa using hh
  have hvEnergy : (∫ x, ‖v x‖^3)≤E*J := by
    simpa only [h,halfPowerDualTest_norm_cube] using hvBound.2
  have hpair := lineConvolution_pairing K f (fun x => conj (h x)) hKi hKm
    f.integrable f.continuous.measurable (by fun_prop) (B+1)
    (fun x => by simpa only [Complex.norm_conj] using hhb x)
  have hleft : (∫ x, g x*conj (h x))=(J:ℂ) := by
    simp only [h,halfPowerDualTest_pair,integral_complex_ofReal]
    rfl
  have hright : (∫ x, f x*reverseLineConvolution K (fun y => conj (h y)) x)=
      -(∫ x, f x*conj (v x)) := by
    simp_rw [reverseLineConvolution_conj K h (sharpTimeKernel_odd r R)
      (sharpTimeKernel_conj r R),mul_neg,integral_neg]
    rfl
  have hidentity : (J:ℂ)= -(∫ x, f x*conj (v x)) := hleft.symm.trans (hpair.trans hright)
  have hnorm : J=‖∫ x, f x*conj (v x)‖ := by
    have hh := congrArg norm hidentity
    simpa only [Complex.norm_real,Real.norm_of_nonneg hJ,norm_neg] using hh
  have hhold := integral_mul_norm_le_Lp_mul_Lq (p:=3/2) (q:=3)
    (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (f.memLp (ENNReal.ofReal (3/2:ℝ)) volume) hv3
  have hi : J≤F^(2/3:ℝ)*(∫ x, ‖v x‖^3)^(1/3:ℝ) := by
    calc
      J = ‖∫ x, f x*conj (v x)‖ := hnorm
      _ ≤ ∫ x, ‖f x*conj (v x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖*‖v x‖ := by simp only [norm_mul,Complex.norm_conj]
      _ ≤ _ := by simpa only [show (1/(3/2):ℝ)=2/3 by norm_num,Real.rpow_ofNat] using hhold
  refine ⟨hgi,?_⟩
  exact cubic_duality_estimate F J E hF hJ hE (hi.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (integral_nonneg fun x => by positivity) hvEnergy (by norm_num))
      (Real.rpow_nonneg hF _)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalHilbertProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The classical one-dimensional input required by the manuscript is
proved at the two required exponents. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PacketRepresentation

theorem horizontalHilbertInput_proved : HorizontalHilbertInput := by
  obtain ⟨C,hC,hthree⟩ := sharpHilbert_uniform_three_halves
  obtain ⟨D,hD,hfour⟩ := sharpHilbert_uniform_fourth
  let B := C+D+1
  have hB : 0<B := by dsimp [B]; positivity
  have hCB : C≤B := by dsimp [B]; linarith
  have hDpow : D≤B^4 := by
    have hsmall : D≤(D+1)^4 := by nlinarith [sq_nonneg D,pow_nonneg hD 3,pow_nonneg hD 4]
    exact hsmall.trans (pow_le_pow_left₀ (by positivity) (by dsimp [B]; linarith) 4)
  refine ⟨B,hB,?_⟩
  intro p hp r R hr hrR f
  rcases hp with rfl | rfl
  · obtain ⟨hi,he⟩ := hthree r R hr hrR f
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hC.le hCB (by norm_num))
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
  · obtain ⟨hi,he⟩ := hfour r R hr hrR f
    simp only [Real.rpow_ofNat]
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hDpow (integral_nonneg fun x => by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NarrowPartitionReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier reconstruction from a finite narrow-window partition. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_list_sum (l : List (SchwartzMap (ℝ×ℝ) ℂ)) (omega : ℝ×ℝ) :
    planarFourier l.sum omega=(l.map (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarFourier f omega)).sum := by
  induction l with
  | nil => simp [planarFourier]
  | cons f fs ih => simp only [List.sum_cons,planarFourier_add,List.map_cons,ih]

theorem narrowPartition_reconstruction (l : List NarrowWindow) (K : Set ℝ)
    (hpartition : ∀ x∈K, (l.map (fun q => q.2 x)).sum=1)
    (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hsupport : ∀ omega, planarFourier f omega≠0 → W*omega.2∈K) :
    (l.map (fun q => schwartzVerticalProjection q.2 W 0 f)).sum=f := by
  apply planar_schwartz_ext_fourier
  intro omega
  rw [planarFourier_list_sum]
  simp only [List.map_map,Function.comp_def,schwartzVerticalProjection_fourier,sub_zero]
  by_cases hz : planarFourier f omega=0
  · simp only [hz,mul_zero,List.map_const',List.sum_replicate,nsmul_zero]
  · have h := hpartition (W*omega.2) (hsupport omega hz)
    rw [List.sum_map_mul_right,h,one_mul]

theorem narrowProjection_absorb (q : NarrowWindow)
    (habs : ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x)
    (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection narrowBandProfile (q.1*W) 0
      (schwartzVerticalProjection q.2 W 0 f)=schwartzVerticalProjection q.2 W 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,sub_zero]
  rw [mul_assoc q.1 W omega.2,←mul_assoc,habs]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NarrowPartitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bound for the fixed narrow cutoff controls a finite partition of any
compact annulus. Its cost is independent of the common frequency dilation. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

private theorem list_sum_eLpNorm {α : Type*} (l : List α)
    (g : α → (ℝ×ℝ) → ℂ) (c : α → ℝ)
    (h : ∀ a∈l, 0 ≤ c a ∧ MemLp (g a) 2 planeMeasure ∧
      eLpNorm (g a) 2 planeMeasure≤ENNReal.ofReal (c a)) :
    MemLp (l.map g).sum 2 planeMeasure ∧
      eLpNorm (l.map g).sum 2 planeMeasure≤ENNReal.ofReal (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons]
    refine ⟨ha.2.1.add ht.1,?_⟩
    calc
      _ ≤ eLpNorm (g a) 2 planeMeasure+eLpNorm (as.map g).sum 2 planeMeasure :=
        eLpNorm_add_le ha.2.1.aestronglyMeasurable ht.1.aestronglyMeasurable (by norm_num)
      _ ≤ ENNReal.ofReal (c a)+ENNReal.ofReal (as.map c).sum := add_le_add ha.2.2 ht.2
      _ = _ := (ENNReal.ofReal_add ha.1 (List.sum_nonneg (by
        intro x hx
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
        exact (h b (List.mem_cons_of_mem _ hb)).1))).symm

theorem narrowPartitionCost_nonneg (l : List NarrowWindow) : 0≤narrowPartitionCost l := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  exact (verticalProjectionCost_pos q.2).le

theorem narrowPartition_PV_bound (l : List NarrowWindow) (K : Set ℝ)
    (habs : ∀ q∈l, 0<q.1 ∧ ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x)
    (hpartition : ∀ x∈K, (l.map (fun q => q.2 x)).sum=1)
    (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (B : ℝ) (hB : 0≤B)
    (hband : ∀ w : ℝ, 0<w → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
        2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
        2 planeMeasure≤ENNReal.ofReal (B*‖g.toLp 2 planeMeasure‖))
    (W : ℝ) (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hsupport : ∀ omega, planarFourier f omega≠0 → W*omega.2∈K) :
    MemLp (productSlopePrincipalValue u R f) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤
        ENNReal.ofReal ((B*narrowPartitionCost l)*‖f.toLp 2 planeMeasure‖) := by
  let g := fun q : NarrowWindow => schwartzVerticalProjection q.2 W 0 f
  have hpiece (q : NarrowWindow) (hq : q∈l) :
      MemLp (productSlopePrincipalValue u R (g q)) 2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue u R (g q)) 2 planeMeasure≤
          ENNReal.ofReal ((B*verticalProjectionCost q.2)*‖f.toLp 2 planeMeasure‖) := by
    have hh := hband (q.1*W) (mul_pos (habs q hq).1 hW) (g q)
    rw [narrowProjection_absorb q (habs q hq).2] at hh
    refine ⟨hh.1,hh.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hn := verticalSchwartzToL2_norm q.2 W hW f
    change ‖(g q).toLp 2 planeMeasure‖≤_ at hn
    nlinarith only [mul_le_mul_of_nonneg_left hn hB]
  have hs := list_sum_eLpNorm l (fun q => productSlopePrincipalValue u R (g q))
    (fun q => (B*verticalProjectionCost q.2)*‖f.toLp 2 planeMeasure‖) (fun q hq =>
      ⟨mul_nonneg (mul_nonneg hB (verticalProjectionCost_pos q.2).le) (norm_nonneg _),hpiece q hq⟩)
  have he : (l.map (fun q => productSlopePrincipalValue u R (g q))).sum=
      productSlopePrincipalValue u R f := by
    have hh := map_list_sum (productPVSchwartzLM u R hR hRs) (l.map g)
    change productSlopePrincipalValue u R (l.map g).sum=_ at hh
    rw [show (l.map g).sum=f from narrowPartition_reconstruction l K hpartition W f hsupport] at hh
    simpa only [List.map_map,Function.comp_def,productPVSchwartzLM_apply] using hh.symm
  rw [he] at hs
  have hc : (l.map (fun q => (B*verticalProjectionCost q.2)*‖f.toLp 2 planeMeasure‖)).sum=
      (B*narrowPartitionCost l)*‖f.toLp 2 planeMeasure‖ := by
    unfold narrowPartitionCost
    simp_rw [mul_assoc]
    rw [List.sum_map_mul_left,List.sum_map_mul_right]
  simpa only [hc] using hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ProductPVContinuity
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise principal value is continuous for continuous bounded
slope fields. The removable value at time zero is irrelevant to integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem productPV_eq_integral (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (R : ℝ)
    (hR : 0≤R) (z : ℝ×ℝ) :
    productSlopePrincipalValue u R f z=
      ∫ t in Set.Ioc 0 R, productPVIntegrand u f z t := by
  rw [productSlopePrincipalValue,intervalIntegral.integral_of_le hR]
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht _
  exact Function.update_of_ne ht _ _

theorem productPVIntegrand_bound (u : (ℝ×ℝ) → ℝ) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) (t : ℝ) :
    ‖productPVIntegrand u f z t‖≤2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ) :=
  productSymmetricIntegrand_bound u z (hub z) f (_root_.OAI.SchwartzMap.global_lipschitz f) t

theorem productPV_continuous (u : (ℝ×ℝ) → ℝ) (hu : Continuous u)
    (hub : ∀ z, |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R) :
    Continuous (productSlopePrincipalValue u R f) := by
  have he : productSlopePrincipalValue u R f=fun z =>
      ∫ t in Set.Ioc 0 R, productPVIntegrand u f z t :=
    funext (productPV_eq_integral u f R hR)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro z
  apply continuousAt_of_dominated (bound:=fun _ => 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ))
  · filter_upwards [] with z
    apply Measurable.aestronglyMeasurable
    unfold productPVIntegrand productSlopeSample
    fun_prop
  · exact Eventually.of_forall fun z => Eventually.of_forall (productPVIntegrand_bound u hub f z)
  · exact integrable_const _
  · filter_upwards [] with t
    unfold productPVIntegrand productSlopeSample
    fun_prop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedVerticalMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The multiplier is linear in its Schwartz symbol on bounded measurable
inputs. The input need not have finite L2 norm. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_dilate (p : SchwartzMap ℝ ℂ) (d W : ℝ) (hd : d≠0) (hW : W≠0) :
    lineProjectionKernel (dilatedSlopeWindow p d hd) W hW=
      lineProjectionKernel p (d*W) (mul_ne_zero hd hW) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineProjectionKernel (dilatedSlopeWindow p d hd) W hW) : SchwartzMap ℝ ℂ) eta=
    (𝓕 (lineProjectionKernel p (d*W) (mul_ne_zero hd hW)) : SchwartzMap ℝ ℂ) eta
  simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply]
  rw [mul_assoc]

theorem verticalMultiplier_dilate (p : SchwartzMap ℝ ℂ) (d W : ℝ) (hd : 0<d) (hW : 0<W)
    (f : (ℝ×ℝ) → ℂ) :
    verticalConvolution (verticalProfileKernel (dilatedSlopeWindow p d hd.ne') W 0) f=
      verticalConvolution (verticalProfileKernel p (d*W) 0) f := by
  simp only [←lineProjectionKernel_eq_verticalProfile _ W hW,
    ←lineProjectionKernel_eq_verticalProfile _ (d*W) (mul_pos hd hW),lineProjectionKernel_dilate]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularResolutionSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete symmetric finite annular partition converges to one away
from the zero vertical frequency. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyScale_last (N : ℕ) :
    (3/2:ℝ)^(2*N+1)*(2/3:ℝ)^N=(3/2:ℝ)^(N+1) := by
  have hcancel : (3/2:ℝ)^N*(2/3:ℝ)^N=1 := by
    rw [←mul_pow]
    norm_num
  rw [show 2*N+1=N+(N+1) by omega,pow_add]
  calc
    _ = ((3/2:ℝ)^N*(2/3:ℝ)^N)*(3/2:ℝ)^(N+1) := by ring
    _ = _ := by rw [hcancel,one_mul]

theorem reassemblySymbol_eq (N : ℕ) (s : ℝ) :
    reassemblySymbol N s=
      reassemblyLow ((16/27)*(2/3:ℝ)^N*s)-
        reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)*s) := by
  unfold reassemblySymbol
  have he (n : ℕ) : reassemblyScale N n*s=(3/2:ℝ)^n*((2/3:ℝ)^N*s) := by
    unfold reassemblyScale
    ring
  simp_rw [he]
  rw [reassemblyDifference_telescope]
  congr 1
  · congr 1
    ring
  · congr 1
    calc
      _ = (16/27)*((3/2:ℝ)^(2*N+1)*(2/3:ℝ)^N)*s := by ring
      _ = _ := by rw [reassemblyScale_last]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVFromNarrow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite frequency covering converts the narrow-band
hypothesis into uniform bounds for all dilated annular inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem fixedAnnulus_compact : IsCompact fixedAnnulus := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-2:ℝ) 2)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  · intro x hx
    exact abs_le.mp hx.2

theorem exists_annular_PV_constant : ∃ D : ℝ, 0<D ∧
    ∀ (u : (ℝ×ℝ) → ℝ) (R : ℝ), 0<R → R≤1/4 →
    ∀ B : ℝ, 0≤B →
      (∀ w : ℝ, 0<w → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
          2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
          2 planeMeasure≤ENNReal.ofReal (B*‖g.toLp 2 planeMeasure‖)) →
    ∀ (W : ℝ), 0<W → ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ omega, planarFourier f omega≠0 → W*omega.2∈fixedAnnulus) →
      MemLp (productSlopePrincipalValue u R f) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤
        ENNReal.ofReal ((B*D)*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨l,habs,hpartition⟩ := exists_finite_narrow_partition fixedAnnulus fixedAnnulus_compact
    (fun x hx => by intro he; norm_num [he,fixedAnnulus] at hx)
  refine ⟨1+narrowPartitionCost l,by linarith [narrowPartitionCost_nonneg l],?_⟩
  intro u R hR hRs B hB hband W hW f hsupport
  have h := narrowPartition_PV_bound l fixedAnnulus habs hpartition u R hR hRs B hB
    hband W hW f hsupport
  refine ⟨h.1,h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  nlinarith only [mul_nonneg hB (norm_nonneg (f.toLp 2 planeMeasure))]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ProductPVVerticalDecay
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Along every vertical sequence escaping to infinity the actual short
principal value tends to zero. Only boundedness of the direction is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem bounded_sample_tendsto_cocompact (u : (ℝ×ℝ) → ℝ)
    (hub : ∀ z, |u z|≤1) (x t : ℝ) (y : ℕ → ℝ)
    (hy : Tendsto (fun n => |y n|) atTop atTop) :
    Tendsto (fun n => productSlopeSample u t (x,y n)) atTop (cocompact (ℝ×ℝ)) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0,0)
  have hnorm : ∀ n, |y n|-|t|≤‖productSlopeSample u t (x,y n)‖ := by
    intro n
    have hmul : |t*u (x,y n)|≤|t| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (hub _)
    have hs := abs_sub_abs_le_abs_sub (y n) (t*u (x,y n))
    have hm : |y n-t*u (x,y n)|≤‖productSlopeSample u t (x,y n)‖ := by
      change ‖y n-t*u (x,y n)‖ ≤ max ‖x-t‖ ‖y n-t*u (x,y n)‖
      exact le_max_right _ _
    linarith
  have ht : Tendsto (fun n => ‖productSlopeSample u t (x,y n)‖) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp hy) (b+|t|)] with n hn
    linarith [hnorm n]
  change Tendsto (fun n => ‖productSlopeSample u t (x,y n)-(0:ℝ×ℝ)‖) atTop atTop
  simpa only [sub_zero] using ht

theorem productPV_vertical_decay (u : (ℝ×ℝ) → ℝ) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R) (x : ℝ)
    (y : ℕ → ℝ) (hy : Tendsto (fun n => |y n|) atTop atTop) :
    Tendsto (fun n => productSlopePrincipalValue u R f (x,y n)) atTop (𝓝 0) := by
  simp_rw [productPV_eq_integral u f R hR]
  have h := tendsto_integral_of_dominated_convergence
    (μ:=volume.restrict (Set.Ioc 0 R)) (fun _ => 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ))
    (F:=fun n t => productPVIntegrand u f (x,y n) t) (f:=fun _ => (0:ℂ))
    (fun n => by
      apply Measurable.aestronglyMeasurable
      unfold productPVIntegrand productSlopeSample
      fun_prop)
    (integrable_const _) (fun n => Eventually.of_forall
      (productPVIntegrand_bound u hub f (x,y n))) (by
      filter_upwards [] with t
      have hp := f.tendsto_cocompact.comp (bounded_sample_tendsto_cocompact u hub x t y hy)
      have hn := f.tendsto_cocompact.comp (bounded_sample_tendsto_cocompact u hub x (-t) y hy)
      simpa only [productPVIntegrand,sub_zero,smul_zero,Function.comp_def] using (hp.sub hn).const_smul t⁻¹)
  simpa only [integral_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScaledConvolutionLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small and large physical scales of convolution on bounded continuous
functions. The large-scale limit uses only decay along escaping sequences. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem scaledLineConvolution_eq (k f : ℝ → ℂ) (W : ℝ) (hW : 0<W) (y : ℝ) :
    lineConvolution (scaledTimeKernel k W) f y=∫ t, k t*f (y-W*t) := by
  let H := fun t : ℝ => k t*f (y-W*t)
  have he (t : ℝ) : scaledTimeKernel k W t*f (y-t)=(W⁻¹:ℂ)*H (t/W) := by
    unfold H scaledTimeKernel
    rw [mul_div_cancel₀ t hW.ne']
    ring
  simp only [lineConvolution,he]
  rw [integral_const_mul,Measure.integral_comp_div H W,abs_of_pos hW,Complex.real_smul,
    ←mul_assoc]
  have hwc : (W:ℂ)≠0 := by exact_mod_cast hW.ne'
  simp only [inv_mul_cancel₀ hwc,one_mul]
  rfl

theorem scaledLineConvolution_small (k f : ℝ → ℂ) (hk : Integrable k)
    (hfm : Measurable f) (hfc : Continuous f) (B : ℝ) (hf : ∀ y, ‖f y‖≤B)
    (W : ℕ → ℝ) (hW : ∀ n, 0<W n) (hWlim : Tendsto W atTop (𝓝 0)) (y : ℝ) :
    Tendsto (fun n => lineConvolution (scaledTimeKernel k (W n)) f y)
      atTop (𝓝 ((∫ t, k t)*f y)) := by
  simp_rw [scaledLineConvolution_eq k f _ (hW _)]
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖k t‖*B)
    (F:=fun n t => k t*f (y-W n*t)) (f:=fun t => k t*f y)
    (fun n => hk.aestronglyMeasurable.mul (hfm.comp (by fun_prop)).aestronglyMeasurable)
    (hk.norm.mul_const B) (fun n => Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)) (by
      filter_upwards [] with t
      have ht : Tendsto (fun n => y-W n*t) atTop (𝓝 y) := by
        simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (hWlim.mul_const t)
      exact (hfc.continuousAt.tendsto.comp ht).const_mul (k t))
  simpa only [integral_mul_const] using h

theorem scaledLineConvolution_large (k f : ℝ → ℂ) (hk : Integrable k)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ y, ‖f y‖≤B)
    (hdecay : ∀ y : ℕ → ℝ, Tendsto (fun n => |y n|) atTop atTop →
      Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (W : ℕ → ℝ) (hW : ∀ n, 0<W n) (hWlim : Tendsto W atTop atTop) (y : ℝ) :
    Tendsto (fun n => lineConvolution (scaledTimeKernel k (W n)) f y) atTop (𝓝 0) := by
  simp_rw [scaledLineConvolution_eq k f _ (hW _)]
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖k t‖*B)
    (F:=fun n t => k t*f (y-W n*t)) (f:=fun _ => (0:ℂ))
    (fun n => hk.aestronglyMeasurable.mul (hfm.comp (by fun_prop)).aestronglyMeasurable)
    (hk.norm.mul_const B) (fun n => Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)) (by
      filter_upwards [volume.ae_ne (0:ℝ)] with t ht
      have hg : Tendsto (fun n => |y-W n*t|) atTop atTop := by
        have hm := hWlim.atTop_mul_const (abs_pos.mpr ht)
        apply tendsto_atTop.mpr
        intro b
        filter_upwards [(tendsto_atTop.mp hm) (b+|y|)] with n hn
        have hh := abs_sub_abs_le_abs_sub (W n*t) y
        rw [abs_mul,abs_of_pos (hW n),abs_sub_comm] at hh
        linarith
      simpa only [mul_zero] using (hdecay (fun n => y-W n*t) hg).const_mul (k t))
  simpa only [integral_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite annular convolutions converge pointwise to the
actual principal value. No L2 estimate for that principal value is used. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem unsignedAnnularSymbol_eq (N : ℕ) :
    signedAnnularSymbol N (fun _ => true)=
      dilatedSlopeWindow reassemblyLow ((16/27)*(2/3:ℝ)^N) (by positivity)-
        dilatedSlopeWindow reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)) (by positivity) := by
  ext x
  simp only [signedAnnularSymbol,ite_true, if_true,sum_apply,dilatedSlopeWindow_apply,
    reassemblyDifferenceSchwartz_apply,sub_apply]
  exact reassemblySymbol_eq N x

theorem annularPVPartial_eq (N : ℕ) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hub : ∀ z, |u z|≤1) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    annularPVPartial N u R f=
      verticalConvolution (verticalProfileKernel reassemblyLow ((16/27)*(2/3:ℝ)^N) 0)
        (productSlopePrincipalValue u R f)-
      verticalConvolution (verticalProfileKernel reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)) 0)
        (productSlopePrincipalValue u R f) := by
  let T := boundedVerticalMultiplierLM 1 (by norm_num) (productSlopePrincipalValue u R f)
    (productSlopePrincipalValue_measurable u hum f f.differentiable R hR hRs)
    (2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R)
    (fun z => productSchwartzPV_pointwise_bound u z (hub z) f R hR)
  have hscale (p : SchwartzMap ℝ ℂ) (d : ℝ) (hd : 0<d) :
      T (dilatedSlopeWindow p d hd.ne')=
        verticalConvolution (verticalProfileKernel p d 0) (productSlopePrincipalValue u R f) := by
    dsimp only [T]
    rw [boundedVerticalMultiplierLM_apply,verticalMultiplier_dilate p d 1 hd (by norm_num),mul_one]
  have hs := congrArg T (unsignedAnnularSymbol_eq N)
  simp only [signedAnnularSymbol,ite_true, if_true,map_sum,map_sub] at hs
  simp_rw [hscale reassemblyDifferenceSchwartz _ (reassemblyScale_pos N _),
    hscale reassemblyLow _ (show (0:ℝ)<(16/27)*(2/3:ℝ)^N by positivity),
    hscale reassemblyLow _ (show (0:ℝ)<(16/27)*(3/2:ℝ)^(N+1) by positivity)] at hs
  exact hs

theorem reassemblyLow_kernel_mass : ∫ t, (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t=1 := by
  have he : (𝓕 (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=reassemblyLow :=
    FourierTransform.fourier_fourierInv_eq reassemblyLow
  have h := congrArg (fun q : SchwartzMap ℝ ℂ => q 0) he
  rw [reassemblyLow_one 0 (by norm_num)] at h
  rw [SchwartzMap.fourier_coe,Real.fourier_eq] at h
  simpa only [Real.inner_apply,mul_zero,neg_zero,Real.fourierChar.map_zero_eq_one,one_smul] using h

theorem annularPVPartial_tendsto (u : (ℝ×ℝ) → ℝ) (hu : Continuous u)
    (hub : ∀ z, |u z|≤1) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Tendsto (fun N => annularPVPartial N u R f z) atTop
      (𝓝 (productSlopePrincipalValue u R f z)) := by
  let F := productSlopePrincipalValue u R f
  let H := fun y : ℝ => F (z.1,y)
  let K : ℝ → ℂ := (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ)
  let B := 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R
  have hF : Continuous F := productPV_continuous u hu hub f R hR.le
  have hH : Continuous H := hF.comp (by fun_prop)
  have hb (y : ℝ) : ‖H y‖≤B := productSchwartzPV_pointwise_bound u _ (hub _) f R hR
  have hk : Integrable K := (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ).integrable
  have hs : Tendsto (fun N : ℕ => (16/27)*(2/3:ℝ)^N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2/3)
        (by norm_num : (2/3:ℝ)<1)).const_mul (16/27)
  have hl : Tendsto (fun N : ℕ => (16/27)*(3/2:ℝ)^(N+1)) atTop atTop := by
    have hh := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3/2)).const_mul_atTop
      (by norm_num : (0:ℝ)<(16/27)*(3/2))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    rw [pow_succ]
    ring
  have hsmall := scaledLineConvolution_small K H hk hH.measurable hH B hb
    (fun N => (16/27)*(2/3:ℝ)^N) (fun _ => by positivity) hs z.2
  have hlarge := scaledLineConvolution_large K H hk hH.measurable B hb
    (fun y hy => productPV_vertical_decay u hub f R hR.le z.1 y hy)
    (fun N => (16/27)*(3/2:ℝ)^(N+1)) (fun _ => by positivity) hl z.2
  have hm : (∫ t, K t)*H z.2=F z := by
    rw [show (∫ t, K t)=1 from reassemblyLow_kernel_mass,one_mul]
  rw [hm] at hsmall
  have he (N : ℕ) : annularPVPartial N u R f z=
      lineConvolution (scaledTimeKernel K ((16/27)*(2/3:ℝ)^N)) H z.2-
      lineConvolution (scaledTimeKernel K ((16/27)*(3/2:ℝ)^(N+1))) H z.2 := by
    rw [annularPVPartial_eq N u hu.measurable hub R hR hRs f]
    simp only [Pi.sub_apply,verticalConvolution,verticalProfileKernel,modulatedTimeKernel,
      zero_mul,Real.fourierChar.map_zero_eq_one,one_smul]
    rfl
  simpa only [he,sub_zero] using hsmall.sub hlarge

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandToFullProof
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform full-frequency principal-value bound from the narrow-band
hypothesis, using finite annular reconstruction and Fatou's lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem bandToFullInput_proved : BandToFullInput := by
  obtain ⟨D,hD,hannular⟩ := exists_annular_PV_constant
  intro B hB
  let E := B*D
  let C := 1+annularPVBoundConstant E
  have hC0 : 0≤annularPVBoundConstant E := by unfold annularPVBoundConstant; positivity
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro R hR hRs field hf hfb hband f
  let u := fun z => field (planeCoordinates z)
  have hum : Continuous u := (product_slope_lipschitz field hf).continuous
  have hub (z) : |u z|≤1 := (hfb _).trans (by norm_num)
  have hRquarter : R≤1/4 := by linarith
  have hrelative := hannular u R hR hRquarter B hB.le hband
  have hp (N : ℕ) := annularPVPartial_bound N field hf hfb R hR hRquarter E
    (mul_nonneg hB.le hD.le) hrelative f
  have hbound : eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤
      ENNReal.ofReal (annularPVBoundConstant E*‖f.toLp 2 planeMeasure‖) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
      (Eventually.of_forall (fun N => (hp N).2))
      (fun N => (hp N).1.aestronglyMeasurable)
    exact Eventually.of_forall (annularPVPartial_tendsto u hum hub R hR hRquarter f)
  refine ⟨⟨(productSlopePrincipalValue_measurable u hum.measurable f f.differentiable R hR
    hRquarter).aestronglyMeasurable,hbound.trans_lt ENNReal.ofReal_lt_top⟩,hbound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  dsimp only [C]
  nlinarith only [norm_nonneg (f.toLp 2 planeMeasure)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ThreeInputMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's main conclusions with the band-to-full input proved.
Only the three explicitly cited classical inputs remain as hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem uniform_truncation_of_three_published_inputs
    (hVariation : LepingleInput) (hLL : LaceyLiInput) (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  conditional_uniform_truncation hVariation hLL hH bandToFullInput_proved

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_TwoInputMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform short directional Hilbert transform estimates conditional on
Lacey–Li and martingale variation bounds, using frequency reassembly and
classical one-dimensional Hilbert estimates. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem uniform_truncation_of_two_published_inputs_oai
    (hVariation : LepingleInput) (hLL : LaceyLiInput) :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  uniform_truncation_of_three_published_inputs hVariation hLL horizontalHilbertInput_proved

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs_oai := @OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs_oai
