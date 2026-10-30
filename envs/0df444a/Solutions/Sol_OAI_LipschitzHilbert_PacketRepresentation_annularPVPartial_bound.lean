-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:23:33.645953+00:00
-- url     : https://prove2.me/submissions/168ee51a-4859-4691-9ddf-20b50c6aed05

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_lineConjugation_derivative_bound

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarPlancherel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-coordinate Plancherel and the common-frequency witness
needed for the actual planar packet Gram matrix. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

/-- Plancherel for the manuscript's product-coordinate Fourier transform. -/
theorem planar_integral_inner_fourier (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, inner ℂ (planarFourier f z) (planarFourier g z) ∂volume.prod volume)=
      ∫ z, inner ℂ (f z) (g z) ∂volume.prod volume := by
  calc
    _ = ∫ x : HilbertPlane, inner ℂ (𝓕 (liftPlanar f) x) (𝓕 (liftPlanar g) x) := by
      rw [integral_hilbertPlane]
      simp only [fourier_liftPlanar]
    _ = ∫ x : HilbertPlane, inner ℂ (liftPlanar f x) (liftPlanar g x) :=
      SchwartzMap.integral_inner_fourier_fourier (liftPlanar f) (liftPlanar g)
    _ = _ := by
      rw [integral_hilbertPlane]
      rfl

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

theorem verticalConvolution_uniform_bound (K : ℝ → ℂ) (hK : Integrable K)
    (f : ℝ×ℝ → ℂ) (C : ℝ) (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖verticalConvolution K f z‖≤C*∫ t, ‖K t‖ := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (z.1,z.2-t)‖≤C*‖K t‖ from by
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [verticalConvolution,integral_const_mul] using h

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

theorem reassemblyOuter_support (s : ℝ) (hs : reassemblyOuter s≠0) : 1 ≤ s ∧ s≤2 := by
  have hn : reassemblyOuterBump s≠0 := by
    intro hz
    exact hs (by simp only [reassemblyOuter_apply,hz,Complex.ofReal_zero])
  have hd : |s-3/2|<1/2 := by
    have hmem : s∈support reassemblyOuterBump := hn
    rw [reassemblyOuterBump.support_eq] at hmem
    simpa only [Metric.mem_ball,Real.dist_eq,reassemblyOuterBump] using hmem
  exact ⟨by linarith [(abs_lt.mp hd).1],by linarith [(abs_lt.mp hd).2]⟩

theorem reassemblyOuter_one (s : ℝ) (hs : 9/8 ≤ s ∧ s≤15/8) : reassemblyOuter s=1 := by
  have hd : s∈Metric.closedBall (3/2:ℝ) reassemblyOuterBump.rIn := by
    simp only [Metric.mem_closedBall,Real.dist_eq,reassemblyOuterBump]
    exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  simp only [reassemblyOuter_apply,reassemblyOuterBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_one (s : ℝ) (hs : |s|≤1) : reassemblyLow s=1 := by
  have hd : s∈Metric.closedBall (0:ℝ) reassemblyLowBump.rIn := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_zero (s : ℝ) (hs : 13/12≤|s|) : reassemblyLow s=0 := by
  have hd : reassemblyLowBump.rOut≤dist s 0 := by
    simpa only [Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.zero_of_le_dist hd,Complex.ofReal_zero]

theorem reassemblyDifference_small (s : ℝ) (hs : |s|≤9/8) : reassemblyDifference s=0 := by
  have h1 : |(16/27)*s|≤1 := by rw [abs_mul]; norm_num; linarith only [hs]
  have h2 : |(8/9)*s|≤1 := by rw [abs_mul]; norm_num; linarith only [hs]
  simp only [reassemblyDifference,reassemblyLow_one _ h1,reassemblyLow_one _ h2,sub_self]

theorem reassemblyDifference_large (s : ℝ) (hs : 117/64≤|s|) : reassemblyDifference s=0 := by
  have h1 : 13/12≤|(16/27)*s| := by rw [abs_mul]; norm_num; linarith only [hs]
  have h2 : 13/12≤|(8/9)*s| := by rw [abs_mul]; norm_num; linarith only [hs]
  simp only [reassemblyDifference,reassemblyLow_zero _ h1,reassemblyLow_zero _ h2,sub_self]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPositiveCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive half of the geometric low-pass difference is Schwartz
and is exactly covered by a fixed admissible enlarged cutoff. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyDifference_even (s : ℝ) : reassemblyDifference (-s)=reassemblyDifference s := by
  simp only [reassemblyDifference,reassemblyLow_apply,mul_neg,reassemblyLowBump.neg]

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

theorem lineProjectionToL2_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : 0≤M) (hq : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    ‖lineProjectionToL2 q W hW f‖≤M*‖f.toLp 2 volume‖ := by
  have h := lineSchwartzProjection_energy q W hW M hq f
  have ho := memLp_toL2_norm_sq volume _ ((lineSchwartzProjection q W hW f).memLp 2 volume)
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖lineProjectionToL2 q W hW f‖^2=_ at ho
  change ‖f.toLp 2 volume‖^2=_ at hf
  rw [←ho,←hf] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 (by simpa only [mul_pow] using h)

theorem lineL2Projection_onSchwartz (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) :
    lineL2Projection q W hW (f.toLp 2 volume)=(lineSchwartzProjection q W hW f).toLp 2 volume := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · refine ⟨SchwartzMap.seminorm ℝ 0 0 q,?_⟩
    exact lineProjectionToL2_bound q W hW _ (apply_nonneg _ _)
      (fun eta => SchwartzMap.norm_le_seminorm ℝ q eta)

theorem lineL2Projection_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : 0≤M) (hq : ∀ eta, ‖q eta‖≤M) :
    ‖lineL2Projection q W hW‖≤M := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact hM
  · exact lineProjectionToL2_bound q W hW M hM hq

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution on bounded L2 functions agrees with the continuous
extension of the corresponding Schwartz Fourier multiplier. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_L2_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hcf : MemLp (lineConvolution K f) 2 volume) (hcg : MemLp (lineConvolution K g) 2 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_energy_bound K hK hKm (f-g) (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have ho := memLp_toL2_norm_sq volume _ (hcf.sub hcg)
  have hi := memLp_toL2_norm_sq volume _ (hf.sub hg)
  rw [hcf.toLp_sub hcg] at ho
  rw [hf.toLp_sub hg] at hi
  rw [←ho,←hi] at he
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))).1
    (by simpa only [mul_pow] using he)

theorem lineL2Projection_on_bounded (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) :
    lineL2Projection q W hW (hf.toLp f)=
      (lineConvolution_energy_bound (lineProjectionKernel q W hW)
        (lineProjectionKernel q W hW).integrable (lineProjectionKernel q W hW).continuous.measurable
        f hfm hf).1.toLp (lineConvolution (lineProjectionKernel q W hW) f) := by
  let K := lineProjectionKernel q W hW
  let C := SchwartzMap.seminorm ℝ 0 0 q
  let L := ∫ t, ‖K t‖
  let T := lineL2Projection q W hW
  let y := (lineConvolution_energy_bound K K.integrable K.continuous.measurable f hfm hf).1.toLp
    (lineConvolution K f)
  change T (hf.toLp f)=y
  have hC : 0≤C := apply_nonneg _ _
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  have hT : ‖T‖≤C := lineL2Projection_bound q W hW C hC (fun x => SchwartzMap.norm_le_seminorm ℝ q x)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hn
  have hdpos : 0<‖T (hf.toLp f)-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let eps := ‖T (hf.toLp f)-y‖/(2*(C+L+1))
  have heps : 0<eps := div_pos hdpos (by positivity)
  obtain ⟨g,hg⟩ := hd.exists_dist_lt (hf.toLp f) heps
  let yg := (lineConvolution_energy_bound K K.integrable K.continuous.measurable
    g g.continuous.measurable (g.memLp 2 volume)).1.toLp (lineConvolution K g)
  have hTg : T (g.toLp 2 volume)=yg := by
    change lineL2Projection q W hW (g.toLp 2 volume)=_
    rw [lineL2Projection_onSchwartz]
    apply Lp.ext
    filter_upwards [(lineSchwartzProjection q W hW g).coeFn_toLp 2 volume,
      (lineConvolution_energy_bound K K.integrable K.continuous.measurable
        g g.continuous.measurable (g.memLp 2 volume)).1.coeFn_toLp] with x hx hy
    dsimp only [yg]
    rw [hx,hy]
    exact lineSchwartzProjection_eq_convolution q W hW g x
  have hc : ‖yg-y‖≤L*‖g.toLp 2 volume-hf.toLp f‖ :=
    lineConvolution_L2_difference K g f K.integrable K.continuous.measurable
      g.continuous.measurable hfm (g.memLp 2 volume) hf _ _
      (SchwartzMap.seminorm ℝ 0 0 g) B (fun x => SchwartzMap.norm_le_seminorm ℝ g x) hB
  have ht : ‖T (hf.toLp f)-T (g.toLp 2 volume)‖≤C*‖hf.toLp f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have htri := norm_add_le (T (hf.toLp f)-T (g.toLp 2 volume)) (T (g.toLp 2 volume)-y)
  rw [sub_add_sub_cancel,hTg] at htri
  rw [norm_sub_rev (g.toLp 2 volume) (hf.toLp f)] at hc
  simp only [dist_eq_norm] at hg
  have hmul : (C+L+1)*eps=‖T (hf.toLp f)-y‖/2 := by
    unfold eps
    field_simp [show C+L+1≠0 by positivity]
  rw [hTg] at ht
  have hs : ‖T (hf.toLp f)-y‖≤(C+L)*‖hf.toLp f-g.toLp 2 volume‖ := by
    nlinarith only [htri,ht,hc]
  have hsmall : (C+L)*‖hf.toLp f-g.toLp 2 volume‖<(C+L+1)*eps := by
    calc
      _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hg.le (add_nonneg hC hL)
      _ < _ := by nlinarith only [heps]
  rw [hmul] at hsmall
  linarith only [hs,hsmall,hdpos]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedConvolutionComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition and multiplier absorption for bounded inputs, before any
L2 membership of the input is known. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_assoc_bounded (K L : SchwartzMap ℝ ℂ) (f : ℝ → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    lineConvolution K (lineConvolution L f) x=
      lineConvolution (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K L) f x := by
  let M := ContinuousLinearMap.mul ℂ ℂ
  have hK : Integrable K := K.integrable
  have hL : Integrable L := L.integrable
  have hfg := hK.ae_convolution_exists M hL
  have hgk : ∀ᵐ y : ℝ, ConvolutionExistsAt L f y M volume := by
    exact Filter.Eventually.of_forall (lineConvolution_integrand_of_bounded L f hL hfm B hf)
  have hi : Integrable (fun p : ℝ×ℝ => (K p.2*L (p.1-p.2))*f (x-p.1)) := by
    apply (hK.convolution_integrand M hL).mul_bdd (c:=B)
    · exact (hfm.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => hf (x-p.1))
  have ha := convolution_assoc' M M M M (fun a b c => mul_assoc a b c) hfg hgk
    (hi.congr (Filter.Eventually.of_forall (fun p => mul_assoc (K p.2) (L (p.1-p.2)) (f (x-p.1)))))
  simpa only [lineConvolution,SchwartzMap.convolution_apply,convolution_def,M,ContinuousLinearMap.mul_apply'] using ha.symm

theorem lineKernel_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : W≠0) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (lineProjectionKernel p W hW) (lineProjectionKernel q W hW)=lineProjectionKernel q W hW := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (lineProjectionKernel p W hW) (lineProjectionKernel q W hW)) : SchwartzMap ℝ ℂ) eta=
    (𝓕 (lineProjectionKernel q W hW) : SchwartzMap ℝ ℂ) eta
  simp only [SchwartzMap.fourier_convolution,SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply',lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,
    dilatedSlopeWindow_apply,hpq]

theorem lineProjection_bounded_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : W≠0)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    lineConvolution (lineProjectionKernel p W hW)
      (lineConvolution (lineProjectionKernel q W hW) f) x=
      lineConvolution (lineProjectionKernel q W hW) f x := by
  rw [lineConvolution_assoc_bounded _ _ f hfm B hf,lineKernel_absorb p q hpq]

theorem verticalProjection_bounded_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : 0<W)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (B : ℝ) (hf : ∀ z, ‖f z‖≤B) (z : ℝ×ℝ) :
    verticalConvolution (verticalProfileKernel p W 0)
      (verticalConvolution (verticalProfileKernel q W 0) f) z=
      verticalConvolution (verticalProfileKernel q W 0) f z := by
  have hslice : Measurable (fun y : ℝ => f (z.1,y)) := hfm.comp (by fun_prop)
  have h := lineProjection_bounded_absorb p q hpq W hW.ne'
    (fun y => f (z.1,y)) hslice B (fun y => hf _) z.2
  simp only [lineProjectionKernel_eq_verticalProfile p W hW,
    lineProjectionKernel_eq_verticalProfile q W hW] at h
  exact h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTimeAverageEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating a quadratic short-time error costs the first absolute
kernel moment. This avoids a factor from the number of time scales. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortTimeQuotient_measurable (F : ℝ×(ℝ×ℝ) → ℂ) (hF : Measurable F) :
    Measurable (shortTimeQuotient F) := by
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    have hc : Continuous (fun p : ℝ×(ℝ×ℝ) => |p.1|) := by fun_prop
    exact (isClosed_le hc continuous_const).measurableSet
  unfold shortTimeQuotient
  exact ((measurable_fst.complex_ofReal.inv).mul hF).ite hs measurable_const

theorem shortTimeQuotient_energy (F : ℝ×(ℝ×ℝ) → ℂ) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B*t^2)
    (t : ℝ) :
    MemLp (fun z => shortTimeQuotient F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖shortTimeQuotient F (t,z)‖^2 ∂planeMeasure)≤B := by
  by_cases ht : |t|≤1/4
  · have hm := (hF t ht).const_mul (t⁻¹ : ℂ)
    refine ⟨by simpa only [shortTimeQuotient,ite_eq_left ht] using hm,?_⟩
    simp only [shortTimeQuotient,ite_eq_left ht,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,mul_pow]
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (henergy t ht) (sq_nonneg |t|⁻¹)
    apply hb.trans
    by_cases ht0 : t=0
    · simpa only [ht0,abs_zero,inv_zero,zero_pow (by decide : 2≠0),zero_mul] using hB
    · have htabs : |t|≠0 := abs_ne_zero.mpr ht0
      rw [inv_pow,←mul_assoc,←sq_abs t]
      rw [mul_comm (|t|^2)⁻¹ B,mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 htabs),mul_one]
  · simp only [shortTimeQuotient,ite_eq_right ht,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
    exact ⟨MemLp.zero',hB⟩

theorem shortTimeAverage_energy (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B*t^2) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then K t*F (t,z) else 0) 2 planeMeasure ∧
      (∫ z, ‖∫ t, if |t|≤1/4 then K t*F (t,z) else 0‖^2 ∂planeMeasure)≤
        (∫ t, |t| *‖K t‖)^2*B := by
  let K1 := fun t : ℝ => (t : ℂ)*K t
  have hK1m : Measurable K1 := measurable_id.complex_ofReal.mul hKm
  have hK1i : Integrable K1 := by
    apply hK1.mono' hK1m.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      simp only [K1,norm_mul,Complex.norm_real,Real.norm_eq_abs,le_refl]
  have heq (z : ℝ×ℝ) : (∫ t, K1 t*shortTimeQuotient F (t,z))=
      ∫ t, if |t|≤1/4 then K t*F (t,z) else 0 := by
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    by_cases hshort : |t|≤1/4
    · simp only [shortTimeQuotient,ite_eq_left hshort,K1]
      have hc : (t : ℂ)≠0 := by exact_mod_cast ht
      field_simp
    · simp only [shortTimeQuotient,ite_eq_right hshort,mul_zero]
  have havg := kernelAverage_energy K1 hK1m hK1i (shortTimeQuotient F)
    (shortTimeQuotient_measurable F hFm) B hB
    (fun t => (shortTimeQuotient_energy F B hB hF henergy t).1)
    (fun t => (shortTimeQuotient_energy F B hB hF henergy t).2)
  simp only [heq] at havg
  simpa only [K1,norm_mul,Complex.norm_real,Real.norm_eq_abs] using havg

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinality-independent square-function energy for the finite vertical bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planar_integral_norm_sq_fourier (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure)=∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := planar_integral_inner_fourier f f
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change (∫ omega, ((‖planarFourier f omega‖^2 : ℝ) : ℂ) ∂planeMeasure)=
    (∫ z, ((‖f z‖^2 : ℝ) : ℂ) ∂planeMeasure) at h
  simp only [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bin/sampling commutator is the integral of the actual sampling-order difference. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingCommutator_eq (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (t : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (z : ℝ×ℝ) :
    verticalSamplingCommutator K u t f z=
      ∫ s, K s*verticalSamplingDifference f u t s z := by
  have hi1 : Integrable (fun s => K s*f (z.1-t,z.2-s-t*u (z.1,z.2-s))) := by
    apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact (hK.aestronglyMeasurable.mul (f.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards [] with s
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  have hi2 : Integrable (fun s => K s*f (z.1-t,z.2-t*u z-s)) := by
    apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact (hK.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    · filter_upwards [] with s
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  change (∫ s, K s*f (z.1-t,z.2-s-t*u (z.1,z.2-s)))-
    (∫ s, K s*f (z.1-t,z.2-t*u z-s))=_
  rw [←integral_sub hi1 hi2]
  apply integral_congr_ae
  filter_upwards [] with s
  change K s*f (z.1-t,z.2-s-t*u (z.1,z.2-s))-
    K s*f (z.1-t,z.2-t*u z-s)=
    K s*(f (z.1-t,z.2-s-t*u (z.1,z.2-s))-f (z.1-t,z.2-s-t*u z))
  rw [show z.2-t*u z-s=z.2-s-t*u z by ring,mul_sub]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalCommutatorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-moment bound for the actual bin/sampling commutator, integrated
over the short times allowed by the horizontal localization. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingCommutator_joint_measurable (K : ℝ → ℂ) (hKm : Measurable K)
    (hK : Integrable K) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => verticalSamplingCommutator K u p.1 f p.2) := by
  have hm : Measurable (fun p : (ℝ×(ℝ×ℝ))×ℝ =>
      K p.2*verticalSamplingDifference f u p.1.1 p.2 p.1.2) := by
    change Measurable (fun p : (ℝ×(ℝ×ℝ))×ℝ => K p.2 *
      (f (p.1.2.1-p.1.1,p.1.2.2-p.2-p.1.1*u (p.1.2.1,p.1.2.2-p.2))-
        f (p.1.2.1-p.1.1,p.1.2.2-p.2-p.1.1*u p.1.2)))
    fun_prop
  have heq : (fun p : ℝ×(ℝ×ℝ) => verticalSamplingCommutator K u p.1 f p.2)=
      (fun p => ∫ s, K s*verticalSamplingDifference f u p.1 s p.2) := by
    funext p
    exact verticalSamplingCommutator_eq K hK u hum p.1 f p.2
  rw [heq]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSlopeCommutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact commutation of the vertical convolution and the frozen-direction
time integral. These identities precede all norm estimates. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_slopeKernelOperator (K T : ℝ → ℂ)
    (hK : Integrable K) (hT : Integrable T)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Integrable (fun t => T t*verticalConvolution K (sampledFunction u t f) z) ∧
      verticalConvolution K (slopeKernelOperator T u f) z=
        ∫ t, T t*verticalConvolution K (sampledFunction u t f) z := by
  let H := fun p : ℝ×ℝ => (K p.1*T p.2)*
    f (z.1-p.2,z.2-p.1-p.2*u (z.1,z.2-p.1))
  have hH : Integrable H (volume.prod volume) := by
    apply (hK.mul_prod hT).mul_bdd (c:=SchwartzMap.seminorm ℝ 0 0 f)
    · exact (f.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => SchwartzMap.norm_le_seminorm ℝ f _
  have hleft (s : ℝ) : K s*slopeKernelOperator T u f (z.1,z.2-s)=∫ t, H (s,t) := by
    rw [slopeKernelOperator,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    ring
  have hright (t : ℝ) : (∫ s, H (s,t))=T t*verticalConvolution K (sampledFunction u t f) z := by
    rw [verticalConvolution,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp only [H,sampledFunction]
    ring
  refine ⟨?_,?_⟩
  · simpa only [hright] using hH.integral_prod_right
  · change (∫ s, K s*slopeKernelOperator T u f (z.1,z.2-s))=_
    simp_rw [hleft]
    rw [integral_integral_swap hH]
    simp_rw [hright]

theorem verticalSlopeCommutator_eq (K T : ℝ → ℂ)
    (hKm : Measurable K) (hK : Integrable K) (hT : Integrable T)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K (slopeKernelOperator T u f) z-
      slopeKernelOperator T u (verticalConvolution K f) z=
        ∫ t, T t*verticalSamplingCommutator K u t f z := by
  obtain ⟨hi1,heq⟩ := verticalConvolution_slopeKernelOperator K T hK hT u hum f z
  have hqm := verticalConvolution_measurable K hKm f f.continuous.measurable
  have hi2 : Integrable (fun t => T t*sampledFunction u t (verticalConvolution K f) z) := by
    apply (hT.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0 f)*(∫ s, ‖K s‖))).mono'
    · exact hT.aestronglyMeasurable.mul (hqm.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (verticalConvolution_uniform_bound K hK f
        (SchwartzMap.seminorm ℝ 0 0 f) (SchwartzMap.norm_le_seminorm ℝ f) _) (norm_nonneg _)
  rw [heq]
  change (∫ t, T t*verticalConvolution K (sampledFunction u t f) z)-
    (∫ t, T t*sampledFunction u t (verticalConvolution K f) z)=_
  rw [←integral_sub hi1 hi2]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (mul_sub _ _ _).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeCommutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the estimated time average with the actual commutator of
the vertical bin and the horizontally localized operator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeCommutator_eq (K T : ℝ → ℂ)
    (hKm : Measurable K) (hK : Integrable K) (hT : Integrable T)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalConvolution K (shortSlopeOperator T u f) z-
      shortSlopeOperator T u (verticalConvolution K f) z=
        ∫ t, if |t|≤1/4 then T t*verticalSamplingCommutator K u t f z else 0 := by
  rw [shortSlopeOperator_eq_kernel,shortSlopeOperator_eq_kernel,
    verticalSlopeCommutator_eq K (shortTimeKernel T) hKm hK
      (shortTimeKernel_integrable T hT) u hum f z]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [shortTimeKernel]
  split_ifs <;> simp

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution on the L2 quotient, with its actual integral representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_congr_ae (K : ℝ → ℂ) (f g : ℝ×ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) (hfg : f=ᵐ[planeMeasure] g) :
    verticalConvolution K f=ᵐ[planeMeasure] verticalConvolution K g := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂planeMeasure,
      f (z.1,z.2-t)=g (z.1,z.2-t) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (verticalTranslation_measurePreserving t).quasiMeasurePreserving.ae hfg
  have hm : MeasurableSet {p : ℝ×(ℝ×ℝ) | f (p.2.1,p.2.2-p.1)=g (p.2.1,p.2.2-p.1)} :=
    measurableSet_eq_fun (hf.comp (by fun_prop)) (hg.comp (by fun_prop))
  have hs := (Measure.ae_ae_comm hm).mp he
  filter_upwards [hs] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  rw [ht]

theorem verticalConvolution_integrand_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    ∀ᵐ z ∂planeMeasure, Integrable (fun t => K t*f (z.1,z.2-t)) := by
  filter_upwards [(verticalConvolution_energy_joint_integrable K hK hKm f hfm hf).prod_left_ae]
    with z hz
  have hc := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (z.1,z.2-t)‖) hKm.norm (hfm.norm.comp (by fun_prop))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hK.norm hz).1
  exact hc.mono' ((hKm.mul (hfm.comp (by fun_prop))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))

theorem verticalConvolution_sub_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f g : ℝ×ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    verticalConvolution K (f-g)=ᵐ[planeMeasure]
      (verticalConvolution K f-verticalConvolution K g) := by
  filter_upwards [verticalConvolution_integrand_ae K hK hKm f hfm hf,
    verticalConvolution_integrand_ae K hK hKm g hgm hg] with z hfz hgz
  change (∫ t, K t*(f (z.1,z.2-t)-g (z.1,z.2-t)))=_
  simp_rw [mul_sub]
  exact integral_sub hfz hgz

theorem verticalConvolutionLp_coe (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    (verticalConvolutionLp K hK hKm f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] verticalConvolution K f :=
  MemLp.coeFn_toLp _

theorem verticalConvolutionLp_toLp (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (hf.toLp f)=
      (verticalConvolution_energy_bound K hK hKm f hfm hf).1.toLp (verticalConvolution K f) := by
  apply Lp.ext
  exact (verticalConvolutionLp_coe K hK hKm _).trans
    ((verticalConvolution_congr_ae K _ f (Lp.stronglyMeasurable (hf.toLp f)).measurable hfm hf.coeFn_toLp).trans
      (MemLp.coeFn_toLp _).symm)

theorem verticalConvolutionLp_sub (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f g : Lp ℂ 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (f-g)=
      verticalConvolutionLp K hK hKm f-verticalConvolutionLp K hK hKm g := by
  apply Lp.ext
  have hc := verticalConvolution_congr_ae K (show Lp ℂ 2 planeMeasure from f-g) ((f : (ℝ×ℝ)→ℂ)-(g : (ℝ×ℝ)→ℂ))
    (Lp.stronglyMeasurable (f-g)).measurable ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_sub f g)
  have hs := verticalConvolution_sub_ae K hK hKm f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  filter_upwards [verticalConvolutionLp_coe K hK hKm (f-g),hc,hs,
    verticalConvolutionLp_coe K hK hKm f,verticalConvolutionLp_coe K hK hKm g,
    Lp.coeFn_sub (verticalConvolutionLp K hK hKm f) (verticalConvolutionLp K hK hKm g)]
    with z h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h6]
  simp only [Pi.sub_apply,h4,h5]

theorem verticalConvolutionLp_norm (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    ‖verticalConvolutionLp K hK hKm f‖≤(∫ t, ‖K t‖)*‖f‖ := by
  have h := (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).2
  rw [←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn,
    ←memLp_toL2_norm_sq planeMeasure _
      (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1] at h
  change ‖verticalConvolutionLp K hK hKm f‖^2≤(∫ t, ‖K t‖)^2*‖f‖^2 at h
  have hn : 0≤∫ t, ‖K t‖ := integral_nonneg (fun t => norm_nonneg (K t))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg f))).mp
  simpa only [mul_pow] using h

theorem verticalConvolutionLp_continuous (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K) :
    Continuous (verticalConvolutionLp K hK hKm) := by
  apply LipschitzWith.continuous (K:=⟨∫ t, ‖K t‖,integral_nonneg fun _ => norm_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,←verticalConvolutionLp_sub]
  exact verticalConvolutionLp_norm K hK hKm (f-g)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinLpReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconstruction of a vertical frequency band for arbitrary L2 inputs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfileLp_continuous (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Continuous (verticalProfileLp q W center hW) :=
  verticalConvolutionLp_continuous _ (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable

theorem verticalProfileLp_schwartz (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalProfileLp q W center hW (f.toLp 2 planeMeasure)=
      (schwartzVerticalProjection q W center f).toLp 2 planeMeasure := by
  apply Lp.ext
  have heq := verticalConvolutionLp_toLp (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)
  change verticalProfileLp q W center hW (f.toLp 2 planeMeasure)=_ at heq
  rw [heq]
  have hmem := (verticalConvolution_energy_bound (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)).1
  filter_upwards [hmem.coeFn_toLp,
    (schwartzVerticalProjection q W center f).coeFn_toLp 2 planeMeasure] with z hz hz'
  rw [hz,hz',schwartzVerticalProjection_eq_convolution _ W center hW]

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

theorem verticalL2Projection_onSchwartz (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalL2Projection p w (f.toLp 2 planeMeasure)=(schwartzVerticalProjection p w 0 f).toLp 2 planeMeasure := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨verticalProjectionCost p,verticalSchwartzToL2_norm p w hw⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalHorizontalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical Fourier projections commute with measurable horizontal
cutoffs. The proof uses their actual convolution representatives. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_eq_profile (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w f=verticalProfileLp p w 0 hw f := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq (verticalL2Projection p w).continuous (verticalProfileLp_continuous p w 0 hw)
  · intro g
    rw [verticalL2Projection_onSchwartz _ _ hw,verticalProfileLp_schwartz]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoundedProjectedOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A band projection of a bounded input can be reproduced on L2 as
soon as that projected output is known to belong to L2. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_dilate (p : SchwartzMap ℝ ℂ) (d W : ℝ)
    (hd : d≠0) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (dilatedSlopeWindow p d hd) W 0 f=
      schwartzVerticalProjection p (d*W) 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,sub_zero,dilatedSlopeWindow_apply]
  rw [mul_assoc]

theorem verticalL2Projection_on_projected_bounded (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : 0<W)
    (F : (ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ) (hFb : ∀ z, ‖F z‖≤B)
    (hG : MemLp (verticalConvolution (verticalProfileKernel q W 0) F) 2 planeMeasure) :
    verticalL2Projection p W (hG.toLp (verticalConvolution (verticalProfileKernel q W 0) F))=
      hG.toLp (verticalConvolution (verticalProfileKernel q W 0) F) := by
  let G := verticalConvolution (verticalProfileKernel q W 0) F
  have hGm : Measurable G := verticalConvolution_measurable _
    (verticalProfileKernel_continuous q W 0).measurable F hFm
  rw [verticalL2Projection_eq_profile p W hW,verticalProfileLp,
    verticalConvolutionLp_toLp _ _ _ G hGm hG]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (verticalConvolution_energy_bound
    (verticalProfileKernel p W 0) (verticalProfileKernel_integrable p W 0 hW)
    (verticalProfileKernel_continuous p W 0).measurable G hGm hG).1,hG.coeFn_toLp] with z hz hz'
  rw [hz,hz']
  exact verticalProjection_bounded_absorb p q hpq W hW F hFm B hFb z

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

theorem reassemblyPositive_halfsum_nonneg (s : ℝ) (hs : 0 ≤ s) :
    reassemblyPositive s+reassemblyPositive (-s)=reassemblyDifference s := by
  have hminus : reassemblyOuter (-s)=0 := by
    by_contra hn
    have h := (reassemblyOuter_support (-s) hn).1
    linarith only [h,hs]
  rw [reassemblyPositive_apply,reassemblyPositive_apply,hminus,zero_mul,add_zero]
  by_cases hd : reassemblyDifference s=0
  · simp only [hd,mul_zero]
  · have hlo : 9/8 < |s| := lt_of_not_ge (fun h => hd (reassemblyDifference_small s h))
    have hhi : |s|<117/64 := lt_of_not_ge (fun h => hd (reassemblyDifference_large s h))
    rw [abs_of_nonneg hs] at hlo hhi
    rw [reassemblyOuter_one s ⟨hlo.le,by linarith only [hhi]⟩,one_mul]

theorem reassemblyPositive_halfsum (s : ℝ) :
    reassemblyPositive s+reassemblyPositive (-s)=reassemblyDifference s := by
  by_cases hs : 0 ≤ s
  · exact reassemblyPositive_halfsum_nonneg s hs
  · simpa only [neg_neg,reassemblyDifference_even,add_comm] using
      reassemblyPositive_halfsum_nonneg (-s) (neg_nonneg.mpr (le_of_not_ge hs))

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

theorem reassemblyOuter_norm (s : ℝ) : ‖reassemblyOuter s‖≤1 := by
  rw [reassemblyOuter_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg reassemblyOuterBump.nonneg]
  exact reassemblyOuterBump.le_one

theorem reassemblyDifference_norm (s : ℝ) : ‖reassemblyDifference s‖≤2 :=
  (norm_sub_le _ _).trans (by linarith only [reassemblyLow_norm ((16/27)*s),reassemblyLow_norm ((8/9)*s)])

theorem geometric_annuli_separated (j k : ℤ) (x : ℝ) (hjk : j+2≤k) :
    reassemblyDifference ((3/2:ℝ)^j*x)=0 ∨ reassemblyDifference ((3/2:ℝ)^k*x)=0 := by
  by_contra hn
  have hj : reassemblyDifference ((3/2:ℝ)^j*x)≠0 := fun h => hn (Or.inl h)
  have hk : reassemblyDifference ((3/2:ℝ)^k*x)≠0 := fun h => hn (Or.inr h)
  have hjlo : 9/8 < |(3/2:ℝ)^j*x| := lt_of_not_ge (fun h => hj (reassemblyDifference_small _ h))
  have hkhi : |(3/2:ℝ)^k*x|<117/64 := lt_of_not_ge (fun h => hk (reassemblyDifference_large _ h))
  have hpow : (3/2:ℝ)^j*(9/4)≤(3/2:ℝ)^k := by
    calc
      _ = (3/2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
  have hscale := mul_le_mul_of_nonneg_right hpow (abs_nonneg x)
  have habs (n : ℤ) : |(3/2:ℝ)^n*x|=(3/2:ℝ)^n*|x| := by
    rw [abs_mul,abs_of_pos (zpow_pos (by norm_num) _)]
  rw [habs j] at hjlo
  rw [habs k] at hkhi
  nlinarith only [hscale,hjlo,hkhi]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_VerticalFrameBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pointwise square bound for finitely many vertical multipliers gives
the same L2 square bound, with no dependence on the number of scales. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {ι : Type*}

theorem verticalFrame_schwartz (I : Finset ι) (p : ι → SchwartzMap ℝ ℂ) (w : ι → ℝ)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖p i (w i*eta)‖^2)≤M)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∑ i∈I, ∫ z, ‖schwartzVerticalProjection (p i) (w i) 0 f z‖^2 ∂planeMeasure)≤
      M*∫ z, ‖f z‖^2 ∂planeMeasure := by
  have heq (i : ι) := planar_integral_norm_sq_fourier (schwartzVerticalProjection (p i) (w i) 0 f)
  have hi (i : ι) : Integrable (fun omega =>
      ‖planarFourier (schwartzVerticalProjection (p i) (w i) 0 f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzVerticalProjection (p i) (w i) 0 f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have hfi : Integrable (fun omega => ‖planarFourier f omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ i∈I, ∫ omega, ‖planarFourier (schwartzVerticalProjection (p i) (w i) 0 f) omega‖^2 ∂planeMeasure :=
      Finset.sum_congr rfl (fun i _ => (heq i).symm)
    _ = ∫ omega, ∑ i∈I, ‖planarFourier (schwartzVerticalProjection (p i) (w i) 0 f) omega‖^2 ∂planeMeasure :=
      (integral_finsetSum I (fun i _ => hi i)).symm
    _ ≤ ∫ omega, M*‖planarFourier f omega‖^2 ∂planeMeasure := by
      apply integral_mono (integrable_finsetSum I (fun i _ => hi i)) (hfi.const_mul M)
      intro omega
      simp only [schwartzVerticalProjection_fourier,sub_zero,norm_mul,mul_pow]
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hM omega.2) (sq_nonneg _)
    _ = _ := by rw [integral_const_mul,planar_integral_norm_sq_fourier]

theorem verticalFrame_L2 (I : Finset ι) (p : ι → SchwartzMap ℝ ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖p i (w i*eta)‖^2)≤M)
    (f : Lp ℂ 2 planeMeasure) :
    (∑ i∈I, ‖verticalL2Projection (p i) (w i) f‖^2)≤M*‖f‖^2 := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro g
    have h := verticalFrame_schwartz I p w M hM g
    have hp (i : ι) : ‖verticalL2Projection (p i) (w i) (g.toLp 2 planeMeasure)‖^2=
        ∫ z, ‖schwartzVerticalProjection (p i) (w i) 0 g z‖^2 ∂planeMeasure := by
      rw [verticalL2Projection_onSchwartz _ _ (hw i)]
      exact memLp_toL2_norm_sq planeMeasure _ ((schwartzVerticalProjection (p i) (w i) 0 g).memLp 2 planeMeasure)
    have hg : ‖g.toLp 2 planeMeasure‖^2=∫ z, ‖g z‖^2 ∂planeMeasure :=
      memLp_toL2_norm_sq planeMeasure g (g.memLp 2 planeMeasure)
    simpa only [hp,hg] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnnularLowerFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete annular resolution also supplies the lower square-frame
bound: at each frequency only three of its summands can be nonzero. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem natural_annular_nonzero_count (I : Finset ℕ) (x : ℝ) :
    (I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)
  change A.card≤3
  have hsep (j k : ℕ) (hjk : j+2≤k) :
      reassemblyDifference ((3/2:ℝ)^j*x)=0 ∨ reassemblyDifference ((3/2:ℝ)^k*x)=0 := by
    simpa only [zpow_natCast] using geometric_annuli_separated (j:ℤ) (k:ℤ) x (by exact_mod_cast hjk)
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjnz := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hknz := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        have hkj : k+2≤j := by omega
        exact (hsep k j hkj).elim hknz hjnz
      · by_contra hn
        have hjk : j+2≤k := by omega
        exact (hsep j k hjk).elim hjnz hknz
    apply (Finset.card_le_card hsub).trans
    rw [Nat.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega


theorem natural_annular_square_sum (I : Finset ℕ) (x : ℝ) :
    (∑ n∈I, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2)≤12 := by
  classical
  let A := I.filter (fun n => reassemblyDifference ((3/2:ℝ)^n*x)≠0)
  have heq : (∑ n∈I, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2)=
      ∑ n∈A, ‖reassemblyDifference ((3/2:ℝ)^n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : reassemblyDifference ((3/2:ℝ)^n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  rw [heq]
  calc
    _ ≤ ∑ n∈A, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [show (2:ℝ)^2=4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (reassemblyDifference_norm ((3/2:ℝ)^n*x)) 2
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by
      have hc : (A.card:ℝ)≤3 := by exact_mod_cast natural_annular_nonzero_count I x
      linarith

theorem reassemblyScale_square_sum (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range (2*N+1), ‖reassemblyDifference (reassemblyScale N n*x)‖^2)≤12 := by
  have he (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
    unfold reassemblyScale
    ring
  simpa only [he] using natural_annular_square_sum (Finset.range (2*N+1)) ((2/3:ℝ)^N*x)

theorem annular_upper_frame (N : ℕ) (f : Lp ℂ 2 planeMeasure) :
    (∑ n∈Finset.range (2*N+1),
      ‖verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n) f‖^2)≤12*‖f‖^2 := by
  apply verticalFrame_L2 _ _ _ (reassemblyScale_pos N) 12
  intro eta
  simpa only [reassemblyDifferenceSchwartz_apply] using reassemblyScale_square_sum N eta

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SignedAnnularSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All signed finite annular multipliers have the same Mihlin bounds.
The proof uses only the fixed support annulus and its finite overlap. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem iteratedDeriv_tsupport_subset (q : ℝ → ℂ) (r : ℕ) :
    tsupport (iteratedDeriv r q) ⊆ tsupport q := by
  induction r with
  | zero => simp only [iteratedDeriv_zero,subset_refl]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem reassemblyDifference_tsupport :
    tsupport reassemblyDifference ⊆ {x : ℝ | 9/8≤|x| ∧ |x|≤117/64} := by
  apply closure_minimal
  · intro x hx
    exact ⟨(lt_of_not_ge (fun h => hx (reassemblyDifference_small x h))).le,
      (lt_of_not_ge (fun h => hx (reassemblyDifference_large x h))).le⟩
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)

theorem reassemblyDifference_derivative_support (r : ℕ) (x : ℝ)
    (hx : iteratedDeriv r reassemblyDifference x≠0) :
    9/8≤|x| ∧ |x|≤117/64 :=
  reassemblyDifference_tsupport (iteratedDeriv_tsupport_subset _ r (subset_closure hx))

theorem natural_closed_annulus_count (I : Finset ℕ) (x : ℝ) :
    (I.filter (fun n => 9/8≤|(3/2:ℝ)^n*x| ∧ |(3/2:ℝ)^n*x|≤117/64)).card≤3 := by
  classical
  let A := I.filter (fun n => 9/8≤|(3/2:ℝ)^n*x| ∧ |(3/2:ℝ)^n*x|≤117/64)
  change A.card≤3
  have hsep (j k : ℕ) (hjk : j+2≤k)
      (hj : 9/8≤|(3/2:ℝ)^j*x|) (hk : |(3/2:ℝ)^k*x|≤117/64) : False := by
    have hpow : (3/2:ℝ)^j*(9/4)≤(3/2:ℝ)^k := by
      calc
        _ = (3/2:ℝ)^(j+2) := by rw [pow_add]; norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hjk
    have hscale := mul_le_mul_of_nonneg_right hpow (abs_nonneg x)
    have habs (n : ℕ) : |(3/2:ℝ)^n*x|=(3/2:ℝ)^n*|x| := by
      rw [abs_mul,abs_of_pos (by positivity)]
    rw [habs] at hj hk
    nlinarith only [hj,hk,hscale]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjmem := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hkmem := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k j (by omega) hkmem.1 hjmem.2
      · by_contra hn
        exact hsep j k (by omega) hjmem.1 hkmem.2
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem signedAnnularSymbol_derivative (N r : ℕ) (s : ℕ → Bool) (x : ℝ) :
    iteratedDeriv r (signedAnnularSymbol N s) x=
      ∑ n∈Finset.range (2*N+1), if s n then
        (reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)
      else -((reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)) := by
  let q (n : ℕ) : SchwartzMap ℝ ℂ :=
    if s n then dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'
    else -dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne'
  have hfun : (signedAnnularSymbol N s : ℝ → ℂ)=fun y => ∑ n∈Finset.range (2*N+1), q n y := by
    funext y
    simp only [signedAnnularSymbol,q,sum_apply]
  rw [hfun,iteratedDeriv_fun_sum (fun n _ => ((q n).smooth r).contDiffAt)]
  apply Finset.sum_congr rfl
  intro n _
  have hd : iteratedDeriv r
      (dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
        (reassemblyScale_pos N n).ne') x=
      (reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x) := by
    change iteratedDeriv r (fun y => reassemblyDifferenceSchwartz (reassemblyScale N n*y)) x=_
    rw [iteratedDeriv_comp_const_smul (reassemblyDifferenceSchwartz.smooth r)]
    rfl
  dsimp only [q]
  split_ifs
  · exact hd
  · change iteratedDeriv r (fun y => -(dilatedSlopeWindow reassemblyDifferenceSchwartz
      (reassemblyScale N n) (reassemblyScale_pos N n).ne' y)) x=_
    rw [iteratedDeriv_fun_neg,hd]

theorem signedAnnularSymbol_mihlin (N r : ℕ) (s : ℕ → Bool) (x : ℝ) :
    |x|^r*‖iteratedDeriv r (signedAnnularSymbol N s) x‖≤
      3*(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz := by
  classical
  let A := (Finset.range (2*N+1)).filter (fun n =>
    9/8≤|reassemblyScale N n*x| ∧ |reassemblyScale N n*x|≤117/64)
  let v (n : ℕ) : ℂ := if s n then
      (reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)
    else -((reassemblyScale N n)^r • iteratedDeriv r reassemblyDifference (reassemblyScale N n*x))
  have hcard : (A.card:ℝ)≤3 := by
    have he (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
      unfold reassemblyScale
      ring
    exact_mod_cast (show A.card≤3 by
      simpa only [A,he] using natural_closed_annulus_count (Finset.range (2*N+1)) ((2/3:ℝ)^N*x))
  have heq : (∑ n∈Finset.range (2*N+1),v n)=∑ n∈A,v n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,reassemblyDifference_derivative_support r _ h⟩)
    dsimp only [v]
    simp only [hz,smul_zero,neg_zero,ite_self]
  have hS : 0≤SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz := apply_nonneg _ _
  have hterm (n : ℕ) (hn : n∈A) :
      |x|^r*‖v n‖≤(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz := by
    have hb := (Finset.mem_filter.mp hn).2.2
    have hnorm : ‖v n‖=(reassemblyScale N n)^r*
        ‖iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)‖ := by
      dsimp only [v]
      split_ifs <;> simp only [norm_neg,norm_smul,Real.norm_eq_abs,
        abs_of_pos (pow_pos (reassemblyScale_pos N n) r)]
    rw [hnorm,←mul_assoc,←mul_pow]
    have habs : |x| *reassemblyScale N n=|reassemblyScale N n*x| := by
      rw [abs_mul,abs_of_pos (reassemblyScale_pos N n)]
      ring
    rw [habs]
    apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hb r)
      (show ‖iteratedDeriv r reassemblyDifference (reassemblyScale N n*x)‖≤
        SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz by
        have hh := reassemblyDifferenceSchwartz.le_seminorm' ℝ 0 r (reassemblyScale N n*x)
        have he : (reassemblyDifferenceSchwartz : ℝ → ℂ)=reassemblyDifference := rfl
        rw [he] at hh
        simpa only [pow_zero,one_mul] using hh)
      (norm_nonneg _) (by positivity)
  rw [signedAnnularSymbol_derivative]
  change |x|^r*‖∑ n∈Finset.range (2*N+1),v n‖≤_
  rw [heq]
  calc
    _ ≤ |x|^r*(∑ n∈A, ‖v n‖) := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ n∈A, |x|^r*‖v n‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _n∈A, (117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz :=
      Finset.sum_le_sum hterm
    _ = (A.card:ℝ)*((117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz) := by simp
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hcard (show
      0≤(117/64:ℝ)^r*SchwartzMap.seminorm ℝ 0 r reassemblyDifferenceSchwartz by positivity)]

theorem signedAnnularMihlinConstant_nonneg : 0 ≤ signedAnnularMihlinConstant := by
  exact Finset.sum_nonneg (fun r _ => by positivity)

theorem signedAnnularSymbol_mihlin_four (N r : ℕ) (hr : r≤4) (s : ℕ → Bool) (x : ℝ) :
    |x|^r*‖iteratedDeriv r (signedAnnularSymbol N s) x‖ ≤ signedAnnularMihlinConstant := by
  apply (signedAnnularSymbol_mihlin N r s x).trans
  unfold signedAnnularMihlinConstant
  exact Finset.single_le_sum
    (f:=fun i : ℕ => (3:ℝ)*(117/64:ℝ)^i*SchwartzMap.seminorm ℝ 0 i reassemblyDifferenceSchwartz)
    (fun i _ => by positivity)
    (Finset.mem_range.mpr (show r<5 by omega))

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

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineDerivativeCommutatorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The differentiated Lipschitz commutator has its actual bounded L2
extension, with the uniform constant proved by dyadic decomposition. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineCommutatorNormConstant_nonneg : 0≤lineCommutatorNormConstant := Real.sqrt_nonneg _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual one-dimensional composition operators with uniform L2
bounds from the inverse Lipschitz estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineCompositionToL2_bound (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi)
    (f : SchwartzMap ℝ ℂ) : ‖lineCompositionToL2 phi hm ha f‖≤2*‖f.toLp 2 volume‖ := by
  have hc := line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)
  have hn := memLp_toL2_norm_sq volume _ hc.1
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖lineCompositionToL2 phi hm ha f‖^2=_ at hn
  change ‖f.toLp 2 volume‖^2=_ at hf
  have hh : ‖lineCompositionToL2 phi hm ha f‖^2≤2*‖f.toLp 2 volume‖^2 := by
    rw [hn,hf]
    exact hc.2
  nlinarith [norm_nonneg (lineCompositionToL2 phi hm ha f),norm_nonneg (f.toLp 2 volume)]

theorem lineCompositionL2_onSchwartz (phi : ℝ → ℝ) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (f : SchwartzMap ℝ ℂ) :
    lineCompositionL2 phi hm ha (f.toLp 2 volume)=lineCompositionToL2 phi hm ha f := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨2,lineCompositionToL2_bound phi hm ha⟩

theorem lineCompositionL2_bound (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    ‖lineCompositionL2 phi hm ha‖≤2 := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · norm_num
  · exact lineCompositionToL2_bound phi hm ha

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLpDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated strong differentiation for the line L2 functions used in
the sampling flow. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineLp_tendsto_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → ℝ → ℂ) (g : ℝ → ℂ) (hF : ∀ i, MemLp (F i) 2 volume)
    (hg : MemLp g 2 volume) (w : ℝ → ℝ)
    (hw : Integrable (fun y => w y^2))
    (hb : ∀ᶠ i in l, ∀ y, ‖F i y-g y‖≤w y)
    (hlim : ∀ y, Tendsto (fun i => F i y) l (𝓝 (g y))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hg.toLp g)) := by
  have hint : Tendsto (fun i => ∫ y, ‖F i y-g y‖^2) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (F:=fun i y => ‖F i y-g y‖^2) (f:=fun _ => (0:ℝ)) (fun y => w y^2)
      (Eventually.of_forall fun i => ((hF i).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      (by
        filter_upwards [hb] with i hi
        exact Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hi y) 2)
      hw (Eventually.of_forall fun y => by
        simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
          ((hlim y).sub_const (g y)).norm.pow 2)
    simpa only [integral_zero] using hh
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF g hg).mpr
  have he (i : ι) : eLpNorm (F i-g) 2 volume=
      ENNReal.ofReal (Real.sqrt (∫ y, ‖F i y-g y‖^2)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) ((hF i).sub hg)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp hint)
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using hh

theorem lineLp_hasDerivAt (F : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ)
    (hF : ∀ s, MemLp (F s) 2 volume) (hg : MemLp g 2 volume)
    (w : ℝ → ℝ) (hw : Integrable (fun y => w y^2))
    (hb : ∀ᶠ s in 𝓝[≠] t, ∀ y, ‖slope (fun r => F r y) t s-g y‖≤w y)
    (hd : ∀ y, HasDerivAt (fun s => F s y) (g y) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hg.toLp g) t := by
  let S := fun s y => slope (fun r => F r y) t s
  have hS (s : ℝ) : MemLp (S s) 2 volume :=
    ((hF s).sub (hF t)).const_smul (s-t)⁻¹
  have hlim := lineLp_tendsto_dominated S g hS hg w hw hb (fun y => (hd y).tendsto_slope)
  apply hasDerivAt_iff_tendsto_slope.mpr
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  change (s-t)⁻¹ • ((hF s).toLp (F s)-(hF t).toLp (F t))=(hS s).toLp (S s)
  rw [←MemLp.toLp_sub,←MemLp.toLp_const_smul]
  rfl

theorem lineLp_hasDerivAt_of_increment_bound (F : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ)
    (hF : ∀ s, MemLp (F s) 2 volume) (hg : MemLp g 2 volume)
    (w : ℝ → ℝ) (hw : Integrable (fun y => w y^2))
    (hb : ∀ᶠ s in 𝓝 t, ∀ y, ‖F s y-F t y‖≤|s-t| *w y)
    (hd : ∀ y, HasDerivAt (fun s => F s y) (g y) t) :
    HasDerivAt (fun s => (hF s).toLp (F s)) (hg.toLp g) t := by
  have hslope : ∀ᶠ s in 𝓝[≠] t, ∀ y, ‖slope (fun r => F r y) t s‖≤w y := by
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hs hst y
    have hne : s-t≠0 := sub_ne_zero.mpr hst
    rw [slope_def_module,norm_smul,Real.norm_eq_abs,abs_inv]
    calc
      |s-t|⁻¹*‖F s y-F t y‖ ≤ |s-t|⁻¹*(|s-t| *w y) :=
        mul_le_mul_of_nonneg_left (hs y) (by positivity)
      _ = w y := by rw [←mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hne),one_mul]
  have hg_bound (y : ℝ) : ‖g y‖≤w y :=
    le_of_tendsto (hd y).tendsto_slope.norm (hslope.mono fun _ hs => hs y)
  apply lineLp_hasDerivAt F g t hF hg (fun y => 2*w y)
  · simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using hw.const_mul 4
  · filter_upwards [hslope] with s hs y
    exact (norm_sub_le _ _).trans (by linarith only [hs y,hg_bound y])
  · exact hd

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StrongOperatorDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strong product rule needed for the sampling conjugation. A
uniform operator bound replaces differentiability in operator norm. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem hasDerivAt_strong_operator_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ℝ → E →L[ℝ] E) (f : ℝ → E) (t : ℝ) (f' d : E) (B : ℝ)
    (hb : ∀ᶠ s in 𝓝 t, ‖C s‖≤B)
    (hf : HasDerivAt f f' t)
    (hcont : ContinuousAt (fun s => C s f') t)
    (hfixed : HasDerivAt (fun s => C s (f t)) d t) :
    HasDerivAt (fun s => C s (f s)) (d+C t f') t := by
  have hzero : Tendsto (fun s => C s (slope f t s-f')) (𝓝[≠] t) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun s => (C s).le_opNorm (slope f t s-f'))
    have hz : Tendsto (fun s => ‖slope f t s-f'‖) (𝓝[≠] t) (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hf.tendsto_slope.sub_const f').norm
    apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (hb.filter_mono nhdsWithin_le_nhds |>.mono fun s hs =>
        mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    simpa only [mul_zero] using hz.const_mul B
  have hsum := (hzero.add (hcont.tendsto.mono_left nhdsWithin_le_nhds)).add hfixed.tendsto_slope
  apply hasDerivAt_iff_tendsto_slope.mpr
  have heq (s : ℝ) : slope (fun r => C r (f r)) t s=
      C s (slope f t s-f')+C s f'+slope (fun r => C r (f t)) t s := by
    simp only [slope_def_module,map_sub,map_smul,smul_sub]
    abel
  simpa only [←heq,zero_add,add_comm (C t f') d] using hsum

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugation generator for a compact smooth direction.
Its Lipschitz bound is uniform in the short time parameter. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingGeneratorSchwartz_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ) :
    lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht y=
      (lineSamplingGenerator u hu B hB hb t ht y : ℂ) := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof-independent inverse family, with quantitative continuity in
space and time. These identities are used in the conjugation derivative. -/
noncomputable section
open Function
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingInverse_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) (y : ℝ) :
    lineSamplingInverse u t (lineSampling u t y)=y :=
  leftInverse_invFun (lineSampling_antilipschitz u hu t ht).injective y

theorem lineSamplingInverse_time_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (s t : ℝ)
    (hs : |s|≤1/2) (y : ℝ) :
    |lineSamplingInverse u s y-lineSamplingInverse u t y|≤2*B*|s-t| := by
  have hh := (lineSampling_antilipschitz u hu s hs).le_mul_dist
    (lineSamplingInverse u s y) (lineSamplingInverse u t y)
  have hleft := lineSampling_inverse_apply u hu B hB hb s y
  have hright := lineSampling_inverse_apply u hu B hB hb t y
  have he : lineSampling u s (lineSamplingInverse u t y)=
      y+(t-s)*u (lineSamplingInverse u t y) := by
    unfold lineSampling at hright ⊢
    linarith
  rw [hleft,he] at hh
  simp only [Real.dist_eq,NNReal.coe_ofNat] at hh
  have habs : |y-(y+(t-s)*u (lineSamplingInverse u t y))|=
      |s-t| *|u (lineSamplingInverse u t y)| := by
    rw [show y-(y+(t-s)*u (lineSamplingInverse u t y))=(s-t)*u (lineSamplingInverse u t y) by ring,abs_mul]
  rw [habs] at hh
  have hb' := mul_le_mul_of_nonneg_left (hb (lineSamplingInverse u t y)) (abs_nonneg (s-t))
  nlinarith

theorem lineSamplingInverse_time_pointwise (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (s t : ℝ)
    (hs : |s|≤1/2) (y : ℝ) :
    |lineSamplingInverse u s y-lineSamplingInverse u t y|≤
      2*|s-t| *|u (lineSamplingInverse u t y)| := by
  have hh := (lineSampling_antilipschitz u hu s hs).le_mul_dist
    (lineSamplingInverse u s y) (lineSamplingInverse u t y)
  have hleft := lineSampling_inverse_apply u hu B hB hb s y
  have hright := lineSampling_inverse_apply u hu B hB hb t y
  have he : lineSampling u s (lineSamplingInverse u t y)=
      y+(t-s)*u (lineSamplingInverse u t y) := by
    unfold lineSampling at hright ⊢
    linarith
  rw [hleft,he] at hh
  simp only [Real.dist_eq,NNReal.coe_ofNat] at hh
  have hid : y-(y+(t-s)*u (lineSamplingInverse u t y))=
      (s-t)*u (lineSamplingInverse u t y) := by ring
  simpa only [hid,abs_mul,mul_assoc] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingInverseDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation in time of the actual inverse sampling map. -/
noncomputable section
open Filter Set
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem lineSampling_deriv_ne_zero (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) (x : ℝ) : 1-t*deriv u x≠0 := by
  have hd : |deriv u x|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀:=x) hu
  have hp : |t*deriv u x|≤1/2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans (by simpa only [mul_one] using ht)
  have hh := (abs_le.mp hp).2
  linarith

theorem lineSamplingInverse_space_hasDerivAt (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ)
    (hd : DifferentiableAt ℝ u (lineSamplingInverse u t y)) :
    HasDerivAt (lineSamplingInverse u t) (1-t*deriv u (lineSamplingInverse u t y))⁻¹ y := by
  have hf : HasDerivAt (lineSampling u t) (1-t*deriv u (lineSamplingInverse u t y))
      (lineSamplingInverse u t y) := (hasDerivAt_id _).sub (hd.hasDerivAt.const_mul t)
  exact hf.of_local_left_inverse
    (lineSamplingInverse_space_lipschitz u hu B hB hb t ht).continuous.continuousAt
    (lineSampling_deriv_ne_zero u hu t ht _) (Eventually.of_forall
      (lineSampling_inverse_apply u hu B hB hb t))

theorem lineSamplingInverse_time_continuousAt (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|<1/2) (y : ℝ) :
    ContinuousAt (fun s => lineSamplingInverse u s y) t := by
  have hlip : LipschitzOnWith ⟨2*B,by positivity⟩ (fun s => lineSamplingInverse u s y)
      (Icc (-(1/2:ℝ)) (1/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r _hr
    change |lineSamplingInverse u s y-lineSamplingInverse u r y|≤(2*B)*|s-r|
    exact lineSamplingInverse_time_lipschitz u hu B hB hb s r (abs_le.mpr hs) y
  have hm := abs_lt.mp ht
  exact (hlip.continuousOn t ⟨hm.1.le,hm.2.le⟩).continuousAt (Icc_mem_nhds hm.1 hm.2)

theorem lineSamplingInverse_time_hasDerivAt (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|<1/2) (y : ℝ)
    (hdu : DifferentiableAt ℝ u (lineSamplingInverse u t y)) :
    HasDerivAt (fun s => lineSamplingInverse u s y)
      (u (lineSamplingInverse u t y)/(1-t*deriv u (lineSamplingInverse u t y))) t := by
  let g := fun s => lineSamplingInverse u s y
  let x := g t
  have hc : ContinuousAt g t := lineSamplingInverse_time_continuousAt u hu B hB hb t ht y
  have hsmall : ∀ᶠ s in 𝓝 t, |s|≤1/2 := by
    have hm := abs_lt.mp ht
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
    exact abs_le.mpr ⟨hs.1.le,hs.2.le⟩
  have heq (s : ℝ) : g s-s*u (g s)=y := lineSampling_inverse_apply u hu B hB hb s y
  by_cases hz : u x=0
  · have hx : x=y := by have hh := heq t; change x-t*u x=y at hh; simpa only [hz,mul_zero,sub_zero] using hh
    have huy : u y=0 := by rwa [hx] at hz
    have hg : g =ᶠ[𝓝 t] fun _ => y := by
      filter_upwards [hsmall] with s hs
      have ha := (lineSampling_antilipschitz u hu s hs).injective
      apply ha
      change g s-s*u (g s)=y-s*u y
      rw [heq s,huy,mul_zero,sub_zero]
    have hd := (hasDerivAt_const t y).congr_of_eventuallyEq hg
    change HasDerivAt g (u x/(1-t*deriv u x)) t
    rw [hz,zero_div]
    exact hd
  · have hun : ∀ᶠ s in 𝓝 t, u (g s)≠0 :=
      (hu.continuous.continuousAt.comp hc).tendsto.eventually (eventually_ne_nhds hz)
    have hden : 1-t*deriv u x≠0 := by
      have hd : |deriv u x|≤1 := by
        simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀:=x) hu
      have hp : |t*deriv u x|<1/2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans_lt (by simpa only [mul_one] using ht)
      have hh := (abs_lt.mp hp).2
      linarith
    have hx : x-y=t*u x := by have hh := heq t; change x-t*u x=y at hh; linarith
    have hf : HasDerivAt (fun z => (z-y)/u z) ((1-t*deriv u x)/u x) x := by
      have hnumerator : HasDerivAt (fun z : ℝ => z-y) (1:ℝ) x := (hasDerivAt_id x).sub_const y
      have hdenominator : HasDerivAt u (deriv u x) x := hdu.hasDerivAt
      have hh := hnumerator.div hdenominator hz
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      simp only [one_mul]
      rw [hx]
      field_simp [hz]
    have hinv : ∀ᶠ s in 𝓝 t, ((g s-y)/u (g s))=s := by
      filter_upwards [hun] with s hs
      apply (div_eq_iff hs).mpr
      have hh := heq s
      linarith
    have hd := hf.of_local_left_inverse hc (div_ne_zero hden hz) hinv
    simpa only [inv_div] using hd

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingSchwartz
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual forward and inverse sampling operators on Schwartz functions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingInverseSchwartz_forward (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2)
    (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht
      (lineSamplingSchwartz u hu hc hcompact t ht f)=f := by
  ext y
  simp only [lineSamplingSchwartz_apply,lineSamplingInverseSchwartz_apply,
    lineSampling_inverse_apply u hu B hB hb t]

theorem lineCompositionL2_schwartz (phi : ℝ → ℝ) (hg : phi.HasTemperateGrowth)
    (ha : AntilipschitzWith 2 phi) (f : SchwartzMap ℝ ℂ) :
    lineCompositionL2 phi hg.1.continuous.measurable ha (f.toLp 2 volume)=
      (SchwartzMap.compCLMOfAntilipschitz ℂ hg ha f).toLp 2 volume := by
  rw [lineCompositionL2_onSchwartz]
  rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineSamplingPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total Schwartz paths for short-time sampling. Outside the interval
needed in the proof the paths are extended by the identity. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hc : ContDiff ℝ ∞ u)
  (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSamplingPath_apply (s : ℝ) (hs : |s|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingPath u hu hc hcompact s f y=f (lineSampling u s y) := by
  simp only [lineSamplingPath,dite_eq_left hs,lineSamplingSchwartz_apply]

theorem lineSamplingInversePath_apply (s : ℝ) (hs : |s|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingInversePath u hu hc hcompact B hB hb s f y=f (lineSamplingInverse u s y) := by
  simp only [lineSamplingInversePath,dite_eq_left hs,lineSamplingInverseSchwartz_apply]

theorem lineSamplingTangent_apply (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingTangent u hu hc hcompact t ht f y=
      (-u y) • deriv f (lineSampling u t y) := by
  simp only [lineSamplingTangent,neg_apply,lineSchwartzProduct_apply,lineDirectionSchwartz_apply,
    lineSamplingSchwartz_apply,schwartzDerivative_one_apply,neg_smul,Complex.real_smul]

theorem lineSamplingInverseTangent_apply (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingInverseTangent u hu hc hcompact B hB hb t ht f y=
      (u (lineSamplingInverse u t y)/(1-t*deriv u (lineSamplingInverse u t y))) •
        deriv f (lineSamplingInverse u t y) := by
  have hdu := (hc.differentiable (by simp)) (lineSamplingInverse u t y)
  have hd := (f.differentiable _).hasDerivAt.scomp y
    (lineSamplingInverse_space_hasDerivAt u hu B hB hb t ht y hdu)
  have hid : deriv (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f) y=
      (1-t*deriv u (lineSamplingInverse u t y))⁻¹ • deriv f (lineSamplingInverse u t y) := hd.deriv
  simp only [lineSamplingInverseTangent,neg_apply,lineSchwartzProduct_apply,
    schwartzDerivative_one_apply,lineSamplingGeneratorSchwartz_apply,lineSamplingGenerator]
  rw [hid,←lineSamplingInverse_eq u hu B hB hb t ht]
  simp only [Complex.ofReal_neg,neg_mul,neg_neg,←Complex.real_smul,smul_smul,div_eq_mul_inv]

theorem lineSamplingPath_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    HasDerivAt (fun s => lineSamplingPath u hu hc hcompact s f y)
      (lineSamplingTangent u hu hc hcompact t ht.le f y) t := by
  have hi : HasDerivAt (fun s : ℝ => lineSampling u s y) (-u y) t := by
    convert (hasDerivAt_const t y).sub ((hasDerivAt_id t).mul_const (u y)) using 1 <;> first | (with_reducible_and_instances rfl) | (simp [lineSampling])
    rfl
  have hd := (f.differentiable _).hasDerivAt.scomp t hi
  rw [←lineSamplingTangent_apply u hu hc hcompact t ht.le f y] at hd
  apply hd.congr_of_eventuallyEq
  have hm := abs_lt.mp ht
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
  exact lineSamplingPath_apply u hu hc hcompact s (abs_le.mpr ⟨hs.1.le,hs.2.le⟩) f y

theorem lineSamplingInversePath_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    HasDerivAt (fun s => lineSamplingInversePath u hu hc hcompact B hB hb s f y)
      (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f y) t := by
  have hi := lineSamplingInverse_time_hasDerivAt u hu B hB hb t ht y
    ((hc.differentiable (by simp)) _)
  have hd := (f.differentiable _).hasDerivAt.scomp t hi
  rw [←lineSamplingInverseTangent_apply u hu hc hcompact B hB hb t ht.le f y] at hd
  apply hd.congr_of_eventuallyEq
  have hm := abs_lt.mp ht
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
  exact lineSamplingInversePath_apply u hu hc hcompact B hB hb s
    (abs_le.mpr ⟨hs.1.le,hs.2.le⟩) f y

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingStrongDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L2 derivatives of the actual sampling paths. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartz_lipschitz (f : SchwartzMap ℝ ℂ) :
    LipschitzWith ⟨lineSchwartzDerivativeBound f,lineSchwartzDerivativeBound_nonneg f⟩ f := by
  apply lipschitzWith_of_nnnorm_deriv_le f.differentiable
  intro x
  change ‖deriv f x‖≤lineSchwartzDerivativeBound f
  exact SchwartzMap.norm_le_seminorm ℝ (schwartzDerivative 1 f) x

theorem line_small_eventually (t : ℝ) (ht : |t|<1/2) : ∀ᶠ s in 𝓝 t, |s|≤1/2 := by
  have hm := abs_lt.mp ht
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
  exact abs_le.mpr ⟨hs.1.le,hs.2.le⟩

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hc : ContDiff ℝ ∞ u)
  (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSamplingPath_L2_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun s => (lineSamplingPath u hu hc hcompact s f).toLp 2 volume)
      ((lineSamplingTangent u hu hc hcompact t ht.le f).toLp 2 volume) t := by
  apply lineLp_hasDerivAt_of_increment_bound
    (fun s => (lineSamplingPath u hu hc hcompact s f : ℝ → ℂ))
    (lineSamplingTangent u hu hc hcompact t ht.le f) t
    (fun s => (lineSamplingPath u hu hc hcompact s f).memLp 2 volume)
    ((lineSamplingTangent u hu hc hcompact t ht.le f).memLp 2 volume)
    (fun y => lineSchwartzDerivativeBound f*|u y|)
  · have hi := ((lineDirectionSchwartz u hc hcompact).memLp 2 volume).integrable_norm_pow
      (by decide : (2:ℕ)≠0)
    simpa only [lineDirectionSchwartz_apply,Complex.norm_real,Real.norm_eq_abs,mul_pow] using
      hi.const_mul (lineSchwartzDerivativeBound f^2)
  · filter_upwards [line_small_eventually t ht] with s hs y
    rw [lineSamplingPath_apply u hu hc hcompact s hs,
      lineSamplingPath_apply u hu hc hcompact t ht.le]
    have hh := (lineSchwartz_lipschitz f).dist_le_mul (lineSampling u s y) (lineSampling u t y)
    simp only [dist_eq_norm,Real.norm_eq_abs] at hh
    calc
      ‖f (lineSampling u s y)-f (lineSampling u t y)‖ ≤
          lineSchwartzDerivativeBound f*|lineSampling u s y-lineSampling u t y| := hh
      _ = |s-t| *(lineSchwartzDerivativeBound f*|u y|) := by
        rw [show lineSampling u s y-lineSampling u t y=(t-s)*u y by simp only [lineSampling]; ring,
          abs_mul,abs_sub_comm t s]
        ring
  · exact lineSamplingPath_hasDerivAt u hu hc hcompact t ht f

theorem lineSamplingInversePath_L2_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun s => (lineSamplingInversePath u hu hc hcompact B hB hb s f).toLp 2 volume)
      ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).toLp 2 volume) t := by
  apply lineLp_hasDerivAt_of_increment_bound
    (fun s => (lineSamplingInversePath u hu hc hcompact B hB hb s f : ℝ → ℂ))
    (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f) t
    (fun s => (lineSamplingInversePath u hu hc hcompact B hB hb s f).memLp 2 volume)
    ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).memLp 2 volume)
    (fun y => 2*lineSchwartzDerivativeBound f*|u (lineSamplingInverse u t y)|)
  · have hi := ((lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht.le
      (lineDirectionSchwartz u hc hcompact)).memLp 2 volume).integrable_norm_pow
      (by decide : (2:ℕ)≠0)
    convert hi.const_mul ((2*lineSchwartzDerivativeBound f)^2) using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp only [lineSamplingInverseSchwartz_apply,lineDirectionSchwartz_apply,
      Complex.norm_real,Real.norm_eq_abs]
    ring
  · filter_upwards [line_small_eventually t ht] with s hs y
    rw [lineSamplingInversePath_apply u hu hc hcompact B hB hb s hs,
      lineSamplingInversePath_apply u hu hc hcompact B hB hb t ht.le]
    have hh := (lineSchwartz_lipschitz f).dist_le_mul
      (lineSamplingInverse u s y) (lineSamplingInverse u t y)
    simp only [dist_eq_norm,Real.norm_eq_abs] at hh
    calc
      ‖f (lineSamplingInverse u s y)-f (lineSamplingInverse u t y)‖ ≤
          lineSchwartzDerivativeBound f*|lineSamplingInverse u s y-lineSamplingInverse u t y| := hh
      _ ≤ lineSchwartzDerivativeBound f*(2*|s-t| *|u (lineSamplingInverse u t y)|) :=
        mul_le_mul_of_nonneg_left (lineSamplingInverse_time_pointwise u hu B hB hb s t hs y)
          (lineSchwartzDerivativeBound_nonneg f)
      _ = |s-t| *(2*lineSchwartzDerivativeBound f*|u (lineSamplingInverse u t y)|) := by ring
  · exact lineSamplingInversePath_hasDerivAt u hu hc hcompact B hB hb t ht f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineSamplingL2Path
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded L2 sampling paths and their agreement with the Schwartz paths. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSamplingL2Path_onSchwartz (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSamplingL2Path u hu s (f.toLp 2 volume)=
      (lineSamplingPath u hu hc hcompact s f).toLp 2 volume := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingL2Path,lineSamplingPath,dite_eq_left hs]
    exact lineCompositionL2_schwartz _ (lineSampling_temperate u hc hcompact s) _ f
  · simp only [lineSamplingL2Path,lineSamplingPath,dite_eq_right hs,ContinuousLinearMap.id_apply]

theorem lineSamplingInverseL2Path_onSchwartz (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume)=
      (lineSamplingInversePath u hu hc hcompact B hB hb s f).toLp 2 volume := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingInverseL2Path,lineSamplingInversePath,dite_eq_left hs]
    exact lineCompositionL2_schwartz _ (lineSamplingInverse_temperate u hu hc hcompact B hB hb s hs) _ f
  · simp only [lineSamplingInverseL2Path,lineSamplingInversePath,dite_eq_right hs,ContinuousLinearMap.id_apply]

theorem lineSamplingL2Path_bound (s : ℝ) : ‖lineSamplingL2Path u hu s‖≤2 := by
  by_cases hs : |s|≤1/2
  · simp only [lineSamplingL2Path,dite_eq_left hs]
    exact lineCompositionL2_bound _ _ _
  · simp only [lineSamplingL2Path,dite_eq_right hs]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))‖≤1).trans (by norm_num)

theorem lineSamplingTangent_eq (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    lineSamplingTangent u hu hc hcompact t ht f=
      lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzProduct (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
          (schwartzDerivative 1 f)) := by
  ext y
  have he : (lineSamplingHomeomorph u hu B hB hb t ht).symm (lineSampling u t y)=y :=
    (lineSamplingHomeomorph u hu B hB hb t ht).symm_apply_apply y
  simp only [lineSamplingTangent_apply,lineSamplingSchwartz_apply,lineSchwartzProduct_apply,
    schwartzDerivative_one_apply,lineSamplingGeneratorSchwartz_apply,lineSamplingGenerator,
    he,Complex.ofReal_neg,neg_smul,Complex.real_smul,neg_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConjugationDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual strong L2 conjugation derivative. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSampling_conjugation_tangent (m : SchwartzMap ℝ ℂ)
    (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    lineSamplingTangent u hu hc hcompact t ht
        (lineSchwartzProjection m 1 (by norm_num)
          (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))+
      lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzProjection m 1 (by norm_num)
          (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht f))=
      lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
          (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))) := by
  rw [lineSamplingTangent_eq u hu hc hcompact B hB hb,lineSchwartzProjection_derivative]
  let p := lineSchwartzProduct (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
    (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))
  have hn : lineSchwartzProjection m 1 (by norm_num) (-p)=
      -lineSchwartzProjection m 1 (by norm_num) p :=
    map_neg (lineSchwartzProjectionLM m 1 (by norm_num)) p
  change _+lineSamplingSchwartz u hu hc hcompact t ht
    (lineSchwartzProjection m 1 (by norm_num) (-p))=_
  rw [hn,←map_add]
  rfl

theorem lineConjugation_L2_hasDerivAt (m : SchwartzMap ℝ ℂ)
    (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun s => lineSamplingL2Path u hu s
      (lineL2Projection m 1 (by norm_num)
        (lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume))))
      ((lineSamplingSchwartz u hu hc hcompact t ht.le
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht.le)
          (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht.le f)))).toLp 2 volume) t := by
  let I := lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht.le f
  let q0 := lineSchwartzProjection m 1 (by norm_num) I
  let q' := lineSchwartzProjection m 1 (by norm_num)
    (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f)
  let Q := fun s => lineL2Projection m 1 (by norm_num)
    (lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume))
  have hI : HasDerivAt (fun s => lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume))
      ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).toLp 2 volume) t := by
    simpa only [lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb] using
      lineSamplingInversePath_L2_hasDerivAt u hu hc hcompact B hB hb t ht f
  have hQ : HasDerivAt Q (q'.toLp 2 volume) t := by
    have hh := ((lineL2Projection m 1 (by norm_num)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hI
    change HasDerivAt Q (lineL2Projection m 1 (by norm_num)
      ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).toLp 2 volume)) t at hh
    rw [lineL2Projection_onSchwartz] at hh
    exact hh
  have hQt : Q t=q0.toLp 2 volume := by
    simp only [Q,lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb,
      lineSamplingInversePath,dite_eq_left ht.le,lineL2Projection_onSchwartz,q0,I]
  have hfixed : HasDerivAt (fun s => lineSamplingL2Path u hu s (Q t))
      ((lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume) t := by
    rw [hQt]
    simpa only [lineSamplingL2Path_onSchwartz u hu hc hcompact] using
      lineSamplingPath_L2_hasDerivAt u hu hc hcompact t ht q0
  have hcont : ContinuousAt (fun s => lineSamplingL2Path u hu s (q'.toLp 2 volume)) t := by
    simpa only [lineSamplingL2Path_onSchwartz u hu hc hcompact] using
      (lineSamplingPath_L2_hasDerivAt u hu hc hcompact t ht q').continuousAt
  have hmain := hasDerivAt_strong_operator_apply
    (fun s => (lineSamplingL2Path u hu s).restrictScalars ℝ) Q t
    (q'.toLp 2 volume) ((lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume) 2
    (Eventually.of_forall fun s => by
      rw [ContinuousLinearMap.norm_restrictScalars]
      exact lineSamplingL2Path_bound u hu s) hQ hcont hfixed
  change HasDerivAt (fun s => lineSamplingL2Path u hu s (Q s))
    ((lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume+
      lineSamplingL2Path u hu t (q'.toLp 2 volume)) t at hmain
  have he : (lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume+
      lineSamplingL2Path u hu t (q'.toLp 2 volume)=
      (lineSamplingSchwartz u hu hc hcompact t ht.le
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht.le)
          (schwartzDerivative 1 I))).toLp 2 volume := by
    rw [lineSamplingL2Path_onSchwartz u hu hc hcompact]
    simp only [lineSamplingPath,dite_eq_left ht.le]
    calc
      _ = (lineSamplingTangent u hu hc hcompact t ht.le q0+
          lineSamplingSchwartz u hu hc hcompact t ht.le q').toLp 2 volume :=
        (map_add (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ _).symm
      _ = _ := congrArg (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume)
        (lineSampling_conjugation_tangent u hu hc hcompact B hB hb m t ht.le f)
  rw [he] at hmain
  exact hmain

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConjugationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the strong conjugation derivative with a uniform bound. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

include hc hcompact in
theorem lineConjugation_zero (m : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ ℂ) :
    lineConjugationL2 u hu B hB hb m 0 (f.toLp 2 volume)=
      lineL2Projection m 1 (by norm_num) (f.toLp 2 volume) := by
  have hforward (g : SchwartzMap ℝ ℂ) : lineSamplingPath u hu hc hcompact 0 g=g := by
    ext y
    rw [lineSamplingPath_apply u hu hc hcompact 0 (by norm_num)]
    simp only [lineSampling,zero_mul,sub_zero]
  have hinverse : lineSamplingInversePath u hu hc hcompact B hB hb 0 f=f := by
    ext y
    rw [lineSamplingInversePath_apply u hu hc hcompact B hB hb 0 (by norm_num)]
    have hh := lineSamplingInverse_apply u hu 0 (by norm_num) y
    simpa only [lineSampling,zero_mul,sub_zero] using congrArg f hh
  simp only [lineConjugationL2,ContinuousLinearMap.comp_apply,
    lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb,hinverse,
    lineL2Projection_onSchwartz,lineSamplingL2Path_onSchwartz u hu hc hcompact,hforward]

include hc hcompact in
theorem lineConjugation_difference_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap ℝ ℂ) :
    ‖lineConjugationL2 u hu B hB hb m t (f.toLp 2 volume)-
      lineL2Projection m 1 (by norm_num) (f.toLp 2 volume)‖≤
        8*lineCommutatorNormConstant*A*|t| *‖f.toLp 2 volume‖ := by
  let F := fun s => lineConjugationL2 u hu B hB hb m s (f.toLp 2 volume)
  have hsmall (s : ℝ) (hs : s∈Icc (-(1/4:ℝ)) (1/4)) : |s|<1/2 := by
    have hh := abs_le.mpr hs
    linarith
  have hd (s : ℝ) (hs : s∈Icc (-(1/4:ℝ)) (1/4)) : DifferentiableAt ℝ F s :=
    (lineConjugation_L2_hasDerivAt u hu hc hcompact B hB hb m s (hsmall s hs) f).differentiableAt
  have hbound (s : ℝ) (hs : s∈Icc (-(1/4:ℝ)) (1/4)) :
      ‖deriv F s‖≤8*lineCommutatorNormConstant*A*‖f.toLp 2 volume‖ := by
    have he := (lineConjugation_L2_hasDerivAt u hu hc hcompact B hB hb m s (hsmall s hs) f).deriv
    change deriv F s=_ at he
    rw [he]
    exact lineConjugation_derivative_bound u hu hc hcompact B hB hb m A hA hm s (hsmall s hs).le f
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hbound (convex_Icc _ _)
    (show (0:ℝ)∈Icc (-(1/4:ℝ)) (1/4) by norm_num) (abs_le.mp ht)
  change ‖F t-F 0‖≤_ at hh
  dsimp only [F] at hh
  rw [lineConjugation_zero u hu hc hcompact B hB hb] at hh
  simpa only [sub_zero,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CompactCompositionCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The composition commutator for actual compact smooth directions. -/
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

include hc hcompact in
theorem lineSamplingInverseL2_forward (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    lineSamplingInverseL2Path u hu B hB hb t
      (lineSamplingL2Path u hu t (f.toLp 2 volume))=f.toLp 2 volume := by
  rw [lineSamplingL2Path_onSchwartz u hu hc hcompact]
  simp only [lineSamplingPath,dite_eq_left ht]
  rw [lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb]
  simp only [lineSamplingInversePath,dite_eq_left ht,lineSamplingInverseSchwartz_forward]

include hc hcompact B hB hb in
theorem compactCompositionCommutator_schwartz (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap ℝ ℂ) :
    ‖lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t (f.toLp 2 volume))-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume))‖≤
        16*lineCommutatorNormConstant*A*|t| *‖f.toLp 2 volume‖ := by
  have ht' : |t|≤1/2 := ht.trans (by norm_num)
  let F := lineSamplingSchwartz u hu hc hcompact t ht' f
  have hF : F.toLp 2 volume=lineSamplingL2Path u hu t (f.toLp 2 volume) := by
    rw [lineSamplingL2Path_onSchwartz u hu hc hcompact]
    simp only [lineSamplingPath,dite_eq_left ht',F]
  have hi := lineSamplingInverseL2_forward u hu hc hcompact B hB hb t ht' f
  have hFnorm : ‖F.toLp 2 volume‖≤2*‖f.toLp 2 volume‖ := by
    rw [hF]
    exact ((lineSamplingL2Path u hu t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (lineSamplingL2Path_bound u hu t) (norm_nonneg _))
  have hh := lineConjugation_difference_bound u hu hc hcompact B hB hb m A hA hm t ht F
  have he : lineConjugationL2 u hu B hB hb m t (F.toLp 2 volume)=
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume)) := by
    simp only [lineConjugationL2,ContinuousLinearMap.comp_apply,hF,hi]
  rw [he,hF,norm_sub_rev] at hh
  rw [hF] at hFnorm
  apply hh.trans
  calc
    _ ≤ 8*lineCommutatorNormConstant*A*|t| *(2*‖f.toLp 2 volume‖) :=
      mul_le_mul_of_nonneg_left hFnorm (by have := lineCommutatorNormConstant_nonneg; positivity)
    _ = _ := by ring

include hc hcompact B hB hb in
theorem compactCompositionCommutator_L2 (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (t : ℝ) (ht : |t|≤1/4) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t f)-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) f)‖≤
        16*lineCommutatorNormConstant*A*|t| *‖f‖ := by
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) ?_
  exact compactCompositionCommutator_schwartz u hu hc hcompact B hB hb m A hA hm t ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteSignedEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sign randomization in a Hilbert space, expressed without a
probability space. A bound for every signed sum bounds the square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem finiteSignedSum_energy {n : ℕ} (f : Fin n → E) (x : E) (B : ℝ)
    (h : ∀ s : Fin n → Bool, ‖x+finiteSignedSum f s‖^2≤B) :
    ‖x‖^2+∑ i, ‖f i‖^2≤B := by
  induction n generalizing x B with
  | zero => simpa [finiteSignedSum] using h Fin.elim0
  | succ n ih =>
    let g : Fin n → E := fun i => f i.succ
    have htail (s : Fin n → Bool) :
        ‖x+finiteSignedSum g s‖^2≤B-‖f 0‖^2 := by
      have hp := h (Fin.cons true s)
      have hn := h (Fin.cons false s)
      simp [finiteSignedSum,Fin.sum_univ_succ] at hp hn
      have hp' : ‖(x+finiteSignedSum g s)+f 0‖^2≤B := by
        convert hp using 2
        all_goals try with_reducible_and_instances rfl
        dsimp [finiteSignedSum,g]
        abel_nf
      have hn' : ‖(x+finiteSignedSum g s)-f 0‖^2≤B := by
        convert hn using 2
        all_goals try with_reducible_and_instances rfl
        dsimp [finiteSignedSum,g]
        abel_nf
      have hpar := parallelogram_law_with_norm ℂ (x+finiteSignedSum g s) (f 0)
      nlinarith
    have hi := ih g x (B-‖f 0‖^2) htail
    rw [Fin.sum_univ_succ]
    dsimp [g] at hi
    linarith

theorem finiteSignedSum_square_le {n : ℕ} (f : Fin n → E) (B : ℝ)
    (h : ∀ s : Fin n → Bool, ‖finiteSignedSum f s‖^2≤B) :
    (∑ i, ‖f i‖^2)≤B := by
  simpa only [norm_zero,zero_pow (by decide : 2≠0),zero_add] using
    finiteSignedSum_energy f (0:E) B (fun s => by simpa only [zero_add] using h s)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteSignedFunctions
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite randomization for actual measurable functions. Membership in
L2 is recovered from signed sums and is not assumed in advance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}

omit [MeasurableSpace X] in
theorem signedFunction_isolate (f : Fin n → X → ℂ) (i : Fin n) :
    signedFunction f (fun _ => true)-signedFunction f (fun j => decide (j≠i))=
      (2:ℂ) • f i := by
  classical
  funext x
  simp only [signedFunction,finiteSignedSum,ite_true, if_true,Pi.sub_apply,←Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro j _ hji
    simp [hji]
  · simp

theorem memLp_of_signedFunction (f : Fin n → X → ℂ)
    (h : ∀ s, MemLp (signedFunction f s) 2 μ) (i : Fin n) : MemLp (f i) 2 μ := by
  have hh := (h (fun _ => true)).sub (h (fun j => decide (j≠i)))
  rw [signedFunction_isolate] at hh
  have hi := hh.const_smul (1/2:ℂ)
  simpa only [smul_smul,show (1/2:ℂ)*2=1 by norm_num,one_smul] using hi

theorem signedLpTerm_coe (f : Fin n → X → ℂ) (h : ∀ i, MemLp (f i) 2 μ)
    (s : Fin n → Bool) (i : Fin n) :
    ((if s i then (h i).toLp (f i) else -(h i).toLp (f i) : Lp ℂ 2 μ) : X → ℂ)=ᵐ[μ]
      (fun x => if s i then f i x else -f i x) := by
  split_ifs
  · exact (h i).coeFn_toLp
  · filter_upwards [Lp.coeFn_neg ((h i).toLp (f i)),(h i).coeFn_toLp] with x hx hfx
    rw [hx]
    change -((h i).toLp (f i) x) = _
    rw [hfx]

theorem signedFunction_toLp (f : Fin n → X → ℂ) (h : ∀ i, MemLp (f i) 2 μ)
    (s : Fin n → Bool) (hs : MemLp (signedFunction f s) 2 μ) :
    finiteSignedSum (fun i => (h i).toLp (f i)) s=hs.toLp (signedFunction f s) := by
  apply Lp.ext
  have he := ae_all_iff.mpr (signedLpTerm_coe μ f h s)
  have hadd := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => if s i then (h i).toLp (f i) else -(h i).toLp (f i))
  filter_upwards [he,hadd,hs.coeFn_toLp] with x hx ha hb
  change (finiteSignedSum (fun i => (h i).toLp (f i)) s) x = _
  change (∑ i, if s i then (h i).toLp (f i) else -(h i).toLp (f i)) x = _
  rw [ha,hb]
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem signedFunction_square_bound (f : Fin n → X → ℂ) (A : ℝ) (hA : 0≤A)
    (h : ∀ s, MemLp (signedFunction f s) 2 μ ∧
      eLpNorm (signedFunction f s) 2 μ≤ENNReal.ofReal A) :
    ∃ hf : ∀ i, MemLp (f i) 2 μ,
      (∑ i, ‖(hf i).toLp (f i)‖^2)≤A^2 := by
  let hf := memLp_of_signedFunction μ f (fun s => (h s).1)
  refine ⟨hf,finiteSignedSum_square_le _ _ ?_⟩
  intro s
  rw [signedFunction_toLp μ f hf s (h s).1,Lp.norm_toLp]
  have he : (eLpNorm (signedFunction f s) 2 μ).toReal≤A := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h s).2
    simpa only [ENNReal.toReal_ofReal hA] using hh
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg he 2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integrable common envelope for bounded displacements of a line
Schwartz function, used to pass to nonsmooth directions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartz_decay (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    (1+|y|)^2*‖f y‖≤lineSchwartzDecayConstant f := by
  have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ) (m:=(2,0))
    (k:=2) (n:=0) (by rfl) (by rfl) f y
  simpa only [lineSchwartzDecayConstant,norm_iteratedFDeriv_zero,Real.norm_eq_abs,show (2:ℝ)^2=4 by norm_num] using hh

theorem lineSchwartz_shift_decay (f : SchwartzMap ℝ ℂ) (y d : ℝ) (hd : |d|≤1) :
    ‖f (y-d)‖≤4*lineSchwartzDecayConstant f/(1+|y|)^2 := by
  have hgeom : 1+|y|≤2*(1+|y-d|) := by
    have hh := abs_add_le (y-d) d
    rw [sub_add_cancel] at hh
    linarith [abs_nonneg (y-d)]
  have hs : (1+|y|)^2≤4*(1+|y-d|)^2 := by
    simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0≤1+|y|) hgeom 2
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    ‖f (y-d)‖*(1+|y|)^2 ≤ ‖f (y-d)‖*(4*(1+|y-d|)^2) :=
      mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = 4*((1+|y-d|)^2*‖f (y-d)‖) := by ring
    _ ≤ 4*lineSchwartzDecayConstant f := mul_le_mul_of_nonneg_left (lineSchwartz_decay f (y-d)) (by norm_num)

theorem lineSchwartz_shift_envelope_integrable (f : SchwartzMap ℝ ℂ) :
    Integrable (fun y : ℝ => (8*lineSchwartzDecayConstant f/(1+|y|)^2)^2) := by
  have hi : Integrable (fun y : ℝ => ((1+|y|)^4)⁻¹) := by
    have hh := integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=4) (by norm_num)
    simpa only [Real.norm_eq_abs,show (- (4:ℝ))=(-(4:ℕ):ℝ) by norm_num,
      Real.rpow_neg_natCast,zpow_neg,zpow_natCast] using hh
  convert hi.const_mul ((8*lineSchwartzDecayConstant f)^2) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineCompositionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong convergence of sampling operators under bounded pointwise
convergence of Lipschitz directions. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingL2Path_schwartz_tendsto
    (v : ℕ → ℝ → ℝ) (u : ℝ → ℝ) (hv : ∀ n, LipschitzWith 1 (v n)) (hu : LipschitzWith 1 u)
    (hvb : ∀ n y, |v n y|≤1) (hub : ∀ y, |u y|≤1)
    (hlim : ∀ y, Tendsto (fun n => v n y) atTop (𝓝 (u y)))
    (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => lineSamplingL2Path (v n) (hv n) t (f.toLp 2 volume)) atTop
      (𝓝 (lineSamplingL2Path u hu t (f.toLp 2 volume))) := by
  let F := fun n y => f (lineSampling (v n) t y)
  let g := fun y => f (lineSampling u t y)
  have hF (n : ℕ) : MemLp (F n) 2 volume :=
    (line_memLp_comp _ (lineSampling_lipschitz (v n) (hv n) t ht).continuous.measurable
      (lineSampling_antilipschitz (v n) (hv n) t ht) f f.continuous.measurable (f.memLp 2 volume)).1
  have hg : MemLp g 2 volume :=
    (line_memLp_comp _ (lineSampling_lipschitz u hu t ht).continuous.measurable
      (lineSampling_antilipschitz u hu t ht) f f.continuous.measurable (f.memLp 2 volume)).1
  have hb : ∀ n y, ‖F n y-g y‖≤8*lineSchwartzDecayConstant f/(1+|y|)^2 := by
    intro n y
    have hvsmall : |t*v n y|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hvb n y) (abs_nonneg t)).trans (by linarith)
    have husmall : |t*u y|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hub y) (abs_nonneg t)).trans (by linarith)
    calc
      _ ≤ ‖f (y-t*v n y)‖+‖f (y-t*u y)‖ := norm_sub_le _ _
      _ ≤ 4*lineSchwartzDecayConstant f/(1+|y|)^2+
          4*lineSchwartzDecayConstant f/(1+|y|)^2 :=
        add_le_add (lineSchwartz_shift_decay f y (t*v n y) hvsmall)
          (lineSchwartz_shift_decay f y (t*u y) husmall)
      _ = _ := by ring
  have hp (y : ℝ) : Tendsto (fun n => F n y) atTop (𝓝 (g y)) :=
    f.continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul (hlim y)))
  have hh := lineLp_tendsto_dominated F g hF hg _ (lineSchwartz_shift_envelope_integrable f)
    (Eventually.of_forall hb) hp
  simpa only [lineSamplingL2Path,dite_eq_left ht,lineCompositionL2_onSchwartz,lineCompositionToL2,LinearMap.coe_mk,AddHom.coe_mk,F,g,Function.comp_def] using hh

theorem lineL2_tendsto_of_schwartz
    (C : ℕ → Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (D : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hC : ∀ n, ‖C n‖≤2) (hD : ‖D‖≤2)
    (hlim : ∀ g : SchwartzMap ℝ ℂ, Tendsto (fun n => C n (g.toLp 2 volume)) atTop (𝓝 (D (g.toLp 2 volume))))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => C n f) atTop (𝓝 (D f)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  obtain ⟨g,hg⟩ := hd.exists_dist_lt f (show 0<eps/8 by positivity)
  have hg' : ‖f-g.toLp 2 volume‖<eps/8 := by simpa only [dist_eq_norm,norm_sub_rev] using hg
  filter_upwards [(Metric.tendsto_nhds.mp (hlim g)) (eps/2) (by positivity)] with n hn
  rw [dist_eq_norm] at hn ⊢
  have h1 : ‖C n f-C n (g.toLp 2 volume)‖≤2*‖f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    exact ((C n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  have h2 : ‖D (g.toLp 2 volume)-D f‖≤2*‖f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    have hh := (D.le_opNorm (g.toLp 2 volume-f)).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    simpa only [norm_sub_rev] using hh
  have htri := norm_add_le (C n f-C n (g.toLp 2 volume))
    (C n (g.toLp 2 volume)-D (g.toLp 2 volume)+ (D (g.toLp 2 volume)-D f))
  have htri' := norm_add_le (C n (g.toLp 2 volume)-D (g.toLp 2 volume)) (D (g.toLp 2 volume)-D f)
  rw [sub_add_sub_cancel,sub_add_sub_cancel] at htri
  rw [sub_add_sub_cancel] at htri'
  linarith

theorem lineSamplingL2Path_tendsto
    (v : ℕ → ℝ → ℝ) (u : ℝ → ℝ) (hv : ∀ n, LipschitzWith 1 (v n)) (hu : LipschitzWith 1 u)
    (hvb : ∀ n y, |v n y|≤1) (hub : ∀ y, |u y|≤1)
    (hlim : ∀ y, Tendsto (fun n => v n y) atTop (𝓝 (u y)))
    (t : ℝ) (ht : |t|≤1/2) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => lineSamplingL2Path (v n) (hv n) t f) atTop
      (𝓝 (lineSamplingL2Path u hu t f)) :=
  lineL2_tendsto_of_schwartz _ _ (fun n => lineSamplingL2Path_bound (v n) (hv n) t)
    (lineSamplingL2Path_bound u hu t)
    (lineSamplingL2Path_schwartz_tendsto v u hv hu hvb hub hlim t ht) f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_CompactDirectionCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoffs of bounded Lipschitz directions, normalized to
preserve the exact Lipschitz constant one. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem compactDirectionCutoff_bound (u : ℝ → ℝ) (hb : ∀ x, |u x|≤1)
    (R : ℝ) (hR : 0<R) (y : ℝ) : |compactDirectionCutoff u R y|≤1 := by
  have ha : 0≤R/(R+1) := by positivity
  have ha' : R/(R+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  rw [compactDirectionCutoff,abs_mul,abs_mul,abs_of_nonneg ha,
    abs_of_nonneg (directionTent_nonneg R y)]
  calc
    _ ≤ 1*1*1 := mul_le_mul (mul_le_mul ha' (hb y) (abs_nonneg _) (by norm_num))
      (directionTent_le_one R hR y) (directionTent_nonneg R y) (by norm_num)
    _ = 1 := by norm_num

theorem compactDirectionCutoff_tendsto (u : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n : ℕ => compactDirectionCutoff u ((n:ℝ)+1) x) atTop (𝓝 (u x)) := by
  have ha : Tendsto (fun n : ℕ => ((n:ℝ)+1)/((n:ℝ)+1+1)) atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_div_add_atTop (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => |x|/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,mul_one,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul |x|
  have ht : Tendsto (fun n : ℕ => directionTent ((n:ℝ)+1) x) atTop (𝓝 (1:ℝ)) := by
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h0 : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    simpa only [directionTent,sub_zero,max_eq_left (by norm_num : (0:ℝ)≤1)] using
      (h1.sub hb).max h0
  simpa only [compactDirectionCutoff,one_mul,mul_one] using (ha.mul_const (u x)).mul ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineMollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive compact mollification on the line preserves the size and
Lipschitz bounds needed for the sampling maps. -/
noncomputable section
open MeasureTheory Function
open scoped Convolution ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lineMollification_apply (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (x : ℝ) :
    lineMollification phi f hf hcompact x=∫ z, phi.normed volume z*f (x-z) := rfl

theorem lineMollification_compact (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) :
    HasCompactSupport (lineMollification phi f hf hcompact : ℝ → ℝ) :=
  (phi.hasCompactSupport_normed (μ:=volume)).convolution
    (L:=ContinuousLinearMap.lsmul ℝ ℝ) hcompact

theorem lineMollification_bound (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (hb : ∀ x, |f x|≤1) (x : ℝ) :
    |lineMollification phi f hf hcompact x|≤1 := by
  rw [lineMollification_apply,←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le (phi.integrable_normed (μ:=volume))
    (Filter.Eventually.of_forall fun z => show ‖phi.normed volume z*f (x-z)‖≤phi.normed volume z from by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (phi.nonneg_normed z),Real.norm_eq_abs]
      exact mul_le_of_le_one_right (phi.nonneg_normed z) (hb _))
  simpa only [phi.integral_normed] using hh

theorem lineMollification_lipschitz (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (hu : LipschitzWith 1 f) :
    LipschitzWith 1 (lineMollification phi f hf hcompact) := by
  have hi (x : ℝ) : Integrable (fun z => phi.normed volume z*f (x-z)) :=
    (phi.continuous_normed.mul (hu.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((phi.hasCompactSupport_normed (μ:=volume)).mul_right)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |lineMollification phi f hf hcompact x-lineMollification phi f hf hcompact y|≤1*|x-y|
  rw [lineMollification_apply,lineMollification_apply,←integral_sub (hi x) (hi y),←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le ((phi.integrable_normed (μ:=volume)).mul_const |x-y|)
    (Filter.Eventually.of_forall fun z => show
      ‖phi.normed volume z*f (x-z)-phi.normed volume z*f (y-z)‖≤phi.normed volume z*|x-y| from by
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (phi.nonneg_normed z),Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (phi.nonneg_normed z)
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right] using hu.dist_le_mul (x-z) (y-z))
  simpa only [integral_mul_const,phi.integral_normed] using hh

theorem lineMollification_approximation (phi : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ)
    (hf : Integrable f) (hcompact : HasCompactSupport f) (hu : LipschitzWith 1 f) (x : ℝ) :
    |lineMollification phi f hf hcompact x-f x|≤phi.rOut := by
  apply phi.dist_normed_convolution_le hu.continuous.aestronglyMeasurable
  intro y hy
  have hh : dist (f y) (f x)≤dist y x := by
    simpa only [NNReal.coe_one,one_mul] using hu.dist_le_mul y x
  exact hh.trans hy.le

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SmoothDirectionApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact smooth approximants of a bounded Lipschitz direction. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

theorem lineDirectionMollifier_radius_tendsto :
    Tendsto (fun n => (lineDirectionMollifier n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hb : ∀ x, |u x|≤1)

theorem smoothDirectionApprox_lipschitz (n : ℕ) :
    LipschitzWith 1 (smoothDirectionApprox u hu hb n : ℝ → ℝ) :=
  lineMollification_lipschitz _ _ _ _ (compactDirectionCutoff_lipschitz u hu hb _ (by positivity))

theorem smoothDirectionApprox_bound (n : ℕ) (x : ℝ) :
    |smoothDirectionApprox u hu hb n x|≤1 :=
  lineMollification_bound _ _ _ _ (compactDirectionCutoff_bound u hb _ (by positivity)) x

theorem smoothDirectionApprox_compact (n : ℕ) :
    HasCompactSupport (smoothDirectionApprox u hu hb n : ℝ → ℝ) :=
  lineMollification_compact _ _ _ _

theorem smoothDirectionApprox_tendsto (x : ℝ) :
    Tendsto (fun n => smoothDirectionApprox u hu hb n x) atTop (𝓝 (u x)) := by
  have hnorm : Tendsto (fun n => |smoothDirectionApprox u hu hb n x-
      compactDirectionCutoff u ((n:ℝ)+1) x|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _)
      (fun n => lineMollification_approximation _ _ _ _
        (compactDirectionCutoff_lipschitz u hu hb _ (by positivity)) x)
      lineDirectionMollifier_radius_tendsto
  have hdiff : Tendsto (fun n => smoothDirectionApprox u hu hb n x-
      compactDirectionCutoff u ((n:ℝ)+1) x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hnorm)
  simpa only [sub_add_cancel,zero_add] using hdiff.add (compactDirectionCutoff_tendsto u x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LipschitzCompositionCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The composition commutator for the actual bounded Lipschitz
directions, obtained from compact smooth approximation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace LipschitzHilbert.PacketRepresentation

theorem lipschitzCompositionCommutator_L2 (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hub : ∀ y, |u y|≤1)
    (t : ℝ) (ht : |t|≤1/4) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t f)-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) f)‖≤
        16*lineCommutatorNormConstant*A*|t| *‖f‖ := by
  let v := fun n => (smoothDirectionApprox u hu hub n : ℝ → ℝ)
  have hv (n : ℕ) : LipschitzWith 1 (v n) := smoothDirectionApprox_lipschitz u hu hub n
  have hvb (n : ℕ) (y : ℝ) : |v n y|≤1 := smoothDirectionApprox_bound u hu hub n y
  have hvl (y : ℝ) : Tendsto (fun n => v n y) atTop (𝓝 (u y)) :=
    smoothDirectionApprox_tendsto u hu hub y
  have ht' : |t|≤1/2 := ht.trans (by norm_num)
  have hc1 := lineSamplingL2Path_tendsto v u hv hu hvb hub hvl t ht' f
  have hc2 := lineSamplingL2Path_tendsto v u hv hu hvb hub hvl t ht'
    (lineL2Projection m 1 (by norm_num) f)
  have hlim := (((lineL2Projection m 1 (by norm_num)).continuous.continuousAt.tendsto.comp hc1).sub hc2).norm
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n => compactCompositionCommutator_L2 (v n) (hv n)
    ((smoothDirectionApprox u hu hub n).smooth ⊤) (smoothDirectionApprox_compact u hu hub n)
    1 (by norm_num) (hvb n) m A hA hm t ht f

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpVerticalCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual vertical-profile commutator has a bound independent of the
inner cutoff. Its principal-time integral has the same bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpVerticalCommutator_eq (q : SchwartzMap ℝ ℂ) (W center epsilon R : ℝ)
    (hW : 0<W) (he : 0<epsilon) (hR : 0<R) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    sharpVerticalCommutator q W center epsilon R u f=
      fun z => ∫ t, if |t|≤1/4 then sharpTimeKernel epsilon R t*
        verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0 := by
  funext z
  exact shortSlopeCommutator_eq (verticalProfileKernel q W center) (sharpTimeKernel epsilon R)
    (by
      unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
      exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
        (continuous_const.mul ((FourierTransform.fourierInv q : SchwartzMap ℝ ℂ).continuous.comp
          (by fun_prop)))).measurable)
    (modulatedTimeKernel_integrable _ W center hW) (sharpTimeKernel_integrable epsilon R he hR)
    u hum f z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSamplingKernelCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved L2 operator commutator is the actual convolution/sampling
difference, with its squared integral bound. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineSamplingKernelCommutator_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hub : ∀ y, |u y|≤1)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap ℝ ℂ) :
    MemLp (lineSamplingKernelCommutator m u t f) 2 volume ∧
      (∫ y, ‖lineSamplingKernelCommutator m u t f y‖^2)≤
        (16*lineCommutatorNormConstant*A*|t|)^2*(∫ y, ‖f y‖^2) := by
  let K := lineProjectionKernel m 1 (by norm_num)
  let phi := lineSampling u t
  let F := fun y => f (phi y)
  let q := lineSchwartzProjection m 1 (by norm_num) f
  have ht' : |t|≤1/2 := ht.trans (by norm_num)
  have hphi : Measurable phi := (lineSampling_lipschitz u hu t ht').continuous.measurable
  have ha : AntilipschitzWith 2 phi := lineSampling_antilipschitz u hu t ht'
  have hF : MemLp F 2 volume := (line_memLp_comp phi hphi ha f f.continuous.measurable (f.memLp 2 volume)).1
  have hFm : Measurable F := f.continuous.measurable.comp hphi
  have hFbound (y : ℝ) : ‖F y‖≤SchwartzMap.seminorm ℝ 0 0 f := f.norm_le_seminorm ℝ _
  have hfirst := (lineConvolution_energy_bound K K.integrable K.continuous.measurable F hFm hF).1
  have hsecond := (line_memLp_comp phi hphi ha q q.continuous.measurable (q.memLp 2 volume)).1
  have hC : lineSamplingL2Path u hu t (f.toLp 2 volume)=hF.toLp F := by
    simp only [lineSamplingL2Path,dite_eq_left ht',lineCompositionL2_onSchwartz]
    rfl
  have hTC : lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t (f.toLp 2 volume))=
      hfirst.toLp (lineConvolution K F) := by
    rw [hC]
    exact lineL2Projection_on_bounded m 1 (by norm_num) F hFm hF _ hFbound
  have hCT : lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume))=
      hsecond.toLp (q ∘ phi) := by
    rw [lineL2Projection_onSchwartz]
    simp only [lineSamplingL2Path,dite_eq_left ht',lineCompositionL2_onSchwartz]
    rfl
  have heq : lineSamplingKernelCommutator m u t f=lineConvolution K F-q ∘ phi := by
    funext y
    simp only [lineSamplingKernelCommutator,Pi.sub_apply,Function.comp_apply,q,
      lineSchwartzProjection_eq_convolution]
    rfl
  have hD : MemLp (lineSamplingKernelCommutator m u t f) 2 volume := by
    rw [heq]
    exact hfirst.sub hsecond
  have hid : lineL2Projection m 1 (by norm_num) (lineSamplingL2Path u hu t (f.toLp 2 volume))-
      lineSamplingL2Path u hu t (lineL2Projection m 1 (by norm_num) (f.toLp 2 volume))=
      hD.toLp (lineSamplingKernelCommutator m u t f) := by
    rw [hTC,hCT,←hfirst.toLp_sub hsecond]
    congr 1
    exact heq.symm
  have hb := lipschitzCompositionCommutator_L2 m A hA hm u hu hub t ht (f.toLp 2 volume)
  rw [hid] at hb
  refine ⟨hD,?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hfNorm : ‖f.toLp 2 volume‖^2=∫ y, ‖f y‖^2 := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  rw [mul_pow,memLp_toL2_norm_sq volume _ hD,hfNorm] at hs
  exact hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingMihlin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiberwise Mihlin control of the actual planar sampling commutator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingCommutator_fiber (m : SchwartzMap ℝ ℂ)
    (u : (ℝ×ℝ) → ℝ) (t : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    verticalSamplingCommutator (lineProjectionKernel m 1 (by norm_num)) u t f (x,y)=
      lineSamplingKernelCommutator m (fun z => u (x,z)) t (scalarVerticalSlice f (x-t)) y := rfl

theorem verticalSamplingCommutator_mihlin_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (verticalSamplingCommutator (lineProjectionKernel m 1 (by norm_num)) u t f) 2 planeMeasure ∧
      (∫ z, ‖verticalSamplingCommutator (lineProjectionKernel m 1 (by norm_num)) u t f z‖^2 ∂planeMeasure)≤
        (16*lineCommutatorNormConstant*A*|t|)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let K := lineProjectionKernel m 1 (by norm_num)
  let D := verticalSamplingCommutator K u t f
  let c := (16*lineCommutatorNormConstant*A*|t|)^2
  have hline (x : ℝ) := lineSamplingKernelCommutator_energy m A hA hm
    (fun y => u (x,y)) (hu x) (fun y => hub (x,y)) t ht (scalarVerticalSlice f (x-t))
  have hDx (x : ℝ) : MemLp (fun y => D (x,y)) 2 volume ∧
      (∫ y, ‖D (x,y)‖^2) ≤ c*(∫ y, ‖f (x-t,y)‖^2) := by
    simpa only [D,K,verticalSamplingCommutator_fiber,scalarVerticalSlice_apply] using hline x
  have hDm : Measurable D := by
    have hsample : Measurable (sampledFunction u t f) :=
      f.continuous.measurable.comp (by fun_prop)
    exact (verticalConvolution_measurable K K.continuous.measurable _ hsample).sub
      ((verticalConvolution_measurable K K.continuous.measurable f f.continuous.measurable).comp (by fun_prop))
  have hi : Integrable (fun z => ‖f z‖^2) planeMeasure :=
    (f.memLp 2 planeMeasure).integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hinput : Integrable (fun x : ℝ => ∫ y : ℝ, ‖f (x-t,y)‖^2) :=
    hi.integral_prod_left.comp_sub_right t
  have hDi : Integrable (fun z => ‖D z‖^2) planeMeasure := by
    apply (integrable_prod_iff (hDm.norm.pow_const 2).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun x => (hDx x).1.integrable_norm_pow (by decide : (2:ℕ)≠0)
    · simp only [Real.norm_of_nonneg (sq_nonneg _)]
      apply (hinput.const_mul c).mono'
        (hDm.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (integral_nonneg fun y => sq_nonneg ‖D (x,y)‖)]
        exact (hDx x).2
  refine ⟨(memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).mpr hDi,?_⟩
  change (∫ z, ‖D z‖^2 ∂planeMeasure) ≤ c*(∫ z, ‖f z‖^2 ∂planeMeasure)
  rw [integral_prod _ hDi]
  calc
    _ ≤ ∫ x, c*(∫ y, ‖f (x-t,y)‖^2) :=
      integral_mono hDi.integral_prod_left (hinput.const_mul c) (fun x => (hDx x).2)
    _ = c*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      rw [integral_const_mul]
      congr 1
      calc
        (∫ x : ℝ, ∫ y : ℝ, ‖f (x-t,y)‖^2) = ∫ x : ℝ, ∫ y : ℝ, ‖f (x,y)‖^2 :=
          integral_sub_right_eq_self (fun x : ℝ => ∫ y : ℝ, ‖f (x,y)‖^2) t
        _ = _ := (integral_prod _ hi).symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MihlinTimeCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform full-input multiplier commutators for the short Hilbert
integral. The first time moment cancels its singularity. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_eq_profile (m : SchwartzMap ℝ ℂ) :
    (lineProjectionKernel m 1 (by norm_num) : ℝ → ℂ)=verticalProfileKernel m 1 0 := by
  funext x
  rw [lineProjectionKernel_eq_scaled m 1 (by norm_num),scaledSchwartzKernel_apply]
  simp only [verticalProfileKernel,modulatedTimeKernel,zero_mul,Real.fourierChar.map_zero_eq_one,one_smul]

theorem mihlinTimeCommutator_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖)) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then K t*
      verticalSamplingCommutator (verticalProfileKernel m 1 0) u t f z else 0) 2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then K t*
      verticalSamplingCommutator (verticalProfileKernel m 1 0) u t f z else 0‖^2 ∂planeMeasure)≤
      (∫ t, |t| *‖K t‖)^2*(16*lineCommutatorNormConstant*A)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let B := (16*lineCommutatorNormConstant*A)^2*(∫ z, ‖f z‖^2 ∂planeMeasure)
  have hB : 0≤B := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hfiber (t : ℝ) (ht : |t|≤1/4) := verticalSamplingCommutator_mihlin_energy m A hA hm u hum hu hub t ht f
  simp only [lineProjectionKernel_eq_profile] at hfiber
  have hqi : Integrable (verticalProfileKernel m 1 0) := modulatedTimeKernel_integrable _ 1 0 (by norm_num)
  have hqm : Measurable (verticalProfileKernel m 1 0) := by
    rw [←lineProjectionKernel_eq_profile]
    exact (lineProjectionKernel m 1 (by norm_num)).continuous.measurable
  have hh := shortTimeAverage_energy K hKm hK1
    (fun p => verticalSamplingCommutator (verticalProfileKernel m 1 0) u p.1 f p.2)
    (verticalSamplingCommutator_joint_measurable _ hqm hqi u hum f) B hB
    (fun t ht => (hfiber t ht).1) (fun t ht => by
      have hh := (hfiber t ht).2
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [B]
      simp only [mul_pow,sq_abs]
      ring)
  exact ⟨hh.1,hh.2.trans_eq (by dsimp only [B]; ring)⟩

theorem sharpVerticalCommutator_mihlin_energy (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (sharpVerticalCommutator m 1 0 epsilon R u f) 2 planeMeasure ∧
      (∫ z, ‖sharpVerticalCommutator m 1 0 epsilon R u f z‖^2 ∂planeMeasure)≤
        (32*lineCommutatorNormConstant*A*R)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  rw [sharpVerticalCommutator_eq m 1 0 epsilon R (by norm_num) he hR u hum f]
  have hh := mihlinTimeCommutator_energy m A hA hm u hum hu hub f
    (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_first_moment epsilon R he hR).1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp := pow_le_pow_left₀
    (integral_nonneg fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _))
    (sharpTimeKernel_first_moment epsilon R he hR).2 2
  have hb := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (sq_nonneg (16*lineCommutatorNormConstant*A))
      (integral_nonneg (μ:=planeMeasure) fun z => sq_nonneg ‖f z‖))
  first | (convert hb using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hb.trans (le_of_eq (by ring)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionPVLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution commutes with the limit of symmetric truncations
on Schwartz inputs. Domination comes from the global derivative bound and
does not use a full-frequency Hilbert estimate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_shortSharp_tendsto (K : ℝ → ℂ)
    (hKm : Measurable K) (hKi : Integrable K) (u : (ℝ×ℝ) → ℝ)
    (hu : Measurable u) (hub : ∀ z, |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4) (z : ℝ×ℝ) :
    Tendsto (fun n => verticalConvolution K
      (shortSlopeOperator (sharpTimeKernel (pvInnerRadius R n) R) u f) z)
      atTop (𝓝 (verticalConvolution K (productSlopePrincipalValue u R f) z)) := by
  let B : ℝ := 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R
  apply tendsto_integral_of_dominated_convergence (fun s => ‖K s‖*B)
  · intro n
    exact (hKm.mul ((shortSlopeOperator_measurable _ (sharpTimeKernel_measurable _ R)
      u hu f f.continuous.measurable).comp (by fun_prop))).aestronglyMeasurable
  · exact hKi.norm.mul_const B
  · intro n
    filter_upwards [] with s
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [shortSharp_eq_productSymmetric u f f.continuous _ R (pvInnerRadius_pos R hR n)
      (pvInnerRadius_lt R hR n).le hRsmall]
    exact productSymmetricTruncation_pointwise_bound u _ (hub _) f (_root_.OAI.SchwartzMap.global_lipschitz f) _ R
      (pvInnerRadius_pos R hR n).le (pvInnerRadius_lt R hR n).le
  · filter_upwards [] with s
    exact (shortSharp_tendsto_productSlopePrincipalValue u f f.differentiable R hR hRsmall _).const_mul (K s)

theorem sharpVerticalCommutator_tendsto (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (hW : 0<W) (hR : 0<R) (hRsmall : R≤1/4) (u : (ℝ×ℝ) → ℝ)
    (hu : Measurable u) (hub : ∀ z, |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Tendsto (fun n => sharpVerticalCommutator q W center (pvInnerRadius R n) R u f z)
      atTop (𝓝 (principalValueProfileCommutator q W center R u f z)) := by
  have hc : verticalConvolution (verticalProfileKernel q W center) f=
      schwartzVerticalProjection q W center f := by
    funext x
    exact (schwartzVerticalProjection_eq_convolution q W center hW f x).symm
  have h1 := verticalConvolution_shortSharp_tendsto (verticalProfileKernel q W center)
    (verticalProfileKernel_continuous q W center).measurable
    (verticalProfileKernel_integrable q W center hW) u hu hub f R hR hRsmall z
  have h2 := shortSharp_tendsto_productSlopePrincipalValue u
    (schwartzVerticalProjection q W center f) (schwartzVerticalProjection q W center f).differentiable
    R hR hRsmall z
  simpa only [sharpVerticalCommutator,principalValueProfileCommutator,Pi.sub_apply,hc] using h1.sub h2

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PrincipalValueProfileCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An unconditional L2 estimate for the actual principal-value/profile
commutator on a vertically band-limited input. It includes the passage to
the singular kernel, rather than assuming a bounded full PV operator. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem principalValueProfileCommutator_measurable (q : SchwartzMap ℝ ℂ)
    (W center R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (principalValueProfileCommutator q W center R u f) :=
  (verticalConvolution_measurable _ (verticalProfileKernel_continuous q W center).measurable
    _ (productSlopePrincipalValue_measurable u hu f f.differentiable R hR hRsmall)).sub
    (productSlopePrincipalValue_measurable u hu _
      (schwartzVerticalProjection q W center f).differentiable R hR hRsmall)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MihlinPVCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual full-input principal-value/multiplier commutators with a
uniform Mihlin bound and no frequency restriction on the input. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpVerticalCommutator_mihlin_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hu : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    eLpNorm (sharpVerticalCommutator m 1 0 epsilon R u f) 2 planeMeasure≤
      ENNReal.ofReal ((32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨hF,henergy⟩ := sharpVerticalCommutator_mihlin_energy m A hA hm epsilon R he hR u hum hu hub f
  have hi : ‖f.toLp 2 planeMeasure‖^2=∫ z, ‖f z‖^2 ∂planeMeasure :=
    memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  rw [←memLp_toL2_norm_sq planeMeasure _ hF,←hi] at henergy
  have hn : ‖hF.toLp (sharpVerticalCommutator m 1 0 epsilon R u f)‖≤
      (32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by have := lineCommutatorNormConstant_nonneg; positivity)).mp
    simpa only [mul_pow] using henergy
  rw [←Lp.enorm_toLp hF,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem principalValueProfileCommutator_mihlin_bound (m : SchwartzMap ℝ ℂ)
    (A : ℝ) (hA : 0≤A) (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (hufiber : ∀ x, LipschitzWith 1 (fun y => u (x,y))) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (principalValueProfileCommutator m 1 0 R u f) 2 planeMeasure ∧
    eLpNorm (principalValueProfileCommutator m 1 0 R u f) 2 planeMeasure≤
      ENNReal.ofReal ((32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖) := by
  have hmeas := principalValueProfileCommutator_measurable m 1 0 R hR hRsmall u hu.continuous.measurable f
  have hb : eLpNorm (principalValueProfileCommutator m 1 0 R u f) 2 planeMeasure≤
      ENNReal.ofReal ((32*lineCommutatorNormConstant*A*R)*‖f.toLp 2 planeMeasure‖) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
      (Eventually.of_forall fun n => sharpVerticalCommutator_mihlin_bound m A hA hm
        (pvInnerRadius R n) R (pvInnerRadius_pos R hR n) hR u hu.continuous.measurable hufiber hub f)
      (fun n => (sharpVerticalCommutator_mihlin_energy m A hA hm
        (pvInnerRadius R n) R (pvInnerRadius_pos R hR n) hR u hu.continuous.measurable hufiber hub f).1.aestronglyMeasurable)
    exact Eventually.of_forall (sharpVerticalCommutator_tendsto m 1 0 R (by norm_num) hR hRsmall
      u hu.continuous.measurable hub f)
  exact ⟨⟨hmeas.aestronglyMeasurable,hb.trans_lt (by simp)⟩,hb⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlaneVerticalLipschitz
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical Euclidean coordinate has Lipschitz constant exactly one. -/
noncomputable section
namespace LipschitzHilbert

theorem planeCoordinates_vertical_dist (x y z : ℝ) :
    dist (planeCoordinates (x,y)) (planeCoordinates (x,z))=dist y z := by
  have hs : dist (planeCoordinates (x,y)) (planeCoordinates (x,z))^2=dist y z^2 := by
    rw [dist_eq_norm,EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two,planeCoordinates_apply,PiLp.sub_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,sub_self,abs_zero,zero_pow (by decide : 2≠0),
      zero_add,Real.dist_eq,Real.norm_eq_abs]
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hs

theorem product_slope_vertical_lipschitz (u : Plane → ℝ) (hu : LipschitzWith 1 u) (x : ℝ) :
    LipschitzWith 1 (fun y => u (planeCoordinates (x,y))) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [NNReal.coe_one,one_mul,planeCoordinates_vertical_dist] using
    hu.dist_le_mul (planeCoordinates (x,y)) (planeCoordinates (x,z))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SignedPVCommutator
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform actual signed-annular principal-value commutators for the
Euclidean Lipschitz slope fields in the target theorem. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem signedPVCommutatorConstant_nonneg : 0 ≤ signedPVCommutatorConstant :=
  mul_nonneg (mul_nonneg (by norm_num) lineCommutatorNormConstant_nonneg) signedAnnularMihlinConstant_nonneg

theorem signedPVCommutator_bound (N : ℕ) (s : ℕ → Bool)
    (field : Plane → ℝ) (hf : LipschitzWith 1 field) (hfb : ∀ z, |field z|≤1/4)
    (R : ℝ) (hR : 0<R) (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (principalValueProfileCommutator (signedAnnularSymbol N s) 1 0 R
      (fun z => field (planeCoordinates z)) f) 2 planeMeasure ∧
    eLpNorm (principalValueProfileCommutator (signedAnnularSymbol N s) 1 0 R
      (fun z => field (planeCoordinates z)) f) 2 planeMeasure≤
        ENNReal.ofReal ((signedPVCommutatorConstant*R)*‖f.toLp 2 planeMeasure‖) := by
  apply principalValueProfileCommutator_mihlin_bound _ signedAnnularMihlinConstant
    signedAnnularMihlinConstant_nonneg
  · intro r hr
    exact signedAnnularSymbol_mihlin_four N r (hr.trans (by norm_num)) s
  · exact hR
  · exact hRs
  · simpa only [mul_one] using product_slope_lipschitz field hf
  · exact product_slope_vertical_lipschitz field hf
  · intro z
    exact (hfb (planeCoordinates z)).trans (by norm_num)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularEnlargement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed symmetric enlarged annular cutoff is one on every nonzero
piece of the concrete annular resolution. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyEnlarged_absorb (x : ℝ) :
    reassemblyEnlarged x*reassemblyDifference x=reassemblyDifference x := by
  have h := reassemblyPositive_halfsum x
  rw [reassemblyPositive_apply,reassemblyPositive_apply,reassemblyDifference_even] at h
  rw [reassemblyEnlarged_apply,add_mul]
  exact h

theorem reassemblyEnlarged_support (x : ℝ) (hx : reassemblyEnlarged x≠0) :
    1≤|x| ∧ |x|≤2 := by
  by_cases hp : reassemblyOuter x=0
  · have hn : reassemblyOuter (-x)≠0 := by
      intro hz
      exact hx (by rw [reassemblyEnlarged_apply,hp,hz,add_zero])
    have h := reassemblyOuter_support (-x) hn
    have hxneg : x≤0 := by linarith [h.1]
    rw [abs_of_nonpos hxneg]
    exact h
  · have h := reassemblyOuter_support x hp
    rw [abs_of_nonneg (show 0≤x by linarith [h.1])]
    exact h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSelfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real vertical cutoffs are self-adjoint in complex L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProjection_inner_schwartz (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, conj (p s)=p s) (w : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    inner ℂ ((schwartzVerticalProjection p w 0 f).toLp 2 planeMeasure) (g.toLp 2 planeMeasure)=
      inner ℂ (f.toLp 2 planeMeasure) ((schwartzVerticalProjection p w 0 g).toLp 2 planeMeasure) := by
  calc
    _ = ∫ z, inner ℂ (schwartzVerticalProjection p w 0 f z) (g z) ∂planeMeasure :=
      memLp_inner_integral planeMeasure _ _ ((schwartzVerticalProjection p w 0 f).memLp 2 planeMeasure) (g.memLp 2 planeMeasure)
    _ = ∫ z, inner ℂ (planarFourier (schwartzVerticalProjection p w 0 f) z) (planarFourier g z) ∂planeMeasure :=
      (planar_integral_inner_fourier _ _).symm
    _ = ∫ z, inner ℂ (planarFourier f z) (planarFourier (schwartzVerticalProjection p w 0 g) z) ∂planeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [schwartzVerticalProjection_fourier,sub_zero,RCLike.inner_apply,map_mul,hp]
      ring
    _ = ∫ z, inner ℂ (f z) (schwartzVerticalProjection p w 0 g z) ∂planeMeasure :=
      planar_integral_inner_fourier _ _
    _ = _ := (memLp_inner_integral planeMeasure _ _ (f.memLp 2 planeMeasure)
      ((schwartzVerticalProjection p w 0 g).memLp 2 planeMeasure)).symm

theorem verticalL2Projection_inner (p : SchwartzMap ℝ ℂ) (hp : ∀ s, conj (p s)=p s)
    (w : ℝ) (hw : 0<w) (f g : Lp ℂ 2 planeMeasure) :
    inner ℂ (verticalL2Projection p w f) g=inner ℂ f (verticalL2Projection p w g) := by
  have hd : DenseRange (fun h : SchwartzMap (ℝ×ℝ) ℂ => h.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on₂ ?_ ?_ f g
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F G
    rw [verticalL2Projection_onSchwartz _ _ hw,verticalL2Projection_onSchwartz _ _ hw]
    exact verticalProjection_inner_schwartz p hp w F G

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_VerticalFrameSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite vertical-band synthesis follows from the same square bound
as analysis, using self-adjointness and Hilbert-space duality. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation
variable {ι : Type*}

theorem verticalFrame_synthesis (I : Finset ι) (p : ι → SchwartzMap ℝ ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hp : ∀ i s, conj (p i s)=p i s)
    (M : ℝ) (hM : 0≤M) (hsymbol : ∀ eta, (∑ i∈I, ‖p i (w i*eta)‖^2)≤M)
    (f : ι → Lp ℂ 2 planeMeasure) :
    ‖∑ i∈I, verticalL2Projection (p i) (w i) (f i)‖≤
      Real.sqrt M*Real.sqrt (∑ i∈I, ‖f i‖^2) := by
  let y := ∑ i∈I, verticalL2Projection (p i) (w i) (f i)
  let E := ∑ i∈I, ‖f i‖^2
  have hE : 0≤E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hid : inner ℂ y y=∑ i∈I, inner ℂ (f i) (verticalL2Projection (p i) (w i) y) := by
    change inner ℂ (∑ i∈I, verticalL2Projection (p i) (w i) (f i)) y=_
    simp only [sum_inner]
    exact Finset.sum_congr rfl (fun i _ => verticalL2Projection_inner (p i) (hp i) (w i) (hw i) (f i) y)
  have hsq : ‖y‖^2≤Real.sqrt E*Real.sqrt (M*‖y‖^2) := by
    calc
      _ = ‖inner ℂ y y‖ := by
        simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg y)]
      _ = ‖∑ i∈I, inner ℂ (f i) (verticalL2Projection (p i) (w i) y)‖ := congrArg norm hid
      _ ≤ ∑ i∈I, ‖inner ℂ (f i) (verticalL2Projection (p i) (w i) y)‖ := norm_sum_le _ _
      _ ≤ ∑ i∈I, ‖f i‖*‖verticalL2Projection (p i) (w i) y‖ :=
        Finset.sum_le_sum (fun _ _ => norm_inner_le_norm _ _)
      _ ≤ Real.sqrt E*Real.sqrt (∑ i∈I, ‖verticalL2Projection (p i) (w i) y‖^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt I _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (verticalFrame_L2 I p w hw M hsymbol y)) (Real.sqrt_nonneg E)
  rw [Real.sqrt_mul hM,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg y)] at hsq
  by_cases hy : ‖y‖=0
  · change ‖y‖≤_
    rw [hy]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hypos : 0<‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    have key : ‖y‖*‖y‖≤‖y‖*(Real.sqrt M*Real.sqrt E) := by nlinarith only [hsq]
    exact le_of_mul_le_mul_left key hypos

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnnularEnlargedFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap of the enlarged annuli used to reconstruct
outputs whose individual annular projections are in L2. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyEnlarged_real (x : ℝ) : conj (reassemblyEnlarged x)=reassemblyEnlarged x := by
  simp only [reassemblyEnlarged_apply,reassemblyOuter_apply,map_add,Complex.conj_ofReal]

theorem reassemblyEnlarged_norm (x : ℝ) : ‖reassemblyEnlarged x‖≤2 := by
  rw [reassemblyEnlarged_apply]
  have h := (norm_add_le _ _).trans (add_le_add (reassemblyOuter_norm x) (reassemblyOuter_norm (-x)))
  norm_num at h ⊢
  exact h

theorem natural_enlarged_nonzero_count (I : Finset ℕ) (x : ℝ) :
    (I.filter (fun n => reassemblyEnlarged ((3/2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => reassemblyEnlarged ((3/2:ℝ)^n*x)≠0)
  change A.card≤3
  have hsep (j k : ℕ) (hj : j∈A) (hk : k∈A) (hjk : j+2≤k) : False := by
    have hjb := reassemblyEnlarged_support _ (Finset.mem_filter.mp hj).2
    have hkb := reassemblyEnlarged_support _ (Finset.mem_filter.mp hk).2
    have hp : (3/2:ℝ)^j*(9/4)≤(3/2:ℝ)^k := by
      calc
        _ = (3/2:ℝ)^(j+2) := by rw [pow_add]; norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hjk
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg x)
    have habs (n : ℕ) : |(3/2:ℝ)^n*x|=(3/2:ℝ)^n*|x| := by
      rw [abs_mul,abs_of_pos (by positivity)]
    rw [habs] at hjb hkb
    nlinarith only [hh,hjb.1,hkb.2]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k j hk hj (by omega)
      · by_contra hn
        exact hsep j k hj hk (by omega)
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem enlarged_annular_square (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range (2*N+1), ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2)≤12 := by
  classical
  let I := Finset.range (2*N+1)
  let A := I.filter (fun n => reassemblyEnlarged (reassemblyScale N n*x)≠0)
  have he : (∑ n∈I, ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2)=
      ∑ n∈A, ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : reassemblyEnlarged (reassemblyScale N n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have hscale (n : ℕ) : reassemblyScale N n*x=(3/2:ℝ)^n*((2/3:ℝ)^N*x) := by
    unfold reassemblyScale
    ring
  have hc : A.card≤3 := by
    simpa only [A,hscale] using natural_enlarged_nonzero_count I ((2/3:ℝ)^N*x)
  change (∑ n∈I, ‖reassemblyEnlarged (reassemblyScale N n*x)‖^2)≤12
  rw [he]
  calc
    _ ≤ ∑ n∈A, (4:ℝ) := Finset.sum_le_sum fun n _ => by
      have h := reassemblyEnlarged_norm (reassemblyScale N n*x)
      nlinarith [norm_nonneg (reassemblyEnlarged (reassemblyScale N n*x))]
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by exact_mod_cast Nat.mul_le_mul_right 4 hc

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBoundedSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform synthesis of actual annular projections of a bounded function
once those individual projections have finite square energy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finiteFunctionSum_toLp {n : ℕ} (f : Fin n → (ℝ×ℝ) → ℂ)
    (h : ∀ i, MemLp (f i) 2 planeMeasure) :
    (finiteFunctionSum_memLp f h).toLp (fun z => ∑ i, f i z)=∑ i, (h i).toLp (f i) := by
  apply Lp.ext
  have hco := ae_all_iff.mpr (fun i => (h i).coeFn_toLp)
  filter_upwards [(finiteFunctionSum_memLp f h).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => (h i).toLp (f i)),hco] with z hz hs hi
  rw [hz,hs]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

theorem annularBounded_synthesis (N : ℕ) (F : (ℝ×ℝ) → ℂ) (hFm : Measurable F)
    (B : ℝ) (hFb : ∀ z, ‖F z‖≤B)
    (hG : ∀ i, MemLp (annularBoundedComponent N F i) 2 planeMeasure) :
    ‖(finiteFunctionSum_memLp (annularBoundedComponent N F) hG).toLp
      (fun z => ∑ i, annularBoundedComponent N F i z)‖≤
      Real.sqrt 12*Real.sqrt (∑ i, ‖(hG i).toLp (annularBoundedComponent N F i)‖^2) := by
  let g := fun i => (hG i).toLp (annularBoundedComponent N F i)
  have hid (i : Fin (2*N+1)) : verticalL2Projection reassemblyEnlarged (reassemblyScale N i) (g i)=g i :=
    verticalL2Projection_on_projected_bounded reassemblyEnlarged reassemblyDifferenceSchwartz
      reassemblyEnlarged_absorb _ (reassemblyScale_pos N i) F hFm B hFb (hG i)
  have hs := verticalFrame_synthesis Finset.univ (fun _ : Fin (2*N+1) => reassemblyEnlarged)
    (fun i => reassemblyScale N i) (fun i => reassemblyScale_pos N i)
    (fun _ => reassemblyEnlarged_real) 12 (by norm_num) (fun eta => by
      exact (Fin.sum_univ_eq_sum_range (fun n =>
        ‖reassemblyEnlarged (reassemblyScale N n*eta)‖^2) (2*N+1)).trans_le
          (enlarged_annular_square N eta)) g
  simp only [hid] at hs
  rw [finiteFunctionSum_toLp]
  exact hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVCommutatorSquare
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed commutator estimate controls the square sum of individual
actual annular PV commutators without assuming a full PV L2 operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem signedAnnularSymbol_fin (N : ℕ) (s : ℕ → Bool) :
    signedAnnularSymbol N s=∑ i : Fin (2*N+1), if s i then annularProfile N i else -annularProfile N i := by
  symm
  unfold annularProfile
  exact Fin.sum_univ_eq_sum_range (fun n => if s n then
    dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne' else
    -dilatedSlopeWindow reassemblyDifferenceSchwartz (reassemblyScale N n)
      (reassemblyScale_pos N n).ne') (2*N+1)

theorem annularPVComm_signed (N : ℕ) (s : ℕ → Bool) (u : (ℝ×ℝ) → ℝ)
    (hum : Measurable u) (hub : ∀ z, |u z|≤1) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    signedFunction (annularPVComm N u R f) (fun i => s i)=
      principalValueProfileCommutator (signedAnnularSymbol N s) 1 0 R u f := by
  rw [←pvCommutatorSymbolLM_apply 1 (by norm_num) u hum hub R hR hRs f,
    signedAnnularSymbol_fin,map_sum]
  funext z
  simp only [signedFunction,finiteSignedSum,Finset.sum_apply,annularPVComm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [map_neg,Pi.neg_apply,pvCommutatorSymbolLM_apply]

theorem annularPVComm_square (N : ℕ) (field : Plane → ℝ) (hf : LipschitzWith 1 field)
    (hfb : ∀ z, |field z|≤1/4) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ∃ hcomm : ∀ i, MemLp (annularPVComm N (fun z => field (planeCoordinates z)) R f i) 2 planeMeasure,
      (∑ i, ‖(hcomm i).toLp (annularPVComm N (fun z => field (planeCoordinates z)) R f i)‖^2)≤
        (signedPVCommutatorConstant*R)^2*‖f.toLp 2 planeMeasure‖^2 := by
  let u := fun z => field (planeCoordinates z)
  have hum : Measurable u := hf.continuous.measurable.comp planeCoordinates.measurable
  have hub (z) : |u z|≤1 := (hfb _).trans (by norm_num)
  have hh := signedFunction_square_bound planeMeasure (annularPVComm N u R f)
    ((signedPVCommutatorConstant*R)*‖f.toLp 2 planeMeasure‖)
    (mul_nonneg (mul_nonneg signedPVCommutatorConstant_nonneg hR.le) (norm_nonneg _)) (fun s => by
      let ss : ℕ → Bool := fun n => if hn : n<2*N+1 then s ⟨n,hn⟩ else false
      have he : (fun i : Fin (2*N+1) => ss i)=s := by
        funext i
        dsimp only [ss]
        rw [dite_eq_left i.isLt]
      rw [←he,annularPVComm_signed N ss u hum hub R hR hRs f]
      exact signedPVCommutator_bound N ss field hf hfb R hR hRs f)
  obtain ⟨hc,hcBound⟩ := hh
  exact ⟨hc,by simpa only [mul_pow] using hcBound⟩

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

theorem annularProjection_fourier_support (p : SchwartzMap ℝ ℂ)
    (hp : ∀ x, p x≠0 → x∈fixedAnnulus) (W : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ)
    (h : planarFourier (schwartzVerticalProjection p W 0 f) omega≠0) :
    W*omega.2∈fixedAnnulus := by
  rw [schwartzVerticalProjection_fourier,sub_zero] at h
  exact hp _ (mul_ne_zero_iff.mp h).1

theorem reassemblyDifference_fixedAnnulus (x : ℝ) (hx : reassemblyDifferenceSchwartz x≠0) :
    x∈fixedAnnulus := by
  change 1≤|x| ∧ |x|≤2
  have hsmall : 9/8 < |x| := lt_of_not_ge (fun h => hx (reassemblyDifference_small x h))
  have hlarge : |x| < 117/64 := lt_of_not_ge (fun h => hx (reassemblyDifference_large x h))
  constructor <;> linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularPVPartialBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite annular output has a uniform L2 bound, derived directly
from the annular input estimates and actual signed PV commutators. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem annularPVComm_eq (N : ℕ) (i : Fin (2*N+1)) (u : (ℝ×ℝ) → ℝ)
    (R : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    annularPVComm N u R f i=
      annularBoundedComponent N (productSlopePrincipalValue u R f) i-
      productSlopePrincipalValue u R
        (schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N i) 0 f) := by
  unfold annularPVComm annularProfile principalValueProfileCommutator
  rw [verticalMultiplier_dilate _ _ 1 (reassemblyScale_pos N i) (by norm_num),
    schwartzVerticalProjection_dilate,mul_one]
  rfl

theorem annularPVPartial_bound_oai (N : ℕ) (field : Plane → ℝ) (hf : LipschitzWith 1 field)
    (hfb : ∀ z, |field z|≤1/4) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (D : ℝ) (hD : 0≤D)
    (hband : ∀ W : ℝ, 0<W → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ omega, planarFourier g omega≠0 → W*omega.2∈fixedAnnulus) →
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure≤
        ENNReal.ofReal (D*‖g.toLp 2 planeMeasure‖))
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
      eLpNorm (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
        ENNReal.ofReal (annularPVBoundConstant D*‖f.toLp 2 planeMeasure‖) := by
  let u := fun z => field (planeCoordinates z)
  let p := fun i : Fin (2*N+1) =>
    schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N i) 0 f
  let V := fun i : Fin (2*N+1) => productSlopePrincipalValue u R (p i)
  let G := annularBoundedComponent N (productSlopePrincipalValue u R f)
  obtain ⟨hc,hcBound⟩ := annularPVComm_square N field hf hfb R hR hRs f
  have hv (i : Fin (2*N+1)) : MemLp (V i) 2 planeMeasure ∧
      eLpNorm (V i) 2 planeMeasure≤ENNReal.ofReal (D*‖(p i).toLp 2 planeMeasure‖) :=
    hband _ (reassemblyScale_pos N i) (p i)
      (annularProjection_fourier_support reassemblyDifferenceSchwartz reassemblyDifference_fixedAnnulus
        (reassemblyScale N i) f)
  have hGid (i : Fin (2*N+1)) : G i=annularPVComm N u R f i+V i := by
    rw [annularPVComm_eq]
    exact (sub_add_cancel _ _).symm
  have hG (i : Fin (2*N+1)) : MemLp (G i) 2 planeMeasure := by
    rw [hGid]
    exact (hc i).add (hv i).1
  have hGlp (i : Fin (2*N+1)) : (hG i).toLp (G i)=
      (hc i).toLp (annularPVComm N u R f i)+(hv i).1.toLp (V i) := by
    apply Lp.ext
    filter_upwards [(hG i).coeFn_toLp,(hc i).coeFn_toLp,(hv i).1.coeFn_toLp,
      Lp.coeFn_add ((hc i).toLp _) ((hv i).1.toLp _)] with z hg he hb ha
    rw [hg,ha]
    simp only [Pi.add_apply]
    rw [he,hb]
    exact congrFun (hGid i) z
  have hvNorm (i : Fin (2*N+1)) : ‖(hv i).1.toLp (V i)‖≤D*‖(p i).toLp 2 planeMeasure‖ := by
    rw [Lp.norm_toLp]
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv i).2
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hD (norm_nonneg _))] using he
  have hpSquare : (∑ i : Fin (2*N+1), ‖(p i).toLp 2 planeMeasure‖^2)≤
      12*‖f.toLp 2 planeMeasure‖^2 := by
    have hh := annular_upper_frame N (f.toLp 2 planeMeasure)
    simp only [verticalL2Projection_onSchwartz _ _ (reassemblyScale_pos N _)] at hh
    rw [Fin.sum_univ_eq_sum_range (fun n =>
      ‖(schwartzVerticalProjection reassemblyDifferenceSchwartz (reassemblyScale N n) 0 f).toLp 2 planeMeasure‖^2)]
    exact hh
  have hvSquare : (∑ i, ‖(hv i).1.toLp (V i)‖^2)≤12*D^2*‖f.toLp 2 planeMeasure‖^2 := by
    calc
      _ ≤ ∑ i : Fin (2*N+1), (D*‖(p i).toLp 2 planeMeasure‖)^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hvNorm i) 2)
      _ = D^2*(∑ i : Fin (2*N+1), ‖(p i).toLp 2 planeMeasure‖^2) := by
        simp only [mul_pow,Finset.mul_sum]
      _ ≤ D^2*(12*‖f.toLp 2 planeMeasure‖^2) :=
        mul_le_mul_of_nonneg_left hpSquare (sq_nonneg D)
      _ = _ := by ring
  have hcSquare : (∑ i, ‖(hc i).toLp (annularPVComm N u R f i)‖^2)≤
      signedPVCommutatorConstant^2*‖f.toLp 2 planeMeasure‖^2 := by
    apply hcBound.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (mul_nonneg signedPVCommutatorConstant_nonneg hR.le) _ 2
    exact mul_le_of_le_one_right signedPVCommutatorConstant_nonneg (by linarith)
  have hgSquare : (∑ i, ‖(hG i).toLp (G i)‖^2)≤
      (2*(signedPVCommutatorConstant^2+12*D^2))*‖f.toLp 2 planeMeasure‖^2 := by
    have hpoint (i : Fin (2*N+1)) : ‖(hG i).toLp (G i)‖^2≤
        2*‖(hc i).toLp (annularPVComm N u R f i)‖^2+2*‖(hv i).1.toLp (V i)‖^2 := by
      rw [hGlp]
      have ht := norm_add_le ((hc i).toLp (annularPVComm N u R f i)) ((hv i).1.toLp (V i))
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖(hc i).toLp (annularPVComm N u R f i)‖-‖(hv i).1.toLp (V i)‖)]
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
    nlinarith only [hh,hcSquare,hvSquare]
  have hsum := annularBounded_synthesis N (productSlopePrincipalValue u R f)
    (productSlopePrincipalValue_measurable u (hf.continuous.measurable.comp planeCoordinates.measurable)
      f f.differentiable R hR hRs) (2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R)
    (fun z => productSchwartzPV_pointwise_bound u z ((hfb _).trans (by norm_num)) f R hR) hG
  have hn : ‖(finiteFunctionSum_memLp G hG).toLp (fun z => ∑ i, G i z)‖≤
      annularPVBoundConstant D*‖f.toLp 2 planeMeasure‖ := by
    apply hsum.trans
    apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgSquare) (Real.sqrt_nonneg 12)).trans_eq
    rw [Real.sqrt_mul (by positivity : 0≤2*(signedPVCommutatorConstant^2+12*D^2)),
      Real.sqrt_sq (norm_nonneg (f.toLp 2 planeMeasure))]
    dsimp only [annularPVBoundConstant]
    ring
  have hid : (fun z => ∑ i, G i z)=annularPVPartial N u R f := by
    funext z
    simpa only [G,annularBoundedComponent,annularPVPartial,Finset.sum_apply] using
      Fin.sum_univ_eq_sum_range (fun n => verticalConvolution
      (verticalProfileKernel reassemblyDifferenceSchwartz (reassemblyScale N n) 0)
      (productSlopePrincipalValue u R f) z) (2*N+1)
  have hm : MemLp (annularPVPartial N u R f) 2 planeMeasure := by
    rw [←hid]
    exact finiteFunctionSum_memLp G hG
  refine ⟨hm,?_⟩
  rw [←hid,←Lp.enorm_toLp (finiteFunctionSum_memLp G hG),←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound_oai := @OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound_oai
