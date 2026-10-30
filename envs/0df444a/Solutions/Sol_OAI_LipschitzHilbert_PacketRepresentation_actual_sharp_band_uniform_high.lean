-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:21:13.315814+00:00
-- url     : https://prove2.me/submissions/27a01bc8-b142-4a6f-903c-2a7baed02890

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_band_projected_high

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed real smooth bin profile whose squared translates sum to one.
The trigonometric construction avoids a variable normalization denominator. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem binSquareStep_zero (x : ℝ) (hx : x≤0) : binSquareStep x=0 := by
  simp [binSquareStep,Real.smoothTransition.zero_of_nonpos hx]

theorem binSquareStep_one (x : ℝ) (hx : 1≤x) : binSquareStep x=1 := by
  simp [binSquareStep,Real.smoothTransition.one_of_one_le hx]

theorem verticalBinProfileReal_sq (x : ℝ) :
    (verticalBinProfileReal x)^2=binSquareStep (x+1)-binSquareStep x := by
  by_cases hx : x≤0
  · simp [verticalBinProfileReal,binSquareStep,Real.smoothTransition.zero_of_nonpos hx]
  · have hx1 : 1≤x+1 := by linarith
    have hs := Real.sin_sq_add_cos_sq (Real.pi/2*Real.smoothTransition x)
    simp only [verticalBinProfileReal,binSquareStep,Real.smoothTransition.one_of_one_le hx1,
      mul_one,Real.sin_pi_div_two,one_mul,one_pow]
    linarith

theorem verticalBinProfile_apply (x : ℝ) : verticalBinProfile x=(verticalBinProfileReal x : ℂ) := rfl

theorem verticalBinProfile_real (x : ℝ) : star (verticalBinProfile x)=verticalBinProfile x := by
  simp only [verticalBinProfile_apply,Complex.star_def,Complex.conj_ofReal]

theorem verticalBinProfile_support (x : ℝ) (hx : verticalBinProfile x≠0) : |x|≤1 := by
  by_contra h
  have ha : 1 < |x| := lt_of_not_ge h
  have hxx : x≤-1 ∨ 1≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at ha
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at ha
      exact Or.inr ha.le
  exact hx (by simp only [verticalBinProfile_apply,verticalBinProfileReal_zero x hxx,Complex.ofReal_zero])

theorem verticalBinProfileReal_sum_sq (x : ℝ) (N : ℕ) :
    (∑ n∈Finset.range N, (verticalBinProfileReal (x-(n:ℝ)))^2)=
      binSquareStep (x+1)-binSquareStep (x+1-N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,verticalBinProfileReal_sq]
    push_cast
    rw [show x+1-((N:ℝ)+1)=x-N by ring,show x-N+1=x+1-N by ring]
    ring

theorem verticalBinProfile_sum_sq (K : ℕ) (x : ℝ) (hx : |x|≤K) :
    (∑ n∈Finset.range (2*K+1), (verticalBinProfile (x+K-(n:ℝ)))^2)=1 := by
  simp only [verticalBinProfile_apply,←Complex.ofReal_pow,←Complex.ofReal_sum]
  rw [verticalBinProfileReal_sum_sq]
  have hb := abs_le.mp hx
  rw [binSquareStep_one _ (by linarith),binSquareStep_zero _ (by push_cast; linarith)]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteVerticalBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite real square partition of a positive vertical band.
Only bins meeting the original band are retained. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinWindow_apply (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) (eta : ℝ) :
    verticalBinWindow K W n eta=verticalBinProfile (W*eta+K-n) := by
  unfold verticalBinWindow verticalBinCenter
  congr 1
  field_simp
  ring

theorem verticalBinWindow_support (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) (eta : ℝ)
    (h : verticalBinWindow K W n eta≠0) : |eta-verticalBinCenter K W n|≤1/W := by
  have hs := verticalBinProfile_support _ h
  rw [abs_mul,abs_of_pos hW] at hs
  exact (le_div_iff₀ hW).mpr (by nlinarith)

theorem verticalBinWindow_mem_labels (K : ℕ) (w W c C eta : ℝ)
    (hw : 0<w) (hW : 0<W) (hlo : c≤w*eta) (hhi : w*eta≤C)
    (n : ℕ) (hn : n∈Finset.range (2*K+1)) (h : verticalBinWindow K W n eta≠0) :
    n∈verticalBinLabels K w W c C := by
  have hs := abs_le.mp (verticalBinWindow_support K W hW n eta h)
  have hsl := mul_le_mul_of_nonneg_left hs.1 hw.le
  have hsu := mul_le_mul_of_nonneg_left hs.2 hw.le
  simp only [mul_neg,mul_one_div,mul_sub] at hsl hsu
  apply Finset.mem_filter.mpr
  refine ⟨hn,?_⟩
  constructor <;> nlinarith

theorem verticalBinWindow_sum_sq (K : ℕ) (w W c C eta : ℝ)
    (hw : 0<w) (hW : 0<W) (hlo : c≤w*eta) (hhi : w*eta≤C) (hK : |W*eta|≤K) :
    (∑ n∈verticalBinLabels K w W c C, (verticalBinWindow K W n eta)^2)=1 := by
  have heq : (∑ n∈verticalBinLabels K w W c C, (verticalBinWindow K W n eta)^2)=
      ∑ n∈Finset.range (2*K+1), (verticalBinWindow K W n eta)^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hn'
    have hz : verticalBinWindow K W n eta=0 := by
      by_contra h
      exact hn' (verticalBinWindow_mem_labels K w W c C eta hw hW hlo hhi n hn h)
    simp only [hz,zero_pow (by decide : 2≠0)]
  rw [heq]
  simp_rw [verticalBinWindow_apply K W hW]
  exact verticalBinProfile_sum_sq K (W*eta) hK

theorem verticalBinLabels_card (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hC : 0≤C) :
    ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(C*W/w)+3 := by
  have hcard : (verticalBinLabels ⌈C*W/w⌉₊ w W c C).card≤2*⌈C*W/w⌉₊+1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hcard' : ((verticalBinLabels ⌈C*W/w⌉₊ w W c C).card:ℝ)≤2*(⌈C*W/w⌉₊:ℝ)+1 := by
    exact_mod_cast hcard
  have hceil := (Nat.ceil_lt_add_one (show 0≤C*W/w by positivity)).le
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FrozenSlopeMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The multiplier identity freezes the direction at the output point.
It is proved by Fubini for actual integrable time and frequency data. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem frozen_slope_multiplier (k : ℝ → ℂ) (F : ℝ×ℝ → ℂ)
    (hk : Integrable k) (hF : Integrable F planeMeasure)
    (u : ℝ×ℝ → ℝ) (x : ℝ×ℝ) :
    slopeKernelOperator k u (planarInverse F) x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*F omega) ∂planeMeasure := by
  let phase := fun (t : ℝ) (omega : ℝ×ℝ) =>
    (x.1-t)*omega.1+(x.2-t*u x)*omega.2
  let H := fun p : ℝ×(ℝ×ℝ) =>
    (k p.1*F p.2)*(Real.fourierChar (phase p.1 p.2):ℂ)
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply (hk.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : ℝ×(ℝ×ℝ) =>
        (Real.fourierChar (phase p.1 p.2) : ℂ)) by dsimp [phase]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      exact le_of_eq (Circle.norm_coe _)
  have hleft (t : ℝ) : k t*planarInverse F (x.1-t,x.2-t*u x) =
      ∫ omega, H (t,omega) ∂planeMeasure := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    change k t*((Real.fourierChar (phase t omega):ℂ)*F omega)=_
    dsimp only [H]
    ring
  have hright (omega : ℝ×ℝ) : (∫ t, H (t,omega)) =
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*F omega) := by
    rw [Real.fourier_eq]
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H]
    have hp : phase t omega=(x.1*omega.1+x.2*omega.2)+(-(t*(omega.1+u x*omega.2))) := by
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

end LipschitzHilbert.PacketRepresentation

end

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

theorem schwartz_frozen_slope_multiplier (k : ℝ → ℂ) (hk : Integrable k)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (u : ℝ×ℝ → ℝ) (x : ℝ×ℝ) :
    PacketRepresentation.slopeKernelOperator k u f x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*planarFourier f omega) ∂volume.prod volume := by
  have h := PacketRepresentation.frozen_slope_multiplier k (planarFourier f)
    hk (planarFourier_integrable f) u x
  simpa only [funext (planarFourier_inversion f)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed enlarged vertical cutoff equals one on every bin profile.
The finite bin partition is exact throughout the prescribed annulus. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinPlateau_mul_profile (x : ℝ) :
    verticalBinPlateau x*verticalBinProfile x=verticalBinProfile x := by
  by_cases hx : verticalBinProfile x=0
  · simp only [hx,mul_zero]
  · rw [verticalBinPlateau_one x (verticalBinProfile_support x hx),one_mul]

theorem positiveBand_bin_partition (w W c C eta : ℝ) (hw : 0<w) (hW : 0<W) (hc : 0 < c)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      (verticalBinWindow ⌈C*W/w⌉₊ W n eta)^2)=1 := by
  apply verticalBinWindow_sum_sq _ w W c C eta hw hW hlo hhi
  have he : 0<eta := pos_of_mul_pos_right (hc.trans_le hlo) hw.le
  rw [abs_of_pos (mul_pos hW he)]
  apply le_trans _ (Nat.le_ceil _)
  apply (le_div_iff₀ hw).mpr
  nlinarith [mul_le_mul_of_nonneg_left hhi hW.le]

end LipschitzHilbert.PacketRepresentation

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalConvolutionL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical convolution acts on actual measurable planar functions.
Its L1 and uniform bounds are independent of bin width and carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1))
      (volume.prod planeMeasure) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) => K p.1*f (p.2.1,p.2.2-p.1)) := by
    exact (hKm.comp measurable_fst).mul (hfm.comp (by fun_prop))
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((verticalTranslation_measurePreserving t).integrable_comp_of_integrable hf).const_mul (K t)
  · have heq (t : ℝ) : (∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure)=
        ‖K t‖*(∫ z, ‖f z‖ ∂planeMeasure) := by
      simp_rw [norm_mul]
      rw [integral_const_mul,integral_verticalTranslation t (fun z => ‖f z‖)]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem verticalConvolution_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (verticalConvolution K f) planeMeasure :=
  (verticalConvolution_joint_integrable K hK hKm f hfm hf).integral_prod_right

theorem verticalConvolution_l1_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    (∫ z, ‖verticalConvolution K f z‖ ∂planeMeasure)≤
      (∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  have hi := verticalConvolution_joint_integrable K hK hKm f hfm hf
  calc
    _ ≤ ∫ z, ∫ t, ‖K t*f (z.1,z.2-t)‖ ∂volume ∂planeMeasure := by
      apply integral_mono (verticalConvolution_integrable K hK hKm f hfm hf).norm
        hi.norm.integral_prod_right
      exact fun z => norm_integral_le_integral_norm _
    _ = ∫ t, ∫ z, ‖K t*f (z.1,z.2-t)‖ ∂planeMeasure ∂volume :=
      integral_integral_swap hi.norm.swap
    _ = _ := by
      simp_rw [norm_mul,integral_const_mul,integral_verticalTranslation _ (fun z => ‖f z‖)]
      rw [integral_mul_const]

theorem verticalConvolution_horizontal_support (K : ℝ → ℂ) (f : ℝ×ℝ → ℂ)
    (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → verticalConvolution K f z=0 := by
  intro z hz
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun t => by
    change K t*f (z.1,z.2-t)=0
    rw [hf (z.1,z.2-t) hz,mul_zero]

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

theorem binSquareStep_nonneg (x : ℝ) : 0≤binSquareStep x := sq_nonneg _

theorem binSquareStep_le_one (x : ℝ) : binSquareStep x≤1 := by
  exact Real.sin_sq_le_one _

theorem verticalBinProfile_sum_norm_sq_le (x : ℝ) (N : ℕ) :
    (∑ n∈Finset.range N, ‖verticalBinProfile (x-(n:ℝ))‖^2)≤1 := by
  have hn (y : ℝ) : ‖verticalBinProfile y‖^2=verticalBinProfileReal y^2 := by
    simp only [verticalBinProfile_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp_rw [hn]
  rw [verticalBinProfileReal_sum_sq]
  exact (sub_le_self _ (binSquareStep_nonneg _)).trans (binSquareStep_le_one _)

theorem verticalBinWindow_sum_norm_sq_le (K : ℕ) (W : ℝ) (hW : 0<W)
    (eta : ℝ) (I : Finset ℕ) (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ‖verticalBinWindow K W n eta‖^2)≤1 := by
  calc
    _ ≤ ∑ n∈Finset.range (2*K+1), ‖verticalBinWindow K W n eta‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => sq_nonneg _)
    _ ≤ 1 := by
      simp_rw [verticalBinWindow_apply K W hW]
      exact verticalBinProfile_sum_norm_sq_le (W*eta+K) (2*K+1)

theorem planar_integral_norm_sq_fourier (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure)=∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := planar_integral_inner_fourier f f
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change (∫ omega, ((‖planarFourier f omega‖^2 : ℝ) : ℂ) ∂planeMeasure)=
    (∫ z, ((‖f z‖^2 : ℝ) : ℂ) ∂planeMeasure) at h
  simp only [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem verticalBin_schwartz_energy_le (f : SchwartzMap (ℝ×ℝ) ℂ)
    (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ) (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ∫ z, ‖schwartzVerticalProjection verticalBinProfile W
      (verticalBinCenter K W n) f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  have hp (n : ℕ) := planar_integral_norm_sq_fourier
    (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f)
  have hpi (n : ℕ) : Integrable (fun omega =>
      ‖planarFourier (schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter K W n) f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter K W n) f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ n∈I, ∫ omega, ‖planarFourier (schwartzVerticalProjection
        verticalBinProfile W (verticalBinCenter K W n) f) omega‖^2 ∂planeMeasure := by
      exact Finset.sum_congr rfl (fun n _ => (hp n).symm)
    _ = ∫ omega, ∑ n∈I, ‖planarFourier (schwartzVerticalProjection
        verticalBinProfile W (verticalBinCenter K W n) f) omega‖^2 ∂planeMeasure :=
      (integral_finsetSum I (fun n _ => hpi n)).symm
    _ ≤ ∫ omega, ‖planarFourier f omega‖^2 ∂planeMeasure := by
      apply integral_mono (integrable_finsetSum I (fun n _ => hpi n))
      · simpa only [planarFourierSchwartz_apply] using
          ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
      · intro omega
        simp only [schwartzVerticalProjection_fourier,norm_mul,mul_pow]
        rw [←Finset.sum_mul]
        exact mul_le_of_le_one_left (sq_nonneg _) (verticalBinWindow_sum_norm_sq_le
          K W hW omega.2 I hI)
    _ = _ := planar_integral_norm_sq_fourier f

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinLpEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite bin square-function bound on the actual L2 quotient. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBinLp_continuous (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) :
    Continuous (verticalBinLp K W hW n) :=
  verticalConvolutionLp_continuous _
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable

theorem verticalBinLp_schwartz (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalBinLp K W hW n (f.toLp 2 planeMeasure)=
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f).toLp 2
        planeMeasure := by
  apply Lp.ext
  have hi := verticalConvolutionLp_toLp
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)
  change verticalBinLp K W hW n (f.toLp 2 planeMeasure)=_ at hi
  rw [hi]
  have hmem := (verticalConvolution_energy_bound
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)).1
  filter_upwards [MemLp.coeFn_toLp hmem,
    (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f).coeFn_toLp
      2 planeMeasure] with z hz hz'
  rw [hz,hz',schwartzVerticalProjection_eq_convolution _ W _ hW]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BoundedFrequencyMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded measurable frequency symbol can be paired with an L1 test
function. This justifies finite recombination before the uniform estimates. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem variableFrequencyMultiplier_measurable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (variableFrequencyMultiplier m f) := by
  have hp : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (Real.fourierChar (p.1.1*p.2.1+p.1.2*p.2.2):ℂ)) := by fun_prop
  have hF : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => planarFourier f p.2) := by
    have heq : (planarFourierSchwartz f : ℝ×ℝ → ℂ)=planarFourier f :=
      funext (planarFourierSchwartz_apply f)
    exact (heq ▸ (planarFourierSchwartz f).continuous.measurable).comp measurable_snd
  exact ((hp.mul (hm.mul hF)).stronglyMeasurable.integral_prod_right').measurable

theorem variableFrequencyMultiplier_bound (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    ‖variableFrequencyMultiplier m f z‖≤C*∫ omega, ‖planarFourier f omega‖ ∂planeMeasure := by
  have h := norm_integral_le_of_norm_le ((planarFourier_integrable f).norm.const_mul C)
    (Filter.Eventually.of_forall (fun omega => show
      ‖Real.fourierChar (z.1*omega.1+z.2*omega.2) • (m (z,omega)*planarFourier f omega)‖≤
      C*‖planarFourier f omega‖ from by
        rw [Circle.norm_smul,norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound z omega) (norm_nonneg _)))
  simpa only [variableFrequencyMultiplier,planeMeasure,integral_const_mul] using h

theorem variableFrequencyMultiplier_pairing_integrable (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ)
    (hm : Measurable m) (C : ℝ) (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    Integrable (fun z => variableFrequencyMultiplier m f z*star (g z)) planeMeasure := by
  have hmeas := (variableFrequencyMultiplier_measurable m hm f).aestronglyMeasurable (μ:=planeMeasure)
  apply (hg.norm.const_mul (C*∫ omega, ‖planarFourier f omega‖ ∂planeMeasure)).mono'
    (hmeas.mul hg.aestronglyMeasurable.star)
  filter_upwards [] with z
  change ‖variableFrequencyMultiplier m f z*star (g z)‖≤_
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (variableFrequencyMultiplier_bound m C hbound f z) (norm_nonneg _)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_L1MultiplierLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite input and test reconstruction for frequency multipliers
with an integrable envelope. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_finset_sum_l1 {ι : Type*} (I : Finset ι)
    (f : ι → (ℝ×ℝ) → ℂ) (hf : ∀ i∈I, Integrable (f i) planeMeasure) (omega : ℝ×ℝ) :
    planarFourier (fun z => ∑ i∈I, f i z) omega=∑ i∈I, planarFourier (f i) omega := by
  have hi (i : ι) (hi : i∈I) : Integrable (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2)) • f i z) planeMeasure := by
    apply (hf i hi).norm.mono'
      ((show Continuous (fun z : ℝ×ℝ => Real.fourierChar (-(z.1*omega.1+z.2*omega.2))) by
        fun_prop).aestronglyMeasurable.smul (hf i hi).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => le_of_eq (Circle.norm_smul _ _))
  unfold planarFourier
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum I hi

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical reconstruction and plateau removal for the finite vertical bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_schwartz_sum {ι : Type*} (I : Finset ι)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (show SchwartzMap (ℝ×ℝ) ℂ from ∑ i∈I, f i) omega=∑ i∈I, planarFourier (f i) omega := by
  have h := planarFourier_finset_sum_l1 I (fun i => f i)
    (fun i _ => (f i).integrable) omega
  have heq : (⇑(∑ i∈I, f i) : (ℝ×ℝ) → ℂ)=(fun z => ∑ i∈I, f i z) := by
    funext z
    simp only [sum_apply]
  rw [heq]
  exact h

theorem verticalBin_schwartz_reconstruction (f : SchwartzMap (ℝ×ℝ) ℂ)
    (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hc : 0 < c)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) :
    (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      schwartzVerticalProjection verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n) f))=f := by
  apply planar_schwartz_ext_fourier
  intro omega
  rw [planarFourier_schwartz_sum]
  simp_rw [schwartzVerticalProjection_fourier]
  by_cases hf : planarFourier f omega=0
  · simp only [hf,mul_zero,Finset.sum_const_zero]
  · obtain ⟨hlo,hhi⟩ := hband omega hf
    have hpart := positiveBand_bin_partition w W c C omega.2 hw hW hc hlo hhi
    change (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      verticalBinWindow ⌈C*W/w⌉₊ W n omega.2 *
        (verticalBinWindow ⌈C*W/w⌉₊ W n omega.2 * planarFourier f omega))=planarFourier f omega
    simp_rw [←mul_assoc,←sq]
    rw [←Finset.sum_mul,hpart,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Self-adjointness of the real vertical bin cutoffs, first on Schwartz
functions and then on the full L2 quotient. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBin_schwartz_adjoint (W center : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, inner ℂ (schwartzVerticalProjection verticalBinProfile W center f z) (g z) ∂planeMeasure)=
      ∫ z, inner ℂ (f z) (schwartzVerticalProjection verticalBinProfile W center g z) ∂planeMeasure := by
  rw [←planar_integral_inner_fourier,←planar_integral_inner_fourier]
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [schwartzVerticalProjection_fourier]
  change inner ℂ (verticalBinProfile (W*(omega.2-center)) • planarFourier f omega)
      (planarFourier g omega)=
    inner ℂ (planarFourier f omega)
      (verticalBinProfile (W*(omega.2-center)) • planarFourier g omega)
  rw [inner_smul_left,inner_smul_right]
  simp only [starRingEnd_apply,verticalBinProfile_real]

theorem verticalBinLp_adjoint (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f g : Lp ℂ 2 planeMeasure) :
    inner ℂ (verticalBinLp K W hW n f) g=inner ℂ f (verticalBinLp K W hW n g) := by
  let P := fun f : Lp ℂ 2 planeMeasure =>
    ∀ g : Lp ℂ 2 planeMeasure,
      inner ℂ (verticalBinLp K W hW n f) g=inner ℂ f (verticalBinLp K W hW n g)
  have hd := SchwartzMap.denseRange_toLpCLM (E:=ℝ×ℝ) (F:=ℂ) (μ:=planeMeasure)
    (by norm_num : (2:ℝ≥0∞)≠⊤)
  have h : P f := by
    apply DenseRange.induction_on (p:=P) hd f
    · simp only [P,Set.ofPred_forall]
      apply isClosed_iInter
      intro g
      exact isClosed_eq ((verticalBinLp_continuous K W hW n).inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro f0
      change ∀ g : Lp ℂ 2 planeMeasure, _
      intro g0
      apply DenseRange.induction_on (p:=fun g : Lp ℂ 2 planeMeasure =>
        inner ℂ (verticalBinLp K W hW n (f0.toLp 2 planeMeasure)) g=
          inner ℂ (f0.toLp 2 planeMeasure) (verticalBinLp K W hW n g)) hd g0
      · exact isClosed_eq (continuous_const.inner continuous_id)
          (continuous_const.inner (verticalBinLp_continuous K W hW n))
      · intro g1
        simp only [SchwartzMap.toLpCLM_apply,verticalBinLp_schwartz,
          SchwartzMap.inner_toL2_toL2_eq]
        exact verticalBin_schwartz_adjoint W (verticalBinCenter K W n) f0 g1
  exact h g

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PhysicalBinAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bin adjoint identity for the actual physical convolution pairings. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem physicalBin_adjoint (J : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    (∫ z, verticalConvolution (verticalProfileKernel verticalBinProfile W
        (verticalBinCenter J W n)) f z*star (g z) ∂planeMeasure)=
      ∫ z, f z*star (verticalConvolution (verticalProfileKernel verticalBinProfile W
        (verticalBinCenter J W n)) g z) ∂planeMeasure := by
  let K := verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)
  have hKi : Integrable K := verticalProfileKernel_integrable _ W _ hW
  have hKm : Measurable K := (verticalProfileKernel_continuous _ W _).measurable
  have h := verticalBinLp_adjoint J W hW n (hg.toLp g) (hf.toLp f)
  change inner ℂ (verticalConvolutionLp K hKi hKm (hg.toLp g)) (hf.toLp f)=
    inner ℂ (hg.toLp g) (verticalConvolutionLp K hKi hKm (hf.toLp f)) at h
  rw [verticalConvolutionLp_toLp K hKi hKm g hgm hg,
    verticalConvolutionLp_toLp K hKi hKm f hfm hf,
    memLp_inner_integral,memLp_inner_integral] at h
  simpa only [K,RCLike.inner_apply,starRingEnd_apply,mul_comm] using h.symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTimeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source cutoff beats the enlarged width and every fixed polynomial. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

/-- The two exponents are exactly the manuscript's `0.9` and `0.97`.
This is the numerical small-time input to compact-witness transfer. -/
theorem eventually_short_time_decay (p : ℝ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,
      2 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 1 / 2 := by
  have hlog := (isLittleO_log_rpow_atTop (r := 97 / 100) (by norm_num)).const_mul_left p
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 100)).eventually_ge_atTop 3,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 97 / 100)).eventually_ge_atTop
      (3 * |Real.log (4 * C)|),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 3)] with L hL hgap hconstant hlogL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr : 0 ≤ L ^ (97 / 100 : ℝ) := Real.rpow_nonneg hL0.le _
  have hs : 0 ≤ L ^ (9 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  simp only [Real.norm_eq_abs, abs_of_nonneg hr] at hlogL
  have hpower : L ^ (97 / 100 : ℝ) = L ^ (9 / 10 : ℝ) * L ^ (7 / 100 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hslow : 3 * L ^ (9 / 10 : ℝ) ≤ L ^ (97 / 100 : ℝ) := by
    rw [hpower]
    nlinarith [mul_le_mul_of_nonneg_left hgap hs]
  have hexponent : Real.log (4 * C) + Real.log L * p +
      (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 0 := by
    have hlogabs := le_abs_self (p * Real.log L)
    have hcabs := le_abs_self (Real.log (4 * C))
    nlinarith
  have hfour : 4 * C * L ^ p * Real.exp (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ)) ≤ 1 := by
    calc
      _ = Real.exp (Real.log (4 * C) + Real.log L * p +
          (L ^ (9 / 10 : ℝ) - L ^ (97 / 100 : ℝ))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity : 0 < 4 * C),
          Real.rpow_def_of_pos hL0]
      _ ≤ 1 := Real.exp_le_one_iff.mpr hexponent
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BinErrorParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's actual width and time scales absorb the cubic
width loss in the squared total bin error. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_cubic_width_short_time (D : ℝ) (hD : 0≤D) :
    ∀ᶠ L : ℝ in atTop, ∀ m tau : ℝ, 0 ≤ m →
      m≤2*Real.exp (L^(9/10:ℝ)) → 0≤tau →
      tau≤Real.exp (-(L^(97/100:ℝ))) → D*m^3*tau^2≤L^(-40:ℝ) := by
  have hconstant : 0<4*(D+1) := by linarith
  filter_upwards [eventually_short_time_decay 40 hconstant,
    eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/100)).eventually_ge_atTop 2]
    with L hsmall hL hgap m tau hm hmb ht htb
  have hLp : 0<L := zero_lt_one.trans_le hL
  let a := L^(9/10:ℝ)
  let b := L^(97/100:ℝ)
  have hab : 2*a≤b := by
    have heq : b=a*L^(7/100:ℝ) := by
      dsimp only [a,b]
      rw [←Real.rpow_add hLp]
      norm_num
    rw [heq]
    nlinarith [Real.rpow_nonneg hLp.le (9/10:ℝ)]
  have hexp : (Real.exp a)^3*(Real.exp (-b))^2=Real.exp (3*a-2*b) := by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  have hdec : Real.exp (3*a-2*b)≤Real.exp (a-b) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnumeric : 8*D*Real.exp (a-b)≤L^(-40:ℝ) := by
    have hpow : 0<L^(40:ℝ) := Real.rpow_pos_of_pos hLp _
    have hh : (8*D*Real.exp (a-b))*L^(40:ℝ)≤1 := by
      dsimp only [a,b]
      have hnonneg : 0≤L^(40:ℝ)*Real.exp (L^(9/10:ℝ)-L^(97/100:ℝ)) := by positivity
      nlinarith only [hsmall,hnonneg]
    rw [Real.rpow_neg hLp.le,←one_div]
    exact (le_div_iff₀ hpow).2 hh
  calc
    D*m^3*tau^2 ≤ D*(2*Real.exp a)^3*(Real.exp (-b))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm hmb 3) hD)
        (pow_le_pow_left₀ ht htb 2) (sq_nonneg _) (by positivity)
    _ = 8*D*Real.exp (3*a-2*b) := by
      calc
        _ = 8*D*((Real.exp a)^3*(Real.exp (-b))^2) := by ring
        _ = _ := by rw [hexp]
    _ ≤ 8*D*Real.exp (a-b) := mul_le_mul_of_nonneg_left hdec (by positivity)
    _ ≤ _ := hnumeric

end LipschitzHilbert

end

end OAI
end

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalKernelMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second absolute moment of a modulated bin kernel has exactly the
square of its physical width. The carrier does not affect it. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_second_absolute_moment_integrable (K : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => t^2*‖K t‖) := by
  simpa only [Real.norm_eq_abs,sq_abs] using K.integrable_pow_mul volume 2

theorem modulatedTimeKernel_moment2_pointwise (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    t^2*‖modulatedTimeKernel K W center t‖=W*((t/W)^2*‖K (t/W)‖) := by
  rw [modulatedTimeKernel_norm K W center t hW]
  field_simp

theorem modulatedTimeKernel_moment2_integrable (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Integrable (fun t => t^2*‖modulatedTimeKernel K W center t‖) := by
  have hi := ((schwartz_second_absolute_moment_integrable K).comp_mul_right' (inv_ne_zero hW.ne')).const_mul W
  apply hi.congr
  filter_upwards [] with t
  simpa only [div_eq_mul_inv] using (modulatedTimeKernel_moment2_pointwise K W center t hW).symm

theorem modulatedTimeKernel_moment2 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, t^2*‖modulatedTimeKernel K W center t‖)=W^2*(∫ t, t^2*‖K t‖) := by
  simp_rw [modulatedTimeKernel_moment2_pointwise K W center _ hW]
  rw [integral_const_mul,
    Measure.integral_comp_div (fun t => t^2*‖K t‖) W,abs_of_pos hW,smul_eq_mul]
  ring

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

theorem schwartz_first_absolute_moment_integrable (k : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => |t| *‖k t‖) := by
  simpa only [pow_one,Real.norm_eq_abs] using k.integrable_pow_mul volume 1

theorem scaledTimeKernel_moment1_pointwise (k : ℝ → ℂ) (l t : ℝ) (hl : 0<l) :
    |t| *‖scaledTimeKernel k l t‖=|t/l| *‖k (t/l)‖ := by
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hl.le,abs_div,abs_of_pos hl]
  ring

theorem scaledTimeKernel_moment1_integrable (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    Integrable (fun t => |t| *‖scaledTimeKernel k l t‖) := by
  have hi := (schwartz_first_absolute_moment_integrable k).comp_mul_right' (inv_ne_zero hl.ne')
  apply hi.congr
  filter_upwards [] with t
  simpa only [div_eq_mul_inv] using (scaledTimeKernel_moment1_pointwise k l t hl).symm

theorem scaledTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    (∫ t, |t| *‖scaledTimeKernel k l t‖)=l*(∫ t, |t| *‖k t‖) := by
  simp_rw [scaledTimeKernel_moment1_pointwise k l _ hl]
  rw [Measure.integral_comp_div (fun t => |t| *‖k t‖) l,abs_of_pos hl,smul_eq_mul]

theorem finiteTimeKernel_measurable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ) :
    Measurable (finiteTimeKernel k N topLength) := by
  unfold finiteTimeKernel scaledTimeKernel
  fun_prop

theorem finiteTimeKernel_integrable (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) : Integrable (finiteTimeKernel k N topLength) := by
  exact integrable_finsetSum _ (fun j _ => scaledTimeKernel_integrable k k.integrable _
    (ne_of_gt (div_pos htop (pow_pos (by norm_num) j.val))))

theorem finiteTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (N : ℕ) (topLength : ℝ)
    (htop : 0<topLength) :
    Integrable (fun t => |t| *‖finiteTimeKernel k N topLength t‖) ∧
      (∫ t, |t| *‖finiteTimeKernel k N topLength t‖)≤
        2*topLength*(∫ t, |t| *‖k t‖) := by
  have hl (j : Fin N) : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  have hsum : Integrable (fun t => ∑ j : Fin N,
      |t| *‖scaledTimeKernel k (topLength/(2:ℝ)^j.val) t‖) :=
    integrable_finsetSum _ (fun j _ => scaledTimeKernel_moment1_integrable k _ (hl j))
  have hp (t : ℝ) : |t| *‖finiteTimeKernel k N topLength t‖≤
      ∑ j : Fin N, |t| *‖scaledTimeKernel k (topLength/(2:ℝ)^j.val) t‖ := by
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
  have hi : Integrable (fun t => |t| *‖finiteTimeKernel k N topLength t‖) := by
    apply hsum.mono'
      (((show Continuous (fun t : ℝ => |t|) by fun_prop).measurable.mul
        (finiteTimeKernel_measurable k N topLength).norm).aestronglyMeasurable)
    filter_upwards [] with t
    change ‖|t| *‖finiteTimeKernel k N topLength t‖‖≤_
    simpa only [Real.norm_of_nonneg (mul_nonneg (abs_nonneg t) (norm_nonneg _))] using hp t
  have hlength : (∑ j : Fin N, topLength/(2:ℝ)^j.val)≤2*topLength := by
    have heq : (∑ j : Fin N, topLength/(2:ℝ)^j.val)=
        topLength*(∑ j : Fin N, (1/2:ℝ)^j.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_eq_mul_inv,one_mul,inv_pow]
    rw [heq,Fin.sum_univ_eq_sum_range]
    nlinarith only [mul_le_mul_of_nonneg_left (sum_half_powers_le_two N) htop.le]
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ∑ j : Fin N, |t| *‖scaledTimeKernel k (topLength/(2:ℝ)^j.val) t‖ :=
      integral_mono hi hsum hp
    _ = (∑ j : Fin N, topLength/(2:ℝ)^j.val)*(∫ t, |t| *‖k t‖) := by
      rw [integral_finsetSum _ (fun j _ => scaledTimeKernel_moment1_integrable k _ (hl j))]
      simp_rw [scaledTimeKernel_moment1 k _ (hl _)]
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hlength
      (integral_nonneg fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _))

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSecantEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical fundamental theorem of calculus in the quadratic form
used to compare the two orders of convolution and sampling. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSchwartzDeriv_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    verticalSchwartzDeriv f z=fderiv ℝ f z (0,1) := rfl

theorem verticalPath_hasDerivAt (f : SchwartzMap (ℝ×ℝ) ℂ) (x y delta theta : ℝ) :
    HasDerivAt (fun a : ℝ => f (x,y+a*delta))
      (delta • verticalSchwartzDeriv f (x,y+theta*delta)) theta := by
  have hp : HasDerivAt (fun a : ℝ => (x,y+a*delta)) (0,delta) theta := by
    simpa using (hasDerivAt_const theta x).prodMk
      ((hasDerivAt_const theta y).add ((hasDerivAt_id theta).mul_const delta))
  have h := (f.hasFDerivAt (x,y+theta*delta)).comp_hasDerivAt theta hp
  have heq : (fderiv ℝ f (x,y+theta*delta)) (0,delta)=
      delta • verticalSchwartzDeriv f (x,y+theta*delta) := by
    rw [verticalSchwartzDeriv_apply]
    have hvec : ((0,delta) : ℝ×ℝ)=delta • ((0,1) : ℝ×ℝ) := by ext <;> simp
    rw [hvec,map_smul]
  simpa only [Function.comp_def,heq] using h

theorem vertical_secant_energy (f : SchwartzMap (ℝ×ℝ) ℂ) (x y0 y1 : ℝ) :
    ‖f (x,y1)-f (x,y0)‖^2≤(y1-y0)^2*
      ∫ theta in (0:ℝ)..1, ‖verticalSchwartzDeriv f (x,y0+theta*(y1-y0))‖^2 := by
  let d := y1-y0
  let H := fun theta : ℝ => verticalSchwartzDeriv f (x,y0+theta*d)
  have hH : Continuous H := (verticalSchwartzDeriv f).continuous.comp (by fun_prop)
  have hi : IntervalIntegrable (fun theta => d • H theta) volume 0 1 :=
    ((continuous_const : Continuous (fun _ : ℝ => d)).smul hH).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _ => verticalPath_hasDerivAt f x y0 d theta) hi
  have heq : f (x,y1)-f (x,y0)=d • ∫ theta in (0:ℝ)..1, H theta := by
    simpa only [zero_mul,add_zero,one_mul,show y0+d=y1 by dsimp [d]; ring,
      intervalIntegral.integral_smul] using hftc.symm
  have hH2 : Integrable (fun theta => ‖H theta‖^2) (volume.restrict (Ioc (0:ℝ) 1)) :=
    (hH.norm.pow 2).intervalIntegrable 0 1 |>.1
  have hc := (weighted_integral_cauchySchwarz (volume.restrict (Ioc (0:ℝ) 1))
    (fun _ => 1) (fun theta => ‖H theta‖) measurable_const hH.measurable.norm
    (fun _ => zero_le_one) (fun _ => norm_nonneg _) (integrable_const 1)
    (by simpa only [one_mul] using hH2)).2
  simp only [one_mul,integral_const,smul_eq_mul,mul_one] at hc
  have hm : (volume.restrict (Ioc (0:ℝ) 1)).real univ=1 := by
    rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc]
    norm_num
  rw [hm,one_mul] at hc
  have hn : ‖∫ theta in (0:ℝ)..1, H theta‖≤∫ theta in Ioc (0:ℝ) 1, ‖H theta‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact norm_integral_le_integral_norm _
  rw [heq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  simp only [intervalIntegral.integral_of_le zero_le_one] at hn ⊢
  apply mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc) (sq_nonneg d)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBernstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical derivative bound used only on the actual finite frequency bins. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSchwartzDeriv_eq (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalSchwartzDeriv f=planarVerticalDerivative f := by
  ext z
  rfl

theorem verticalSchwartzDeriv_fourier (f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (verticalSchwartzDeriv f) omega=
      (2*Real.pi*Complex.I*omega.2)*planarFourier f omega := by
  rw [verticalSchwartzDeriv_eq]
  exact planarFourier_verticalDerivative f omega.1 omega.2

theorem vertical_bernstein_energy (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (_hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    (∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure)≤
      (2*Real.pi*R)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hi (g : SchwartzMap (ℝ×ℝ) ℂ) :
      Integrable (fun omega => ‖planarFourier g omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz g).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have hp (omega : ℝ×ℝ) : ‖planarFourier (verticalSchwartzDeriv f) omega‖^2≤
      (2*Real.pi*R)^2*‖planarFourier f omega‖^2 := by
    rw [verticalSchwartzDeriv_fourier,norm_mul]
    by_cases hf : planarFourier f omega=0
    · simp only [hf,norm_zero,mul_zero,zero_pow (by decide : 2≠0),le_refl]
    · have hc : ‖(2*Real.pi*Complex.I*omega.2 : ℂ)‖=2*Real.pi*|omega.2| := by
        simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
      rw [hc,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left (hband omega hf) (by positivity)
  calc
    _ = ∫ omega, ‖planarFourier (verticalSchwartzDeriv f) omega‖^2 ∂planeMeasure :=
      (planar_integral_norm_sq_fourier _).symm
    _ ≤ ∫ omega, (2*Real.pi*R)^2*‖planarFourier f omega‖^2 ∂planeMeasure :=
      integral_mono (hi _) ((hi f).const_mul _) hp
    _ = _ := by rw [integral_const_mul,planar_integral_norm_sq_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short sampling maps and the interpolation between the two orders of
vertical convolution and directional sampling. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalTranslation_isometry (s : ℝ) : Isometry (verticalTranslation s) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist (z.1,z.2-s) (w.1,w.2-s)=dist z w
  simp only [Prod.dist_eq,Real.dist_eq,sub_sub_sub_cancel_right]

theorem verticalBlend_lipschitz (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (s theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) : LipschitzWith 2 (verticalBlend u s theta) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hz := hu.dist_le_mul z w
  have hs := hu.dist_le_mul (verticalTranslation s z) (verticalTranslation s w)
  rw [(verticalTranslation_isometry s).dist_eq z w] at hs
  rw [Real.dist_eq] at hz hs ⊢
  have hid : verticalBlend u s theta z-verticalBlend u s theta w=
      (1-theta)*(u z-u w)+theta*(u (verticalTranslation s z)-u (verticalTranslation s w)) := by
    unfold verticalBlend
    ring
  rw [hid]
  calc
    _ ≤ |1-theta| *|u z-u w| +|theta| *|u (verticalTranslation s z)-u (verticalTranslation s w)| := by
      simpa only [abs_mul] using abs_add_le ((1-theta)*(u z-u w))
        (theta*(u (verticalTranslation s z)-u (verticalTranslation s w)))
    _ ≤ (1-theta)*(2*dist z w)+theta*(2*dist z w) := by
      rw [abs_of_nonneg (sub_nonneg.mpr h1),abs_of_nonneg h0]
      exact add_le_add (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr h1))
        (mul_le_mul_of_nonneg_left hs h0)
    _ = _ := by norm_num; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalSamplingDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise quadratic comparison of the two sampling orders. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingDifference_energy_pointwise (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (t s : ℝ) (z : ℝ×ℝ) :
    ‖verticalSamplingDifference f u t s z‖^2≤
      (2*|t| *|s|)^2 * ∫ theta in (0:ℝ)..1,
        ‖verticalSchwartzDeriv f (verticalSampling (verticalBlend u s theta) t t s z)‖^2 := by
  have hu' := hu.dist_le_mul z (verticalTranslation s z)
  have hd : dist z (verticalTranslation s z)=|s| := by
    change dist z (z.1,z.2-s)=|s|
    simp only [Prod.dist_eq,Real.dist_eq,sub_self,abs_zero]
    rw [show z.2-(z.2-s)=s by ring,max_eq_right (abs_nonneg s)]
  rw [hd,Real.dist_eq] at hu'
  have hdelta : |(z.2-s-t*u (verticalTranslation s z))-(z.2-s-t*u z)|≤2*|t| *|s| := by
    have heq : (z.2-s-t*u (verticalTranslation s z))-(z.2-s-t*u z)=
        t*(u z-u (verticalTranslation s z)) := by ring
    rw [heq,abs_mul]
    calc
      _ ≤ |t| *(2*|s|) := mul_le_mul_of_nonneg_left hu' (abs_nonneg t)
      _ = _ := by ring
  have hpath (theta : ℝ) :
      (z.1-t,(z.2-s-t*u z)+theta*((z.2-s-t*u (verticalTranslation s z))-(z.2-s-t*u z)))=
        verticalSampling (verticalBlend u s theta) t t s z := by
    ext
    · rfl
    · dsimp [verticalSampling,verticalBlend]
      ring
  have h := vertical_secant_energy f (z.1-t) (z.2-s-t*u z)
    (z.2-s-t*u (verticalTranslation s z))
  simp_rw [hpath] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right
  · have hs := pow_le_pow_left₀ (abs_nonneg _) hdelta 2
    simpa only [sq_abs] using hs
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro theta htheta
    exact sq_nonneg _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalDifferenceEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual L2 error when a vertical translation passes through a short
variable-direction sampling map. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingDifference_energy (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (t s : ℝ) (ht : |t|≤1/4) :
    MemLp (verticalSamplingDifference f u t s) 2 planeMeasure ∧
      (∫ z, ‖verticalSamplingDifference f u t s z‖^2 ∂planeMeasure)≤
        16*t^2*s^2*(∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure) := by
  let mu : Measure ℝ := volume.restrict (Ioc 0 1)
  let H := fun p : ℝ×(ℝ×ℝ) =>
    ‖verticalSchwartzDeriv f (verticalSampling (verticalBlend u s p.1) t t s p.2)‖^2
  let E := ∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure
  have hum := hu.continuous.measurable
  have hdfm := (verticalSchwartzDeriv f).continuous.measurable
  have hHm : Measurable H := by
    dsimp [H,verticalSampling,verticalBlend,verticalTranslation]
    fun_prop
  have hH0 (p) : 0≤H p := sq_nonneg _
  have hs (theta : ℝ) (htheta : theta∈Ioc (0:ℝ) 1) :
      Integrable (fun z => H (theta,z)) planeMeasure ∧
        (∫ z, H (theta,z) ∂planeMeasure)≤4*E := by
    have h := verticalSampling_energy (verticalBlend u s theta)
      (verticalBlend_lipschitz u hu s theta htheta.1.le htheta.2) t t s ht
      (verticalSchwartzDeriv f) hdfm ((verticalSchwartzDeriv f).memLp 2 planeMeasure)
    exact ⟨h.1.integrable_norm_pow (by decide : 2≠0),h.2⟩
  have hIoc : ∀ᵐ theta ∂mu, theta∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hi : Integrable H (mu.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    refine ⟨hIoc.mono (fun theta htheta => (hs theta htheta).1),?_⟩
    apply (integrable_const (4*E)).mono' hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hIoc] with theta htheta
    have heq : (∫ z, ‖H (theta,z)‖ ∂planeMeasure)=∫ z, H (theta,z) ∂planeMeasure := by
      simp only [Real.norm_of_nonneg (hH0 _)]
    rw [heq,Real.norm_of_nonneg (integral_nonneg (fun z => hH0 (theta,z)))]
    exact (hs theta htheta).2
  have hDm : Measurable (verticalSamplingDifference f u t s) := by
    change Measurable (fun z : ℝ×ℝ => f (z.1-t,z.2-s-t*u (z.1,z.2-s))-
      f (z.1-t,z.2-s-t*u z))
    fun_prop
  have hp (z : ℝ×ℝ) : ‖verticalSamplingDifference f u t s z‖^2≤
      (2*|t| *|s|)^2*∫ theta, H (theta,z) ∂mu := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,H,mu] using
      verticalSamplingDifference_energy_pointwise f u hu t s z
  have hdom : Integrable (fun z => (2*|t| *|s|)^2*∫ theta, H (theta,z) ∂mu) planeMeasure :=
    hi.integral_prod_right.const_mul _
  have hDi : Integrable (fun z => ‖verticalSamplingDifference f u t s z‖^2) planeMeasure :=
    hdom.mono' (hDm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp z))
  refine ⟨(memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).2 hDi,?_⟩
  have htotal : (∫ theta, ∫ z, H (theta,z) ∂planeMeasure ∂mu)≤4*E := by
    have hb := integral_mono_ae hi.integral_prod_left (integrable_const (4*E))
      (hIoc.mono (fun theta htheta => (hs theta htheta).2))
    have hmass : mu.real univ=1 := by
      dsimp [mu]
      rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc]
      norm_num
    simpa only [integral_const,hmass,one_smul] using hb
  calc
    _ ≤ ∫ z, (2*|t| *|s|)^2*∫ theta, H (theta,z) ∂mu ∂planeMeasure :=
      integral_mono hDi hdom hp
    _ = (2*|t| *|s|)^2*(∫ theta, ∫ z, H (theta,z) ∂planeMeasure ∂mu) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (2*|t| * |s|)^2*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (theta : ℝ) => H (theta,z)) hi.swap)
    _ ≤ (2*|t| *|s|)^2*(4*E) := mul_le_mul_of_nonneg_left htotal (sq_nonneg _)
    _ = _ := by dsimp only [E]; simp only [mul_pow,sq_abs]; ring

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalCommutatorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative bin/sampling commutator bound from the second absolute
kernel moment and the vertical derivative energy. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingCommutator_energy (K : ℝ → ℂ) (hKm : Measurable K)
    (hK : Integrable K) (hK2 : Integrable (fun s => s^2*‖K s‖))
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (t : ℝ) (ht : |t|≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (verticalSamplingCommutator K u t f) 2 planeMeasure ∧
      (∫ z, ‖verticalSamplingCommutator K u t f z‖^2 ∂planeMeasure)≤
        16*t^2*(∫ s, ‖K s‖)*(∫ s, s^2*‖K s‖)*
          (∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure) := by
  let D := fun p : ℝ×(ℝ×ℝ) => verticalSamplingDifference f u t p.1 p.2
  let E := ∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure
  have hE : 0≤E := integral_nonneg (fun _ => sq_nonneg _)
  have hum := hu.continuous.measurable
  have hDm : Measurable D := by
    change Measurable (fun p : ℝ×(ℝ×ℝ) =>
      f (p.2.1-t,p.2.2-p.1-t*u (p.2.1,p.2.2-p.1))-
        f (p.2.1-t,p.2.2-p.1-t*u p.2))
    fun_prop
  have hs (s : ℝ) := verticalSamplingDifference_energy f u hu t s ht
  have hH : Integrable (fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖D p‖^2)
      (volume.prod planeMeasure) := by
    have hm := (hKm.comp measurable_fst).norm.mul (hDm.norm.pow_const 2)
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun s =>
        ((hs s).1.integrable_norm_pow (by decide : 2≠0)).const_mul ‖K s‖
    · apply (hK2.const_mul (16*t^2*E)).mono'
        hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with s
      change ‖∫ z, ‖‖K s‖*‖D (s,z)‖^2‖ ∂planeMeasure‖≤16*t^2*E*(s^2*‖K s‖)
      have hnonneg : 0≤∫ z, ‖‖K s‖*‖D (s,z)‖^2‖ ∂planeMeasure := integral_nonneg (fun _ => norm_nonneg _)
      rw [Real.norm_of_nonneg hnonneg]
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K s)),Real.norm_of_nonneg (sq_nonneg _)]
      rw [integral_const_mul]
      have hb := mul_le_mul_of_nonneg_left (hs s).2 (norm_nonneg (K s))
      dsimp [D,E] at hb ⊢
      nlinarith only [hb]
  have hCeq : verticalSamplingCommutator K u t f=
      (fun z => ∫ s, K s*D (s,z)) :=
    funext (verticalSamplingCommutator_eq K hK u hum t f)
  have hCm : Measurable (verticalSamplingCommutator K u t f) := by
    rw [hCeq]
    exact ((hKm.comp measurable_fst).mul hDm).stronglyMeasurable.prod_swap.integral_prod_right'.measurable
  have hp : ∀ᵐ z ∂planeMeasure, ‖verticalSamplingCommutator K u t f z‖^2≤
      (∫ s, ‖K s‖)*∫ s, ‖K s‖*‖D (s,z)‖^2 := by
    filter_upwards [hH.prod_left_ae] with z hz
    have hd : Measurable (fun s => ‖D (s,z)‖) := hDm.norm.comp (by fun_prop)
    obtain ⟨hprod,hcs⟩ := weighted_integral_cauchySchwarz volume
      (fun s => ‖K s‖) (fun s => ‖D (s,z)‖) hKm.norm hd
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hK.norm hz
    have hn : ‖verticalSamplingCommutator K u t f z‖≤∫ s, ‖K s‖*‖D (s,z)‖ := by
      rw [hCeq]
      exact norm_integral_le_of_norm_le hprod (Filter.Eventually.of_forall fun s => le_of_eq (norm_mul _ _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hdom := hH.integral_prod_right.const_mul (∫ s, ‖K s‖)
  have hi : Integrable (fun z => ‖verticalSamplingCommutator K u t f z‖^2) planeMeasure :=
    hdom.mono' (hCm.norm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hp] with z hz
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz)
  refine ⟨(memLp_two_iff_integrable_sq_norm hCm.aestronglyMeasurable).2 hi,?_⟩
  have htotal : (∫ s, ∫ z, ‖K s‖*‖D (s,z)‖^2 ∂planeMeasure)≤
      16*t^2*E*(∫ s, s^2*‖K s‖) := by
    rw [←integral_const_mul]
    apply integral_mono hH.integral_prod_left (hK2.const_mul _)
    intro s
    change (∫ z, ‖K s‖*‖D (s,z)‖^2 ∂planeMeasure)≤16*t^2*E*(s^2*‖K s‖)
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (hs s).2 (norm_nonneg (K s))
    dsimp [D,E] at hb ⊢
    nlinarith only [hb]
  calc
    _ ≤ ∫ z, (∫ s, ‖K s‖)*(∫ s, ‖K s‖*‖D (s,z)‖^2) ∂planeMeasure :=
      integral_mono_ae hi hdom hp
    _ = (∫ s, ‖K s‖)*(∫ s, ∫ z, ‖K s‖*‖D (s,z)‖^2 ∂planeMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (∫ s, ‖K s‖)*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (s : ℝ) => ‖K s‖*‖D (s,z)‖^2) hH.swap)
    _ ≤ (∫ s, ‖K s‖)*(16*t^2*E*(∫ s, s^2*‖K s‖)) :=
      mul_le_mul_of_nonneg_left htotal (integral_nonneg (fun _ => norm_nonneg _))
    _ = _ := by dsimp only [E]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalBinCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bin commutator on a vertical frequency band. Its constant
depends only on the fixed profile; its scale dependence is `t² (W R)²`. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfileCommutatorConstant_nonneg (q : SchwartzMap ℝ ℂ) :
    0≤verticalProfileCommutatorConstant q := by
  unfold verticalProfileCommutatorConstant
  positivity

theorem verticalProfileCommutator_energy (q : SchwartzMap ℝ ℂ)
    (W center : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (t : ℝ) (ht : |t|≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    MemLp (verticalSamplingCommutator (verticalProfileKernel q W center) u t f)
      2 planeMeasure ∧
    (∫ z, ‖verticalSamplingCommutator (verticalProfileKernel q W center) u t f z‖^2
        ∂planeMeasure)≤
      verticalProfileCommutatorConstant q*t^2*(W*R)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hK := modulatedTimeKernel_integrable (𝓕⁻ q) W center hW
  have hKm : Measurable (verticalProfileKernel q W center) := by
    unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ q : SchwartzMap ℝ ℂ).continuous.comp
        (by fun_prop)))).measurable
  obtain ⟨hmem,henergy⟩ := verticalSamplingCommutator_energy
    (verticalProfileKernel q W center) hKm hK
    (modulatedTimeKernel_moment2_integrable (𝓕⁻ q) W center hW) u hu t ht f
  refine ⟨hmem, henergy.trans ?_⟩
  have hcoeff : 0≤16*t^2*(∫ s, ‖verticalProfileKernel q W center s‖)*
      (∫ s, s^2*‖verticalProfileKernel q W center s‖) := by positivity
  calc
    _ ≤ (16*t^2*(∫ s, ‖verticalProfileKernel q W center s‖)*
        (∫ s, s^2*‖verticalProfileKernel q W center s‖))*
        ((2*Real.pi*R)^2*(∫ z, ‖f z‖^2 ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left (vertical_bernstein_energy f R hR hband) hcoeff
    _ = _ := by
      unfold verticalProfileKernel
      rw [modulatedTimeKernel_l1 _ W center hW,modulatedTimeKernel_moment2 _ W center hW]
      unfold verticalProfileCommutatorConstant
      ring

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

theorem verticalProfileCommutator_average_energy (q : SchwartzMap ℝ ℂ)
    (W center : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R)
    (K : ℝ → ℂ) (hKm : Measurable K) (hK1 : Integrable (fun t => |t| *‖K t‖)) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then
      K t*verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0)
        2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then
      K t*verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0‖^2
        ∂planeMeasure)≤
      (∫ t, |t| *‖K t‖)^2*verticalProfileCommutatorConstant q*(W*R)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hqm : Measurable (verticalProfileKernel q W center) := by
    unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((FourierTransform.fourierInv q : SchwartzMap ℝ ℂ).continuous.comp
        (by fun_prop)))).measurable
  have hqi := modulatedTimeKernel_integrable (FourierTransform.fourierInv q) W center hW
  let B := verticalProfileCommutatorConstant q*(W*R)^2*
    (∫ z, ‖f z‖^2 ∂planeMeasure)
  have hB : 0≤B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (verticalProfileCommutatorConstant_nonneg q) (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  have h := shortTimeAverage_energy K hKm hK1
    (fun p => verticalSamplingCommutator (verticalProfileKernel q W center) u p.1 f p.2)
    (verticalSamplingCommutator_joint_measurable _ hqm hqi u hu.continuous.measurable f)
    B hB (fun t ht => (verticalProfileCommutator_energy q W center hW u hu t ht f R hR hband).1)
    (fun t ht => by
      have he := (verticalProfileCommutator_energy q W center hW u hu t ht f R hR hband).2
      convert he using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [B]; ring))
  refine ⟨h.1,h.2.trans_eq ?_⟩
  dsimp only [B]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteBinCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated bin commutator for the actual finite dyadic time kernel.
The bound is uniform in the number of scales and in the bin carrier. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem finiteBinCommutator_energy (k q : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength W center : ℝ) (htop : 0<topLength) (hW : 0<W)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    MemLp (fun z => ∫ t, if |t|≤1/4 then finiteTimeKernel k N topLength t*
      verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0)
        2 planeMeasure ∧
    (∫ z, ‖∫ t, if |t|≤1/4 then finiteTimeKernel k N topLength t*
      verticalSamplingCommutator (verticalProfileKernel q W center) u t f z else 0‖^2
        ∂planeMeasure)≤
      4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant q*(topLength*W*R)^2*
        (∫ z, ‖f z‖^2 ∂planeMeasure) := by
  obtain ⟨hKi,hKb⟩ := finiteTimeKernel_moment1 k N topLength htop
  obtain ⟨hmem,he⟩ := verticalProfileCommutator_average_energy q W center hW u hu
    f R hR hband (finiteTimeKernel k N topLength)
    (finiteTimeKernel_measurable k N topLength) hKi
  refine ⟨hmem,he.trans ?_⟩
  have hs := pow_le_pow_left₀
    (integral_nonneg fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _)) hKb 2
  have hconst : 0≤verticalProfileCommutatorConstant q*(W*R)^2*
      (∫ z, ‖f z‖^2 ∂planeMeasure) := by
    exact mul_nonneg (mul_nonneg (verticalProfileCommutatorConstant_nonneg q) (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right hs hconst
  first | (convert hb using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hb.trans (le_of_eq (by ring)))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TotalBinError
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual projected bin commutators. The bin energy estimate
leaves only one factor of the number of bins in the squared error. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem totalBinError_energy (k : SchwartzMap ℝ ℂ) (N J : ℕ)
    (I : Finset ℕ) (hI : I⊆Finset.range (2*J+1))
    (topLength W : ℝ) (htop : 0<topLength) (hW : 0<W)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤R) :
    let E := fun n : I => finiteBinError k verticalBinProfile N topLength W
      (verticalBinCenter J W n) u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)
    MemLp (fun z => ∑ n : I, E n z) 2 planeMeasure ∧
      (∫ z, ‖∑ n : I, E n z‖^2 ∂planeMeasure)≤
        (I.card:ℝ)*(4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
          (topLength*W*R)^2)*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  intro E
  let A := 4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
    (topLength*W*R)^2
  have hA : 0≤A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (verticalProfileCommutatorConstant_nonneg _)) (sq_nonneg _)
  let P := fun n : I => schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f
  have hb (n : I) : ∀ omega, planarFourier (P n) omega≠0 → |omega.2|≤R := by
    intro omega hn
    apply hband omega
    intro hz
    apply hn
    dsimp only [P]
    rw [schwartzVerticalProjection_fourier,hz,mul_zero]
  have he (n : I) : MemLp (E n) 2 planeMeasure ∧
      (∫ z, ‖E n z‖^2 ∂planeMeasure)≤A*(∫ z, ‖P n z‖^2 ∂planeMeasure) :=
    finiteBinCommutator_energy k verticalBinProfile N topLength W
      (verticalBinCenter J W n) htop hW u hu (P n) R hR (hb n)
  refine ⟨?_,?_⟩
  · simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun n _ => (he n).1)
  · have hs := weighted_integral_sum_square planeMeasure E (fun n => (he n).1)
      (fun _ => (1:ℝ)) (fun _ => by norm_num)
    simp only [div_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      Fintype.card_coe] at hs
    have hE : (∑ n : I, ∫ z, ‖E n z‖^2 ∂planeMeasure)≤A*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      calc
        _ ≤ ∑ n : I, A*(∫ z, ‖P n z‖^2 ∂planeMeasure) :=
          Finset.sum_le_sum fun n _ => (he n).2
        _ = A*(∑ n : I, ∫ z, ‖P n z‖^2 ∂planeMeasure) := (Finset.mul_sum ..).symm
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hA
          simpa only [P,Finset.sum_coe_sort I (fun n : ℕ =>
            ∫ z, ‖schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f z‖^2
              ∂planeMeasure)] using verticalBin_schwartz_energy_le f J W hW I hI
    exact hs.trans (by simpa only [mul_assoc,A] using
      mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg I.card))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TotalBinErrorScale
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Substitution of the manuscript's actual bin count and width into the
total commutator error, followed by its small-time decay. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem totalBinErrorCoefficient_nonneg (k : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0<C) :
    0≤totalBinErrorCoefficient k C := by
  unfold totalBinErrorCoefficient
  exact mul_nonneg (by linarith) (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (verticalProfileCommutatorConstant_nonneg _)) (sq_nonneg _))

theorem totalProjectedBinError_energy (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C m : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W)
    (hC : 0<C) (hm : 1 ≤ m) (hWm : W=m*w)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤C/w) :
    MemLp (totalProjectedBinError k N topLength w W c C u f) 2 planeMeasure ∧
      (∫ z, ‖totalProjectedBinError k N topLength w W c C u f z‖^2 ∂planeMeasure)≤
        totalBinErrorCoefficient k C*m^3*topLength^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
  have hI : I⊆Finset.range (2*⌈C*W/w⌉₊+1) := Finset.filter_subset _ _
  obtain ⟨hmem,he⟩ := totalBinError_energy k N ⌈C*W/w⌉₊ I hI topLength W htop hW
    u hu f (C/w) (by positivity) hband
  refine ⟨hmem,he.trans ?_⟩
  have hquot : C*W/w=C*m := by rw [hWm]; field_simp
  have hcard : (I.card:ℝ)≤(2*C+3)*m := by
    have hc := verticalBinLabels_card w W c C hw hW hC.le
    have hc' : (I.card:ℝ)≤2*(C*m)+3 := by
      calc
        _ ≤ 2*(C*W/w)+3 := hc
        _ = _ := by rw [hquot]
    nlinarith
  have hfreq : topLength*W*(C/w)=topLength*m*C := by rw [hWm]; field_simp
  have hnonneg : 0≤4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
      (topLength*W*(C/w))^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (verticalProfileCommutatorConstant_nonneg _)) (sq_nonneg _)
  calc
    _ ≤ ((2*C+3)*m)*(4*(∫ t, |t| *‖k t‖)^2*verticalProfileCommutatorConstant verticalBinProfile*
        (topLength*W*(C/w))^2)*(∫ z, ‖f z‖^2 ∂planeMeasure) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hnonneg)
        (integral_nonneg fun _ => sq_nonneg _)
    _ = _ := by rw [hfreq]; unfold totalBinErrorCoefficient; ring

theorem eventually_totalProjectedBinError (k : SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0<C) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (topLength w W c m : ℝ),
      0<topLength → 0<w → 0<W → 1 ≤ m → W=m*w →
      m≤2*Real.exp (L^(9/10:ℝ)) → topLength≤Real.exp (-(L^(97/100:ℝ))) →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → ∀ (f : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ omega, planarFourier f omega≠0 → |omega.2|≤C/w) →
      (∫ z, ‖totalProjectedBinError k N topLength w W c C u f z‖^2 ∂planeMeasure)≤
        L^(-40:ℝ)*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  filter_upwards [eventually_cubic_width_short_time (totalBinErrorCoefficient k C)
    (totalBinErrorCoefficient_nonneg k C hC)] with L hdec
  intro N topLength w W c m htop hw hW hm hWm hmb htb u hu f hband
  exact (totalProjectedBinError_energy k N topLength w W c C m htop hw hW hC hm hWm
    u hu f hband).2.trans (mul_le_mul_of_nonneg_right
      (hdec m topLength (by linarith) hmb htop.le htb) (integral_nonneg fun _ => sq_nonneg _))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short-time frozen-direction operator and the exact reason it may
replace the full kernel in a pairing on a narrow horizontal strip. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_pairing_eq (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : (ℝ×ℝ) → ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0)
    (z : ℝ×ℝ) :
    shortSlopeOperator K u f z*star (g z)=slopeKernelOperator K u f z*star (g z) := by
  by_cases hg0 : g z=0
  · simp only [hg0,star_zero,mul_zero]
  have hz : z.1∈Icc l r := by
    by_contra h
    exact hg0 (hg z h)
  unfold shortSlopeOperator slopeKernelOperator
  rw [←integral_mul_const,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : |t|≤1/4
  · simp only [ite_eq_left ht]
  · have hnot : z.1-t∉Icc l r := by
      intro h
      apply ht
      apply abs_le.mpr
      constructor <;> linarith [hz.1,hz.2,h.1,h.2]
    rw [ite_eq_right ht,hf _ hnot]
    simp only [mul_zero,zero_mul]

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

theorem finiteActualBinCommutator_eq (k q : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength W center : ℝ) (htop : 0<topLength) (hW : 0<W)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (fun z => verticalConvolution (verticalProfileKernel q W center)
        (shortSlopeOperator (finiteTimeKernel k N topLength) u f) z-
      shortSlopeOperator (finiteTimeKernel k N topLength) u
        (verticalConvolution (verticalProfileKernel q W center) f) z)=
      finiteBinError k q N topLength W center u f := by
  have hqm : Measurable (verticalProfileKernel q W center) := by
    unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((FourierTransform.fourierInv q : SchwartzMap ℝ ℂ).continuous.comp
        (by fun_prop)))).measurable
  funext z
  exact shortSlopeCommutator_eq _ _ hqm
    (modulatedTimeKernel_integrable (FourierTransform.fourierInv q) W center hW)
    (finiteTimeKernel_integrable k N topLength htop) u hum f z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortSlopeLinearity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Schwartz input reconstruction through the short-time operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem slopeKernelOperator_schwartz_sum {ι : Type*} [Fintype ι]
    (K : ℝ → ℂ) (hK : Integrable K) (u : (ℝ×ℝ) → ℝ)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator K u (show SchwartzMap (ℝ×ℝ) ℂ from ∑ n, f n) z=
      ∑ n, slopeKernelOperator K u (f n) z := by
  have hi (n : ι) : Integrable (fun t => K t*f n (z.1-t,z.2-t*u z)) := by
    apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 (f n))).mono'
    · exact hK.aestronglyMeasurable.mul ((f n).continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ (f n) _) (norm_nonneg _)
  unfold slopeKernelOperator
  simp only [sum_apply,Finset.mul_sum]
  exact integral_finsetSum _ (fun n _ => hi n)

theorem shortSlopeOperator_schwartz_sum {ι : Type*} [Fintype ι]
    (K : ℝ → ℂ) (hK : Integrable K) (u : (ℝ×ℝ) → ℝ)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (show SchwartzMap (ℝ×ℝ) ℂ from ∑ n, f n) z=
      ∑ n, shortSlopeOperator K u (f n) z := by
  simp only [shortSlopeOperator_eq_kernel]
  exact slopeKernelOperator_schwartz_sum _ (shortTimeKernel_integrable K hK) u f z

theorem shortSlopeOperator_bin_reconstruction (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hc : 0 < c)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C)
    (z : ℝ×ℝ) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    shortSlopeOperator K u f z=
      ∑ n : I, shortSlopeOperator K u
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
          (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)) z := by
  intro J I
  have hr := verticalBin_schwartz_reconstruction f w W c C hw hW hc hband
  have hr' : (∑ n : I, schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f))=f := by
    exact (Finset.sum_coe_sort I (fun n : ℕ =>
      schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f))).trans hr
  calc
    _ = shortSlopeOperator K u (show SchwartzMap (ℝ×ℝ) ℂ from
        ∑ n : I, schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
          (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)) z :=
      congrArg (fun g : SchwartzMap (ℝ×ℝ) ℂ => shortSlopeOperator K u g z) hr'.symm
    _ = _ := shortSlopeOperator_schwartz_sum K hK u _ z

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ActualBinReconstruction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact bin diagonalization of the actual localized time operator.
The error is the same projected commutator sum whose energy is estimated. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem actualBin_reconstruction (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W) (hc : 0 < c)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C)
    (z : ℝ×ℝ) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    shortSlopeOperator (finiteTimeKernel k N topLength) u f z=
      (∑ n : I, verticalConvolution (verticalProfileKernel verticalBinProfile W
        (verticalBinCenter J W n)) (shortSlopeOperator (finiteTimeKernel k N topLength) u
          (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)) z)-
        totalProjectedBinError k N topLength w W c C u f z := by
  intro J I
  let P := fun n : I => schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f
  let T := finiteTimeKernel k N topLength
  have hr := shortSlopeOperator_bin_reconstruction T (finiteTimeKernel_integrable k N topLength htop)
    u f w W c C hw hW hc hband z
  have he (n : I) : shortSlopeOperator T u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n)) z=
    verticalConvolution (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n))
      (shortSlopeOperator T u (P n)) z-
      finiteBinError k verticalBinProfile N topLength W (verticalBinCenter J W n) u (P n) z := by
    have h := congrFun (finiteActualBinCommutator_eq k verticalBinProfile N topLength W
      (verticalBinCenter J W n) htop hW u hum (P n)) z
    have hp : verticalConvolution (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n))
        (P n)=(schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n) :
          (ℝ×ℝ) → ℂ) := by
      funext x
      exact (schwartzVerticalProjection_eq_convolution _ W _ hW (P n) x).symm
    rw [hp] at h
    change _-shortSlopeOperator T u
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n)) z=_ at h
    linear_combination -h
  calc
    _ = ∑ n : I, shortSlopeOperator T u
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) (P n)) z := hr
    _ = ∑ n : I, (verticalConvolution
        (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n))
          (shortSlopeOperator T u (P n)) z-
        finiteBinError k verticalBinProfile N topLength W (verticalBinCenter J W n) u (P n) z) :=
      Finset.sum_congr rfl (fun n _ => he n)
    _ = _ := by rw [Finset.sum_sub_distrib]; rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ActualBinPairing
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact diagonalization in the bilinear pairing, with the actual error
sum and the same bin projections on the input and test. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem positive_band_abs_bound (f : SchwartzMap (ℝ×ℝ) ℂ) (w c C : ℝ)
    (hw : 0<w) (hc : 0 < c)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) :
    ∀ omega, planarFourier f omega≠0 → |omega.2|≤C/w := by
  intro omega h
  obtain ⟨hlo,hhi⟩ := hband omega h
  have hnonneg : 0≤omega.2 := by nlinarith
  rw [abs_of_nonneg hnonneg]
  exact (le_div_iff₀ hw).2 (by nlinarith)

theorem actualBin_pairing (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W)
    (hc : 0 < c) (hC : 0<C) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    (∫ z, shortSlopeOperator (finiteTimeKernel k N topLength) u f z*star (g z) ∂planeMeasure)=
      (∑ n : I, ∫ z, shortSlopeOperator (finiteTimeKernel k N topLength) u
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f) z*
          star (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g z)
            ∂planeMeasure)-
        ∫ z, totalProjectedBinError k N topLength w W c C u f z*star (g z) ∂planeMeasure := by
  intro J I
  let T := finiteTimeKernel k N topLength
  let P := fun n : I => schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f
  let A := fun n : I => shortSlopeOperator T u (P n)
  let Q := fun n : I => verticalConvolution (verticalProfileKernel verticalBinProfile W
    (verticalBinCenter J W n)) (A n)
  have hTi : Integrable T := finiteTimeKernel_integrable k N topLength htop
  have hTm : Measurable T := finiteTimeKernel_measurable k N topLength
  have hA (n : I) : MemLp (A n) 2 planeMeasure :=
    (shortSlopeOperator_energy T hTm hTi u hu (P n) (P n).continuous.measurable
      ((P n).memLp 2 planeMeasure)).1
  have hAm (n : I) : Measurable (A n) :=
    shortSlopeOperator_measurable T hTm u hu.continuous.measurable (P n) (P n).continuous.measurable
  have hQ (n : I) : MemLp (Q n) 2 planeMeasure :=
    (verticalConvolution_energy_bound _ (verticalProfileKernel_integrable _ W _ hW)
      (verticalProfileKernel_continuous _ W _).measurable (A n) (hAm n) (hA n)).1
  have hi (n : I) : Integrable (fun z => Q n z*star (g z)) planeMeasure :=
    (hQ n).integrable_mul (g.memLp 2 planeMeasure).star
  have hI : I⊆Finset.range (2*J+1) := Finset.filter_subset _ _
  have hE : MemLp (totalProjectedBinError k N topLength w W c C u f) 2 planeMeasure :=
    (totalBinError_energy k N J I hI topLength W htop hW u hu f (C/w) (by positivity)
      (positive_band_abs_bound f w c C hw hc hband)).1
  have hie : Integrable (fun z => totalProjectedBinError k N topLength w W c C u f z*
      star (g z)) planeMeasure := hE.integrable_mul (g.memLp 2 planeMeasure).star
  have hp (z : ℝ×ℝ) : shortSlopeOperator T u f z*star (g z)=
      (∑ n : I, Q n z*star (g z))-
        totalProjectedBinError k N topLength w W c C u f z*star (g z) := by
    rw [actualBin_reconstruction k N topLength w W c C htop hw hW hc u
      hu.continuous.measurable f hband z,sub_mul,Finset.sum_mul]
  calc
    _ = ∫ z, (∑ n : I, Q n z*star (g z))-
        totalProjectedBinError k N topLength w W c C u f z*star (g z) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = (∑ n : I, ∫ z, Q n z*star (g z) ∂planeMeasure)-
        ∫ z, totalProjectedBinError k N topLength w W c C u f z*star (g z) ∂planeMeasure := by
      rw [integral_sub (integrable_finsetSum _ (fun n _ => hi n)) hie,
        integral_finsetSum _ (fun n _ => hi n)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      have h := physicalBin_adjoint J W hW n (A n) g (hAm n) g.continuous.measurable
        (hA n) (g.memLp 2 planeMeasure)
      simpa only [←schwartzVerticalProjection_eq_convolution verticalBinProfile W
        (verticalBinCenter J W n) hW g] using h

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

theorem hilbertAnnularSymbol_support (x : ℝ) (hx : hilbertAnnularSymbol x≠0) :
    1/2≤|x| ∧ |x|≤2 := by
  constructor
  · by_contra hn
    have ha := (lt_of_not_ge hn).le
    have ha1 : |x|≤1 := by linarith
    have ha2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    apply hx
    change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
      (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=0
    rw [verticalBinPlateauReal_one x ha1,verticalBinPlateauReal_one (2*x) ha2]
    simp
  · by_contra hn
    have ha : 2≤|x| := (lt_of_not_ge hn).le
    have hz (s : ℝ) (hs : 2≤|s|) : verticalBinPlateauReal s=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hs with hs | hs
      · exact Or.inr hs
      · exact Or.inl (by linarith)
    have ha2 : 2≤|2*x| := by rw [abs_mul]; norm_num; linarith
    apply hx
    change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
      (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=0
    rw [hz x ha,hz (2*x) ha2]
    simp

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortSlopeL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable time-kernel errors have direct mass bounds under short
Lipschitz sampling, sufficient for restricted pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_uniform (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖shortSlopeOperator K u f z‖≤C*(∫ t, ‖K t‖) := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show
      ‖if |t|≤1/4 then K t*f (z.1-t,z.2-t*u z) else 0‖≤C*‖K t‖ from by
      by_cases ht : |t|≤1/4
      · rw [ite_eq_left ht,norm_mul,mul_comm C]
        exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
      · rw [ite_eq_right ht,norm_zero]
        exact mul_nonneg hC (norm_nonneg _)))
  simpa only [shortSlopeOperator,integral_const_mul] using h

theorem shortSlopeOperator_l1 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (shortSlopeOperator K u f) planeMeasure ∧
      (∫ z, ‖shortSlopeOperator K u f z‖ ∂planeMeasure)≤
        4*(∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  let F := fun p : ℝ×(ℝ×ℝ) =>
    if |p.1|≤1/4 then f (p.2.1-p.1,p.2.2-p.1*u p.2) else 0
  have hum := hu.continuous.measurable
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hFm : Measurable F := (hfm.comp (by fun_prop)).ite hs measurable_const
  have hslice (t : ℝ) : Integrable (fun z => ‖F (t,z)‖) planeMeasure ∧
      (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤4*∫ z, ‖f z‖ ∂planeMeasure := by
    by_cases ht : |t|≤1/4
    · simpa only [F,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
        planar_integral_comp_le_four (verticalSampling u t t 0)
          (verticalSampling_measurable u hum t t 0)
          (verticalSampling_antilipschitz u hu t t 0 ht) (fun z => ‖f z‖) hf.norm
          (fun _ => norm_nonneg _)
    · simp only [F,ite_eq_right ht,norm_zero,integral_zero]
      exact ⟨integrable_zero _ _ _,by positivity⟩
  let H := fun p : ℝ×(ℝ×ℝ) => K p.1*F p
  have hHm : Measurable H := (hKm.comp measurable_fst).mul hFm
  have hHi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hslice t).1.mono
          (hFm.comp (by fun_prop)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => by simp)).const_mul (K t)
    · apply (hK.norm.mul_const (4*∫ z, ‖f z‖ ∂planeMeasure)).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖K t*F (t,z)‖ ∂planeMeasure‖≤_
      simp only [norm_mul,integral_const_mul]
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hslice t).2 (norm_nonneg _)
  have heq (z : ℝ×ℝ) : (∫ t, H (t,z))=shortSlopeOperator K u f z := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H,F]
    split_ifs <;> simp
  have hbound (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z‖≤∫ t, ‖H (t,z)‖ := by
    rw [←heq]
    exact norm_integral_le_integral_norm _
  refine ⟨?_,?_⟩
  · simpa only [heq] using hHi.integral_prod_right
  · calc
      _ ≤ ∫ z : ℝ×ℝ, (∫ t : ℝ, ‖H (t,z)‖) ∂planeMeasure :=
        integral_mono (by simpa only [heq] using hHi.integral_prod_right.norm)
          hHi.norm.integral_prod_right hbound
      _ = ∫ t, ∫ z, ‖H (t,z)‖ ∂planeMeasure :=
        integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖H (t,z)‖) hHi.norm.swap
      _ ≤ ∫ t, ‖K t‖*(4*∫ z, ‖f z‖ ∂planeMeasure) := by
        apply integral_mono hHi.norm.integral_prod_left (hK.norm.mul_const _)
        intro t
        simp only [H,norm_mul,integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hslice t).2 (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortKernelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted mass bounds for an integrable short-time kernel error. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortKernel_pairing (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f planeMeasure) (hg : Integrable g planeMeasure)
    (hf1 : ∀ z, ‖f z‖≤1) (hg1 : ∀ z, ‖g z‖≤1) :
    Integrable (fun z => shortSlopeOperator K u f z*star (g z)) planeMeasure ∧
    ‖∫ z, shortSlopeOperator K u f z*star (g z) ∂planeMeasure‖≤
      min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*(∫ t, ‖K t‖) := by
  have hA := shortSlopeOperator_l1 K hKm hK u hu f hfm hf
  have hm := shortSlopeOperator_measurable K hKm u hu.continuous.measurable f hfm
  have hp (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z*star (g z)‖≤‖shortSlopeOperator K u f z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hg1 z)
  have hi := hA.1.norm.mono' (show Measurable (fun z => shortSlopeOperator K u f z*star (g z)) from by fun_prop).aestronglyMeasurable (Filter.Eventually.of_forall hp)
  refine ⟨hi,?_⟩
  rw [min_mul_of_nonneg _ _ (integral_nonneg fun _ => norm_nonneg _)]
  apply le_min
  · calc
      _ ≤ ∫ z, ‖shortSlopeOperator K u f z‖ ∂planeMeasure :=
        norm_integral_le_of_norm_le hA.1.norm (Filter.Eventually.of_forall hp)
      _ ≤ _ := hA.2.trans_eq (by ring)
  · have hp' (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z*star (g z)‖≤
        (∫ t, ‖K t‖)*‖g z‖ := by
      rw [norm_mul,norm_star]
      have hb := shortSlopeOperator_uniform K hK u f 1 (by norm_num) hf1 z
      simp only [one_mul] at hb
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have h := norm_integral_le_of_norm_le (hg.norm.const_mul (∫ t, ‖K t‖))
      (Filter.Eventually.of_forall hp')
    simpa only [integral_const_mul,integral_mul_const,mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelDifferencePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A kernel L1 error controls the actual localized bilinear form by the
smaller of the input and test masses. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem slopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (fun t => K t-J t) u f z=
      slopeKernelOperator K u f z-slopeKernelOperator J u f z := by
  simp only [slopeKernelOperator,sub_mul]
  exact integral_sub (slope_integrand_integrable K hK u f z)
    (slope_integrand_integrable J hJ u f z)

theorem shortSlopeOperator_kernel_sub (K J : ℝ → ℂ) (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator (fun t => K t-J t) u f z=
      shortSlopeOperator K u f z-shortSlopeOperator J u f z := by
  simp only [shortSlopeOperator_eq_kernel]
  have heq : shortTimeKernel (fun t => K t-J t)=
      fun t => shortTimeKernel K t-shortTimeKernel J t := by
    funext t
    unfold shortTimeKernel
    split_ifs <;> simp
  rw [heq]
  exact slopeOperator_kernel_sub _ _ (shortTimeKernel_integrable K hK)
    (shortTimeKernel_integrable J hJ) u f z

theorem kernelDifference_pairing (K J : ℝ → ℂ) (hKm : Measurable K) (hJm : Measurable J)
    (hK : Integrable K) (hJ : Integrable J)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hf1 : ∀ z, ‖f z‖≤1) (hg1 : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖(∫ z, slopeKernelOperator K u f z*star (g z) ∂planeMeasure)-
      (∫ z, slopeKernelOperator J u f z*star (g z) ∂planeMeasure)‖≤
      min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)*
        (∫ t, ‖K t-J t‖) := by
  have hkp := shortKernel_pairing K hKm hK u hu f g f.continuous.measurable
    g.continuous.measurable f.integrable g.integrable hf1 hg1
  have hjp := shortKernel_pairing J hJm hJ u hu f g f.continuous.measurable
    g.continuous.measurable f.integrable g.integrable hf1 hg1
  have hdiff := shortKernel_pairing (fun t => K t-J t) (hKm.sub hJm) (hK.sub hJ) u hu
    f g f.continuous.measurable g.continuous.measurable f.integrable g.integrable hf1 hg1
  have heqK (z : ℝ×ℝ) := shortSlopeOperator_pairing_eq K u f g l r hwidth hfstrip hgstrip z
  have heqJ (z : ℝ×ℝ) := shortSlopeOperator_pairing_eq J u f g l r hwidth hfstrip hgstrip z
  simp_rw [←heqK,←heqJ]
  rw [←integral_sub hkp.1 hjp.1]
  have heq (z : ℝ×ℝ) : shortSlopeOperator K u f z*star (g z)-
      shortSlopeOperator J u f z*star (g z)=
        shortSlopeOperator (fun t => K t-J t) u f z*star (g z) := by
    rw [shortSlopeOperator_kernel_sub K J hK hJ]
    ring
  simpa only [heq] using hdiff.2

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

theorem hilbertArbitraryEndpoint_pairing :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 →
        (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖(∫ z, slopeKernelOperator (sharpTimeKernel epsilon R) u f z*star (g z) ∂planeMeasure)-
        (∫ z, slopeKernelOperator (finiteTimeKernel hilbertTimeKernel N (R/2))
          u f z*star (g z) ∂planeMeasure)‖≤
        B*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  refine ⟨B,hB,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi,herror,hbound⟩ := hkernel epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  have hJ := finiteTimeKernel_integrable hilbertTimeKernel N (R/2) (by positivity)
  have hK : Integrable (sharpTimeKernel epsilon R) := by
    apply (herror.add hJ).congr
    filter_upwards [] with t
    simp only [Pi.add_apply,sub_add_cancel]
  have h := kernelDifference_pairing (sharpTimeKernel epsilon R)
    (finiteTimeKernel hilbertTimeKernel N (R/2)) (sharpTimeKernel_measurable _ _)
    (finiteTimeKernel_measurable _ _ _) hK hJ u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  exact h.trans ((mul_le_mul_of_nonneg_left hbound
    (le_min (by positivity) (integral_nonneg fun _ => norm_nonneg _))).trans_eq (mul_comm _ _))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalHilbertLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini transfers the precisely stated one-dimensional Hilbert input
to the horizontal remainder on the actual plane. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem horizontalTruncatedHilbert_slice (r R : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    horizontalTruncatedHilbert r R f (x,y)=
      oneDimensionalTruncatedHilbert r R (planarSchwartzSlice f y 0) x := by
  simp only [horizontalTruncatedHilbert,slopeKernelOperator,oneDimensionalTruncatedHilbert,
    planarSchwartzSlice_apply,mul_zero,sub_zero,zero_mul,add_zero]

theorem horizontalTruncatedHilbert_measurable (r R : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (horizontalTruncatedHilbert r R f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ =>
      sharpTimeKernel r R p.2*f (p.1.1-p.2,p.1.2)) :=
    ((sharpTimeKernel_measurable r R).comp measurable_snd).mul
      (f.continuous.measurable.comp (by fun_prop))
  have hmi : Measurable (fun z : ℝ×ℝ => ∫ t : ℝ,
      sharpTimeKernel r R t*f (z.1-t,z.2)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  change Measurable (fun z => horizontalTruncatedHilbert r R f z)
  simpa only [horizontalTruncatedHilbert,slopeKernelOperator,mul_zero,sub_zero] using hmi

theorem horizontalHilbert_power_bound (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, p=3/2 ∨ p=4 →
      ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        Integrable (fun z => ‖horizontalTruncatedHilbert r R f z‖^p) planeMeasure ∧
        (∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure)≤
          C^p*(∫ z, ‖f z‖^p ∂planeMeasure) := by
  obtain ⟨C,hC,hbound⟩ := hH
  refine ⟨C,hC,?_⟩
  intro p hp r R hr hrR f
  have hp0 : 0<p := by rcases hp with h | h <;> rw [h] <;> norm_num
  let H := fun z : ℝ×ℝ => ‖horizontalTruncatedHilbert r R f (z.2,z.1)‖^p
  have hHm : Measurable H :=
    ((horizontalTruncatedHilbert_measurable r R f).comp measurable_swap).norm.pow_const p
  have hH0 (z) : 0≤H z := Real.rpow_nonneg (norm_nonneg _) _
  have hf : Integrable (fun z => ‖f z‖^p) planeMeasure := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (f.memLp (ENNReal.ofReal p) planeMeasure).integrable_norm_rpow
        (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hp0) (by simp)
  have hslice (y : ℝ) : Integrable (fun x => H (y,x)) ∧
      (∫ x, H (y,x))≤C^p*(∫ x, ‖f (x,y)‖^p) := by
    simpa only [H,horizontalTruncatedHilbert_slice,planarSchwartzSlice_apply,
      zero_mul,add_zero] using hbound p hp r R hr hrR (planarSchwartzSlice f y 0)
  have hHi : Integrable H (volume.prod volume) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun y => (hslice y).1
    · apply (hf.swap.integral_prod_left.const_mul (C^p)).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with y
      simp only [Real.norm_of_nonneg (hH0 _)]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => hH0 _)]
      exact (hslice y).2
  have hmain : (∫ z, H z ∂volume.prod volume)≤C^p*(∫ z, ‖f z‖^p ∂planeMeasure) := by
    rw [integral_prod _ hHi]
    calc
      _ ≤ ∫ y, C^p*(∫ x, ‖f (x,y)‖^p) :=
        integral_mono hHi.integral_prod_left (hf.swap.integral_prod_left.const_mul (C^p))
          (fun y => (hslice y).2)
      _ = C^p*(∫ z, ‖f z‖^p ∂planeMeasure) := by
        rw [integral_const_mul]
        congr 1
        exact (integral_prod_symm _ hf).symm
  have hi : Integrable (fun z => ‖horizontalTruncatedHilbert r R f z‖^p) planeMeasure := by
    simpa only [H,Function.comp_def,Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap,Prod.mk.eta] using hHi.swap
  refine ⟨hi,?_⟩
  have heq : (∫ z, H z ∂volume.prod volume)=
      ∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure := by
    simpa only [H,Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap,Prod.mk.eta] using
      (MeasureTheory.integral_prod_swap (μ := volume) (ν := volume) H).symm
  exact heq ▸ hmain

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarPairingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy--Schwarz in the actual planar integral pairing. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem planar_pairing_energy (f g : (ℝ×ℝ) → ℂ)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    ‖∫ z, f z*star (g z) ∂planeMeasure‖^2≤
      (∫ z, ‖f z‖^2 ∂planeMeasure)*(∫ z, ‖g z‖^2 ∂planeMeasure) := by
  have hpair : (∫ z, f z*star (g z) ∂planeMeasure)=inner ℂ (hg.toLp g) (hf.toLp f) := by
    rw [memLp_inner_integral]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [RCLike.inner_apply,starRingEnd_apply]
  rw [hpair]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜:=ℂ) (hg.toLp g) (hf.toLp f)) 2
  rw [mul_pow,memLp_toL2_norm_sq,memLp_toL2_norm_sq] at h
  simpa only [mul_comm] using h

theorem planar_pairing_bound_of_energy (f g : (ℝ×ℝ) → ℂ)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure)
    (L E : ℝ) (hL : 0<L) (hE : 0≤E)
    (he : (∫ z, ‖f z‖^2 ∂planeMeasure)≤L^(-40:ℝ)*E) :
    ‖∫ z, f z*star (g z) ∂planeMeasure‖≤
      L^(-20:ℝ)*Real.sqrt E*Real.sqrt (∫ z, ‖g z‖^2 ∂planeMeasure) := by
  have hg0 : 0≤∫ z, ‖g z‖^2 ∂planeMeasure := integral_nonneg fun _ => sq_nonneg _
  have hp := (planar_pairing_energy f g hf hg).trans (mul_le_mul_of_nonneg_right he hg0)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hpow : (L^(-20:ℝ))^2=L^(-40:ℝ) := by
    rw [pow_two,←Real.rpow_add hL]
    norm_num
  simpa only [mul_pow,hpow,Real.sq_sqrt hE,Real.sq_sqrt hg0] using hp

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBandL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_measurable (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (annularBandSymbol psi beta l W center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold annularBandSymbol symbolY
  apply Measurable.mul
  · apply psi.continuous.measurable.comp
    fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBinMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The annular symbol with the enlarged bin plateau is exactly the time
kernel acting on the true bin projection. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annularBinMultiplier_eq (psi : SchwartzMap ℝ ℂ) (l W center : ℝ) (hl : 0<l)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 (annularBandSymbol psi verticalBinPlateau l W center u)
      (schwartzVerticalProjection verticalBinProfile W center f) z=
      slopeKernelOperator (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) u
        (schwartzVerticalProjection verticalBinProfile W center f) z := by
  rw [schwartz_frozen_slope_multiplier _
    (scaledTimeKernel_integrable (𝓕⁻ psi : SchwartzMap ℝ ℂ) (𝓕⁻ psi : SchwartzMap ℝ ℂ).integrable
      l hl.ne')]
  have hfour (s : ℝ) : 𝓕 (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) s=psi (l*s) := by
    rw [scaledTimeKernel_fourier _ l hl]
    have heq : (𝓕 (𝓕⁻ psi : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=psi := fourier_fourierInv_eq psi
    exact congrArg (fun q : SchwartzMap ℝ ℂ => q (l*s)) heq
  unfold variableFrequencyMultiplierL1
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [hfour]
  congr 1
  simp only [annularBandSymbol,symbolY,schwartzVerticalProjection_fourier]
  rw [mul_assoc,←mul_assoc (verticalBinPlateau _) (verticalBinProfile _),verticalBinPlateau_mul_profile]

theorem slopeKernelOperator_finiteTimeKernel (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength : ℝ) (htop : 0<topLength) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (finiteTimeKernel k N topLength) u f z=
      ∑ j : Fin N, slopeKernelOperator (scaledTimeKernel k (topLength/(2:ℝ)^j.val)) u f z := by
  have hi (j : Fin N) : Integrable (fun t =>
      scaledTimeKernel k (topLength/(2:ℝ)^j.val) t*f (z.1-t,z.2-t*u z)) := by
    have hk := scaledTimeKernel_integrable k k.integrable (topLength/(2:ℝ)^j.val)
      (ne_of_gt (div_pos htop (pow_pos (by norm_num) _)))
    apply (hk.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact hk.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  unfold slopeKernelOperator finiteTimeKernel
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ (fun j _ => hi j)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularBinPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the original narrow horizontal strip, the actual projected time
pairing equals the finite annular-symbol pairing without a time cutoff. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annularBin_pairing (psi : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (htop : 0<topLength) (hW : 0<W) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0) :
    (∫ z, shortSlopeOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
      (schwartzVerticalProjection verticalBinProfile W center f) z*
        star (schwartzVerticalProjection verticalBinProfile W center g z) ∂planeMeasure)=
      ∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi verticalBinPlateau (topLength/(2:ℝ)^j.val) W center u)
        (schwartzVerticalProjection verticalBinProfile W center f) z*
          star (schwartzVerticalProjection verticalBinProfile W center g z) ∂planeMeasure := by
  let F := schwartzVerticalProjection verticalBinProfile W center f
  let G := schwartzVerticalProjection verticalBinProfile W center g
  let T := finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength
  let M := fun j : Fin N => annularBandSymbol psi verticalBinPlateau
    (topLength/(2:ℝ)^j.val) W center u
  have hlen (j : Fin N) : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  have hFp : ∀ z, z.1∉Icc l r → F z=0 := by
    intro z hz
    rw [schwartzVerticalProjection_eq_convolution _ W center hW]
    exact verticalConvolution_horizontal_support _ f (Icc l r) hf z hz
  have hGp : ∀ z, z.1∉Icc l r → G z=0 := by
    intro z hz
    rw [schwartzVerticalProjection_eq_convolution _ W center hW]
    exact verticalConvolution_horizontal_support _ g (Icc l r) hg z hz
  have hi (j : Fin N) : Integrable (fun z => variableFrequencyMultiplierL1 (M j) F z*star (G z))
      planeMeasure := by
    apply variableFrequencyMultiplier_pairing_integrable (M j)
      (annularBandSymbol_measurable _ _ _ _ _ u hum)
      (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 verticalBinPlateau)
      _ F G G.integrable
    intro z omega
    dsimp only [M,annularBandSymbol]
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _)
      (SchwartzMap.norm_le_seminorm ℝ verticalBinPlateau _) (norm_nonneg _)
      (apply_nonneg _ _)
  have heq (z : ℝ×ℝ) : slopeKernelOperator T u F z=
      ∑ j : Fin N, variableFrequencyMultiplierL1 (M j) F z := by
    rw [slopeKernelOperator_finiteTimeKernel _ N topLength htop]
    exact Finset.sum_congr rfl (fun j _ => (annularBinMultiplier_eq psi
      (topLength/(2:ℝ)^j.val) W center (hlen j) u f z).symm)
  calc
    _ = ∫ z, slopeKernelOperator T u F z*star (G z) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun z =>
        shortSlopeOperator_pairing_eq T u F G l r hwidth hFp hGp z)
    _ = ∫ z, ∑ j : Fin N, variableFrequencyMultiplierL1 (M j) F z*star (G z) ∂planeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [heq,Finset.sum_mul]
    _ = _ := integral_finsetSum _ (fun j _ => hi j)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ActualBandDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the physical localized operator pairing with
the finite diagonal form used by the high-disparity estimate. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem actualBand_pairing_eq_diagonal (psi : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W)
    (hc : 0 < c) (hC : 0<C) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    (∫ z, shortSlopeOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
      u f z*star (g z) ∂planeMeasure)=
      finiteDiagonalBandL1 (N:=N) psi verticalBinPlateau topLength W
        (fun n : I => verticalBinCenter J W n) u
        (fun n z => verticalConvolution
          (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)) f z)
        (verticalBinVector I J W g)-
      ∫ z, totalProjectedBinError (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C u f z*
        star (g z) ∂planeMeasure := by
  intro J I
  rw [actualBin_pairing (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C htop hw hW hc hC u hu f g hband]
  congr 1
  calc
    _ = ∑ n : I, ∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi verticalBinPlateau (topLength/(2:ℝ)^j.val) W
          (verticalBinCenter J W n) u)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f) z*
          star (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g z)
            ∂planeMeasure := by
      apply Finset.sum_congr rfl
      intro n _
      exact annularBin_pairing psi N topLength W (verticalBinCenter J W n) htop hW u
        hu.continuous.measurable f g l r hwidth hf hg
    _ = ∑ j : Fin N, ∑ n : I, ∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi verticalBinPlateau (topLength/(2:ℝ)^j.val) W
          (verticalBinCenter J W n) u)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f) z*
          star (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g z)
            ∂planeMeasure := Finset.sum_comm
    _ = _ := by
      unfold finiteDiagonalBandL1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro n _
      have hpf : (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f :
          (ℝ×ℝ) → ℂ)=verticalConvolution
            (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)) f :=
        funext (schwartzVerticalProjection_eq_convolution _ W _ hW f)
      have hpg : (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g :
          (ℝ×ℝ) → ℂ)=verticalConvolution
            (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)) g :=
        funext (schwartzVerticalProjection_eq_convolution _ W _ hW g)
      change (∫ z, _*star ((schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter J W n) g : (ℝ×ℝ) → ℂ) z) ∂planeMeasure)=_
      rw [hpf,hpg]
      rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ActualBandHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-disparity bound for the localized finite time operator,
combining the diagonal bin estimate and the full commutator error under
the martingale variation and directional maximal hypotheses. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped FourierTransform Topology
namespace LipschitzHilbert.PacketRepresentation

theorem actual_band_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W) ≤ c/2 → c/2≤C →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
      (∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ)) ≤ m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
        (fun z => field (planeCoordinates z)) f z*star (g z) ∂planeMeasure‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,A,Lbase,hD,hA,hbase,hmain⟩ := band_projected_high hVariation hLL psi c C a M hc hC ha hM hpsi
  obtain ⟨Lerr,herr⟩ := eventually_atTop.1
    (eventually_totalProjectedBinError (𝓕⁻ psi : SchwartzMap ℝ ℂ) C hC)
  refine ⟨D,A+1,max Lbase Lerr,hD,by linarith,hbase.trans (le_max_left _ _),?_⟩
  intro L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength field hfield hfieldBound
    f g hband F E ratio hF hE hr heq hlog hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip
    hmlo hmhi hWeq
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hLe : Lerr≤L := (le_max_right _ _).trans hL
  have hL16 : 16≤L := hbase.trans hLb
  have hLp : 0<L := by linarith
  have hmone : 1 ≤ m := (Real.one_le_exp (Real.rpow_nonneg hLp.le (9/10:ℝ))).trans hmlo
  have hu : LipschitzWith 2 (fun z : ℝ×ℝ => field (planeCoordinates z)) := by
    simpa only [mul_one] using product_slope_lipschitz field hfield
  have hdiag := hmain L hLb N topLength W w htop hW hw hwW hsmall hcC htime hlength
    field hfield hfieldBound f g f.continuous.measurable g.continuous.measurable
    (f.memLp 2 planeMeasure) (g.memLp 2 planeMeasure) f.integrable g.integrable
    F E ratio hF hE hr heq hlog hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  let error := totalProjectedBinError (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C u f
  have heEnergy : (∫ z, ‖error z‖^2 ∂planeMeasure)≤L^(-40:ℝ)*(∫ z, ‖f z‖^2 ∂planeMeasure) :=
    herr L hLe N topLength w W c m htop hw hW hmone hWeq hmhi htime u hu f
      (positive_band_abs_bound f w c C hw hc hband)
  have heMem : MemLp error 2 planeMeasure :=
    (totalProjectedBinError_energy (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C m
      htop hw hW hC hmone hWeq u hu f (positive_band_abs_bound f w c C hw hc hband)).1
  have hePair := planar_pairing_bound_of_energy error g heMem (g.memLp 2 planeMeasure)
    L (∫ z, ‖f z‖^2 ∂planeMeasure) hLp (integral_nonneg fun _ => sq_nonneg _) heEnergy
  have heBound : ‖∫ z, error z*star (g z) ∂planeMeasure‖≤L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
    calc
      _ ≤ L^(-20:ℝ)*Real.sqrt (∫ z, ‖f z‖^2 ∂planeMeasure)*
          Real.sqrt (∫ z, ‖g z‖^2 ∂planeMeasure) := hePair
      _ ≤ L^(-20:ℝ)*Real.sqrt F*Real.sqrt E := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfE) (by positivity))
          (Real.sqrt_le_sqrt hgE) (Real.sqrt_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L) (by norm_num : (-20:ℝ)≤-19))
          (Real.sqrt_nonneg F)) (Real.sqrt_nonneg E)
  have hwidth : r-l≤1/4 := by linarith
  have hfull : (∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
      u f z*star (g z) ∂planeMeasure)=
      ∫ z, shortSlopeOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
        u f z*star (g z) ∂planeMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z =>
      (shortSlopeOperator_pairing_eq _ u f g l r hwidth hfstrip hgstrip z).symm
  rw [hfull,actualBand_pairing_eq_diagonal psi N topLength w W c C htop hw hW hc hC u hu f g
    hband l r hwidth hfstrip hgstrip]
  exact (norm_sub_le _ _).trans ((add_le_add hdiag heBound).trans_eq (by ring))

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

theorem normalizedBandProjection_apply (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    normalizedBandProjection p w f z=((verticalProjectionCost p)⁻¹ : ℂ)*
      verticalConvolution (verticalProfileKernel p w 0) f z := by
  change ((verticalProjectionCost p)⁻¹ : ℂ)*schwartzVerticalProjection p w 0 f z=_
  rw [schwartzVerticalProjection_eq_convolution p w 0 hw]

theorem normalizedBandProjection_sizes (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure)≤∫ z, ‖f z‖ ∂planeMeasure ∧
      (∫ z, ‖normalizedBandProjection p w f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  let C := verticalProjectionCost p
  have hC : 0<C := verticalProjectionCost_pos p
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : C⁻¹*A≤1 := by
    rw [mul_comm,←div_eq_mul_inv]
    apply (div_le_one hC).2
    change A≤1+A
    linarith
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have hKnorm : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  have hn (z) : ‖normalizedBandProjection p w f z‖=C⁻¹*‖verticalConvolution K f z‖ := by
    rw [normalizedBandProjection_apply p w hw,norm_mul]
    simp only [C,K,norm_inv,Complex.norm_real,Real.norm_of_nonneg (verticalProjectionCost_pos p).le]
  have h1 := verticalConvolution_l1_bound K hKi hKm f f.continuous.measurable f.integrable
  have h2 := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  rw [hKnorm] at h1 h2
  constructor
  · simp_rw [hn]
    rw [integral_const_mul]
    calc
      _ ≤ C⁻¹*(A*∫ z, ‖f z‖ ∂planeMeasure) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hC.le)
      _ ≤ ∫ z, ‖f z‖ ∂planeMeasure := by
        rw [←mul_assoc]
        exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) hAC
  · simp_rw [hn,mul_pow]
    rw [integral_const_mul]
    calc
      _ ≤ (C⁻¹)^2*(A^2*∫ z, ‖f z‖^2 ∂planeMeasure) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ ∫ z, ‖f z‖^2 ∂planeMeasure := by
        rw [←mul_assoc,←mul_pow]
        exact mul_le_of_le_one_left (integral_nonneg fun _ => sq_nonneg _)
          (by nlinarith [pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hC.le) hA) hAC 2])

theorem normalizedBandProjection_uniform (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    ∀ z, ‖normalizedBandProjection p w f z‖≤1 := by
  intro z
  rw [normalizedBandProjection_apply p w hw,norm_mul]
  have hC := verticalProjectionCost_pos p
  simp only [norm_inv,Complex.norm_real,Real.norm_of_nonneg hC.le]
  have h := verticalConvolution_uniform_bound (verticalProfileKernel p w 0)
    (modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw) f 1 hf z
  rw [one_mul,show (∫ s, ‖verticalProfileKernel p w 0 s‖)=
    (∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖) from modulatedTimeKernel_l1 _ w 0 hw] at h
  apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hC.le)).trans
  rw [mul_comm,←div_eq_mul_inv]
  apply (div_le_one hC).2
  unfold verticalProjectionCost
  linarith

theorem normalizedBandProjection_band (p : SchwartzMap ℝ ℂ) (w c C : ℝ)
    (hp : ∀ eta, p eta≠0 → c≤eta ∧ eta≤C) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ∀ omega, planarFourier (normalizedBandProjection p w f) omega≠0 →
      c≤w*omega.2 ∧ w*omega.2≤C := by
  intro omega h
  by_contra hbad
  have hp0 : p (w*omega.2)=0 := by
    by_contra hnonzero
    exact hbad (hp _ hnonzero)
  apply h
  rw [normalizedBandProjection,planarFourier_smul,schwartzVerticalProjection_fourier]
  simp only [sub_zero,hp0,zero_mul,mul_zero]

theorem normalizedBandProjection_support (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → normalizedBandProjection p w f z=0 := by
  intro z hz
  rw [normalizedBandProjection_apply p w hw,verticalConvolution_horizontal_support _ f S hf z hz,mul_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ActualCutoffBandHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual high-disparity estimate with the original band cutoff on
the input. The original bounded input need not itself have a spectrum. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem slopeKernelOperator_schwartz_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=c*slopeKernelOperator K u f z := by
  unfold slopeKernelOperator
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_apply,smul_eq_mul]
  ring

theorem bandProjection_pairing_normalize (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖∫ z, slopeKernelOperator K u (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure‖=
      verticalProjectionCost p*
        ‖∫ z, slopeKernelOperator K u (normalizedBandProjection p w f) z*star (g z) ∂planeMeasure‖ := by
  have hC := verticalProjectionCost_pos p
  have hp : schwartzVerticalProjection p w 0 f=
      (verticalProjectionCost p : ℂ) • normalizedBandProjection p w f := by
    unfold normalizedBandProjection
    rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast hC.ne' : (verticalProjectionCost p : ℂ)≠0),one_smul]
  rw [hp]
  simp_rw [slopeKernelOperator_schwartz_smul,mul_assoc]
  rw [integral_const_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hC.le]

theorem actual_cutoff_band_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi p : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hp : ∀ s : ℝ, p s≠0 → c ≤ s ∧ s≤C) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W) ≤ c/2 → c/2≤C → topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ)) ≤ m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
        (fun z => field (planeCoordinates z)) (schwartzVerticalProjection p w 0 f) z*
          star (g z) ∂planeMeasure‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,A,L0,hD,hA,hL0,hmain⟩ := actual_band_high hVariation hLL psi c C a M hc hC ha hM hpsi
  refine ⟨D,verticalProjectionCost p*A,L0,hD,mul_pos (verticalProjectionCost_pos p) hA,hL0,?_⟩
  intro L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength field hfield hfieldBound
    f g F E ratio hF hE hr heq hlog hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip
    hmlo hmhi hWeq
  have hsizes := normalizedBandProjection_sizes p w hw f
  have h := hmain L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength
    field hfield hfieldBound (normalizedBandProjection p w f) g
    (normalizedBandProjection_band p w c C hp f) F E ratio hF hE hr heq hlog
    (normalizedBandProjection_uniform p w hw f hfInf) hgInf (hsizes.1.trans hfL1) hgL1
    (hsizes.2.trans hfE) hgE l r m hstrip
    (normalizedBandProjection_support p w hw f (Icc l r) hfstrip) hgstrip hmlo hmhi hWeq
  rw [bandProjection_pairing_normalize]
  exact (mul_le_mul_of_nonneg_left h (verticalProjectionCost_pos p).le).trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalHilbertPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted horizontal estimates at the two exponents used in the
manuscript, transferred to the original vertical cutoff. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_power_le_l1 (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hf : ∀ z, ‖f z‖≤1) (p : ℝ) (hp : 1≤p) :
    (∫ z, ‖f z‖^p ∂planeMeasure)≤∫ z, ‖f z‖ ∂planeMeasure := by
  have hp0 : 0<p := lt_of_lt_of_le zero_lt_one hp
  have hi : Integrable (fun z => ‖f z‖^p) planeMeasure := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (f.memLp (ENNReal.ofReal p) planeMeasure).integrable_norm_rpow
        (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0) (by simp)
  exact integral_mono hi (f.integrable.norm) fun z =>
    Real.rpow_le_self_of_le_one (norm_nonneg _) (hf z) hp

theorem horizontalHilbert_restricted_pairing (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ r R : ℝ, 0 < r → r≤R → ∀ f g : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ‖∫ z, horizontalTruncatedHilbert r R f z*star (g z) ∂planeMeasure‖≤
        C*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*(∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨C,hC,hbound⟩ := horizontalHilbert_power_bound hH
  refine ⟨C,hC,?_⟩
  intro p q hp hpq r R hr hrR f g hf hg
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have hsz := hbound p hp r R hr hrR f
  have hmem : MemLp (horizontalTruncatedHilbert r R f) (ENNReal.ofReal p) planeMeasure := by
    apply (integrable_norm_rpow_iff
      (horizontalTruncatedHilbert_measurable r R f).aestronglyMeasurable
      (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0) (by simp)).1
    simpa only [ENNReal.toReal_ofReal hp0.le] using hsz.1
  have hfpower := schwartz_power_le_l1 f hf p hpq.lt.le
  have hgpower := schwartz_power_le_l1 g hg q hpq.symm.lt.le
  have hroot : (∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure)^(1/p)≤
      C*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p) := by
    calc
      _ ≤ (C^p*(∫ z, ‖f z‖ ∂planeMeasure))^(1/p) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
          (hsz.2.trans (mul_le_mul_of_nonneg_left hfpower (Real.rpow_nonneg hC.le _)))
          (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (integral_nonneg fun _ => norm_nonneg _),
          ←Real.rpow_mul hC.le,mul_one_div_cancel hp0.ne',Real.rpow_one]
  calc
    _ ≤ ∫ z, ‖horizontalTruncatedHilbert r R f z*star (g z)‖ ∂planeMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ z, ‖horizontalTruncatedHilbert r R f z‖*‖g z‖ ∂planeMeasure := by
      simp only [norm_mul,norm_star]
    _ ≤ (∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure)^(1/p)*
        (∫ z, ‖g z‖^q ∂planeMeasure)^(1/q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hmem (g.memLp _ _)
    _ ≤ _ := mul_le_mul hroot
      (Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
        hgpower (by positivity)) (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg hC.le (Real.rpow_nonneg (integral_nonneg fun _ => norm_nonneg _) _))

theorem horizontalHilbertProjection_restricted_pairing (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ r R : ℝ, 0 < r → r≤R → ∀ (cutoff : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ f g : SchwartzMap (ℝ×ℝ) ℂ, (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ‖∫ z, horizontalTruncatedHilbert r R (schwartzVerticalProjection cutoff w 0 f) z*
        star (g z) ∂planeMeasure‖≤
        (C*verticalProjectionCost cutoff)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨C,hC,hbound⟩ := horizontalHilbert_restricted_pairing hH
  refine ⟨C,hC,?_⟩
  intro p q hp hpq r R hr hrR cutoff w hw f g hf hg
  have hb := hbound p q hp hpq r R hr hrR (normalizedBandProjection cutoff w f) g
    (normalizedBandProjection_uniform cutoff w hw f hf) hg
  have hs := (normalizedBandProjection_sizes cutoff w hw f).1
  change ‖∫ z, slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0)
    (schwartzVerticalProjection cutoff w 0 f) z*star (g z) ∂planeMeasure‖≤_
  rw [bandProjection_pairing_normalize]
  calc
    _ ≤ verticalProjectionCost cutoff*
        (C*(∫ z, ‖normalizedBandProjection cutoff w f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q)) :=
      mul_le_mul_of_nonneg_left hb (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost cutoff*
        (C*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*(∫ z, ‖g z‖ ∂planeMeasure)^(1/q)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg fun _ => norm_nonneg _) _)
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (integral_nonneg fun _ => norm_nonneg _) hs (one_div_nonneg.mpr hpq.pos.le)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and kernel linearity of the actual scalar pairing. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem slopeKernelOperator_measurable (K : ℝ → ℂ) (hK : Measurable K)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (slopeKernelOperator K u f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ =>
      K p.2*f (p.1.1-p.2,p.1.2-p.2*u p.1)) := by fun_prop
  have hi : Measurable (fun z : ℝ×ℝ => ∫ t : ℝ, K t*f (z.1-t,z.2-t*u z)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  exact hi

theorem slopeKernelOperator_uniform (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    ‖slopeKernelOperator K u f z‖≤
      (∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f := by
  have h := norm_integral_le_of_norm_le
    (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f))
    (Filter.Eventually.of_forall fun t => show
      ‖K t*f (z.1-t,z.2-t*u z)‖≤‖K t‖*SchwartzMap.seminorm ℝ 0 0 f from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _))
  simpa only [slopeKernelOperator,integral_mul_const] using h

theorem kernelPairing_integrable (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (fun z => slopeKernelOperator K u f z*star (g z)) planeMeasure := by
  have hm := slopeKernelOperator_measurable K hKm u hu f
  apply ((g.integrable (μ:=planeMeasure)).norm.const_mul
    ((∫ t, ‖K t‖)*SchwartzMap.seminorm ℝ 0 0 f)).mono'
  · exact (show Measurable (fun z => slopeKernelOperator K u f z*star (g z)) from by fun_prop).aestronglyMeasurable
  · filter_upwards [] with z
    rw [norm_mul,norm_star]
    exact mul_le_mul_of_nonneg_right (slopeKernelOperator_uniform K hK u f z) (norm_nonneg _)

theorem kernelPairing_add (K J : ℝ → ℂ) (hKm : Measurable K) (hJm : Measurable J)
    (hK : Integrable K) (hJ : Integrable J) (u : (ℝ×ℝ) → ℝ) (hu : Measurable u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing (fun t => K t+J t) u f g=kernelPairing K u f g+kernelPairing J u f g := by
  have heq (z : ℝ×ℝ) : slopeKernelOperator (fun t => K t+J t) u f z=
      slopeKernelOperator K u f z+slopeKernelOperator J u f z := by
    simp only [slopeKernelOperator,add_mul]
    exact integral_add (slope_integrand_integrable K hK u f z)
      (slope_integrand_integrable J hJ u f z)
  simp only [kernelPairing,heq,add_mul]
  exact integral_add (kernelPairing_integrable K hKm hK u hu f g)
    (kernelPairing_integrable J hJm hJ u hu f g)

theorem kernelPairing_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) :
    kernelPairing K u (c • f) g=c*kernelPairing K u f g := by
  have heq (z : ℝ×ℝ) : slopeKernelOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=
      c*slopeKernelOperator K u f z := by
    unfold slopeKernelOperator
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [smul_apply,smul_eq_mul]
    ring
  simp only [kernelPairing,heq,mul_assoc]
  exact integral_const_mul _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-time kernel has its exact logarithmic L1 mass. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_l1 (r R : ℝ) (hr : 0 < r) (hrR : r≤R) :
    (∫ t, ‖sharpTimeKernel r R t‖)=2*Real.log (R/r) := by
  let A := (Ioo r R).indicator (fun t : ℝ => t⁻¹)
  have hA : Integrable A := by
    apply (integrable_indicator_iff measurableSet_Ioo).2
    apply Measure.integrableOn_of_bounded (by simp)
      (show AEStronglyMeasurable (fun t : ℝ => t⁻¹) volume from by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,abs_inv,abs_of_pos (hr.trans ht.1)]
    exact (inv_le_inv₀ (hr.trans ht.1) hr).2 ht.1.le
  have hAI : (∫ t, A t)=Real.log (R/r) := by
    rw [integral_indicator measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
      ←intervalIntegral.integral_of_le hrR]
    exact integral_inv_of_pos hr (hr.trans_le hrR)
  have heq (t : ℝ) : ‖sharpTimeKernel r R t‖=A t+A (-t) := by
    change ‖sharpTimeKernel r R t‖=(Ioo r R).indicator (fun t : ℝ => t⁻¹) t+
      (Ioo r R).indicator (fun t : ℝ => t⁻¹) (-t)
    by_cases ht : 0≤t
    · have hn : -t∉Ioo r R := by intro h; linarith [h.1]
      rw [Set.indicator_of_notMem hn,add_zero]
      by_cases h : t∈Ioo r R
      · rw [Set.indicator_of_mem h]
        rw [sharpTimeKernel,ite_eq_left (show r< |t| ∧ |t|<R by
          simpa only [abs_of_nonneg ht,Set.mem_Ioo] using h)]
        simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
      · rw [Set.indicator_of_notMem h]
        simp only [sharpTimeKernel,abs_of_nonneg ht,ite_eq_right (show ¬(r<t ∧ t<R) by simpa only [Set.mem_Ioo] using h),norm_zero]
    · have hn : t∉Ioo r R := by intro h; linarith [h.1]
      rw [Set.indicator_of_notMem hn,zero_add]
      have ht' : t<0 := lt_of_not_ge ht
      by_cases h : -t∈Ioo r R
      · rw [Set.indicator_of_mem h]
        rw [sharpTimeKernel,ite_eq_left (show r< |t| ∧ |t|<R by
          simpa only [abs_of_neg ht',Set.mem_Ioo] using h)]
        simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_neg ht']
      · rw [Set.indicator_of_notMem h]
        simp only [sharpTimeKernel,abs_of_neg ht',ite_eq_right (show ¬(r< -t ∧ -t<R) by simpa only [Set.mem_Ioo] using h),norm_zero]
  simp_rw [heq]
  rw [integral_add hA hA.comp_neg]
  have hn : (∫ t, A (-t))=∫ t, A t := by
    simpa using Measure.integral_comp_mul_left A (-1)
  rw [hn,hAI]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LongHilbertPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-time remainder has logarithmic size times the smaller
restricted mass, also for the original vertical projection. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpHilbert_long_pairing (a R : ℝ) (ha : 0<a) (haR : a≤R)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖kernelPairing (sharpTimeKernel a R) u f g‖≤
      (2*Real.log (R/a))*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  have h := (shortKernel_pairing (sharpTimeKernel a R) (sharpTimeKernel_measurable a R)
    (sharpTimeKernel_integrable a R ha (ha.trans_le haR)) u hu f g
    f.continuous.measurable g.continuous.measurable f.integrable g.integrable hf hg).2
  simp_rw [shortSlopeOperator_pairing_eq _ u f g l r hwidth hfstrip hgstrip] at h
  rw [sharpTimeKernel_l1 a R ha haR] at h
  exact h.trans_eq (mul_comm _ _)

theorem sharpHilbertProjection_long_pairing (a R : ℝ) (ha : 0<a) (haR : a≤R)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hfstrip : ∀ z, z.1∉Icc l r → f z=0) (hgstrip : ∀ z, z.1∉Icc l r → g z=0) :
    ‖kernelPairing (sharpTimeKernel a R) u (schwartzVerticalProjection p w 0 f) g‖≤
      (verticalProjectionCost p*(2*Real.log (R/a)))*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  have h := sharpHilbert_long_pairing a R ha haR u hu (normalizedBandProjection p w f) g
    (normalizedBandProjection_uniform p w hw f hf) hg l r hwidth
    (normalizedBandProjection_support p w hw f _ hfstrip) hgstrip
  have hs := (normalizedBandProjection_sizes p w hw f).1
  have hlog : 0≤2*Real.log (R/a) := by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg ((one_le_div ha).2 haR)
  unfold kernelPairing
  rw [bandProjection_pairing_normalize]
  calc
    _ ≤ verticalProjectionCost p*((2*Real.log (R/a))*
        min (4*∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left h (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost p*((2*Real.log (R/a))*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      exact mul_le_mul_of_nonneg_left (min_le_min (mul_le_mul_of_nonneg_left hs (by norm_num)) le_rfl) hlog
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpTimeSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact splitting of sharp time truncations; the two boundary points
are removed only by a null-set argument. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_split_ae (r s R : ℝ) (hrs : r ≤ s) (hsR : s≤R) :
    (sharpTimeKernel r R)=ᵐ[volume] fun t => sharpTimeKernel r s t+sharpTimeKernel s R t := by
  have hs : ∀ᵐ t : ℝ, t≠s := by apply ae_iff.mpr; simp
  have hns : ∀ᵐ t : ℝ, t≠ -s := by apply ae_iff.mpr; simp
  filter_upwards [hs,hns] with t ht hnt
  have hn : |t|≠s := by
    intro h
    by_cases hz : 0≤t
    · exact ht (by simpa only [abs_of_nonneg hz] using h)
    · exact hnt (by rw [abs_of_neg (lt_of_not_ge hz)] at h; linarith)
  by_cases h1 : r< |t|
  · by_cases h2 : |t| < s
    · have h3 : |t|<R := h2.trans_le hsR
      have h4 : ¬s< |t| := by linarith
      simp only [sharpTimeKernel,h1,h2,h3,h4,and_self,false_and,
        ite_true, if_true,ite_false, if_false,add_zero]
    · have h3 : s< |t| := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm hn)
      by_cases h4 : |t|<R
      · simp only [sharpTimeKernel,h1,h2,h3,h4,and_self,and_false,
          ite_true, if_true,ite_false, if_false,zero_add]
      · simp only [sharpTimeKernel,h2,h4,and_false,ite_false, if_false,add_zero]
  · have h2 : ¬s< |t| := by linarith
    simp only [sharpTimeKernel,h1,h2,false_and,ite_false, if_false,add_zero]

theorem kernelPairing_sharp_split (r s R : ℝ) (hr : 0 < r) (hrs : r ≤ s) (hsR : s≤R)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing (sharpTimeKernel r R) u f g=
      kernelPairing (sharpTimeKernel r s) u f g+kernelPairing (sharpTimeKernel s R) u f g := by
  have hs : 0 < s := hr.trans_le hrs
  have hR : 0<R := hs.trans_le hsR
  have heq : kernelPairing (sharpTimeKernel r R) u f g=
      kernelPairing (fun t => sharpTimeKernel r s t+sharpTimeKernel s R t) u f g := by
    unfold kernelPairing
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold slopeKernelOperator
    apply integral_congr_ae
    filter_upwards [sharpTimeKernel_split_ae r s R hrs hsR] with t ht
    rw [ht]
  rw [heq]
  exact kernelPairing_add _ _ (sharpTimeKernel_measurable r s) (sharpTimeKernel_measurable s R)
    (sharpTimeKernel_integrable r s hr hs) (sharpTimeKernel_integrable s R hs hR) u hu f g

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_KernelAverageL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L1 and uniform bounds for the integrable time averages used in the
very-short-time error. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelAverage_l1 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ)
    (hF : ∀ t, Integrable (fun z => F (t,z)) planeMeasure)
    (hbound : ∀ t, (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤B) :
    Integrable (fun z => ∫ t, K t*F (t,z)) planeMeasure ∧
      (∫ z, ‖∫ t, K t*F (t,z)‖ ∂planeMeasure)≤(∫ t, ‖K t‖)*B := by
  let H := fun p : ℝ×(ℝ×ℝ) => K p.1*F p
  have hHm : Measurable H := (hKm.comp measurable_fst).mul hFm
  have hHi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t => (hF t).const_mul (K t)
    · apply (hK.norm.mul_const B).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖K t*F (t,z)‖ ∂planeMeasure‖≤_
      simp only [norm_mul,integral_const_mul]
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
  refine ⟨hHi.integral_prod_right,?_⟩
  calc
    _ ≤ ∫ z : ℝ×ℝ, (∫ t, ‖H (t,z)‖) ∂planeMeasure :=
      integral_mono hHi.integral_prod_right.norm hHi.norm.integral_prod_right
        (fun z => norm_integral_le_integral_norm _)
    _ = ∫ t, ∫ z, ‖H (t,z)‖ ∂planeMeasure :=
      integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖H (t,z)‖) hHi.norm.swap
    _ ≤ ∫ t, ‖K t‖*B := by
      apply integral_mono hHi.norm.integral_prod_left (hK.norm.mul_const B)
      intro t
      simp only [H,norm_mul,integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)
    _ = _ := integral_mul_const B _

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTimeAverageL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating a short-time linear error costs only the first absolute
moment of the time kernel, also in L1. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortTimeQuotient_l1 (F : ℝ×(ℝ×ℝ) → ℂ) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → Integrable (fun z => F (t,z)) planeMeasure)
    (hbound : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤B*|t|)
    (t : ℝ) :
    Integrable (fun z => shortTimeQuotient F (t,z)) planeMeasure ∧
      (∫ z, ‖shortTimeQuotient F (t,z)‖ ∂planeMeasure)≤B := by
  by_cases ht : |t|≤1/4
  · refine ⟨by simpa only [shortTimeQuotient,ite_eq_left ht] using
      (hF t ht).const_mul (t⁻¹:ℂ),?_⟩
    simp only [shortTimeQuotient,ite_eq_left ht,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
    rw [integral_const_mul]
    apply (mul_le_mul_of_nonneg_left (hbound t ht) (inv_nonneg.mpr (abs_nonneg t))).trans
    by_cases ht0 : t=0
    · simpa only [ht0,abs_zero,inv_zero,zero_mul] using hB
    · rw [mul_comm B |t|,←mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr ht0),one_mul]
  · simp only [shortTimeQuotient,ite_eq_right ht,norm_zero,integral_zero]
    exact ⟨integrable_zero _ _ _,hB⟩

theorem shortTimeAverage_l1 (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F) (B : ℝ) (hB : 0≤B)
    (hF : ∀ t, |t|≤1/4 → Integrable (fun z => F (t,z)) planeMeasure)
    (hbound : ∀ t, |t|≤1/4 → (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤B*|t|) :
    Integrable (fun z => ∫ t, if |t|≤1/4 then K t*F (t,z) else 0) planeMeasure ∧
      (∫ z, ‖∫ t, if |t|≤1/4 then K t*F (t,z) else 0‖ ∂planeMeasure)≤
        (∫ t, |t| *‖K t‖)*B := by
  let K1 := fun t : ℝ => (t:ℂ)*K t
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
      have hc : (t:ℂ)≠0 := by exact_mod_cast ht
      field_simp
    · simp only [shortTimeQuotient,ite_eq_right hshort,mul_zero]
  have h := kernelAverage_l1 K1 hK1m hK1i (shortTimeQuotient F)
    (shortTimeQuotient_measurable F hFm) B
    (fun t => (shortTimeQuotient_l1 F B hB hF hbound t).1)
    (fun t => (shortTimeQuotient_l1 F B hB hF hbound t).2)
  simp only [heq] at h
  simpa only [K1,norm_mul,Complex.norm_real,Real.norm_eq_abs] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalProjectionDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vertical derivative of the actual band projection has L1 and
uniform bounds of order inverse bandwidth. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem verticalDerivativeProfile_apply (p : SchwartzMap ℝ ℂ) (s : ℝ) :
    verticalDerivativeProfile p s=(2*Real.pi*Complex.I : ℂ)*(s:ℂ)*p s := by
  unfold verticalDerivativeProfile
  rw [smul_apply,SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [smul_eq_mul,mul_assoc]

theorem verticalProjection_derivative (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f)=
      (w⁻¹:ℂ) • schwartzVerticalProjection (verticalDerivativeProfile p) w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  rw [verticalSchwartzDeriv_fourier,planarFourier_smul,
    schwartzVerticalProjection_fourier,schwartzVerticalProjection_fourier,
    verticalDerivativeProfile_apply]
  simp only [sub_zero]
  push_cast
  have hwc : (w:ℂ)≠0 := by exact_mod_cast hw.ne'
  field_simp

theorem verticalProjection_derivative_sizes (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    (∫ z, ‖verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f) z‖ ∂planeMeasure)≤
      (verticalProjectionCost (verticalDerivativeProfile p)/w)*(∫ z, ‖f z‖ ∂planeMeasure) ∧
    ∀ z, ‖verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f) z‖≤
      verticalProjectionCost (verticalDerivativeProfile p)/w := by
  let q := verticalDerivativeProfile p
  let K := verticalProfileKernel q w 0
  let A := ∫ s, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) s‖
  have hA : A≤verticalProjectionCost q := by
    change A≤1+A
    linarith
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ q) w 0 hw
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ q : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hmass : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ q) w 0 hw
  have heq (z : ℝ×ℝ) : ‖verticalSchwartzDeriv (schwartzVerticalProjection p w 0 f) z‖=
      w⁻¹*‖verticalConvolution K f z‖ := by
    rw [verticalProjection_derivative p w hw,smul_apply,norm_smul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hw.le,schwartzVerticalProjection_eq_convolution q w 0 hw]
  constructor
  · simp_rw [heq]
    rw [integral_const_mul]
    have h := verticalConvolution_l1_bound K hKi hKm f f.continuous.measurable f.integrable
    rw [hmass] at h
    calc
      _ ≤ w⁻¹*(A*∫ z, ‖f z‖ ∂planeMeasure) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hw.le)
      _ ≤ w⁻¹*(verticalProjectionCost q*∫ z, ‖f z‖ ∂planeMeasure) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA
          (integral_nonneg fun _ => norm_nonneg _)) (inv_nonneg.mpr hw.le)
      _ = _ := by dsimp [q]; ring
  · intro z
    rw [heq]
    have h := verticalConvolution_uniform_bound K hKi f 1 hf z
    rw [hmass,one_mul] at h
    calc
      _ ≤ w⁻¹*verticalProjectionCost q := mul_le_mul_of_nonneg_left (h.trans hA) (inv_nonneg.mpr hw.le)
      _ = _ := by dsimp [q]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortVerticalDifference
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact vertical FTC for replacing short directional sampling by
horizontal sampling. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortVerticalDifference_identity (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (t : ℝ) (z : ℝ×ℝ) :
    shortVerticalDifference f u t z=(-t*u z) •
      ∫ theta in Ioc (0:ℝ) 1, verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z) := by
  let d := -t*u z
  let H := fun theta : ℝ => verticalSchwartzDeriv f (z.1-t,z.2+theta*d)
  have hc : Continuous H := (verticalSchwartzDeriv f).continuous.comp (by fun_prop)
  have hi : IntervalIntegrable (fun theta => d • H theta) volume 0 1 :=
    ((continuous_const : Continuous (fun _ : ℝ => d)).smul hc).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _ => verticalPath_hasDerivAt f (z.1-t) z.2 d theta) hi
  have heq : shortVerticalDifference f u t z=d • ∫ theta in (0:ℝ)..1, H theta := by
    simpa only [shortVerticalDifference,zero_mul,add_zero,one_mul,
      show z.2+d=z.2-t*u z by dsimp [d]; ring,intervalIntegral.integral_smul] using h.symm
  rw [heq,intervalIntegral.integral_of_le zero_le_one]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with theta
  change verticalSchwartzDeriv f (z.1-t,z.2+theta*(-t*u z))=
    verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)
  rw [show z.2+theta*(-t*u z)=z.2-theta*t*u z by ring]

theorem shortVerticalDifference_norm (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : ∀ z, |u z|≤1) (t : ℝ) (z : ℝ×ℝ) :
    ‖shortVerticalDifference f u t z‖≤|t| *
      ∫ theta in Ioc (0:ℝ) 1, ‖verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)‖ := by
  rw [shortVerticalDifference_identity,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
  calc
    _ ≤ (|t| *|u z|)*∫ theta in Ioc (0:ℝ) 1,
        ‖verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_of_le_one_right (abs_nonneg _) (hu z)
      · exact integral_nonneg fun _ => norm_nonneg _

theorem shortVerticalDifference_uniform (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : ∀ z, |u z|≤1) (t C : ℝ)
    (hC : ∀ z, ‖verticalSchwartzDeriv f z‖≤C) (z : ℝ×ℝ) :
    ‖shortVerticalDifference f u t z‖≤|t| *C := by
  apply (shortVerticalDifference_norm f u hu t z).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hi : Integrable (fun theta : ℝ =>
      ‖verticalSchwartzDeriv f (z.1-t,z.2-theta*t*u z)‖) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((verticalSchwartzDeriv f).continuous.comp (by fun_prop)).norm.intervalIntegrable 0 1 |>.1
  have h := integral_mono hi (integrable_const C) (fun theta => hC _)
  simpa only [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul] using h

theorem scaledSlope_lipschitz (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) :
    LipschitzWith 2 (fun z => theta*u z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := hu.dist_le_mul z w
  rw [Real.dist_eq] at h ⊢
  rw [←mul_sub,abs_mul,abs_of_nonneg h0]
  calc
    _ ≤ theta*(2*dist z w) := mul_le_mul_of_nonneg_left h h0
    _ ≤ 2*dist z w := mul_le_of_le_one_left (by positivity) h1

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortVerticalDifferenceL1
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short vertical FTC error is controlled in L1 by the vertical
Schwartz derivative and the explicit sampling distortion. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortVerticalDifference_l1 (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (t : ℝ) (ht : |t|≤1/4) :
    Integrable (shortVerticalDifference f u t) planeMeasure ∧
      (∫ z, ‖shortVerticalDifference f u t z‖ ∂planeMeasure)≤
        4*|t| *(∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) := by
  let nu : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  let G := fun p : ℝ×(ℝ×ℝ) =>
    verticalSchwartzDeriv f (p.2.1-t,p.2.2-p.1*t*u p.2)
  have hum := hu.continuous.measurable
  have hGm : Measurable G := (verticalSchwartzDeriv f).continuous.measurable.comp (by fun_prop)
  have htheta : ∀ᵐ theta ∂nu, theta∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hslice (theta : ℝ) (hth : theta∈Ioc (0:ℝ) 1) :
      Integrable (fun z => ‖G (theta,z)‖) planeMeasure ∧
      (∫ z, ‖G (theta,z)‖ ∂planeMeasure)≤4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure := by
    have hs := scaledSlope_lipschitz u hu theta hth.1.le hth.2
    have h := planar_integral_comp_le_four (verticalSampling (fun z => theta*u z) t t 0)
      (verticalSampling_measurable _ hs.continuous.measurable t t 0)
      (verticalSampling_antilipschitz _ hs t t 0 ht)
      (fun z => ‖verticalSchwartzDeriv f z‖) (verticalSchwartzDeriv f).integrable.norm
      (fun _ => norm_nonneg _)
    simpa only [G,Function.comp_def,verticalSampling,sub_zero,mul_assoc,mul_left_comm t theta] using h
  have hGi : Integrable G (nu.prod planeMeasure) := by
    apply (integrable_prod_iff hGm.aestronglyMeasurable).2
    constructor
    · filter_upwards [htheta] with theta hth
      exact (integrable_norm_iff (hGm.comp (by fun_prop)).aestronglyMeasurable).1 (hslice theta hth).1
    · apply (integrable_const (4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure)).mono'
        hGm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [htheta] with theta hth
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hslice theta hth).2
  have hDm : Measurable (shortVerticalDifference f u t) := by
    unfold shortVerticalDifference
    exact (f.continuous.measurable.comp (by fun_prop)).sub
      (f.continuous.measurable.comp (by fun_prop))
  have hp (z : ℝ×ℝ) : ‖shortVerticalDifference f u t z‖≤|t| *(∫ theta, ‖G (theta,z)‖ ∂nu) :=
    shortVerticalDifference_norm f u hub t z
  have hdom := hGi.norm.integral_prod_right.const_mul |t|
  have hDi := hdom.mono' hDm.aestronglyMeasurable (Filter.Eventually.of_forall hp)
  refine ⟨hDi,?_⟩
  have htotal : (∫ theta, ∫ z, ‖G (theta,z)‖ ∂planeMeasure ∂nu)≤
      4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure := by
    have h := integral_mono_ae hGi.norm.integral_prod_left
      (integrable_const (4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure))
      (htheta.mono fun theta hth => (hslice theta hth).2)
    simpa only [integral_const,nu,measureReal_def,Measure.restrict_apply_univ,
      Real.volume_Ioc,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul] using h
  calc
    _ ≤ ∫ z, |t| *(∫ theta, ‖G (theta,z)‖ ∂nu) ∂planeMeasure := integral_mono hDi.norm hdom hp
    _ = |t| *(∫ theta, ∫ z, ‖G (theta,z)‖ ∂planeMeasure ∂nu) := by
      rw [integral_const_mul]
      exact congrArg (fun b : ℝ => |t| *b)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (theta : ℝ) => ‖G (theta,z)‖) hGi.norm.swap)
    _ ≤ |t| *(4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) :=
      mul_le_mul_of_nonneg_left htotal (abs_nonneg _)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortVerticalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated very-short-time replacement error, with its exact
first-moment dependence. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortVerticalDifference_joint_measurable (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => shortVerticalDifference f u p.1 p.2) := by
  unfold shortVerticalDifference
  exact (f.continuous.measurable.comp (by fun_prop)).sub
    (f.continuous.measurable.comp (by fun_prop))

theorem shortVerticalError_l1 (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (shortVerticalError K u f) planeMeasure ∧
      (∫ z, ‖shortVerticalError K u f z‖ ∂planeMeasure)≤
        4*(∫ t, |t| *‖K t‖)*(∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) := by
  have h := shortTimeAverage_l1 K hKm hK1
    (fun p => shortVerticalDifference f u p.1 p.2)
    (shortVerticalDifference_joint_measurable f u hu.continuous.measurable)
    (4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) (by positivity)
    (fun t ht => (shortVerticalDifference_l1 f u hu hub t ht).1)
    (fun t ht => (shortVerticalDifference_l1 f u hu hub t ht).2.trans_eq (by ring))
  exact ⟨h.1,h.2.trans_eq (by ring)⟩

theorem shortVerticalError_uniform (K : ℝ → ℂ)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (u : (ℝ×ℝ) → ℝ) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (C : ℝ) (hC : 0≤C)
    (hDf : ∀ z, ‖verticalSchwartzDeriv f z‖≤C) (z : ℝ×ℝ) :
    ‖shortVerticalError K u f z‖≤(∫ t, |t| *‖K t‖)*C := by
  have h := norm_integral_le_of_norm_le (hK1.mul_const C)
    (Filter.Eventually.of_forall (fun t => show
      ‖if |t|≤1/4 then K t*shortVerticalDifference f u t z else 0‖≤(|t| *‖K t‖)*C from by
      by_cases ht : |t|≤1/4
      · rw [ite_eq_left ht,norm_mul]
        exact (mul_le_mul_of_nonneg_left (shortVerticalDifference_uniform f u hub t C hDf z)
          (norm_nonneg _)).trans_eq (by ring)
      · rw [ite_eq_right ht,norm_zero]
        positivity))
  simpa only [shortVerticalError,integral_mul_const] using h

theorem shortVerticalProjectionError_sizes (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    (∫ z, ‖shortVerticalError K u (schwartzVerticalProjection p w 0 f) z‖ ∂planeMeasure)≤
      (4*(∫ t, |t| *‖K t‖)*verticalProjectionCost (verticalDerivativeProfile p)/w)*
        (∫ z, ‖f z‖ ∂planeMeasure) ∧
    ∀ z, ‖shortVerticalError K u (schwartzVerticalProjection p w 0 f) z‖≤
      (∫ t, |t| *‖K t‖)*verticalProjectionCost (verticalDerivativeProfile p)/w := by
  have hD := verticalProjection_derivative_sizes p w hw f hf
  constructor
  · have h := (shortVerticalError_l1 K hKm hK1 u hu hub
      (schwartzVerticalProjection p w 0 f)).2
    exact h.trans ((mul_le_mul_of_nonneg_left hD.1 (by positivity)).trans_eq (by ring))
  · intro z
    have h := shortVerticalError_uniform K hK1 u hub (schwartzVerticalProjection p w 0 f)
      (verticalProjectionCost (verticalDerivativeProfile p)/w)
      (div_nonneg (verticalProjectionCost_pos _).le hw.le) hD.2 z
    exact h.trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VeryShortHilbertError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual sharply truncated directional transform differs from its
horizontal counterpart by a uniformly controlled very-short-time error. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem veryShortHilbertError_identity (r R : ℝ) (hr : 0 < r) (hR : 0<R) (hsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortVerticalError (sharpTimeKernel r R) u f z=
      slopeKernelOperator (sharpTimeKernel r R) u f z-
        slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0) f z := by
  have hK := sharpTimeKernel_integrable r R hr hR
  unfold shortVerticalError slopeKernelOperator
  rw [←integral_sub (slope_integrand_integrable _ hK u f z)
    (slope_integrand_integrable _ hK (fun _ => 0) f z)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : |t|≤1/4
  · simp only [ite_eq_left ht,shortVerticalDifference,mul_zero,sub_zero,mul_sub]
  · have hzero : sharpTimeKernel r R t=0 := by
      unfold sharpTimeKernel
      apply ite_eq_right
      intro h
      exact ht (h.2.le.trans hsmall)
    simp only [ite_eq_right ht,hzero,mul_zero,zero_mul,sub_self]

theorem veryShortHilbertProjection_pairing (r R : ℝ) (hr : 0 < r) (hR : 0<R) (hsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1) :
    ‖∫ z, (slopeKernelOperator (sharpTimeKernel r R) u (schwartzVerticalProjection p w 0 f) z-
      slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0) (schwartzVerticalProjection p w 0 f) z)*
        star (g z) ∂planeMeasure‖≤
      (2*R*verticalProjectionCost (verticalDerivativeProfile p)/w)*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  let K := sharpTimeKernel r R
  let F := schwartzVerticalProjection p w 0 f
  let M := ∫ t, |t| *‖K t‖
  let C := verticalProjectionCost (verticalDerivativeProfile p)/w
  have hC : 0≤C := div_nonneg (verticalProjectionCost_pos _).le hw.le
  have hM : 0≤M := integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hmom := sharpTimeKernel_first_moment r R hr hR
  have hsz := shortVerticalProjectionError_sizes K (sharpTimeKernel_measurable r R) hmom.1
    u hu hub p w hw f hf
  have hi := (shortVerticalError_l1 K (sharpTimeKernel_measurable r R) hmom.1 u hu hub F).1
  have h1 (z : ℝ×ℝ) : ‖shortVerticalError K u F z*star (g z)‖≤‖shortVerticalError K u F z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hg z)
  have h2 (z : ℝ×ℝ) : ‖shortVerticalError K u F z*star (g z)‖≤(M*C)*‖g z‖ := by
    rw [norm_mul,norm_star]
    exact mul_le_mul_of_nonneg_right (by simpa only [M,C,mul_div_assoc] using hsz.2 z) (norm_nonneg _)
  have hb1 : ‖∫ z, shortVerticalError K u F z*star (g z) ∂planeMeasure‖≤
      (M*C)*(4*∫ z, ‖f z‖ ∂planeMeasure) := by
    exact (norm_integral_le_of_norm_le hi.norm (Filter.Eventually.of_forall h1)).trans
      (hsz.1.trans_eq (by dsimp [M,C]; ring))
  have hb2 : ‖∫ z, shortVerticalError K u F z*star (g z) ∂planeMeasure‖≤
      (M*C)*(∫ z, ‖g z‖ ∂planeMeasure) := by
    have h := norm_integral_le_of_norm_le ((g.integrable (μ:=planeMeasure)).norm.const_mul (M*C))
      (Filter.Eventually.of_forall h2)
    simpa only [integral_const_mul] using h
  simp_rw [←veryShortHilbertError_identity r R hr hR hsmall]
  change ‖∫ z, shortVerticalError K u F z*star (g z) ∂planeMeasure‖≤_
  calc
    _ ≤ (M*C)*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
      rw [mul_min_of_nonneg _ _ (mul_nonneg hM hC)]
      exact le_min hb1 hb2
    _ ≤ (2*R*C)*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmom.2 hC)
        (le_min (by positivity) (integral_nonneg fun _ => norm_nonneg _))
    _ = _ := by dsimp [C]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertTimeDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the actual short, middle and long time pieces. The
middle term is the finite annular operator already estimated by the
packet argument; all other terms have explicit restricted bounds. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelPairing_projection_normalize (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing K u (schwartzVerticalProjection p w 0 f) g=
      (verticalProjectionCost p : ℂ)*kernelPairing K u (normalizedBandProjection p w f) g := by
  have heq : schwartzVerticalProjection p w 0 f=
      (verticalProjectionCost p : ℂ) • normalizedBandProjection p w f := by
    unfold normalizedBandProjection
    rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast (verticalProjectionCost_pos p).ne' :
      (verticalProjectionCost p : ℂ)≠0),one_smul]
  rw [heq,kernelPairing_smul]

theorem hilbertProjected_middle_error :
    ∃ B : ℝ, 0≤B ∧ ∀ s T : ℝ, 0 < s → s≤T →
      ∃ N : ℕ, s≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*s ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (p : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) →
        (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel s T) u (schwartzVerticalProjection p w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection p w 0 f) g‖≤
        (verticalProjectionCost p*B)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hmain⟩ := hilbertArbitraryEndpoint_pairing
  refine ⟨B,hB,?_⟩
  intro s T hs hsT
  obtain ⟨N,hlo,hhi,hbound⟩ := hmain s T hs hsT
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hb := hbound u hu (normalizedBandProjection p w f) g
    (normalizedBandProjection_uniform p w hw f hf) hg l r hwidth
    (normalizedBandProjection_support p w hw f _ hfstrip) hgstrip
  have hsize := (normalizedBandProjection_sizes p w hw f).1
  rw [kernelPairing_projection_normalize,kernelPairing_projection_normalize,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg (verticalProjectionCost_pos _).le]
  calc
    _ ≤ verticalProjectionCost p*(B*min
        (4*∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left hb (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost p*(B*min
        (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      exact mul_le_mul_of_nonneg_left
        (min_le_min (mul_le_mul_of_nonneg_left hsize (by norm_num)) le_rfl) hB
    _ = _ := by ring

theorem hilbertProjected_short_error (epsilon s : ℝ) (he : 0<epsilon) (hes : epsilon ≤ s)
    (hs : s≤1/4) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1) :
    ‖kernelPairing (sharpTimeKernel epsilon s) u (schwartzVerticalProjection p w 0 f) g-
      kernelPairing (sharpTimeKernel epsilon s) (fun _ => 0) (schwartzVerticalProjection p w 0 f) g‖≤
      (2*s*verticalProjectionCost (verticalDerivativeProfile p)/w)*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  have hsp : 0 < s := he.trans_le hes
  have hK := sharpTimeKernel_integrable epsilon s he hsp
  have hKm := sharpTimeKernel_measurable epsilon s
  unfold kernelPairing
  rw [←integral_sub (kernelPairing_integrable _ hKm hK u hu.continuous.measurable _ g)
    (kernelPairing_integrable _ hKm hK (fun _ => 0) measurable_const _ g)]
  simp_rw [←sub_mul]
  exact veryShortHilbertProjection_pairing epsilon s he hsp hs u hu hub p w hw f g hf hg

theorem hilbertTimeDecomposition_bound (hH : HorizontalHilbertInput) :
    ∃ B C : ℝ, 0≤B ∧ 0<C ∧ ∀ epsilon s T R : ℝ,
      0<epsilon → epsilon ≤ s → s≤T → T≤R → s≤1/4 →
      ∃ N : ℕ, s≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*s ∧
      ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
      ∀ (cutoff : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) →
        (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection cutoff w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection cutoff w 0 f) g‖≤
        (verticalProjectionCost cutoff*(B+2*Real.log (R/T))+
          2*s*verticalProjectionCost (verticalDerivativeProfile cutoff)/w)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)+
        (C*verticalProjectionCost cutoff)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨B,hB,hmid⟩ := hilbertProjected_middle_error
  obtain ⟨C,hC,hhor⟩ := horizontalHilbertProjection_restricted_pairing hH
  refine ⟨B,C,hB,hC,?_⟩
  intro epsilon s T R he hes hsT hTR hsquarter
  have hs : 0 < s := he.trans_le hes
  obtain ⟨N,hlo,hhi,hmidbound⟩ := hmid s T hs hsT
  refine ⟨N,hlo,hhi,?_⟩
  intro p q hp hpq u hu hub cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  let F := schwartzVerticalProjection cutoff w 0 f
  let A := kernelPairing (sharpTimeKernel epsilon s) u F g
  let H := kernelPairing (sharpTimeKernel epsilon s) (fun _ => 0) F g
  let M := kernelPairing (sharpTimeKernel s T) u F g
  let J := kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u F g
  let V := kernelPairing (sharpTimeKernel T R) u F g
  have hshort := hilbertProjected_short_error epsilon s he hes hsquarter u hu hub
    cutoff w hw f g hf hg
  have hmiddle := hmidbound u hu cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  have hlong := sharpHilbertProjection_long_pairing T R (hs.trans_le hsT) hTR
    u hu cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  have hhorizontal := hhor p q hp hpq epsilon s he hes cutoff w hw f g hf hg
  have hsplit : kernelPairing (sharpTimeKernel epsilon R) u F g=A+(M+V) := by
    rw [kernelPairing_sharp_split epsilon s R he hes (hsT.trans hTR) u hu.continuous.measurable,
      kernelPairing_sharp_split s T R hs hsT hTR u hu.continuous.measurable]
  have heq : kernelPairing (sharpTimeKernel epsilon R) u F g-J=(A-H)+(M-J)+V+H := by
    rw [hsplit]
    ring
  change ‖kernelPairing (sharpTimeKernel epsilon R) u F g-J‖≤_
  rw [heq]
  calc
    _ ≤ ‖A-H‖+‖M-J‖+‖V‖+‖H‖ := by
      calc
        _ ≤ ‖A-H+(M-J)+V‖+‖H‖ := norm_add_le _ _
        _ ≤ (‖A-H+(M-J)‖+‖V‖)+‖H‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ _ := by
      have h := add_le_add (add_le_add (add_le_add hshort hmiddle) hlong) hhorizontal
      exact h.trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertEndpointCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary endpoint cases: no very-short segment when the
inner endpoint is already large, and no packet segment for wide bands. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertMiddleLong_bound :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon T R : ℝ, 0<epsilon → epsilon≤T → T≤R →
      ∃ N : ℕ, epsilon≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*epsilon ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (p : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection p w 0 f) g‖≤
        (verticalProjectionCost p*(B+2*Real.log (R/T)))*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hmid⟩ := hilbertProjected_middle_error
  refine ⟨B,hB,?_⟩
  intro epsilon T R he heT hTR
  obtain ⟨N,hlo,hhi,hbound⟩ := hmid epsilon T he heT
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hm := hbound u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hl := sharpHilbertProjection_long_pairing T R (he.trans_le heT) hTR u hu p w hw
    f g hf hg l r hwidth hfstrip hgstrip
  rw [kernelPairing_sharp_split epsilon T R he heT hTR u hu.continuous.measurable]
  rw [show ∀ a b c : ℂ, a+b-c=(a-c)+b by intros; ring]
  exact (norm_add_le _ _).trans ((add_le_add hm hl).trans_eq (by ring))

theorem hilbertShortLong_bound (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon T R : ℝ, 0<epsilon → epsilon≤T → T≤R → T≤1/4 →
      ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
      ∀ (cutoff : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection cutoff w 0 f) g‖≤
        (verticalProjectionCost cutoff*(2*Real.log (R/T))+
          2*T*verticalProjectionCost (verticalDerivativeProfile cutoff)/w)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)+
        (C*verticalProjectionCost cutoff)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨C,hC,hhor⟩ := horizontalHilbertProjection_restricted_pairing hH
  refine ⟨C,hC,?_⟩
  intro epsilon T R he heT hTR hTquarter p q hp hpq u hu hub cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  have hs := hilbertProjected_short_error epsilon T he heT hTquarter u hu hub cutoff w hw f g hf hg
  have hh := hhor p q hp hpq epsilon T he heT cutoff w hw f g hf hg
  have hl := sharpHilbertProjection_long_pairing T R (he.trans_le heT) hTR u hu cutoff w hw
    f g hf hg l r hwidth hfstrip hgstrip
  have hs' := (norm_le_insert'
    (kernelPairing (sharpTimeKernel epsilon T) u (schwartzVerticalProjection cutoff w 0 f) g)
    (kernelPairing (sharpTimeKernel epsilon T) (fun _ => 0) (schwartzVerticalProjection cutoff w 0 f) g)).trans
    (add_le_add hh hs)
  rw [kernelPairing_sharp_split epsilon T R he heT hTR u hu.continuous.measurable]
  exact (norm_add_le _ _).trans ((add_le_add hs' hl).trans_eq (by ring))

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-disparity packet theorem now bounds the actual sharp
Hilbert truncation, with its three explicit analytic remainder terms. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem dyadic_time_lower (N : ℕ) (T s : ℝ) (hT : 0<T)
    (hs : s≤T/(2:ℝ)^N) (j : Fin N) : s≤(T/2)/(2:ℝ)^j.val := by
  rw [div_div,←pow_succ']
  apply hs.trans
  apply (div_le_div_iff₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).2
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hT.le

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpRemainderDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact restricted-mass algebra and exponential absorption for the
analytic remainders in the actual sharp Hilbert estimate. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem sqrt_product_of_ratio (F E ratio : ℝ) (hF : 0<F) (hr : 0 < ratio)
    (heq : E=ratio^2*F) : Real.sqrt F*Real.sqrt E=ratio*F := by
  rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  nlinarith [Real.mul_self_sqrt hF.le]

theorem restricted_power_ratio (F E ratio L a b : ℝ) (hF : 0<F) (hr : 0 < ratio)
    (heq : E=ratio^2*F) (hlog : Real.log ratio=L) (hab : a+b=1) :
    F^a*E^b=Real.exp ((b-a)*L)*Real.sqrt F*Real.sqrt E := by
  have hE : 0<E := heq ▸ mul_pos (pow_pos hr 2) hF
  have hlogE : Real.log E=2*L+Real.log F := by
    rw [heq,Real.log_mul (pow_pos hr 2).ne' hF.ne',Real.log_pow,hlog]
    ring
  have hratio : ratio=Real.exp L := by rw [←hlog,Real.exp_log hr]
  have ha : a=1-b := by linarith
  calc
    _ = Real.exp (Real.log F*a+Real.log E*b) := by
      rw [Real.rpow_def_of_pos hF,Real.rpow_def_of_pos hE,Real.exp_add]
    _ = Real.exp ((b-a)*L)*Real.exp L*F := by
      rw [←Real.exp_log hF,←Real.exp_add,←Real.exp_add,hlogE,ha,Real.log_exp]
      congr 1
      ring
    _ = _ := by
      rw [←hratio]
      calc
        _ = Real.exp ((b-a)*L)*(ratio*F) := by ring
        _ = Real.exp ((b-a)*L)*(Real.sqrt F*Real.sqrt E) := by
          rw [sqrt_product_of_ratio F E ratio hF hr heq]
        _ = _ := by ring

theorem smaller_mass_ratio (F E ratio L : ℝ) (hF : 0<F) (hr : 0 < ratio)
    (heq : E=ratio^2*F) (hlog : Real.log ratio=L) :
    min (4*F) E≤4*Real.exp (-L)*(Real.sqrt F*Real.sqrt E) := by
  rw [sqrt_product_of_ratio F E ratio hF hr heq]
  have hratio : ratio=Real.exp L := by rw [←hlog,Real.exp_log hr]
  rw [hratio]
  calc
    min (4*F) E ≤ 4*F := min_le_left _ _
    _ = _ := by rw [mul_assoc,←mul_assoc (Real.exp (-L)),←Real.exp_add]; ring_nf; simp

theorem eventually_remainder_decay (K Q : ℝ) (hK : 0≤K) :
    ∀ᶠ L : ℝ in atTop,
      4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3)≤L^(-19:ℝ) := by
  have hfast := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 20 1 (by norm_num)
  have hslow := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 19 (1/3) (by norm_num)
  have ht : Tendsto (fun L : ℝ => 8*K*(L^(20:ℝ)*Real.exp (-L))+
      Q*(L^(19:ℝ)*Real.exp (-L/3))) atTop (nhds 0) := by
    simpa only [one_mul,mul_zero,add_zero,neg_mul,one_div_mul_eq_div,neg_div] using
      (hfast.const_mul (8*K)).add (hslow.const_mul Q)
  filter_upwards [eventually_ge_atTop (1:ℝ), ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with L hL hsmall
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hp : 0<L^(19:ℝ) := Real.rpow_pos_of_pos hLp _
  have heq : L^(20:ℝ)=L^(19:ℝ)*L := by
    rw [show (20:ℝ)=19+1 by norm_num,Real.rpow_add hLp,Real.rpow_one]
  have hpre : (4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3))*L^(19:ℝ)≤1 := by
    have hfirst : 4*K*(1+L)*Real.exp (-L)*L^(19:ℝ)≤
        8*K*(L^(20:ℝ)*Real.exp (-L)) := by
      rw [heq]
      have hfactor : 0≤K*Real.exp (-L)*L^(19:ℝ) := by positivity
      nlinarith
    nlinarith
  rw [Real.rpow_neg hLp.le,←one_div]
  exact (le_div_iff₀ hp).2 hpre

theorem absorb_sharp_remainders (z : ℂ) (A K Q F E ratio L : ℝ)
    (hK : 0≤K) (hL : 0≤L) (hF : 0<F) (hr : 0 < ratio)
    (heq : E=ratio^2*F) (hlog : Real.log ratio=L)
    (hdecay : 4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3)≤L^(-19:ℝ))
    (hbound : ‖z‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
      K*(1+L)*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ)) :
    ‖z‖≤(A+1)*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  have hm := smaller_mass_ratio F E ratio L hF hr heq hlog
  have hp := restricted_power_ratio F E ratio L (2/3) (1/3) hF hr heq hlog (by norm_num)
  have hp' : F^(2/3:ℝ)*E^(1/3:ℝ)=Real.exp (-L/3)*Real.sqrt F*Real.sqrt E := by
    have hexp : ((1/3:ℝ)-2/3)*L= -L/3 := by ring
    simpa only [hexp] using hp
  have hs : 0≤Real.sqrt F*Real.sqrt E := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    ‖z‖ ≤ A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        K*(1+L)*(4*Real.exp (-L)*(Real.sqrt F*Real.sqrt E))+
        Q*(Real.exp (-L/3)*Real.sqrt F*Real.sqrt E) := by
      rw [mul_assoc Q (F^(2/3:ℝ)),hp'] at hbound
      exact hbound.trans (add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (by positivity))) le_rfl)
    _ = A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        (4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3))*(Real.sqrt F*Real.sqrt E) := by ring
    _ ≤ A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        L^(-19:ℝ)*(Real.sqrt F*Real.sqrt E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hdecay hs)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SharpTimeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's time and averaging-width choices, with the exact
logarithmic long-time cost used by the sharp truncation argument. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem sharpSourceTime_pos (L : ℝ) : 0 < sharpSourceTime L := Real.exp_pos _
theorem sharpSourceWidthRatio_pos (L : ℝ) : 0 < sharpSourceWidthRatio L := Real.exp_pos _

theorem eventually_sharpSourceParameters :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ sharpSourceTime L≤1/4 ∧ 10 ≤ sharpSourceWidthRatio L := by
  have ht : Tendsto sharpSourceTime atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<97/100)))
  have hm : Tendsto sharpSourceWidthRatio atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10))
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    hm.eventually_ge_atTop 10] with L hL hT hmL
  exact ⟨hL,hT.le,hmL⟩

theorem sharpSourceTime_log (L R : ℝ) (hL : 1≤L) (hR : 0<R) (hR1 : R≤1) :
    Real.log (R/sharpSourceTime L)≤L := by
  rw [Real.log_div hR.ne' (sharpSourceTime_pos L).ne',sharpSourceTime,Real.log_exp,sub_neg_eq_add]
  have hr : Real.log R≤0 := Real.log_nonpos hR.le hR1
  have hp : L^(97/100:ℝ)≤L := Real.rpow_le_self_of_one_le hL (by norm_num)
  linarith

theorem sharpSourceWidthRatio_geometry (L w : ℝ) (hw : 0<w) (hm : 10 ≤ sharpSourceWidthRatio L) :
    w ≤ sharpSourceWidthRatio L*w ∧ 5*(w/(sharpSourceWidthRatio L*w))≤1/2 := by
  have hm0 := sharpSourceWidthRatio_pos L
  constructor
  · nlinarith
  · have heq : w/(sharpSourceWidthRatio L*w)=1/sharpSourceWidthRatio L := by field_simp
    rw [heq]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
    have hi : (1:ℝ)/sharpSourceWidthRatio L≤1/10 := (one_div_le_one_div_of_le (by norm_num) hm)
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandHighAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformity in the inner endpoint and in the band width. All four
relative positions of the inner, very-short and packet cutoffs are covered. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem restricted_remainder_mono (F E f e k K q Q : ℝ)
    (hf0 : 0≤f) (he0 : 0≤e) (hf : f≤F) (he : e≤E)
    (hk0 : 0≤k) (hk : k≤K) (hq0 : 0≤q) (hq : q≤Q) :
    k*min (4*f) e+q*f^(2/3:ℝ)*e^(1/3:ℝ)≤
      K*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ) := by
  have hF0 : 0≤F := hf0.trans hf
  have hE0 : 0≤E := he0.trans he
  have hQ0 : 0≤Q := hq0.trans hq
  apply add_le_add
  · exact mul_le_mul hk (min_le_min (by linarith) he) (by positivity) (hk0.trans hk)
  · exact mul_le_mul
      (mul_le_mul hq (Real.rpow_le_rpow hf0 hf (by norm_num)) (by positivity) (hq0.trans hq))
      (Real.rpow_le_rpow he0 he (by norm_num)) (by positivity) (by positivity)

theorem actual_sharp_band_high_all (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ A K Q L0 : ℝ, 0<A ∧ 0≤K ∧ 0<Q ∧ 16≤L0 ∧
    ∀ L : ℝ, L0≤L → ∀ epsilon T R W w m : ℝ,
      0<epsilon → epsilon≤R → 0<T → T≤R → T≤1/4 → Real.log (R/T)≤L →
      T/2≤Real.exp (-(L^(97/100:ℝ))) → 0<W → 0<w → w≤W →
      5*(w/W)≤1/2 → Real.exp (L^(9/10:ℝ)) ≤ m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ) (F E ratio : ℝ),
      0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+K*(1+L)*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ) := by
  obtain ⟨D,A,L0,hD,hA,hL0,hfin⟩ := actual_cutoff_band_high hVariation hLL
    hilbertAnnularSymbol p 1 2 (1/2) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hilbertAnnularSymbol_support hp
  obtain ⟨B1,C1,hB1,hC1,hdecomp⟩ := hilbertTimeDecomposition_bound hH
  obtain ⟨B2,hB2,hmidlong⟩ := hilbertMiddleLong_bound
  obtain ⟨C2,hC2,hshortlong⟩ := hilbertShortLong_bound hH
  let P := verticalProjectionCost p
  let P' := verticalProjectionCost (verticalDerivativeProfile p)
  let B := B1+B2
  let K := P*B+2*P+2*D*P'
  let Q := (C1+C2)*P
  have hP : 0<P := verticalProjectionCost_pos p
  have hP' : 0<P' := verticalProjectionCost_pos _
  have hB : 0≤B := add_nonneg hB1 hB2
  have hK : 0≤K := by dsimp [K]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  refine ⟨A,K,Q,L0,hA,hK,hQ,hL0,?_⟩
  intro L hL epsilon T R W w m he heR hT hTR hTquarter hlogRT htime hW hw hwW hratio hmlo hmhi hWeq
    field hfield hfieldBound f g F E ratio hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  let u := fun z : ℝ×ℝ => field (planeCoordinates z)
  let S := schwartzVerticalProjection p w 0 f
  let H := kernelPairing (sharpTimeKernel epsilon R) u S g
  let rem := K*(1+L)*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ)
  have hL0' : 0≤L := by linarith only [hL0,hL]
  have hu : LipschitzWith 2 u := by simpa only [u,mul_one] using product_slope_lipschitz field hfield
  have hub (z) : |u z|≤1 := (hfieldBound _).trans (by norm_num)
  have hwidth : r-l≤1/4 := by linarith only [hstrip]
  have hlog0 : 0≤Real.log (R/T) := Real.log_nonneg ((one_le_div hT).2 hTR)
  have hmodel0 : 0≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by positivity
  have hpromote (z : ℂ) (k q : ℝ) (hk0 : 0≤k) (hk : k≤K*(1+L)) (hq0 : 0≤q) (hq : q≤Q)
      (hb : ‖z‖≤k*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)+
        q*(∫ z, ‖f z‖ ∂planeMeasure)^(2/3:ℝ)*(∫ z, ‖g z‖ ∂planeMeasure)^(1/3:ℝ)) : ‖z‖ ≤ rem := by
    exact hb.trans (restricted_remainder_mono F E _ _ k (K*(1+L)) q Q
      (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
      hf1 hg1 hk0 hk hq0 hq)
  have hbase (b s : ℝ) (hb : b≤B) (hs : s≤D*w) :
      P*(b+2*Real.log (R/T))+2*s*P'/w≤K*(1+L) := by
    have hsmall : 2*s*P'/w≤2*D*P' := by
      calc
        _ ≤ 2*(D*w)*P'/w := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hP'.le) hw.le
        _ = _ := by field_simp
    have hc0 : P*B+2*D*P'≤K := by dsimp [K]; linarith only [hP]
    have hc1 : 2*P≤K := by
      dsimp [K]
      nlinarith only [mul_nonneg hP.le hB, mul_nonneg hD.le hP'.le]
    calc
      _ ≤ P*(B+2*L)+2*D*P' := add_le_add
        (mul_le_mul_of_nonneg_left (by linarith) hP.le) hsmall
      _ = (P*B+2*D*P')+(2*P)*L := by ring
      _ ≤ K+K*L := add_le_add hc0 (mul_le_mul_of_nonneg_right hc1 hL0')
      _ = _ := by ring
  have hQ1 : C1*P≤Q := by dsimp [Q]; nlinarith only [mul_pos hC2 hP]
  have hQ2 : C2*P≤Q := by dsimp [Q]; nlinarith only [mul_pos hC1 hP]
  have hfinish (N : ℕ) (hlength : ∀ j : Fin N, D*w≤(T/2)/(2:ℝ)^j.val)
      (herr : ‖H-kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u S g‖ ≤ rem) :
      ‖H‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+rem := by
    have hmain := hfin L hL N (T/2) W w (by positivity) hW hw hwW hratio (by norm_num) htime
      hlength field hfield hfieldBound f g F E ratio hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2
      l r m hstrip hfstrip hgstrip hmlo hmhi hWeq
    exact (norm_le_insert' H _).trans (add_le_add hmain herr)
  change ‖H‖≤_
  rw [add_assoc]
  change ‖H‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+rem
  by_cases hET : T≤epsilon
  · have hb := sharpHilbertProjection_long_pairing epsilon R he heR u hu p w hw f g hf hg
      l r hwidth hfstrip hgstrip
    have hlogE : Real.log (R/epsilon)≤Real.log (R/T) := by
      apply Real.log_le_log (div_pos (he.trans_le heR) he)
      exact div_le_div_of_nonneg_left (he.trans_le heR).le hT hET
    have hk0 : 0≤P*(2*Real.log (R/epsilon)) :=
      mul_nonneg hP.le (mul_nonneg (by norm_num) (Real.log_nonneg ((one_le_div he).2 heR)))
    have hk : P*(2*Real.log (R/epsilon))≤K*(1+L) := by
      apply le_trans _ (hbase 0 0 hB (by positivity))
      calc
        _ ≤ P*(2*Real.log (R/T)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlogE (by norm_num)) hP.le
        _ = _ := by ring
    have hh := hpromote H _ 0 hk0 hk le_rfl hQ.le (by simpa only [zero_mul,add_zero] using hb)
    exact hh.trans (le_add_of_nonneg_left hmodel0)
  · have heT : epsilon≤T := (lt_of_not_ge hET).le
    by_cases hTD : T≤D*w
    · have hb := hshortlong epsilon T R he heT hTR hTquarter (3/2) 3 (Or.inl rfl)
        (by norm_num [Real.holderConjugate_iff]) u hu hub p w hw f g hf hg l r hwidth hfstrip hgstrip
      have hk0 : 0≤P*(2*Real.log (R/T))+2*T*P'/w := by positivity
      have hk := hbase 0 T hB hTD
      have hh := hpromote H _ (C2*P) hk0 (by simpa only [zero_add] using hk) (by positivity) hQ2
        (by norm_num only [one_div_div] at hb; exact hb)
      exact hh.trans (le_add_of_nonneg_left hmodel0)
    · have hDT : D*w≤T := (lt_of_not_ge hTD).le
      by_cases heD : epsilon≤D*w
      · obtain ⟨N,hlo,_,hb⟩ := hdecomp epsilon (D*w) T R he heD hDT hTR (hDT.trans hTquarter)
        have herr := hb (3/2) 3 (Or.inl rfl) (by norm_num [Real.holderConjugate_iff])
          u hu hub p w hw f g hf hg l r hwidth hfstrip hgstrip
        have hk0 : 0≤P*(B1+2*Real.log (R/T))+2*(D*w)*P'/w := by positivity
        apply hfinish N (dyadic_time_lower N T (D*w) hT hlo)
        exact hpromote _ _ (C1*P) hk0 (hbase B1 (D*w) (by dsimp [B]; linarith only [hB2]) le_rfl)
          (by positivity) hQ1 (by norm_num only [one_div_div] at herr; exact herr)
      · obtain ⟨N,hlo,_,hb⟩ := hmidlong epsilon T R he heT hTR
        have herr := hb u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
        have hk0 : 0≤P*(B2+2*Real.log (R/T)) := by positivity
        have hk : P*(B2+2*Real.log (R/T))≤K*(1+L) := by
          simpa only [mul_zero,zero_mul,zero_div,add_zero] using
            hbase B2 0 (by dsimp [B]; linarith only [hB1]) (by positivity)
        apply hfinish N (dyadic_time_lower N T (D*w) hT ((lt_of_not_ge heD).le.trans hlo))
        exact hpromote _ _ 0 hk0 hk le_rfl hQ.le (by simpa only [zero_mul,add_zero] using herr)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpBandUniformHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source time/width choices and exponential absorption give the
uniform high-disparity restricted estimate for every sharp truncation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem actual_sharp_band_uniform_high_oai (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C L0 : ℝ, 0<C ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ) (F E ratio : ℝ),
      0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤C*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨A,K,Q,Lbase,hA,hK,hQ,hLbase,hraw⟩ :=
    actual_sharp_band_high_all hVariation hLL hH p hp
  obtain ⟨Lpar,hpar⟩ := eventually_atTop.1 eventually_sharpSourceParameters
  obtain ⟨Ldec,hdec⟩ := eventually_atTop.1 (eventually_remainder_decay K Q hK)
  let L0 := max Lbase (max Lpar Ldec)
  refine ⟨A+1,L0,by linarith,hLbase.trans (le_max_left _ _),?_⟩
  intro L hL epsilon R w he heR hRquarter hw field hfield hfieldBound f g F E ratio
    hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hLp : Lpar≤L := (le_trans (le_max_left Lpar Ldec) (le_max_right Lbase (max Lpar Ldec))).trans hL
  have hLd : Ldec≤L := (le_trans (le_max_right Lpar Ldec) (le_max_right Lbase (max Lpar Ldec))).trans hL
  obtain ⟨hL1,_,hm10⟩ := hpar L hLp
  have hR : 0<R := he.trans_le heR
  let T := min R (sharpSourceTime L)
  let m := sharpSourceWidthRatio L
  let W := m*w
  have hT : 0<T := lt_min hR (sharpSourceTime_pos L)
  have hTR : T≤R := min_le_left _ _
  have hTS : T ≤ sharpSourceTime L := min_le_right _ _
  have htime : T/2≤Real.exp (-(L^(97/100:ℝ))) := by
    change T/2 ≤ sharpSourceTime L
    linarith
  have hlogRT : Real.log (R/T)≤L := by
    by_cases hRS : R ≤ sharpSourceTime L
    · simp only [T,min_eq_left hRS,div_self hR.ne',Real.log_one]
      exact le_trans (by norm_num) hL1
    · rw [show T=sharpSourceTime L from min_eq_right (le_of_not_ge hRS)]
      exact sharpSourceTime_log L R hL1 hR (by linarith)
  have hgeometry := sharpSourceWidthRatio_geometry L w hw hm10
  have hmpos : 0 < m := sharpSourceWidthRatio_pos L
  have hbound := hraw L hLb epsilon T R W w m he heR hT hTR (hTR.trans hRquarter)
    hlogRT htime (mul_pos hmpos hw) hw hgeometry.1 hgeometry.2 le_rfl
    (by change m≤2*m; linarith) rfl field hfield hfieldBound f g F E ratio
    hF hE hr heq hlog hf hg hf1 hg1 hf2 hg2 l r hstrip hfstrip hgstrip
  exact absorb_sharp_remainders _ A K Q F E ratio L hK (by linarith) hF hr heq hlog
    (hdec L hLd) hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high_oai := @OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high_oai
