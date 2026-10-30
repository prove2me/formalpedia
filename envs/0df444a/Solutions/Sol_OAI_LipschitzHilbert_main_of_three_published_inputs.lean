-- Prove2me | solution 1 for OAI.LipschitzHilbert.main_of_three_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:37:44.349179+00:00
-- url     : https://prove2.me/submissions/b685f04f-17cf-4454-9a15-5b297618444d

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_Truncation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The relation between the two-sided hard cutoff and positive-time symmetrization. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

theorem directionalKernel_intervalIntegrable
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ} (hf : Continuous f)
    (x : DirectionPlane) (a b : ℝ) (hzero : ∀ t ∈ uIcc a b, t ≠ 0) :
    IntervalIntegrable (directionalKernel v f x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hs : Continuous (fun t : ℝ => sample v t x) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  exact (continuousOn_id.inv₀ hzero).smul (hf.comp hs).continuousOn

/-- Symmetrization is an exact identity for every positive hard inner cutoff. -/
theorem twoSidedTruncation_eq_shortTransform
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ} (hf : Continuous f)
    {ε a : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (x : DirectionPlane) :
    twoSidedTruncation v ε a f x = shortTransform v ε a f x := by
  have hp : IntervalIntegrable (directionalKernel v f x) volume ε a :=
    directionalKernel_intervalIntegrable v hf x ε a (by
      intro t ht
      rw [uIcc_of_le ha] at ht
      exact ne_of_gt (hε.trans_le ht.1))
  have hn : IntervalIntegrable (fun t => directionalKernel v f x (-t)) volume ε a := by
    have hs : Continuous (fun t : ℝ => sample v (-t) x) :=
      continuous_const.sub (continuous_id.neg.smul continuous_const)
    apply ContinuousOn.intervalIntegrable
    have hi : ContinuousOn (fun t : ℝ => (-t)⁻¹) (uIcc ε a) := by
      apply continuousOn_id.neg.inv₀
      intro t ht
      rw [uIcc_of_le ha] at ht
      exact neg_ne_zero.mpr (ne_of_gt (hε.trans_le ht.1))
    exact hi.smul (hf.comp hs).continuousOn
  unfold twoSidedTruncation shortTransform
  rw [← intervalIntegral.integral_comp_neg (directionalKernel v f x),
    ← intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [directionalKernel, inv_neg, neg_smul, smul_sub]
  abel

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothPrincipalValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise symmetric principal values for smooth inputs. At a fixed
output point the direction is frozen, so differentiability of the input
removes the singularity in the positive-time symmetric quotient. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

theorem shortTransform_tendsto_smoothPrincipalValue
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ}
    (hf : Differentiable ℝ f) {a : ℝ} (ha : 0 < a) (x : DirectionPlane) :
    Tendsto (fun ε : ℝ => shortTransform v ε a f x) (𝓝[>] 0)
      (𝓝 (smoothPrincipalValue v a f x)) := by
  let g := fun t : ℝ => f (sample v t x)-f (sample v (-t) x)
  have hg : Differentiable ℝ g := by
    dsimp only [g,sample]
    fun_prop
  have hg0 : g 0 = 0 := by simp [g,sample]
  let reg := Function.update (fun t : ℝ => t⁻¹ • g t) 0 (deriv g 0)
  have hreg : Continuous reg := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t = 0
    · subst t
      apply continuousAt_update_same.mpr
      simpa only [zero_add,hg0,sub_zero] using (hg 0).hasDerivAt.tendsto_slope_zero
    · apply (continuousAt_update_of_ne ht).mpr
      exact (continuousAt_id.inv₀ ht).smul hg.continuous.continuousAt
  have hcont : Continuous (fun ε : ℝ => ∫ t in ε..a, reg t) := by
    have hc := (intervalIntegral.continuous_primitive (μ := volume)
      (fun l r => hreg.intervalIntegrable l r) a).neg
    have he : (fun ε : ℝ => ∫ t in ε..a, reg t) =
        (fun ε : ℝ => -(∫ t in a..ε, reg t)) := by
      funext ε
      exact intervalIntegral.integral_symm a ε
    rw [he]
    exact hc
  have heq : (fun ε : ℝ => shortTransform v ε a f x) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ t in ε..a, reg t) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
    change 0 < ε at hε
    unfold shortTransform
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hεa.le] at ht
    have ht0 : t ≠ 0 := (hε.trans_le ht.1).ne'
    exact (Function.update_of_ne ht0 (deriv g 0) (fun t : ℝ => t⁻¹ • g t)).symm
  exact (hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds).congr' heq.symm

end LipschitzHilbert

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

theorem smoothPrincipalValue_measurable
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) : Measurable (smoothPrincipalValue v a f) := by
  let ε := fun n : ℕ => a/((n:ℝ)+1)
  have hpos (n : ℕ) : 0 < ε n := div_pos ha (by positivity)
  have hle (n : ℕ) : ε n ≤ a := by
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htend : Tendsto ε atTop (𝓝 (0:ℝ)) := by
    simpa only [ε,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_const_nhds (x := a)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hright : Tendsto ε atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend,Eventually.of_forall hpos⟩
  apply measurable_of_tendsto_metrizable
    (fun n => (shortTransform_continuous hv hf.continuous (hpos n) (hle n)).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  exact (shortTransform_tendsto_smoothPrincipalValue v hf ha x).comp hright

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothPrincipalValueBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform truncation bounds pass to the symmetric principal value.
Fatou's lemma yields the strong bound, and Chebyshev's inequality gives
its weak `(2,2)` consequence. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace LipschitzHilbert

theorem smoothPrincipalValue_eLpNorm_le
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞}
    (hbound : ∀ ε : ℝ, 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C) :
    eLpNorm (smoothPrincipalValue v a f) 2 volume ≤ C := by
  let ε := fun n : ℕ => a/(((n+1:ℕ):ℝ)+1)
  have hpos (n : ℕ) : 0 < ε n := div_pos ha (by positivity)
  have hlt (n : ℕ) : ε n < a := by
    apply (div_lt_iff₀ (by positivity : 0 < ((n+1:ℕ):ℝ)+1)).mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htend : Tendsto ε atTop (𝓝 (0:ℝ)) := by
    have hs := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp
      (tendsto_add_atTop_nat 1)
    simpa only [ε,div_eq_mul_inv,one_mul,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := a)).mul hs
  have hright : Tendsto ε atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend,Eventually.of_forall hpos⟩
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall (fun n => hbound (ε n) (hpos n) (hlt n)))
    (fun n => (shortTransform_continuous hv hf.continuous (hpos n)
      (hlt n).le).aestronglyMeasurable)
  exact Eventually.of_forall fun x =>
    (shortTransform_tendsto_smoothPrincipalValue v hf ha x).comp hright

theorem smoothPrincipalValue_memLp
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞} (hC : C < ∞)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C) :
    MemLp (smoothPrincipalValue v a f) 2 volume :=
  ⟨(smoothPrincipalValue_measurable hv hf ha).aestronglyMeasurable,
    (smoothPrincipalValue_eLpNorm_le hv hf ha hbound).trans_lt hC⟩

theorem smoothPrincipalValue_weak_two
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞}
    (hbound : ∀ ε : ℝ, 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C)
    {level : ℝ≥0∞} (hlevel : level ≠ 0) (hleveltop : level ≠ ∞) :
    volume {x | level < ‖smoothPrincipalValue v a f x‖ₑ} ≤ level⁻¹ ^ 2 * C ^ 2 := by
  have hmarkov := meas_ge_le_mul_pow_eLpNorm_enorm (hf := (smoothPrincipalValue_measurable hv hf ha).aestronglyMeasurable) (p := (2:ℝ≥0∞)) volume
    (by norm_num) (by norm_num) hlevel (by exact fun h => (hleveltop h).elim)
    (f := smoothPrincipalValue v a f)
  have hnorm := smoothPrincipalValue_eLpNorm_le hv hf ha hbound
  calc
    volume {x | level < ‖smoothPrincipalValue v a f x‖ₑ} ≤
        volume {x | level ≤ ‖smoothPrincipalValue v a f x‖ₑ} :=
      measure_mono (by
        intro x hx
        change level < ‖smoothPrincipalValue v a f x‖ₑ at hx
        change level ≤ ‖smoothPrincipalValue v a f x‖ₑ
        exact le_of_lt hx)
    _ ≤ level⁻¹ ^ 2 * eLpNorm (smoothPrincipalValue v a f) 2 volume ^ 2 := by
      simpa using hmarkov
    _ ≤ level⁻¹ ^ 2 * C ^ 2 := by gcongr

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SmoothPrincipalValueLinear
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the actual symmetric principal value on smooth inputs. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert

theorem shortIntegrand_intervalIntegrable
    (v : DirectionPlane → DirectionPlane) {f : DirectionPlane → ℂ}
    (hf : Continuous f) {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a)
    (x : DirectionPlane) :
    IntervalIntegrable (fun t : ℝ =>
      t⁻¹ • (f (sample v t x)-f (sample v (-t) x))) volume ε a := by
  apply ContinuousOn.intervalIntegrable
  have hs : Continuous (fun t : ℝ => sample v t x) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hn : Continuous (fun t : ℝ => sample v (-t) x) :=
    continuous_const.sub (continuous_id.neg.smul continuous_const)
  apply (continuousOn_id.inv₀ ?_).smul ((hf.comp hs).sub (hf.comp hn)).continuousOn
  intro t ht
  rw [uIcc_of_le hεa] at ht
  exact (hε.trans_le ht.1).ne'

theorem shortTransform_add
    (v : DirectionPlane → DirectionPlane) {f g : DirectionPlane → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) (x : DirectionPlane) :
    shortTransform v ε a (f+g) x =
      shortTransform v ε a f x + shortTransform v ε a g x := by
  unfold shortTransform
  have heq : (fun t : ℝ => t⁻¹ •
      ((f+g) (sample v t x)-(f+g) (sample v (-t) x))) =
      (fun t : ℝ => t⁻¹ • (f (sample v t x)-f (sample v (-t) x)) +
        t⁻¹ • (g (sample v t x)-g (sample v (-t) x))) := by
    funext t
    simp only [Pi.add_apply, smul_sub, smul_add]
    abel
  rw [heq]
  exact intervalIntegral.integral_add
    (shortIntegrand_intervalIntegrable v hf hε hεa x)
    (shortIntegrand_intervalIntegrable v hg hε hεa x)

theorem shortTransform_smul
    (v : DirectionPlane → DirectionPlane) (c : ℂ)
    (f : DirectionPlane → ℂ) (ε a : ℝ) (x : DirectionPlane) :
    shortTransform v ε a (c • f) x = c • shortTransform v ε a f x := by
  unfold shortTransform
  have heq : (fun t : ℝ => t⁻¹ •
      ((c • f) (sample v t x)-(c • f) (sample v (-t) x))) =
      (fun t : ℝ => c • (t⁻¹ • (f (sample v t x)-f (sample v (-t) x)))) := by
    funext t
    simp only [Pi.smul_apply, ← smul_sub]
    exact smul_comm _ _ _
  rw [heq,intervalIntegral.integral_smul]

theorem smoothPrincipalValue_add
    (v : DirectionPlane → DirectionPlane) {f g : DirectionPlane → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {a : ℝ} (ha : 0 < a) :
    smoothPrincipalValue v a (f+g) =
      smoothPrincipalValue v a f + smoothPrincipalValue v a g := by
  funext x
  apply tendsto_nhds_unique (shortTransform_tendsto_smoothPrincipalValue v (hf.add hg) ha x)
  apply ((shortTransform_tendsto_smoothPrincipalValue v hf ha x).add
    (shortTransform_tendsto_smoothPrincipalValue v hg ha x)).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
  exact (shortTransform_add v hf.continuous hg.continuous hε hεa.le x).symm

theorem smoothPrincipalValue_smul
    (v : DirectionPlane → DirectionPlane) (c : ℂ)
    {f : DirectionPlane → ℂ} (hf : Differentiable ℝ f)
    {a : ℝ} (ha : 0 < a) :
    smoothPrincipalValue v a (c • f) = c • smoothPrincipalValue v a f := by
  funext x
  apply tendsto_nhds_unique
    (shortTransform_tendsto_smoothPrincipalValue v (hf.const_smul c) ha x)
  apply ((shortTransform_tendsto_smoothPrincipalValue v hf ha x).const_smul c).congr'
  exact Eventually.of_forall fun ε => (shortTransform_smul v c f ε a x).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SmoothPrincipalValueExtension
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density consequence of a uniform short-transform estimate. The
extension agrees almost everywhere with the actual symmetric principal
value on every Schwartz input and has the same operator bound. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem exists_smoothPrincipalValue_extension
    {v : DirectionPlane → DirectionPlane} (hv : Continuous v)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0}
    (hbound : ∀ (f : SchwartzMap DirectionPlane ℂ) (ε : ℝ), 0 < ε → ε < a →
      eLpNorm (shortTransform v ε a f) 2 volume ≤ C*eLpNorm f 2 volume) :
    ∃ T : Lp ℂ 2 (volume : Measure DirectionPlane) →L[ℂ]
        Lp ℂ 2 (volume : Measure DirectionPlane),
      ‖T‖ ≤ C ∧ ∀ f : SchwartzMap DirectionPlane ℂ,
        (T (f.toLp 2 volume) : DirectionPlane → ℂ) =ᵐ[volume]
          smoothPrincipalValue v a f := by
  have hmem (f : SchwartzMap DirectionPlane ℂ) :
      MemLp (smoothPrincipalValue v a f) 2 volume :=
    smoothPrincipalValue_memLp hv f.differentiable ha
      (ENNReal.mul_lt_top (by simp) (f.memLp 2 volume).eLpNorm_lt_top)
      (hbound f)
  let S : SchwartzMap DirectionPlane ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure DirectionPlane) :=
    { toFun := fun f => (hmem f).toLp (smoothPrincipalValue v a f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(hmem (f+g)).coeFn_toLp,
          (hmem f).coeFn_toLp, (hmem g).coeFn_toLp,
          Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _)] with x hx hf hg hadd
        rw [hx,hadd]
        simp only [Pi.add_apply,hf,hg]
        exact congrFun (smoothPrincipalValue_add v f.differentiable g.differentiable ha) x
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
          Lp.coeFn_smul c ((hmem f).toLp _)] with x hx hf hsmul
        simp only [RingHom.id_apply]
        rw [hx,hsmul]
        simp only [Pi.smul_apply,hf]
        exact congrFun (smoothPrincipalValue_smul v c f.differentiable ha) x }
  let inclusion := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure DirectionPlane)).toLinearMap
  have hdense : DenseRange inclusion :=
    SchwartzMap.denseRange_toLpCLM (F := ℂ) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  have hnorm (f : SchwartzMap DirectionPlane ℂ) : ‖S f‖ ≤ (C:ℝ)*‖inclusion f‖ := by
    change ‖(hmem f).toLp (smoothPrincipalValue v a f)‖ ≤ (C:ℝ)*‖f.toLp 2 volume‖
    rw [Lp.norm_toLp,SchwartzMap.norm_toLp]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (f.memLp 2 volume).eLpNorm_ne_top)
      (smoothPrincipalValue_eLpNorm_le hv f.differentiable ha (hbound f))
    simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using h
  refine ⟨S.extendOfNorm inclusion,
    LinearMap.opNorm_extendOfNorm_le hdense C.property hnorm, ?_⟩
  intro f
  have heq := LinearMap.extendOfNorm_eq (f := S) (e := inclusion)
    hdense ⟨C,hnorm⟩ f
  change ((S.extendOfNorm inclusion) (inclusion f) : DirectionPlane → ℂ) =ᵐ[volume] _
  rw [heq]
  exact (hmem f).coeFn_toLp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortTransformExtension
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dense Schwartz-space realization of a uniformly bounded hard
truncation extends to a bounded linear operator on L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem exists_shortTransform_extension (v : DirectionPlane → DirectionPlane) (hv : Continuous v)
    (epsilon R : ℝ) (he : 0<epsilon) (heR : epsilon≤R) (C : ℝ≥0)
    (hbound : ∀ f : SchwartzMap DirectionPlane ℂ,
      eLpNorm (shortTransform v epsilon R f) 2 volume≤C*eLpNorm f 2 volume) :
    ∃ T : Lp ℂ 2 (volume : Measure DirectionPlane) →L[ℂ] Lp ℂ 2 volume,
      ‖T‖≤C ∧ ∀ f : SchwartzMap DirectionPlane ℂ,
        (T (f.toLp 2 volume) : DirectionPlane → ℂ)=ᵐ[volume] shortTransform v epsilon R f := by
  have hmem (f : SchwartzMap DirectionPlane ℂ) : MemLp (shortTransform v epsilon R f) 2 volume :=
    ⟨(shortTransform_continuous hv f.continuous he heR).aestronglyMeasurable,
      (hbound f).trans_lt (ENNReal.mul_lt_top (by simp) (f.memLp 2 volume).eLpNorm_lt_top)⟩
  let S : SchwartzMap DirectionPlane ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure DirectionPlane) :=
    { toFun := fun f => (hmem f).toLp (shortTransform v epsilon R f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(hmem (f+g)).coeFn_toLp,(hmem f).coeFn_toLp,(hmem g).coeFn_toLp,
          Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _)] with x hx hf hg hadd
        rw [hx,hadd]
        simp only [Pi.add_apply,hf,hg]
        exact shortTransform_add v f.continuous g.continuous he heR x
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hmem (c • f)).coeFn_toLp,(hmem f).coeFn_toLp,
          Lp.coeFn_smul c ((hmem f).toLp _)] with x hx hf hsmul
        simp only [RingHom.id_apply]
        rw [hx,hsmul]
        simp only [Pi.smul_apply,hf]
        exact shortTransform_smul v c f epsilon R x }
  let inclusion := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure DirectionPlane)).toLinearMap
  have hdense : DenseRange inclusion :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠∞)
  have hnorm (f : SchwartzMap DirectionPlane ℂ) : ‖S f‖≤(C:ℝ)*‖inclusion f‖ := by
    change ‖(hmem f).toLp (shortTransform v epsilon R f)‖≤(C:ℝ)*‖f.toLp 2 volume‖
    rw [Lp.norm_toLp,SchwartzMap.norm_toLp]
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (f.memLp 2 volume).eLpNorm_ne_top) (hbound f)
    simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using h
  refine ⟨S.extendOfNorm inclusion,LinearMap.opNorm_extendOfNorm_le hdense C.property hnorm,?_⟩
  intro f
  have heq := LinearMap.extendOfNorm_eq (f:=S) (e:=inclusion) hdense ⟨C,hnorm⟩ f
  change ((S.extendOfNorm inclusion) (inclusion f) : DirectionPlane → ℂ)=ᵐ[volume] _
  rw [heq]
  exact (hmem f).coeFn_toLp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_ConditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Theorem 1.1 of the supplied manuscript, conditional on the four
precisely cited published inputs. The principal value is the actual
pointwise symmetric limit on Schwartz functions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

theorem conditional_main (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C := by
  obtain ⟨B,hB,hbound⟩ := conditional_uniform_truncation hVariation hLL hH hReassembly
  let C : ℝ≥0 := ⟨B,hB.le⟩
  let a : ℝ := 1/1000000
  have ha : 0<a := by norm_num [a]
  have hBcoe : ENNReal.ofReal B=(C:ℝ≥0∞) := by
    change ENNReal.ofReal (C:ℝ)=(C:ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  refine ⟨a,⟨ha,by norm_num [a]⟩,C,hB,?_⟩
  intro v hv hunit
  have hb (f : SchwartzMap Plane ℂ) (epsilon : ℝ) (he : 0<epsilon) (hea : epsilon<a) :
      eLpNorm (shortTransform v epsilon a f) 2 volume≤C*eLpNorm f 2 volume := by
    have h := hbound 1 (by norm_num) epsilon a he hea.le (by norm_num [a]) v hv hunit f
    rw [ENNReal.ofReal_mul hB.le,SchwartzMap.norm_toLp,
      ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top,hBcoe] at h
    exact h
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro epsilon he hea f
    have heq : twoSidedTruncation v epsilon a f=shortTransform v epsilon a f := by
      funext x
      exact twoSidedTruncation_eq_shortTransform v f.continuous he hea.le x
    rw [heq]
    exact hb f epsilon he hea
  · intro f
    exact smoothPrincipalValue_eLpNorm_le hv.continuous f.differentiable ha (hb f)
  · intro f level hl hlfin
    exact smoothPrincipalValue_weak_two hv.continuous f.differentiable ha (hb f) hl hlfin
  · intro epsilon he hea
    obtain ⟨T,hT,hTf⟩ := exists_shortTransform_extension v hv.continuous epsilon a he hea.le C
      (fun f => hb f epsilon he hea)
    refine ⟨T,hT,?_⟩
    intro f
    have heq : twoSidedTruncation v epsilon a f=shortTransform v epsilon a f := by
      funext x
      exact twoSidedTruncation_eq_shortTransform v f.continuous he hea.le x
    rw [heq]
    exact hTf f
  · exact exists_smoothPrincipalValue_extension hv.continuous ha hb

end LipschitzHilbert

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

theorem main_of_three_published_inputs_oai (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  conditional_main hVariation hLL hH bandToFullInput_proved

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.main_of_three_published_inputs_oai := @OAI.LipschitzHilbert.main_of_three_published_inputs_oai
