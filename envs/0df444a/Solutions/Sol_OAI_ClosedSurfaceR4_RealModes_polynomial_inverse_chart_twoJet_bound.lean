-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:51.898211+00:00
-- url     : https://prove2.me/submissions/6c748870-b6fb-4f52-8983-1fa01b7db5c7

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI011

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith


lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.sub {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hbf.add hU hs hf hg.neg (hbg.neg hU hg)

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)



lemma WeightedBound.comp {U : Set E} {V : Set F} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {s C D : ℝ} {m : ℕ} {f : E → F} {g : F → G} (hs : 0 < s) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hbf : WeightedBound U s m C f)
    (hbg : ∀ j ≤ m, ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ D) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ (C / s) ^ i := by
    have hp : C ≤ C ^ i := by
      simpa only [pow_one] using pow_le_pow_right₀ hC hi1
    calc
      _ ≤ C / s ^ i := hbf.deriv_le hs (hij.trans hj) hx
      _ ≤ C ^ i / s ^ i := div_le_div_of_nonneg_right hp (pow_nonneg hs.le _)
      _ = _ := (div_pow C s i).symm
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx
    (fun i hij => hbg i (hij.trans hj) x hx) hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * D * (C / s) ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      gcongr




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for the finite higher-jet monomials in paper 094-01.
The loss exponent adds under products and is unchanged when the output
order increases; only the multiplicative constant depends on that order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.mul_real {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : A → ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) :=
  hbf.smul_real hU hs hC hD hf hg hbg

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual positional two-jet on a fixed bounded domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem directional_of_prefix {U : Set E} (hU : IsOpen U)
    {f : E → V} (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedBound U 1 j (C/s^(j-1)) f)
    (v : E) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m C (fun x => fderiv ℝ f x v) := by
  intro j hj x hx
  have hh := ((hb (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
    j le_rfl x hx
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good phase directions remain good in their actual nonlinear phase charts. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverse_chart_derivative (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ Base := by
  have hh : e ∘ e.symm =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  rw [← fderiv_comp y (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
    hh.fderiv_eq,fderiv_id]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseTwoJetBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed phase charts transfer original-coordinate prefix bounds to the
two-jet profiles needed by the actual mean and quadratic solvers. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4
open WeightedEstimates

namespace RealModes
open SmallModes

theorem realTwoJet_prefix_bound_on {U : Set Base} (hU : IsOpen U)
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m + 2, WeightedBound U 1 j (C / s ^ (j - 2)) F) :
    WeightedBound U s m C (realTwoJet F) := by
  have hfirst (v : Base) (hv : ‖v‖ = 1) (j : ℕ) (hj : j ≤ m + 1) :
      WeightedBound U 1 j (C / s ^ (j - 1)) (coordDeriv v F) := by
    have hh := (hb (j + 1) (by omega)).directional hU zero_lt_one hF.contDiffOn v
    change WeightedBound U 1 j (C / s ^ (j - 1)) (fun x => fderiv ℝ F x v)
    have he : j + 1 - 2 = j - 1 := by omega
    simpa only [hv,one_mul,div_one,he] using hh
  have hfirst' (v : Base) (hv : ‖v‖ = 1) :
      WeightedBound U s m C (coordDeriv v F) := by
    apply directional_of_prefix hU hF hs hC _ v hv.le
    intro j hj
    apply (hb j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have hsecond (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      WeightedBound U s m C (coordDeriv v (coordDeriv w F)) :=
    directional_of_prefix hU (contDiff_real_coordDeriv hF w) hs hC (hfirst w hw) v hv.le
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  change WeightedBound U s m C (fun x i => realTwoJet F x i)
  apply WeightedBound.pi hU.uniqueDiffOn hs hC
  · intro i
    fin_cases i <;> first
      | exact (contDiff_real_coordDeriv hF _).contDiffOn
      | exact (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF _) _).contDiffOn
  · intro i
    fin_cases i
    · exact hfirst' dx hx
    · exact hfirst' dy hy
    · exact hsecond dx dx hx hx
    · exact hsecond dx dy hx hy
    · exact hsecond dy dy hy hy

end RealModes

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedReciprocal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weighted bounds for the reciprocal operations occurring in
metric inversion and normal reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) x‖ =
      (j.factorial : ℝ)*‖x⁻¹‖^(j+1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have h := iteratedDerivWithin_one_div j isOpen_compl_singleton
    (show x ∈ ({0}ᶜ : Set ℝ) from hx)
  simp only [one_div] at h
  rw [h,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Real.norm_natCast,norm_zpow]
  have he : (-1-(j : ℤ)) = -((j+1 : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow,← norm_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both the input size and inverse denominator enter polynomially at each
fixed derivative order. There is no compact-range hypothesis. -/
theorem WeightedBound.inv_real {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C K : ℝ} {m : ℕ} {f : E → ℝ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x ∈ U, f x ≠ 0)
    (hInv : ∀ x ∈ U, ‖(f x)⁻¹‖ ≤ K) (hb : WeightedBound U s m C f) :
    WeightedBound U s m ((m.factorial : ℝ)^2*K^(m+1)*C^m) (fun x => (f x)⁻¹) := by
  have hV : UniqueDiffOn ℝ ({0}ᶜ : Set ℝ) := isOpen_compl_singleton.uniqueDiffOn
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) ({0}ᶜ) :=
    contDiffOn_id.inv (fun x hx => hx)
  have hD : 0 ≤ (m.factorial : ℝ)*K^(m+1) := by positivity
  have hd : ∀ j ≤ m, ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j (fun y : ℝ => y⁻¹) ({0}ᶜ) (f x)‖ ≤
        (m.factorial : ℝ)*K^(m+1) := by
    intro j hj x hx
    rw [norm_iteratedFDerivWithin_inv j (hne x hx)]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le hj
    · exact (pow_le_pow_left₀ (norm_nonneg _) (hInv x hx) _).trans
        (pow_le_pow_right₀ hK (by omega))
    · positivity
    · positivity
  have hh := hb.comp hU hV hs hC hD hf hg (fun x hx => hne x hx) hd
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.comp {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) (hge : ∀ x, 1 ≤ x → 1 ≤ g x) :
    HasPolynomialBound (fun x => f (g x)) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨e*d,C*D^d,one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD),?_⟩
  intro x hx
  refine ⟨(hf (g x) (hge x hx)).1,?_⟩
  calc
    f (g x) ≤ C*(g x)^d := (hf (g x) (hge x hx)).2
    _ ≤ C*(D*x^e)^d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hg x hx).1 (hg x hx).2 _) (zero_le_one.trans hC)
    _ = (C*D^d)*x^(e*d) := by rw [mul_pow,pow_mul]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneAdjugate
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit two-dimensional inverse matrix used for phase charts. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma planeAdjugate_comp (A : Base →L[ℝ] Base) :
    (planeAdjugate A).comp A = coordDet A • ContinuousLinearMap.id ℝ Base := by
  apply ContinuousLinearMap.ext
  intro v
  change planeAdjugate A (A v) = coordDet A • v
  rw [planeAdjugate_apply,linear_apply_basis A v]
  apply Prod.ext <;>
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,coordDet] <;> ring

lemma planeAdjugateOperator_norm_le : ‖planeAdjugateOperator‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) planeAdjugate_norm_le

lemma inverse_matrix_comp (A : Base →L[ℝ] Base) (hA : coordDet A ≠ 0) :
    ((coordDet A)⁻¹ • planeAdjugate A).comp A = ContinuousLinearMap.id ℝ Base := by
  rw [ContinuousLinearMap.smul_comp,planeAdjugate_comp,smul_smul,inv_mul_cancel₀ hA,one_smul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseJacobian
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the inverse Jacobian field in dimension two. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

lemma contDiffOn_coordDet {U : Set Base} {A : Base → Base →L[ℝ] Base}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun x => coordDet (A x)) U := by
  have hx : ContDiffOn ℝ ∞ (fun x => A x dx) U := hA.clm_apply contDiffOn_const
  have hy : ContDiffOn ℝ ∞ (fun x => A x dy) U := hA.clm_apply contDiffOn_const
  exact (hx.fst.mul hy.snd).sub (hx.snd.mul hy.fst)

lemma contDiffOn_inverseJacobianField {U : Set Base} {A : Base → Base →L[ℝ] Base}
    (hA : ContDiffOn ℝ ∞ A U) (hne : ∀ x ∈ U, coordDet (A x) ≠ 0) :
    ContDiffOn ℝ ∞ (inverseJacobianField A) U :=
  ((contDiffOn_coordDet hA).inv hne).smul
    (planeAdjugateOperator.contDiff.comp_contDiffOn hA)

lemma weighted_coordDet {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → Base →L[ℝ] Base} (hA : ContDiffOn ℝ ∞ A U)
    {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hb : WeightedBound U s m C A) :
    WeightedBound U s m (2^(m+1)*C^2) (fun x => coordDet (A x)) := by
  have he (v : Base) (hv : ‖v‖ ≤ 1) (π : Base →L[ℝ] ℝ) (hπ : ‖π‖ ≤ 1) :
      WeightedBound U s m C (fun x => π (A x v)) := by
    have hh := (hb.clm_apply_const hU hs hA v).linear hU hs
      (hA.clm_apply contDiffOn_const) π
    apply hh.mono_const
    calc
      ‖π‖*(‖v‖*C) ≤ 1*(1*C) := by gcongr
      _ = C := by ring
  have hdx : ‖dx‖ ≤ (1 : ℝ) := by simp [dx]
  have hdy : ‖dy‖ ≤ (1 : ℝ) := by simp [dy]
  have ha := he dx hdx (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ..)
  have hb' := he dy hdy (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.norm_fst_le ..)
  have hc := he dx hdx (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ..)
  have hd := he dy hdy (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ..)
  have hx : ContDiffOn ℝ ∞ (fun x => A x dx) U := hA.clm_apply contDiffOn_const
  have hy : ContDiffOn ℝ ∞ (fun x => A x dy) U := hA.clm_apply contDiffOn_const
  have had := ha.mul_real hU hs hC hC hx.fst hy.snd hd
  have hcb := hc.mul_real hU hs hC hC hx.snd hy.fst hb'
  have hh := had.sub hU hs (hx.fst.mul hy.snd) (hx.snd.mul hy.fst) hcb
  have hcost : (2:ℝ)^(m+1)*C^2 = 2^m*C*C + 2^m*C*C := by ring
  rw [hcost]
  exact hh

theorem weighted_inverseJacobianField {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {A : Base → Base →L[ℝ] Base} (hA : ContDiffOn ℝ ∞ A U)
    {s C K : ℝ} {m : ℕ} (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hb : WeightedBound U s m C A)
    (hne : ∀ x ∈ U, coordDet (A x) ≠ 0)
    (hinv : ∀ x ∈ U, ‖(coordDet (A x))⁻¹‖ ≤ K) :
    WeightedBound U s m (inverseJacobianBudget m C K) (inverseJacobianField A) := by
  have hC0 := zero_le_one.trans hC
  have hd := weighted_coordDet hU hA hs.le hC0 hb
  have hD : 0 ≤ 2^(m+1)*C^2 := by positivity
  have hd' := hd.mono_const (le_add_of_nonneg_left zero_le_one)
  have hi := hd'.inv_real hU hs (by linarith : 1 ≤ 1+2^(m+1)*C^2) hK
    (contDiffOn_coordDet hA) hne hinv
  have ha := (hb.linear hU hs.le hA planeAdjugateOperator).mono_const
    (mul_le_mul_of_nonneg_right planeAdjugateOperator_norm_le hC0)
  exact hi.smul_real hU hs.le (by positivity) (by positivity)
    ((contDiffOn_coordDet hA).inv hne) (planeAdjugateOperator.contDiff.comp_contDiffOn hA) ha

lemma inverseJacobianBudget_polynomial (m : ℕ) (C K : ℝ → ℝ)
    (hC : HasPolynomialBound C) (hK : HasPolynomialBound K) :
    HasPolynomialBound (fun x => inverseJacobianBudget m (C x) (K x)) := by
  unfold inverseJacobianBudget
  repeat first
    | exact hC
    | exact hK
    | apply HasPolynomialBound.add
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialInverseChartJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative derivatives of an inverse chart from its actual inverse
Jacobian field. The finite-order budget is polynomial in the field's jets. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverseChartJetBudget_one_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ inverseChartJetBudget n B := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpos : 0 ≤ (n.factorial : ℝ)*B*(inverseChartJetBudget n B)^n := by
      have hb := zero_le_one.trans ih
      positivity
    exact ih.trans (le_add_of_nonneg_right hpos)

lemma inverseChartJetBudget_le_succ (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    inverseChartJetBudget n B ≤ inverseChartJetBudget (n+1) B := by
  have hb := zero_le_one.trans (inverseChartJetBudget_one_le n hB)
  change _ ≤ _ + _
  exact le_add_of_nonneg_right (by positivity)

lemma inverseChartJetBudget_polynomial (n : ℕ) :
    HasPolynomialBound (inverseChartJetBudget n) := by
  induction n with
  | zero => exact polynomialBound_const zero_le_one
  | succ n ih =>
    exact ih.add (((polynomialBound_const (Nat.cast_nonneg n.factorial)).mul
      polynomialBound_id).mul (ih.pow n))

/-- The derivative equation is the ordinary inverse-function identity. No
bound on the position of the inverse chart is needed for positive jets. -/
theorem inverse_chart_positive_jets
    (e : OpenPartialHomeomorph Base Base)
    (hi : ContDiff ℝ ∞ e.symm) (J : Base → Base →L[ℝ] Base)
    (hJ : ContDiffOn ℝ ∞ J e.source)
    (heq : ∀ y ∈ e.target, fderiv ℝ e.symm y = J (e.symm y))
    {m : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hjets : ∀ k ≤ m, ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ k J e.source x‖ ≤ B) :
    ∀ j, 1 ≤ j → j ≤ m+1 → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ inverseChartJetBudget (m+1) B := by
  have hstep : ∀ n ≤ m+1, ∀ j, 1 ≤ j → j ≤ n → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ inverseChartJetBudget n B := by
    intro n
    induction n with
    | zero => intro hn j hj hjn; omega
    | succ n ih =>
      intro hn j hj hjn y hy
      by_cases hjold : j ≤ n
      · exact (ih (by omega) j hj hjold y hy).trans (inverseChartJetBudget_le_succ n hB)
      have hjnew : j = n+1 := by omega
      subst j
      have hcomp := norm_iteratedFDerivWithin_comp_le hJ hi.contDiffOn
        (show (n : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) e.open_source.uniqueDiffOn
        e.open_target.uniqueDiffOn (fun x hx => e.map_target hx) hy
        (fun k hk => hjets k (by omega) _ (e.map_target hy))
        (fun k hk hkn => (ih (by omega) k hk hkn y hy).trans
          (by
            simpa only [pow_one] using
              pow_le_pow_right₀ (inverseChartJetBudget_one_le n hB) hk))
      have heq' : EqOn (fderivWithin ℝ e.symm e.target) (J ∘ e.symm) e.target := by
        intro x hx
        rw [fderivWithin_of_isOpen e.open_target hx]
        exact heq x hx
      rw [← norm_iteratedFDerivWithin_fderivWithin e.open_target.uniqueDiffOn hy,
        iteratedFDerivWithin_congr heq' hy]
      exact hcomp.trans (le_add_of_nonneg_left
        (zero_le_one.trans (inverseChartJetBudget_one_le n hB)))
  exact hstep (m+1) le_rfl

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPhaseChartInverse
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial inverse-chart jets from forward jets and the actual Jacobian
lower bound. The exponent is fixed before the chart and numerical bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

lemma inverse_chart_derivative_eq_field
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    fderiv ℝ e.symm y = inverseJacobianField (fderiv ℝ e) (e.symm y) := by
  have hdet := coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
    he.contDiffOn hi.contDiffOn (fun x hx => e.map_source hx)
    (fun x hx => e.left_inv hx) (e.map_target hy)
  have hleft := inverse_matrix_comp (fderiv ℝ e (e.symm y)) hdet
  have hright := inverse_chart_derivative e he hi hy
  change fderiv ℝ e.symm y =
    (coordDet (fderiv ℝ e (e.symm y)))⁻¹ • planeAdjugate (fderiv ℝ e (e.symm y))
  rw [← ContinuousLinearMap.id_comp (fderiv ℝ e.symm y),← hleft,
    ContinuousLinearMap.comp_assoc,hright,ContinuousLinearMap.comp_id]

theorem polynomial_inverse_chart_bound (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
    ∀ B : ℝ, 1 ≤ B →
      (∀ j, 1 ≤ j → j ≤ m+1 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      ∀ j, 1 ≤ j → j ≤ m+1 → ∀ y ∈ e.target,
        ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ C*B^d := by
  have hpoly := (inverseChartJetBudget_polynomial (m+1)).comp
    ((polynomialBound_const zero_le_one).add
      (inverseJacobianBudget_polynomial m (fun x => x) (fun x => x)
        polynomialBound_id polynomialBound_id))
    (fun B hB => le_add_of_nonneg_right (by
      dsimp [inverseJacobianBudget]
      have hB0 := zero_le_one.trans hB
      positivity))
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  refine ⟨d,C,hC,?_⟩
  intro e he hi B hB hfwd hdet j hj hjm y hy
  have hB0 := zero_le_one.trans hB
  have hA : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    (he.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn
  have hbA : WeightedBound e.source 1 m B (fderiv ℝ e) := by
    intro k hk x hx
    simp only [one_pow,one_mul]
    have hsame := iteratedFDerivWithin_congr
      (fun z hz => fderivWithin_of_isOpen e.open_source hz
        (𝕜 := ℝ) (f := (e : Base → Base))) hx (𝕜 := ℝ) (n := k)
    rw [← hsame,norm_iteratedFDerivWithin_fderivWithin e.open_source.uniqueDiffOn hx]
    exact hfwd (k+1) (by omega) (by omega) x hx
  have hne : ∀ x ∈ e.source, coordDet (fderiv ℝ e x) ≠ 0 := fun x hx =>
    coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
      he.contDiffOn hi.contDiffOn (fun z hz => e.map_source hz) (fun z hz => e.left_inv hz) hx
  have hbJ := weighted_inverseJacobianField e.open_source.uniqueDiffOn hA
    zero_lt_one hB hB hbA hne hdet
  have hJ := contDiffOn_inverseJacobianField hA hne
  have hbound : ∀ k ≤ m, ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ k (inverseJacobianField (fderiv ℝ e)) e.source x‖ ≤
        1+inverseJacobianBudget m B B := by
    intro k hk x hx
    have hh := hbJ k hk x hx
    simp only [one_pow,one_mul] at hh
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  have hJB : 0 ≤ 1+inverseJacobianBudget m B B := by
    dsimp [inverseJacobianBudget]
    positivity
  exact (inverse_chart_positive_jets e hi (inverseJacobianField (fderiv ℝ e)) hJ
    (fun z hz => inverse_chart_derivative_eq_field e he hi hz) hJB hbound j hj hjm y hy).trans
      (hpoly B hB).2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartJetTransfer
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit jet transfer through nonlinear phase coordinates. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates PhaseGeometry

theorem realTwoJet_coordinate_prefix_bound
    {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V) (hTU : MapsTo T V U)
    {m : ℕ} {s C D : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hTd : ∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ V,
      ‖iteratedFDerivWithin ℝ j T V x‖ ≤ D)
    {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) F) :
    WeightedBound V s m (((m+2).factorial : ℝ)*D^(m+2)*C) (realTwoJet (F ∘ T)) := by
  apply realTwoJet_prefix_bound_on hV (hF.comp hT) hs hs1 (by positivity)
  intro j hj
  have hc (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) (x : Base) (hx : x ∈ V) :
      ‖iteratedFDerivWithin ℝ k T V x‖ ≤ D := hTd k hk (hkj.trans hj) x hx
  have hh := (hb j hj).comp_coordinates hV.uniqueDiffOn hU.uniqueDiffOn zero_lt_one le_rfl
    hD (div_nonneg hC (pow_nonneg hs.le _)) hT.contDiffOn hF.contDiffOn hTU hc
  apply hh.mono_const
  calc
    (j.factorial : ℝ)*(C/s^(j-2))*D^j = ((j.factorial : ℝ)*D^j)*C/s^(j-2) := by ring
    _ ≤ (((m+2).factorial : ℝ)*D^(m+2)*C)/s^(j-2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
      apply mul_le_mul_of_nonneg_right _ hC
      gcongr

theorem polynomial_inverse_chart_twoJet_bound_oai (m : ℕ) :
    ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (F : RField 4) (e : OpenPartialHomeomorph Base Base),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
    ∀ s B : ℝ, 0 < s → s ≤ 1 → 1 ≤ B →
      (∀ j ≤ m+2, WeightedBound e.source 1 j (B/s^(j-2)) F) →
      (∀ j, 1 ≤ j → j ≤ m+2 → ∀ x ∈ e.source,
        ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B) →
      (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B) →
      WeightedBound e.target s m (C*B^d) (realTwoJet (F ∘ e.symm)) := by
  obtain ⟨d₀,C₀,hC₀,hInv⟩ := polynomial_inverse_chart_bound (m+1)
  have hp := ((polynomialBound_const (Nat.cast_nonneg (m+2).factorial)).mul
    (((polynomialBound_const (zero_le_one.trans hC₀)).mul (polynomialBound_id.pow d₀)).pow
      (m+2))).mul polynomialBound_id
  obtain ⟨d,C,hC,hpoly⟩ := hp
  refine ⟨d,C,hC,?_⟩
  intro F e hF he hi s B hs hs1 hB hFjet hejet hdet
  have hD : 1 ≤ C₀*B^d₀ := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hB)
  have hb := realTwoJet_coordinate_prefix_bound hi e.open_source e.open_target
    (fun x hx => e.map_target hx) hs hs1 (zero_le_one.trans hB) hD
    (fun j hj hjm x hx => hInv e he hi B hB hejet hdet j hj (by omega) x hx) hF hFjet
  exact hb.mono_const (hpoly B hB).2

end ClosedSurfaceR4.RealModes

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound_oai := @OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound_oai
