-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:20.620586+00:00
-- url     : https://prove2.me/submissions/65c318d7-88e6-4ad9-b260-6933a326c876

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

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




lemma smooth_compact_weighted_bound {U : Set E} {V K : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) (hK : IsCompact K) (hKV : K ⊆ V)
    {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : E → F) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ f U → MapsTo f U K → WeightedBound U s m C f →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  obtain ⟨D, hD, hbD⟩ := compact_coefficient_bound hV hK hKV hg m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hC hf hfk hbf
  exact hbf.comp hU hV hs hC (le_trans zero_le_one hD) hf hg
    (fun x hx => hKV (hfk hx)) (fun j hj x hx => hbD j hj (f x) (hfk hx))




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ}
    {f g : E → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f U x‖ * ‖iteratedFDerivWithin ℝ (j - i) g U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_mul_le (n := j) (N := ∞) hf hg hU hx
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ ≤ 2 ^ j * C * D := weighted_binomial_bound hs hC hD j _ _
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun i hi => hbf i (hi.trans hj) x hx) (fun i hi => hbg i (hi.trans hj) x hx)
    _ ≤ _ := by gcongr; norm_num

lemma WeightedBound.const_mul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℂ) :
    WeightedBound U s m (‖a‖ * C) (fun x => a * f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul]
  calc
    _ = ‖a‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg a)

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

lemma WeightedBound.dot {ι : Type*} [Fintype ι] {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : E → ι → ℂ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m ((Fintype.card ι : ℝ) * (2 ^ m * C * D))
      (fun x => dotProduct (f x) (g x)) := by
  have hfsm (i : ι) := contDiffOn_pi.mp hf i
  have hgsm (i : ι) := contDiffOn_pi.mp hg i
  have hh := WeightedBound.finset_sum hU hs Finset.univ (fun _ : ι => 2 ^ m * C * D)
    (fun i x => f x i * g x i) (fun i _ => (hfsm i).mul (hgsm i)) (fun i _ =>
      (hbf.component hU hs hC hf i).mul hU hs hC hD (hfsm i) (hgsm i)
        (hbg.component hU hs hD hg i))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dotProduct] using hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma weighted_smul_field {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f : Scalar} {V : Field n} (hs : 0 < s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hV : ContDiffOn ℝ ∞ V U)
    (hbf : WeightedBound U s m C f) (hbV : WeightedBound U s m D V) :
    WeightedBound U s m (2 ^ m * C * D) (fun p => f p • V p) := by
  apply WeightedBound.pi hU hs (by positivity)
  · intro i
    exact hf.mul (contDiffOn_pi.mp hV i)
  · intro i
    exact hbf.mul hU hs.le hC hD hf (contDiffOn_pi.mp hV i) (hbV.component hU hs.le hD hV i)



end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticError
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.WeightedEstimates

lemma weighted_conjugate {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {s C : ℝ} {m : ℕ} {Z : Base → CVec n} (hs : 0 < s) (hC : 0 ≤ C)
    (hZ : ContDiffOn ℝ ∞ Z U) (hbZ : WeightedBound U s m C Z) :
    WeightedBound U s m C (fun p => conjugate (Z p)) := by
  apply WeightedBound.pi hU hs hC
  · intro i
    exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hZ i)
  · intro i
    have hh := (hbZ.component hU hs.le hC hZ i).linear hU hs.le
      (contDiffOn_pi.mp hZ i) Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp



end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
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
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma WeightedBound.restrict_open {U : Set E} (hU : IsOpen U) {f : E → F}
    {s C : ℝ} {m : ℕ} (hb : WeightedBound univ s m C f) : WeightedBound U s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  simpa only [iteratedFDerivWithin_univ] using hb j hj x (mem_univ x)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma norm_firstDirection (i : Fin 3) : ‖firstDirection i‖ ≤ 1 := by
  fin_cases i <;> (first | (simp [firstDirection, dx, dy, Prod.norm_def]; all_goals first | (norm_num [firstDirection, dx, dy, Prod.norm_def]; done) | rfl | decide) | (norm_num [firstDirection, dx, dy, Prod.norm_def]; done) | norm_num [firstDirection, dx, dy, Prod.norm_def])

lemma norm_secondDirection (i : Fin 3) : ‖secondDirection i‖ ≤ 1 := by
  fin_cases i <;> (first | (simp [secondDirection, dx, dy, Prod.norm_def]; all_goals first | (norm_num [secondDirection, dx, dy, Prod.norm_def]; done) | rfl | decide) | (norm_num [secondDirection, dx, dy, Prod.norm_def]; done) | norm_num [secondDirection, dx, dy, Prod.norm_def])

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma weighted_real_complex {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)




lemma weighted_derivativeAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → CVec n} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v φ)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (derivativeAmplitude τ φ Z v) := by
  have hd := (hb.directional hU hs hZ v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hdφ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hφ v
  have hc := weighted_real_complex hU.uniqueDiffOn hs.le hP hdφ hp
  have hcs := Complex.ofRealCLM.contDiff.comp_contDiffOn hdφ
  have hc' := hc.const_mul hU.uniqueDiffOn hcs (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ)) * ((ClosedSurfaceR4.SmallModes.coordDeriv v φ p : ℝ) : ℂ)) U := by
    exact contDiffOn_const.mul hcs
  have hz := ClosedSurfaceR4.SmallModes.weighted_smul_field hU.uniqueDiffOn hs
    (show 0 ≤ 1 / τ * P by positivity) hC hcm hZ hc'
    (hb.mono_order (Nat.le_succ m))
  have hzs : ContDiffOn ℝ ∞
      (fun p => (Complex.I / (τ : ℂ) * ((ClosedSurfaceR4.SmallModes.coordDeriv v φ p : ℝ) : ℂ)) • Z p) U := by
    exact hcm.smul hZ
  have ha := hd'.add hU.uniqueDiffOn hs.le
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hZ v) hzs hz
  convert ha using 1 <;> first | rfl | ring

lemma weighted_halfDot {n : ℕ} {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {X Y : Base → CVec n} {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbX : WeightedBound U s m C X) (hbY : WeightedBound U s m D Y) :
    WeightedBound U s m ((n : ℝ) * (2 ^ m * C * D)) (fun p => (X p ⬝ᵥ Y p) / 2) := by
  have hh := (hbX.dot hU hs hC hD hX hY hbY).const_mul hU (contDiffOn_dot hX hY) (1 / 2 : ℂ)
  apply (hh.congr (fun p _ => by ring)).mono_const
  simp only [norm_div, norm_one, Complex.norm_ofNat, Fintype.card_fin]
  have hn : 0 ≤ (n : ℝ) * (2 ^ m * C * D) := by positivity
  nlinarith

end ClosedSurfaceR4.QuadraticMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)



theorem weighted_phaseCrossTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} {τ s C D P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U)
    (hbZ : WeightedBound U s (m + 1) C Z) (hbW : WeightedBound U s (m + 1) D W)
    (hpφ : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v φ))
    (hpψ : ∀ v, ‖v‖ ≤ 1 → WeightedBound U s m P (ClosedSurfaceR4.SmallModes.coordDeriv v ψ)) :
    let A := (1 + 2 ^ m * P) * C / τ
    let B := (1 + 2 ^ m * P) * D / τ
    WeightedBound U s m ((n : ℝ) * (2 ^ m * A * B)) (phasePlusTensor τ φ ψ Z W) ∧
      WeightedBound U s m ((n : ℝ) * (2 ^ m * A * B)) (phaseMinusTensor τ φ ψ Z W) := by
  dsimp only
  have hA : 0 ≤ (1 + 2 ^ m * P) * C / τ := by positivity
  have hB : 0 ≤ (1 + 2 ^ m * P) * D / τ := by positivity
  have hdZ (v : Base) (hv : ‖v‖ ≤ 1) := QuadraticMean.weighted_derivativeAmplitude
    hU hτ hs hτs hC hP hφ hZ hbZ v hv (hpφ v hv)
  have hdW (v : Base) (hv : ‖v‖ ≤ 1) := QuadraticMean.weighted_derivativeAmplitude
    hU hτ hs hτs hD hP hψ hW hbW v hv (hpψ v hv)
  have hsZ (v : Base) := QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ v
  have hsW (v : Base) := QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ v
  constructor
  · apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · exact contDiffOn_pi.mp (contDiffOn_phasePlusTensor hU hφ hψ hZ hW τ)
    · intro i
      exact QuadraticMean.weighted_halfDot hU.uniqueDiffOn hs.le hA hB (hsZ _) (hsW _)
        (hdZ _ (norm_firstDirection i)) (hdW _ (norm_secondDirection i))
  · apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · exact contDiffOn_pi.mp (contDiffOn_phaseMinusTensor hU hφ hψ hZ hW τ)
    · intro i
      exact QuadraticMean.weighted_halfDot hU.uniqueDiffOn hs.le hA hB (hsZ _)
        (QuadraticMean.contDiffOn_conjugate (hsW _)) (hdZ _ (norm_firstDirection i))
        (QuadraticMean.weighted_conjugate hU.uniqueDiffOn hs hB (hsW _)
          (hdW _ (norm_secondDirection i)))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetWordDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every ordered coordinate jet is a derivative of a component of the
actual second jet, with precisely the excess derivative count. -/
noncomputable section

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma exists_lowWord (w : List (Fin 2)) (hw : w.length ≤ 2) :
    ∃ i : Fin 7, lowWord i = w := by
  cases w with
  | nil => exact ⟨0, rfl⟩
  | cons a w =>
    cases w with
    | nil =>
      fin_cases a
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    | cons b w =>
      have he : w = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      fin_cases a <;> fin_cases b
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩

lemma split_lowWord (w : List (Fin 2)) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, w = v ++ lowWord i ∧ v.length = w.length - 2 := by
  obtain ⟨i, hi⟩ := exists_lowWord (w.drop (w.length - 2)) (by
    rw [List.length_drop]
    omega)
  refine ⟨w.take (w.length - 2), i, ?_, ?_⟩
  · rw [hi, List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]

lemma iteratedDirectional_append {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v w : List A) (f : A → E) :
    iteratedDirectional (v ++ w) f = iteratedDirectional v (iteratedDirectional w f) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append, iteratedDirectional, ih]

/-- The scale loss of an ordered jet factor is its derivative order minus two. -/
lemma jet_as_lowJet_derivative (w : List (Fin 2)) (a : Fin 4) :
    ∃ v : List (Fin 2), ∃ i : Fin 7, v.length = w.length - 2 ∧
      ∀ (G : Base → Space), jet G w a =
        iteratedDirectional (v.map coordinateVector) (fun p => lowJet G p (Sum.inr (i, a))) := by
  obtain ⟨v, i, hw, hv⟩ := split_lowWord w
  refine ⟨v, i, hv, ?_⟩
  intro G
  change iteratedDirectional (w.map coordinateVector) (fun p => G p a) = _
  rw [hw, List.map_append, iteratedDirectional_append]
  rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

/-- A weighted bound on the second-jet map controls every actual higher jet. -/
theorem weighted_actual_jet {U : Set Base} (hU : IsOpen U) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (m : ℕ) (w : List (Fin 2)) (a : Fin 4)
    (hb : WeightedBound U s (m + (w.length - 2)) B (lowJet G)) :
    WeightedBound U s m (B / s ^ (w.length - 2)) (jet G w a) := by
  obtain ⟨v, i, hv, he⟩ := jet_as_lowJet_derivative w a
  rw [he G]
  have hQ := (lowJet_smooth hG).contDiffOn (s := U)
  have hcomp := hb.component hU.uniqueDiffOn hs.le hB hQ (Sum.inr (i, a))
  have hf : ContDiffOn ℝ ∞ (fun p => lowJet G p (Sum.inr (i, a))) U :=
    (contDiff_pi.mp (lowJet_smooth hG) (Sum.inr (i, a))).contDiffOn
  have hvnorm : ∀ x ∈ v.map coordinateVector, ‖x‖ ≤ 1 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact norm_coordinateVector_le j
  have hcomp' : WeightedBound U s (m + (v.map coordinateVector).length) B
      (fun p => lowJet G p (Sum.inr (i, a))) := by
    simpa only [List.length_map, hv] using hcomp
  have hd := hcomp'.iteratedDirectional hU hs hB hf (v.map coordinateVector) hvnorm m
  simpa only [List.length_map, hv] using hd

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedWeightedSeminorm_component {K : Compacts A} (s : ℝ≥0) (m j : ℕ)
    (hj : j ≤ m) (f : SupportedField (F := F) K) :
    (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f ≤
      supportedWeightedSeminorm K s m f := by
  let q : ℕ → Seminorm ℝ (SupportedField (F := F) K) :=
    fun j => s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j
  have h : q j f ≤ (Finset.range (m + 1)).sup q f :=
    Seminorm.le_finset_sup_apply (show j ∈ Finset.range (m + 1) by simpa using hj)
  simpa only [q, supportedWeightedSeminorm, smul_apply, NNReal.smul_def,
    NNReal.coe_pow, smul_eq_mul] using h

lemma weightedBound_of_supportedSeminorm {K : Compacts A} (s : ℝ≥0) (m : ℕ)
    (f : SupportedField (F := F) K) :
    WeightedBound Set.univ s m (supportedWeightedSeminorm K s m f) f := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  calc
    (s : ℝ) ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤
        (s : ℝ) ^ j * ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j f :=
      mul_le_mul_of_nonneg_left (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
        (pow_nonneg s.coe_nonneg _)
    _ ≤ _ := supportedWeightedSeminorm_component s m j hj f

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalIsometryBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric coordinate transport on the open domains used by the local
polynomial estimates. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weightedBound_comp_isometry_on {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) {U : Set B} (hU : IsOpen U) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound U s m C f) :
    WeightedBound (e ⁻¹' U) s m C (f ∘ e) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j (hU.preimage e.continuous) hx]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  have hh := hb j hj (e x) hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hh
  exact hh

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedLowCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform angular-slice estimates for smooth low-jet coefficients on a
compact admissible set. The angular parameter adds no scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_lowJet_pair {U : Set Base} (hU : IsOpen U) {Q : Base → LowJet}
    (hQ : ContDiffOn ℝ ∞ Q U) {s B : ℝ} (hs : 0 < s) (hB : 1 ≤ B) (m : ℕ)
    (hb : WeightedBound U s m B Q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (2 * B) (fun p => (Q p, t)) := by
  have hleft : WeightedBound U s m B (fun p => (Q p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hc : ‖((0 : LowJet), t)‖ ≤ 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ht.1]
    exact max_le (by norm_num) ht.2
  have hright : WeightedBound U s m 1 (fun _ : Base => ((0 : LowJet), t)) :=
    (weightedBound_const U s m ((0 : LowJet), t)).mono_const hc
  have hsum := hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const) contDiffOn_const hright
  have hp : WeightedBound U s m (B + 1) (fun p => (Q p, t)) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hsum
  exact hp.mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedCoefficientVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A low-jet coefficient variation is linear in the varied map and loses
only the two derivatives in its second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_low_coefficient_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → E} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn (hK.prod isCompact_Icc) hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma ofExpression_loss (e : Expression) : (ofExpression e).loss = e.loss := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, loss, ↓reduceIte, Expression.loss, ih]
  | add _ _ ihe ihf => simp only [ofExpression, loss, Expression.loss, ihe, ihf]

lemma loss_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (h : ∀ i ∈ l, (f i).loss ≤ N) : (sumList l f).loss ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem loss_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).loss ≤ e.loss + 2 := by
  induction e with
  | coeff c =>
    apply loss_sumList_le
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    simpa only [loss, Fin.succ_ne_zero, ↓reduceIte, Nat.add_zero] using hl
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      simp only [differentiate, loss, Fin.succ_ne_zero, ↓reduceIte]
      omega
    · simp only [differentiate, hi, ↓reduceIte, loss]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, loss]
    omega

theorem loss_third_variation (e : Expression) :
    ((((ofExpression e).differentiate 0).differentiate 1).differentiate 2).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  omega

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma order_sumList_le {ι : Type*} (l : List ι) (f : ι → MixedExpression) (N : ℕ)
    (hN : 2 ≤ N) (h : ∀ i ∈ l, (f i).order ≤ N) : (sumList l f).order ≤ N := by
  induction l with
  | nil => exact hN
  | cons i l ih =>
    exact max_le (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma order_differentiate (j : Fin 3) (e : MixedExpression) :
    (e.differentiate j).order ≤ e.order := by
  induction e with
  | coeff c =>
    apply order_sumList_le _ _ 2 (le_refl 2)
    intro i _
    have hl : (lowWord i.1).length ≤ 2 := by
      obtain ⟨i, a⟩ := i
      fin_cases i <;> simp [lowWord]
    exact max_le hl (le_refl 2)
  | atom i w a e ih =>
    by_cases hi : i = 0
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
    · simp only [differentiate, hi, ↓reduceIte, order]
      omega
  | add e f ihe ihf =>
    simp only [differentiate, order]
    omega

lemma order_ofExpression (e : Expression) : (ofExpression e).order = e.order := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, order, Expression.order, ih]
  | add _ _ ihe ihf => simp only [ofExpression, order, Expression.order, ihe, ihf]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

lemma variations_order (e : Expression) (i : Fin 3) : (e.variations i).order ≤ e.order := by
  have h₁ := order_differentiate 0 (ofExpression e)
  have h₂ := order_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := order_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [order_ofExpression] at h₁
  fin_cases i
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)

lemma variations_loss (e : Expression) (i : Fin 3) : (e.variations i).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  fin_cases i
  · change ((ofExpression e).differentiate 0).loss ≤ e.loss + 6
    omega
  · change (((ofExpression e).differentiate 0).differentiate 1).loss ≤ e.loss + 6
    omega
  · exact loss_third_variation e

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedComplexMixedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-scale evaluation: the output is measured at the slow scale, while
only the explicit jet excess contributes short-scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

theorem compact_complex_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (J : JetData) (s τ : ℝ),
      0 < s → 0 < τ → τ ≤ 1 → ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U K →
      WeightedBound U s m B (lowJet G) →
      (∀ i w a, ContDiffOn ℝ ∞ (J i w a) U) →
      (∀ i w a, w.length ≤ e.order →
        WeightedBound U s m (B / τ ^ slotLoss i w) (J i w a)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / τ ^ e.loss) (fun p => e.evalComplex G J (p, t)) := by
  induction e with
  | coeff c =>
    have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn he
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient_vector hU hO hK hKO hc m B hB
    refine ⟨D, hD, ?_⟩
    intro G J s τ hs _ _ hG hGK hb _ _ t ht
    simpa only [loss, pow_zero, div_one, evalComplex, Function.comp_def,
      Complex.ofRealCLM_apply] using hd (lowJet G) s hs (lowJet_smooth hG).contDiffOn hGK hb t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have htBound := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun j v b hv => hJB j v b (hv.trans (le_max_right _ _))) t ht
    have hjBound := hJB i w a (le_max_left _ _)
    have hp := hjBound.mul hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (hJ i w a) (evalComplex_parameter_smooth hG hQ hJ (e := e) he t) htBound
    convert hp using 1 <;> first | rfl | simp only [loss, slotLoss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_left _ _))) t ht
    have hc' := hc G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_right _ _))) t ht
    have hd'' : WeightedBound U s m (D / τ ^ max e.loss f.loss)
        (fun p => e.evalComplex G J (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / τ ^ max e.loss f.loss)
        (fun p => f.evalComplex G J (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_right _ _)))
    simpa only [loss, add_div, evalComplex] using hd''.add hU.uniqueDiffOn hs.le
      (evalComplex_parameter_smooth hG hQ hJ (e := e) he.1 t)
      (evalComplex_parameter_smooth hG hQ hJ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedModulatedJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slow-scale bounds on the amplitudes of fast oscillatory jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

lemma weighted_complexify {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → ℝ} {s C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun p => (f p : ℂ)) := by
  have hh := hb.linear hU hs hf Complex.ofRealCLM
  have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    hh.mono_const (mul_le_of_le_one_left hC hn)

lemma weighted_amplitudeDerivative {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hb : WeightedBound U s (m + 1) C Z) (v : Base) (hv : ‖v‖ ≤ 1)
    (hp : WeightedBound U s m P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m ((1 + 2 ^ m * P) * C / τ) (amplitudeDerivative τ φ v Z) := by
  have hd := (hb.directional hU hs hZ.contDiffOn v).mono_const
    (mul_le_of_le_one_left (div_nonneg hC hs.le) hv)
  have hd' := hd.mono_const (div_le_div_of_nonneg_left hC hτ hτs)
  have hds : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))
  have hc := weighted_complexify hU.uniqueDiffOn hs.le hP hds.contDiffOn hp
  have hcs := Complex.ofRealCLM.contDiff.comp hds
  have hc' := hc.const_mul hU.uniqueDiffOn hcs.contDiffOn (Complex.I / (τ : ℂ))
  have hn : ‖Complex.I / (τ : ℂ)‖ = 1 / τ := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [hn] at hc'
  have hcm := (contDiff_const (c := Complex.I / (τ : ℂ))).mul hcs
  have hz := hc'.mul hU.uniqueDiffOn hs.le (by positivity) hC hcm.contDiffOn hZ.contDiffOn
    (hb.mono_order (Nat.le_succ m))
  have ha := hd'.add hU.uniqueDiffOn hs.le
    ((hZ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := v))).contDiffOn
    (hcm.mul hZ).contDiffOn hz
  convert ha using 1 <;> first | rfl | ring

lemma jetConstant_nonneg {P : ℝ} (hP : 0 ≤ P) (m r : ℕ) : 0 ≤ jetConstant P m r := by
  induction r generalizing m with
  | zero => exact zero_le_one
  | succ r ih => exact mul_nonneg (by positivity) (ih (m + 1))

/-- Output derivatives remain at the slow scale. Only the length of the jet
word contributes short-scale powers. -/
theorem weighted_amplitudeJet {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → ℂ} {τ s C P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (w : List Base)
    (hw : ∀ v ∈ w, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + w.length) C Z)
    (hp : ∀ v ∈ w, WeightedBound U s (m + w.length) P (fun p => fderiv ℝ φ p v)) :
    WeightedBound U s m (jetConstant P m w.length * C / τ ^ w.length)
      (amplitudeJet τ φ w Z) := by
  induction w generalizing m with
  | nil => simpa only [amplitudeJet, List.length_nil, Nat.add_zero, jetConstant, one_mul, pow_zero, div_one] using hb
  | cons v w ih =>
    have hlen : m + (v :: w).length = (m + 1) + w.length := by simp; omega
    have hb' := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (m + 1)
      (hlen ▸ hb) (fun x hx => hlen ▸ hp x (List.mem_cons_of_mem _ hx))
    have hd := weighted_amplitudeDerivative hU hτ hs hτs
      (div_nonneg (mul_nonneg (jetConstant_nonneg hP _ _) hC) (pow_nonneg hτ.le _)) hP
      hφ (amplitudeJet_smooth hφ hZ τ w) hb' v (hw v (List.mem_cons_self ..))
      ((hp v (List.mem_cons_self ..)).mono_order (by simp))
    convert hd using 1
    · simp only [List.length_cons, jetConstant, pow_succ]
      ring
    · rfl

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetDataBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite-order budget for all demodulated jet slots. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeBudget_ge_one {N m : ℕ} {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    1 ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma le_amplitudeBudget {N m : ℕ} {B P : ℝ} (hP : 0 ≤ P) :
    B ≤ amplitudeBudget N m B P := by
  have hsum := Finset.sum_nonneg (s := Finset.range (N + 1))
    (fun r _ => jetConstant_nonneg hP m r)
  dsimp only [amplitudeBudget]
  linarith

lemma jetConstant_le_amplitudeBudget {N m r : ℕ} {B P : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hr : r ≤ N) :
    jetConstant P m r ≤ amplitudeBudget N m B P := by
  have h := Finset.single_le_sum (fun a _ => jetConstant_nonneg hP m a)
    (show r ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  dsimp only [amplitudeBudget]
  linarith

theorem weighted_amplitudeData {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) {τ s B P : ℝ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (m N : ℕ) (hGb : WeightedBound U s (m + N) B (lowJet G))
    (hHb : ∀ j, WeightedBound U s (m + N) 1 (H j))
    (hφb : ∀ j v, WeightedBound U s (m + N) P (fun p => fderiv ℝ (φ j) p (coordinateVector v)))
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) (hw : w.length ≤ N) :
    WeightedBound U s m (amplitudeBudget N m B P / τ ^ slotLoss i w)
      (amplitudeData G φ H τ i w a) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hj := weighted_actual_jet hU hG hs hB m w a (hGb.mono_order (by omega))
    have hc := weighted_complexify hU.uniqueDiffOn hs.le (by positivity)
      (jet_smooth hG w a).contDiffOn hj
    apply hc.mono_const
    calc
      B / s ^ (w.length - 2) ≤ B / τ ^ (w.length - 2) :=
        div_le_div_of_nonneg_left hB (pow_pos hτ _) (pow_le_pow_left₀ hτ.le hτs _)
      _ ≤ _ := div_le_div_of_nonneg_right (le_amplitudeBudget hP) (pow_nonneg hτ.le _)
  · have hcomp := (hHb j).component hU.uniqueDiffOn hs.le zero_le_one (hH j).contDiffOn a
    have hc := weighted_amplitudeJet hU hτ hs hτs zero_le_one hP
      (hφ j) (contDiff_pi.mp (hH j) a) (w.map coordinateVector)
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le v) m
      (hcomp.mono_order (by simp only [List.length_map]; omega))
      (fun v hv => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
        exact (hφb j v).mono_order (by simp only [List.length_map]; omega))
    simp only [List.length_map, mul_one] at hc
    apply hc.mono_const
    exact div_le_div_of_nonneg_right (jetConstant_le_amplitudeBudget hB hP hw)
      (pow_nonneg hτ.le _)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp slow-scale estimates for the first three conjugated polynomial
variations. The power E+6 is independent of correction accuracy and order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Unit amplitude bounds give the sharp exponent for every first, second,
and third variation after removing all participating phase factors. -/
theorem compact_conjugated_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) 1 (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / τ ^ (e.loss + 6))
          (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  classical
  let A := amplitudeBudget e.order m B P
  have hA : 1 ≤ A := amplitudeBudget_ge_one (zero_le_one.trans hB) hP
  have hex := fun i : Fin 3 => compact_complex_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m A hA
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G φ H s τ hτ hs hτs hs1 hG hφ hH hGK hGb hHb hφb t ht i
  have hdata := weighted_amplitudeData hU hG hφ hH hτ hs hτs (zero_le_one.trans hB) hP
    m e.order hGb hHb hφb
  have h := hb i G (amplitudeData G φ H τ) s τ hs hτ (hτs.trans hs1) hG hGK
    ((hGb.mono_order (by omega)).mono_const (le_amplitudeBudget hP))
    (fun j w a => (amplitudeData_smooth hG hφ hH τ j w a).contDiffOn)
    (fun j w a hw => hdata j w a (hw.trans (e.variations_order i))) t ht
  have hbound : D i / τ ^ (e.variations i).loss ≤ (∑ j, D j) / τ ^ (e.loss + 6) := by
    calc
      _ ≤ D i / τ ^ (e.loss + 6) := div_le_div_of_nonneg_left (hD i) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (e.variations_loss i))
      _ ≤ _ := div_le_div_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)) (pow_nonneg hτ.le _)
  apply (h.mono_const hbound).congr
  intro p _
  exact conjugatedVariation_eq e G hφ hH τ i (p, t)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetScaling
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling each oscillatory amplitude independently. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

lemma amplitudeDerivative_real_smul {Z : Base → ℂ} (hZ : ContDiff ℝ ∞ Z)
    (φ : Base → ℝ) (τ c : ℝ) (v : Base) :
    amplitudeDerivative τ φ v (fun p => c • Z p) =
      fun p => c • amplitudeDerivative τ φ v Z p := by
  funext p
  have hd := congrArg (fun L : Base →L[ℝ] ℂ => L v)
    (((hZ.differentiable (by simp) p).hasFDerivAt.const_smul c).fderiv)
  change fderiv ℝ (fun q => c • Z q) p v = c • fderiv ℝ Z p v at hd
  change fderiv ℝ (fun q => c • Z q) p v + _ = _
  rw [hd]
  simp only [amplitudeDerivative, Complex.real_smul]
  ring

lemma amplitudeJet_real_smul {φ : Base → ℝ} {Z : Base → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z) (τ c : ℝ) (w : List Base) :
    amplitudeJet τ φ w (fun p => c • Z p) = fun p => c • amplitudeJet τ φ w Z p := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [amplitudeJet, ih]
    exact amplitudeDerivative_real_smul (amplitudeJet_smooth hφ hZ τ w) φ τ c v

lemma scaleDirections_smooth {H : DirectionFields} (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (c : Fin 3 → ℝ) : ∀ j, ContDiff ℝ ∞ (scaleDirections H c j) :=
  fun j => ContDiff.const_smul (c j) (hH j)

lemma amplitudeData_scale (G : Base → Space) {φ : Fin 3 → Base → ℝ}
    {H : DirectionFields} (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hH : ∀ j, ContDiff ℝ ∞ (H j)) (τ : ℝ) (c : Fin 3 → ℝ) :
    amplitudeData G φ (scaleDirections H c) τ =
      scaleJets (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) := by
  funext i w a p
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (scaleJets_base (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) w a p).symm
  · rw [scaleJets_succ]
    change amplitudeJet τ (φ j) (w.map coordinateVector) (fun q => c j • H j q a) p = _
    rw [amplitudeJet_real_smul (hφ j) (contDiff_pi.mp (hH j) a)]
    rfl

lemma conjugatedVariation_scale (e : Expression) (G : Base → Space)
    {φ : Fin 3 → Base → ℝ} {H : DirectionFields}
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hH : ∀ j, ContDiff ℝ ∞ (H j))
    (τ : ℝ) (c : Fin 3 → ℝ) (i : Fin 3) (z : Base × ℝ) :
    conjugatedVariation e G φ (scaleDirections H c) τ i z =
      (c 0 * (if 1 ≤ i then c 1 else 1) * (if 2 ≤ i then c 2 else 1)) •
        conjugatedVariation e G φ H τ i z := by
  rw [conjugatedVariation_eq e G hφ (scaleDirections_smooth hH c),
    conjugatedVariation_eq e G hφ hH, amplitudeData_scale G hφ hH τ c]
  have h := evalComplex_scaleJets (fun j => e.variations_degree i j) G
    (amplitudeData G φ H τ) (fun j _ => (c j : ℂ)) z
  fin_cases i <;> simpa [Complex.real_smul] using h

lemma scaleDirections_inverse (H : DirectionFields) (C : Fin 3 → ℝ) (hC : ∀ j, C j ≠ 0) :
    scaleDirections (scaleDirections H (fun j => (C j)⁻¹)) C = H := by
  funext j p
  simp only [scaleDirections, smul_smul, mul_inv_cancel₀ (hC j), one_smul]

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConjugatedMultilinearBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated polynomial estimates retain the product of the input
amplitude bounds. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

/-- Product estimate corresponding to the fixed-power perturbation bound
in the small-modes argument. No output-order or accuracy dependence is
hidden in the short-scale exponent. -/
theorem compact_conjugated_multilinear_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ j, WeightedBound U s (m + e.order) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ (e.loss + 6)) (fun p => conjugatedVariation e G φ H τ i (p, t)) := by
  obtain ⟨D, hD, hb⟩ := compact_conjugated_variation_bound hU hO hK hKO e he m B P hB hP
  refine ⟨D, hD, ?_⟩
  intro G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let V := scaleDirections H (fun j => (C j)⁻¹)
  have hV := scaleDirections_smooth hH (fun j => (C j)⁻¹)
  have hunit : ∀ j, WeightedBound U s (m + e.order) 1 (V j) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hH j).contDiffOn (C j)⁻¹
    change WeightedBound U s (m + e.order) 1 (fun p => (C j)⁻¹ • H j p)
    simpa only [abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hbound := hb G φ V s τ hτ hs hτs hs1 hG hφ hV hGK hGb hunit hφb t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heq : (fun p => conjugatedVariation e G φ H τ i (p, t)) =
      (fun p => W • conjugatedVariation e G φ V τ i (p, t)) := by
    funext p
    have h := conjugatedVariation_scale e G hφ hV τ C i (p, t)
    rw [scaleDirections_inverse H C (fun j => ne_of_gt (hC j))] at h
    exact h
  rw [heq]
  have hsmooth : ContDiffOn ℝ ∞ (fun p => conjugatedVariation e G φ V τ i (p, t)) U := by
    have h := evalComplex_parameter_smooth hG (fun p hp => hKO (hGK hp))
      (fun j w a => (amplitudeData_smooth hG hφ hV τ j w a).contDiffOn)
      (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact conjugatedVariation_eq e G hφ hV τ i (p, t)
  have h := hbound.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos hW]
  ring

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial perturbations have one fixed short-scale exponent. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

variable {n : ℕ}

/-- The perturbation parameter enters linearly in the bound, and the single
short-scale loss works at every requested output order. -/
theorem compact_conjugated_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B Q : ℝ) (hB : 1 ≤ B) (hQ : 0 ≤ Q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Fin 3 → Base → ℝ)
      (H : DirectionFields) (s τ ε : ℝ) (C : Fin 3 → ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → (∀ j, 0 < C j) →
      ContDiff ℝ ∞ G → (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, ContDiff ℝ ∞ (H j)) →
      Set.MapsTo (lowJet G) U K → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ j, WeightedBound U s (m + order P) (C j) (H j)) →
      (∀ j v, WeightedBound U s (m + order P) Q
        (fun p => fderiv ℝ (φ j) p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * ε * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            τ ^ loss P) (fun p => conjugated P ε G φ H τ i (p, t)) := by
  classical
  have hex := fun l => compact_conjugated_multilinear_bound hU hO hK hKO (P l) (hP l) m B Q hB hQ
  choose D hD hb using hex
  refine ⟨∑ l, D l, Finset.sum_nonneg (fun l _ => hD l), ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGK hGb hHb hφb t ht i
  let W := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 ≤ W := by
    have h₀ := (hC 0).le
    have h₁ := (hC 1).le
    have h₂ := (hC 2).le
    dsimp only [W]
    split_ifs <;> positivity
  have hval (l : Fin n) : WeightedBound U s m (D l * ε * W / τ ^ loss P)
      (fun p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t)) := by
    have hl : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hh := hb l G φ H s τ C hτ hs hτs hs1 hC hG hφ hH hGK
      (hGb.mono_order (Nat.add_le_add_left hl m))
      (fun j => (hHb j).mono_order (Nat.add_le_add_left hl m))
      (fun j v => (hφb j v).mono_order (Nat.add_le_add_left hl m)) t ht i
    have hsmooth := conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t
    have hh' : WeightedBound U s m (D l * W / τ ^ loss P)
        (fun p => conjugatedVariation (P l) G φ H τ i (p, t)) :=
      hh.mono_const (div_le_div_of_nonneg_left (mul_nonneg (hD l) hW) (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
          (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))))
    have hscaled := hh'.const_smul hU.uniqueDiffOn hsmooth (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have heps : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l * W / τ ^ loss P) :=
        mul_le_mul_of_nonneg_right heps
          (div_nonneg (mul_nonneg (hD l) hW) (pow_nonneg hτ.le _))
      _ = _ := by ring
  have hsum := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l * ε * W / τ ^ loss P)
    (fun l p => ε ^ (l.val + 1) • conjugatedVariation (P l) G φ H τ i (p, t))
    (fun l _ => (conjugatedVariation_smooth (hP l) hG hφ hH hO
      (fun p hp => hKO (hGK hp)) τ i t).const_smul _) (fun l _ => hval l)
  simpa only [conjugated, ← Finset.sum_div, ← Finset.sum_mul, W] using hsum

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanCoefficient
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial contribution to the quadratic zero-phase coefficient. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma weighted_starField {U : Set Base} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {H : Base → Fin 4 → ℂ} (hs : 0 < s) (hC : 0 ≤ C) (hH : ContDiff ℝ ∞ H)
    (hb : WeightedBound U s m C H) : WeightedBound U s m C (starField H) := by
  apply WeightedBound.pi hU hs hC
  · intro a
    exact (Complex.conjCLE.contDiff.comp (contDiff_pi.mp hH a)).contDiffOn
  · intro a
    have hh := (hb.component hU hs.le hC hH.contDiffOn a).linear hU hs.le
      (contDiff_pi.mp hH a).contDiffOn Complex.conjCLE.toContinuousLinearMap
    apply hh.mono_const
    apply mul_le_of_le_one_left hC
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPolynomialMean
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial part of the normalized quadratic mean is O(η), with
finite-loss value and difference bounds and constants chosen before scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma normalized_product_scale {δ τ s ε E A D : ℝ} {r p : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hA : 0 ≤ A) (hD : 0 ≤ D) (hp : r ≤ p) :
    δ⁻¹ ^ 2 * (E * ε * (A * (δ * τ)) * (D * (δ * τ)) / τ ^ r) ≤
      (τ / s + ε / τ ^ p) * E * A * D := by
  have hfrac : ε / τ ^ r ≤ ε / τ ^ p :=
    div_le_div_of_nonneg_left hε (pow_pos hτ p) (pow_le_pow_of_le_one hτ.le hτ1 hp)
  have hsmall : ε * τ ^ 2 / τ ^ r ≤ τ / s + ε / τ ^ p := by
    calc
      _ = (ε / τ ^ r) * τ ^ 2 := by ring
      _ ≤ ε / τ ^ r := mul_le_of_le_one_right (div_nonneg hε (pow_nonneg hτ.le _))
        (pow_le_one₀ hτ.le hτ1)
      _ ≤ ε / τ ^ p := hfrac
      _ ≤ _ := le_add_of_nonneg_left (div_nonneg hτ.le hs.le)
  calc
    _ = (ε * τ ^ 2 / τ ^ r) * (E * A * D) := by
      field_simp [hδ.ne']
    _ ≤ (τ / s + ε / τ ^ p) * (E * A * D) :=
      mul_le_mul_of_nonneg_right hsmall (mul_nonneg (mul_nonneg hE hA) hD)
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_rf95b2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_rf95b2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_rf95b2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_rf95b2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_rf95b2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_rf95b2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth phases have uniform directional-derivative bounds in every atlas chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance phaseReadBoundFiberNormed_rf95b2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseReadBoundFiberSpace_rf95b2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseReadBoundDualAdd_rf95b2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseReadBoundDualSmul_rf95b2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseReadBoundSectionNormed_rf95b2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseReadBoundSectionSpace_rf95b2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem phase_read_gradient_bound {ι : Type*} [Fintype ι]
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a)) (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k a (s : ℝ), 0 ≤ s → s ≤ 1 →
      ∀ v : SmallModes.Base, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a))) := by
  classical
  choose C hC hc using fun (k : A.centers) (a : ι) => compact_smooth_bound
    (A.vectorChartRead_smooth k (hφ a))
    (localize_compact (k : M) (A.outer_support k) (φ a)) (m+1)
  let P := ∑ k : A.centers, ∑ a : ι, C k a
  have hP : 0 ≤ P := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun a _ => hC k a))
  refine ⟨P,hP,?_⟩
  intro k a s hs hs1 v hv
  have hb := weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth k (hφ a)) (hc k a)
  change WeightedEstimates.WeightedBound univ 1 (m+1) (C k a) (A.vectorPlaneRead k (φ a)) at hb
  have hd := hb.directional isOpen_univ (by norm_num : (0:ℝ)<1)
    (A.vectorPlaneRead_smooth k (hφ a)).contDiffOn v
  have hsize : ‖v‖*(C k a/1) ≤ C k a := by
    simpa only [div_one] using mul_le_of_le_one_left (hC k a) hv
  have hd' := (hd.mono_const hsize).shrink_scale hs hs1
  apply hd'.mono_const
  have h₁ : C k a ≤ ∑ b : ι, C k b := Finset.single_le_sum
    (fun b _ => hC k b) (Finset.mem_univ a)
  have h₂ : (∑ b : ι, C k b) ≤ P := Finset.single_le_sum
    (fun j _ => Finset.sum_nonneg (fun b _ => hC j b)) (Finset.mem_univ k)
  exact h₁.trans h₂

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseChartBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth phases have uniform directional-derivative bounds in every atlas chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance phaseChartReadBoundFiberNormed_rf95b2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseChartReadBoundFiberSpace_rf95b2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseChartReadBoundDualAdd_rf95b2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseChartReadBoundDualSmul_rf95b2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseChartReadBoundSectionNormed_rf95b2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseChartReadBoundSectionSpace_rf95b2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The coordinate derivatives used by the polynomial phase estimates obey
fixed profiles as the slow scale varies. -/
theorem phase_chart_gradient_bound {ι : Type*} [Fintype ι]
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a)) (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k a (s : ℝ), 0 ≤ s → s ≤ 1 → ∀ v : Fin 2,
      WeightedEstimates.WeightedBound univ s m P
        (fun x => fderiv ℝ (A.vectorChartRead k (φ a)) x (coordinateVector v)) := by
  classical
  choose C hC hc using fun (k : A.centers) (a : ι) => compact_smooth_bound
    (A.vectorChartRead_smooth k (hφ a))
    (localize_compact (k : M) (A.outer_support k) (φ a)) (m+1)
  let P := ∑ k : A.centers, ∑ a : ι, C k a
  have hP : 0 ≤ P := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun a _ => hC k a))
  refine ⟨P,hP,?_⟩
  intro k a s hs hs1 v
  have hd := (hc k a).directional isOpen_univ (by norm_num : (0:ℝ)<1)
    (A.vectorChartRead_smooth k (hφ a)).contDiffOn (coordinateVector v)
  have hv : ‖coordinateVector v‖ = 1 := by simp only [coordinateVector,Pi.norm_single,norm_one]
  have hd' := hd.mono_const (show ‖coordinateVector v‖*(C k a/1) ≤ C k a by rw [hv]; simp)
  apply (hd'.shrink_scale hs hs1).mono_const
  exact (Finset.single_le_sum (fun b _ => hC k b) (Finset.mem_univ a)).trans
    (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun b _ => hC j b)) (Finset.mem_univ k))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledMetricQuadraticTargets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric quadratic coefficients have size delta squared when the
oscillatory amplitudes have size delta times their wavelength. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

theorem scaled_quadraticAmplitude_bound {n : ℕ} {ι : Type*} {U : Set Base}
    (hU : IsOpen U) {φ : ι → Base → ℝ} {Z : ι → Field n}
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) U) (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
    {s τ δ A P : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hP : 0 ≤ P) (m : ℕ)
    (hb : ∀ i, WeightedBound U s (m + 1) (A * (δ * τ)) (Z i))
    (hp : ∀ i v, ‖v‖ ≤ 1 → WeightedBound U s m P (coordDeriv v (φ i)))
    (l : QuadraticLabel ι) :
    WeightedBound U s m (δ ^ 2 * ((n : ℝ) * 2 ^ m * ((1 + 2 ^ m * P) * A) ^ 2))
      (quadraticAmplitude τ φ Z l) := by
  have hh (i j : ι) := weighted_phaseCrossTensor hU hτ hs hτs
    (show 0 ≤ A * (δ * τ) by positivity) (show 0 ≤ A * (δ * τ) by positivity) hP
    (hφ i) (hφ j) (hZ i) (hZ j) (hb i) (hb j) (hp i) (hp j)
  have he : (n : ℝ) * (2 ^ m * ((1 + 2 ^ m * P) * (A * (δ * τ)) / τ) *
      ((1 + 2 ^ m * P) * (A * (δ * τ)) / τ)) =
      δ ^ 2 * ((n : ℝ) * 2 ^ m * ((1 + 2 ^ m * P) * A) ^ 2) := by
    field_simp [hτ.ne']
  rcases l with i | ⟨i,j,b⟩
  · change WeightedBound U s m _ (phasePlusTensor τ (φ i) (φ i) (Z i) (Z i))
    simpa only [he] using (hh i i).1
  · cases b
    · simpa only [quadraticAmplitude, Bool.false_eq_true, ↓reduceIte, he] using (hh i j).1
    · simpa only [quadraticAmplitude, ↓reduceIte, he] using (hh i j).2

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CutoffQuadraticBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoff multiplication preserves the delta-squared quadratic estimate. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma cutoff_square_complex_bound {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedBound univ s m D (fun x => ((χ x * χ x : ℝ) : ℂ)) := by
  let C := supportedWeightedSeminorm K 1 m χ
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨2^m*C*C,by positivity,?_⟩
  intro s hs hs1
  have hb : WeightedBound univ s m C χ :=
    (weightedBound_of_supportedSeminorm 1 m χ).shrink_scale hs.le hs1
  have hχc : ContDiffOn ℝ ∞ (fun x => (χ x : ℂ)) univ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn χ.contDiff.contDiffOn
  have hbc := QuadraticMean.weighted_real_complex isOpen_univ.uniqueDiffOn hs.le hC χ.contDiff.contDiffOn hb
  have hm : WeightedBound univ s m (2^m*C*C) (fun x => (χ x : ℂ)*(χ x : ℂ)) :=
    WeightedBound.mul isOpen_univ.uniqueDiffOn hs.le hC hC hχc hχc hbc hbc
  simpa only [Complex.ofReal_mul] using hm

theorem cutoff_quadratic_bound {ι : Type*} {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) (A P : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ s δ : ℝ)
      (φ : ι → SmallModes.Base → ℝ) (Z : ι → SmallModes.Field 4),
      (∀ a, ContDiff ℝ ∞ (φ a)) → (∀ a, ContDiff ℝ ∞ (Z a)) →
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A → 0 ≤ P →
      (∀ a, WeightedBound univ s (m+1) (A*(δ*τ)) (Z a)) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedBound univ s m P (SmallModes.coordDeriv v (φ a))) →
      ∀ l : RealModes.QuadraticLabel ι,
      WeightedBound univ s m (B*δ^2)
        (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) := by
  obtain ⟨D,hD,hd⟩ := cutoff_square_complex_bound χ m
  let C := 4 * 2^m * ((1+2^m*P)*A)^2
  refine ⟨2^m*D*C,by dsimp [C] <;> positivity,?_⟩
  intro τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ hA hP hb hp l
  have hquad : WeightedBound univ s m (δ^2*C) (RealModes.quadraticAmplitude τ φ Z l) :=
    RealModes.scaled_quadraticAmplitude_bound isOpen_univ (fun a => (hφ a).contDiffOn)
      (fun a => (hZ a).contDiffOn) hτ hs hτs hδ hA hP m hb hp l
  have hcs : ContDiffOn ℝ ∞ (fun x => ((χ x * χ x : ℝ) : ℂ)) univ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (χ.contDiff.contDiffOn.mul χ.contDiff.contDiffOn)
  have hqs : ContDiffOn ℝ ∞ (RealModes.quadraticAmplitude τ φ Z l) univ :=
    (RealModes.quadraticAmplitude_smooth hφ hZ τ l).contDiffOn
  have hout : WeightedBound univ s m (2^m*D*(δ^2*C))
      (fun x => ((χ x * χ x : ℝ) : ℂ) • RealModes.quadraticAmplitude τ φ Z l x) :=
    SmallModes.weighted_smul_field isOpen_univ.uniqueDiffOn hs hD
      (by dsimp [C] <;> positivity) hcs hqs (hd s hs hs1) hquad
  have he : (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) =
      (fun x => ((χ x * χ x : ℝ) : ℂ) • RealModes.quadraticAmplitude τ φ Z l x) := by
    funext x j
    rw [Pi.smul_apply,Pi.smul_apply,pow_two]
    rfl
  rw [he]
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasQuadraticBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform delta-squared bounds for the actual global quadratic targets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasQuadraticBoundsFiberNormed_rf95b2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticBoundsFiberSpace_rf95b2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasQuadraticBoundsDualAdd_rf95b2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticBoundsDualSmul_rf95b2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance atlasQuadraticBoundsSectionNormed_rf95b2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticBoundsSectionSpace_rf95b2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
theorem globalQuadraticTarget_bound (k : A.centers) (m : ℕ) (A₀ P₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ s δ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
      (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
      (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A₀ → 0 ≤ P₀ →
      (∀ a, WeightedEstimates.WeightedBound univ s (m+1) (A₀*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P₀
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∀ l : RealModes.QuadraticLabel ι, WeightedEstimates.WeightedBound univ s m (B*δ^2)
        (A.globalQuadraticTarget τ φ Z hφ hZ k l) := by
  obtain ⟨B,hB,hb⟩ := cutoff_quadratic_bound (ι := ι) (A.supportedPlaneWeight k) m A₀ P₀
  refine ⟨B,hB,?_⟩
  intro τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ hA hP hz hp l
  exact hb τ s δ (fun a => A.vectorPlaneRead k (φ a)) (fun a => A.vectorPlaneRead k (Z a))
    (fun a => A.vectorPlaneRead_smooth k (hφ a)) (fun a => A.vectorPlaneRead_smooth k (hZ a))
    hτ hs hτs hs1 hδ hA hP hz hp l

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalCubicRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform atlas estimate for the actual mixed metric and quadratic correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cubicDualAdd
local instance cubicFiberNormed_rf95b2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance cubicFiberSpace_rf95b2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance cubicDualSmul_rf95b2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance cubicSectionNormed_rf95b2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cubicSectionSpace_rf95b2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma planeWeight_square_bound (i : A.centers) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedEstimates.WeightedBound univ s m C (fun x => (A.planeWeight i x)^2) := by
  let C := supportedWeightedSeminorm (modeSupport (A.chartWeightCompact i)) 1 m
    (A.supportedPlaneWeight i)
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨2^m*C*C,by positivity,?_⟩
  intro s hs hs1
  have hb : WeightedEstimates.WeightedBound univ s m C (A.planeWeight i) :=
    (weightedBound_of_supportedSeminorm 1 m (A.supportedPlaneWeight i)).shrink_scale hs.le hs1
  have hh := hb.mul_real uniqueDiffOn_univ hs.le hC hC
    (A.planeWeight_smooth i).contDiffOn (A.planeWeight_smooth i).contDiffOn hb
  simpa only [pow_two] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart readings retain the unweighted derivative prefix of the true map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem vectorPlaneRead_prefix_bounds (i : A.centers) (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → ∀ j ≤ q+m,
      WeightedEstimates.WeightedBound univ 1 j (D*C/s^(j-q)) (A.vectorPlaneRead i F) := by
  classical
  choose D hD hd using fun j => A.vectorPlaneRead_bound (V := V) i j
  let T := ∑ j ∈ Finset.range (q+m+1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hD j)
  refine ⟨T,hT,?_⟩
  intro F s C hs hs1 hC hF hb j hj
  have hp : A.WeightedBound 1 j (C/s^(j-q)) F := fun k => (hb k).prefix hs hs1 hC hj
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (by positivity) hF hp
  apply hh.mono_const
  calc
    D j*(C/s^(j-q)) = D j*C/s^(j-q) := by ring
    _ ≤ T*C/s^(j-q) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC)
      (pow_nonneg hs.le _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem jet_lowWord_bound {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G)
    (w : Fin 7) (a : Fin 4) :
    WeightedBound U s m C (fun p => jet G (lowWord w) a p) := by
  let f : Base → ℝ := fun p => G p a
  have hf : ContDiff ℝ ∞ f := contDiff_pi.mp hG a
  have hp (j : ℕ) (hj : j ≤ m+2) : WeightedBound U 1 j (C/s^(j-2)) f :=
    (hb j hj).component hU.uniqueDiffOn zero_le_one
      (div_nonneg hC (pow_nonneg hs.le _)) hG.contDiffOn a
  have hzero : WeightedBound U s m C f := by
    intro j hj x hx
    have hh := hp j (by omega) j le_rfl x hx
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ s^j*(C/s^(j-2)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ ≤ s^j*(C/s^j) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le _ _))) (pow_nonneg hs.le _)
      _ = C := by field_simp
  have hunit (v : Fin 2) : ‖coordinateVector v‖ = 1 := by
    simp only [coordinateVector,Pi.norm_single,norm_one]
  have hfirst (v : Fin 2) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (C/s^(j-1)) (fun x => fderiv ℝ f x (coordinateVector v)) := by
    have hh := (hp (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn (coordinateVector v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hunit,one_mul,div_one,he] using hh
  have hone (v : Fin 2) :
      WeightedBound U s m C (fun x => fderiv ℝ f x (coordinateVector v)) := by
    apply directional_of_prefix hU hf hs hC _ (coordinateVector v) (hunit v).le
    intro j hj
    apply (hp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have htwo (v v' : Fin 2) : WeightedBound U s m C
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector v')) x (coordinateVector v)) :=
    directional_of_prefix hU
      ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
      hs hC (hfirst v') (coordinateVector v) (hunit v).le
  fin_cases w
  · exact hzero
  · exact hone 0
  · exact hone 1
  · exact htwo 0 0
  · exact htwo 0 1
  · exact htwo 1 0
  · exact htwo 1 1

theorem bounded_lowJet_prefix {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G) →
      WeightedBound U s m (D+C) (lowJet G) := by
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) (contDiff_id : ContDiff ℝ ∞ (id : Base → Base)).contDiffOn m
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hb
  apply WeightedBound.pi hU.uniqueDiffOn hs (by linarith)
  · intro i
    exact (contDiff_pi.mp (lowJet_smooth hG) i).contDiffOn
  · intro i
    cases i with
    | inl i =>
      exact ((hd s hs.le hs1).component hU.uniqueDiffOn hs.le
        (zero_le_one.trans hD) contDiff_id.contDiffOn i).mono_const (by linarith)
    | inr i =>
      exact (jet_lowWord_bound hU hG hs hs1 hC hb i.1 i.2).mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetCompactRange
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact positional-jet range for all maps in a bounded C2 family. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem bounded_lowJet_range {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G →
      WeightedBound U 1 2 C G → MapsTo (lowJet G) U Q := by
  obtain ⟨D,_,hd⟩ := bounded_lowJet_prefix hU K hUK 0
  refine ⟨Metric.closedBall 0 (D+C),isCompact_closedBall _ _,?_⟩
  intro G hG hb p hp
  have hj := hd G hG 1 C zero_lt_one le_rfl hC (fun j hj => by
    simpa only [one_pow,div_one] using hb.mono_order (by omega : j ≤ 2))
  simpa only [Metric.mem_closedBall,dist_zero_right] using hj.norm_le hp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPhaseBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform product bounds for the actual nonzero-phase coefficients. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression ModulatedJets

theorem quadraticPhaseCoefficient_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ ψ : Base → ℝ)
      (H K : Base → Fin 4 → ℂ) (s τ ε C D : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ φ → ContDiff ℝ ∞ ψ →
      ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H → WeightedBound U s (m + order P) D K →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ ψ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / τ ^ loss P)
          (quadraticPhaseCoefficient P ε G φ ψ H K τ t) := by
  obtain ⟨E, hE, he⟩ := compact_conjugated_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E / 4, div_nonneg hE (by norm_num), ?_⟩
  intro G φ ψ H K s τ ε C D hτ hs hτs hs1 hε hε1 hC hD hG hφ hψ hH hK hGQ hGb hHb hKb hφb hψb t ht
  have hpb : ∀ j v, WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (pairPhases φ ψ j) p (coordinateVector v)) := by
    intro j v
    fin_cases j
    · exact hφb v
    · exact hψb v
    · change WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
      simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
        (weightedBound_zero U s (m + order P)).mono_const hF
  have hhb : ∀ j, WeightedBound U s (m + order P) (![C, D, 1] j) (pairDirections H K j) := by
    intro j
    fin_cases j
    · exact hHb
    · exact hKb
    · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
  have hh := he G (pairPhases φ ψ) (pairDirections H K) s τ ε ![C, D, 1]
    hτ hs hτs hs1 hε hε1 (fun j => by fin_cases j; exact hC; exact hD; norm_num)
    hG (pairPhases_smooth hφ hψ) (pairDirections_smooth hH hK) hGQ hGb hhb hpb t ht 1
  have hsm : ContDiffOn ℝ ∞ (fun p => conjugated P ε G
      (pairPhases φ ψ) (pairDirections H K) τ 1 (p,t)) U :=
    ContDiffOn.sum fun l _ =>
      (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hψ)
        (pairDirections_smooth hH hK) hO (fun _ hp => hQO (hGQ hp)) τ 1 t).const_smul _
  have hf := hh.const_smul hU.uniqueDiffOn hsm (1 / 4 : ℝ)
  convert hf using 1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
      show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  · funext p
    simp only [quadraticPhaseCoefficient, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticFamilyBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One constant controls every doubled and mixed polynomial phase. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

theorem quadraticFamilyCoefficient_bound {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (s τ ε C : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) → (∀ i, ContDiff ℝ ∞ (H i)) →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ i, WeightedBound U s (m + order P) C (H i)) →
      (∀ i v, WeightedBound U s (m + order P) F
        (fun p => fderiv ℝ (φ i) p (coordinateVector v))) →
      ∀ (l : RealModes.QuadraticLabel ι), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C ^ 2 / τ ^ loss P)
          (quadraticFamilyCoefficient P ε G φ H τ t l) := by
  obtain ⟨E, hE, he⟩ := quadraticPhaseCoefficient_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ hGb hHb hφb l t ht
  have hneg (i : ι) (v : Fin 2) : WeightedBound U s (m + order P) F
      (fun p => fderiv ℝ (fun x => -φ i x) p (coordinateVector v)) := by
    have hh := (hφb i v).neg hU.uniqueDiffOn
      (((hφ i).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).contDiffOn
    simpa only [fderiv_fun_neg, neg_apply] using hh
  rcases l with i | ⟨i,j,b⟩
  · simpa only [quadraticFamilyCoefficient, pow_two, mul_assoc] using
      he G (φ i) (φ i) (H i) (H i) s τ ε C C hτ hs hτs hs1 hε hε1 hC hC
        hG (hφ i) (hφ i) (hH i) (hH i) hGQ hGb (hHb i) (hHb i) (hφb i) (hφb i) t ht
  · cases b
    · simpa only [quadraticFamilyCoefficient, Bool.false_eq_true, ↓reduceIte, pow_two, mul_assoc] using
        he G (φ i) (φ j) (H i) (H j) s τ ε C C hτ hs hτs hs1 hε hε1 hC hC
          hG (hφ i) (hφ j) (hH i) (hH j) hGQ hGb (hHb i) (hHb j) (hφb i) (hφb j) t ht
    · simpa only [quadraticFamilyCoefficient, ↓reduceIte, pow_two, mul_assoc] using
        he G (φ i) (fun x => -φ j x) (H i) (starField (H j)) s τ ε C C hτ hs hτs hs1 hε hε1 hC hC
          hG (hφ i) (hφ j).neg (hH i) (starField_smooth (hH j)) hGQ hGb (hHb i)
          (weighted_starField hU.uniqueDiffOn hs hC.le (hH j) (hHb j)) (hφb i) (hneg j) t ht

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticTensorBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three tensor components use a common derivative order and a common
short-scale exponent, independently of the number of correction steps. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

theorem quadraticFamilyTensor_bound {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (s τ ε C : ℝ),
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C →
      ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) → (∀ i, ContDiff ℝ ∞ (H i)) →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ i, WeightedBound U s (m + tensorOrder P) C (H i)) →
      (∀ i v, WeightedBound U s (m + tensorOrder P) F
        (fun p => fderiv ℝ (φ i) p (coordinateVector v))) →
      ∀ (l : RealModes.QuadraticLabel ι), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C ^ 2 / τ ^ tensorLoss P)
          (quadraticFamilyTensor P ε G φ H τ t l) := by
  have hex (k : Fin 3) := quadraticFamilyCoefficient_bound (ι := ι)
    hU hO hQ hQO (P k) (hP k) m B F hB hF
  choose E hE he using hex
  let E₀ := ∑ k, E k
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg (fun k _ => hE k)
  refine ⟨E₀, hE₀, ?_⟩
  intro G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ hGb hHb hφb l t ht
  apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
  · intro k
    exact quadraticFamilyCoefficient_smooth hO (hP k) hG hφ hH
      (fun _ hp => hQO (hGQ hp)) ε τ t l
  · intro k
    have hord : order (P k) ≤ tensorOrder P :=
      Finset.le_sup (f := fun j => order (P j)) (Finset.mem_univ k)
    have hloss : loss (P k) ≤ tensorLoss P :=
      Finset.le_sup (f := fun j => loss (P j)) (Finset.mem_univ k)
    have hb := he k G φ H s τ ε C hτ hs hτs hs1 hε hε1 hC hG hφ hH hGQ
      (hGb.mono_order (Nat.add_le_add_left hord m))
      (fun i => (hHb i).mono_order (Nat.add_le_add_left hord m))
      (fun i v => (hφb i v).mono_order (Nat.add_le_add_left hord m)) l t ht
    apply hb.mono_const
    calc
      _ ≤ E k * ε * C ^ 2 / τ ^ tensorLoss P :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (hE k) hε) (sq_nonneg C)) (pow_pos hτ _)
          (pow_le_pow_of_le_one hτ.le (hτs.trans hs1) hloss)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hτ.le _)
        gcongr
        exact Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ k)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledQuadraticTargets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets have size O(delta^2), with the polynomial contribution
retaining an eta factor when the input amplitudes have size delta * tau. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadratic_product_scale {δ τ s ε E A : ℝ} {r p : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hA : 0 ≤ A) (hp : r ≤ p) :
    E * ε * (A * (δ * τ)) ^ 2 / τ ^ r ≤
      δ ^ 2 * (τ / s + ε / τ ^ p) * E * A ^ 2 := by
  have hh := normalized_product_scale hδ hτ hs hτ1 hε hE hA hA hp
  calc
    _ = δ ^ 2 * (δ⁻¹ ^ 2 * (E * ε * (A * (δ * τ)) * (A * (δ * τ)) / τ ^ r)) := by
      field_simp [hδ.ne']
    _ ≤ δ ^ 2 * ((τ / s + ε / τ ^ p) * E * A * A) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg δ)
    _ = _ := by ring

theorem scaled_quadraticFamilyTensor_bound {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : ι → Base → ℝ)
      (H : ι → Base → Fin 4 → ℂ) (s δ τ ε A : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < A →
      tensorLoss P ≤ p → ContDiff ℝ ∞ G → (∀ i, ContDiff ℝ ∞ (φ i)) →
      (∀ i, ContDiff ℝ ∞ (H i)) → Set.MapsTo (lowJet G) U Q →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ i, WeightedBound U s (m + tensorOrder P) (A * (δ * τ)) (H i)) →
      (∀ i v, WeightedBound U s (m + tensorOrder P) F
        (fun x => fderiv ℝ (φ i) x (coordinateVector v))) →
      ∀ (l : RealModes.QuadraticLabel ι), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (δ ^ 2 * (τ / s + ε / τ ^ p) * E * A ^ 2)
          (quadraticFamilyTensor P ε G φ H τ t l) := by
  obtain ⟨E, hE, he⟩ := quadraticFamilyTensor_bound (ι := ι) hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ H s δ τ ε A p hδ hτ hs hτs hs1 hε hε1 hA hp hG hφ hH hGQ hGb hHb hφb l t ht
  exact (he G φ H s τ ε (A * (δ * τ)) hτ hs hτs hs1 hε hε1 (by positivity)
    hG hφ hH hGQ hGb hHb hφb l t ht).mono_const
      (quadratic_product_scale hδ hτ hs (hτs.trans hs1) hε hE hA.le hp)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialQuadraticBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform delta-squared bounds for the actual global quadratic targets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance polynomialQuadraticBoundsFiberNormed_rf95b2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialQuadraticBoundsFiberSpace_rf95b2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialQuadraticBoundsDualAdd_rf95b2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialQuadraticBoundsDualSmul_rf95b2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


local instance polynomialQuadraticBoundsSectionNormed_rf95b2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialQuadraticBoundsSectionSpace_rf95b2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
theorem globalPolynomialQuadraticTarget_bound {n : ℕ}
    (Q : A.centers → Fin 3 → Fin n → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ) (k : A.centers)
    {U : Set Base} (hU : IsOpen U) (hKU : (A.chartWeightCompact k : Set Base) ⊆ U)
    {K : Set LowJet} (hK : IsCompact K) (m : ℕ)
    (B F₀ A₀ P₀ : ℝ) (hB : 1 ≤ B) (hF₀ : 0 ≤ F₀) (hA₀ : 0 < A₀) (hP₀ : 0 ≤ P₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
      (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
      (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
      (s δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ/s+ε/τ^tensorLoss (Q k) ≤ 1 →
      MapsTo (lowJet (A.jetChartMap k F)) U K →
      WeightedEstimates.WeightedBound U s (m+tensorOrder (Q k)) B (lowJet (A.jetChartMap k F)) →
      (∀ a, WeightedEstimates.WeightedBound univ s (m+tensorOrder (Q k)+1)
        (A₀*(δ*τ)) (A.vectorChartRead k (Z a))) →
      (∀ a v, WeightedEstimates.WeightedBound U s (m+tensorOrder (Q k)) F₀
        (fun x => fderiv ℝ (A.vectorChartRead k (φ a)) x (coordinateVector v))) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P₀
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∀ l : RealModes.QuadraticLabel ι, WeightedEstimates.WeightedBound univ s m (E*δ^2)
        (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l) := by
  obtain ⟨M,hM,hm⟩ := A.globalQuadraticTarget_bound (ι := ι) k m A₀ P₀
  obtain ⟨D,hD,hd⟩ := A.planeWeight_square_bound k m
  obtain ⟨E,hE,he⟩ := scaled_quadraticFamilyTensor_bound (ι := ι)
    hU isOpen_univ hK (subset_univ _) (Q k) (hQ k) m B F₀ hB hF₀
  let C := 2^m*D*(E*A₀^2)
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  refine ⟨M+C,add_nonneg hM hC,?_⟩
  intro F hF φ Z hφ hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall hjet hb hZb hφb hφm l
  have hpoly := he (A.jetChartMap k F) (fun a => A.vectorChartRead k (φ a))
    (fun a => A.vectorChartRead k (Z a)) s δ τ ε A₀ (tensorLoss (Q k))
    hδ hτ hs hτs hs1 hε hε1 hA₀ le_rfl (A.jetChartMap_smooth k hF)
    (fun a => A.vectorChartRead_smooth k (hφ a)) (fun a => A.vectorChartRead_smooth k (hZ a))
    hjet hb (fun a => ((hZb a).mono_order (by omega)).restrict_open hU) hφb l 0 (by simp)
  have hpoly' := hpoly.mono_const
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (sq_nonneg δ)) hE) (sq_nonneg A₀))
  simp only [mul_one] at hpoly'
  have hsm : ContDiff ℝ ∞ (quadraticFamilyTensor (Q k) ε (A.jetChartMap k F)
      (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l) := by
    apply contDiff_pi.mpr
    intro j
    exact contDiffOn_univ.mp (quadraticFamilyCoefficient_smooth isOpen_univ (hQ k j)
      (A.jetChartMap_smooth k hF) (fun a => A.vectorChartRead_smooth k (hφ a))
      (fun a => A.vectorChartRead_smooth k (hZ a)) (fun _ _ => mem_univ _) ε τ 0 l)
  let V := planeCoordinateIsometry.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage planeCoordinateIsometry.symm.continuous
  have hpc := weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU hsm hpoly'
  have hcs : ContDiff ℝ ∞ (coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
      (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l) :=
    hsm.comp planeCoordinateIsometry.symm.contDiff
  let T := fun x => (A.planeWeight k x)^2 •
    coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
      (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l x
  have hT : ContDiff ℝ ∞ T := ((A.planeWeight_smooth k).pow 2).smul hcs
  have hprod := ((hd s hs hs1).restrict_open hV).smul_real hV.uniqueDiffOn hs.le hD
    (by positivity : 0 ≤ δ^2*E*A₀^2) ((A.planeWeight_smooth k).pow 2).contDiffOn hcs.contDiffOn hpc
  have hsp : tsupport T ⊆ V := by
    intro x hx
    have hw := tsupport_smul_subset_left (fun x => (A.planeWeight k x)^2) _ hx
    have hw' : x ∈ tsupport (A.planeWeight k) := by
      apply (show tsupport (fun x => (A.planeWeight k x)^2) ⊆ tsupport (A.planeWeight k) from ?_) hw
      simpa only [pow_two] using (tsupport_mul_subset_left (f := A.planeWeight k) (g := A.planeWeight k))
    obtain ⟨y,hy,heq⟩ := (A.supportedPlaneWeight k).tsupport_subset hw'
    change planeCoordinateIsometry.symm x ∈ U
    rw [← heq,planeCoordinateIsometry.symm_apply_apply]
    exact hKU hy
  have hpg : WeightedEstimates.WeightedBound univ s m (C*δ^2) T := by
    have hh := hprod.extend_support hV hsp (by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [C]
    ring
  have hmetric := hm τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ.le hA₀.le hP₀
    (fun a => weightedBound_comp_isometry planeCoordinateIsometry.symm
      (A.vectorChartRead_smooth k (hZ a)) ((hZb a).mono_order (by omega))) hφm l
  have hms := (A.globalQuadraticTarget τ φ Z hφ hZ k l).contDiff
  have hadd := hmetric.add uniqueDiffOn_univ hs.le hms.contDiffOn hT.contDiffOn hpg
  have heq : A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l =
      (fun x => A.globalQuadraticTarget τ φ Z hφ hZ k l x+T x) := by
    funext x
    exact smul_add ((A.planeWeight k x)^2)
      (RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
        (fun a => A.vectorPlaneRead k (Z a)) l x)
      (coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
        (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l x)
  rw [heq]
  convert hadd using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasJetProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact jet ranges and coefficient bounds derived from the actual atlas input norms. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_jet_profiles
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (Q : A.centers → Set LowJet) (B : A.centers → ℕ → ℝ),
      (∀ i, IsCompact (Q i)) ∧ (∀ i m, 1 ≤ B i m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) ∧
      ∀ i m, WeightedEstimates.WeightedBound (U i) s m (B i m) (lowJet (A.jetChartMap i G)) := by
  classical
  choose E hE he using fun i m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  let C := fun i m => ‖spaceCoordinates.toContinuousLinearMap‖ * E i m * R m
  have hC (i m) : 0 ≤ C i m := mul_nonneg
    (mul_nonneg (norm_nonneg _) (hE i m)) (hR m)
  have hpref (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
      (s : ℝ≥0) (hs : 0 < (s:ℝ)) (hs1 : s ≤ 1)
      (hb : ∀ m, A.ShiftedBound 2 m s (R m) G) (i m j) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound (U i) 1 j (C i m/(s:ℝ)^(j-2)) (A.jetChartMap i G) := by
    have hh := (he i m G s (R m) hs hs1 (hR m) hG (hb m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hc := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hh
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    change WeightedEstimates.WeightedBound univ 1 j _
      ((spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry) at hc
    rw [heq] at hc
    have hb' : WeightedEstimates.WeightedBound univ 1 j (C i m/(s:ℝ)^(j-2)) (A.jetChartMap i G) := by
      simpa only [C,mul_div_assoc,mul_assoc] using hc
    exact hb'.restrict_open (hU i)
  choose Q hQ hmaps using fun i => bounded_lowJet_range (hU i) (KU i) (hUK i) (hC i 0)
  choose D hD hd using fun i m => bounded_lowJet_prefix (hU i) (KU i) (hUK i) m
  refine ⟨Q,fun i m => D i m+C i m,hQ,fun i m => (hD i m).trans
    (le_add_of_nonneg_right (hC i m)),?_⟩
  intro G hG s hs hs1 hb
  constructor
  · intro i
    apply hmaps i _ (A.jetChartMap_smooth i hG)
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref G hG s hs hs1 hb i 0 2 (by omega)
  · intro i m
    exact hd i m (A.jetChartMap i G) (A.jetChartMap_smooth i hG) s (C i m)
      hs hs1 (hC i m) (hpref G hG s hs hs1 hb i m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialTargetProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical profiles for full quadratic targets, derived before varying maps and scales. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology NNReal BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_target_profiles_oai {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : A.centers → Fin 3 → Fin n → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    (R a : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (ha : ∀ m, 0 ≤ a m) :
    ∃ E : A.centers → ℕ → ℝ, (∀ i m, 0 ≤ E i m) ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (Z : ι → M → Fin 4 → ℂ) (hZ : ∀ b, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z b))
        (s : ℝ≥0) (δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ 1) →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ i b m, WeightedEstimates.WeightedBound univ s m (a m*(δ*τ)) (A.vectorPlaneRead i (Z b))) →
      ∀ i m l, WeightedEstimates.WeightedBound univ s m (E i m*δ^2)
        (A.globalPolynomialQuadraticTarget Q hQ G hG ε τ φ Z hφ hZ i l) := by
  classical
  obtain ⟨K,B,hK,hB,hjet⟩ := A.atlas_jet_profiles U hU KU hUK R hR
  choose Fp hFp hfp using fun m => A.phase_chart_gradient_bound φ hφ m
  choose Mp hMp hmp using fun m => A.phase_read_gradient_bound φ hφ m
  let Ap := fun i m => 1+a (m+tensorOrder (Q i)+1)
  have hAp (i m) : 0 < Ap i m := by dsimp [Ap] <;> linarith [ha (m+tensorOrder (Q i)+1)]
  choose E hE he using fun i m => A.globalPolynomialQuadraticTarget_bound Q hQ i
    (hU i) (hweight i) (hK i) m (B i (m+tensorOrder (Q i)))
    (Fp (m+tensorOrder (Q i))) (Ap i m) (Mp m)
    (hB i _) (hFp _) (hAp i m) (hMp m)
  refine ⟨E,hE,?_⟩
  intro G hG Z hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall hr hz i m l
  obtain ⟨hmap,hbound⟩ := hjet G hG s hs hs1 hr
  apply he i m G hG φ Z hφ hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1 (hsmall i)
    (hmap i) (hbound i _) _ _ _ l
  · intro b
    have hh := weightedBound_comp_isometry planeCoordinateIsometry
      (A.vectorPlaneRead_smooth i (hZ b)) (hz i b (m+tensorOrder (Q i)+1))
    have heq : A.vectorPlaneRead i (Z b) ∘ planeCoordinateIsometry = A.vectorChartRead i (Z b) := by
      funext x
      simp only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    rw [heq] at hh
    apply hh.mono_const
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ.le hτ.le)
  · intro b v
    exact (hfp (m+tensorOrder (Q i)) i b s s.coe_nonneg hs1 v).restrict_open (hU i)
  · intro b v hv
    exact hmp m i b s s.coe_nonneg hs1 v hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles_oai.{u_1, u_2}
