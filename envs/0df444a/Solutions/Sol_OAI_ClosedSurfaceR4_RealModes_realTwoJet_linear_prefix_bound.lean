-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:49:54.523025+00:00
-- url     : https://prove2.me/submissions/5282c1f1-1c37-4f25-9721-e49cd82a5bef

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI007

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseTwoJetBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LinearFrameJetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit two-jet bounds in linear coordinates, without compact-range
constants depending on the chosen phase. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4

namespace WeightedEstimates
open SmallModes

theorem WeightedBound.comp_linear_equiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → E} {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (L : Base ≃L[ℝ] Base) (hD : 1 ≤ D) (hL : ‖L.toContinuousLinearMap‖ ≤ D)
    (hb : WeightedBound U s m C f) :
    WeightedBound (L ⁻¹' U) s m (C*D^m) (f ∘ L) := by
  intro j hj x hx
  rw [L.iteratedFDerivWithin_comp_right f hU hx j]
  have hn := (iteratedFDerivWithin ℝ j f U (L x)).norm_compContinuousLinearMap_le
    (fun _ => L.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  calc
    _ ≤ s^j*(‖iteratedFDerivWithin ℝ j f U (L x)‖*‖L.toContinuousLinearMap‖^j) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg hs _)
    _ = (s^j*‖iteratedFDerivWithin ℝ j f U (L x)‖)*‖L.toContinuousLinearMap‖^j := by ring
    _ ≤ C*D^m := mul_le_mul (hb j hj (L x) hx)
      ((pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_right₀ hD hj))
      (pow_nonneg (norm_nonneg _) _) hC

end WeightedEstimates

namespace RealModes
open SmallModes WeightedEstimates

theorem realTwoJet_linear_prefix_bound_oai {U : Set Base} (hU : IsOpen U)
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (L : Base ≃L[ℝ] Base) (hD : 1 ≤ D) (hL : ‖L.toContinuousLinearMap‖ ≤ D)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) F) :
    WeightedBound (L ⁻¹' U) s m (C*D^(m+2)) (realTwoJet (F ∘ L)) := by
  apply realTwoJet_prefix_bound_on (hU.preimage L.continuous) (hF.comp L.contDiff) hs hs1
    (mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) _))
  intro j hj
  have hh := (hb j hj).comp_linear_equiv hU.uniqueDiffOn zero_le_one
    (div_nonneg hC (pow_nonneg hs.le _)) L hD hL
  apply hh.mono_const
  calc
    C/s^(j-2)*D^j = (C*D^j)/s^(j-2) := by ring
    _ ≤ (C*D^(m+2))/s^(j-2) := by
      gcongr

end RealModes
end ClosedSurfaceR4

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound_oai := @OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound_oai
