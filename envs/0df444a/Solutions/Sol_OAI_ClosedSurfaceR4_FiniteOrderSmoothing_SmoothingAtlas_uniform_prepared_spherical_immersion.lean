-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:20.953518+00:00
-- url     : https://prove2.me/submissions/b4efb4b6-b752-4df6-971b-2ba16a499ed4

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_spherical_preparation_correction

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




end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPullback
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma metricPullback_pos (g : SmoothMetric M) {φ : Base → M} {x : Base}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, Base) planeModel φ x)) {v : Base} (hv : v ≠ 0) :
    0 < metricPullback g φ x v v := by
  apply g.pos
  intro hz
  apply hv
  apply hi
  exact hz.trans (map_zero _).symm

lemma coordinateMetric_evaluate (g : SmoothMetric M) (p : M) (x v w : Base) :
    PhaseMean.evaluate (coordinateMetric g p x) v w =
      metricPullback g (coordinateInverse p) x v w := by
  let D : Base →L[ℝ] TangentSpace planeModel (coordinateInverse p x) :=
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) x
  change PhaseMean.evaluate (fun i => g.inner (coordinateInverse p x)
      (D (PhaseMean.firstDirection i)) (D (PhaseMean.secondDirection i))) v w =
    g.inner (coordinateInverse p x) (D v) (D w)
  have he (v : Base) : v = v.1 • dx + v.2 • dy := by
    ext <;> simp [dx,dy]
  conv_rhs => rw [he v, he w]
  simp only [PhaseMean.evaluate,
    PhaseMean.firstDirection, PhaseMean.secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead, Function.comp_apply,
    map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [g.symm _
    (D dy) (D dx)]
  dsimp
  ring

lemma tensor_positive_iff (H : PhaseMean.Tensor) :
    (∀ v : Base, v ≠ 0 → 0 < PhaseMean.evaluate H v v) ↔
      0 < H 0 ∧ 0 < H 0 * H 2 - (H 1)^2 := by
  constructor
  · intro h
    have h₀ : 0 < H 0 := by
      simpa [PhaseMean.evaluate] using h (1, 0) (by simp)
    have hv : (-H 1, H 0) ≠ (0 : Base) := by
      intro he
      have he' := congrArg Prod.snd he
      exact h₀.ne' he'
    have hh := h (-H 1, H 0) hv
    have he : PhaseMean.evaluate H (-H 1, H 0) (-H 1, H 0) = H 0 * (H 0 * H 2 - (H 1)^2) := by
      simp only [PhaseMean.evaluate]
      ring
    rw [he] at hh
    exact ⟨h₀, (mul_pos_iff_of_pos_left h₀).mp hh⟩
  · rintro ⟨h₀, hd⟩ v hv
    have he : H 0 * PhaseMean.evaluate H v v =
        (H 0 * v.1 + H 1 * v.2)^2 + (H 0 * H 2 - (H 1)^2) * v.2^2 := by
      simp only [PhaseMean.evaluate]
      ring
    apply (mul_pos_iff_of_pos_left h₀).mp
    rw [he]
    by_cases hv₂ : v.2 = 0
    · have hv₁ : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Prod.ext hz hv₂
      simp only [hv₂, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_pos_of_ne_zero (mul_ne_zero h₀.ne' hv₁)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hd (sq_pos_of_ne_zero hv₂))


end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
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

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateInverse_mfderiv_injective (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    Function.Injective (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) := by
  have hxt : x ∈ (coordinateChart p).target := by rwa [coordinateChart_target]
  have hs : coordinateInverse p x ∈ (coordinateChart p).source := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).map_target hxt
  have hi := ((coordinateInverse_smoothOn p) x hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) (coordinateInverse p x) hs).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hs)
  have he : coordinateChart p ∘ coordinateInverse p =ᶠ[𝓝 x] id := by
    filter_upwards [(coordinateDomain_open p).mem_nhds hx] with y hy
    change coordinateChart p (coordinateInverse p y) = y
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).right_inv (by rwa [coordinateChart_target])
  have hd : (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) (coordinateInverse p x)).comp
      (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) =
      ContinuousLinearMap.id ℝ SmallModes.Base := by
    rw [← mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp)),
      he.mfderiv_eq,mfderiv_id]
    rfl
  intro v w hv
  have hvw := congrArg (mfderiv planeModel 𝓘(ℝ,SmallModes.Base)
    (coordinateChart p) (coordinateInverse p x)) hv
  have hdv := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L v) hd
  have hdw := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L w) hd
  exact hdv.symm.trans (hvw.trans hdw)

lemma coordinateMetric_positive (g : SmoothMetric M) (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    0 < coordinateMetric g p x 0 ∧
      0 < coordinateMetric g p x 0 * coordinateMetric g p x 2 - (coordinateMetric g p x 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [coordinateMetric_evaluate]
  exact metricPullback_pos g (coordinateInverse_mfderiv_injective p hx) hv



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma coordinateInverse_mfderiv_right (p : M) {q : M}
    (hq : q ∈ (coordinateChart p).source) :
    (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) (coordinateChart p q)).comp
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q) =
    ContinuousLinearMap.id ℝ (TangentSpace planeModel q) := by
  have hx : coordinateChart p q ∈ coordinateDomain p := by
    rw [← coordinateChart_target]
    exact (coordinateChart p).map_source hq
  have hi := ((coordinateInverse_smoothOn p) _ hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) q hq).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hq)
  have he : coordinateInverse p ∘ coordinateChart p =ᶠ[𝓝 q] id := by
    filter_upwards [(coordinateChart p).open_source.mem_nhds hq] with a ha
    change coordinateInverse p (coordinateChart p a) = a
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).left_inv ha
  rw [← mfderiv_comp q (hi.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)),
    he.mfderiv_eq,mfderiv_id]
  try rfl

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma coordinateMetric_pullback_chart (g : SmoothMetric M) (p : M) {q : M}
    (hq : q ∈ (coordinateChart p).source) (v w : TangentSpace planeModel q) :
    PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q))
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q v)
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q w) = g.inner q v w := by
  let D : TangentSpace planeModel q →L[ℝ] SmallModes.Base :=
    mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q
  change PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q)) (D v) (D w) =
    g.inner q v w
  rw [coordinateMetric_evaluate]
  have hinv : coordinateInverse p (coordinateChart p q) = q := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).left_inv hq
  let I : SmallModes.Base →L[ℝ] TangentSpace planeModel q :=
    mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) (coordinateChart p q)
  have hcomp : I.comp D = ContinuousLinearMap.id ℝ (TangentSpace planeModel q) :=
    coordinateInverse_mfderiv_right p hq
  have hv : I (D v) = v := congrArg (fun L => L v) hcomp
  have hw : I (D w) = w := congrArg (fun L => L w) hcomp
  change g.inner (coordinateInverse p (coordinateChart p q)) (I (D v)) (I (D w)) =
    g.inner q v w
  calc
    _ = g.inner (coordinateInverse p (coordinateChart p q)) v w :=
      congrArg₂ (fun a b : TangentSpace planeModel q =>
        g.inner (coordinateInverse p (coordinateChart p q)) a b) hv hw
    _ = g.inner q v w := congrArg (fun r => g.inner r v w) hinv

end ClosedSurfaceR4

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_C1ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing C1 maps on the fixed finite surface atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_C1 (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) 1 f) : ContDiff ℝ 1 (localize p ψ f) := by
  have hchart := (chart_symm_smooth p).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)
  have hlocal : ContDiffOn ℝ 1
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target :=
    ((((hψ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_contMDiffOn hchart).pow 2).smul
      (hf.comp_contMDiffOn hchart)).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  · obtain ⟨y,hy,hxy⟩ := localize_tsupport p hsupp f hx
    have hxT : x ∈ (chart p).target := hxy ▸ (chart p).map_source (hsupp hy)
    apply (hlocal.contDiffAt ((chart p).open_target.mem_nhds hxT)).congr_of_eventuallyEq
    filter_upwards [(chart p).open_target.mem_nhds hxT] with z hz
    exact indicator_of_mem hz _
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma continuous_weightedJet {w : Base → ℝ} {l : Base → V}
    (hw : ContDiff ℝ 1 w) (hl : ContDiff ℝ 1 l) : Continuous (weightedJet w l) := by
  exact (hw.continuous.smul (hl.continuous_fderiv one_ne_zero)).sub
    ((ContinuousLinearMap.smulRightL ℝ Base V).continuous₂.comp
      ((hw.continuous_fderiv one_ne_zero).prodMk hl.continuous))

lemma weightedJet_eq_smul {w : Base → ℝ} {l h : Base → V} {x : Base}
    (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x)
    (he : l =ᶠ[𝓝 x] fun y => w y • h y) :
    weightedJet w l x = (w x)^2 • fderiv ℝ h x := by
  unfold weightedJet
  rw [he.fderiv_eq, fderiv_fun_smul hw hh, he.self_of_nhds]
  ext v
  simp only [sub_apply,smul_apply,add_apply,ContinuousLinearMap.smulRight_apply]
  simp only [smul_add,smul_smul,pow_two,mul_comm (w x) ((fderiv ℝ w x) v)]
  abel

lemma weightedJet_sub {w : Base → ℝ} {f g : Base → V} {x : Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    weightedJet w (g-f) x = weightedJet w g x-weightedJet w f x := by
  unfold weightedJet
  rw [fderiv_sub hg hf]
  ext v
  simp only [sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,Pi.sub_apply,smul_sub]
  abel

lemma norm_weightedJet_le {w : Base → ℝ} {l : Base → V} {x : Base} {C : ℝ}
    (hl : ‖l x‖ ≤ C) (hd : ‖fderiv ℝ l x‖ ≤ C) :
    ‖weightedJet w l x‖ ≤ (‖w x‖+‖fderiv ℝ w x‖)*C := by
  calc
    _ ≤ ‖w x • fderiv ℝ l x‖+‖(fderiv ℝ w x).smulRight (l x)‖ := norm_sub_le _ _
    _ = ‖w x‖*‖fderiv ℝ l x‖+‖fderiv ℝ w x‖*‖l x‖ := by
      rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ ‖w x‖*C+‖fderiv ℝ w x‖*C := by gcongr
    _ = _ := by ring

theorem compact_injective_stability {K : Set (Base →L[ℝ] V)}
    (hK : IsCompact K) (hI : ∀ L ∈ K, Function.Injective L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ L ∈ K, ∀ H : Base →L[ℝ] V,
      ‖H-L‖ < ε → Function.Injective H := by
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open
    ContinuousLinearMap.isOpen_injective hI
  exact ⟨ε,hε,fun L hL H hH => he
    (Metric.mem_thickening_iff.mpr ⟨L,hL,by simpa only [dist_eq_norm] using hH⟩)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

lemma localizedWeight_smooth (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source) :
    ContDiff ℝ ∞ (localizedWeight p ψ) := localize_smooth p hψ hs contMDiff_const

omit [CompactSpace M] in
lemma fderiv_comp_chart_symm {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {x : Base}
    (hx : x ∈ (chart p).target) :
    fderiv ℝ (f ∘ (chart p).symm) x =
      (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x (hf.mdifferentiable one_ne_zero).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt_symm hx)

lemma localized_weightedJet {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) :
    weightedJet (localizedWeight p ψ) (localize p ψ f) x =
      (ψ ((chart p).symm x))^4 •
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
  have hh : DifferentiableAt ℝ (f ∘ (chart p).symm) x :=
    ((hf.mdifferentiable one_ne_zero).mdifferentiableAt.comp x
      ((chart_mdifferentiable p).mdifferentiableAt_symm hx)).differentiableAt
  have he : localize p ψ f =ᶠ[𝓝 x]
      fun y => localizedWeight p ψ y • (f ∘ (chart p).symm) y := by
    filter_upwards [(chart p).open_target.mem_nhds hx] with y hy
    simp only [localizedWeight,localize,indicator_of_mem hy,smul_eq_mul,mul_one,
      Function.comp_apply]
  rw [weightedJet_eq_smul ((localizedWeight_smooth p hψ hs).differentiable (by simp) x) hh he,
    fderiv_comp_chart_symm hf p hx]
  have hw : localizedWeight p ψ x = (ψ ((chart p).symm x))^2 := by
    simp only [localizedWeight,localize,indicator_of_mem hx,smul_eq_mul,mul_one]
  rw [hw,← pow_mul]
  norm_num
  rfl

/-- The weighted jet loses no immersion information wherever its weight is
nonzero; the chart differential is an isomorphism there. -/
lemma localized_weightedJet_injective_iff {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) (hw : ψ ((chart p).symm x) ≠ 0) :
    Function.Injective (weightedJet (localizedWeight p ψ) (localize p ψ f) x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) := by
  rw [localized_weightedJet hf p hψ hs hx]
  constructor
  · intro hi
    have hcomp : Function.Injective
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
      intro v u h
      apply hi
      change (ψ ((chart p).symm x))^4 •
          ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
            (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) v = _
      exact congrArg ((ψ ((chart p).symm x))^4 • ·) h
    change Function.Injective
      ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) ∘
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) at hcomp
    exact hcomp.of_comp_right ((chart_mdifferentiable p).symm.mfderiv_surjective hx)
  · intro hi
    exact (smul_right_injective V (pow_ne_zero 4 hw)).comp
      (hi.comp ((chart_mdifferentiable p).symm.mfderiv_injective hx))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionApproximation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing a compact C1 immersion while keeping its differential injective. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma coreThreshold_pos : 0 < A.coreThreshold := by unfold coreThreshold; positivity

omit [CompactSpace M] in
lemma weightCore_nonzero (i : A.centers) {p : M} (hp : p ∈ A.weightCore i) :
    A.weight i p ≠ 0 := by
  intro hz
  have h := A.coreThreshold_pos
  change A.coreThreshold ≤ (A.weight i p)^2 at hp
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hp
  exact (not_lt_of_ge hp) h

omit [CompactSpace M] in
lemma weightCore_source (i : A.centers) : A.weightCore i ⊆ (chart (i : M)).source :=
  fun _ hp => A.weight_support i (subset_tsupport _ (A.weightCore_nonzero i hp))

lemma weightCore_compact (i : A.centers) : IsCompact (A.weightCore i) :=
  (isClosed_le continuous_const ((A.weight_smooth i).continuous.pow 2)).isCompact

lemma coordinateCore_compact (i : A.centers) : IsCompact (A.coordinateCore i) :=
  (A.weightCore_compact i).image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.weightCore_source i))

omit [CompactSpace M] in
lemma mem_some_weightCore (p : M) : ∃ i : A.centers, p ∈ A.weightCore i := by
  classical
  by_contra hn
  have hi (i : A.centers) : (A.weight i p)^2 ≤ A.coreThreshold :=
    le_of_lt (lt_of_not_ge (fun h => hn ⟨i,h⟩))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset A.centers)) (fun i _ => hi i)
  rw [A.partition p] at hs
  have hcount : (∑ _i : A.centers, A.coreThreshold) =
      (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) := by
    simp [coreThreshold,div_eq_mul_inv]
  rw [hcount] at hs
  have hlt : (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (not_lt_of_ge hs) hlt

omit [CompactSpace M] in
lemma coordinateCore_target (i : A.centers) : A.coordinateCore i ⊆ (chart (i : M)).target := by
  rintro _ ⟨p,hp,rfl⟩
  exact (chart (i : M)).map_source (A.weightCore_source i hp)

omit [CompactSpace M] in
lemma coordinateCore_weight_nonzero (i : A.centers) {x : Base}
    (hx : x ∈ A.coordinateCore i) : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [(chart (i : M)).left_inv (A.weightCore_source i hp)]
  exact A.weightCore_nonzero i hp

/-- Every C1 immersion has a positive tolerance in the finite localized C1
norm within which all C1 maps remain immersions. -/
theorem immersion_C1_tolerance {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) 1 g →
      A.C1Bound ε (g-f) → ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g p) := by
  classical
  let w : A.centers → Base → ℝ := fun i => localizedWeight (i : M) (A.weight i)
  let l : A.centers → (M → V) → Base → V := fun i h => localize (i : M) (A.weight i) h
  have hw (i : A.centers) : ContDiff ℝ 1 (w i) :=
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hl (i : A.centers) : ContDiff ℝ 1 (l i f) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  have hdata (i : A.centers) : ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      (∀ x ∈ A.coordinateCore i, ‖w i x‖+‖fderiv ℝ (w i) x‖ ≤ D) ∧
      ∀ x ∈ A.coordinateCore i, ∀ H : Base →L[ℝ] V,
        ‖H-weightedJet (w i) (l i f) x‖ < r → Function.Injective H := by
    obtain ⟨r,hr,hrb⟩ := compact_injective_stability
      ((A.coordinateCore_compact i).image (continuous_weightedJet (hw i) (hl i)))
      (by
        rintro _ ⟨x,hx,rfl⟩
        exact (localized_weightedJet_injective_iff hf (i : M) (A.weight_smooth i)
          (A.weight_support i) (A.coordinateCore_target i hx)
          (A.coordinateCore_weight_nonzero i hx)).mpr (hI _))
    obtain ⟨C,hC⟩ := (A.coordinateCore_compact i).exists_bound_of_continuousOn
      (((hw i).continuous.norm.add ((hw i).continuous_fderiv one_ne_zero).norm).continuousOn)
    refine ⟨r,1+|C|,hr,by positivity,?_,?_⟩
    · intro x hx
      exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))
    · intro x hx H hH
      exact hrb _ (mem_image_of_mem _ hx) H hH
  choose r D hr hD hDb hrb using hdata
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : A.centers, ε < r i / D i :=
    Filter.eventually_all.mpr (fun i => gt_mem_nhds (div_pos (hr i) (hD i)))
  obtain ⟨η,hη,hηb⟩ := Metric.eventually_nhds_iff.mp hev
  let ε := η/2
  have hε : 0 < ε := half_pos hη
  have hεi (i : A.centers) : ε < r i / D i :=
    hηb (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using half_lt_self hη) i
  refine ⟨ε,hε,?_⟩
  intro g hg hb p
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hgl : ContDiff ℝ 1 (l i g) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hg
  have hclose : ‖weightedJet (w i) (l i g) x-weightedJet (w i) (l i f) x‖ < r i := by
    have he : weightedJet (w i) (localize (i : M) (A.weight i) (g-f)) x =
        weightedJet (w i) (l i g) x-weightedJet (w i) (l i f) x := by
      have hlsub : localize (i : M) (A.weight i) (g-f) = l i g-l i f := by
        funext y
        by_cases hy : y ∈ (chart (i : M)).target
        · simp only [l,localize,indicator_of_mem hy,Pi.sub_apply,smul_sub]
        · simp only [l,localize,indicator_of_notMem hy,Pi.sub_apply,sub_self]
      rw [hlsub]
      exact weightedJet_sub ((hl i).differentiable one_ne_zero x)
        (hgl.differentiable one_ne_zero x)
    rw [← he]
    calc
      _ ≤ (‖w i x‖+‖fderiv ℝ (w i) x‖)*ε := norm_weightedJet_le (hb i x).1 (hb i x).2
      _ ≤ D i*ε := mul_le_mul_of_nonneg_right (hDb i x hx) hε.le
      _ < r i := by simpa only [mul_comm] using (lt_div_iff₀ (hD i)).mp (hεi i)
  have hgi := (localized_weightedJet_injective_iff hg (i : M) (A.weight_smooth i)
    (A.weight_support i) (A.coordinateCore_target i hx)
    (A.coordinateCore_weight_nonzero i hx)).mp (hrb i x hx _ hclose)
  change Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g
    ((chart (i : M)).symm (chart (i : M) p))) at hgi
  rw [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hgi
  exact hgi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLinearLowerBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact family of injective chart differentials has one positive
lower bound, retained by a fixed operator-norm perturbation. -/
noncomputable section
open Set Metric
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial

theorem compact_injective_lower_bound {K : Set (Base →L[ℝ] Space)}
    (hK : IsCompact K) (hI : ∀ L ∈ K, Function.Injective L) :
    ∃ c : ℝ, 0 < c ∧ ∀ L ∈ K, ∀ H : Base →L[ℝ] Space, ‖H-L‖ ≤ c →
      ∀ v : Base, c*‖v‖ ≤ ‖H v‖ := by
  let S : Set ((Base →L[ℝ] Space) × Base) := K ×ˢ sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hf : Continuous (fun z : (Base →L[ℝ] Space) × Base => ‖z.1 z.2‖) := by fun_prop
  have hp : ∀ z ∈ S, 0 < ‖z.1 z.2‖ := by
    rintro ⟨L,v⟩ ⟨hL,hv⟩
    apply norm_pos_iff.mpr
    intro hz
    have hv0 : v = 0 := hI L hL (hz.trans L.map_zero.symm)
    have hnorm : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    rw [hv0,norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨μ,hμ,hbound⟩ := hS.exists_forall_le' hf.continuousOn hp
  have hbase (L : Base →L[ℝ] Space) (hL : L ∈ K) (v : Base) : μ*‖v‖ ≤ ‖L v‖ := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hh := hbound (L,u) ⟨hL,by simpa only [mem_sphere,dist_zero_right] using hu⟩
    change μ ≤ ‖L u‖ at hh
    rw [show L u = ‖v‖⁻¹ • L v from L.map_smul _ _] at hh
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm] at hh
    exact (le_div_iff₀ hn).mp (by simpa only [div_eq_inv_mul] using hh)
  refine ⟨μ/2,half_pos hμ,?_⟩
  intro L hL H hHL v
  have hd : ‖(L-H) v‖ ≤ (μ/2)*‖v‖ := by
    exact ((L-H).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (by simpa only [norm_sub_rev] using hHL) (norm_nonneg v))
  have he : L v = H v+(L-H) v := by simp
  have ht : ‖L v‖ ≤ ‖H v‖+‖(L-H) v‖ := by rw [he]; exact norm_add_le _ _
  have hb := hbase L hL v
  nlinarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed
local instance coordinateFiberSpace_r303330_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_r303330_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r303330_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r303330_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricLowerBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One lower bound for the coordinate differentials of every immersion
in a fixed C1 neighborhood. The coordinate cores cover the surface. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_coordinate_metric_lower_bound {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 δ (G-F) →
      ∀ i : A.centers, ∀ x ∈ A.coordinateCore i, ∀ v : Base,
        c*‖v‖ ≤ ‖fderiv ℝ (A.vectorChartRead i G) x v‖ := by
  classical
  have hcore (i : A.centers) : A.coordinateCore i ⊆ (A.chartWeightCompact i : Set Base) := by
    rintro x ⟨p,hp,rfl⟩
    exact ⟨p,subset_tsupport _ (A.weightCore_nonzero i hp),rfl⟩
  have hdata (i : A.centers) : ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ A.coordinateCore i, ∀ H : Base →L[ℝ] Space,
        ‖H-fderiv ℝ (A.vectorChartRead i F) x‖ ≤ c → ∀ v, c*‖v‖ ≤ ‖H v‖ := by
    have hcont := ((A.vectorChartRead_smooth i hF).fderiv_right (m := ∞) (by simp)).continuous
    obtain ⟨c,hc,hbound⟩ := compact_injective_lower_bound
      ((A.coordinateCore_compact i).image hcont) (by
        rintro _ ⟨x,hx,rfl⟩
        rw [A.vectorChartRead_fderiv i hF (hcore i hx),
          fderiv_comp_chart_symm (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M) (A.coordinateCore_target i hx)]
        exact (hImm _).comp ((chart_mdifferentiable (i : M)).symm.mfderiv_injective
          (A.coordinateCore_target i hx)))
    exact ⟨c,hc,fun x hx => hbound _ (mem_image_of_mem _ hx)⟩
  choose c hc hb using hdata
  choose R hR hr using fun i : A.centers => A.vectorChartRead_bound (V := Space) i 1
  obtain ⟨δ,hδ,_,hδi⟩ := finite_positive_threshold (fun i => c i/(R i+1))
    (fun i => div_pos (hc i) (by have := hR i; positivity))
  obtain ⟨a,ha,_,hai⟩ := finite_positive_threshold c hc
  refine ⟨δ,a,hδ,ha,?_⟩
  intro G hG hclose i x hx v
  have hread := hr i (G-F) 1 δ zero_lt_one le_rfl hδ.le (hG.sub hF) hclose
  have hd := hread 1 le_rfl x (mem_univ x)
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] at hd
  have he : A.vectorChartRead i (G-F) = A.vectorChartRead i G-A.vectorChartRead i F := by
    funext y
    by_cases hy : y ∈ (chart (i : M)).target <;>
      simp [vectorChartRead,localize,hy,smul_sub]
  rw [he,fderiv_sub ((A.vectorChartRead_smooth i hG).differentiable (by simp) x)
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) x)] at hd
  have hsize : R i*δ ≤ c i := by
    have hRi := hR i
    have he := (le_div_iff₀ (by positivity : 0 < R i+1)).mp (hδi i)
    nlinarith
  exact (mul_le_mul_of_nonneg_right (hai i) (norm_nonneg v)).trans
    (hb i x hx _ (hd.trans hsize) v)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricAtlasReference
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth metric section gives the reference tensor used by
the compact good-phase construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean
open JetPolynomial (planeCoordinateIsometry)
open JetPolynomial.Perturbation (modeSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
local instance metricReferenceSectionNormed_r303330_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r303330_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_inner_smooth (g : SmoothMetric M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (g.inner p)) := g.contMDiff

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
local instance metricReferenceSectionNormed_r303330_2 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r303330_2 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorComponent_metric (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : Plane) :
    A.bundleComponent A.tensorTriv i g.inner p v w =
      evaluate (coordinateMetric g (i : M) (coordinateChart (i : M) p))
        (planeCoordinates v) (planeCoordinates w) := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hp' : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source, chart_source] using hp
  have hc := A.tensorComponent_tangentCoordinates i g.inner hp
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w)
  simp only [Trivialization.continuousLinearMapAt_symmL _ ht] at hc
  have hm := coordinateMetric_pullback_chart g (i : M) hp'
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w)
  rw [A.coordinateChart_tangentCoordinates i hp] at hm
  change evaluate (coordinateMetric g (i : M) (coordinateChart (i : M) p))
      (planeCoordinates
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)))
      (planeCoordinates
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w))) =
      g.inner p
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w) at hm
  simp only [Trivialization.continuousLinearMapAt_symmL _ ht] at hm
  exact hc.trans hm.symm

lemma tensorPlaneRead_metric_on_weight (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorPlaneRead i g.inner (planeCoordinateIsometry (chart (i : M) p)) =
      coordinateMetric g (i : M) (coordinateChart (i : M) p) := by
  change A.tensorChartRead i g.inner
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) p))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, A.tensorChartRead_on_weight i g.inner hp]
  ext k
  rw [fiberToThree_apply, A.tensorComponent_metric g i (A.weight_support i hp)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

variable [CompactSpace M]

lemma tensorPlaneRead_metric (g : SmoothMetric M) (i : A.centers)
    {x : SmallModes.Base} (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRead i g.inner x = coordinateMetric g (i : M) x := by
  change x ∈ planeCoordinateIsometry '' ((chart (i : M)) '' tsupport (A.weight i)) at hx
  rcases hx with ⟨y, ⟨p, hp, rfl⟩, rfl⟩
  exact A.tensorPlaneRead_metric_on_weight g i hp

lemma tensorPlaneRead_metric_smooth (g : SmoothMetric M) (i : A.centers) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i g.inner) :=
  A.tensorPlaneRead_smooth i (metric_inner_smooth g)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact positive metric range and global first-order bounds for atlas readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadBoundsFiberNormed
local instance metricReadBoundsFiberSpace_r303330_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricReadBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadBoundsFiberNormed
local instance metricReadBoundsFiberSpace_r303330_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricReadBoundsDualSmul_r303330_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricReadBoundsSectionNormed_r303330_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadBoundsSectionSpace_r303330_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metricReadSupport_domain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

theorem metric_plane_read_bounds (g : SmoothMetric M) :
    ∃ T : Set PhaseMean.Tensor, ∃ B : ℝ, IsCompact T ∧
      (∀ H ∈ T, 0 < H 0) ∧ (∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) ∧ 1 ≤ B ∧
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        A.tensorPlaneRead i g.inner x ∈ T) ∧
      (∀ i x, ‖A.tensorPlaneRead i g.inner x‖ ≤ B) ∧
      (∀ i x y, ‖A.tensorPlaneRead i g.inner y-A.tensorPlaneRead i g.inner x‖ ≤ B*‖y-x‖) := by
  classical
  let T : Set PhaseMean.Tensor := ⋃ i : A.centers,
    A.tensorPlaneRead i g.inner '' (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)
  have hT : IsCompact T := isCompact_iUnion (fun i =>
    (modeSupport (A.chartWeightCompact i)).isCompact.image (A.tensorPlaneRead_metric_smooth g i).continuous)
  have hpos (H : PhaseMean.Tensor) (hH : H ∈ T) :
      0 < H 0 ∧ 0 < H 0*H 2-(H 1)^2 := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hH
    rw [A.tensorPlaneRead_metric g i hx]
    exact coordinateMetric_positive g (i : M) (A.metricReadSupport_domain i hx)
  obtain ⟨C,hC,hbound⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 1 g.contMDiff
  choose D hD hd using fun i : A.centers => A.tensorPlaneRead_bound i 1
  let B : ℝ := 1+∑ i : A.centers, D i*C
  have hB : 1 ≤ B := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (hD i) hC)
    change 1 ≤ 1+∑ i : A.centers, D i*C
    linarith
  have hb (i : A.centers) : WeightedEstimates.WeightedBound univ 1 1 B (A.tensorPlaneRead i g.inner) := by
    apply (hd i g.inner 1 C zero_lt_one le_rfl hC g.contMDiff hbound).mono_const
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg (hD i) hC) (Finset.mem_univ i)
    change D i*C ≤ 1+∑ i : A.centers, D i*C
    linarith
  refine ⟨T,B,hT,fun H hH => (hpos H hH).1,fun H hH => (hpos H hH).2,hB,
    fun i x hx => mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩,
    fun i x => (hb i).norm_le (mem_univ x),?_⟩
  intro i x y
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _
    (convex_univ : Convex ℝ (univ : Set SmallModes.Base)) (mem_univ x) (mem_univ y)
  · intro a _
    exact (A.tensorPlaneRead_metric_smooth g i).differentiable (by simp) a
  · intro a _
    have hh := (hb i).deriv_le zero_lt_one (le_refl 1) (mem_univ a)
    simpa only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasBackgroundLowerBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed coordinate lower bound dominates any fixed smooth background
metric. Both constants are chosen before the finite preparation set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma coordinateChart_differential (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart (i : M)) p =
      planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (surfaceDifferential (chart (i : M)) p) := by
  have he : (coordinateChart (i : M) : M → SmallModes.Base) =
      planeCoordinateIsometry ∘ (chart (i : M)) := rfl
  have hleft : MDifferentiable 𝓘(ℝ,Base) 𝓘(ℝ,SmallModes.Base) planeCoordinateIsometry :=
    (planeCoordinateIsometry.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := mfderiv_comp p hleft.mdifferentiableAt
    ((chart_mdifferentiable (i : M)).mdifferentiableAt hp)
  rw [mfderiv_eq_fderiv] at hh
  have hd : fderiv ℝ planeCoordinateIsometry (chart (i : M) p) =
      planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap :=
    planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [hd] at hh
  rw [he]
  exact hh

theorem uniform_background_metric_lower_bound (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 δ (G-F) →
      ∀ (p : M) (v : TangentSpace planeModel p),
        c*g.inner p v v ≤ inducedForm G p v v := by
  obtain ⟨δ,a,hδ,ha,hlower⟩ := A.uniform_coordinate_metric_lower_bound hF hImm
  obtain ⟨T,B,_,_,_,hB,_,hbound,_⟩ := A.metric_plane_read_bounds g
  refine ⟨δ,a^2/(4*B+1),hδ,div_pos (sq_pos_of_pos ha) (by positivity),?_⟩
  intro G hG hclose p v
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ (A.weightCore_nonzero i hi)
  let u := surfaceDifferential (chart (i : M)) p v
  have hmetric : g.inner p v v ≤ (4*B)*‖u‖^2 := by
    have hcoord : p ∈ (coordinateChart (i : M)).source := by
      simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
    rw [← coordinateMetric_pullback_chart g (i : M) hcoord v v,
      ← A.tensorPlaneRead_metric_on_weight g i hp,A.coordinateChart_differential i (A.weight_support i hp)]
    change PhaseMean.evaluate _ (planeCoordinateIsometry u) (planeCoordinateIsometry u) ≤ _
    calc
      _ ≤ ‖PhaseMean.evaluate _ (planeCoordinateIsometry u) (planeCoordinateIsometry u)‖ := le_abs_self _
      _ ≤ 4*‖A.tensorPlaneRead i g.inner (planeCoordinateIsometry (chart (i : M) p))‖*
          ‖planeCoordinateIsometry u‖*‖planeCoordinateIsometry u‖ := PhaseMean.norm_evaluate_le _ _ _
      _ ≤ (4*B)*‖u‖^2 := by
        rw [planeCoordinateIsometry.norm_map]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hbound i (planeCoordinateIsometry (chart (i : M) p))))
          (sq_nonneg ‖u‖)]
  have hL := hlower G hG hclose i (chart (i : M) p) (mem_image_of_mem _ hi) u
  have he : fderiv ℝ (A.vectorChartRead i G) (chart (i : M) p) u =
      surfaceDifferential G p v := by
    rw [A.vectorChartRead_differential i hG hp]
    rfl
  rw [he] at hL
  have hsq : a^2*‖u‖^2 ≤ ‖surfaceDifferential G p v‖^2 := by
    nlinarith [mul_nonneg ha.le (norm_nonneg u),norm_nonneg (surfaceDifferential G p v)]
  have hc : 0 ≤ a^2/(4*B+1) := by positivity
  have hcomp : a^2/(4*B+1)*g.inner p v v ≤ a^2*‖u‖^2 := by
    calc
      _ ≤ a^2/(4*B+1)*((4*B)*‖u‖^2) := mul_le_mul_of_nonneg_left hmetric hc
      _ = (a^2*((4*B)*‖u‖^2))/(4*B+1) := by ring
      _ ≤ a^2*‖u‖^2 := by
        apply (div_le_iff₀ (by positivity : 0 < 4*B+1)).2
        nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg ‖u‖)]
  exact hcomp.trans (by simpa only [inducedForm,real_inner_self_eq_norm_sq] using hsq)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedJetCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second jets of radial normalization, for the finite-point flattening
of the starting spherical immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma radialNormalize_smoothAt {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialNormalize x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SafeRadialNormalization
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A globally smooth extension of radial normalization that agrees with it
outside the half-unit ball. Only this fixed extension is used in atlas bounds. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma safeRadialNormalize_eq {x : Space} (hx : (1/2 : ℝ) ≤ ‖x‖) :
    safeRadialNormalize x = radialNormalize x := by
  have hz : normalizationCutoff x = 0 := normalizationCutoff.zero_of_le_dist
    (by simpa only [normalizationCutoff,dist_zero_right] using hx)
  simp [safeRadialNormalize,hz]

lemma safeRadialNormalize_smooth : ContDiff ℝ ∞ safeRadialNormalize := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : ContDiffAt ℝ ∞ (fun _ : Space => (0 : Space)) 0 := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    have he : normalizationCutoff =ᶠ[𝓝 (0 : Space)] (fun _ => (1 : ℝ)) :=
      normalizationCutoff.eventuallyEq_one
    filter_upwards [he] with y hy
    simp [safeRadialNormalize,hy]
  · exact (contDiffAt_const.sub normalizationCutoff.contDiff.contDiffAt).smul
      (radialNormalize_smoothAt hx)

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalizationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed C2 atlas budget for radial normalization. A smooth extension
through zero is used only outside the region contributing to localization. -/
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma normalized_localization_eq (i : A.centers) (H : M → Space)
    (hH : ∀ p, (1/2 : ℝ) ≤ ‖H p‖) :
    localize (i : M) (A.weight i) (radialNormalize ∘ H) =
      fun x => (A.chartWeight i x)^2 • safeRadialNormalize (A.vectorChartRead i H x) := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · by_cases hw : A.weight i ((chart (i : M)).symm x) = 0
    · simp [localize,chartWeight,hx,hw]
    · have hp := subset_tsupport (A.weight i) hw
      have ho := A.outer_one i _ hp
      simp only [vectorChartRead,localize,chartWeight,indicator_of_mem hx,ho,one_pow,one_smul,
        Function.comp_apply]
      rw [safeRadialNormalize_eq (hH _)]
  · simp [localize,chartWeight,hx]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma radial_normalization_smooth {H : M → Space}
    (hH : ContMDiff planeModel spaceModel ∞ H) (hb : ∀ p, (1/2 : ℝ) ≤ ‖H p‖) :
    ContMDiff planeModel spaceModel ∞ (radialNormalize ∘ H) := by
  have he : radialNormalize ∘ H = safeRadialNormalize ∘ H := by
    funext p
    exact (safeRadialNormalize_eq (hb p)).symm
  rw [he]
  exact safeRadialNormalize_smooth.contMDiff.comp hH

lemma chartWeight_square_compact (i : A.centers) :
    HasCompactSupport (fun x => (A.chartWeight i x)^2) := by
  have hw : HasCompactSupport (A.chartWeight i) :=
    (A.chartWeightCompact i).isCompact.of_isClosed_subset (isClosed_tsupport _)
      (A.supportedChartWeight i).tsupport_subset
  apply hw.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx hz
  exact hx (by simp [hz])

lemma exists_weighted_bound (m : ℕ) {H : M → Space}
    (hH : ContMDiff planeModel spaceModel ∞ H) :
    ∃ C : ℝ, 0 ≤ C ∧ A.WeightedBound 1 m C H := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hH)
    (localize_compact (i : M) (A.weight_support i) H) m
  exact ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun i =>
    (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))⟩

theorem radial_normalization_C2_budget (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ H : M → Space,
      ContMDiff planeModel spaceModel ∞ H → (∀ p, (1/2 : ℝ) ≤ ‖H p‖) →
      A.WeightedBound 1 2 C H → A.WeightedBound 1 2 D (radialNormalize ∘ H) := by
  classical
  have hlocal (i : A.centers) : ∃ D : ℝ, 0 ≤ D ∧ ∀ H : M → Space,
      ContMDiff planeModel spaceModel ∞ H → (∀ p, (1/2 : ℝ) ≤ ‖H p‖) →
      A.WeightedBound 1 2 C H → WeightedEstimates.WeightedBound univ 1 2 D
        (localize (i : M) (A.weight i) (radialNormalize ∘ H)) := by
    obtain ⟨R,hR,hr⟩ := A.vectorChartRead_bound (V := Space) i 2
    let E := max 1 (R*C)
    have hE : 1 ≤ E := le_max_left _ _
    obtain ⟨B,hB,hb⟩ := compact_coefficient_bound uniqueDiffOn_univ
      (isCompact_closedBall (0 : Space) E) (subset_univ _)
      safeRadialNormalize_smooth.contDiffOn 2
    obtain ⟨W,hW,hw⟩ := compact_smooth_bound ((A.chartWeight_smooth i).pow 2)
      (A.chartWeight_square_compact i) 2
    refine ⟨4*W*(2*B*E^2),by positivity,?_⟩
    intro H hH hnorm hHC
    have hread : WeightedEstimates.WeightedBound univ 1 2 E (A.vectorChartRead i H) :=
      (hr H 1 C zero_lt_one le_rfl (zero_le_one.trans hC) hH hHC).mono_const (le_max_right _ _)
    have hcomp := hread.comp uniqueDiffOn_univ uniqueDiffOn_univ zero_lt_one hE
      (zero_le_one.trans hB) (A.vectorChartRead_smooth i hH).contDiffOn
      safeRadialNormalize_smooth.contDiffOn (fun _ _ => mem_univ _) (by
        intro j hj x hx
        apply hb j hj (A.vectorChartRead i H x)
        simpa only [mem_closedBall,dist_zero_right] using hread.norm_le (mem_univ x))
    rw [A.normalized_localization_eq i H hnorm]
    convert hw.smul_real uniqueDiffOn_univ zero_le_one hW (by positivity)
      ((A.chartWeight_smooth i).pow 2).contDiffOn
      (safeRadialNormalize_smooth.comp (A.vectorChartRead_smooth i hH)).contDiffOn hcomp using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  choose D hD hd using hlocal
  refine ⟨∑ i, D i,Finset.sum_nonneg (fun i _ => hD i),?_⟩
  intro H hH hnorm hb i
  exact (hd i H hH hnorm hb).mono_const
    (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasUniformNorm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform value and first-jet consequences of the fixed atlas norms. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_uniform_norm {f : M → Space} {C : ℝ}
    (hb : A.WeightedBound 1 0 C f) (p : M) :
    ‖f p‖ ≤ (Fintype.card A.centers : ℝ)*C := by
  have hpiece (i : A.centers) : ‖(A.weight i p)^2 • f p‖ ≤ C := by
    by_cases hp : p ∈ (chart (i : M)).source
    · have hh := (hb i).norm_le (mem_univ (chart (i : M) p))
      rw [localize_chart (i : M) (A.weight i) f hp] at hh
      exact hh
    · have hz : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (A.weight_support i h))
      have hC : 0 ≤ C := (norm_nonneg _).trans ((hb i).norm_le (mem_univ 0))
      simpa [hz] using hC
  have he : f p = ∑ i : A.centers, (A.weight i p)^2 • f p := by
    rw [← Finset.sum_smul,A.partition,one_smul]
  rw [he]
  calc
    _ ≤ ∑ i : A.centers, ‖(A.weight i p)^2 • f p‖ := norm_sum_le _ _
    _ ≤ ∑ _i : A.centers, C := Finset.sum_le_sum (fun i _ => hpiece i)
    _ = (Fintype.card A.centers : ℝ)*C := by simp

lemma weightedBound_C1 {f : M → Space} {C : ℝ}
    (hb : A.WeightedBound 1 1 C f) : A.C1Bound C f := by
  intro i x
  refine ⟨(hb i).norm_le (mem_univ x),?_⟩
  have hh := hb i 1 le_rfl x (mem_univ x)
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] using hh

variable [CompactSpace M]

theorem weighted_immersion_tolerance {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 ε (G-F) →
      ∀ p, Function.Injective (mfderiv planeModel spaceModel G p) := by
  obtain ⟨ε,hε,hs⟩ := A.immersion_C1_tolerance (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hI
  exact ⟨ε,hε,fun G hG hb => hs G (hG.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (A.weightedBound_C1 hb)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SafeNormalizationStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed smooth extension acts uniformly continuously on bounded
first jets. This gives the C1 stability used in finite-point preparation. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets
open WeightedEstimates

lemma safeNormalizeFirstJet_continuous : Continuous safeNormalizeFirstJet := by
  exact (safeRadialNormalize_smooth.continuous.comp continuous_fst).prodMk
    (((safeRadialNormalize_smooth.fderiv_right (m := ∞) (by simp)).continuous.comp
      continuous_fst).clm_comp continuous_snd)

theorem safe_normalization_first_jet_stability (C : ℝ) (_hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (x y : Space) (L A : JetPolynomial.Base →L[ℝ] Space),
      ‖x‖ ≤ C → ‖L‖ ≤ C → ‖y-x‖ ≤ δ → ‖A-L‖ ≤ δ →
      ‖safeRadialNormalize y-safeRadialNormalize x‖ ≤ ε ∧
        ‖(fderiv ℝ safeRadialNormalize y).comp A-
          (fderiv ℝ safeRadialNormalize x).comp L‖ ≤ ε := by
  have hu := (isCompact_closedBall (0 : SafeFirstJet) (C+1)).uniformContinuousOn_of_continuous
    safeNormalizeFirstJet_continuous.continuousOn
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min 1 (d/2),lt_min zero_lt_one (half_pos hd),min_le_left _ _,?_⟩
  intro x y L A hx hL hy hA
  let J : SafeFirstJet := (x,L)
  let H : SafeFirstJet := (y,A)
  have hJ : ‖J‖ ≤ C := max_le hx hL
  have hHJ : ‖H-J‖ ≤ min 1 (d/2) := max_le hy hA
  have hH : ‖H‖ ≤ C+1 := by
    calc
      ‖H‖ ≤ ‖H-J‖+‖J‖ := norm_le_norm_sub_add H J
      _ ≤ C+1 := by linarith [min_le_left (1 : ℝ) (d/2)]
  have hdist : dist H J < d := by
    rw [dist_eq_norm]
    exact hHJ.trans_lt ((min_le_right (1 : ℝ) (d/2)).trans_lt (half_lt_self hd))
  have hh := hclose H (by simpa only [mem_closedBall,dist_zero_right] using hH)
    J (by simpa only [mem_closedBall,dist_zero_right] using hJ.trans (by linarith : C ≤ C+1)) hdist
  rw [dist_eq_norm] at hh
  exact ⟨(norm_fst_le _).trans hh.le,(norm_snd_le _).trans hh.le⟩

theorem safe_normalization_C1_stability (f : JetPolynomial.Base → Space)
    (hf : ContDiff ℝ ∞ f) (C : ℝ) (hC : 0 ≤ C)
    (hb : WeightedBound univ 1 1 C f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : JetPolynomial.Base → Space,
      ContDiff ℝ ∞ q → WeightedBound univ 1 1 δ q →
      WeightedBound univ 1 1 ε (fun x => safeRadialNormalize (f x+q x)-safeRadialNormalize (f x)) := by
  obtain ⟨δ,hδ,_,hd⟩ := safe_normalization_first_jet_stability C hC hε
  refine ⟨δ,hδ,?_⟩
  intro q hq hqb
  have hpoint (x : JetPolynomial.Base) :
      ‖safeRadialNormalize (f x+q x)-safeRadialNormalize (f x)‖ ≤ ε ∧
      ‖fderiv ℝ (fun x => safeRadialNormalize (f x+q x)-safeRadialNormalize (f x)) x‖ ≤ ε := by
    have hf₁ := hb 1 le_rfl x (mem_univ x)
    have hq₁ := hqb 1 le_rfl x (mem_univ x)
    simp only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] at hf₁ hq₁
    have hh := hd (f x) (f x+q x) (fderiv ℝ f x) (fderiv ℝ (f+q) x)
      (hb.norm_le (mem_univ x)) hf₁ (by simpa using hqb.norm_le (mem_univ x)) (by
        rw [fderiv_add (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) (hq.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
        simpa using hq₁)
    refine ⟨hh.1,?_⟩
    have hs : HasFDerivAt (fun y => f y+q y) (fderiv ℝ f x+fderiv ℝ q x) x :=
      (hf.differentiable (by simp) x).hasFDerivAt.add
        (hq.differentiable (by simp) x).hasFDerivAt
    have hg := ((safeRadialNormalize_smooth.differentiable (by simp) (f x+q x)).hasFDerivAt.comp x hs).sub
      ((safeRadialNormalize_smooth.differentiable (by simp) (f x)).hasFDerivAt.comp x
        (hf.differentiable (by simp) x).hasFDerivAt)
    have hdf : fderiv ℝ (fun y => safeRadialNormalize (f y+q y)-safeRadialNormalize (f y)) x =
        (fderiv ℝ safeRadialNormalize (f x+q x)).comp (fderiv ℝ f x+fderiv ℝ q x)-
          (fderiv ℝ safeRadialNormalize (f x)).comp (fderiv ℝ f x) := hg.fderiv
    rw [hdf]
    have hs' : fderiv ℝ (f+q) x = fderiv ℝ f x+fderiv ℝ q x := hs.fderiv
    rw [hs'] at hh
    exact hh.2
  intro j hj x hx
  interval_cases j
  · simpa using (hpoint x).1
  · simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] using (hpoint x).2

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalizationStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small C1 perturbations of a spherical immersion remain small after
normalization, in the same fixed atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma normalized_difference_localization (i : A.centers) (F Q : M → Space)
    (hF : ∀ p, ‖F p‖ = 1) (hH : ∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖) :
    localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)-F) =
      fun x => (A.chartWeight i x)^2 •
        (safeRadialNormalize (A.vectorChartRead i F x+A.vectorChartRead i Q x)-
          safeRadialNormalize (A.vectorChartRead i F x)) := by
  have he : radialNormalize ∘ F = F := by
    funext p
    simp [Function.comp_apply,radialNormalize,hF p]
  have heF := A.normalized_localization_eq i F (fun p => by rw [hF]; norm_num)
  rw [he] at heF
  have heH := A.normalized_localization_eq i (F+Q) hH
  have heR : A.vectorChartRead i (F+Q) = A.vectorChartRead i F+A.vectorChartRead i Q :=
    localize_add _ _ _ _
  have hs : localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)-F) =
      localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)) - localize (i : M) (A.weight i) F := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx,smul_sub]
  rw [hs,heH,heF,heR]
  funext x
  simp only [Pi.sub_apply,Pi.add_apply,smul_sub]

omit [CompactSpace M] in
lemma weighted_perturbation_annulus {F Q : M → Space} (hF : ∀ p, ‖F p‖ = 1)
    {δ : ℝ} (hδ : (Fintype.card A.centers : ℝ)*δ ≤ 1/2)
    (hb : A.WeightedBound 1 1 δ Q) : ∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖ := by
  intro p
  have h0 : A.WeightedBound 1 0 δ Q := fun i => (hb i).mono_order (by omega)
  have hn := (A.weightedBound_uniform_norm h0 p).trans hδ
  have he : F p = (F p+Q p)-Q p := by abel
  have ht := norm_sub_le (F p+Q p) (Q p)
  rw [← he,hF] at ht
  linarith

theorem radial_normalization_C1_stability {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : M → Space, ContMDiff planeModel spaceModel ∞ Q →
      A.WeightedBound 1 1 δ Q →
      (∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖) ∧
      A.WeightedBound 1 1 ε (radialNormalize ∘ (F+Q)-F) := by
  classical
  have hlocal (i : A.centers) : ∃ δ : ℝ, 0 < δ ∧ ∀ Q : M → Space,
      ContMDiff planeModel spaceModel ∞ Q → A.WeightedBound 1 1 δ Q →
      (∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖) →
      WeightedEstimates.WeightedBound univ 1 1 ε
        (localize (i : M) (A.weight i) (radialNormalize ∘ (F+Q)-F)) := by
    obtain ⟨W,hW,hw⟩ := compact_smooth_bound ((A.chartWeight_smooth i).pow 2)
      (A.chartWeight_square_compact i) 1
    obtain ⟨C,hC,hCbound⟩ := compact_smooth_bound (A.vectorChartRead_smooth i hF)
      (localize_compact (i : M) (A.outer_support i) F) 1
    obtain ⟨η,hη,hstab⟩ := safe_normalization_C1_stability (A.vectorChartRead i F)
      (A.vectorChartRead_smooth i hF) C hC hCbound
      (div_pos hε (by positivity : 0 < 2*(W+1)))
    obtain ⟨R,hR,hr⟩ := A.vectorChartRead_bound (V := Space) i 1
    refine ⟨η/(R+1),div_pos hη (by positivity),?_⟩
    intro Q hQ hb hnorm
    have hread : WeightedEstimates.WeightedBound univ 1 1 η (A.vectorChartRead i Q) := by
      apply (hr Q 1 (η/(R+1)) zero_lt_one le_rfl (by positivity) hQ hb).mono_const
      have : R*(η/(R+1)) ≤ (R+1)*(η/(R+1)) := by gcongr; linarith
      have he : (R+1)*(η/(R+1)) = η := by field_simp
      rwa [he] at this
    have hc := hstab (A.vectorChartRead i Q) (A.vectorChartRead_smooth i hQ) hread
    rw [A.normalized_difference_localization i F Q hunit hnorm]
    apply (hw.smul_real uniqueDiffOn_univ zero_le_one hW (by positivity)
      ((A.chartWeight_smooth i).pow 2).contDiffOn
      ((safeRadialNormalize_smooth.comp ((A.vectorChartRead_smooth i hF).add
        (A.vectorChartRead_smooth i hQ))).sub
        (safeRadialNormalize_smooth.comp (A.vectorChartRead_smooth i hF))).contDiffOn hc).mono_const
    have he : 2*W*(ε/(2*(W+1))) ≤ 2*(W+1)*(ε/(2*(W+1))) := by gcongr; linarith
    simpa only [pow_one,mul_div_cancel₀ ε (by positivity : 2*(W+1) ≠ 0)] using he
  choose d hd hdb using hlocal
  obtain ⟨δ₁,hδ₁,_,hδ₁i⟩ := finite_positive_threshold d hd
  let δ := min (1/(2*((Fintype.card A.centers : ℝ)+1))) δ₁
  have hδ : 0 < δ := lt_min (by positivity) hδ₁
  have hδi (i : A.centers) : δ ≤ d i := (min_le_right _ _).trans (hδ₁i i)
  refine ⟨δ,hδ,?_⟩
  intro Q hQ hb
  have hnorm : ∀ p, (1/2 : ℝ) ≤ ‖F p+Q p‖ := by
    apply A.weighted_perturbation_annulus hunit _ hb
    have hδ0 : δ ≤ 1/(2*((Fintype.card A.centers : ℝ)+1)) := min_le_left _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2*((Fintype.card A.centers : ℝ)+1))).mp hδ0
    have hn : 0 ≤ (Fintype.card A.centers : ℝ) := by positivity
    nlinarith
  exact ⟨hnorm,fun i => hdb i Q hQ (fun j => (hb j).mono_const (hδi i)) hnorm⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreparedSphericalImmersion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-point preparation on a closed surface: a spherical immersion
can be flattened at any finite set, with fixed C2 bounds and arbitrary C1 accuracy. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_spherical_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (c : P → A.centers) (G : M → Space),
        (∀ p, A.weight (c p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
        A.WeightedBound 1 1 ε (G-F) ∧ A.WeightedBound 1 2 D G ∧
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
            (chartAt Plane (c p : M) p) v w = 0 := by
  obtain ⟨Dq,hDq,hprep⟩ := A.finite_spherical_preparation_correction hF hunit
  obtain ⟨Cf,hCf,hFb⟩ := A.exists_weighted_bound 2 hF
  let C := max 1 (Cf+Dq)
  have hC : 1 ≤ C := le_max_left _ _
  obtain ⟨D,hD,hDb⟩ := A.radial_normalization_C2_budget C hC
  obtain ⟨εi,hεi,hIi⟩ := A.weighted_immersion_tolerance hF hImm
  refine ⟨D,hD,?_⟩
  intro P ε hε
  obtain ⟨δ,hδ,hstable⟩ := A.radial_normalization_C1_stability hF hunit (lt_min hε hεi)
  obtain ⟨c,Q,hc,hQ,hQ1,hQ2,hjets⟩ := hprep P δ hδ
  obtain ⟨hnorm,hclose⟩ := hstable Q hQ hQ1
  let G := radialNormalize ∘ (F+Q)
  have hG : ContMDiff planeModel spaceModel ∞ G := radial_normalization_smooth (hF.add hQ) hnorm
  have hunitG (p : M) : ‖G p‖ = 1 := by
    have hn : F p+Q p ≠ 0 := by
      intro hz
      have := hnorm p
      norm_num [hz] at this
    change ‖‖F p+Q p‖⁻¹ • (F p+Q p)‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]
  have hHbound : A.WeightedBound 1 2 C (F+Q) := by
    intro i
    have hb := (hFb i).add uniqueDiffOn_univ zero_le_one
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hQ).contDiffOn (hQ2 i)
    have he : (fun x => localize (i : M) (A.weight i) F x+localize (i : M) (A.weight i) Q x) =
        localize (i : M) (A.weight i) (F+Q) := (localize_add _ _ _ _).symm
    rw [he] at hb
    exact hb.mono_const (le_max_right _ _)
  refine ⟨c,G,hc,hG,hunitG,?_,?_,hDb (F+Q) (hF.add hQ) hnorm hHbound,hjets⟩
  · exact hIi G hG (fun i => (hclose i).mono_const (min_le_right _ _))
  · exact fun i => (hclose i).mono_const (min_le_left _ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformPreparedSphericalImmersion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-point spherical preparation with all constants chosen before the
finite set, including domination of a fixed background metric. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_prepared_spherical_immersion_oai (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ D c : ℝ, 0 ≤ D ∧ 0 < c ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (a : P → A.centers) (G : M → Space),
        (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
        A.WeightedBound 1 1 ε (G-F) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
            (chartAt Plane (a p : M) p) v w = 0 := by
  obtain ⟨D,hD,hprep⟩ := A.prepared_spherical_immersion hF hunit hImm
  obtain ⟨δ,c,hδ,hc,hlower⟩ := A.uniform_background_metric_lower_bound g hF hImm
  refine ⟨D,c,hD,hc,?_⟩
  intro P ε hε
  obtain ⟨a,G,ha,hG,hu,hI,hclose,hC,hflat⟩ := hprep P (min ε δ) (lt_min hε hδ)
  exact ⟨a,G,ha,hG,hu,hI,fun i => (hclose i).mono_const (min_le_left _ _),hC,
    hlower G hG (fun i => (hclose i).mono_const (min_le_right _ _)),hflat⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion_oai.{u_1}
