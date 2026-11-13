-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:42:27.565445+00:00
-- url     : https://prove2.me/submissions/7675adb3-b503-4455-92b8-7d5a9f38f1d4

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI009

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `ContinuousLinearMap.IsInvertible.eventually_nhds`: invertible operators form an open set
(SurfaceImmersion primitives, q249). -/
theorem _root_.ContinuousLinearMap.IsInvertible.eventually_nhds {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} (hf : f.IsInvertible) : ∀ᶠ g in nhds f, g.IsInvertible := by
  obtain ⟨e, rfl⟩ := hf
  exact Filter.mem_of_superset (ContinuousLinearEquiv.nhds e) (by rintro _ ⟨e', rfl⟩; exact ⟨e', rfl⟩)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform stability of the finite primitive inverse when its coefficient
functionals, cutoffs and phase covectors all vary independently. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberSpace
local instance dataFiberComplete : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd
local instance dataDualSmul_r8fa271_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberGroup
lemma primitiveDataOperator_smooth :
    ContDiff ℝ ∞ (primitiveDataOperator (ι := ι)) := by
  have hs : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι =>
      finitePrimitiveOperator z.1.1 z.1.2 z.2) := by
    apply ContDiff.sum
    intro i _
    have hp : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι => z.1.2 i) :=
      (contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_fst)
    have hv : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι => z.2 i) :=
      (contDiff_apply ℝ (Plane →L[ℝ] ℝ) i).comp contDiff_snd
    have hq : ContDiff ℝ ∞ (fun z : PrimitiveOperatorData ι =>
        (z.1.1 i).comp tensorSymmetrizer) :=
      ((contDiff_apply ℝ (TensorFiber →L[ℝ] ℝ) i).comp
        (contDiff_fst.comp contDiff_fst)).clm_comp contDiff_const
    exact (hp.pow 2).smul (hq.smulRight (hv.smulRight hv))
  exact (hs.add contDiff_const).sub contDiff_const

lemma isOpen_primitiveDataPositive (i : ι) :
    IsOpen {w : PrimitiveOperatorData ι × TensorFiber |
      (primitiveDataOperator w.1).IsInvertible ∧
      0 < w.1.1.1 i ((primitiveDataOperator w.1).inverse w.2)} := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  have hop : ContinuousAt (fun z : PrimitiveOperatorData ι × TensorFiber =>
      primitiveDataOperator z.1) w :=
    (primitiveDataOperator_smooth.continuous.comp continuous_fst).continuousAt
  have hi := hop.eventually hw.1.eventually_nhds
  have hinv := (hw.1.contDiffAt_map_inverse (n := ∞)).continuousAt.comp (x := w) hop
  have hval := hinv.clm_apply continuous_snd.continuousAt
  have hcoeff : Continuous (fun z : PrimitiveOperatorData ι × TensorFiber => z.1.1.1 i) := by
    fun_prop
  exact hi.and ((hcoeff.continuousAt.clm_apply hval).eventually (lt_mem_nhds hw.2))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 control of the actual inverse and square-root amplitude map.
The parameter bounds are fixed before a later family is composed with it. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberSpace
local instance amplitudeFiberComplete : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeDualAdd
local instance amplitudeDualSmul_r8fa271_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberGroup
lemma primitiveParameterInverse_smoothAt {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible) :
    ContDiffAt ℝ ∞ primitiveParameterInverse z :=
  hz.contDiffAt_map_inverse.comp z
    (primitiveDataOperator_smooth.contDiffAt.comp z contDiffAt_fst)

lemma primitiveParameterCoefficient_smoothAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible) :
    ContDiffAt ℝ ∞ (primitiveParameterCoefficient i) z := by
  have hq : ContDiff ℝ ∞ (fun w : PrimitiveAmplitudeData ι => w.1.1.1 i) := by
    exact (contDiff_apply ℝ (TensorFiber →L[ℝ] ℝ) i).comp
      (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
  exact hq.contDiffAt.clm_apply
    ((primitiveParameterInverse_smoothAt hz).clm_apply contDiffAt_snd)

lemma primitiveParameterAmplitude_smoothAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient i z) :
    ContDiffAt ℝ ∞ (primitiveParameterAmplitude i) z := by
  have hw : ContDiff ℝ ∞ (fun w : PrimitiveAmplitudeData ι => w.1.1.2 i) := by
    exact (contDiff_apply ℝ ℝ i).comp
      (contDiff_snd.comp (contDiff_fst.comp contDiff_fst))
  exact hw.contDiffAt.mul ((Real.contDiffAt_sqrt hp.ne').comp z
    (primitiveParameterCoefficient_smoothAt i hz))

private lemma parameterNormData_continuousAt (i : ι) {z : PrimitiveAmplitudeData ι}
    (hz : (primitiveDataOperator z.1).IsInvertible)
    (hp : 0 < primitiveParameterCoefficient i z) :
    ContinuousAt (parameterNormData i) z := by
  have hi := primitiveParameterInverse_smoothAt hz
  have ha := primitiveParameterAmplitude_smoothAt i hz hp
  exact hi.continuousAt.prodMk
    ((hi.continuousAt_fderiv (by simp)).prodMk
      (ha.continuousAt.prodMk (ha.continuousAt_fderiv (by simp))))

/-- One neighborhood and one C1 constant control inverse operators and actual
amplitudes uniformly around any compact positive family of finite data. -/
theorem compact_primitive_amplitude_C1 (i : ι) {K : Set (PrimitiveAmplitudeData ι)}
    (hK : IsCompact K)
    (hgood : ∀ z ∈ K, (primitiveDataOperator z.1).IsInvertible ∧
      0 < primitiveParameterCoefficient i z) :
    ∃ eps C : ℝ, 0 < eps ∧ 1 ≤ C ∧
      ∀ z ∈ K, ∀ z' : PrimitiveAmplitudeData ι, ‖z'-z‖ < eps →
        (primitiveDataOperator z'.1).IsInvertible ∧
        0 < primitiveParameterCoefficient i z' ∧
        ‖primitiveParameterInverse z'‖ ≤ C ∧
        ‖fderiv ℝ primitiveParameterInverse z'‖ ≤ C ∧
        |primitiveParameterAmplitude i z'| ≤ C ∧
        ‖fderiv ℝ (primitiveParameterAmplitude i) z'‖ ≤ C := by
  have hc : ContinuousOn (parameterNormData i) K := fun z hz =>
    (parameterNormData_continuousAt i (hgood z hz).1 (hgood z hz).2).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (f := parameterNormData i) hc
  let C : ℝ := max 1 (B+1)
  let O : Set (PrimitiveAmplitudeData ι) := {z |
    (primitiveDataOperator z.1).IsInvertible ∧
    0 < primitiveParameterCoefficient i z ∧ ‖parameterNormData i z‖ < C}
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hg : ∀ᶠ w in 𝓝 z,
        (primitiveDataOperator w.1).IsInvertible ∧
          0 < primitiveParameterCoefficient i w :=
      (isOpen_primitiveDataPositive i).eventually_mem ⟨hz.1,hz.2.1⟩
    have hnorm : ContinuousAt (fun w => ‖parameterNormData i w‖) z :=
      ContinuousAt.norm (f := parameterNormData i)
        (parameterNormData_continuousAt i hz.1 hz.2.1)
    have hn : ∀ᶠ w in 𝓝 z, ‖parameterNormData i w‖ < C :=
      hnorm.eventually (gt_mem_nhds hz.2.2)
    exact (hg.and hn).mono (fun _ h => ⟨h.1.1,h.1.2,h.2⟩)
  have hKO : K ⊆ O := by
    intro z hz
    refine ⟨(hgood z hz).1,(hgood z hz).2,?_⟩
    exact (hB z hz).trans_lt ((lt_add_one B).trans_le (le_max_right _ _))
  obtain ⟨eps,heps,hnear⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨eps,C,heps,le_max_left _ _,?_⟩
  intro z hz z' hdist
  have hmem : z' ∈ O := hnear (Metric.mem_thickening_iff.mpr
    ⟨z,hz,by simpa only [dist_eq_norm] using hdist⟩)
  have hb : ‖parameterNormData i z'‖ ≤ C := hmem.2.2.le
  have hinv := (norm_fst_le (parameterNormData i z')).trans hb
  have hder := (norm_fst_le (parameterNormData i z').2).trans
    ((norm_snd_le (parameterNormData i z')).trans hb)
  have ha := (norm_fst_le (parameterNormData i z').2.2).trans
    ((norm_snd_le (parameterNormData i z').2).trans
      ((norm_snd_le (parameterNormData i z')).trans hb))
  have had := (norm_snd_le (parameterNormData i z').2.2).trans
    ((norm_snd_le (parameterNormData i z').2).trans
      ((norm_snd_le (parameterNormData i z')).trans hb))
  change ‖primitiveParameterAmplitude i z'‖ ≤ C at ha
  exact ⟨hmem.1,hmem.2.1,hinv,hder,by simpa only [Real.norm_eq_abs] using ha,had⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundedPrimitiveAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform inverse and amplitude bounds from the fixed reference size and
positive coefficient margin. Inactive chart coefficients need not vary continuously. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeGroup
local instance boundedAmplitudeComplete_r8fa271_1 : CompleteSpace TensorFiber := inferInstance
local instance boundedFiberFinite : FiniteDimensional ℝ TensorFiber := inferInstance
local instance boundedDualFinite : FiniteDimensional ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFinite : FiniteDimensional ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance boundedDualFamilyFinite : FiniteDimensional ℝ (ι → TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFamilyFinite : FiniteDimensional ℝ (ι → Plane →L[ℝ] ℝ) := inferInstance
local instance boundedOperatorDataFinite : FiniteDimensional ℝ (PrimitiveOperatorData ι) := inferInstance
local instance boundedDataFinite : FiniteDimensional ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance boundedDataProper : ProperSpace (PrimitiveAmplitudeData ι) :=
  FiniteDimensional.proper ℝ (PrimitiveAmplitudeData ι)

local instance boundedDataNormed_r8fa271_1 : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedDataSpace
lemma boundedPrimitiveReference_compact (i : ι) (D k : ℝ) :
    IsCompact (boundedPrimitiveReference i D k) := by
  have hq : Continuous (fun z : PrimitiveAmplitudeData ι => z.1.1.1 i z.2) := by
    have h : Continuous (fun z : PrimitiveAmplitudeData ι => z.1.1.1 i) := by fun_prop
    exact h.clm_apply continuous_snd
  have hclosed : IsClosed (boundedPrimitiveReference i D k) :=
    (isClosed_le continuous_norm continuous_const).inter
      ((isClosed_eq (primitiveDataOperator_smooth.continuous.comp continuous_fst) continuous_const).inter
        (isClosed_le continuous_const hq))
  exact (isCompact_closedBall (0 : PrimitiveAmplitudeData ι) D).of_isClosed_subset
    hclosed (fun z hz => by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1)

lemma boundedPrimitiveReference_good (i : ι) (D : ℝ) {k : ℝ} (hk : 0 < k)
    {z : PrimitiveAmplitudeData ι} (hz : z ∈ boundedPrimitiveReference i D k) :
    (primitiveDataOperator z.1).IsInvertible ∧ 0 < primitiveParameterCoefficient i z := by
  change (primitiveDataOperator z.1).IsInvertible ∧
    0 < z.1.1.1 i ((primitiveDataOperator z.1).inverse z.2)
  rw [hz.2.1,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_apply]
  exact ⟨⟨ContinuousLinearEquiv.refl ℝ TensorFiber,rfl⟩,hk.trans_le hz.2.2⟩

theorem bounded_primitive_amplitude_C1_oai (i : ι) (D : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ eps C : ℝ, 0 < eps ∧ 1 ≤ C ∧
      ∀ z : PrimitiveAmplitudeData ι, ‖z‖ ≤ D →
      primitiveDataOperator z.1 = ContinuousLinearMap.id ℝ TensorFiber →
      k ≤ z.1.1.1 i z.2 → ∀ z' : PrimitiveAmplitudeData ι, ‖z'-z‖ < eps →
        (primitiveDataOperator z'.1).IsInvertible ∧
        0 < primitiveParameterCoefficient i z' ∧
        ‖primitiveParameterInverse z'‖ ≤ C ∧
        ‖fderiv ℝ primitiveParameterInverse z'‖ ≤ C ∧
        |primitiveParameterAmplitude i z'| ≤ C ∧
        ‖fderiv ℝ (primitiveParameterAmplitude i) z'‖ ≤ C := by
  obtain ⟨eps,C,heps,hC,hbound⟩ := compact_primitive_amplitude_C1 i
    (boundedPrimitiveReference_compact i D k)
    (fun _ hz => boundedPrimitiveReference_good i D hk hz)
  exact ⟨eps,C,heps,hC,fun z hn hi hp z' hd => hbound z ⟨hn,hi,hp⟩ z' hd⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1_oai.{u_1}
