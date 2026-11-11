-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:20.216822+00:00
-- url     : https://prove2.me/submissions/2f089929-b95f-4b16-9be6-99bbdc9d4e49

import Mathlib
import Definitions.Def_OAIQ240Bp019

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_TimeSteps
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.parameterSegmentPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric

namespace PackingSufficiencySupport.Hamiltonian

theorem segmentPath_smooth (a : ℝ) : ContDiff ℝ ∞ (segmentPath a) :=
  contDiff_const.add (segmentLinear.contDiff.comp (contDiff_id.sub contDiff_const))

theorem segment_integral_eq (f : ℝ × ℝ → ℝ) (hf : Continuous f) (a : ℝ) (p : ℝ × ℝ) :
    (∫ x in a..p.1, f (x,p.2)) =
      (p.1-a) * pathAverage ((⟨f,hf⟩ : C(ℝ × ℝ,ℝ)).comp (segmentPath a p)) := by
  let u := (⟨f,hf⟩ : C(ℝ × ℝ,ℝ)).comp (segmentPath a p)
  have he : (∫ s in (0:ℝ)..1, extendPath u s) = ∫ s in (0:ℝ)..1, f (a+s*(p.1-a),p.2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    change extendPath u s = f (a+s*(p.1-a),p.2)
    rw [show extendPath u s = u ⟨s,hs⟩ from extendPath_coe u ⟨s,hs⟩]
    change f (segmentPath a p ⟨s,hs⟩) = _
    rw [segmentPath_apply]
  change _ = (p.1-a) * (∫ s in (0:ℝ)..1, extendPath u s)
  rw [he]
  have hi := intervalIntegral.smul_integral_comp_add_mul (fun x => f (x,p.2))
    (a := (0:ℝ)) (b := 1) (p.1-a) a
  simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, add_sub_cancel, mul_comm] using hi.symm

theorem contDiff_segment_integral {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ x in a..p.1, f (x,p.2)) := by
  have he : (fun p : ℝ × ℝ => ∫ x in a..p.1, f (x,p.2)) =
      fun p => (p.1-a) * pathAverage ((⟨f,hf.continuous⟩ : C(ℝ × ℝ,ℝ)).comp (segmentPath a p)) := by
    funext p
    exact segment_integral_eq f hf.continuous a p
  rw [he]
  exact (contDiff_fst.sub contDiff_const).mul
    (pathAverage.contDiff.comp ((postcomp_contDiff hf).comp (segmentPath_smooth a)))

theorem planarMarginal_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (A : ℝ) :
    ContDiff ℝ ∞ (planarMarginal A f) :=
  (contDiff_segment_integral hf (-A)).comp (contDiff_const.prodMk contDiff_id)

theorem planarPrimitive_curl {A : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hg : Continuous (planarMarginal A f)) (p : ℝ × ℝ) :
    deriv (fun x => planarPrimitiveY A f ρ (x,p.2)) p.1 -
      deriv (fun t => planarPrimitiveX A f ρ (p.1,t)) p.2 = f p := by
  have hc : Continuous (fun x => f (x,p.2) - ρ x * planarMarginal A f p.2) :=
    (hf.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const)
  have hY := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (-A) p.1)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hG := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (-A) p.2)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hX := hG.const_mul (-ρ p.1)
  change deriv (fun x => ∫ v in -A..x, f (v,p.2) - ρ v * planarMarginal A f p.2) p.1 -
    deriv (fun t => -ρ p.1 * ∫ v in -A..t, planarMarginal A f v) p.2 = _
  rw [hY.deriv, hX.deriv]
  ring

theorem interval_primitive_zero_outside {A : ℝ} (hA : 0 ≤ A) {g : ℝ → ℝ}
    (hg : Continuous g) (hgs : ∀ x, A ≤ |x| → g x = 0)
    (hg0 : (∫ x in -A..A, g x) = 0) {t : ℝ} (ht : A ≤ |t|) :
    (∫ x in -A..t, g x) = 0 := by
  rcases le_abs.mp ht with ht | ht
  · have hi := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hg.intervalIntegrable (-A) A) (hg.intervalIntegrable A t)
    have hz : (∫ x in A..t, g x) = 0 := by
      have he : (∫ x in A..t, g x) = ∫ x in A..t, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ht] at hx
        exact hgs x (hx.1.trans (le_abs_self x))
      simpa using he
    rw [hg0,hz,zero_add] at hi
    exact hi.symm
  · have hta : t ≤ -A := by linarith
    have hz : (∫ x in -A..t, g x) = ∫ x in -A..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_ge hta] at hx
      apply hgs x
      rw [abs_of_nonpos (hx.2.trans (neg_nonpos.mpr hA))]
      linarith [hx.2]
    simpa using hz

open MeasureTheory Function

theorem integral_eq_full_of_box_support {A : ℝ} {g : ℝ → ℝ}
    (hgs : ∀ x, A ≤ |x| → g x = 0) : (∫ x in -A..A, g x) = ∫ x, g x := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hx' : |x| < A := by
    by_contra! ha
    exact hx (hgs x ha)
  exact ⟨(abs_lt.mp hx').1,(abs_lt.mp hx').2.le⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.coordinateForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open MeasureTheory Function
open scoped Classical

theorem bilinear_skew_plane (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (u v : Plane) :
    B u v - B v u = (B (1,0) (0,1)-B (0,1) (1,0))*planarArea u v := by
  have hu : u = u.1 • ((1:ℝ),(0:ℝ)) + u.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hu,hv]
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,planarArea_apply]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem parameterSegmentPath_smooth (a : ℝ) : ContDiff ℝ ∞ (parameterSegmentPath (P := P) a) :=
  contDiff_const.add ((parameterSegmentLinear (P := P)).contDiff.comp (contDiff_id.sub contDiff_const))

theorem parameter_segment_integral_eq (f : P × ℝ → ℝ) (hf : Continuous f)
    (a : ℝ) (p : P × ℝ) :
    (∫ x in a..p.2, f (p.1,x)) =
      (p.2-a) * pathAverage ((⟨f,hf⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)) := by
  let u := (⟨f,hf⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)
  have he : (∫ s in (0:ℝ)..1, extendPath u s) =
      ∫ s in (0:ℝ)..1, f (p.1,a+s*(p.2-a)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    rw [show extendPath u s = u ⟨s,hs⟩ from extendPath_coe u ⟨s,hs⟩]
    change f (parameterSegmentPath a p ⟨s,hs⟩) = _
    rw [parameterSegmentPath_apply]
  change _ = (p.2-a) * (∫ s in (0:ℝ)..1, extendPath u s)
  rw [he]
  have hi := intervalIntegral.smul_integral_comp_add_mul (fun x => f (p.1,x))
    (a := (0:ℝ)) (b := 1) (p.2-a) a
  simpa only [smul_eq_mul,mul_zero,mul_one,add_zero,add_sub_cancel,mul_comm] using hi.symm

variable [FiniteDimensional ℝ P]

theorem contDiff_parameter_segment_integral {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => ∫ x in a..p.2, f (p.1,x)) := by
  have he : (fun p : P × ℝ => ∫ x in a..p.2, f (p.1,x)) =
      fun p => (p.2-a)*pathAverage
        ((⟨f,hf.continuous⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)) := by
    funext p
    exact parameter_segment_integral_eq f hf.continuous a p
  rw [he]
  exact (contDiff_snd.sub contDiff_const).mul
    (pathAverage.contDiff.comp ((postcomp_contDiff (K := Time) (E := P × ℝ) (F := ℝ) hf).comp (parameterSegmentPath_smooth (P := P) a)))

theorem planarPrimitive_parameter_smooth {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (A : ℝ) :
    ContDiff ℝ ∞ (fun p : P × Plane => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2) ∧
    ContDiff ℝ ∞ (fun p : P × Plane => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2) := by
  have hff : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => f (p.1.1,(p.2,p.1.2))) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
  have hg : ContDiff ℝ ∞ (fun p : P × ℝ => planarMarginal A (fun x => f (p.1,x)) p.2) :=
    (contDiff_parameter_segment_integral hff (-A)).comp (contDiff_id.prodMk contDiff_const)
  have hG : ContDiff ℝ ∞ (fun p : P × Plane =>
      ∫ t in -A..p.2.2, planarMarginal A (fun x => f (p.1,x)) t) :=
    (contDiff_parameter_segment_integral hg (-A)).comp
      (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  refine ⟨((hρ.comp (contDiff_fst.comp contDiff_snd)).neg.mul hG),?_⟩
  have hF : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ =>
      f (p.1.1,(p.2,p.1.2)) - ρ p.2*planarMarginal A (fun x => f (p.1.1,x)) p.1.2) :=
    hff.sub ((hρ.comp contDiff_snd).mul (hg.comp contDiff_fst))
  exact (contDiff_parameter_segment_integral hF (-A)).comp
    ((contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).prodMk (contDiff_fst.comp contDiff_snd))

omit [FiniteDimensional ℝ P] in
theorem planarPrimitive_zero_outside {A : ℝ} (hA : 0 ≤ A) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hfs : ∀ x t, A ≤ |x| ∨ A ≤ |t| → f (x,t) = 0)
    (hρs : ∀ x, A ≤ |x| → ρ x = 0)
    (hρ1 : (∫ x in -A..A, ρ x) = 1)
    (hg : Continuous (planarMarginal A f))
    (hf0 : (∫ t in -A..A, planarMarginal A f t) = 0) :
    ∀ p, A ≤ |p.1| ∨ A ≤ |p.2| →
      planarPrimitiveX A f ρ p = 0 ∧ planarPrimitiveY A f ρ p = 0 := by
  have hgt (t : ℝ) (ht : A ≤ |t|) : planarMarginal A f t = 0 := by
    unfold planarMarginal
    have he : (fun x => f (x,t)) = fun _ => (0:ℝ) := by
      funext x
      exact hfs x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hF (t : ℝ) : (∫ x in -A..A, f (x,t) - ρ x * planarMarginal A f t) = 0 := by
    have hc : Continuous (fun x => f (x,t)) := hf.comp (continuous_id.prodMk continuous_const)
    have hd : Continuous (fun x => ρ x * planarMarginal A f t) := hρ.mul continuous_const
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable (-A) A)
      (hd.intervalIntegrable (-A) A)]
    rw [intervalIntegral.integral_mul_const, hρ1, one_mul]
    exact sub_self _
  have hzero (p : ℝ × ℝ) (hp : A ≤ |p.1| ∨ A ≤ |p.2|) :
      planarPrimitiveX A f ρ p = 0 ∧ planarPrimitiveY A f ρ p = 0 := by
    rcases hp with hp | hp
    · constructor
      · simp [planarPrimitiveX, hρs _ hp]
      · apply interval_primitive_zero_outside hA
          ((hf.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const))
          (fun x hx => by
            change f (x,p.2) - ρ x * planarMarginal A f p.2 = 0
            rw [hfs x p.2 (Or.inl hx),hρs x hx]; ring) (hF p.2) hp
    · constructor
      · unfold planarPrimitiveX
        rw [interval_primitive_zero_outside hA hg hgt hf0 hp, mul_zero]
      · unfold planarPrimitiveY
        have he : (fun x => f (x,p.2) - ρ x * planarMarginal A f p.2) = fun _ => (0:ℝ) := by
          funext x
          rw [hfs x p.2 (Or.inr hp), hgt p.2 hp]
          ring
        rw [he,intervalIntegral.integral_zero]
  exact hzero


end

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_clm_eval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → E →L[ℝ] F} {x : E} (hg : DifferentiableAt ℝ g x) (u v : E) :
    fderiv ℝ (fun y => g y v) x u = fderiv ℝ g x u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simp



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open MeasureTheory Set

theorem planarCovector_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U V : P → ℝ} (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun p => planarCovector (U p) (V p)) := by
  exact (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem planar_deriv_first {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p) :
    deriv (fun x => f (x,p.2)) p.1 = fderiv ℝ f p (1,0) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv

theorem planar_deriv_second {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p) :
    deriv (fun y => f (p.1,y)) p.2 = fderiv ℝ f p (0,1) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.deriv

theorem planarCovector_exterior {U V : Plane → ℝ}
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (p : Plane) :
    euclideanExteriorOneForm (fun x => planarCovector (U x) (V x)) p =
      (deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2) • planarArea := by
  let α : Plane → Plane →L[ℝ] ℝ := fun x => planarCovector (U x) (V x)
  have ha : DifferentiableAt ℝ α p := (planarCovector_smooth hU hV).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV' : fderiv ℝ α p (1,0) (0,1) = fderiv ℝ V p (1,0) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,zero_add]
  have hU' : fderiv ℝ α p (0,1) (1,0) = fderiv ℝ U p (0,1) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,add_zero]
  rw [planar_deriv_first (hV.contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    planar_deriv_second (hU.contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ α p u v - fderiv ℝ α p v u = _
  rw [bilinear_skew_plane,hV',hU']
  rfl


end

section
open scoped ContDiff Topology
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_bilinear_flip {P A B C : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : P → A →L[ℝ] B →L[ℝ] C} {p : P} (h : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q => (f q).flip) p := by
  have hflip : ContDiff ℝ ∞ (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := A →L[ℝ] B →L[ℝ] C)
      (F := B →L[ℝ] A →L[ℝ] C) (ContinuousLinearMap.flipₗᵢ ℝ A B C)
  exact hflip.contDiffAt.comp p h


end

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem staticPullbackOneForm_fderiv {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) (u v : F) :
    fderiv ℝ (staticPullbackOneForm α g) x u v =
      fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
        α (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hd := ((ha.differentiableAt (by simp)).hasFDerivAt.comp x
    (hg.differentiableAt (by simp)).hasFDerivAt).clm_comp
      ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (staticPullbackOneForm α g) x = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem staticPullbackOneForm_exterior {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (staticPullbackOneForm α g) x =
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearComp_apply,staticPullbackOneForm_fderiv ha hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq u v]
  ring


end

section
open scoped ContDiff
open MeasureTheory Set Function

theorem translated_covector_exterior {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (a z : Plane) :
    euclideanExteriorOneForm (fun x => α (x-a)) z =
      euclideanExteriorOneForm α (z-a) := by
  have hD (x : Plane) : fderiv ℝ (fun y : Plane => y-a) x = ContinuousLinearMap.id ℝ Plane :=
    ((hasFDerivAt_id x).sub_const a).fderiv
  have he : staticPullbackOneForm α (fun x => x-a) = fun x => α (x-a) := by
    funext x
    unfold staticPullbackOneForm
    rw [hD]
    rfl
  have hsm : ContDiffAt ℝ ∞ (fun x : Plane => x-a) z := contDiffAt_id.sub contDiffAt_const
  have hd := staticPullbackOneForm_exterior (α := α) hα.contDiffAt hsm
  rw [he,hD] at hd
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ => B u v) hd


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartTwoForm_apply_chart {Ω : ManifoldTwoForm E M} {c z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) c).source) (v w : TangentSpace 𝓘(ℝ,E) z) :
    chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z w) = Ω z v w := by
  change E at v w
  change chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
    (chartDifferential c z v) (chartDifferential c z w) = Ω z v w
  simp only [chartTwoForm,(extChartAt 𝓘(ℝ,E) c).left_inv hz,
    ContinuousLinearMap.bilinearComp_apply]
  have hA : (chartDifferential (E := E) c z).IsInvertible := by
    convert! (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hz) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hA.inverse_apply_eq.mpr rfl,hA.inverse_apply_eq.mpr rfl]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

theorem planar_det (A : Plane →L[ℝ] Plane) :
    A.det = planarArea (A (1,0)) (A (0,1)) := by
  let b : Module.Basis (Fin 2) ℝ Plane :=
    Module.Basis.ofEquivFun (LinearEquiv.finTwoArrow ℝ ℝ).symm
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix b,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,b,Module.Basis.coe_ofEquivFun,
    LinearEquiv.finTwoArrow,planarArea_apply]
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartDifferential_inverse {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y := by
  apply ContinuousLinearMap.inverse_eq
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hy)
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hy)


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclideanPullbackTwoForm_chart {Ω : ℝ → ManifoldTwoForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackTwoForm Ω g p =
      (chartTwoForm (Ω p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  ext v w
  exact (chartTwoForm_apply_chart hc _ _).symm


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartSupportedOneForm_chart {c b : M} {α : E → E →L[ℝ] ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartOneForm (chartSupportedOneForm c α) b y =
      (α (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)
  let A : E →L[ℝ] E :=
    (chartDifferential c ((extChartAt 𝓘(ℝ,E) b).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  simp only [chartOneForm,chartSupportedOneForm,ite_eq_left hc,chartDifferential_inverse hy,he]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem chartSupportedOneForm_zero {c : M} {α : E → E →L[ℝ] ℝ} {K : Set E}
    (hα : ∀ y ∉ K, α y=0) {x : M}
    (hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K) : chartSupportedOneForm c α x=0 := by
  classical
  unfold chartSupportedOneForm
  split_ifs with hc
  · have hn : extChartAt 𝓘(ℝ,E) c x ∉ K := by
      intro hk
      exact hx ⟨extChartAt 𝓘(ℝ,E) c x,hk,(extChartAt 𝓘(ℝ,E) c).left_inv hc⟩
    rw [hα _ hn]
    exact ContinuousLinearMap.zero_comp _
  · rfl

theorem chartSupportedOneForm_smooth [T2Space M] {c : M}
    {α : P × E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α)
    {K : Set E} (hKc : IsCompact K) (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hzero : ∀ p y, y ∉ K → α (p,y)=0) (b : M) :
    ContDiffOn ℝ ∞ (fun q : P × E =>
      chartOneForm (chartSupportedOneForm c (fun y => α (q.1,y))) b q.2)
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) b).target) := by
  intro p hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
  let x := (extChartAt 𝓘(ℝ,E) b).symm p.2
  by_cases hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source
  · have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc)
    have ht : ContDiffAt ℝ ∞
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) p.2 :=
      (ho.comp p.2 hi).contDiffAt
    have hv := hα.contDiffAt.comp p (contDiffAt_fst.prodMk (ht.comp p contDiffAt_snd))
    have hd := (ht.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
    apply ((hv.clm_comp hd).congr_of_eventuallyEq _).contDiffWithinAt
    have hb := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
    have hcn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    filter_upwards [hb,hcn] with q hqb hqc
    exact chartSupportedOneForm_chart hqb hqc
  · have hcomp : IsCompact ((extChartAt 𝓘(ℝ,E) c).symm '' K) :=
      hKc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK)
    have hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K := by
      rintro ⟨y,hy,he⟩
      exact hc (he ▸ (extChartAt 𝓘(ℝ,E) c).map_target (hK hy))
    have hn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (hcomp.isClosed.isOpen_compl.mem_nhds hx)
    apply ((contDiffAt_const (c := (0 : E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (chartSupportedOneForm c (fun y => α (q.1,y))
      ((extChartAt 𝓘(ℝ,E) b).symm q.2)).comp _ = 0
    change (extChartAt 𝓘(ℝ,E) b).symm q.2 ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K at hq
    rw [chartSupportedOneForm_zero (hzero q.1) hq]
    exact ContinuousLinearMap.zero_comp _



theorem chartSupportedTwoForm_chart {c b : M} {α : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartTwoForm (chartSupportedTwoForm c α) b y =
      (α (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)
  let A : E →L[ℝ] E :=
    (chartDifferential c ((extChartAt 𝓘(ℝ,E) b).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  simp only [chartTwoForm,chartSupportedTwoForm,ite_eq_left hc,chartDifferential_inverse hy,he]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem chartSupportedTwoForm_zero {c : M} {α : E → E →L[ℝ] E →L[ℝ] ℝ} {K : Set E}
    (hα : ∀ y ∉ K, α y=0) {x : M}
    (hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K) : chartSupportedTwoForm c α x=0 := by
  classical
  unfold chartSupportedTwoForm
  split_ifs with hc
  · have hn : extChartAt 𝓘(ℝ,E) c x ∉ K := by
      intro hk
      exact hx ⟨extChartAt 𝓘(ℝ,E) c x,hk,(extChartAt 𝓘(ℝ,E) c).left_inv hc⟩
    rw [hα _ hn]
    ext u v; rfl
  · rfl

theorem chartSupportedTwoForm_smooth [T2Space M] {c : M}
    {α : P × E → E →L[ℝ] E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α)
    {K : Set E} (hKc : IsCompact K) (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hzero : ∀ p y, y ∉ K → α (p,y)=0) (b : M) :
    ContDiffOn ℝ ∞ (fun q : P × E =>
      chartTwoForm (chartSupportedTwoForm c (fun y => α (q.1,y))) b q.2)
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) b).target) := by
  intro p hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
  let x := (extChartAt 𝓘(ℝ,E) b).symm p.2
  by_cases hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source
  · have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc)
    have ht : ContDiffAt ℝ ∞
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) p.2 :=
      (ho.comp p.2 hi).contDiffAt
    have hv := hα.contDiffAt.comp p (contDiffAt_fst.prodMk (ht.comp p contDiffAt_snd))
    have hd := (ht.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
    have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hv.clm_comp hd)).clm_comp hd)
    apply (hsm.congr_of_eventuallyEq _).contDiffWithinAt
    have hb := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
    have hcn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    filter_upwards [hb,hcn] with q hqb hqc
    exact chartSupportedTwoForm_chart hqb hqc
  · have hcomp : IsCompact ((extChartAt 𝓘(ℝ,E) c).symm '' K) :=
      hKc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK)
    have hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K := by
      rintro ⟨y,hy,he⟩
      exact hc (he ▸ (extChartAt 𝓘(ℝ,E) c).map_target (hK hy))
    have hn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (hcomp.isClosed.isOpen_compl.mem_nhds hx)
    apply ((contDiffAt_const (c := (0 : E →L[ℝ] E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (chartSupportedTwoForm c (fun y => α (q.1,y))
      ((extChartAt 𝓘(ℝ,E) b).symm q.2)).bilinearComp _ _ = 0
    change (extChartAt 𝓘(ℝ,E) b).symm q.2 ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K at hq
    rw [chartSupportedTwoForm_zero (hzero q.1) hq]
    ext u v; rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclideanExteriorOneForm_zero_outside {α : E → E →L[ℝ] ℝ} {K : Set E}
    (hK : IsClosed K) (hzero : ∀ x ∉ K, α x=0) {x : E} (hx : x ∉ K) :
    euclideanExteriorOneForm α x=0 := by
  have he : α =ᶠ[𝓝 x] fun _ => (0 : E →L[ℝ] ℝ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hzero y hy
  unfold euclideanExteriorOneForm
  rw [he.fderiv_eq]
  ext u v
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

theorem chartSupportedOneForm_exterior {c b : M} {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) {K : Set E} (hKc : IsCompact K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hzero : ∀ y ∉ K, α y=0) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target) :
    euclideanExteriorOneForm (chartOneForm (chartSupportedOneForm c α) b) y =
      chartTwoForm (chartSupportedTwoForm c (euclideanExteriorOneForm α)) b y := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)
  let x := (extChartAt 𝓘(ℝ,E) b).symm y
  by_cases hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source
  · have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc)
    have ht : ContDiffAt ℝ ∞
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y :=
      (ho.comp y hi).contDiffAt
    have he : chartOneForm (chartSupportedOneForm c α) b =ᶠ[𝓝 y]
        staticPullbackOneForm α (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) := by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy,
        hi.continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)] with z hzb hzc
      exact chartSupportedOneForm_chart hzb hzc
    rw [chartSupportedTwoForm_chart hy hc]
    calc
      _ = euclideanExteriorOneForm
          (staticPullbackOneForm α (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm)) y := by
        unfold euclideanExteriorOneForm
        rw [he.fderiv_eq]
      _ = _ := staticPullbackOneForm_exterior hα.contDiffAt ht
  · have hcomp : IsCompact ((extChartAt 𝓘(ℝ,E) c).symm '' K) :=
      hKc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK)
    have hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K := by
      rintro ⟨z,hz,he⟩
      exact hc (he ▸ (extChartAt 𝓘(ℝ,E) c).map_target (hK hz))
    have he : chartOneForm (chartSupportedOneForm c α) b =ᶠ[𝓝 y]
        fun _ => (0 : E →L[ℝ] ℝ) := by
      filter_upwards [hi.continuousAt.preimage_mem_nhds
        (hcomp.isClosed.isOpen_compl.mem_nhds hx)] with z hz
      change (chartSupportedOneForm c α ((extChartAt 𝓘(ℝ,E) b).symm z)).comp _ = 0
      change (extChartAt 𝓘(ℝ,E) b).symm z ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K at hz
      rw [chartSupportedOneForm_zero hzero hz]
      exact ContinuousLinearMap.zero_comp _
    have hd : ∀ z ∉ K, euclideanExteriorOneForm α z=0 :=
      fun z hz => euclideanExteriorOneForm_zero_outside hKc.isClosed hzero hz
    have hz := chartSupportedTwoForm_zero hd hx
    calc
      euclideanExteriorOneForm (chartOneForm (chartSupportedOneForm c α) b) y =
          (0 : E →L[ℝ] E →L[ℝ] ℝ) := by
        unfold euclideanExteriorOneForm
        rw [he.fderiv_eq]
        ext u v
        simp
      _ = _ := by
        change 0 = (chartSupportedTwoForm c _ x).bilinearComp _ _
        rw [hz]
        ext u v
        rfl


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_FixedSpatialIntegral
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open MeasureTheory Set Function
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem planar_fixed_support_integral_smooth {A : ℝ} {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → f (p,(x,y))=0) :
    ContDiff ℝ ∞ (fun p => ∫ z, f (p,z)) := by
  have hff : ContDiff ℝ ∞ (fun q : (P × ℝ) × ℝ => f (q.1.1,(q.2,q.1.2))) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => planarMarginal A (fun z => f (q.1,z)) q.2) :=
    (contDiff_parameter_segment_integral hff (-A)).comp (contDiff_id.prodMk contDiff_const)
  have hh : ContDiff ℝ ∞ (fun p => ∫ y in -A..A, planarMarginal A (fun z => f (p,z)) y) :=
    (contDiff_parameter_segment_integral hg (-A)).comp (contDiff_id.prodMk contDiff_const)
  have he : (fun p => ∫ y in -A..A, planarMarginal A (fun z => f (p,z)) y) =
      (fun p => ∫ z, f (p,z)) := by
    funext p
    have hfp : Continuous (fun z => f (p,z)) :=
      hf.continuous.comp (continuous_const.prodMk continuous_id)
    have hfc : HasCompactSupport (fun z => f (p,z)) := by
      apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (max A 0))
      intro z hz
      have hh : max A 0 < max |z.1| |z.2| := by
        simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hz
      exact hzero p z.1 z.2 ((lt_max_iff.mp ((le_max_left A 0).trans_lt hh)).imp le_of_lt le_of_lt)
    have hgm (y : ℝ) : planarMarginal A (fun z => f (p,z)) y = ∫ x, f (p,(x,y)) :=
      integral_eq_full_of_box_support (fun x hx => hzero p x y (Or.inl hx))
    have hgy (y : ℝ) (hy : A ≤ |y|) : planarMarginal A (fun z => f (p,z)) y=0 := by
      unfold planarMarginal
      have he : (fun x => f (p,(x,y))) = fun _ => (0:ℝ) := funext fun x => hzero p x y (Or.inr hy)
      rw [he,intervalIntegral.integral_zero]
    rw [integral_eq_full_of_box_support hgy]
    simp_rw [hgm]
    change (∫ y, ∫ x, f (p,(x,y))) = ∫ z : ℝ × ℝ, f (p,z)
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact (integral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (fun z => f (p,z)) (hfp.integrable_of_hasCompactSupport hfc)).symm
  rw [he] at hh
  exact hh

theorem exists_planar_unit_bump {A : ℝ} (hA : 0<A) :
    ∃ ρ : Plane → ℝ, ContDiff ℝ ∞ ρ ∧
      (∀ z, 0 ≤ ρ z) ∧ HasCompactSupport ρ ∧
      (∀ x y, A ≤ |x| ∨ A ≤ |y| → ρ (x,y)=0) ∧ (∫ z, ρ z)=1 := by
  let b : ContDiffBump (0:ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let r := b.normed volume
  have hrs : ContDiff ℝ ∞ r := b.contDiff_normed
  have hr0 (x : ℝ) (hx : A ≤ |x|) : r x=0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hh : |x|<A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hh
  let ρ : Plane → ℝ := fun z => r z.1*r z.2
  have hs : ContDiff ℝ ∞ ρ := (hrs.comp contDiff_fst).mul (hrs.comp contDiff_snd)
  have hz (x y : ℝ) (hxy : A ≤ |x| ∨ A ≤ |y|) : ρ (x,y)=0 := by
    rcases hxy with hx|hy
    · exact mul_eq_zero_of_left (hr0 x hx) _
    · exact mul_eq_zero_of_right _ (hr0 y hy)
  have hc : HasCompactSupport ρ := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) A)
    intro z hn
    have hh : A < max |z.1| |z.2| := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hn
    exact hz z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  refine ⟨ρ,hs,fun z => mul_nonneg (b.nonneg_normed (μ := volume) _) (b.nonneg_normed (μ := volume) _),hc,hz,?_⟩
  have hi := integral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) ρ (hs.continuous.integrable_of_hasCompactSupport hc)
  change (∫ z : ℝ × ℝ, ρ z)=1
  rw [Measure.volume_eq_prod ℝ ℝ,hi]
  change (∫ x, ∫ y, r x*r y)=1
  simp_rw [integral_const_mul]
  rw [show (∫ y, r y)=1 from b.integral_normed]
  simp only [mul_one]
  exact b.integral_normed


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SurfaceCoordinateBox

theorem isCompact_compactCarrier (B : SurfaceCoordinateBox M) : IsCompact B.compactCarrier := by
  exact (isCompact_closedBall B.point B.radius).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) B.center).mono B.closed_subset)

theorem carrier_subset_compactCarrier (B : SurfaceCoordinateBox M) :
    B.carrier ⊆ B.compactCarrier := by
  intro x hx
  exact ⟨extChartAt 𝓘(ℝ,Plane) B.center x,Metric.ball_subset_closedBall hx.2,
    (extChartAt 𝓘(ℝ,Plane) B.center).left_inv hx.1⟩

theorem nonempty_carrier (B : SurfaceCoordinateBox M) : B.carrier.Nonempty := by
  have hp : B.point ∈ (extChartAt 𝓘(ℝ,Plane) B.center).target :=
    B.closed_subset (Metric.mem_closedBall_self B.radius_pos.le)
  refine ⟨(extChartAt 𝓘(ℝ,Plane) B.center).symm B.point,
    (extChartAt 𝓘(ℝ,Plane) B.center).map_target hp,?_⟩
  change extChartAt 𝓘(ℝ,Plane) B.center ((extChartAt 𝓘(ℝ,Plane) B.center).symm B.point) ∈ Metric.ball B.point B.radius
  rw [(extChartAt 𝓘(ℝ,Plane) B.center).right_inv hp]
  exact Metric.mem_ball_self B.radius_pos

theorem exists_compactCarrier_subset {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U) :
    ∃ B : SurfaceCoordinateBox M, x ∈ B.carrier ∧ B.compactCarrier ⊆ U := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) x
  have hy := (extChartAt 𝓘(ℝ,Plane) x).map_source hx
  have hS : IsOpen ((extChartAt 𝓘(ℝ,Plane) x).target ∩
      (extChartAt 𝓘(ℝ,Plane) x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hU
  have hxy : extChartAt 𝓘(ℝ,Plane) x x ∈
      (extChartAt 𝓘(ℝ,Plane) x).target ∩ (extChartAt 𝓘(ℝ,Plane) x).symm ⁻¹' U := by
    refine ⟨hy,?_⟩
    simpa only [mem_preimage,(extChartAt 𝓘(ℝ,Plane) x).left_inv hx] using hxU
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hS _ hxy
  have hs := (Metric.closedBall_subset_ball (x := extChartAt 𝓘(ℝ,Plane) x x)
    (show r/2 < r by linarith)).trans hrsub
  let B : SurfaceCoordinateBox M :=
    ⟨x,extChartAt 𝓘(ℝ,Plane) x x,r/2,by positivity,hs.trans inter_subset_left⟩
  refine ⟨B,⟨hx,Metric.mem_ball_self (by dsimp [B] <;> positivity)⟩,?_⟩
  rintro z ⟨y,hy,rfl⟩
  exact (hs hy).2

end SurfaceCoordinateBox

end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem planar_skew_coefficient (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = -B v u) (u v : Plane) :
    B u v = B (1,0) (0,1)*planarArea u v := by
  have he := bilinear_skew_plane B u v
  rw [hB v u,hB (0,1) (1,0)] at he
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartTwoForm_change {Ω : ManifoldTwoForm Plane M} {c b : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) b).target)
    (hc : (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source) :
    chartTwoForm Ω b y =
      (chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackTwoForm_chart (Ω := fun _ => Ω) (p := (0,y)) hi hc
  simpa only [euclideanPullbackTwoForm,chartTwoForm,chartDifferential_inverse hy] using he

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartTwoForm_skew {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) (c : M) (y u v : Plane) :
    chartTwoForm Ω c y u v = -chartTwoForm Ω c y v u := by
  exact hΩ _ _ _

theorem chartTwoForm_density_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {y : Plane}
    (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) b).target)
    (hc : (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source) :
    chartTwoForm Ω b y (1,0) (0,1) =
      (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det *
        chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y)) (1,0) (0,1) := by
  rw [chartTwoForm_change hy hc,ContinuousLinearMap.bilinearComp_apply,
    planar_skew_coefficient _ (chartTwoForm_skew hΩ _ _), ← planar_det,mul_comm]

theorem chart_area_integral_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {K : Set M}
    (hK : IsCompact K)
    (hKb : K ⊆ (extChartAt 𝓘(ℝ,Plane) b).source)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hpos : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K,
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det) :
    (∫ y in extChartAt 𝓘(ℝ,Plane) b '' K, chartTwoForm Ω b y (1,0) (0,1)) =
      ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K, chartTwoForm Ω c y (1,0) (0,1) := by
  let g : Plane → Plane := extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm
  have hyb {y : Plane} (hy : y ∈ extChartAt 𝓘(ℝ,Plane) b '' K) :
      y ∈ (extChartAt 𝓘(ℝ,Plane) b).target := by
    obtain ⟨x,hx,rfl⟩ := hy
    exact (extChartAt 𝓘(ℝ,Plane) b).map_source (hKb hx)
  have hyK {y : Plane} (hy : y ∈ extChartAt 𝓘(ℝ,Plane) b '' K) :
      (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ K := by
    obtain ⟨x,hx,rfl⟩ := hy
    simpa only [(extChartAt 𝓘(ℝ,Plane) b).left_inv (hKb hx)] using hx
  have hgs : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K, ContDiffAt ℝ ∞ g y := by
    intro y hy
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) b).mem_nhds (hyb hy))
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hKc (hyK hy))
    exact (ho.comp y hi).contDiffAt
  have hgi : InjOn g (extChartAt 𝓘(ℝ,Plane) b '' K) := by
    intro y hy z hz he
    apply (extChartAt 𝓘(ℝ,Plane) b).symm.injOn (hyb hy) (hyb hz)
    exact (extChartAt 𝓘(ℝ,Plane) c).injOn (hKc (hyK hy)) (hKc (hyK hz)) he
  have him : g '' (extChartAt 𝓘(ℝ,Plane) b '' K) = extChartAt 𝓘(ℝ,Plane) c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(extChartAt 𝓘(ℝ,Plane) b).symm z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨extChartAt 𝓘(ℝ,Plane) b x,⟨x,hx,rfl⟩,?_⟩
      exact congrArg (extChartAt 𝓘(ℝ,Plane) c) ((extChartAt 𝓘(ℝ,Plane) b).left_inv (hKb hx))
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) b).mono hKb)).measurableSet
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs y hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => chartTwoForm Ω c y (1,0) (0,1))
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) b).mono hKb)).measurableSet
  intro y hy
  dsimp only
  change chartTwoForm Ω b y (1,0) (0,1) =
    |(fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det| •
      chartTwoForm Ω c (extChartAt 𝓘(ℝ,Plane) c ((extChartAt 𝓘(ℝ,Plane) b).symm y)) (1,0) (0,1)
  rw [chartTwoForm_density_change hΩ (hyb hy) (hKc (hyK hy)),abs_of_pos (hpos y hy)]
  rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

theorem chartSupported_extendedCoefficient {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    {K : Set M} (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) :
    chartSupportedTwoForm c (fun y => extendedChartCoefficient c Ω (p,y) • planarArea) = Ω p := by
  funext x
  by_cases hx : x ∈ (extChartAt 𝓘(ℝ,Plane) c).source
  · have hy := (extChartAt 𝓘(ℝ,Plane) c).map_source hx
    unfold chartSupportedTwoForm extendedChartCoefficient spatialZeroExtension
    simp only [ite_eq_left hx,ite_eq_left hy]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,
      smul_eq_mul]
    rw [← planar_skew_coefficient _ (chartTwoForm_skew (hskew p) c _) ]
    exact chartTwoForm_apply_chart hx u v
  · unfold chartSupportedTwoForm
    rw [ite_eq_right hx,hz p x (fun hk => hx (hKc hk))]


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem chartMass_eq_setIntegral {c : M} {Ω : ManifoldTwoForm Plane M} {K : Set M}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0) :
    chartMass c Ω = ∫ y in extChartAt 𝓘(ℝ,Plane) c '' K, chartTwoForm Ω c y (1,0) (0,1) := by
  unfold chartMass
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => extendedChartCoefficient_zero (fun _ x hx => hz x hx) (0:ℝ) hy)]
  apply setIntegral_congr_fun
    (hK.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)).measurableSet
  rintro y ⟨x,hx,rfl⟩
  exact ite_eq_left ((extChartAt 𝓘(ℝ,Plane) c).map_source (hKc hx))

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartMass_change {Ω : ManifoldTwoForm Plane M}
    (hΩ : ∀ x u v, Ω x u v = -Ω x v u) {c b : M} {K : Set M}
    (hK : IsCompact K) (hKb : K ⊆ (extChartAt 𝓘(ℝ,Plane) b).source)
    (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ x, x ∉ K → Ω x=0)
    (hpos : ∀ y ∈ extChartAt 𝓘(ℝ,Plane) b '' K,
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det) :
    chartMass b Ω = chartMass c Ω := by
  rw [chartMass_eq_setIntegral hK hKb hz,chartMass_eq_setIntegral hK hKc hz]
  exact chart_area_integral_change hΩ hK hKb hKc hpos

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in

theorem chartMass_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : ContDiffOn ℝ ∞ (fun q : P × Plane => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) : ContDiff ℝ ∞ (fun p => chartMass c (Ω p)) := by
  have hcK := hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc)
  obtain ⟨R,hR⟩ := hcK.isBounded.subset_closedBall (0:Plane)
  have hf := extendedChartCoefficient_smooth hΩ hK hKc hz
  change ContDiff ℝ ∞ (fun p => ∫ y, extendedChartCoefficient c Ω (p,y))
  apply planar_fixed_support_integral_smooth (A := max R 0+1) hf
  intro p x y hxy
  apply extendedChartCoefficient_zero hz p
  intro hxyK
  have hn : max |x| |y| ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using hR hxyK
  rcases hxy with hx|hy
  · have := (le_max_left |x| |y|).trans hn
    linarith [le_max_left R 0]
  · have := (le_max_right |x| |y|).trans hn
    linarith [le_max_left R 0]


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem euclideanExteriorOneForm_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    euclideanExteriorOneForm (α+β) x =
      euclideanExteriorOneForm α x + euclideanExteriorOneForm β x := by
  rw [euclideanExteriorOneForm,fderiv_add hα hβ]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,add_apply]
  ring

theorem euclideanExteriorOneForm_smul (a : ℝ) {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) :
    euclideanExteriorOneForm (a • α) x = a • euclideanExteriorOneForm α x := by
  rw [euclideanExteriorOneForm,fderiv_const_smul hα]
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,smul_apply,
    smul_eq_mul]
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartSupportedTwoForm_own_chart {c : M} {α : Plane → Plane →L[ℝ] Plane →L[ℝ] ℝ}
    {y : Plane} (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target) :
    chartTwoForm (chartSupportedTwoForm c α) c y = α y := by
  have he : (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) c).mem_nhds hy] with z hz
    exact (extChartAt 𝓘(ℝ,Plane) c).right_inv hz
  rw [chartSupportedTwoForm_chart hy ((extChartAt 𝓘(ℝ,Plane) c).map_target hy),
    he.fderiv_eq,(extChartAt 𝓘(ℝ,Plane) c).right_inv hy,fderiv_id]
  rfl

theorem extendedCoefficient_chartSupported {c : M} {f : Plane → ℝ}
    (hz : ∀ y, y ∉ (extChartAt 𝓘(ℝ,Plane) c).target → f y=0) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => chartSupportedTwoForm c (fun z => f z • planarArea)) (0,y) = f y := by
  classical
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target
  · change (if y ∈ _ then chartTwoForm (chartSupportedTwoForm c (fun z => f z • planarArea)) c y (1,0) (0,1) else 0)=f y
    rw [ite_eq_left hy,chartSupportedTwoForm_own_chart hy]
    simp only [smul_apply,smul_eq_mul,planarArea]
    norm_num
  · change (if y ∈ _ then _ else 0)=f y
    rw [ite_eq_right hy,hz y hy]

theorem chartMass_chartSupported {c : M} {f : Plane → ℝ}
    (hz : ∀ y, y ∉ (extChartAt 𝓘(ℝ,Plane) c).target → f y=0) :
    chartMass c (chartSupportedTwoForm c (fun z => f z • planarArea)) = ∫ y, f y := by
  unfold chartMass
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (extendedCoefficient_chartSupported hz)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartMass_sub {c : M} {Ω Λ : ManifoldTwoForm Plane M}
    (hΩ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)))
    (hΛ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y))) :
    chartMass c (Ω-Λ) = chartMass c Ω - chartMass c Λ := by
  have he (y : Plane) : extendedChartCoefficient c (fun _ : ℝ => Ω-Λ) (0,y) =
      extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)-extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y) := by
    unfold extendedChartCoefficient spatialZeroExtension
    split_ifs
    · rfl
    · exact (sub_self 0).symm
  unfold chartMass
  simp_rw [he]
  exact integral_sub hΩ hΛ


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.spatial_smooth {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (p : P) (c : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (chartOneForm (α p) c) y :=
  ((hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds ⟨mem_univ p,hy⟩)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)

theorem SmoothTwoFormFamily.neg {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) : SmoothTwoFormFamily (-Ω) := by
  have he : -Ω = fun p => (-1:ℝ) • Ω p := by ext p x u v; simp
  rw [he]
  exact hΩ.smul contDiff_const

theorem SmoothTwoFormFamily.sub {Ω Λ : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (hΛ : SmoothTwoFormFamily Λ) : SmoothTwoFormFamily (Ω-Λ) := by
  have he : Ω-Λ = Ω+(-Λ) := sub_eq_add_neg Ω Λ
  rw [he]
  exact hΩ.add hΛ.neg


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

namespace SurfaceCoordinateBox

theorem exists_unit_bump [T2Space M] (B : SurfaceCoordinateBox M) : Nonempty (BoxUnitBump B) := by
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := Plane →L[ℝ] Plane →L[ℝ] ℝ)
  obtain ⟨ρ,hρ,hρpos,hρc,hρzero,hρmass⟩ := exists_planar_unit_bump (show 0<B.radius/2 by linarith [B.radius_pos])
  let f : Plane → ℝ := fun z => ρ (z-B.point)
  have hf : ContDiff ℝ ∞ f := hρ.comp (contDiff_id.sub contDiff_const)
  let C := Metric.closedBall B.point (B.radius/2)
  have hC : C ⊆ (extChartAt 𝓘(ℝ,Plane) B.center).target :=
    (Metric.closedBall_subset_closedBall (show B.radius/2≤B.radius by linarith [B.radius_pos])).trans B.closed_subset
  have hfzero (z : Plane) (hz : z ∉ C) : f z=0 := by
    have hh : B.radius/2 < max |z.1-B.point.1| |z.2-B.point.2| := by
      simpa only [C,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
        Real.norm_eq_abs,not_le] using hz
    exact hρzero _ _ ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  let Ω := chartSupportedTwoForm B.center (fun z => f z • planarArea)
  let K := (extChartAt 𝓘(ℝ,Plane) B.center).symm '' C
  have hK : IsCompact K := (isCompact_closedBall B.point (B.radius/2)).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) B.center).mono hC)
  have hKB : K ⊆ B.carrier := by
    rintro x ⟨z,hz,rfl⟩
    refine ⟨(extChartAt 𝓘(ℝ,Plane) B.center).map_target (hC hz),?_⟩
    change extChartAt 𝓘(ℝ,Plane) B.center ((extChartAt 𝓘(ℝ,Plane) B.center).symm z) ∈ Metric.ball B.point B.radius
    rw [(extChartAt 𝓘(ℝ,Plane) B.center).right_inv (hC hz)]
    exact Metric.closedBall_subset_ball (by linarith [B.radius_pos]) hz
  have hΩzero (x : M) (hx : x ∉ K) : Ω x=0 :=
    chartSupportedTwoForm_zero (fun z hz => by rw [hfzero z hz,zero_smul]) hx
  have hΩsmooth : SmoothTwoForm Ω := by
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × Plane => f q.2 • planarArea) :=
      (hf.comp contDiff_snd).smul contDiff_const
    intro b
    have hs := chartSupportedTwoForm_smooth (P := ℝ) (E := Plane) (M := M) (c := B.center)
      (α := fun q : ℝ × Plane => f q.2 • planarArea) hsm
      (K := C) (isCompact_closedBall B.point (B.radius/2)) hC
      (fun _ z hz => by rw [hfzero z hz,zero_smul]) b
    exact hs.comp (f := fun y : Plane => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _,hy⟩)
  have hΩskew (x : M) (u v : Plane) : Ω x u v = -Ω x v u := by
    unfold Ω chartSupportedTwoForm
    split_ifs <;> simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,smul_eq_mul,zero_apply,neg_zero]
    simp only [planarArea_apply]
    ring
  have hmass : chartMass B.center Ω=1 := by
    rw [chartMass_chartSupported (fun z hz => hfzero z (fun hc => hz (hC hc)))]
    change (∫ z, ρ (z-B.point))=1
    rw [MeasureTheory.integral_sub_right_eq_self]
    exact hρmass
  exact ⟨⟨Ω,hΩsmooth,hΩskew,K,hK,hKB,hΩzero,hmass⟩⟩

end SurfaceCoordinateBox

theorem BoxUnitBump.mass_in_chart (hpos : PositivePlaneTransitions M)
    {B : SurfaceCoordinateBox M} (β : BoxUnitBump B) (c : M)
    (hc : β.supportSet ⊆ (extChartAt 𝓘(ℝ,Plane) c).source) : chartMass c β.form=1 := by
  rw [← β.unit_mass]
  apply chartMass_change β.skew β.compact_supportSet hc
    (fun x hx => (β.support_subset hx).1) β.zero_off
  rintro y ⟨x,hx,rfl⟩
  apply hpos c B.center _ ((extChartAt 𝓘(ℝ,Plane) c).map_source (hc hx))
  simpa only [(extChartAt 𝓘(ℝ,Plane) c).left_inv (hc hx)] using (β.support_subset hx).1



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricOrientation
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set
namespace PackingSufficiencySupport.Hamiltonian

theorem connected_cover_overlap_chain {X I : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {U : I → Set X} (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {i j : I}
    (hi : (U i).Nonempty) (hj : (U j).Nonempty) :
    Relation.ReflTransGen (fun a b => (U a ∩ U b).Nonempty) i j := by
  let R : I → Prop := fun b =>
    Relation.ReflTransGen (fun a b => (U a ∩ U b).Nonempty) i b
  let S : Set X := ⋃ b, ⋃ (_ : R b), U b
  have hS : IsOpen S := isOpen_iUnion fun b => isOpen_iUnion fun _ => hU b
  have hd : Sᶜ = ⋃ b, ⋃ (_ : ¬R b), U b := by
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := hcover x
      have hr : ¬R b := by
        intro hr
        exact hx (mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hr,hb⟩⟩)
      exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hr,hb⟩⟩
    · intro hx hy
      obtain ⟨b,hb,hxb⟩ := mem_iUnion₂.mp hx
      obtain ⟨c,hc,hxc⟩ := mem_iUnion₂.mp hy
      exact hb (hc.tail ⟨x,hxc,hxb⟩)
  have hSc : IsOpen Sᶜ := by rw [hd]; exact isOpen_iUnion fun b => isOpen_iUnion fun _ => hU b
  have hne : S.Nonempty := by
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,mem_iUnion₂.mpr ⟨i,Relation.ReflTransGen.refl,hx⟩⟩
  have hall : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hSc,hS⟩).eq_univ hne
  obtain ⟨x,hx⟩ := hj
  have hxS : x ∈ S := by rw [hall]; exact mem_univ _
  obtain ⟨b,hb,hxb⟩ := mem_iUnion₂.mp hxS
  exact hb.tail ⟨x,hxb,hx⟩

end PackingSufficiencySupport.Hamiltonian

end

noncomputable section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



namespace PackingSufficiencySupport.Hamiltonian
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

omit [Fintype I] in
theorem partitionTwoForm_smooth (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω) (i : I) :
    SmoothTwoFormFamily (partitionTwoForm ρ Ω i) :=
  hΩ.spatial_smul (ρ i).contMDiff

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] [Fintype I] in
theorem partitionTwoForm_skew (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : ∀ p x u v, Ω p x u v = -Ω p x v u)
    (i : I) (p : P) (x : M) (u v : Plane) :
    partitionTwoForm ρ Ω i p x u v = -partitionTwoForm ρ Ω i p x v u := by
  change ρ i x * Ω p x u v = -(ρ i x * Ω p x v u)
  rw [hΩ p x u v,mul_neg]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partitionTwoForm_sum (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : P → ManifoldTwoForm Plane M} (hz : ∀ p x, x ∉ K → Ω p x=0) :
    ∑ i, partitionTwoForm ρ Ω i = Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  funext p x
  simp only [Finset.sum_apply,partitionTwoForm]
  rw [← Finset.sum_smul]
  by_cases hx : x ∈ K
  · have hs : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    rw [hs,one_smul]
  · rw [hz p x hx,MulActionWithZero.smul_zero]

end PackingSufficiencySupport.Hamiltonian



end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

namespace IsPrimitiveFamily

theorem zero : IsPrimitiveFamily (0 : P → ManifoldTwoForm E M) 0 := by
  constructor
  · intro c
    simpa only [Pi.zero_apply,chartOneForm_zero] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P × E => (0 : E →L[ℝ] ℝ)) _)
  · intro p c y _
    change euclideanExteriorOneForm (chartOneForm 0 c) y = chartTwoForm 0 c y
    rw [show chartOneForm (0 : ManifoldOneForm E M) c = fun _ => 0 from funext fun z => chartOneForm_zero c z]
    simp only [chartTwoForm_zero,euclideanExteriorOneForm,fderiv_const_apply,ContinuousLinearMap.flip_zero]
    exact sub_self (0 : E →L[ℝ] E →L[ℝ] ℝ)

theorem add {Ω Λ : P → ManifoldTwoForm E M} {α β : P → ManifoldOneForm E M}
    (hα : IsPrimitiveFamily Ω α) (hβ : IsPrimitiveFamily Λ β) :
    IsPrimitiveFamily (Ω+Λ) (α+β) := by
  constructor
  · intro c
    simpa only [Pi.add_apply,chartOneForm_add] using (hα.smooth c).add (hβ.smooth c)
  · intro p c y hy
    simp only [Pi.add_apply,chartTwoForm_add]
    rw [show chartOneForm (α p + β p) c =
      chartOneForm (α p) c + chartOneForm (β p) c from funext fun z => chartOneForm_add _ _ c z]
    rw [euclideanExteriorOneForm_add ((hα.smooth.spatial_smooth p c hy).differentiableAt (by simp))
      ((hβ.smooth.spatial_smooth p c hy).differentiableAt (by simp)),hα.exterior p c y hy,hβ.exterior p c y hy]

theorem smul {Ω : P → ManifoldTwoForm E M} {α : P → ManifoldOneForm E M}
    (hα : IsPrimitiveFamily Ω α) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsPrimitiveFamily (fun p => f p • Ω p) (fun p => f p • α p) := by
  constructor
  · intro c
    simpa only [chartOneForm_smul,Function.comp_apply,Pi.smul_def'] using
      (hf.comp contDiff_fst).contDiffOn.smul (hα.smooth c)
  · intro p c y hy
    simp only [chartTwoForm_smul]
    rw [show chartOneForm (f p • α p) c = f p • chartOneForm (α p) c from
      funext fun z => chartOneForm_smul _ _ c z]
    rw [euclideanExteriorOneForm_smul _ ((hα.smooth.spatial_smooth p c hy).differentiableAt (by simp)),
      hα.exterior p c y hy]

theorem sum {I : Type*} (s : Finset I) {Ω : I → P → ManifoldTwoForm E M}
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, IsPrimitiveFamily (Ω i) (α i)) :
    IsPrimitiveFamily (∑ i ∈ s, Ω i) (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero (P := P) (E := E) (M := M)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hα j (Finset.mem_insert_of_mem hj)))

theorem const_slice {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {Ω : Q → ManifoldTwoForm E M} {α : Q → ManifoldOneForm E M}
    (hα : IsPrimitiveFamily Ω α) (q : Q) :
    IsPrimitiveFamily (fun _ : P => Ω q) (fun _ : P => α q) := by
  constructor
  · intro c
    apply (hα.smooth c).comp (f := fun t : P × E => (q,t.2))
      (contDiffOn_const.prodMk contDiffOn_snd)
    exact fun t ht => ⟨mem_univ _,ht.2⟩
  · intro _ c y hy
    exact hα.exterior q c y hy

end IsPrimitiveFamily

end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem extendedChartCoefficient_zero_form (c : M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => (0 : ManifoldTwoForm Plane M)) (0,y)=0 := by
  unfold extendedChartCoefficient spatialZeroExtension
  split_ifs <;> simp only [chartTwoForm_zero,zero_apply]

theorem extendedChartCoefficient_sum {I : Type*} (s : Finset I) (c : M)
    (Ω : I → ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => ∑ i ∈ s, Ω i) (0,y) =
      ∑ i ∈ s, extendedChartCoefficient c (fun _ : ℝ => Ω i) (0,y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,extendedChartCoefficient_zero_form]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,extendedChartCoefficient_add,ih]

theorem chartMass_sum {I : Type*} (s : Finset I) (c : M)
    (Ω : I → ManifoldTwoForm Plane M)
    (hΩ : ∀ i ∈ s, Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω i) (0,y))) :
    chartMass c (∑ i ∈ s, Ω i) = ∑ i ∈ s, chartMass c (Ω i) := by
  unfold chartMass
  simp_rw [extendedChartCoefficient_sum]
  exact integral_finsetSum s hΩ

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceIntegralIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory Classical
open scoped ContDiff Manifold Topology ENNReal

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I J : Type*} [Fintype I] [Fintype J] {K : Set M}

omit [T2Space M] in

theorem partitionFormMass_independent (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (C : J → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (ν : SmoothPartitionOfUnity J 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hν : ν.IsSubordinate (fun j => (C j).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (hskew : ∀ x u v, Ω x u v = -Ω x v u) (hz : ∀ x, x ∉ K → Ω x=0) :
    partitionFormMass B ρ Ω = partitionFormMass C ν Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → J → ManifoldTwoForm Plane M := fun i j x => ρ i x • (ν j x • Ω x)
  let L : I → J → Set M := fun i j => K ∩ tsupport (ρ i) ∩ tsupport (ν j)
  have hL (i : I) (j : J) : IsCompact (L i j) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).inter_right (isClosed_tsupport (ν j))
  have hLB (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.1.2).1
  have hLC (i : I) (j : J) : L i j ⊆ (extChartAt 𝓘(ℝ,Plane) (C j).center).source :=
    fun _ hx => (hν j hx.2).1
  have hDz (i : I) (j : J) (x : M) (hx : x ∉ L i j) : D i j x=0 := by
    by_cases hk : x ∈ K
    · by_cases hi : x ∈ tsupport (ρ i)
      · have hj : x ∉ tsupport (ν j) := fun hj => hx ⟨⟨hk,hi⟩,hj⟩
        simp only [D,image_eq_zero_of_notMem_tsupport hj,zero_smul,smul_zero]
      · simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hDs (i : I) (j : J) : SmoothTwoForm (D i j) :=
    (((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ν j).contMDiff).spatial_smul
      (ρ i).contMDiff).eval 0
  have hDa (i : I) (j : J) (x : M) (u v : Plane) : D i j x u v = -D i j x v u := by
    change ρ i x * (ν j x * Ω x u v) = -(ρ i x * (ν j x * Ω x v u))
    rw [hskew x u v]; ring
  have hsumJ (i : I) : (∑ j, D i j) = fun x => ρ i x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ j, ν j x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ν.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hsumI (j : J) : (∑ i, D i j) = fun x => ν j x • Ω x := by
    funext x
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [Finset.sum_apply,D,sum_apply,smul_apply,smul_eq_mul]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ K
    · have hh : (∑ i, ρ i x)=1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hh,one_mul]
    · simp only [hz x hx,zero_apply,mul_zero]
  have hchange (i : I) (j : J) : chartMass (B i).center (D i j)=chartMass (C j).center (D i j) := by
    apply chartMass_change (hDa i j) (hL i j) (hLB i j) (hLC i j) (hDz i j)
    rintro y ⟨x,hx,rfl⟩
    apply hpos (B i).center (C j).center _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hLB i j hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hLB i j hx)] using hLC i j hx
  unfold partitionFormMass
  calc
    (∑ i, chartMass (B i).center (fun x => ρ i x • Ω x)) =
        ∑ i, ∑ j, chartMass (B i).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsumJ i]
      exact chartMass_sum Finset.univ (B i).center (D i)
        (fun j _ => (hDs i j).coefficient_integrable _ (hL i j) (hLB i j) (hDz i j))
    _ = ∑ i, ∑ j, chartMass (C j).center (D i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hchange i j)
    _ = ∑ j, ∑ i, chartMass (C j).center (D i j) := Finset.sum_comm
    _ = ∑ j, chartMass (C j).center (fun x => ν j x • Ω x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hsumI j]
      exact (chartMass_sum Finset.univ (C j).center (fun i => D i j)
        (fun i _ => (hDs i j).coefficient_integrable _ (hL i j) (hLC i j) (hDz i j))).symm

end

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

theorem chartInverseExtension_measurable (c : M) : Measurable (chartInverseExtension c) := by
  classical
  exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) c).measurable_piecewise
    continuousOn_const (isOpen_extChartAt_target c).measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartInverseExtension_eq {c : M} {y : Plane}
    (hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target) :
    chartInverseExtension c y=(extChartAt 𝓘(ℝ,Plane) c).symm y := ite_eq_left hy

omit [BorelSpace M] in
theorem chartAreaMeasure_finite (c : M) {w : Plane → ℝ} (hw : Integrable w) :
    IsFiniteMeasure (chartAreaMeasure c w) := by
  have hl : (∫⁻ y, ENNReal.ofReal (w y)) < (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt (lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (le_abs_self (w y))))
    simpa only [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm w).mp hw.hasFiniteIntegral
  let := isFiniteMeasure_withDensity hl.ne
  exact inferInstanceAs (IsFiniteMeasure (Measure.map _ _))

theorem integral_chartAreaMeasure (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {f : M → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂chartAreaMeasure c w)=
      ∫ y, w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y) := by
  rw [chartAreaMeasure,integral_map (chartInverseExtension_measurable c).aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul (hw.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos y)]
  change w y*f (chartInverseExtension c y)=_
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · rw [chartInverseExtension_eq hy]
  · rw [hz y hy,zero_mul,zero_mul]

theorem integrable_chartAreaMeasure (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {f : M → ℝ} (hf : Measurable f) :
    Integrable f (chartAreaMeasure c w) ↔
      Integrable (fun y => w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y)) := by
  rw [chartAreaMeasure,integrable_map_measure hf.aestronglyMeasurable
    (chartInverseExtension_measurable c).aemeasurable,
    integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (hpos y)]
  change w y*f (chartInverseExtension c y)=_
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · rw [chartInverseExtension_eq hy]
  · rw [hz y hy,zero_mul,zero_mul]

theorem chartAreaMeasure_null (c : M) {w : Plane → ℝ}
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {C : Set M} (hC : MeasurableSet C)
    (hnull : volume ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C)=0) :
    chartAreaMeasure c w C=0 := by
  rw [chartAreaMeasure,Measure.map_apply (chartInverseExtension_measurable c) hC,
    withDensity_apply _ ((chartInverseExtension_measurable c) hC)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem ((chartInverseExtension_measurable c) hC),
    (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull))] with y hy hn
  have hyt : y∉(extChartAt 𝓘(ℝ,Plane) c).target := by
    intro ht
    apply hn
    refine ⟨ht,?_⟩
    simpa only [mem_preimage,chartInverseExtension_eq ht] using hy
  rw [hz y hyt,ENNReal.ofReal_zero]
  rfl

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K : Set M}

theorem partitionChartDensity_off_target (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (i : I) {y : Plane}
    (hy : y∉(extChartAt 𝓘(ℝ,Plane) (B i).center).target) :
    partitionChartDensity B ρ Λ i y=0 := ite_eq_right hy

theorem partitionChartDensity_nonneg (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Λ : ManifoldTwoForm Plane M}
    (hΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1)) (i : I) (y : Plane) :
    0≤partitionChartDensity B ρ Λ i y := by
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) (B i).center).target
  · unfold partitionChartDensity extendedChartCoefficient spatialZeroExtension
    rw [ite_eq_left hy]
    change 0 ≤ chartTwoForm (fun x => ρ i x • Λ x) (B i).center y (1,0) (0,1)
    rw [chartTwoForm_spatial_smul]
    exact mul_nonneg (ρ.nonneg i _) (hΛ _ _ hy)
  · rw [partitionChartDensity_off_target B ρ Λ i hy]

theorem partitionChartDensity_spatial_smul (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Λ : ManifoldTwoForm Plane M) (f : M → ℝ) (i : I) (y : Plane) :
    partitionChartDensity B ρ (fun x => f x • Λ x) i y=
      partitionChartDensity B ρ Λ i y * f ((extChartAt 𝓘(ℝ,Plane) (B i).center).symm y) := by
  unfold partitionChartDensity extendedChartCoefficient spatialZeroExtension
  split_ifs
  · change chartTwoForm (fun x => ρ i x • (f x • Λ x)) (B i).center y (1,0) (0,1) =
      chartTwoForm (fun x => ρ i x • Λ x) (B i).center y (1,0) (0,1) * _
    rw [chartTwoForm_spatial_smul,chartTwoForm_spatial_smul,chartTwoForm_spatial_smul]
    simp only [smul_apply, smul_eq_mul]
    ring
  · exact (zero_mul _).symm

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem partitionChartDensity_properties (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) (i : I) :
    ContDiff ℝ ∞ (partitionChartDensity B ρ Λ i) ∧
      HasCompactSupport (partitionChartDensity B ρ Λ i) ∧
      Integrable (partitionChartDensity B ρ Λ i) := by
  let L := tsupport (ρ i)
  have hL : IsCompact L := (B i).isCompact_compactCarrier.of_isClosed_subset
    (isClosed_tsupport _) ((hρ i).trans (B i).carrier_subset_compactCarrier)
  have hLc : L⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source := fun _ hx => (hρ i hx).1
  have hs : SmoothTwoFormFamily (fun _ : ℝ => fun x => ρ i x • Λ x) :=
    (SmoothTwoFormFamily.const hΛ).spatial_smul (ρ i).contMDiff
  have hz : ∀ (p : ℝ) x,x∉L→ρ i x • Λ x=0 := by
    intro _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change (0:ℝ) * _ = 0
    exact zero_mul _
  have hfull : ContDiff ℝ ∞ (extendedChartCoefficient (B i).center
      (fun _ : ℝ => fun x => ρ i x • Λ x)) :=
    extendedChartCoefficient_smooth (Ω := fun _ : ℝ => fun x => ρ i x • Λ x)
      (c := (B i).center) (hs (B i).center) hL hLc hz
  have hsm : ContDiff ℝ ∞ (partitionChartDensity B ρ Λ i) :=
    hfull.comp (f := fun y : Plane => ((0 : ℝ),y))
      (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (partitionChartDensity B ρ Λ i) := by
    apply HasCompactSupport.intro (hL.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) (B i).center).mono hLc))
    exact fun _ hy => extendedChartCoefficient_zero hz 0 hy
  exact ⟨hsm,hc,hsm.continuous.integrable_of_hasCompactSupport hc⟩

variable [Fintype I] [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
theorem partitionAreaMeasure_finite (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) :
    IsFiniteMeasure (partitionAreaMeasure B ρ Λ) := by
  have (i : I) : IsFiniteMeasure (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) :=
    chartAreaMeasure_finite _ (partitionChartDensity_properties B ρ hρ hΛ i).2.2
  exact inferInstanceAs (IsFiniteMeasure (∑ i, chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)))

theorem integral_partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    (∫ x, f x ∂partitionAreaMeasure B ρ Λ)=
      partitionFormMass B ρ (fun x => f x • Λ x) := by
  have hfp : SmoothTwoForm (fun x => f x • Λ x) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hf).eval 0
  have hmeas (i : I) : Measurable (partitionChartDensity B ρ Λ i) :=
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
  have hint (i : I) : Integrable f
      (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) := by
    rw [integrable_chartAreaMeasure _ (hmeas i) (partitionChartDensity_nonneg B ρ hpos i)
      (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
    simpa only [← partitionChartDensity_spatial_smul] using
      (partitionChartDensity_properties B ρ hρ hfp i).2.2
  rw [partitionAreaMeasure,integral_finsetSum_measure (fun i _ => hint i)]
  unfold partitionFormMass chartMass
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_chartAreaMeasure _ (hmeas i) (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (partitionChartDensity_spatial_smul B ρ Λ f i y).symm)

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [MeasurableSpace M] [BorelSpace M]

theorem integral_chartAreaMeasure_restrict (c : M) {w : Plane → ℝ}
    (hw : Measurable w) (hpos : ∀ y,0≤w y)
    (hz : ∀ y,y∉(extChartAt 𝓘(ℝ,Plane) c).target→w y=0)
    {C : Set M} (hC : MeasurableSet C) {f : M → ℝ} (hf : Measurable f) :
    (∫ x in C, f x ∂chartAreaMeasure c w)=
      ∫ y in (extChartAt 𝓘(ℝ,Plane) c).target ∩
        (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C,
        w y*f ((extChartAt 𝓘(ℝ,Plane) c).symm y) := by
  rw [← integral_indicator hC, integral_chartAreaMeasure c hw hpos hz (hf.indicator hC)]
  have hD : MeasurableSet ((extChartAt 𝓘(ℝ,Plane) c).target ∩
      (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C) :=
    by
      have he : (extChartAt 𝓘(ℝ,Plane) c).target ∩
          (extChartAt 𝓘(ℝ,Plane) c).symm ⁻¹' C =
          (extChartAt 𝓘(ℝ,Plane) c).target ∩ chartInverseExtension c ⁻¹' C := by
        ext y
        by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
        · simp only [mem_inter_iff,mem_preimage,hy,true_and,chartInverseExtension_eq hy]
        · simp only [mem_inter_iff,hy,false_and]
      rw [he]
      exact (isOpen_extChartAt_target c).measurableSet.inter
        (chartInverseExtension_measurable c hC)
  rw [← integral_indicator hD]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈(extChartAt 𝓘(ℝ,Plane) c).target
  · by_cases hc : (extChartAt 𝓘(ℝ,Plane) c).symm y∈C
    · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,hc,and_self,↓reduceIte]
    · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,hc,and_false,↓reduceIte,mul_zero]
  · simp only [Set.indicator,mem_inter_iff,mem_preimage,hy,false_and,↓reduceIte,hz y hy,zero_mul]

variable {I : Type*} [Fintype I] {K : Set M}

variable [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem smooth_integrable_partitionAreaMeasure (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    Integrable f (partitionAreaMeasure B ρ Λ) := by
  have hfp : SmoothTwoForm (fun x => f x • Λ x) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΛ).spatial_smul hf).eval 0
  apply integrable_finsetSum_measure.mpr
  intro i _
  rw [integrable_chartAreaMeasure _
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
    (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hf.continuous.measurable]
  simpa only [← partitionChartDensity_spatial_smul] using
    (partitionChartDensity_properties B ρ hρ hfp i).2.2

theorem integral_partitionAreaMeasure_restrict (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {C : Set M} (hC : MeasurableSet C)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f) :
    (∫ x in C, f x ∂partitionAreaMeasure B ρ Λ)=
      restrictedPartitionFormMass B ρ C (fun x => f x • Λ x) := by
  have hh := (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos hf).indicator hC
  have hint : ∀ i ∈ (Finset.univ : Finset I), Integrable (C.indicator f)
      (chartAreaMeasure (B i).center (partitionChartDensity B ρ Λ i)) :=
    integrable_finsetSum_measure.mp hh
  rw [← integral_indicator hC,partitionAreaMeasure,
    integral_finsetSum_measure hint]
  unfold restrictedPartitionFormMass
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator hC, integral_chartAreaMeasure_restrict _
    (partitionChartDensity_properties B ρ hρ hΛ i).1.continuous.measurable
    (partitionChartDensity_nonneg B ρ hpos i)
    (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy) hC hf.continuous.measurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => (partitionChartDensity_spatial_smul B ρ Λ f i y).symm)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partitionAreaMeasure_null (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (Λ : ManifoldTwoForm Plane M)
    {C : Set M} (hC : MeasurableSet C)
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C)=0) :
    partitionAreaMeasure B ρ Λ C=0 := by
  rw [partitionAreaMeasure,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact chartAreaMeasure_null _ (fun _ hy => partitionChartDensity_off_target B ρ Λ i hy)
    hC (hnull i)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem fixedCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ContDiff ℝ ∞ (fun q : P × Plane => fixedCovectorOperator A hA (fun x => f (q.1,x)) q.2) ∧
      (∀ p x y, A ≤ |x| ∨ A ≤ |y| → fixedCovectorOperator A hA (fun z => f (p,z)) (x,y)=0) ∧
      (∀ p z, euclideanExteriorOneForm (fixedCovectorOperator A hA (fun x => f (p,x))) z =
        f (p,z) • planarArea) := by
  let b : ContDiffBump (0 : ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρs (x : ℝ) (hx : A ≤ |x|) : ρ x=0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hh : |x|<A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hh
  have hρ1 : (∫ x in -A..A, ρ x)=1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact b.integral_normed
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hfc (y : P) : HasCompactSupport (fun x => f (y,x)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) A)
    intro p hp
    have hh : A < max |p.1| |p.2| := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hp
    exact hzero y p.1 p.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  have hg (y : P) : ContDiff ℝ ∞ (planarMarginal A (fun x => f (y,x))) :=
    planarMarginal_smooth (hfy y) A
  have hgt (y : P) (t : ℝ) (ht : A ≤ |t|) : planarMarginal A (fun x => f (y,x)) t=0 := by
    unfold planarMarginal
    have he : (fun x => f (y,(x,t))) = fun _ => (0:ℝ) := funext fun x => hzero y x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hgm (y : P) (t : ℝ) : planarMarginal A (fun x => f (y,x)) t = ∫ x, f (y,(x,t)) :=
    integral_eq_full_of_box_support (fun x hx => hzero y x t (Or.inl hx))
  have hgm0 (y : P) : (∫ t in -A..A, planarMarginal A (fun x => f (y,x)) t)=0 := by
    rw [integral_eq_full_of_box_support (hgt y)]
    simp_rw [hgm]
    rw [←integral_prod_symm (fun x => f (y,x))]
    · exact hmass y
    · exact (hfy y).continuous.integrable_of_hasCompactSupport (hfc y)
  let U : P × Plane → ℝ := fun p => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2
  let V : P × Plane → ℝ := fun p => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2
  have hU : ContDiff ℝ ∞ U := (planarPrimitive_parameter_smooth hf hρ A).1
  have hV : ContDiff ℝ ∞ V := (planarPrimitive_parameter_smooth hf hρ A).2
  change ContDiff ℝ ∞ (fun q => planarCovector (U q) (V q)) ∧
    (∀ p x y, A ≤ |x| ∨ A ≤ |y| → planarCovector (U (p,(x,y))) (V (p,(x,y)))=0) ∧
    (∀ p z, euclideanExteriorOneForm (fun x => planarCovector (U (p,x)) (V (p,x))) z = f (p,z) • planarArea)
  refine ⟨planarCovector_smooth hU hV,?_,?_⟩
  · intro p x y h
    obtain ⟨h1,h2⟩ := planarPrimitive_zero_outside hA.le (hfy p).continuous hρ.continuous
      (hzero p) hρs hρ1 (hg p).continuous (hgm0 p) (x,y) h
    change planarCovector (planarPrimitiveX A (fun z => f (p,z)) ρ (x,y))
      (planarPrimitiveY A (fun z => f (p,z)) ρ (x,y))=0
    rw [h1,h2,planarCovector_zero]
  · intro p z
    have hUp : ContDiff ℝ ∞ (fun x => U (p,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
    have hVp : ContDiff ℝ ∞ (fun x => V (p,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
    rw [planarCovector_exterior hUp hVp]
    congr 1
    exact planarPrimitive_curl (hfy p).continuous hρ.continuous (hg p).continuous z

theorem translated_covector_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {β : P × Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (a : Plane) :
    ContDiff ℝ ∞ (fun q : P × Plane => β (q.1,q.2-a)) :=
  hβ.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))

theorem covector_family_slice_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {β : P × Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (p : P) :
    ContDiff ℝ ∞ (fun z => β (p,z)) :=
  hβ.comp (contDiff_const.prodMk contDiff_id)

theorem translatedCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A) (a : Plane)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ContDiff ℝ ∞ (fun q : P × Plane => translatedCovectorOperator A hA a (fun x => f (q.1,x)) q.2) ∧
      (∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → translatedCovectorOperator A hA a (fun z => f (p,z)) (x,y)=0) ∧
      (∀ p z, euclideanExteriorOneForm (translatedCovectorOperator A hA a (fun x => f (p,x))) z =
        f (p,z) • planarArea) := by
  let g : P × Plane → ℝ := fun q => f (q.1,q.2+a)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hgzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → g (p,(x,y))=0 := by
    intro p x y h
    apply hzero
    simpa only [add_sub_cancel_right] using h
  have hgmass : ∀ p, (∫ x, g (p,x))=0 := by
    intro p
    exact (integral_add_right_eq_self (fun x => f (p,x)) a).trans (hmass p)
  have hs := fixedCovectorOperator_spec (P := P) (A := A) hA (f := g) hg hgzero hgmass
  refine ⟨?_,?_,?_⟩
  · have hh : ContDiff ℝ ∞ (fun q : P × Plane =>
        fixedCovectorOperator A hA (fun w => g (q.1,w)) (q.2-a)) :=
      translated_covector_family_smooth (β := fun q : P × Plane =>
        fixedCovectorOperator A hA (fun w => g (q.1,w)) q.2) hs.1 a
    exact hh
  · intro p x y h
    exact hs.2.1 p (x-a.1) (y-a.2) h
  · intro p z
    have hβp : ContDiff ℝ ∞ (fixedCovectorOperator A hA (fun x => g (p,x))) :=
      covector_family_slice_smooth (β := fun q : P × Plane =>
        fixedCovectorOperator A hA (fun w => g (q.1,w)) q.2) hs.1 p
    change euclideanExteriorOneForm (fun x => fixedCovectorOperator A hA (fun w => g (p,w)) (x-a)) z = _
    rw [translated_covector_exterior (a := a) (z := z) hβp,hs.2.2]
    simp only [g,sub_add_cancel]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

theorem boxCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (B : SurfaceCoordinateBox M)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    {K : Set M} (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (hz : ∀ p x, x ∉ K → Ω p x=0) (hmass : ∀ p, chartMass B.center (Ω p)=0) :
    SmoothOneFormFamily (fun p => boxCovectorOperator B (Ω p)) ∧
      (∀ p x, x ∉ B.compactCarrier → boxCovectorOperator B (Ω p) x=0) ∧
      (∀ p c y, y ∈ (extChartAt 𝓘(ℝ,Plane) c).target →
        euclideanExteriorOneForm (chartOneForm (boxCovectorOperator B (Ω p)) c) y =
          chartTwoForm (Ω p) c y) := by
  have hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) B.center).source := fun x hx => (hKB hx).1
  let f := extendedChartCoefficient B.center Ω
  have hf : ContDiff ℝ ∞ f := extendedChartCoefficient_smooth (hΩ B.center) hK hKc hz
  have hzero (p : P) (x y : ℝ) (hxy : B.radius ≤ |x-B.point.1| ∨ B.radius ≤ |y-B.point.2|) :
      f (p,(x,y))=0 := by
    apply extendedChartCoefficient_zero hz p
    rintro ⟨z,hzK,hzxy⟩
    have hb := (hKB hzK).2
    change extChartAt 𝓘(ℝ,Plane) B.center z ∈ Metric.ball B.point B.radius at hb
    rw [hzxy] at hb
    have hh : max |x-B.point.1| |y-B.point.2| < B.radius := by
      simpa only [Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using hb
    rcases hxy with hx|hy
    · exact False.elim ((not_lt_of_ge hx) (lt_of_le_of_lt (le_max_left _ _) hh))
    · exact False.elim ((not_lt_of_ge hy) (lt_of_le_of_lt (le_max_right _ _) hh))
  let β : P × Plane → Plane →L[ℝ] ℝ := fun q =>
    translatedCovectorOperator B.radius B.radius_pos B.point (fun y => f (q.1,y)) q.2
  have hs := translatedCovectorOperator_spec B.radius_pos B.point hf hzero hmass
  have hbzero (p : P) (z : Plane) (hz : z ∉ Metric.closedBall B.point B.radius) : β (p,z)=0 := by
    have hh : B.radius < max |z.1-B.point.1| |z.2-B.point.2| := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
        Real.norm_eq_abs,not_le] using hz
    exact hs.2.1 p z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  refine ⟨?_,?_,?_⟩
  · intro c
    exact chartSupportedOneForm_smooth hs.1 (isCompact_closedBall B.point B.radius) B.closed_subset hbzero c
  · intro p x hx
    exact chartSupportedOneForm_zero (hbzero p) hx
  · intro p c y hy
    have hp : ContDiff ℝ ∞ (fun z => β (p,z)) := hs.1.comp (contDiff_const.prodMk contDiff_id)
    change euclideanExteriorOneForm (chartOneForm (chartSupportedOneForm B.center (fun z => β (p,z))) c) y = _
    rw [chartSupportedOneForm_exterior hp (isCompact_closedBall B.point B.radius) B.closed_subset (hbzero p) hy]
    have he : euclideanExteriorOneForm (fun z => β (p,z)) = fun z => f (p,z) • planarArea := funext (hs.2.2 p)
    rw [he]
    exact congrArg (fun Ω => chartTwoForm Ω c y) (chartSupported_extendedCoefficient hskew hKc hz p)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfacePrimitiveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I : Type*} [Fintype I] {K : Set M}

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem surfaceCovectorSupport_compact (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (D : SurfaceMassTransferData B B₀) : IsCompact (surfaceCovectorSupport B B₀ D) := by
  apply isCompact_iUnion
  intro i
  exact (B i).isCompact_compactCarrier.union (D.compact_supportSet i)

theorem surfaceCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (B₀ : SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (D : SurfaceMassTransferData B B₀)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u) (hz : ∀ p x, x ∉ K → Ω p x=0)
    (hmass : ∀ p, partitionFormMass B ρ (Ω p)=0) :
    IsPrimitiveFamily Ω (fun p => surfaceCovectorOperator B B₀ ρ D (Ω p)) ∧
      (∀ p x, x ∉ surfaceCovectorSupport B B₀ D →
        surfaceCovectorOperator B B₀ ρ D (Ω p) x=0) := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let Ωi := partitionTwoForm ρ Ω
  let Ki : I → Set M := fun i => K ∩ tsupport (ρ i)
  have hKi (i : I) : IsCompact (Ki i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hKiB (i : I) : Ki i ⊆ (B i).carrier := fun _ hx => hρ i hx.2
  have hΩi (i : I) : SmoothTwoFormFamily (Ωi i) := partitionTwoForm_smooth ρ hΩ i
  have hzΩi (i : I) : ∀ p x, x ∉ Ki i → Ωi i p x=0 := partitionTwoForm_zero ρ hz i
  have hsΩi (i : I) : ∀ p x u v, Ωi i p x u v = -Ωi i p x v u :=
    partitionTwoForm_skew ρ hskew i
  let m : I → P → ℝ := fun i p => chartMass (B i).center (Ωi i p)
  have hm (i : I) : ContDiff ℝ ∞ (m i) :=
    chartMass_smooth (hΩi i (B i).center) (hKi i) (fun x hx => (hKiB i hx).1) (hzΩi i)
  let Ξ : I → P → ManifoldTwoForm Plane M := fun i p => Ωi i p-m i p • (D.bump i).form
  have hlocal (i : I) : IsPrimitiveFamily (Ξ i) (fun p => boxCovectorOperator (B i) (Ξ i p)) ∧
      ∀ p x, x ∉ (B i).compactCarrier → boxCovectorOperator (B i) (Ξ i p) x=0 := by
    have hscaled : SmoothTwoFormFamily (fun p => m i p • (D.bump i).form) :=
      (SmoothTwoFormFamily.const (D.bump i).smooth).smul (hm i)
    have hdif : SmoothTwoFormFamily (Ξ i) := (hΩi i).sub hscaled
    have ha : ∀ p x u v, Ξ i p x u v = -Ξ i p x v u := by
      intro p x u v
      change Ωi i p x u v - m i p * (D.bump i).form x u v =
        -(Ωi i p x v u - m i p * (D.bump i).form x v u)
      rw [hsΩi i p x u v,(D.bump i).skew x u v]; ring
    have hzero : ∀ p x, x ∉ Ki i ∪ (D.bump i).supportSet → Ξ i p x=0 := by
      intro p x hx
      change Ωi i p x - m i p • (D.bump i).form x=0
      rw [hzΩi i p x (fun hk => hx (Or.inl hk)),
        (D.bump i).zero_off x (fun hk => hx (Or.inr hk))]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change (0 : ℝ) - m i p * 0 = 0
      rw [mul_zero,sub_self]
    have hmasslocal : ∀ p, chartMass (B i).center (Ξ i p)=0 := by
      intro p
      have h1 := (hΩi i).eval p |>.coefficient_integrable (B i).center (hKi i)
        (fun x hx => (hKiB i hx).1) (hzΩi i p)
      have h2 := hscaled.eval p |>.coefficient_integrable (B i).center (D.bump i).compact_supportSet
        (fun x hx => ((D.bump i).support_subset hx).1)
        (fun x hx => by
          change m i p • (D.bump i).form x=0
          rw [(D.bump i).zero_off x hx]
          apply ContinuousLinearMap.ext
          intro first
          apply ContinuousLinearMap.ext
          intro second
          exact mul_zero _)
      change chartMass (B i).center (Ωi i p-m i p • (D.bump i).form)=0
      rw [chartMass_sub h1 h2,chartMass_smul,(D.bump i).unit_mass,mul_one]
      exact sub_self _
    have hh := boxCovectorOperator_spec (B i) hdif ha ((hKi i).union (D.bump i).compact_supportSet)
      (union_subset (hKiB i) (D.bump i).support_subset) hzero hmasslocal
    exact ⟨⟨hh.1,hh.2.2⟩,hh.2.1⟩
  let α : I → P → ManifoldOneForm Plane M := fun i p =>
    boxCovectorOperator (B i) (Ξ i p) + m i p • D.primitive i
  have hα (i : I) : IsPrimitiveFamily (fun p => Ωi i p-m i p • D.common.form) (α i) := by
    have ht := ((D.primitive_spec i).const_slice (P := P) 0).smul (hm i)
    have hh := (hlocal i).1.add ht
    have he : (Ξ i + fun p => m i p • ((D.bump i).form-D.common.form)) =
        (fun p => Ωi i p - m i p • D.common.form) := by
      funext p x
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change Ωi i p x u v - m i p * (D.bump i).form x u v +
        m i p * ((D.bump i).form x u v - D.common.form x u v) =
          Ωi i p x u v - m i p * D.common.form x u v
      ring
    exact he ▸ hh
  have hall := IsPrimitiveFamily.sum Finset.univ (fun i _ => hα i)
  have he : (∑ i, fun p => Ωi i p-m i p • D.common.form)=Ω := by
    funext p x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [Finset.sum_apply,sum_apply,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,smul_eq_mul]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul]
    have hm0 : (∑ i, m i p)=0 := hmass p
    rw [hm0,zero_mul,sub_zero]
    have hh := congrArg (fun F : P → ManifoldTwoForm Plane M => F p x u v)
      (partitionTwoForm_sum ρ hz)
    simpa only [Finset.sum_apply,sum_apply] using hh
  have hαsum : (∑ i, α i) = fun p => surfaceCovectorOperator B B₀ ρ D (Ω p) := by
    funext p x
    simp only [Finset.sum_apply,surfaceCovectorOperator,α,Ξ,m,Ωi,Pi.add_apply,Pi.smul_apply]
    rfl
  refine ⟨hαsum ▸ he ▸ hall,?_⟩
  intro p x hx
  change (∑ i, α i p) x=0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hxi : x ∉ (B i).compactCarrier ∪ D.supportSet i := fun hi => hx (mem_iUnion.mpr ⟨i,hi⟩)
  change boxCovectorOperator (B i) (Ξ i p) x + m i p • D.primitive i x=0
  rw [(hlocal i).2 p x (fun hi => hxi (Or.inl hi)),D.zero_off i x (fun hi => hxi (Or.inr hi)),
    smul_zero,add_zero]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory
open Filter

@[simp] theorem diagonalScale_det (a b : ℝ) : (diagonalScale a b).det = a*b := by
  rw [planar_det]
  simp [planarArea_apply]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceInteriorBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SurfaceCoordinateBox

theorem interior_overlap_chain {U : Set M} (hU : IsOpen U) (hc : IsPreconnected U)
    (B C : Inside U) :
    Relation.ReflTransGen (fun A D : Inside U => (A.1.carrier ∩ D.1.carrier).Nonempty) B C := by
  let := Subtype.preconnectedSpace hc
  let V : Inside U → Set U := fun D => Subtype.val ⁻¹' D.1.carrier
  have ho (D : Inside U) : IsOpen (V D) := D.1.isOpen_carrier.preimage continuous_subtype_val
  have hcover (x : U) : ∃ D, x ∈ V D := by
    obtain ⟨D,hx,hDU⟩ := exists_compactCarrier_subset hU x.property
    exact ⟨⟨D,hDU⟩,hx⟩
  have hn (D : Inside U) : (V D).Nonempty := by
    obtain ⟨x,hx⟩ := D.1.nonempty_carrier
    exact ⟨⟨x,D.2 (D.1.carrier_subset_compactCarrier hx)⟩,hx⟩
  have hh := connected_cover_overlap_chain ho hcover (hn B) (hn C)
  induction hh with
  | refl => exact Relation.ReflTransGen.refl
  | @tail A D _ hAD ih =>
    obtain ⟨x,hxA,hxD⟩ := hAD
    exact ih.tail ⟨x.1,hxA,hxD⟩

theorem finite_partition_inside [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
    [SigmaCompactSpace M] {K U : Set M} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (s : Finset (Inside U))
      (ρ : SmoothPartitionOfUnity s 𝓘(ℝ,Plane) M K),
      ρ.IsSubordinate (fun B => B.1.1.carrier) := by
  classical
  have hcover : K ⊆ ⋃ B : Inside U, B.1.carrier := by
    intro x hx
    obtain ⟨B,hxB,hBU⟩ := exists_compactCarrier_subset hU (hKU hx)
    exact mem_iUnion.mpr ⟨⟨B,hBU⟩,hxB⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun B : Inside U => B.1.carrier)
    (fun B => B.1.isOpen_carrier) hcover
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Plane) hK.isClosed
    (fun B : s => B.1.1.carrier) (fun B => B.1.1.isOpen_carrier) (by
      intro x hx
      obtain ⟨B,hBs,hxB⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨B,hBs⟩,hxB⟩)
  exact ⟨s,ρ,hρ⟩

end SurfaceCoordinateBox

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem HasInteriorPrimitiveFamily.add {U : Set M} {Ω Λ : P → ManifoldTwoForm Plane M}
    (hΩ : HasInteriorPrimitiveFamily U Ω) (hΛ : HasInteriorPrimitiveFamily U Λ) :
    HasInteriorPrimitiveFamily U (Ω+Λ) := by
  obtain ⟨K,hK,hKU,α,hα,hzα⟩ := hΩ
  obtain ⟨L,hL,hLU,β,hβ,hzβ⟩ := hΛ
  refine ⟨K∪L,hK.union hL,union_subset hKU hLU,α+β,hα.add hβ,?_⟩
  intro p x hx
  change α p x+β p x=0
  rw [hzα p x (fun hk => hx (Or.inl hk)),hzβ p x (fun hl => hx (Or.inr hl)),add_zero]

theorem surface_box_difference_inside {U : Set M} (B : SurfaceCoordinateBox M)
    (hBU : B.compactCarrier ⊆ U)
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hsΩ : ∀ x u v,Ω x u v= -Ω x v u) (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K⊆B.carrier) (hLB : L⊆B.carrier)
    (hzΩ : ∀ x,x∉K→Ω x=0) (hzΛ : ∀ x,x∉L→Λ x=0)
    (hm : chartMass B.center Ω=chartMass B.center Λ) :
    HasInteriorPrimitiveFamily U (fun _ : P => Ω-Λ) := by
  have hs : ∀ p : P,∀ x u v,(Ω-Λ) x u v= -(Ω-Λ) x v u := by
    intro _ x u v
    change Ω x u v-Λ x u v= -(Ω x v u-Λ x v u)
    rw [hsΩ x u v,hsΛ x u v]; ring
  have hz : ∀ p : P,∀ x,x∉K∪L→(Ω-Λ) x=0 := by
    intro _ x hx
    change Ω x-Λ x=0
    rw [hzΩ x (fun hk => hx (Or.inl hk)),hzΛ x (fun hl => hx (Or.inr hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    exact sub_self (0 : ℝ)
  have hm0 : ∀ _ : P,chartMass B.center (Ω-Λ)=0 := by
    intro _
    rw [chartMass_sub (hΩ.coefficient_integrable B.center hK (fun x hx => (hKB hx).1) hzΩ)
      (hΛ.coefficient_integrable B.center hL (fun x hx => (hLB hx).1) hzΛ),hm,sub_self]
  have hh := boxCovectorOperator_spec B
    ((SmoothTwoFormFamily.const (P := P) hΩ).sub (SmoothTwoFormFamily.const hΛ))
    hs (hK.union hL) (union_subset hKB hLB) hz hm0
  exact ⟨B.compactCarrier,B.isCompact_compactCarrier,hBU,
    (fun _ : P => boxCovectorOperator B (Ω-Λ)),⟨hh.1,hh.2.2⟩,hh.2.1⟩

theorem surface_overlap_difference_inside {U : Set M} (hpos : PositivePlaneTransitions M)
    {B C : SurfaceCoordinateBox M} (hBU : B.compactCarrier⊆U) (hCU : C.compactCarrier⊆U)
    (β : BoxUnitBump B) (γ : BoxUnitBump C) (hBC : (B.carrier∩C.carrier).Nonempty) :
    HasInteriorPrimitiveFamily U (fun _ : P => β.form-γ.form) := by
  obtain ⟨x,hx⟩ := hBC
  obtain ⟨D,_,hD⟩ := SurfaceCoordinateBox.exists_compactCarrier_subset
    (B.isOpen_carrier.inter C.isOpen_carrier) hx
  obtain ⟨δ⟩ := D.exists_unit_bump
  have hδB : δ.supportSet⊆B.carrier :=
    δ.support_subset.trans (D.carrier_subset_compactCarrier.trans (hD.trans inter_subset_left))
  have hδC : δ.supportSet⊆C.carrier :=
    δ.support_subset.trans (D.carrier_subset_compactCarrier.trans (hD.trans inter_subset_right))
  have h1 : HasInteriorPrimitiveFamily U (fun _ : P => β.form-δ.form) :=
    surface_box_difference_inside B hBU β.smooth δ.smooth β.skew δ.skew β.compact_supportSet
      δ.compact_supportSet β.support_subset hδB β.zero_off δ.zero_off
      (β.unit_mass.trans (δ.mass_in_chart hpos B.center (fun z hz => (hδB hz).1)).symm)
  have h2 : HasInteriorPrimitiveFamily U (fun _ : P => δ.form-γ.form) :=
    surface_box_difference_inside C hCU δ.smooth γ.smooth δ.skew γ.skew δ.compact_supportSet
      γ.compact_supportSet hδC γ.support_subset δ.zero_off γ.zero_off
      ((δ.mass_in_chart hpos C.center (fun z hz => (hδC hz).1)).trans γ.unit_mass.symm)
  have he : (fun _ : P => β.form-δ.form)+(fun _ : P => δ.form-γ.form)=
      (fun _ : P => β.form-γ.form) := by
    funext p; simp only [Pi.add_apply]; abel
  exact he ▸ h1.add h2

theorem surface_bump_difference_inside {U : Set M} (hU : IsOpen U) (hc : IsPreconnected U)
    (hpos : PositivePlaneTransitions M) {B C : SurfaceCoordinateBox.Inside U}
    (β : BoxUnitBump B.1) (γ : BoxUnitBump C.1) :
    HasInteriorPrimitiveFamily U (fun _ : P => β.form-γ.form) := by
  have hchain := SurfaceCoordinateBox.interior_overlap_chain hU hc B C
  revert γ
  induction hchain with
  | refl =>
    intro γ
    exact surface_box_difference_inside B.1 B.2 β.smooth γ.smooth β.skew γ.skew
      β.compact_supportSet γ.compact_supportSet β.support_subset γ.support_subset
      β.zero_off γ.zero_off (β.unit_mass.trans γ.unit_mass.symm)
  | @tail C D _ hCD ih =>
    intro γ
    obtain ⟨δ⟩ := C.1.exists_unit_bump
    have h1 := ih δ
    have h2 : HasInteriorPrimitiveFamily U (fun _ : P => δ.form-γ.form) :=
      surface_overlap_difference_inside hpos C.2 D.2 δ γ hCD
    have he : (fun _ : P => β.form-δ.form)+(fun _ : P => δ.form-γ.form)=
        (fun _ : P => β.form-γ.form) := by
      funext p; simp only [Pi.add_apply]; abel
    exact he ▸ h1.add h2

theorem exists_interior_mass_transfer_data {I : Type*} {U : Set M}
    (hU : IsOpen U) (hc : IsPreconnected U) (hpos : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox.Inside U) (B₀ : SurfaceCoordinateBox.Inside U) :
    ∃ D : SurfaceMassTransferData (fun i => (B i).1) B₀.1,
      ∀ i,D.supportSet i⊆U := by
  classical
  let β (i : I) : BoxUnitBump (B i).1 := Classical.choice (B i).1.exists_unit_bump
  obtain ⟨β₀⟩ := B₀.1.exists_unit_bump
  have hh (i : I) := surface_bump_difference_inside (P := ℝ) hU hc hpos (β i) β₀
  choose L hL hLU α hα hz using hh
  refine ⟨⟨β,β₀,(fun i => α i 0),L,hL,(fun i => hz i 0),?_⟩,hLU⟩
  intro i
  exact (hα i).const_slice (P := ℝ) 0

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K L : Set M}

theorem restrictSurfacePartition_subordinate
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hLK : L⊆K)
    {V : I → Set M} (hρ : ρ.IsSubordinate V) :
    (restrictSurfacePartition ρ hLK).IsSubordinate V := hρ

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {I : Type*} [Fintype I] {K L U : Set M}

theorem interior_surface_primitive (hU : IsOpen U) (hc : IsPreconnected U)
    (hne : U.Nonempty) (hpos : PositivePlaneTransitions M)
    (hL : IsCompact L) (hLU : L⊆U) (hLK : L⊆K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v,Ω p x u v= -Ω p x v u)
    (hz : ∀ p x,x∉L→Ω p x=0)
    (hmass : ∀ p,partitionFormMass B ρ (Ω p)=0) :
    HasInteriorPrimitiveFamily U Ω := by
  obtain ⟨s,ν,hν⟩ := SurfaceCoordinateBox.finite_partition_inside hL hU hLU
  let C : s → SurfaceCoordinateBox.Inside U := fun i => i.1
  obtain ⟨x,hx⟩ := hne
  obtain ⟨B₀,_,hB₀⟩ := SurfaceCoordinateBox.exists_compactCarrier_subset hU hx
  obtain ⟨D,hD⟩ := exists_interior_mass_transfer_data hU hc hpos C ⟨B₀,hB₀⟩
  have hm (p : P) : partitionFormMass (fun i => (C i).1) ν (Ω p)=0 := by
    rw [← partitionFormMass_independent hpos hL B (fun i => (C i).1)
      (restrictSurfacePartition ρ hLK) ν
      (restrictSurfacePartition_subordinate ρ hLK hρ) hν (hΩ.eval p) (hskew p) (hz p)]
    exact hmass p
  have hh := surfaceCovectorOperator_spec hL (fun i => (C i).1) B₀ ν hν D hΩ hskew hz hm
  refine ⟨surfaceCovectorSupport (fun i => (C i).1) B₀ D,
    surfaceCovectorSupport_compact _ _ _,?_,
    (fun p => surfaceCovectorOperator (fun i => (C i).1) B₀ ν D (Ω p)),hh⟩
  intro z hz
  obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
  exact hzi.elim (fun ht => (C i).2 ht) (fun ht => hD i ht)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem SmoothTwoFormFamily.coefficient_smul {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) {f : P × M → ℝ}
    (hf : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f) :
    SmoothTwoFormFamily (fun p x => f (p,x) • Ω p x) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  intro c q hq
  have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) c).symm q.2 :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hinv : ContMDiffAt (𝓘(ℝ,P).prod 𝓘(ℝ,E)) (𝓘(ℝ,P).prod 𝓘(ℝ,E)) ∞
      (fun z : P × E => (z.1,(extChartAt 𝓘(ℝ,E) c).symm z.2)) q :=
    contMDiffAt_fst.prodMk (hi.comp q contMDiffAt_snd)
  have hfs : ContDiffAt ℝ ∞
      (fun z : P × E => f (z.1,(extChartAt 𝓘(ℝ,E) c).symm z.2)) q :=
    by
      have hmd := hf.contMDiffAt.comp q hinv
      rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hmd
      exact hmd.contDiffAt
  have hΩs := (hΩ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartTwoForm_spatial_smul,Pi.smul_def'] using (hfs.smul hΩs).contDiffWithinAt

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_interior_boundary_cutoff {K V : Set M} (hK : IsCompact K)
    (hV : IsOpen V) (hfront : frontier K⊆V) :
    ∃ ψ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ψ ∧
      IsCompact (tsupport ψ) ∧ tsupport ψ⊆interior K ∧
      (∀ x∈K, x∉V→ψ x=1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have hL : IsCompact (K\V) := hK.diff hV
  have hLK : K\V⊆interior K := by
    intro x hx
    by_contra hn
    exact hx.2 (hfront ⟨subset_closure hx.1,hn⟩)
  obtain ⟨D,hD,hLD,hDK⟩ := exists_compact_between hL isOpen_interior hLK
  obtain ⟨ψ,hψ1,hψ0,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hL.isClosed hLD
  have hs : tsupport (ψ : M → ℝ)⊆D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hψ0 x hn)) hD.isClosed
  refine ⟨ψ,ψ.contMDiff,hD.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hDK,?_⟩
  intro x hx hn
  exact (subset_of_mem_nhdsSet hψ1 ⟨hx,hn⟩)

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_interior_coefficient_difference {K V : Set M}
    (hK : IsCompact K) (hV : IsOpen V) (hfront : frontier K⊆V)
    {a b : P × M → ℝ}
    (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ b)
    (hgerm : ∀ p x,x∈V→a (p,x)=b (p,x)) :
    ∃ (L : Set M) (d : P × M → ℝ),IsCompact L ∧ L⊆interior K ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ d ∧
      (∀ p x,x∈K→d (p,x)=a (p,x)-b (p,x)) ∧
      (∀ p x,x∉L→d (p,x)=0) := by
  obtain ⟨ψ,hψ,hL,hLK,hψ1⟩ := exists_interior_boundary_cutoff (E := E) hK hV hfront
  refine ⟨tsupport ψ,(fun q => ψ q.2*(a q-b q)),hL,hLK,
    (hψ.comp contMDiff_snd).mul (ha.sub hb),?_,?_⟩
  · intro p x hx
    change ψ x * (a (p,x)-b (p,x))=a (p,x)-b (p,x)
    by_cases hv : x∈V
    · rw [hgerm p x hv,sub_self,mul_zero]
    · rw [hψ1 x hx hv,one_mul]
  · intro p x hx
    change ψ x * (a (p,x)-b (p,x))=0
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K L : Set M}

theorem interior_difference_mass
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (hK : MeasurableSet K)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {a b d : P × M → ℝ}
    (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b)
    (hd : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d)
    (hLK : L⊆K) (hz : ∀ p x,x∉L→d (p,x)=0)
    (he : ∀ p x,x∈K→d (p,x)=a (p,x)-b (p,x)) (p : P) :
    partitionFormMass B ρ (fun x => d (p,x) • Λ x)=
      restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
      restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x) := by
  have ha' : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => a (p,x)) :=
    ha.comp (contMDiff_const.prodMk contMDiff_id)
  have hb' : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => b (p,x)) :=
    hb.comp (contMDiff_const.prodMk contMDiff_id)
  have hd' : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => d (p,x)) :=
    hd.comp (contMDiff_const.prodMk contMDiff_id)
  rw [← integral_partitionAreaMeasure B ρ hρ hΛ hpos hd']
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K) (fun x hx => hz p x (fun hl => hx (hLK hl)))]
  calc
    (∫ x in K,d (p,x) ∂partitionAreaMeasure B ρ Λ)=
        ∫ x in K,(a (p,x)-b (p,x)) ∂partitionAreaMeasure B ρ Λ :=
      setIntegral_congr_fun hK (he p)
    _ = (∫ x in K,a (p,x) ∂partitionAreaMeasure B ρ Λ)-
        ∫ x in K,b (p,x) ∂partitionAreaMeasure B ρ Λ :=
      integral_sub (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos ha').integrableOn
        (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos hb').integrableOn
    _ = _ := by
      rw [integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK ha',
        integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK hb']

theorem restricted_form_mass_nonneg
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (hK : MeasurableSet K)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f)
    (hfpos : ∀ x∈K,0≤f x) :
    0 ≤ restrictedPartitionFormMass B ρ K (fun x => f x • Λ x) := by
  rw [← integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK hf]
  exact setIntegral_nonneg hK hfpos

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

theorem partitionFormMass_smooth (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hz : ∀ p x,x∉K→Ω p x=0) :
    ContDiff ℝ ∞ (fun p => partitionFormMass B ρ (Ω p)) := by
  apply ContDiff.sum
  intro i _
  exact chartMass_smooth (partitionTwoForm_smooth ρ hΩ i (B i).center)
    (hK.inter_right (isClosed_tsupport (ρ i)))
    (fun _ hx => (hρ i hx.2).1) (partitionTwoForm_zero ρ hz i)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem partitionFormMass_sub (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hzΩ : ∀ x,x∉K→Ω x=0) (hzΛ : ∀ x,x∉K→Λ x=0) :
    partitionFormMass B ρ (Ω-Λ)=partitionFormMass B ρ Ω-partitionFormMass B ρ Λ := by
  have he : Ω-Λ=Ω+(-1:ℝ) • Λ := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change Ω x u v-Λ x u v=Ω x u v+(-1)*Λ x u v
    ring
  rw [he,partitionFormMass_add hK B ρ hρ hΩ
    (((SmoothTwoFormFamily.const (P := ℝ) hΛ).smul contDiff_const).eval (0:ℝ))
    hzΩ (fun x hx => by
      change (-1:ℝ) • Λ x=0
      rw [hzΛ x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_zero (-1:ℝ)),
    partitionFormMass_smul]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceRedistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {I : Type*} [Fintype I] {K L T : Set M}

theorem surface_interior_redistribution
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hpos : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {D : P → ManifoldTwoForm Plane M} (hD : SmoothTwoFormFamily D)
    (hsD : ∀ p x u v,D p x u v= -D p x v u)
    (hL : IsCompact L) (hLK : L⊆interior K) (hzD : ∀ p x,x∉L→D p x=0)
    {χ : ManifoldTwoForm Plane M} (hχ : SmoothTwoForm χ)
    (hsχ : ∀ x u v,χ x u v= -χ x v u)
    (hT : IsCompact T) (hTK : T⊆interior K) (hzχ : ∀ x,x∉T→χ x=0)
    (hmχ : partitionFormMass B ρ χ=1) :
    ContDiff ℝ ∞ (fun p => partitionFormMass B ρ (D p)) ∧
      SmoothTwoFormFamily (redistributedDifference B ρ D χ) ∧
      (∀ p,partitionFormMass B ρ (redistributedDifference B ρ D χ p)=0) ∧
      HasInteriorPrimitiveFamily (interior K) (redistributedDifference B ρ D χ) := by
  have hzDK : ∀ p x,x∉K→D p x=0 :=
    fun p x hx => hzD p x (fun hl => hx (interior_subset (hLK hl)))
  have hzχK : ∀ x,x∉K→χ x=0 :=
    fun x hx => hzχ x (fun ht => hx (interior_subset (hTK ht)))
  let H : P → ℝ := fun p => partitionFormMass B ρ (D p)
  have hH : ContDiff ℝ ∞ H := partitionFormMass_smooth hK B ρ hρ hD hzDK
  have hHχ : SmoothTwoFormFamily (fun p => H p • χ) :=
    (SmoothTwoFormFamily.const hχ).smul hH
  have hΞ : SmoothTwoFormFamily (redistributedDifference B ρ D χ) := hHχ.sub hD
  have hs : ∀ p x u v,redistributedDifference B ρ D χ p x u v=
      -redistributedDifference B ρ D χ p x v u := by
    intro p x u v
    change H p*χ x u v-D p x u v= -(H p*χ x v u-D p x v u)
    rw [hsχ x u v,hsD p x u v]; ring
  have hz : ∀ p x,x∉L∪T→ redistributedDifference B ρ D χ p x=0 := by
    intro p x hx
    change H p • χ x-D p x=0
    rw [hzχ x (fun ht => hx (Or.inr ht)),hzD p x (fun hl => hx (Or.inl hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change H p*0-0=0
    ring
  have hm (p : P) : partitionFormMass B ρ (redistributedDifference B ρ D χ p)=0 := by
    change partitionFormMass B ρ (H p • χ-D p)=0
    have hzHχ : ∀ x,x∉K→(H p • χ) x=0 := by
      intro x hx
      change H p • χ x=0
      rw [hzχK x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_zero (H p)
    rw [partitionFormMass_sub hK B ρ hρ (hHχ.eval p) (hD.eval p) hzHχ (hzDK p),
      partitionFormMass_smul,hmχ,mul_one]
    exact sub_self _
  refine ⟨hH,hΞ,hm,?_⟩
  exact interior_surface_primitive isOpen_interior hc hne hpos (hL.union hT)
    (union_subset hLK hTK) ((union_subset hLK hTK).trans interior_subset)
    B ρ hρ hΞ hs hz hm


end

section
open scoped ContDiff Manifold Topology ENNReal
open Set Function Manifold MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [μ.OuterRegular]

omit [BorelSpace M] in

theorem exists_small_measure_smooth_cutoff {C H : Set M}
    (hC : IsCompact C) (hnull : μ C=0) (hH : IsClosed H) (hdis : Disjoint C H)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ ζ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
      (∀ x, ζ x ∈ Icc (0:ℝ) 1) ∧ (∀ x ∈ H, ζ x=0) ∧
      (∀ᶠ x in 𝓝ˢ C, ζ x=1) ∧ μ (tsupport ζ) < ENNReal.ofReal δ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨U,hCU,hU,hμU⟩ := C.exists_isOpen_lt_of_lt (μ := μ) (ENNReal.ofReal δ)
    (by simpa only [hnull] using (ENNReal.ofReal_pos.mpr hδ))
  have hCV : C ⊆ U ∩ Hᶜ := fun x hx => ⟨hCU hx,disjoint_left.mp hdis hx⟩
  obtain ⟨D,hD,hCD,hDV⟩ := exists_compact_between hC (hU.inter hH.isOpen_compl) hCV
  obtain ⟨ζ,hζ1,hζ0,hζ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hC.isClosed hCD
  have hsupport : tsupport (ζ : M → ℝ) ⊆ D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hζ0 x hn)) hD.isClosed
  refine ⟨ζ,ζ.contMDiff,HasCompactSupport.of_support_subset_isCompact hD
    ((subset_tsupport ζ).trans hsupport),hζ,?_,hζ1,?_⟩
  · intro x hx
    exact hζ0 x (fun hxd => (hDV hxd).2 hx)
  · exact (measure_mono (hsupport.trans (hDV.trans inter_subset_left))).trans_lt hμU


end

section
open scoped ContDiff Manifold Topology ENNReal
open Set Function Manifold MeasureTheory
variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [μ.OuterRegular] [IsFiniteMeasureOnCompacts μ]

theorem exists_uniform_small_area_density {Y : Set P} {K C H : Set M}
    (hY : IsCompact Y) (hK : IsCompact K) (hC : IsCompact C) (hnull : μ C=0)
    (hH : IsClosed H) (hdis : Disjoint C H)
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ a)
    (hapos : ∀ p ∈ Y, ∀ x ∈ K, 0<a (p,x)) {ε : ℝ} (hε : 0<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ), 0<e ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ b ∧
      (∀ p ∈ Y, ∀ x ∈ K, 0<b (p,x)) ∧
      (∃ U : Set M, IsOpen U ∧ C ⊆ U ∧ ∀ p x, x ∈ U → b (p,x)=a (p,x)) ∧
      (∀ p x, x ∈ H → b (p,x)=e) ∧
      (∀ p ∈ Y, (∫ x in K, b (p,x) ∂μ)<ε) := by
  obtain ⟨A₀,hA₀⟩ := (hY.prod hK).bddAbove_image ha.continuous.continuousOn
  let A : ℝ := max A₀ 1
  have hA1 : 1≤A := le_max_right _ _
  have hA : 0<A := lt_of_lt_of_le zero_lt_one hA1
  have hbound : ∀ p ∈ Y, ∀ x ∈ K, a (p,x)≤A := by
    intro p hp x hx
    exact (hA₀ ⟨(p,x),⟨hp,hx⟩,rfl⟩).trans (le_max_left _ _)
  let δ : ℝ := ε/(4*A)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hAδ : A*δ=ε/4 := by dsimp [δ]; field_simp
  obtain ⟨ζ,hζ,hζc,hζrange,hζH,hζC,hζμ⟩ :=
    exists_small_measure_smooth_cutoff (E := E) hC hnull hH hdis hδ
  obtain ⟨U,hU,hCU,hUζ⟩ := mem_nhdsSet_iff_exists.mp hζC
  let e : ℝ := ε/(4*((μ K).toReal+1))
  have hμK : 0≤(μ K).toReal := ENNReal.toReal_nonneg
  have he : 0<e := div_pos hε (by positivity)
  have hem : e*((μ K).toReal+1)=ε/4 := by
    dsimp [e]
    field_simp
  have hesmall : e*(μ K).toReal<ε/4 := by nlinarith
  let b : P × M → ℝ := fun q => ζ q.2*a q+(1-ζ q.2)*e
  have hb : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ b :=
    ((hζ.comp contMDiff_snd).mul ha).add
      ((contMDiff_const.sub (hζ.comp contMDiff_snd)).mul contMDiff_const)
  refine ⟨e,b,he,hb,?_,⟨U,hU,hCU,?_⟩,?_,?_⟩
  · intro p hp x hx
    have hc := hζrange x
    have hap := hapos p hp x hx
    change 0<ζ x*a (p,x)+(1-ζ x)*e
    by_cases hz : ζ x=0
    · simp only [hz,zero_mul,sub_zero,one_mul,zero_add]; exact he
    · have hzp : 0<ζ x := lt_of_le_of_ne hc.1 (Ne.symm hz)
      exact add_pos_of_pos_of_nonneg (mul_pos hzp hap) (mul_nonneg (sub_nonneg.mpr hc.2) he.le)
  · intro p x hx
    change ζ x*a (p,x)+(1-ζ x)*e=a (p,x)
    rw [hUζ hx]; ring
  · intro p x hx
    change ζ x*a (p,x)+(1-ζ x)*e=e
    rw [hζH x hx]; ring
  · intro p hp
    have hζsmall : (∫ x in K, ζ x ∂μ)<δ := by
      apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
      apply lt_of_le_of_lt _ hζμ
      apply le_trans (integral_le_measure (μ := μ.restrict K)
        (s := tsupport ζ) (fun x _ => (hζrange x).2)
        (fun x hx => le_of_eq (image_eq_zero_of_notMem_tsupport hx)))
      exact Measure.restrict_apply_le _ _
    have hζint : IntegrableOn ζ K μ := hζ.continuous.continuousOn.integrableOn_compact hK
    have hbint : IntegrableOn (fun x => b (p,x)) K μ :=
      (hb.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
    have hcint : IntegrableOn (fun _ : M => e) K μ :=
      continuousOn_const.integrableOn_compact hK
    have hle : (∫ x in K, b (p,x) ∂μ) ≤ ∫ x in K, (A*ζ x+e) ∂μ := by
      apply setIntegral_mono_on hbint ((hζint.const_mul A).add hcint) hK.measurableSet
      intro x hx
      have hmul := mul_le_mul_of_nonneg_left (hbound p hp x hx) (hζrange x).1
      dsimp [b]
      nlinarith [(hζrange x).1]
    have heq : (∫ x in K, (A*ζ x+e) ∂μ) = A*(∫ x in K, ζ x ∂μ)+e*(μ K).toReal := by
      rw [integral_add (hζint.const_mul A) hcint,integral_const_mul,setIntegral_const]
      change A*(∫ x in K, ζ x ∂μ)+(μ K).toReal*e = _
      ring
    rw [heq] at hle
    have hh := mul_lt_mul_of_pos_left hζsmall hA
    nlinarith


end

section

open scoped ContDiff Manifold Topology ENNReal
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K : Set M}



theorem exists_uniform_small_area_coefficient
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm Λ c y (1,0) (0,1))
    {Y : Set P} {C H : Set M} (hY : IsCompact Y) (hK : IsCompact K)
    (hC : IsCompact C)
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C)=0)
    (hH : IsClosed H) (hdis : Disjoint C H)
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x)) {ε : ℝ} (hε : 0<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ), 0<e ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
      (∀ p∈Y,∀ x∈K,0<b (p,x)) ∧
      (∃ U : Set M,IsOpen U ∧ C⊆U ∧ ∀ p x,x∈U→b (p,x)=a (p,x)) ∧
      (∀ p x,x∈H→b (p,x)=e) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) := by
  let μ := partitionAreaMeasure B ρ Λ
  let := partitionAreaMeasure_finite B ρ hρ hΛ
  have hn : μ C=0 := partitionAreaMeasure_null B ρ Λ hC.measurableSet hnull
  obtain ⟨e,b,he,hb,hbp,hU,hH',hsmall⟩ :=
    exists_uniform_small_area_density (μ := μ) hY hK hC hn hH hdis ha hapos hε
  refine ⟨e,b,he,hb,hbp,hU,hH',?_⟩
  intro p hp
  have hbs : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => b (p,x)) :=
    hb.comp (contMDiff_const.prodMk contMDiff_id)
  rw [← integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK.measurableSet hbs]
  exact hsmall p hp


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K T Z : Set M}

theorem exists_surface_area_redistribution_bp240_oai
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
    (hZ : IsClosed Z) (hdis : Disjoint (frontier K) Z)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 < chartTwoForm Λ c y (1,0) (0,1))
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    {Y : Set P} (hY : IsCompact Y) (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x))
    {χ : ManifoldTwoForm Plane M} (hχ : SmoothTwoForm χ)
    (hsχ : ∀ x u v,χ x u v= -χ x v u)
    (hpχ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0 ≤ chartTwoForm χ c y (1,0) (0,1))
    (hT : IsCompact T) (hTK : T⊆interior K) (hzχ : ∀ x,x∉T→χ x=0)
    (hmχ : partitionFormMass B ρ χ=1)
    {A : P → ℝ} {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-A p|<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ) (H : P → ℝ) (Ξ : P → ManifoldTwoForm Plane M),
      0<e ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
      ContDiff ℝ ∞ H ∧ SmoothTwoFormFamily Ξ ∧
      (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
        restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)) ∧
      (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
      (∀ p x,x∈K→a (p,x) • Λ x+Ξ p x=b (p,x) • Λ x+H p • χ x) ∧
      (∀ p∈Y,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
        (extChartAt 𝓘(ℝ,Plane) c).symm y∈K→
        0 < chartTwoForm (fun x => a (p,x) • Λ x+Ξ p x) c y (1,0) (0,1)) ∧
      (∀ p x,x∈Z→b (p,x)=e) ∧
      HasInteriorPrimitiveFamily (interior K) Ξ ∧
      (∀ p∈Y,∀ x∈K,0<b (p,x)) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) ∧
      (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→b (p,x)=a (p,x)) := by
  have hpΛ' := fun c y hy => (hpΛ c y hy).le
  obtain ⟨e,b,he,hb,hbp,⟨V,hV,hCV,hba⟩,hbZ,hbm⟩ :=
    exists_uniform_small_area_coefficient B ρ hρ hΛ hpΛ' hY hK (hK.of_isClosed_subset isClosed_frontier
      (by simpa only [hK.isClosed.closure_eq] using (frontier_subset_closure : frontier K ⊆ closure K)))
      hnull hZ hdis ha hapos hε
  obtain ⟨L,d,hL,hLK,hd,hde,hdz⟩ :=
    exists_interior_coefficient_difference hK hV hCV ha hb
      (fun p x hx => (hba p x hx).symm)
  let D : P → ManifoldTwoForm Plane M := fun p x => d (p,x) • Λ x
  have hD : SmoothTwoFormFamily D := (SmoothTwoFormFamily.const hΛ).coefficient_smul hd
  have hsD : ∀ p x u v,D p x u v= -D p x v u := by
    intro p x u v
    change d (p,x)*Λ x u v= -(d (p,x)*Λ x v u)
    rw [hsΛ x u v]; ring
  have hzD : ∀ p x,x∉L→D p x=0 := by
    intro p x hx
    change d (p,x) • Λ x=0
    rw [hdz p x hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    exact zero_mul _
  obtain ⟨hH,hΞ,_,hprimitive⟩ := surface_interior_redistribution hK hc hne hor B ρ hρ
    hD hsD hL hLK hzD hχ hsχ hT hTK hzχ hmχ
  let H : P → ℝ := fun p => partitionFormMass B ρ (D p)
  let Ξ := redistributedDifference B ρ D χ
  have hmass (p : P) : H p=restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
      restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x) :=
    interior_difference_mass B ρ hρ hK.measurableSet hΛ hpΛ' ha hb hd
      (hLK.trans interior_subset) hdz hde p
  have hbound (p : P) (hp : p∈Y) : 0<H p ∧ |H p-A p|<2*ε := by
    have hm0 : 0 ≤ restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x) :=
      restricted_form_mass_nonneg B ρ hρ hK.measurableSet hΛ hpΛ'
        (hb.comp (contMDiff_const.prodMk contMDiff_id)) (fun x hx => (hbp p hp x hx).le)
    have herr' := abs_lt.mp (herr p hp)
    have hh := hmass p
    have hhsmall := hbm p hp
    have hlarge := hA p hp
    constructor
    · linarith
    · exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hformula (p : P) (x : M) (hx : x∈K) :
      a (p,x) • Λ x+Ξ p x=b (p,x) • Λ x+H p • χ x := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change a (p,x)*Λ x u v+(H p*χ x u v-d (p,x)*Λ x u v)=
      b (p,x)*Λ x u v+H p*χ x u v
    rw [hde p x hx]; ring
  refine ⟨e,b,H,Ξ,he,hb,hH,hΞ,hmass,hbound,hformula,?_,hbZ,hprimitive,hbp,hbm,⟨V,hV,hCV,hba⟩⟩
  intro p hp c y hy hk
  have heq : chartTwoForm (fun x => a (p,x) • Λ x+Ξ p x) c y=
      chartTwoForm (fun x => b (p,x) • Λ x+H p • χ x) c y := by
    dsimp only [chartTwoForm]
    rw [hformula p _ hk]
  rw [heq]
  change 0 < chartTwoForm ((fun x => b (p,x) • Λ x)+H p • χ) c y (1,0) (0,1)
  rw [chartTwoForm_add,chartTwoForm_spatial_smul,chartTwoForm_smul]
  change 0<b (p,(extChartAt 𝓘(ℝ,Plane) c).symm y)*chartTwoForm Λ c y (1,0) (0,1)+
    H p*chartTwoForm χ c y (1,0) (0,1)
  exact add_pos_of_pos_of_nonneg (mul_pos (hbp p hp _ hk) (hpΛ c y hy))
    (mul_nonneg (hbound p hp).1.le (hpχ c y hy))



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240_oai.{u_1, u_2} := @OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240_oai.{u_1, u_2}
