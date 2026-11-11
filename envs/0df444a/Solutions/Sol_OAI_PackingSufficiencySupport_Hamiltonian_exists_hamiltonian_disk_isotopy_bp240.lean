-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:02:09.032098+00:00
-- url     : https://prove2.me/submissions/16bc6095-8afe-412c-bd70-9bc42c569fcf

import Mathlib
import Definitions.Def_OAIQ240Bp010

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_TimeSteps
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.parameterSegmentPath_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.timeStep_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.timeSteps_zero
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeStep_preserves_density {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (ρ : ℝ × E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hPDE : ∀ p v w, fderiv ℝ ρ p (1,X p) * B v w +
      ρ p * (B (fderiv ℝ X p (0,v)) w + B v (fderiv ℝ X p (0,w))) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x v w : E) :
    ρ (t+h,timeStep X hX h t x) *
      B (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) =
      ρ (t,x) * B v w := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let A := fderiv ℝ (fixedStep Y hY h) (t,x)
  let D : C(Time,(ℝ × E) →L[ℝ] (ℝ × E)) :=
    ⟨fun s => fderiv ℝ Y (u s),
      ((clockField_smooth X hXs).continuous_fderiv (by simp)).comp u.continuous⟩
  have hA (z : ℝ × E) : A z = constantPath z + h • pathIntegral (pathLinear D (A z)) :=
    congrArg (fun T : (ℝ × E) →L[ℝ] C(Time,ℝ × E) => T z)
      (fixedStep_variation Y hY (clockField_smooth X hXs) hh (t,x))
  have hA0 (z : ℝ × E) : extendPath (A z) 0 = z := by
    have he := congrArg (fun V : C(Time,ℝ × E) => V ⟨0,by simp⟩) (hA z)
    exact (extendPath_coe (A z) ⟨0,by simp⟩).trans (by simpa using he)
  let V : E → ℝ → E := fun z s => (extendPath (A (0,z)) s).2
  have hhor (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      extendPath (A (0,z)) s = (0,V z s) := by
    apply Prod.ext
    · rw [show extendPath (A (0,z)) s = A (0,z) ⟨s,hs⟩ from extendPath_coe _ ⟨s,hs⟩]
      exact fixedStep_variation_clock X hX hXs hh (t,x) z ⟨s,hs⟩
    · rfl
  have hVd (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (V z) (h • fderiv ℝ X (extendPath u s) (0,V z s)) (Icc (0:ℝ) 1) s := by
    have hd := (path_equation_derivative _ _ (0,z) h (hA (0,z)) hs).snd
    change HasDerivWithinAt (V z)
      (h • (fderiv ℝ Y (extendPath u s) (extendPath (A (0,z)) s)).2) _ s at hd
    rw [hhor z s hs,clockField_fderiv hXs] at hd
    exact hd
  let F : ℝ → ℝ := fun s => ρ (extendPath u s) * B (V v s) (V w s)
  have hFc : Continuous F := (hρ.continuous.comp (extendPath u).continuous).mul
    ((B.continuous.comp (extendPath (A (0,v))).continuous.snd).clm_apply
      (extendPath (A (0,w))).continuous.snd)
  have hFd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) : HasDerivAt F 0 s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
    have hUd := fixedStep_derivative Y hY hh (t,x) hs'
    have hρd := ((hρ.differentiable (by simp) (extendPath u s)).hasFDerivAt).comp_hasDerivWithinAt s hUd
    have hBd := ContinuousLinearMap.hasDerivWithinAt_of_bilinear (B := B)
      (hVd v s hs') (hVd w s hs')
    have hd := hρd.mul hBd
    have hz : fderiv ℝ ρ (extendPath u s) (h • Y (extendPath u s)) *
          B (V v s) (V w s) + ρ (extendPath u s) *
          (B (V v s) (h • fderiv ℝ X (extendPath u s) (0,V w s)) +
            B (h • fderiv ℝ X (extendPath u s) (0,V v s)) (V w s)) = 0 := by
      simp only [map_smul,smul_apply, smul_eq_mul]
      have he := hPDE (extendPath u s) (V v s) (V w s)
      change fderiv ℝ ρ (extendPath u s) (Y (extendPath u s)) * B (V v s) (V w s) +
        ρ (extendPath u s) * _ = 0 at he
      linear_combination h * he
    have hd0 : HasDerivWithinAt F 0 (Icc (0:ℝ) 1) s := hd.congr_deriv hz
    exact hd0.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hFc.continuousOn hFd (intervalIntegrable_const (c := (0:ℝ)))
  have hend : F 1 = F 0 := sub_eq_zero.mp (by simpa using hi.symm)
  have hzero : F 0 = ρ (t,x) * B v w := by
    change ρ (extendPath u 0) * B (extendPath (A (0,v)) 0).2 (extendPath (A (0,w)) 0).2 = _
    rw [hA0,hA0,show extendPath u 0 = (t,x) from
      (extendPath_coe u ⟨0,by simp⟩).trans (fixedStep_initial Y hY hh (t,x))]
  have hfinal : extendPath u 1 = (t+h,timeStep X hX h t x) := by
    rw [show extendPath u 1 = u ⟨1,by simp⟩ from extendPath_coe u ⟨1,by simp⟩]
    exact Prod.ext (stepEndpoint_clock X hX hh (t,x)) rfl
  have hfinalV (z : E) : V z 1 = fderiv ℝ (timeStep X hX h t) x z := by
    rw [timeStep_fderiv X hX hXs hh, stepEndpoint_fderiv Y hY (clockField_smooth X hXs) hh]
    exact congrArg Prod.snd (extendPath_coe (A (0,z)) ⟨1,by simp⟩)
  have hone : F 1 = ρ (t+h,timeStep X hX h t x) *
      B (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) := by
    change ρ (extendPath u 1) * B (V v 1) (V w 1) = _
    rw [hfinal,hfinalV,hfinalV]
  exact hone.symm.trans (hend.trans hzero)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeSteps_preserves_density {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (ρ : ℝ × E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hPDE : ∀ p v w, fderiv ℝ ρ p (1,X p) * B v w +
      ρ p * (B (fderiv ℝ X p (0,v)) w + B v (fderiv ℝ X p (0,w))) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x v w : E) :
    ρ (t+N*h,timeSteps X hX hXs hh t N x) *
      B (fderiv ℝ (timeSteps X hX hXs hh t N) x v)
        (fderiv ℝ (timeSteps X hX hXs hh t N) x w) = ρ (t,x) * B v w := by
  induction N with
  | zero => simp [timeSteps]
  | succ N ih =>
    let F := timeSteps X hX hXs hh t N
    let G := timeStep X hX h (t+N*h)
    have hF : Differentiable ℝ F := (timeSteps_smooth X hX hXs hh t N).1.differentiable (by simp)
    have hG : Differentiable ℝ G := (timeStep_smooth X hX hXs hh (t+N*h)).differentiable (by simp)
    change ρ (t+(N+1:ℕ)*h,G (F x)) *
      B (fderiv ℝ (G ∘ F) x v) (fderiv ℝ (G ∘ F) x w) = _
    rw [fderiv_comp x (hG (F x)) (hF x)]
    have ht : t + (N+1:ℕ)*h = (t+N*h)+h := by push_cast <;> ring
    rw [ht]
    exact (timeStep_preserves_density X hX hXs ρ hρ B hPDE hh (t+N*h) (F x)
      (fderiv ℝ F x v) (fderiv ℝ F x w)).trans ih

end PackingSufficiencySupport.Hamiltonian

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
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.coordinateForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

theorem planarArea_trace_identity (A : Plane →L[ℝ] Plane) (v w : Plane) :
    planarArea (A v) w + planarArea v (A w) =
      ((A (1,0)).1+(A (0,1)).2) * planarArea v w := by
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hw : w = w.1 • ((1:ℝ),(0:ℝ)) + w.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have ha : A v = v.1 • A (1,0) + v.2 • A (0,1) := by conv_lhs => rw [hv]; rw [map_add,map_smul,map_smul]
  have hb : A w = w.1 • A (1,0) + w.2 • A (0,1) := by conv_lhs => rw [hw]; rw [map_add,map_smul,map_smul]
  simp only [planarArea_apply,ha,hb,Prod.fst_add,Prod.snd_add,Prod.smul_def,smul_eq_mul]
  ring

theorem plane_deriv_first {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun x => F (x,p.2)) p.1 = fderiv ℝ F p (1,0) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem plane_deriv_second {F : Plane → ℝ} (hF : Differentiable ℝ F) (p : Plane) :
    deriv (fun t => F (p.1,t)) p.2 = fderiv ℝ F p (0,1) := by
  exact ((hF p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem hasDerivAt_horizontal_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × Plane → E} (hF : Differentiable ℝ F) (p : ℝ × Plane) :
    HasDerivAt (fun x => F (p.1,(x,p.2.2))) (fderiv ℝ F p (0,(1,0))) p.2.1 :=
  (hF p).hasFDerivAt.comp_hasDerivAt p.2.1 ((hasDerivAt_const p.2.1 p.1).prodMk
    ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2)))

theorem hasDerivAt_horizontal_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × Plane → E} (hF : Differentiable ℝ F) (p : ℝ × Plane) :
    HasDerivAt (fun y => F (p.1,(p.2.1,y))) (fderiv ℝ F p (0,(0,1))) p.2.2 :=
  (hF p).hasFDerivAt.comp_hasDerivAt p.2.2 ((hasDerivAt_const p.2.2 p.1).prodMk
    ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2)))

theorem bilinear_skew_plane (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (u v : Plane) :
    B u v - B v u = (B (1,0) (0,1)-B (0,1) (1,0))*planarArea u v := by
  have hu : u = u.1 • ((1:ℝ),(0:ℝ)) + u.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  conv_lhs => rw [hu,hv]
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,planarArea_apply]
  ring

theorem pullbackForm_smooth {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) :
    ContDiff ℝ ∞ (pullbackForm phi alpha) :=
  (ha.comp hp).clm_comp (hp.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem pullbackForm_curl {phi : Plane → Plane} (hp : ContDiff ℝ ∞ phi)
    {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha) (p : Plane) :
    planarCurl (pullbackForm phi alpha) p = planarCurl alpha (phi p) *
      planarArea (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1)) := by
  have hd := (((ha.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (phi p)).hasFDerivAt.comp p
    (((hp.differentiable (by simp)) p).hasFDerivAt)).clm_comp
      (((hp.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : ℕ∞ω)+1 ≤ ∞)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt)
  have hs := (hp.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  dsimp only [Function.comp_def] at hd
  unfold planarCurl pullbackForm
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  rw [hs.eq (1,0) (0,1)]
  have hb := bilinear_skew_plane (fderiv ℝ alpha (phi p))
    (fderiv ℝ phi p (1,0)) (fderiv ℝ phi p (0,1))
  linear_combination hb

theorem integral_curl_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (a b : Plane) (hab : a ≤ b) :
    (∫ p in Icc a b, planarCurl alpha p) =
      ((∫ t in a.2..b.2, alpha (b.1,t) (0,1)) - ∫ t in a.2..b.2, alpha (a.1,t) (0,1)) -
      ((∫ r in a.1..b.1, alpha (r,b.2) (1,0)) - ∫ r in a.1..b.1, alpha (r,a.2) (1,0)) := by
  let F : Plane → ℝ := fun p => alpha p (0,1)
  let G : Plane → ℝ := fun p => -alpha p (1,0)
  have hF : ContDiff ℝ ∞ F := ha.clm_apply contDiff_const
  have hG : ContDiff ℝ ∞ G := (ha.clm_apply contDiff_const).neg
  have hFd (p : Plane) : fderiv ℝ F p =
      (ContinuousLinearMap.apply ℝ ℝ (0,1)).comp (fderiv ℝ alpha p) :=
    ((ContinuousLinearMap.apply ℝ ℝ (0,1) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).fderiv
  have hGd (p : Plane) : fderiv ℝ G p =
      -((ContinuousLinearMap.apply ℝ ℝ (1,0)).comp (fderiv ℝ alpha p)) :=
    (((ContinuousLinearMap.apply ℝ ℝ (1,0) : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
      ((ha.differentiable (by simp)) p).hasFDerivAt).neg).fderiv
  have he (p : Plane) : fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1) = planarCurl alpha p := by
    rw [hFd,hGd]
    rfl
  have hi : IntegrableOn (fun p => fderiv ℝ F p (1,0)+fderiv ℝ G p (0,1)) (Icc a b) :=
    (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).add
      ((hG.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have hg := integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G
    (fderiv ℝ F) (fderiv ℝ G) a b hab hF.continuous.continuousOn hG.continuous.continuousOn
    (fun p _ => ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt)
    (fun p _ => ((hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt) hi
  simp_rw [he] at hg
  simp only [F,G,intervalIntegral.integral_neg] at hg
  linear_combination hg

theorem polar_deriv_first (p : Plane) :
    fderiv ℝ polarCoord.symm p (1,0) = (Real.cos p.2,Real.sin p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_deriv_second (p : Plane) :
    fderiv ℝ polarCoord.symm p (0,1) = (-p.1*Real.sin p.2,p.1*Real.cos p.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap]

theorem polar_area (p : Plane) :
    planarArea (fderiv ℝ polarCoord.symm p (1,0)) (fderiv ℝ polarCoord.symm p (0,1)) = p.1 := by
  rw [polar_deriv_first,polar_deriv_second,planarArea_apply]
  have ht := Real.cos_sq_add_sin_sq p.2
  dsimp
  linear_combination p.1 * ht

theorem integral_curl_polar_rectangle {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 ≤ R) :
    (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*planarCurl alpha (polarCoord.symm p)) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  let eta := pullbackForm polarCoord.symm alpha
  have he (p : Plane) : planarCurl eta p = p.1*planarCurl alpha (polarCoord.symm p) := by
    rw [pullbackForm_curl polar_smooth ha,polar_area,mul_comm]
  have h := integral_curl_rectangle (pullbackForm_smooth polar_smooth ha)
    ((0:ℝ),-Real.pi) (R,Real.pi) ⟨hR,by linarith [Real.pi_pos]⟩
  change (∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), planarCurl eta p) = _ at h
  simp_rw [he] at h
  have hside (r : ℝ) : eta (r,Real.pi) (1,0) = eta (r,-Real.pi) (1,0) := by
    simp [eta,pullbackForm,polar_deriv_first,polarCoord_symm_apply]
  have hin (t : ℝ) : eta (0,t) (0,1) = 0 := by
    simp [eta,pullbackForm,polar_deriv_second,Prod.mk_zero_zero]
  have hout (t : ℝ) : eta (R,t) (0,1) =
      alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
    simp [eta,pullbackForm,polar_deriv_second]
  change _ = ((∫ t in -Real.pi..Real.pi, eta (R,t) (0,1)) -
    ∫ t in -Real.pi..Real.pi, eta (0,t) (0,1)) -
    ((∫ r in (0:ℝ)..R, eta (r,Real.pi) (1,0)) - ∫ r in (0:ℝ)..R, eta (r,-Real.pi) (1,0)) at h
  simp_rw [hside,hin,hout] at h
  simpa using h

theorem polar_mem_roundDisk {R : ℝ} (hR : 0 < R) {p : Plane} (hp : 0 < p.1) :
    polarCoord.symm p ∈ roundDisk R ↔ p.1 < R := by
  have hn : (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 = p.1^2 := by
    simp only [polarCoord_symm_apply]
    linear_combination p.1^2 * Real.cos_sq_add_sin_sq p.2
  change (polarCoord.symm p).1^2+(polarCoord.symm p).2^2 < R^2 ↔ _
  rw [hn]
  constructor <;> intro h <;> nlinarith

theorem integral_roundDisk_polar (f : Plane → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, f p) =
      ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
  have hm : MeasurableSet (roundDisk R) :=
    (isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  let S : Set Plane := {p | p.1 < R}
  have hS : MeasurableSet S := (isOpen_lt continuous_fst continuous_const).measurableSet
  have he (p : Plane) (hp : p ∈ polarCoord.target) :
      p.1 * (roundDisk R).indicator f (polarCoord.symm p) =
        S.indicator (fun p => p.1*f (polarCoord.symm p)) p := by
    have hi := polar_mem_roundDisk hR hp.1
    by_cases ht : p.1 < R
    · simp only [indicator_of_mem (hi.mpr ht),indicator_of_mem (show p ∈ S from ht)]
    · simp only [indicator_of_notMem (mt hi.mp ht),indicator_of_notMem (show p ∉ S from ht),mul_zero]
  have hinter : polarCoord.target ∩ S = Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target,mem_inter_iff,mem_prod,mem_Ioi,mem_Ioo,S,mem_ofPred_eq]
    tauto
  calc
    (∫ p in roundDisk R, f p) = ∫ p in polarCoord.target,
        p.1 * (roundDisk R).indicator f (polarCoord.symm p) := by
      rw [← integral_indicator hm]
      exact (integral_comp_polarCoord_symm ((roundDisk R).indicator f)).symm
    _ = ∫ p in polarCoord.target, S.indicator (fun p => p.1*f (polarCoord.symm p)) p :=
      setIntegral_congr_fun polarCoord.open_target.measurableSet he
    _ = ∫ p in Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, p.1*f (polarCoord.symm p) := by
      rw [setIntegral_indicator hS,hinter]
    _ = ∫ p in Icc ((0:ℝ),-Real.pi) (R,Real.pi), p.1*f (polarCoord.symm p) := by
      apply setIntegral_congr_set
      rw [Icc_prod_eq]
      exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioo_ae_eq_Icc MeasureTheory.Ioo_ae_eq_Icc

theorem integral_curl_roundDisk {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {R : ℝ} (hR : 0 < R) :
    (∫ p in roundDisk R, planarCurl alpha p) =
      ∫ t in -Real.pi..Real.pi,
        alpha (polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) := by
  rw [integral_roundDisk_polar _ hR]
  exact integral_curl_polar_rectangle ha hR.le

theorem periodicPrimitive_hasDerivAt {a : ℝ → ℝ} (ha : Continuous a) (t : ℝ) :
    HasDerivAt (periodicPrimitive a) (a t) t := by
  exact intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt

theorem periodicPrimitive_periodic {a : ℝ → ℝ} (ha : Continuous a)
    (hp : Periodic a (2*Real.pi)) (hz : (∫ s in -Real.pi..Real.pi, a s) = 0) :
    Periodic (periodicPrimitive a) (2*Real.pi) := by
  intro t
  unfold periodicPrimitive
  rw [hp.intervalIntegral_add_eq_add _ _ (fun s t => ha.intervalIntegrable s t)]
  convert add_zero (∫ s in -Real.pi..t, a s) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem periodic_arg_neg {h : ℝ → ℝ} (hp : Periodic h (2*Real.pi)) {z : ℂ}
    (hz : z ≠ 0) : h z.arg = h ((-z).arg+Real.pi) := by
  by_cases hi : 0 < z.im ∨ z.im = 0 ∧ z.re < 0
  · rw [Complex.arg_neg_eq_arg_sub_pi_iff.mpr hi,sub_add_cancel]
  · have hj : z.im < 0 ∨ z.im = 0 ∧ 0 < z.re := by
      by_cases him : z.im = 0
      · right
        refine ⟨him,?_⟩
        have hn : z.re ≠ 0 := fun hn => hz (Complex.ext hn him)
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact False.elim (hi (Or.inr ⟨him,hn⟩))
        · exact hn
      · exact Or.inl (lt_of_le_of_ne (le_of_not_gt (fun h => hi (Or.inl h))) him)
    rw [Complex.arg_neg_eq_arg_add_pi_iff.mpr hj]
    convert (hp z.arg).symm using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

theorem contDiffAt_arg_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have h := (Complex.contDiffAt_log (n := ∞) hz).restrict_scalars ℝ
  have ht : ContDiffAt ℝ ∞ (fun x : ℂ => (Complex.log x).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z h
  simpa only [Complex.log_im] using ht

theorem periodic_arg_polar {h : ℝ → ℝ} (hp : Periodic h (2*Real.pi))
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    h (Complex.arg (R*(Real.cos t+Real.sin t*Complex.I))) = h t := by
  have he := Complex.arg_mul_cos_add_sin_mul_I_sub hR t
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  have he' : Complex.arg (R*(Real.cos t+Real.sin t*Complex.I)) =
      t + (⌊(Real.pi-t)/(2*Real.pi)⌋ : ℤ) • (2*Real.pi) := by
    rw [zsmul_eq_mul]
    linarith
  rw [he']
  exact hp.zsmul _ t

theorem angularExtension_zero {R delta : ℝ} (hd : 0 < delta) (h : ℝ → ℝ) (p : Plane)
    (hp : delta ≤ |radiusSq p-R^2|) : angularExtension R delta hd h p = 0 := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  change b (radiusSq p) * h (Complex.arg (Complex.equivRealProdCLM.symm p)) = 0
  have hb : b (radiusSq p) = 0 := b.zero_of_le_dist (by simpa only [Real.dist_eq] using hp)
  rw [hb,zero_mul]

theorem angularExtension_polar {R delta : ℝ} (hR : 0 < R) (hd : 0 < delta)
    {h : ℝ → ℝ} (hp : Periodic h (2*Real.pi)) (t : ℝ) :
    angularExtension R delta hd h (polarCoord.symm (R,t)) = h t := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  change b (radiusSq (polarCoord.symm (R,t))) * _ = h t
  have hb : b (R^2) = 1 := b.one_of_mem_closedBall (by simp only [Metric.mem_closedBall,dist_self]; exact le_of_lt b.rIn_pos)
  rw [radiusSq_polar,hb,one_mul]
  have he : Complex.equivRealProdCLM.symm (polarCoord.symm (R,t)) =
      R*(Real.cos t+Real.sin t*Complex.I) := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply,polarCoord_symm_apply]
  rw [he]
  exact periodic_arg_polar hp hR t

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_CircleCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.parameterSegmentPath_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.timeStep_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Metric
open scoped Classical
open Function MeasureTheory

theorem circlePullback_periodic (alpha : Plane → Plane →L[ℝ] ℝ) (R : ℝ) :
    Periodic (circlePullback alpha R) (2*Real.pi) := by
  intro t
  simp only [circlePullback,polarCoord_symm_apply,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem polar_surjective_circle {R : ℝ} (hR : 0 < R) {p : Plane}
    (hp : radiusSq p = R^2) : ∃ t : ℝ, polarCoord.symm (R,t) = p := by
  let z := Complex.equivRealProdCLM.symm p
  have hn : ‖z‖ = R := by
    have hsq : ‖z‖^2 = radiusSq p := by
      rw [Complex.sq_norm]
      simp [z,Complex.normSq_apply,radiusSq,Complex.equivRealProdCLM_symm_apply,pow_two]
    nlinarith [norm_nonneg z]
  refine ⟨z.arg,?_⟩
  have hx := Complex.norm_mul_cos_arg z
  have hy := Complex.norm_mul_sin_arg z
  rw [hn] at hx hy
  exact Prod.ext hx hy

theorem fderiv_zero_outside_collar {H : Plane → ℝ} {R delta : ℝ}
    (hH : ∀ p, delta ≤ |radiusSq p-R^2| → H p = 0) {p : Plane}
    (hp : delta < |radiusSq p-R^2|) : fderiv ℝ H p = 0 := by
  have he : H =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const ((radiusSq_smooth.continuous.sub continuous_const).abs)).mem_nhds hp]
      with x hx
    exact hH x hx.le
  rw [he.fderiv_eq]
  simp only [fderiv_const_apply]

theorem exists_positive_lt_finite {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d < a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨d,hd,hds⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    refine ⟨min d (a i/2),lt_min hd (half_pos (ha i (Finset.mem_insert_self _ _))),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (half_lt_self (ha j (Finset.mem_insert_self _ _)))
    · exact (min_le_left _ _).trans_lt (hds j hj)

theorem planarCurl_sub_differential {alpha : Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) (p : Plane) :
    planarCurl (fun p => alpha p - fderiv ℝ H p) p = planarCurl alpha p := by
  have hs := (hH.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  unfold planarCurl
  rw [fderiv_fun_sub ((ha.differentiable (by simp)) p)
    (((hH.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (∞ : ℕ∞ω)+1 ≤ ∞)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p)]
  simp only [sub_apply]
  rw [hs.eq (1,0) (0,1)]
  ring

theorem exists_disjoint_radial_collars {ι : Type*} [Fintype ι]
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R) (i : ι) :
    ∃ d : ℝ, 0 < d ∧ d < (R i)^2 ∧ ∀ j, j ≠ i → d < |(R j)^2-(R i)^2| := by
  classical
  let a : ι → ℝ := fun j => if j = i then (R i)^2 else |(R j)^2-(R i)^2|
  have ha0 (j : ι) : 0 < a j := by
    dsimp [a]
    split_ifs with hj
    · exact sq_pos_of_pos (hR i)
    · apply abs_pos.mpr
      intro he
      have heq : R j = R i := by nlinarith [hR i,hR j]
      exact hj (hRi heq)
  obtain ⟨d,hd,hda⟩ := exists_positive_lt_finite Finset.univ a (fun j _ => ha0 j)
  refine ⟨d,hd,?_,?_⟩
  · simpa [a] using hda i (Finset.mem_univ i)
  · intro j hj
    simpa [a,hj] using hda j (Finset.mem_univ j)

theorem exists_sphere_distance_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (hR : 0 < R) (v : E) (hv : ‖v‖ = R) (x : E) :
    ∃ y : E, ‖y‖ = R ∧ dist x y ≤ |‖x‖^2-R^2| / R := by
  by_cases hx : x = 0
  · subst x
    refine ⟨v,hv,?_⟩
    simp only [dist_zero_left,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_sub,
      abs_neg,abs_of_nonneg (sq_nonneg R),hv]
    rw [pow_two,mul_div_cancel_right₀ _ hR.ne']
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (R/‖x‖) • x
    have hy : ‖y‖ = R := by
      simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hR hx0)]
      exact div_mul_cancel₀ R hx0.ne'
    refine ⟨y,hy,?_⟩
    have hd : dist x y = |‖x‖-R| := by
      rw [dist_eq_norm,show x-y = (1-R/‖x‖) • x by dsimp [y]; rw [sub_smul,one_smul]]
      rw [norm_smul,Real.norm_eq_abs]
      calc
        |1-R/‖x‖| *‖x‖ = |(1-R/‖x‖)*‖x‖| := by rw [abs_mul,abs_of_pos hx0]
        _ = |‖x‖-R| := by congr 1; field_simp
    rw [hd]
    apply (le_div_iff₀ hR).mpr
    have he : |‖x‖^2-R^2| = |‖x‖-R| *(‖x‖+R) := by
      rw [show ‖x‖^2-R^2 = (‖x‖-R)*(‖x‖+R) by ring,abs_mul,
        abs_of_pos (add_pos hx0 hR)]
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx0.le) (abs_nonneg _)

theorem lipschitz_zero_on_sphere_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {L : ℝ≥0} {f : E → F}
    (hf : LipschitzWith L f) {R : ℝ} (hR : 0 < R) (v : E) (hv : ‖v‖ = R)
    (hz : ∀ x, ‖x‖ = R → f x = 0) (x : E) :
    ‖f x‖ ≤ ((L : ℝ)/R)*|‖x‖^2-R^2| := by
  obtain ⟨y,hy,hxy⟩ := exists_sphere_distance_bound hR v hv x
  have h := hf.dist_le_mul x y
  rw [hz y hy,dist_zero_right] at h
  calc
    ‖f x‖ ≤ (L:ℝ)*dist x y := h
    _ ≤ (L:ℝ)*(|‖x‖^2-R^2|/R) := mul_le_mul_of_nonneg_left hxy L.coe_nonneg
    _ = _ := by ring

theorem radialDrift_smooth {X : ℝ × Plane → Plane} (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (radialDrift X) := by unfold radialDrift; fun_prop

theorem radialDrift_compact {X : ℝ × Plane → Plane} (hc : HasCompactSupport X) :
    HasCompactSupport (radialDrift X) := by
  apply hc.mono ?_
  intro p hp
  contrapose! hp
  simpa only [mem_support,not_not] using (show radialDrift X p = 0 by
    simp [radialDrift,show X p = 0 from notMem_support.mp hp])

theorem complex_normSq_plane (p : Plane) :
    ‖Complex.equivRealProdCLM.symm p‖^2 = radiusSq p := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,radiusSq,Complex.equivRealProdCLM_symm_apply,pow_two]

theorem exists_radialDrift_bound {X : ℝ × Plane → Plane} (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, |radialDrift X (t,x)| ≤ C*|radiusSq x-R^2| := by
  let e : (ℝ × ℂ) ≃L[ℝ] (ℝ × Plane) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr Complex.equivRealProdCLM
  let D : ℝ × ℂ → ℝ := fun p => radialDrift X (e p)
  have hDs : ContDiff ℝ ∞ D := (radialDrift_smooth hX).comp e.contDiff
  have hDc : HasCompactSupport D := (radialDrift_compact hc).comp_homeomorph e.toHomeomorph
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hDc hDs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  refine ⟨(L:ℝ)/R,div_nonneg L.coe_nonneg hR.le,?_⟩
  intro t x
  have hLt : LipschitzWith L (fun z : ℂ => D (t,z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist z w)] using hL.dist_le_mul (t,z) (t,w)
  have hz (z : ℂ) (hz : ‖z‖ = R) : D (t,z) = 0 := by
    apply htan t (Complex.equivRealProdCLM z)
    rw [← complex_normSq_plane,ContinuousLinearEquiv.symm_apply_apply,hz]
  have h := lipschitz_zero_on_sphere_bound hLt hR (R:ℂ)
    (by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]) hz
    (Complex.equivRealProdCLM.symm x)
  simpa only [D,e,ContinuousLinearEquiv.prodCongr_apply,ContinuousLinearEquiv.refl_apply,
    ContinuousLinearEquiv.apply_symm_apply,Real.norm_eq_abs,complex_normSq_plane] using h

theorem trajectory_preserves_circle {X : ℝ × Plane → Plane} (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {u : ℝ → Plane} {a b c h : ℝ} (hu : ContinuousOn u (Icc a b))
    (hud : ∀ s ∈ Ico a b, HasDerivWithinAt u (h • X (c+h*s,u s)) (Ici s) s)
    (ha : radiusSq (u a) = R^2) :
    ∀ s ∈ Icc a b, radiusSq (u s) = R^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_radialDrift_bound hX hc hR htan
  let g : ℝ → ℝ := fun s => radiusSq (u s)-R^2
  let g' : ℝ → ℝ := fun s => h*radialDrift X (c+h*s,u s)
  have hgc : ContinuousOn g (Icc a b) := (radiusSq_smooth.continuous.comp_continuousOn hu).sub continuousOn_const
  have hgd (s : ℝ) (hs : s ∈ Ico a b) : HasDerivWithinAt g (g' s) (Ici s) s := by
    have hd1 : HasDerivWithinAt (fun s => (u s).1) (h*(X (c+h*s,u s)).1) (Ici s) s :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hud s hs)
    have hd2 : HasDerivWithinAt (fun s => (u s).2) (h*(X (c+h*s,u s)).2) (Ici s) s :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hud s hs)
    have hd := ((hd1.pow 2).add (hd2.pow 2)).sub_const (R^2)
    exact hd.congr_deriv (by simp only [g',radialDrift] <;> ring)
  have hgb (s : ℝ) (_hs : s ∈ Ico a b) : ‖g' s‖ ≤ (|h| *C)*‖g s‖ := by
    simp only [g',g,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hbound (c+h*s) (u s)) (abs_nonneg h)).trans_eq (by ring)
  have he := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hgc hgd
    (show g a = 0 from sub_eq_zero.mpr ha) hgb
  intro s hs
  exact sub_eq_zero.mp (he s hs)

theorem timeStep_preserves_circle {L : ℝ≥0} (X : C(ℝ × Plane,Plane))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) {x : Plane} (hx : radiusSq x = R^2) :
    radiusSq (timeStep X hX h t x) = R^2 := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let v : ℝ → Plane := fun s => (extendPath u s).2
  have hc : ContinuousOn v (Icc (0:ℝ) 1) := (extendPath u).continuous.snd.continuousOn
  have hd (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt v (h • X (t+h*s,v s)) (Ici s) s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.le⟩
    have he : (extendPath u s).1 = t+h*s := by
      rw [show extendPath u s = u ⟨s,hs'⟩ from extendPath_coe u ⟨s,hs'⟩]
      exact fixedStep_clock X hX hh (t,x) ⟨s,hs'⟩
    have hd0 : HasDerivWithinAt v (h • X (extendPath u s)) (Icc (0:ℝ) 1) s :=
      (ContinuousLinearMap.snd ℝ ℝ Plane).hasFDerivAt.comp_hasDerivWithinAt s
        (fixedStep_derivative Y hY hh (t,x) hs')
    have hd1 := hd0.mono_of_mem_nhdsWithin (s := Ici s) (by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2),
        (self_mem_nhdsWithin : Ici s ∈ 𝓝[Ici s] s)] with q hq hsq
      exact ⟨hs.1.trans hsq,hq.le⟩)
    change HasDerivWithinAt v (h • X (extendPath u s)) (Ici s) s at hd1
    have hp : extendPath u s = (t+h*s,v s) := Prod.ext he rfl
    rwa [hp] at hd1
  have hv0 : v 0 = x := by
    change (extendPath u 0).2 = x
    rw [show extendPath u 0 = u ⟨0,by simp⟩ from extendPath_coe u ⟨0,by simp⟩]
    change (fixedStep Y hY h (t,x) ⟨0,by simp⟩).2 = x
    rw [fixedStep_initial Y hY hh]
  have he := trajectory_preserves_circle hXs hXc hR htan hc hd
    (show radiusSq (v 0) = R^2 by rw [hv0]; exact hx) 1 (by simp)
  change radiusSq ((extendPath u 1).2) = R^2 at he
  rw [show extendPath u 1 = u ⟨1,by simp⟩ from extendPath_coe u ⟨1,by simp⟩] at he
  exact he

theorem timeStep_preserves_circle_iff {L : ℝ≥0} (X : C(ℝ × Plane,Plane))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x : Plane) :
    radiusSq (timeStep X hX h t x) = R^2 ↔ radiusSq x = R^2 := by
  constructor
  · intro hx
    have he := timeStep_preserves_circle X hX hXs hXc hR htan
      (h := -h) (by simpa using hh) (t+h) hx
    rwa [timeStep_inverse X hX hh t x] at he
  · exact timeStep_preserves_circle X hX hXs hXc hR htan hh t

theorem timeSteps_preserves_circle_iff {L : ℝ≥0} (X : C(ℝ × Plane,Plane))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {R : ℝ} (hR : 0 < R)
    (htan : ∀ t x, radiusSq x = R^2 → radialDrift X (t,x) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x : Plane) :
    radiusSq (timeSteps X hX hXs hh t N x) = R^2 ↔ radiusSq x = R^2 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change radiusSq (timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N x)) = R^2 ↔ _
    rw [timeStep_preserves_circle_iff X hX hXs hXc hR htan hh,ih]

theorem coordinateForm_smooth {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (coordinateForm U V) :=
  (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem form_eval_fderiv {alpha : Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (p v w : Plane) : fderiv ℝ (fun q => alpha q w) p v = fderiv ℝ alpha p v w := by
  have he := ((ContinuousLinearMap.apply ℝ ℝ w : (Plane →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp p
    ((ha.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt).fderiv
  exact congrArg (fun D : Plane →L[ℝ] ℝ => D v) he

theorem coordinateForm_curl {U V : Plane → ℝ} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) (p : Plane) :
    planarCurl (coordinateForm U V) p =
      deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2 := by
  rw [plane_deriv_first (hV.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    plane_deriv_second (hU.differentiable (by simp))]
  unfold planarCurl
  rw [← form_eval_fderiv (coordinateForm_smooth hU hV),
    ← form_eval_fderiv (coordinateForm_smooth hU hV)]
  simp only [coordinateForm_apply,mul_zero,mul_one,zero_add,add_zero]

theorem closedRoundDisk_isCompact (R : ℝ) : IsCompact (closedRoundDisk R) := by
  apply (isCompact_closedBall (0 : Plane) (R^2+1)).of_isClosed_subset
    (isClosed_le radiusSq_smooth.continuous continuous_const)
  intro p hp
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,
    Real.norm_eq_abs,Real.norm_eq_abs]
  change p.1^2+p.2^2 ≤ R^2 at hp
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg p.2,sq_nonneg (p.1-1),sq_nonneg (p.1+1)]
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg p.1,sq_nonneg (p.2-1),sq_nonneg (p.2+1)]

theorem radiusSq_eq_zero_of_isLocalMax {p : Plane} (hp : IsLocalMax radiusSq p) :
    p = 0 := by
  have h1 : IsLocalMax (fun x : ℝ => x^2+p.2^2) p.1 :=
    hp.comp_continuous (g := fun x : ℝ => (x,p.2))
      (continuousAt_id.prodMk continuousAt_const)
  have h2 : IsLocalMax (fun y : ℝ => p.1^2+y^2) p.2 :=
    hp.comp_continuous (g := fun y : ℝ => (p.1,y))
      (continuousAt_const.prodMk continuousAt_id)
  have hd1 : HasDerivAt (fun x : ℝ => x^2+p.2^2) (2*p.1) p.1 := by
    simpa using (hasDerivAt_pow 2 p.1).add_const (p.2^2)
  have hd2 : HasDerivAt (fun y : ℝ => p.1^2+y^2) (2*p.2) p.2 := by
    simpa using (hasDerivAt_pow 2 p.2).const_add (p.1^2)
  have he1 : 2*p.1 = 0 := hd1.deriv.symm.trans h1.deriv_eq_zero
  have he2 : 2*p.2 = 0 := hd2.deriv.symm.trans h2.deriv_eq_zero
  apply Prod.ext <;> dsimp <;> linarith

theorem homeomorph_mapsTo_closedRoundDisk (Φ : Plane ≃ₜ Plane) (R : ℝ)
    (hcircle : ∀ p, radiusSq p = R^2 → radiusSq (Φ p) = R^2) :
    MapsTo Φ (closedRoundDisk R) (closedRoundDisk R) := by
  have hne : (closedRoundDisk R).Nonempty := ⟨0,by simp [closedRoundDisk,radiusSq,sq_nonneg]⟩
  obtain ⟨p,hp,hm⟩ := (closedRoundDisk_isCompact R).exists_isMaxOn hne
    (radiusSq_smooth.continuous.comp Φ.continuous).continuousOn
  have hbound : radiusSq (Φ p) ≤ R^2 := by
    by_cases he : radiusSq p = R^2
    · exact (hcircle p he).le
    · have hlt : radiusSq p < R^2 := lt_of_le_of_ne hp he
      have hnhds : closedRoundDisk R ∈ 𝓝 p :=
        Filter.mem_of_superset ((isOpen_lt radiusSq_smooth.continuous continuous_const).mem_nhds hlt)
          (fun q (hq : radiusSq q < R^2) => (show q ∈ closedRoundDisk R from hq.le))
      have hlocal : IsLocalMax (radiusSq ∘ Φ) p := hm.isLocalMax hnhds
      have hlocal' : IsLocalMax (radiusSq ∘ Φ) (Φ.symm (Φ p)) := by simpa using hlocal
      have hcomp := hlocal'.comp_continuous Φ.symm.continuous.continuousAt
      have hz : Φ p = 0 := radiusSq_eq_zero_of_isLocalMax (by
        simpa only [Function.comp_def,Homeomorph.apply_symm_apply] using hcomp)
      simpa only [hz,radiusSq,Prod.fst_zero,Prod.snd_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add]
        using sq_nonneg R
  intro q hq
  exact (hm hq).trans hbound

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Classical
open Set Function MeasureTheory
open scoped ContDiff Topology Classical NNReal
open Set Function MeasureTheory

theorem homeomorph_image_closedRoundDisk (Φ : Plane ≃ₜ Plane) (R : ℝ)
    (hcircle : ∀ p, radiusSq (Φ p) = R^2 ↔ radiusSq p = R^2) :
    Φ '' closedRoundDisk R = closedRoundDisk R := by
  apply Set.Subset.antisymm
  · exact (homeomorph_mapsTo_closedRoundDisk Φ R (fun p => (hcircle p).mpr)).image_subset
  · intro p hp
    have hi : ∀ q, radiusSq (Φ.symm q) = R^2 → radiusSq q = R^2 := by
      intro q hq
      simpa only [Homeomorph.apply_symm_apply] using (hcircle (Φ.symm q)).mpr hq
    exact ⟨Φ.symm p,homeomorph_mapsTo_closedRoundDisk Φ.symm R
      (fun q hq => (hcircle (Φ.symm q)).mp (by simpa only [Homeomorph.apply_symm_apply] using hq)) hp,
      Φ.apply_symm_apply p⟩

theorem backgroundDensity_positive {g f : Plane → ℝ}
    (hg : ∀ x, 0 < g x) (hf : ∀ x, 0 < g x+f x) (p : ℝ × Plane) :
    0 < backgroundDensity g f p := by
  have hb := Real.smoothTransition.nonneg p.1
  have hc := Real.smoothTransition.le_one p.1
  unfold backgroundDensity
  by_cases hx : 0 ≤ f p.2
  · exact add_pos_of_pos_of_nonneg (hg p.2) (mul_nonneg hb hx)
  · have hx' : f p.2 < 0 := lt_of_not_ge hx
    have hmul := mul_le_mul_of_nonpos_right hc hx'.le
    nlinarith [hf p.2]

theorem backgroundDensity_smooth {g f : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (backgroundDensity g f) :=
  (hg.comp contDiff_snd).add ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (hf.comp contDiff_snd))

theorem backgroundField_smooth {g f U V : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hgpos : ∀ x, 0 < g x) (hpos : ∀ x, 0 < g x+f x) :
    ContDiff ℝ ∞ (backgroundField g f U V) := by
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (((hβ.comp contDiff_fst).neg.mul (hV.comp contDiff_snd)).div
    (backgroundDensity_smooth hg hf) (fun p => (backgroundDensity_positive hgpos hpos p).ne')).prodMk
    (((hβ.comp contDiff_fst).mul (hU.comp contDiff_snd)).div
      (backgroundDensity_smooth hg hf) (fun p => (backgroundDensity_positive hgpos hpos p).ne'))

theorem backgroundField_transport {g f U V : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hgpos : ∀ x, 0 < g x) (hpos : ∀ x, 0 < g x+f x)
    (hcurl : ∀ p, deriv (fun x => V (x,p.2)) p.1 - deriv (fun t => U (p.1,t)) p.2 = f p)
    (p : ℝ × Plane) (v w : Plane) :
    fderiv ℝ (backgroundDensity g f) p (1,backgroundField g f U V p) * planarArea v w +
      backgroundDensity g f p * (planarArea (fderiv ℝ (backgroundField g f U V) p (0,v)) w +
        planarArea v (fderiv ℝ (backgroundField g f U V) p (0,w))) = 0 := by
  let X := backgroundField g f U V
  let ρ := backgroundDensity g f
  let b := deriv Real.smoothTransition p.1
  let d := fderiv ℝ ρ p
  let A := (fderiv ℝ X p).comp (ContinuousLinearMap.inr ℝ ℝ Plane)
  have hXd : Differentiable ℝ X := (backgroundField_smooth hg hf hU hV hgpos hpos).differentiable (by simp)
  have hρd : Differentiable ℝ ρ := (backgroundDensity_smooth hg hf).differentiable (by simp)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hflux1 : d (0,(1,0)) * (X p).1 + ρ p * (A (1,0)).1 =
      -b * fderiv ℝ V p.2 (1,0) := by
    have hd := (hasDerivAt_horizontal_first hρd p).mul (hasDerivAt_horizontal_first hXd p).fst
    have he : (fun x => ρ (p.1,(x,p.2.2)) * (X (p.1,(x,p.2.2))).1) =
        fun x => -b * V (x,p.2.2) := by
      funext x
      dsimp [X,ρ,backgroundField,b]
      field_simp [(backgroundDensity_positive hgpos hpos (p.1,(x,p.2.2))).ne']
    change HasDerivAt (fun x => ρ (p.1,(x,p.2.2)) * (X (p.1,(x,p.2.2))).1) _ p.2.1 at hd
    rw [he] at hd
    have hd' := ((hVd p.2).hasFDerivAt.comp_hasDerivAt p.2.1
      ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2))).const_mul (-b)
    exact hd.unique hd'
  have hflux2 : d (0,(0,1)) * (X p).2 + ρ p * (A (0,1)).2 =
      b * fderiv ℝ U p.2 (0,1) := by
    have hd := (hasDerivAt_horizontal_second hρd p).mul (hasDerivAt_horizontal_second hXd p).snd
    have he : (fun y => ρ (p.1,(p.2.1,y)) * (X (p.1,(p.2.1,y))).2) =
        fun y => b * U (p.2.1,y) := by
      funext y
      dsimp [X,ρ,backgroundField,b]
      field_simp [(backgroundDensity_positive hgpos hpos (p.1,(p.2.1,y))).ne']
    change HasDerivAt (fun y => ρ (p.1,(p.2.1,y)) * (X (p.1,(p.2.1,y))).2) _ p.2.2 at hd
    rw [he] at hd
    have hd' := ((hUd p.2).hasFDerivAt.comp_hasDerivAt p.2.2
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2))).const_mul b
    exact hd.unique hd'
  have ht : d (1,(0,0)) = b * f p.2 := by
    have hd := (hρd p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    have hβ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    have hb := (hβ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p.1).hasDerivAt
    have hd' := (hb.mul_const (f p.2)).const_add (g p.2)
    exact hd.unique hd'
  have hc : fderiv ℝ V p.2 (1,0) - fderiv ℝ U p.2 (0,1) = f p.2 := by
    simpa only [plane_deriv_first hVd,plane_deriv_second hUd] using hcurl p.2
  have hlin : d (1,X p) = d (1,(0,0)) + (X p).1 * d (0,(1,0)) + (X p).2 * d (0,(0,1)) := by
    have he : ((1:ℝ),X p) = ((1:ℝ),(0:Plane)) +
        (X p).1 • ((0:ℝ),((1:ℝ),(0:ℝ))) + (X p).2 • ((0:ℝ),((0:ℝ),(1:ℝ))) := by
      ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hdiv : d (1,X p) + ρ p * ((A (1,0)).1+(A (0,1)).2) = 0 := by
    rw [hlin]
    linear_combination hflux1 + hflux2 + ht - b * hc
  change d (1,X p) * planarArea v w + ρ p * (planarArea (A v) w + planarArea v (A w)) = 0
  rw [planarArea_trace_identity]
  linear_combination (planarArea v w) * hdiv

theorem backgroundField_tangent {g f U V : Plane → ℝ} {R : ℝ}
    (ht : ∀ p, radiusSq p = R^2 → -p.2*U p+p.1*V p = 0) :
    ∀ t p, radiusSq p = R^2 → radialDrift (backgroundField g f U V) (t,p) = 0 := by
  intro t p hp
  have he := ht p hp
  unfold radialDrift backgroundField
  dsimp only
  calc
    2*(p.1*(-deriv Real.smoothTransition t*V p/backgroundDensity g f (t,p)) +
      p.2*(deriv Real.smoothTransition t*U p/backgroundDensity g f (t,p))) =
      (-2*deriv Real.smoothTransition t/backgroundDensity g f (t,p)) * (-p.2*U p+p.1*V p) := by ring
    _ = 0 := by rw [he,mul_zero]


end

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

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in

theorem compactSupport_fiber {Q F : Type*} [TopologicalSpace Q] [T2Space Q]
    [Zero F] {f : P × Q → F} (hc : HasCompactSupport f) (y : P) :
    HasCompactSupport (fun x => f (y,x)) := by
  apply HasCompactSupport.intro (hc.image continuous_snd)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(y,x),h,rfl⟩)

theorem exists_parametric_compact_primitive {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : ∀ y, (∫ x, f (y,x)) = 0) :
    ∃ U V : P × Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y p, deriv (fun x => V (y,(x,p.2))) p.1 -
        deriv (fun t => U (y,(p.1,t))) p.2 = f (y,p)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, U (y,x) = 0 ∧ V (y,x) = 0 := by
  obtain ⟨A,hA,hbound⟩ := hfc.isBounded.subset_ball_lt 1 (0 : P × Plane)
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hzero (y : P) (x t : ℝ) (ht : A ≤ ‖y‖ ∨ A ≤ |x| ∨ A ≤ |t|) : f (y,(x,t)) = 0 := by
    by_contra hn
    have hb := hbound (subset_tsupport f (show (y,(x,t)) ∈ support f from hn))
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] at hb
    rcases ht with ht | ht | ht
    · exact (not_lt_of_ge ht) hb.1
    · exact (not_lt_of_ge ht) hb.2.1
    · exact (not_lt_of_ge ht) hb.2.2
  let b : ContDiffBump (0 : ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρs (x : ℝ) (hx : A ≤ |x|) : ρ x = 0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hb' : |x| < A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hb'
  have hρ1 : (∫ x in -A..A, ρ x) = 1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact b.integral_normed
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hg (y : P) : ContDiff ℝ ∞ (planarMarginal A (fun x => f (y,x))) :=
    planarMarginal_smooth (hfy y) A
  have hgt (y : P) (t : ℝ) (ht : A ≤ |t|) : planarMarginal A (fun x => f (y,x)) t = 0 := by
    unfold planarMarginal
    have he : (fun x => f (y,(x,t))) = fun _ => (0:ℝ) := funext fun x => hzero y x t (Or.inr (Or.inr ht))
    rw [he,intervalIntegral.integral_zero]
  have hgm (y : P) (t : ℝ) : planarMarginal A (fun x => f (y,x)) t = ∫ x, f (y,(x,t)) :=
    integral_eq_full_of_box_support (fun x hx => hzero y x t (Or.inr (Or.inl hx)))
  have hgm0 (y : P) : (∫ t in -A..A, planarMarginal A (fun x => f (y,x)) t) = 0 := by
    rw [integral_eq_full_of_box_support (hgt y)]
    simp_rw [hgm]
    rw [← integral_prod_symm (fun x => f (y,x))]
    · exact hf0 y
    · exact (hfy y).continuous.integrable_of_hasCompactSupport (compactSupport_fiber hfc y)
  let U : P × Plane → ℝ := fun p => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2
  let V : P × Plane → ℝ := fun p => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2
  have huv (p : P × Plane) (hp : p ∉ Metric.closedBall 0 A) : U p = 0 ∧ V p = 0 := by
    have hp' : A < max ‖p.1‖ (max |p.2.1| |p.2.2|) := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hp
    rcases lt_max_iff.mp hp' with hp' | hp'
    · have he : (fun x => f (p.1,x)) = fun _ => (0:ℝ) := by
        funext x
        exact hzero p.1 x.1 x.2 (Or.inl hp'.le)
      change planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2 = 0 ∧
        planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2 = 0
      rw [he]
      simp [planarPrimitiveX,planarPrimitiveY,planarMarginal]
    · apply planarPrimitive_zero_outside hA0.le (hfy p.1).continuous hρ.continuous
        (fun x t ht => hzero p.1 x t (Or.inr ht)) hρs hρ1 (hg p.1).continuous (hgm0 p.1) p.2
      exact (lt_max_iff.mp hp').imp le_of_lt le_of_lt
  refine ⟨U,V,(planarPrimitive_parameter_smooth hf hρ A).1,
    (planarPrimitive_parameter_smooth hf hρ A).2,
    HasCompactSupport.intro (isCompact_closedBall 0 A) (fun p hp => (huv p hp).1),
    HasCompactSupport.intro (isCompact_closedBall 0 A) (fun p hp => (huv p hp).2),?_,?_⟩
  · intro y p
    exact planarPrimitive_curl (hfy y).continuous hρ.continuous (hg y).continuous p
  · intro y hy x
    have he : (fun x => f (y,x)) = fun _ => (0:ℝ) := funext hy
    change planarPrimitiveX A (fun x => f (y,x)) ρ x = 0 ∧
      planarPrimitiveY A (fun x => f (y,x)) ρ x = 0
    rw [he]
    simp [planarPrimitiveX,planarPrimitiveY,planarMarginal]


end

open scoped ContDiff



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped NNReal
open MeasureTheory
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem periodic_parameter_arg_smooth {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : ∀ y, Periodic (fun t => h (y,t)) (2*Real.pi)) {p : P × ℂ} (hz : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : P × ℂ => h (q.1,q.2.arg)) p := by
  by_cases hs : p.2 ∈ Complex.slitPlane
  · exact hh.contDiffAt.comp p (contDiffAt_fst.prodMk
      ((contDiffAt_arg_slit hs).comp p contDiffAt_snd))
  · have hsneg : -p.2 ∈ Complex.slitPlane :=
      (Complex.mem_slitPlane_or_neg_mem_slitPlane hz).resolve_left hs
    have hd : ContDiffAt ℝ ∞ (fun q : P × ℂ => h (q.1,(-q.2).arg+Real.pi)) p :=
      hh.contDiffAt.comp p (contDiffAt_fst.prodMk
        (((contDiffAt_arg_slit hsneg).comp p contDiffAt_snd.neg).add contDiffAt_const))
    apply hd.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds hz] with q hq
    exact periodic_arg_neg (hp q.1) hq

theorem angularExtension_parameter_smooth {R delta : ℝ} (hd : 0 < delta)
    (hdR : delta < R^2) {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : ∀ y, Periodic (fun t => h (y,t)) (2*Real.pi)) :
    ContDiff ℝ ∞ (fun p : P × Plane => angularExtension R delta hd (fun t => h (p.1,t)) p.2) := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases h0 : p.2 = 0
  · have hn : ∀ᶠ q : P × Plane in 𝓝 p, delta < |radiusSq q.2-R^2| := by
      apply (isOpen_lt continuous_const (((radiusSq_smooth.continuous.comp continuous_snd).sub
        continuous_const).abs)).mem_nhds
      simpa [h0,radiusSq,abs_of_nonneg (sq_nonneg R)] using hdR
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    exact angularExtension_zero hd _ q.2 hq.le
  · have hz : Complex.equivRealProdCLM.symm p.2 ≠ 0 := by
      intro he
      apply h0
      apply Complex.equivRealProdCLM.symm.injective
      simpa only [map_zero] using he
    exact (b.contDiff.comp (radiusSq_smooth.comp contDiff_snd)).contDiffAt.mul
      ((periodic_parameter_arg_smooth hh hp hz).comp p
        (contDiff_fst.prodMk (Complex.equivRealProdCLM.symm.contDiff.comp contDiff_snd)).contDiffAt)

omit [NormedSpace ℝ P] in
theorem angularExtension_parameter_compact {R delta : ℝ} (hd : 0 < delta)
    {h : P × ℝ → ℝ} {K : Set P} (hK : IsCompact K)
    (hzero : ∀ y, y ∉ K → ∀ t, h (y,t) = 0) :
    HasCompactSupport (fun p : P × Plane => angularExtension R delta hd (fun t => h (p.1,t)) p.2) := by
  apply HasCompactSupport.intro (hK.prod (isCompact_closedBall (0 : Plane) (R^2+delta+1)))
  intro p hp
  by_cases hy : p.1 ∈ K
  · have hx : p.2 ∉ Metric.closedBall 0 (R^2+delta+1) := fun hx => hp ⟨hy,hx⟩
    apply angularExtension_zero hd _ p.2
    by_contra! ht
    have hq : radiusSq p.2 < R^2+delta := by linarith [(abs_lt.mp ht).2]
    apply hx
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
    have h1 : p.2.1^2 ≤ radiusSq p.2 := by dsimp [radiusSq] <;> nlinarith [sq_nonneg p.2.2]
    have h2 : p.2.2^2 ≤ radiusSq p.2 := by dsimp [radiusSq] <;> nlinarith [sq_nonneg p.2.1]
    have hb : 0 < R^2+delta := by positivity
    constructor
    · nlinarith [sq_abs p.2.1,abs_nonneg p.2.1,sq_nonneg (|p.2.1|-1)]
    · nlinarith [sq_abs p.2.2,abs_nonneg p.2.2,sq_nonneg (|p.2.2|-1)]
  · simp only [angularExtension,hzero p.1 hy,mul_zero]

theorem circlePullback_parameter_smooth {alpha : P × Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (R : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => circlePullback (fun x => alpha (p.1,x)) R p.2) := by
  apply (ha.comp (contDiff_fst.prodMk (polar_smooth.comp (contDiff_const.prodMk contDiff_snd)))).clm_apply
  fun_prop

variable [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
theorem fiber_fderiv {F : P × Plane → ℝ} (hF : ContDiff ℝ ∞ F) (y : P) (x : Plane) :
    fderiv ℝ (fun x => F (y,x)) x =
      (fderiv ℝ F (y,x)).comp (ContinuousLinearMap.inr ℝ P Plane) := by
  have hi : HasFDerivAt (fun x : Plane => (y,x)) (ContinuousLinearMap.inr ℝ P Plane) x := by
    simpa only [Prod.mk_add_mk,zero_add,add_zero,ContinuousLinearMap.inr_apply] using
      ((ContinuousLinearMap.inr ℝ P Plane).hasFDerivAt (x := x)).const_add (y,0)
  exact (((hF.differentiable (by simp)) (y,x)).hasFDerivAt.comp x hi).fderiv

omit [FiniteDimensional ℝ P] in
theorem fiber_fderiv_smooth {F : P × Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he : (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) =
      fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ P Plane) := by
    funext p
    exact fiber_fderiv hF p.1 p.2
  rw [he]
  exact (hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const

omit [FiniteDimensional ℝ P] in
theorem fiber_fderiv_compact {F : P × Plane → ℝ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    HasCompactSupport (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he : (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) =
      (fun A : (P × Plane) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inr ℝ P Plane)) ∘ fderiv ℝ F := by
    funext p
    exact fiber_fderiv hF p.1 p.2
  rw [he]
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp only [ContinuousLinearMap.zero_comp])

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem fixedStep_affine {L M : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (Y : C(F,F)) (hY : LipschitzWith M Y) (A : E →L[ℝ] F) (b : F)
    (hXY : ∀ x, Y (b+A x) = A (X x))
    {h : ℝ} (hhX : ‖h‖*L < 1) (hhY : ‖h‖*M < 1) (x : E) :
    fixedStep Y hY h (b+A x) =
      ⟨fun s => b+A (fixedStep X hX h x s),
        continuous_const.add (A.continuous.comp (fixedStep X hX h x).continuous)⟩ := by
  let u := fixedStep X hX h x
  let q : C(Time,F) := ⟨fun s => b+A (u s),continuous_const.add (A.continuous.comp u.continuous)⟩
  change fixedStep Y hY h (b+A x) = q
  apply (picard_contracts Y hY (p := (b+A x,h)) hhY).fixedPoint_unique'
    (localPath_fixed Y hY (p := (b+A x,h)) hhY)
  apply ContinuousMap.ext
  intro s
  have hu := congrArg (fun v : C(Time,E) => v s) (fixedStep_equation X hX hhX x)
  have hq : (fun t : ℝ => extendPath (Y.comp q) t) =
      fun t => A (extendPath (X.comp u) t) := by
    funext t
    exact hXY _
  have hi := A.intervalIntegral_comp_comm (μ := volume)
    ((extendPath (X.comp u)).continuous.intervalIntegrable 0 (s:ℝ))
  change b+A x + h • (∫ t in 0..(s:ℝ), extendPath (Y.comp q) t) = b+A (u s)
  rw [hq,hi]
  change u s = x + h • (∫ t in 0..(s:ℝ), extendPath (X.comp u) t) at hu
  rw [hu,map_add,map_smul]
  simp only [add_assoc]

theorem stepEndpoint_affine {L M : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (Y : C(F,F)) (hY : LipschitzWith M Y) (A : E →L[ℝ] F) (b : F)
    (hXY : ∀ x, Y (b+A x) = A (X x))
    {h : ℝ} (hhX : ‖h‖*L < 1) (hhY : ‖h‖*M < 1) (x : E) :
    stepEndpoint Y hY h (b+A x) = b+A (stepEndpoint X hX h x) := by
  exact congrArg (fun u : C(Time,F) => u ⟨1,by simp⟩)
    (fixedStep_affine X hX Y hY A b hXY hhX hhY x)

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem timeStep_fiber {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (y : P) (x : E) :
    timeStep (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX) h t (y,x) =
      (y,timeStep (fiberField X y) (fiberField_lipschitz X hX y) h t x) := by
  let A : (ℝ × E) →L[ℝ] (ℝ × (P × E)) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod
      ((0 : (ℝ × E) →L[ℝ] P).prod (ContinuousLinearMap.snd ℝ ℝ E))
  let b : ℝ × (P × E) := (0,(y,0))
  have hXY : ∀ p, clockField (E := P × E) (parameterField X) (b+A p) =
      A (clockField (E := E) (fiberField X y) p) := by
    intro p
    simp only [b,A,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',zero_apply,Prod.mk_add_mk,
      zero_add,add_zero,clockField_apply,parameterField,fiberField,ContinuousMap.coe_mk]
  have he := stepEndpoint_affine (clockField (E := E) (fiberField X y))
    (clockField_lipschitz (E := E) (fiberField X y) (fiberField_lipschitz X hX y)) (clockField (E := P × E) (parameterField X))
    (clockField_lipschitz (E := P × E) (parameterField X) (parameterField_lipschitz X hX)) A b hXY hh hh (t,x)
  have he' := congrArg Prod.snd he
  simpa only [b,A,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',zero_apply,Prod.mk_add_mk,
    zero_add,add_zero,timeStep] using he'

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

theorem timeSteps_fiber {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (N : ℕ) (y : P) (x : E) :
    timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
        (parameterField_smooth X hXs) hh t N (y,x) =
      (y,timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
        (fiberField_smooth X hXs y) hh t N x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX) h (t+N*h)
      (timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
        (parameterField_smooth X hXs) hh t N (y,x)) = _
    rw [ih,timeStep_fiber X hX hh]
    rfl

theorem timeSteps_fiber_smooth {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : P × E => timeSteps (fiberField X p.1)
      (fiberField_lipschitz X hX p.1) (fiberField_smooth X hXs p.1) hh t N p.2) ∧
    ContDiff ℝ ∞ (fun p : P × E => (timeSteps (fiberField X p.1)
      (fiberField_lipschitz X hX p.1) (fiberField_smooth X hXs p.1) hh t N).symm p.2) := by
  let Φ := timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
    (parameterField_smooth X hXs) hh t N
  let φ (y : P) := timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
    (fiberField_smooth X hXs y) hh t N
  have he (p : P × E) : Φ p = (p.1,φ p.1 p.2) := timeSteps_fiber X hX hXs hh t N p.1 p.2
  have hei (p : P × E) : Φ.symm p = (p.1,(φ p.1).symm p.2) := by
    apply Φ.injective
    rw [Φ.apply_symm_apply,he,(φ p.1).apply_symm_apply]
  have hs := timeSteps_smooth (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
    (parameterField_smooth X hXs) hh t N
  constructor
  · have hfun : (fun p : P × E => φ p.1 p.2) = fun p => (Φ p).2 :=
      funext fun p => (congrArg Prod.snd (he p)).symm
    change ContDiff ℝ ∞ (fun p : P × E => φ p.1 p.2)
    rw [hfun]
    exact hs.1.snd
  · have hfun : (fun p : P × E => (φ p.1).symm p.2) = fun p => (Φ.symm p).2 :=
      funext fun p => (congrArg Prod.snd (hei p)).symm
    change ContDiff ℝ ∞ (fun p : P × E => (φ p.1).symm p.2)
    rw [hfun]
    exact hs.2.snd

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
theorem fiberField_compact (X : C(ℝ × (P × E),E)) (hc : HasCompactSupport X) (y : P) :
    HasCompactSupport (fiberField X y) := by
  apply HasCompactSupport.intro
    (hc.image (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  intro p hp
  change X (p.1,(y,p.2)) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(p.1,(y,p.2)),h,rfl⟩)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory
section
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in

theorem parametric_backgroundField_smooth {g f U V : P × Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hgpos : ∀ p, 0 < g p) (hpos : ∀ p, 0 < g p+f p) :
    ContDiff ℝ ∞ (fun p : ℝ × (P × Plane) =>
      backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
        (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)) := by
  have hb : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.mp hb).2
  have hd : ContDiff ℝ ∞ (fun p : ℝ × (P × Plane) =>
      g p.2 + Real.smoothTransition p.1 * f p.2) :=
    (hg.comp contDiff_snd).add ((hb.comp contDiff_fst).mul (hf.comp contDiff_snd))
  have hdpos (p : ℝ × (P × Plane)) : 0 < g p.2 + Real.smoothTransition p.1 * f p.2 :=
    backgroundDensity_positive (fun x => hgpos (p.2.1,x)) (fun x => hpos (p.2.1,x)) (p.1,p.2.2)
  exact (((hβ.comp contDiff_fst).neg.mul (hV.comp contDiff_snd)).div hd (fun p => (hdpos p).ne')).prodMk
    (((hβ.comp contDiff_fst).mul (hU.comp contDiff_snd)).div hd (fun p => (hdpos p).ne'))

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem parametric_backgroundField_compact {g f U V : P × Plane → ℝ}
    (hU : HasCompactSupport U) (hV : HasCompactSupport V) :
    HasCompactSupport (fun p : ℝ × (P × Plane) =>
      backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
        (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)) := by
  apply HasCompactSupport.intro (smoothTransition_deriv_compact.prod (hU.union hV))
  intro p hp
  have hn : p.1 ∉ tsupport (deriv Real.smoothTransition) ∨ p.2 ∉ tsupport U ∪ tsupport V := by
    simpa only [mem_prod,not_and_or] using hp
  rcases hn with ht | hx
  · simp [backgroundField,image_eq_zero_of_notMem_tsupport ht]
  · have hu : U p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hv : V p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    simp [backgroundField,hu,hv]

end

theorem radialDiskChart_target {R : ℝ} (hR : 0 < R) :
    (radialDiskChart R).target = roundDisk R := by
  simp only [radialDiskChart,OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,OpenPartialHomeomorph.univBall_target _ hR,
    preimage_univ,inter_univ,univ_inter]
  ext p
  simp only [mem_preimage,Metric.mem_ball,dist_zero_right]
  change ‖Complex.equivRealProdCLM.symm p‖ < R ↔ radiusSq p < R^2
  rw [← complex_normSq_plane]
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).symm

theorem radialDiskChart_apply {R : ℝ} (hR : 0 < R) (p : Plane) :
    radialDiskChart R p = (R / Real.sqrt (1+radiusSq p)) • p := by
  change Complex.equivRealProdCLM
    (OpenPartialHomeomorph.univBall (0:ℂ) R (Complex.equivRealProdCLM.symm p)) = _
  simp only [OpenPartialHomeomorph.univBall,dite_eq_left hR]
  change Complex.equivRealProdCLM
    (R • ((Real.sqrt (1+‖Complex.equivRealProdCLM.symm p‖^2))⁻¹ •
      Complex.equivRealProdCLM.symm p) + 0) = _
  rw [add_zero,map_smul,map_smul,ContinuousLinearEquiv.apply_symm_apply,
    complex_normSq_plane,smul_smul,div_eq_mul_inv]

theorem radialDiskChart_smooth (R : ℝ) : ContDiff ℝ ∞ (radialDiskChart R) :=
  Complex.equivRealProdCLM.contDiff.comp
    (OpenPartialHomeomorph.contDiff_univBall.comp Complex.equivRealProdCLM.symm.contDiff)

theorem radialDiskChart_symm_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (radialDiskChart R).symm (roundDisk R) := by
  apply Complex.equivRealProdCLM.contDiff.comp_contDiffOn
  apply OpenPartialHomeomorph.contDiffOn_univBall_symm.comp
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn
  intro p hp
  rw [Metric.mem_ball,dist_zero_right]
  have hs : ‖Complex.equivRealProdCLM.symm p‖^2 < R^2 := by
    rw [complex_normSq_plane]
    exact hp
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp hs

theorem radialDiskChart_fderiv {R : ℝ} (hR : 0 < R) (p v : Plane) :
    fderiv ℝ (radialDiskChart R) p v =
      (R / Real.sqrt (1+radiusSq p)) • v -
        (R / (Real.sqrt (1+radiusSq p))^3 * (p.1*v.1+p.2*v.2)) • p := by
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  have hs : Real.sqrt (1+radiusSq p) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hq := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2
  have hr := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2
  have hd := HasFDerivAt.const_add 1 (hq.add hr)
  have hds := hd.sqrt hp.ne'
  have hdi := (hasDerivAt_inv hs).comp_hasFDerivAt p hds
  have hdc := hdi.const_mul R
  have he := hdc.smul (hasFDerivAt_id p)
  have hfun : (fun q : Plane => (R * (Real.sqrt (1+(q.1^2+q.2^2)))⁻¹) • q) =
      radialDiskChart R := by
    funext q
    rw [radialDiskChart_apply hR]
    rfl
  change HasFDerivAt (fun q : Plane => (R * (Real.sqrt (1+(q.1^2+q.2^2)))⁻¹) • q) _ p at he
  rw [hfun] at he
  rw [he.fderiv]
  ext <;> simp [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    Prod.smul_def,smul_eq_mul,radiusSq] <;> field_simp <;> ring

theorem radialDiskDensity_pos {R : ℝ} (hR : 0 < R) (p : Plane) :
    0 < radialDiskDensity R p := by
  exact div_pos (sq_pos_of_pos hR) (sq_pos_of_pos (by have := radiusSq_nonneg p; linarith))

theorem radialDiskDensity_smooth (R : ℝ) : ContDiff ℝ ∞ (radialDiskDensity R) := by
  apply contDiff_const.div ((contDiff_const.add radiusSq_smooth).pow 2)
  intro p
  exact pow_ne_zero _ (by have := radiusSq_nonneg p; positivity)

theorem planarArea_radial_rank_one (a b : ℝ) (p v w : Plane) :
    planarArea (a • v - (b * (p.1*v.1+p.2*v.2)) • p)
      (a • w - (b * (p.1*w.1+p.2*w.2)) • p) =
      (a^2-a*b*radiusSq p)*planarArea v w := by
  change (a*v.1-b*(p.1*v.1+p.2*v.2)*p.1)*(a*w.2-b*(p.1*w.1+p.2*w.2)*p.2) -
    (a*v.2-b*(p.1*v.1+p.2*v.2)*p.2)*(a*w.1-b*(p.1*w.1+p.2*w.2)*p.1) =
      (a^2-a*b*(p.1^2+p.2^2))*(v.1*w.2-v.2*w.1)
  ring

theorem radialDiskChart_area {R : ℝ} (hR : 0 < R) (p v w : Plane) :
    planarArea (fderiv ℝ (radialDiskChart R) p v)
      (fderiv ℝ (radialDiskChart R) p w) = radialDiskDensity R p * planarArea v w := by
  rw [radialDiskChart_fderiv hR,radialDiskChart_fderiv hR,planarArea_radial_rank_one]
  congr 1
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  have hs : Real.sqrt (1+radiusSq p) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hs2 := Real.sq_sqrt hp.le
  unfold radialDiskDensity
  generalize Real.sqrt (1+radiusSq p) = s at *
  rw [show radiusSq p = s^2-1 by linarith]
  field_simp
  ring

theorem radiusSq_smul (a : ℝ) (p : Plane) : radiusSq (a • p) = a^2*radiusSq p := by
  change (a*p.1)^2+(a*p.2)^2 = a^2*(p.1^2+p.2^2)
  ring

theorem radialDiskChart_radiusSq {R : ℝ} (hR : 0 < R) (p : Plane) :
    radiusSq (radialDiskChart R p) = R^2*radiusSq p/(1+radiusSq p) := by
  rw [radialDiskChart_apply hR,radiusSq_smul,div_pow,Real.sq_sqrt]
  · ring
  · have := radiusSq_nonneg p
    linarith

theorem diskChartRadius_pos {R r : ℝ} (hr : 0 < r) (hrR : r < R) :
    0 < diskChartRadius R r := by
  apply div_pos hr
  apply Real.sqrt_pos.mpr
  nlinarith

theorem radialDiskChart_closed_iff {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (p : Plane) : radialDiskChart R p ∈ closedRoundDisk r ↔
      p ∈ closedRoundDisk (diskChartRadius R r) := by
  change radiusSq (radialDiskChart R p) ≤ r^2 ↔ radiusSq p ≤ _
  have hd : 0 < R^2-r^2 := by nlinarith
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  rw [radialDiskChart_radiusSq hR,div_le_iff₀ hp]
  change _ ↔ radiusSq p ≤ (r/Real.sqrt (R^2-r^2))^2
  rw [div_pow,Real.sq_sqrt hd.le,le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem radialDiskChart_open_iff {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (p : Plane) : radialDiskChart R p ∈ roundDisk r ↔
      p ∈ roundDisk (diskChartRadius R r) := by
  change radiusSq (radialDiskChart R p) < r^2 ↔ radiusSq p < _
  have hd : 0 < R^2-r^2 := by nlinarith
  have hp : 0 < 1+radiusSq p := by have := radiusSq_nonneg p; linarith
  rw [radialDiskChart_radiusSq hR,div_lt_iff₀ hp]
  change _ ↔ radiusSq p < (r/Real.sqrt (R^2-r^2))^2
  rw [div_pow,Real.sq_sqrt hd.le,lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem radialDiskChart_image_closed {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) :
    radialDiskChart R '' closedRoundDisk (diskChartRadius R r) = closedRoundDisk r := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (radialDiskChart_closed_iff hR hr hrR q).mpr hq
  · intro hp
    have ht : p ∈ (radialDiskChart R).target := by
      rw [radialDiskChart_target hR]
      change radiusSq p < R^2
      change radiusSq p ≤ r^2 at hp
      nlinarith
    refine ⟨(radialDiskChart R).symm p,?_,(radialDiskChart R).right_inv ht⟩
    apply (radialDiskChart_closed_iff hR hr hrR _).mp
    rw [(radialDiskChart R).right_inv ht]
    exact hp

theorem radialDiskChart_image_open {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) :
    radialDiskChart R '' roundDisk (diskChartRadius R r) = roundDisk r := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (radialDiskChart_open_iff hR hr hrR q).mpr hq
  · intro hp
    have ht : p ∈ (radialDiskChart R).target := by
      rw [radialDiskChart_target hR]
      change radiusSq p < R^2
      change radiusSq p < r^2 at hp
      nlinarith
    refine ⟨(radialDiskChart R).symm p,?_,(radialDiskChart R).right_inv ht⟩
    apply (radialDiskChart_open_iff hR hr hrR _).mp
    rw [(radialDiskChart R).right_inv ht]
    exact hp

theorem diskChartRadius_strictMonoOn {R : ℝ} (hR : 0 < R) :
    StrictMonoOn (diskChartRadius R) (Ico 0 R) := by
  intro r hr s hs hrs
  have hdr : 0 < R^2-r^2 := by nlinarith [hr.1,hr.2]
  have hds : 0 < R^2-s^2 := by nlinarith [hs.1,hs.2]
  have hnr : 0 ≤ diskChartRadius R r := div_nonneg hr.1 (Real.sqrt_nonneg _)
  have hns : 0 ≤ diskChartRadius R s := div_nonneg hs.1 (Real.sqrt_nonneg _)
  apply (sq_lt_sq₀ hnr hns).mp
  change (r/Real.sqrt (R^2-r^2))^2 < (s/Real.sqrt (R^2-s^2))^2
  rw [div_pow,div_pow,Real.sq_sqrt hdr.le,Real.sq_sqrt hds.le,div_lt_div_iff₀ hdr hds]
  nlinarith [mul_pos (sq_pos_of_pos hR) (show 0 < s^2-r^2 by nlinarith [hr.1])]

theorem planar_det (A : Plane →L[ℝ] Plane) :
    A.det = planarArea (A (1,0)) (A (0,1)) := by
  let b : Module.Basis (Fin 2) ℝ Plane :=
    Module.Basis.ofEquivFun (LinearEquiv.finTwoArrow ℝ ℝ).symm
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix b,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,b,Module.Basis.coe_ofEquivFun,
    LinearEquiv.finTwoArrow,planarArea_apply]
  ring

theorem radialDiskChart_det {R : ℝ} (hR : 0 < R) (p : Plane) :
    (fderiv ℝ (radialDiskChart R) p).det = radialDiskDensity R p := by
  rw [planar_det,radialDiskChart_area hR]
  simp [planarArea_apply]

theorem radialDiskChart_integral {R : ℝ} (hR : 0 < R) (f : Plane → ℝ) :
    (∫ x in roundDisk R, f x) = ∫ x, radialDiskDensity R x*f (radialDiskChart R x) := by
  have he := integral_target_eq_integral_abs_det_fderiv_smul volume
    (f := radialDiskChart R) (f' := fderiv ℝ (radialDiskChart R))
    (fun x _ => (((radialDiskChart_smooth R).differentiable (by simp)) x).hasFDerivAt) f
  simpa only [radialDiskChart_target hR,radialDiskChart_source,setIntegral_univ,
    radialDiskChart_det hR,abs_of_pos (radialDiskDensity_pos hR _),smul_eq_mul] using he

theorem radialDiskChart_integral_inner {R r : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (hrR : r < R) (f : Plane → ℝ) :
    (∫ x in roundDisk r, f x) = ∫ x in roundDisk (diskChartRadius R r),
      radialDiskDensity R x*f (radialDiskChart R x) := by
  have hm : MeasurableSet (roundDisk (diskChartRadius R r)) :=
    (isOpen_lt radiusSq_smooth.continuous continuous_const).measurableSet
  have hinj : InjOn (radialDiskChart R) (roundDisk (diskChartRadius R r)) :=
    (radialDiskChart R).injOn.mono (by rw [radialDiskChart_source]; exact subset_univ _)
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (f' := fderiv ℝ (radialDiskChart R))
    (fun x _ => (((radialDiskChart_smooth R).differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    hinj f
  simpa only [radialDiskChart_image_open hR hr hrR,radialDiskChart_det hR,
    abs_of_pos (radialDiskDensity_pos hR _),smul_eq_mul] using he

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Chart
open scoped ContDiff Topology
open Set Function

variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_image (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E → E) (A : Set E) : conjugate c φ '' (c '' A) = c '' (φ '' A) := by
  rw [image_image,image_image]
  apply image_congr
  intro x _
  exact conjugate_apply c hc φ x

theorem conjugate_contDiffAt_of_mem (c : OpenPartialHomeomorph E F)
    (hc : ContDiff ℝ ∞ c) (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) {x : F} (hx : x ∈ c.target) :
    ContDiffAt ℝ ∞ (conjugate c φ) x := by
  have hi := (hci x hx).contDiffAt (c.open_target.mem_nhds hx)
  have hd := hc.contDiffAt.comp x (hφ.contDiffAt.comp x hi)
  apply hd.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hx] with q hq
  exact conjugate_of_mem c φ hq

theorem chart_fderiv_right_inverse (c : OpenPartialHomeomorph E F)
    (hc : ContDiff ℝ ∞ c) (hci : ContDiffOn ℝ ∞ c.symm c.target)
    {x : F} (hx : x ∈ c.target) (v : F) :
    fderiv ℝ c (c.symm x) (fderiv ℝ c.symm x v) = v := by
  have hi := ((hci x hx).contDiffAt (c.open_target.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := ((hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) _).hasFDerivAt.comp x hi.hasFDerivAt
  have he : (id : F → F) =ᶠ[𝓝 x] (c ∘ c.symm) := by
    filter_upwards [c.open_target.mem_nhds hx] with q hq
    exact (c.right_inv hq).symm
  have hder := (hd.congr_of_eventuallyEq he).fderiv
  have hv := congrArg (fun L : F →L[ℝ] F => L v) hder
  simpa only [fderiv_id,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply] using hv.symm

theorem conjugate_fderiv_chart (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (φ : E → E) (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (conjugate c φ) (c x) (fderiv ℝ c x v) =
      fderiv ℝ c (φ x) (fderiv ℝ φ x v) := by
  have hx : c x ∈ c.target := c.map_source (by rw [hcs]; trivial)
  have hd := (conjugate_contDiffAt_of_mem c hc hci φ hφ hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hl := hd.hasFDerivAt.comp x (((hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x).hasFDerivAt)
  have hr := (((hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (φ x)).hasFDerivAt).comp x
    (((hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x).hasFDerivAt)
  have he : (conjugate c φ ∘ c) = (c ∘ φ) := funext (conjugate_apply c hcs φ)
  rw [he] at hl
  have hder := hl.unique hr
  exact congrArg (fun L : E →L[ℝ] F => L v) hder

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
theorem fiber_displacement_compact (φ : P → E → E)
    (hφ : HasCompactSupport (fun p : P × E => φ p.1 p.2-p.2)) (y : P) :
    HasCompactSupport (fun p : E => φ y p-p) := by
  apply HasCompactSupport.intro (hφ.image continuous_snd)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := fun p : P × E => φ p.1 p.2-p.2)
    (fun h => hx ⟨(y,x),h,rfl⟩)

theorem exists_conjugate_family (c : OpenPartialHomeomorph E F)
    (hcs : c.source = univ) (hc : ContDiff ℝ ∞ c)
    (hci : ContDiffOn ℝ ∞ c.symm c.target)
    (Φ : P → E ≃ₜ E) (hΦ : ContDiff ℝ ∞ (fun p : P × E => Φ p.1 p.2))
    (hΦi : ContDiff ℝ ∞ (fun p : P × E => (Φ p.1).symm p.2))
    (hΦc : HasCompactSupport (fun p : P × E => Φ p.1 p.2-p.2)) :
    ∃ Ψ : P → F ≃ₜ F,
      (∀ y x, Ψ y x = conjugate c (Φ y) x) ∧
      ContDiff ℝ ∞ (fun p : P × F => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × F => (Ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × F => Ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × F => Ψ p.1 p.2-p.2) ⊆
        univ ×ˢ c.target := by
  let Ψ : P → F ≃ₜ F := fun y => conjugateHomeomorph c hcs hc hci (Φ y)
    (hΦ.comp (contDiff_const.prodMk contDiff_id))
    (hΦi.comp (contDiff_const.prodMk contDiff_id))
    (fiber_displacement_compact (fun y => Φ y) hΦc y)
  have hs := conjugate_smooth_compact c hcs hc hci (fun y => Φ y) hΦ hΦc
  have hsi := conjugate_smooth_compact c hcs hc hci (fun y => (Φ y).symm) hΦi
    (inverse_displacement_compact Φ hΦc)
  refine ⟨Ψ,fun _ _ => rfl,hs.1,hsi.1,hs.2.1,?_⟩
  intro p hp
  obtain ⟨q,_,rfl⟩ := hs.2.2 hp
  exact ⟨mem_univ _,c.map_source (by rw [hcs]; trivial)⟩

end PackingSufficiencySupport.Chart
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_DiskMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

section
variable [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in

theorem radialDisk_pullback_compact {R : ℝ} (hR : 0 < R) {f : P × Plane → ℝ}
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ univ ×ˢ roundDisk R) :
    HasCompactSupport (fun p : P × Plane =>
      radialDiskDensity R p.2 * f (p.1,radialDiskChart R p.2)) := by
  let c := radialDiskChart R
  have ht : tsupport f ⊆ univ ×ˢ c.target := by simpa only [c, radialDiskChart_target hR] using hfs
  have hc : ContinuousOn (fun p : P × Plane => (p.1,c.symm p.2)) (tsupport f) :=
    continuousOn_fst.prodMk (c.continuousOn_symm.comp continuousOn_snd (fun p hp => (ht hp).2))
  apply HasCompactSupport.intro (hfc.image_of_continuousOn hc)
  intro p hp
  have hz : f (p.1,c p.2) = 0 := by
    by_contra hn
    apply hp
    refine ⟨(p.1,c p.2),subset_closure hn,?_⟩
    have hs : p.2 ∈ c.source := by rw [radialDiskChart_source]; trivial
    simp only [c.left_inv hs]
  exact mul_eq_zero_of_right _ hz

end

 theorem planarArea_map (A : Plane →L[ℝ] Plane) (v w : Plane) :
    planarArea (A v) (A w) = A.det * planarArea v w := by
  have hd (u : Plane) : A u = u.1 • A (1,0) + u.2 • A (0,1) := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp
  rw [planar_det,hd v,hd w]
  simp only [planarArea_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

 theorem family_spatial_fderiv {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F)
    (y : P) (x : Plane) :
    fderiv ℝ (fun x => F (y,x)) x =
      (fderiv ℝ F (y,x)).comp (ContinuousLinearMap.inr ℝ P Plane) := by
  have hi : HasFDerivAt (fun x : Plane => (y,x)) (ContinuousLinearMap.inr ℝ P Plane) x :=
    (hasFDerivAt_const y x).prodMk (hasFDerivAt_id x)
  exact (((hF.differentiable (by simp)) (y,x)).hasFDerivAt.comp x hi).fderiv

 theorem family_spatial_fderiv_smooth {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he : (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) =
      fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ P Plane) :=
    funext (fun p => family_spatial_fderiv hF p.1 p.2)
  rw [he]
  exact (hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const

 theorem spatialJacobian_smooth {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialJacobian F) := by
  have hd := family_spatial_fderiv_smooth hF
  have ha := hd.clm_apply (contDiff_const (c := ((1,0) : Plane)))
  have hb := hd.clm_apply (contDiff_const (c := ((0,1) : Plane)))
  have he : spatialJacobian F = fun p => planarArea
      (fderiv ℝ (fun x => F (p.1,x)) p.2 (1,0))
      (fderiv ℝ (fun x => F (p.1,x)) p.2 (0,1)) :=
    funext (fun p => planar_det _)
  rw [he]
  exact (planarArea.contDiff.comp ha).clm_apply hb

omit [NormedSpace ℝ P] in
 theorem spatialJacobian_support (F : P × Plane → Plane) :
    tsupport (fun p => spatialJacobian F p-1) ⊆ tsupport (fun p => F p-p.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have he : (fun x => F (p.1,x)) =ᶠ[𝓝 p.2] id := by
    have hh := (continuous_const.prodMk continuous_id).tendsto p.2
      ((isClosed_tsupport (fun p : P × Plane => F p-p.2)).isOpen_compl.mem_nhds hn)
    filter_upwards [hh] with x hx
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => F p-p.2) hx)
  apply hp
  simp [spatialJacobian,he.fderiv_eq,fderiv_id,planar_det,planarArea_apply]

omit [NormedSpace ℝ P] in
 theorem homeomorph_image_of_fixed_compl (φ : Plane ≃ₜ Plane) (S : Set Plane)
    (h : ∀ x ∉ S, φ x = x) : φ '' S = S := by
  apply Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    by_contra hn
    have hh : φ (φ y) = φ y := h (φ y) hn
    apply hn
    rw [φ.injective hh]
    exact hy
  · intro x hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    by_contra hn
    have hh := h (φ.symm x) hn
    rw [φ.apply_symm_apply] at hh
    exact hn (hh ▸ hx)

theorem spatialJacobian_integral {R : ℝ} (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hfs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hpos : ∀ p : P × Plane, 0 < spatialJacobian (fun p => φ p.1 p.2) p) (y : P) :
    (∫ x, spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x)-1) = 0 := by
  let J := spatialJacobian (fun p : P × Plane => φ p.1 p.2)
  have hJ : ContDiff ℝ ∞ J := spatialJacobian_smooth hφ
  have hd : ContDiff ℝ ∞ (φ y) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hfix (x : Plane) (hx : x ∉ closedRoundDisk R) : φ y x = x := by
    apply sub_eq_zero.mp
    apply image_eq_zero_of_notMem_tsupport (f := fun p : P × Plane => φ p.1 p.2-p.2) (x := (y,x))
    intro hh
    apply hx
    change radiusSq x ≤ R^2
    exact le_of_lt (hfs hh).2
  have himg := homeomorph_image_of_fixed_compl (φ y) (closedRoundDisk R) hfix
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (closedRoundDisk_isCompact R).measurableSet
    (f' := fderiv ℝ (φ y))
    (fun x _ => ((hd.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    (φ y).injective.injOn (fun _ : Plane => (1 : ℝ))
  have hJpos (x : Plane) : 0 < (fderiv ℝ (φ y) x).det := hpos (y,x)
  simp only [himg,smul_eq_mul,mul_one,abs_of_pos (hJpos _)] at hi
  have he : (∫ x in closedRoundDisk R, J (y,x)-1) = 0 := by
    rw [integral_sub]
    · exact sub_eq_zero.mpr hi.symm
    · exact ContinuousOn.integrableOn_compact (closedRoundDisk_isCompact R)
        (hJ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    · exact integrableOn_const (closedRoundDisk_isCompact R).measure_lt_top.ne
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at he
  · exact he
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport (f := fun p : P × Plane => J p-1) (x := (y,x))
    intro hh
    have hs := hfs (spatialJacobian_support (fun p : P × Plane => φ p.1 p.2) hh)
    exact hx (show radiusSq x ≤ R^2 from le_of_lt hs.2)

variable [FiniteDimensional ℝ P]

 theorem rectangularPotential_smooth {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (B : ℝ) : ContDiff ℝ ∞ (rectangularPotential B α) := by
  have h1 : ContDiff ℝ ∞ (fun p : P × ℝ => α (p.1,(p.2,B)) (1,0)) :=
    (hα.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => α (p.1.1,(p.1.2,p.2)) (0,1)) :=
    (hα.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).clm_apply contDiff_const
  exact ((contDiff_parameter_segment_integral h1 B).comp
    (contDiff_fst.prodMk contDiff_snd.fst)).add
    ((contDiff_parameter_segment_integral h2 B).comp
      ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
 theorem rectangularPotential_eq_of_hasFDerivAt {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : Continuous α) (B : ℝ) (y : P) {H : Plane → ℝ}
    (hH : ∀ x, HasFDerivAt H (α (y,x)) x) (x : Plane) :
    rectangularPotential B α (y,x) = H x-H (B,B) := by
  have h1 (t : ℝ) : HasDerivAt (fun t => H (t,B)) (α (y,(t,B)) (1,0)) t :=
    (hH (t,B)).comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t B))
  have h2 (t : ℝ) : HasDerivAt (fun t => H (x.1,t)) (α (y,(x.1,t)) (0,1)) t :=
    (hH (x.1,t)).comp_hasDerivAt t ((hasDerivAt_const t x.1).prodMk (hasDerivAt_id t))
  have hi1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h1 t)
    (((hα.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))).clm_apply
      continuous_const).intervalIntegrable B x.1)
  have hi2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h2 t)
    (((hα.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).clm_apply
      continuous_const).intervalIntegrable B x.2)
  change (∫ t in B..x.1, α (y,(t,B)) (1,0)) +
    (∫ t in B..x.2, α (y,(x.1,t)) (0,1)) = _
  rw [hi1,hi2]
  simp only [Prod.eta]
  ring

omit [FiniteDimensional ℝ P] in
 theorem rectangularPotential_hasFDerivAt {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α)
    (hc : ∀ y x v w, fderiv ℝ (fun x => α (y,x)) x v w =
      fderiv ℝ (fun x => α (y,x)) x w v) (B : ℝ) (y : P) (x : Plane) :
    HasFDerivAt (fun x => rectangularPotential B α (y,x)) (α (y,x)) x := by
  have hαy : ContDiff ℝ ∞ (fun x => α (y,x)) := hα.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨H,hH⟩ := (convex_univ : Convex ℝ (univ : Set Plane)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hαy.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableOn (fun x _ v w => hc y x v w)
  have he : (fun x => rectangularPotential B α (y,x)) = fun x => H x-H (B,B) :=
    funext (rectangularPotential_eq_of_hasFDerivAt hα.continuous B y (fun x => hH x trivial))
  rw [he]
  exact (hH x trivial).sub_const _

theorem exists_parametric_closed_primitive {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hclosed : ∀ y x v w, fderiv ℝ (fun x => α (y,x)) x v w =
      fderiv ℝ (fun x => α (y,x)) x w v) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ y x, HasFDerivAt (fun x => H (y,x)) (α (y,x)) x) ∧
      ∀ y, (∀ x, α (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  obtain ⟨A,hA,hB⟩ := hαc.isBounded.subset_ball_lt 1 (0 : P × Plane)
  let B := A+1
  let H := rectangularPotential B α
  have hHd (y : P) (x : Plane) : HasFDerivAt (fun x => H (y,x)) (α (y,x)) x :=
    rectangularPotential_hasFDerivAt hα hclosed B y x
  have hzero (y : P) (hy : ∀ x, α (y,x) = 0) (x : Plane) : H (y,x) = 0 := by
    simp [H,rectangularPotential,hy]
  have ha0 (y : P) (x : Plane) (hx : A ≤ |x.1| ∨ A ≤ |x.2|) : α (y,x) = 0 := by
    by_contra hn
    have hb := hB (subset_tsupport α (show (y,x) ∈ support α from hn))
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] at hb
    rcases hx with hx | hx
    · exact (not_lt_of_ge hx) hb.2.1
    · exact (not_lt_of_ge hx) hb.2.2
  have hvert (y : P) (u : ℝ) (hu : A ≤ |u|) (v w : ℝ) : H (y,(u,v)) = H (y,(u,w)) := by
    have hd (t : ℝ) : HasDerivAt (fun t => H (y,(u,t))) 0 t := by
      have hh := (hHd y (u,t)).comp_hasDerivAt t
        ((hasDerivAt_const t u).prodMk (hasDerivAt_id t))
      exact hh.congr_deriv (by rw [ha0 y (u,t) (Or.inl hu)]; rfl)
    exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) v w
  have hhor (y : P) (v : ℝ) (hv : A ≤ |v|) (u w : ℝ) : H (y,(u,v)) = H (y,(w,v)) := by
    have hd (t : ℝ) : HasDerivAt (fun t => H (y,(t,v))) 0 t := by
      have hh := (hHd y (t,v)).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t v))
      exact hh.congr_deriv (by rw [ha0 y (t,v) (Or.inr hv)]; rfl)
    exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) u w
  have hAB : A ≤ |B| := le_trans (by dsimp [B] <;> linarith) (le_abs_self B)
  have hout (y : P) (x : Plane) (hx : A ≤ |x.1| ∨ A ≤ |x.2|) : H (y,x) = 0 := by
    have he : H (y,x) = H (y,(B,B)) := by
      rcases hx with hx | hx
      · exact (hvert y x.1 hx x.2 B).trans (hhor y B hAB x.1 B)
      · exact (hhor y x.2 hx x.1 B).trans (hvert y B hAB x.2 B)
    rw [he]
    simp only [H,rectangularPotential,intervalIntegral.integral_same,zero_add]
  refine ⟨H,rectangularPotential_smooth hα B,?_,hHd,hzero⟩
  apply HasCompactSupport.intro ((hαc.image continuous_fst).prod
    (isCompact_Icc : IsCompact (Icc (-A,-A) (A,A) : Set Plane)))
  intro p hp
  by_cases hy : p.1 ∈ Prod.fst '' tsupport α
  · apply hout
    have hx : p.2 ∉ Icc (-A,-A) (A,A) := fun h => hp ⟨hy,h⟩
    by_contra! ht
    apply hx
    exact ⟨⟨(abs_lt.mp ht.1).1.le,(abs_lt.mp ht.2).1.le⟩,
      ⟨(abs_lt.mp ht.1).2.le,(abs_lt.mp ht.2).2.le⟩⟩
  · apply hzero
    intro x
    exact image_eq_zero_of_notMem_tsupport (f := α) (x := (p.1,x))
      (fun h => hy ⟨(p.1,x),h,rfl⟩)

theorem compact_potential_zero_outside {H : Plane → ℝ} {α : Plane → Plane →L[ℝ] ℝ}
    (hHc : HasCompactSupport H) (hd : ∀ x, HasFDerivAt H (α x) x)
    {T : ℝ} (hT : 0 < T) (ha : ∀ x, T ≤ radiusSq x → α x = 0)
    (x : Plane) (hx : T ≤ radiusSq x) : H x = 0 := by
  have hx0 : x ≠ 0 := by
    intro he
    subst x
    simp [radiusSq] at hx
    linarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let γ : ℝ → Plane := fun t => (1+t^2) • x
  have hγ (t : ℝ) : T ≤ radiusSq (γ t) := by
    dsimp [γ]
    rw [radiusSq_smul]
    have ht := sq_nonneg t
    have hxz := radiusSq_nonneg x
    nlinarith [sq_nonneg (t^2)]
  have hg (t : ℝ) : HasDerivAt (fun t => H (γ t)) 0 t := by
    have hgd : HasDerivAt γ ((2*t) • x) t := by
      simpa [γ] using (((hasDerivAt_id t).pow 2).const_add 1).smul_const x
    have hh := (hd (γ t)).comp_hasDerivAt t hgd
    rw [ha (γ t) (hγ t)] at hh
    exact hh.congr_deriv (by simp)
  have he (t : ℝ) : H x = H (γ t) := by
    have hh := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv) 0 t
    simpa [γ] using hh
  obtain ⟨A,hA,hB⟩ := hHc.isBounded.subset_ball_lt 1 (0 : Plane)
  let t := Real.sqrt (A/‖x‖)
  have ht : t^2 = A/‖x‖ := Real.sq_sqrt (by positivity)
  rw [he t]
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hb := hB hs
  simp only [Metric.mem_ball, dist_zero_right] at hb
  have hn : ‖γ t‖ = A+‖x‖ := by
    dsimp [γ]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),ht]
    field_simp
    ring
  rw [hn] at hb
  linarith

theorem exists_parametric_disk_closed_primitive {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    {R : ℝ} (_hR : 0 < R) (hαs : tsupport α ⊆ univ ×ˢ roundDisk R)
    (hclosed : ∀ y x v w, fderiv ℝ (fun x => α (y,x)) x v w =
      fderiv ℝ (fun x => α (y,x)) x w v) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x, HasFDerivAt (fun x => H (y,x)) (α (y,x)) x) ∧
      ∀ y, (∀ x, α (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  obtain ⟨H,hH,hHc,hd,hzero⟩ := exists_parametric_closed_primitive hα hαc hclosed
  refine ⟨H,hH,hHc,?_,hd,hzero⟩
  by_cases hs : (tsupport α).Nonempty
  · obtain ⟨p,hp,hmax⟩ := hαc.exists_isMaxOn hs
      (radiusSq_smooth.continuous.comp continuous_snd).continuousOn
    have hpr : radiusSq p.2 < R^2 := (hαs hp).2
    let T := (radiusSq p.2+R^2)/2
    have hT : 0 < T := by dsimp [T] <;> nlinarith [radiusSq_nonneg p.2]
    have hpT : radiusSq p.2 < T := by dsimp [T] <;> linarith
    have hTR : T < R^2 := by dsimp [T] <;> linarith
    have ha (y : P) (x : Plane) (hx : T ≤ radiusSq x) : α (y,x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hh := hmax hm
      change radiusSq x ≤ radiusSq p.2 at hh
      linarith
    have hsupport : tsupport H ⊆ {p : P × Plane | radiusSq p.2 ≤ T} := by
      apply closure_minimal _ (isClosed_le (radiusSq_smooth.continuous.comp continuous_snd) continuous_const)
      intro q hq
      by_contra hn
      have hn' : T ≤ radiusSq q.2 := le_of_not_ge hn
      exact hq (compact_potential_zero_outside (compactSupport_fiber hHc q.1)
        (hd q.1) hT (ha q.1) q.2 hn')
    intro q hq
    exact ⟨trivial,lt_of_le_of_lt (hsupport hq) hTR⟩
  · have hα0 (y : P) (x : Plane) : α (y,x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hs ⟨(y,x),h⟩)
    have hHz : H = 0 := funext (fun p => hzero p.1 (hα0 p.1) p.2)
    simp [hHz]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_none _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhase_some _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.realPhaseDerivative_one _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseJ_sq _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseSq_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem familyGenerator_smooth (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2)) (v : P) :
    ContDiff ℝ ∞ (familyGenerator φ v) :=
  ((hφ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp (contDiff_fst.prodMk hφi)).clm_apply contDiff_const

theorem fderiv_apply_const {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → G}
    (hF : ContDiff ℝ ∞ F) (p v w : E) :
    fderiv ℝ (fun p => fderiv ℝ F p v) p w = fderiv ℝ (fderiv ℝ F) p w v := by
  have hFd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := (hFd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)
  rw [hh.fderiv]
  simp

theorem family_symplectic_variation {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F)
    (hsp : ∀ y x u w, planarArea (fderiv ℝ (fun x => F (y,x)) x u)
      (fderiv ℝ (fun x => F (y,x)) x w) = planarArea u w)
    (y v : P) (x u w : Plane) :
    planarArea (fderiv ℝ (fderiv ℝ F) (y,x) (0,u) (v,0))
        (fderiv ℝ F (y,x) (0,w)) +
      planarArea (fderiv ℝ F (y,x) (0,u))
        (fderiv ℝ (fderiv ℝ F) (y,x) (0,w) (v,0)) = 0 := by
  have hFdd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hFd := hFdd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf (d : Plane) : Differentiable ℝ (fun p : P × Plane => fderiv ℝ F p (0,d)) :=
    hFd.clm_apply (differentiable_const _)
  have he : (fun p : P × Plane => planarArea (fderiv ℝ F p (0,u))
      (fderiv ℝ F p (0,w))) = fun _ => planarArea u w := by
    funext p
    have hh := hsp p.1 p.2 u w
    simpa only [family_spatial_fderiv hF,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hh
  have hd := planarArea.hasFDerivAt_of_bilinear ((hf u (y,x)).hasFDerivAt)
    ((hf w (y,x)).hasFDerivAt)
  have hz := hd.fderiv
  rw [he,fderiv_const_apply] at hz
  have hh := congrArg (fun A : P × Plane →L[ℝ] ℝ => A (v,0)) hz
  simp only [zero_apply,add_apply,ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply,fderiv_apply_const hF] at hh
  have hs : IsSymmSndFDerivAt ℝ F (y,x) := hF.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq (v,0) (0,u),hs.eq (v,0) (0,w)] at hh
  linarith

theorem familyGenerator_fderiv_image (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (y v : P) (x u : Plane) :
    fderiv ℝ (fun z => familyGenerator φ v (y,z)) (φ y x) (fderiv ℝ (φ y) x u) =
      fderiv ℝ (fderiv ℝ (fun p : P × Plane => φ p.1 p.2)) (y,x) (0,u) (v,0) := by
  let F : P × Plane → Plane := fun p => φ p.1 p.2
  let V : P × Plane → Plane := fun p => fderiv ℝ F p (v,0)
  have hFD : ContDiff ℝ ∞ (fderiv ℝ F) := hφ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV : ContDiff ℝ ∞ V := hFD.clm_apply contDiff_const
  have hG := familyGenerator_smooth φ hφ hφi v
  have hGy : Differentiable ℝ (fun z => familyGenerator φ v (y,z)) :=
    (hG.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hφy : Differentiable ℝ (φ y) :=
    (hφ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (fun z => familyGenerator φ v (y,φ y z)) = fun z => V (y,z) := by
    funext z
    simp [familyGenerator,V,F]
  have hc := fderiv_comp x (hGy (φ y x)) (hφy x)
  have hec : ((fun z => familyGenerator φ v (y,z)) ∘ φ y) = fun z => V (y,z) := he
  rw [hec,family_spatial_fderiv hV] at hc
  have hh := congrArg (fun A : Plane →L[ℝ] Plane => A u) hc.symm
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    V,fderiv_apply_const (F := F) hφ,F] using hh

theorem family_fderiv_right_inverse (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (y : P) (z u : Plane) :
    fderiv ℝ (φ y) ((φ y).symm z) (fderiv ℝ (φ y).symm z u) = u := by
  have hφy : Differentiable ℝ (φ y) :=
    (hφ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hφyi : Differentiable ℝ (φ y).symm :=
    (hφi.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := fderiv_comp z (hφy ((φ y).symm z)) (hφyi z)
  have hid : ((φ y) ∘ (φ y).symm) = id := funext (fun z => (φ y).apply_symm_apply z)
  rw [hid,fderiv_id] at he
  have hh := congrArg (fun A : Plane →L[ℝ] Plane => A u) he.symm
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh

theorem familyGenerator_infinitesimal (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hsp : ∀ y x u w, planarArea (fderiv ℝ (φ y) x u)
      (fderiv ℝ (φ y) x w) = planarArea u w)
    (y v : P) (z u w : Plane) :
    planarArea (fderiv ℝ (fun z => familyGenerator φ v (y,z)) z u) w +
      planarArea u (fderiv ℝ (fun z => familyGenerator φ v (y,z)) z w) = 0 := by
  let x := (φ y).symm z
  let a := fderiv ℝ (φ y).symm z u
  let b := fderiv ℝ (φ y).symm z w
  have hu : fderiv ℝ (φ y) x a = u := family_fderiv_right_inverse φ hφ hφi y z u
  have hw : fderiv ℝ (φ y) x b = w := family_fderiv_right_inverse φ hφ hφi y z w
  have hvu := familyGenerator_fderiv_image φ hφ hφi y v x a
  have hvw := familyGenerator_fderiv_image φ hφ hφi y v x b
  have he : φ y x = z := (φ y).apply_symm_apply z
  rw [he,hu] at hvu
  rw [he,hw] at hvw
  have hh := family_symplectic_variation hφ hsp y v x a b
  have hfu : fderiv ℝ (fun p : P × Plane => φ p.1 p.2) (y,x) (0,a) = u := by
    simpa only [family_spatial_fderiv hφ,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hu
  have hfw : fderiv ℝ (fun p : P × Plane => φ p.1 p.2) (y,x) (0,b) = w := by
    simpa only [family_spatial_fderiv hφ,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hw
  rw [hfu,hfw,← hvu,← hvw] at hh
  exact hh

theorem familyGenerator_support (φ : P → Plane ≃ₜ Plane) (v : P) :
    tsupport (familyGenerator φ v) ⊆ tsupport (fun p : P × Plane => φ p.1 p.2-p.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hfix : φ p.1 p.2 = p.2 := sub_eq_zero.mp
    (image_eq_zero_of_notMem_tsupport (f := fun p : P × Plane => φ p.1 p.2-p.2) hn)
  have hinv : (φ p.1).symm p.2 = p.2 := by
    apply (φ p.1).injective
    rw [(φ p.1).apply_symm_apply,hfix]
  have he : (fun q : P × Plane => φ q.1 q.2) =ᶠ[𝓝 p] Prod.snd := by
    filter_upwards [(isClosed_tsupport (fun p : P × Plane => φ p.1 p.2-p.2)).isOpen_compl.mem_nhds hn] with q hq
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => φ p.1 p.2-p.2) hq)
  apply hp
  dsimp [familyGenerator]
  rw [hinv,show (p.1,p.2) = p from Prod.eta p,he.fderiv_eq]
  rw [fderiv_snd]
  rfl

variable [FiniteDimensional ℝ P]

theorem exists_hamiltonian_of_symplectic_family (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hφc : HasCompactSupport (fun p : P × Plane => φ p.1 p.2-p.2))
    {R : ℝ} (hR : 0 < R)
    (hφs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hsp : ∀ y x u w, planarArea (fderiv ℝ (φ y) x u)
      (fderiv ℝ (φ y) x w) = planarArea u w) (v : P) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x, HasFDerivAt (fun x => H (y,x)) (-planarArea (familyGenerator φ v (y,x))) x) ∧
      ∀ y, (∀ x, familyGenerator φ v (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  let α : P × Plane → Plane →L[ℝ] ℝ := fun p => -planarArea (familyGenerator φ v p)
  have hG := familyGenerator_smooth φ hφ hφi v
  have hα : ContDiff ℝ ∞ α := (planarArea.contDiff.comp hG).neg
  have hsα : tsupport α ⊆ tsupport (fun p : P × Plane => φ p.1 p.2-p.2) := by
    apply Subset.trans _ (familyGenerator_support φ v)
    apply closure_minimal _ (isClosed_tsupport _)
    intro p hp
    by_contra hn
    apply hp
    simp [α,image_eq_zero_of_notMem_tsupport (f := familyGenerator φ v) hn]
  have hαc : HasCompactSupport α := hφc.of_isClosed_subset (isClosed_tsupport _) hsα
  have hαs : tsupport α ⊆ univ ×ˢ roundDisk R := hsα.trans hφs
  have hd (y : P) (x : Plane) : fderiv ℝ (fun x => α (y,x)) x =
      -(planarArea.comp (fderiv ℝ (fun x => familyGenerator φ v (y,x)) x)) := by
    have hGy := (hG.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact ((planarArea.hasFDerivAt.comp x (hGy x).hasFDerivAt).neg).fderiv
  have hclosed (y : P) (x u w : Plane) :
      fderiv ℝ (fun x => α (y,x)) x u w = fderiv ℝ (fun x => α (y,x)) x w u := by
    rw [hd]
    simp only [neg_apply,ContinuousLinearMap.comp_apply]
    have hh := familyGenerator_infinitesimal φ hφ hφi hsp y v x u w
    have hskew (a b : Plane) : planarArea a b = -planarArea b a := by
      simp only [planarArea_apply]
      ring
    rw [hskew u] at hh
    linarith
  obtain ⟨H,hH,hHc,hHs,hHd,hH0⟩ := exists_parametric_disk_closed_primitive hα hαc hR hαs hclosed
  refine ⟨H,hH,hHc,hHs,hHd,?_⟩
  intro y hy
  apply hH0
  intro x
  simp [α,hy]


end

open scoped ContDiff Topology NNReal
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_NormalizedRoundedBoxes
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


namespace SupportedSmoothIsotopyFamily

theorem joint_support {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    tsupport (fun p : (P × ℝ) × E => Φ.map p.1.1 p.1.2 p.2-p.2) ⊆
      univ ×ˢ Φ.support := by
  apply closure_minimal _ (isClosed_univ.prod Φ.compact_support.isClosed)
  intro p hp
  refine ⟨mem_univ _,?_⟩
  by_contra hn
  exact hp (sub_eq_zero.mpr (Φ.fixed p.1.1 p.1.2 p.2 hn))

theorem timeCutoff_hasCompactSupport {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (ρ : P × ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    HasCompactSupport (fun p : (P × ℝ) × E =>
      (Φ.timeCutoff ρ hρ).map p.1.1 p.1.2 p.2-p.2) := by
  apply HasCompactSupport.intro (hρc.prod Φ.compact_support)
  intro p hp
  by_cases h : p.1 ∈ tsupport ρ
  · have hn : p.2 ∉ Φ.support := fun hx => hp ⟨h,hx⟩
    exact sub_eq_zero.mpr (Φ.fixed p.1.1 (ρ p.1*p.1.2) p.2 hn)
  · have hz := image_eq_zero_of_notMem_tsupport h
    simp only [timeCutoff,Prod.eta,hz,zero_mul,Φ.zero,Homeomorph.refl_apply,id_eq,sub_self]

variable [FiniteDimensional ℝ P]

theorem exists_joint_compact {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (Y : Set P) (hY : IsCompact Y) :
    ∃ Ψ : SupportedSmoothIsotopyFamily P E W,
      HasCompactSupport (fun p : (P × ℝ) × E => Ψ.map p.1.1 p.1.2 p.2-p.2) ∧
      (∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, Ψ.map y t = Φ.map y t) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := exists_smooth_cutoff (hY.prod isCompact_Icc)
    isOpen_univ (subset_univ (Y ×ˢ Icc (0:ℝ) 1))
  refine ⟨Φ.timeCutoff ρ hρ,Φ.timeCutoff_hasCompactSupport ρ hρ hρc,?_⟩
  intro y hy t ht
  have hh : ρ (y,t) = 1 := (Filter.Eventually.self_of_nhdsSet hρ1) (y,t) ⟨hy,ht⟩
  change Φ.map y (ρ (y,t)*t) = Φ.map y t
  rw [hh,one_mul]

end SupportedSmoothIsotopyFamily

end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parameter_relative_circle_primitive
    {alpha : P × Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hac : HasCompactSupport alpha) {R delta : ℝ}
    (hR : 0 < R) (hd : 0 < delta) (hdR : delta < R^2) (Y : Set P)
    (hz : ∀ y ∈ Y, (∫ p in roundDisk R, planarCurl (fun x => alpha (y,x)) p) = 0) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ y p, delta ≤ |radiusSq p-R^2| → H (y,p) = 0) ∧
      (∀ y ∈ Y, ∀ t, fderiv ℝ (fun x => H (y,x)) (polarCoord.symm (R,t))
        (-R*Real.sin t,R*Real.cos t) = circlePullback (fun x => alpha (y,x)) R t) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  let a : P × ℝ → ℝ := fun p => circlePullback (fun x => alpha (p.1,x)) R p.2
  have has : ContDiff ℝ ∞ a := circlePullback_parameter_smooth ha R
  let m : P → ℝ := fun y => (∫ t in -Real.pi..Real.pi, a (y,t))/(2*Real.pi)
  have hms : ContDiff ℝ ∞ m :=
    ((contDiff_parameter_segment_integral has (-Real.pi)).comp
      (contDiff_id.prodMk contDiff_const)).div_const _
  let b : P × ℝ → ℝ := fun p => a p-m p.1
  have hbs : ContDiff ℝ ∞ b := has.sub (hms.comp contDiff_fst)
  have hby (y : P) : ContDiff ℝ ∞ (fun t => b (y,t)) :=
    hbs.comp (contDiff_const.prodMk contDiff_id)
  have hmY (y : P) (hy : y ∈ Y) : m y = 0 := by
    have hai : ContDiff ℝ ∞ (fun x : Plane => alpha (y,x)) :=
      ha.comp (contDiff_const.prodMk contDiff_id)
    have hz' := (integral_curl_roundDisk hai hR).symm.trans (hz y hy)
    change (∫ t in -Real.pi..Real.pi, circlePullback (fun x => alpha (y,x)) R t) / (2*Real.pi) = 0
    exact div_eq_zero_iff.mpr (Or.inl hz')
  have hb0 (y : P) : (∫ t in -Real.pi..Real.pi, b (y,t)) = 0 := by
    have hai : IntervalIntegrable (fun t => a (y,t)) volume (-Real.pi) Real.pi :=
      (has.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    simp only [b]
    rw [intervalIntegral.integral_sub hai intervalIntegrable_const,intervalIntegral.integral_const]
    dsimp [m]
    field_simp
    ring
  have hbp (y : P) : Periodic (fun t => b (y,t)) (2*Real.pi) := by
    intro t
    dsimp [b,a]
    rw [circlePullback_periodic (fun x => alpha (y,x)) R t]
  have hp (y : P) := periodicPrimitive_periodic (hby y).continuous (hbp y) (hb0 y)
  let H : P × Plane → ℝ := fun p =>
    angularExtension R delta hd (periodicPrimitive (fun t => b (p.1,t))) p.2
  have hH : ContDiff ℝ ∞ H := angularExtension_parameter_smooth hd hdR
    (contDiff_parameter_segment_integral hbs (-Real.pi)) hp
  have hbzero (y : P) (hy : ∀ x, alpha (y,x) = 0) : (fun t => b (y,t)) = fun _ => (0:ℝ) := by
    have ha0 : (fun t => a (y,t)) = fun _ => (0:ℝ) := by
      funext t
      simp only [a,circlePullback,hy,zero_apply]
    funext t
    change a (y,t) - (∫ t in -Real.pi..Real.pi, a (y,t))/(2*Real.pi) = 0
    rw [ha0,congrFun ha0 t]
    simp only [intervalIntegral.integral_zero,zero_div,sub_self]
  have hHc : HasCompactSupport H := by
    have hK : IsCompact (Prod.fst '' tsupport alpha) := hac.image continuous_fst
    apply angularExtension_parameter_compact (h := fun p =>
      periodicPrimitive (fun t => b (p.1,t)) p.2) (K := Prod.fst '' tsupport alpha) hd hK
    intro y hy t
    have he := hbzero y (fun x => image_eq_zero_of_notMem_tsupport
      (fun h => hy ⟨(y,x),h,rfl⟩))
    change periodicPrimitive (fun t => b (y,t)) t = 0
    rw [he]
    simp only [periodicPrimitive,intervalIntegral.integral_zero]
  refine ⟨H,hH,hHc,fun _ p hp => angularExtension_zero hd _ p hp,?_,?_⟩
  · intro y hy t
    have hc : HasDerivAt (fun t => polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) t := by
      change HasDerivAt (fun t => (R*Real.cos t,R*Real.sin t)) _ t
      exact (((Real.hasDerivAt_cos t).const_mul R).prodMk
        ((Real.hasDerivAt_sin t).const_mul R)).congr_deriv (by ext <;> simp [neg_mul])
    have hHy : ContDiff ℝ ∞ (fun x => H (y,x)) := hH.comp (contDiff_const.prodMk contDiff_id)
    have hdH := ((hHy.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (polarCoord.symm (R,t))).hasFDerivAt.comp_hasDerivAt t hc
    have he : (fun t => H (y,polarCoord.symm (R,t))) = periodicPrimitive (fun t => b (y,t)) :=
      funext fun t => angularExtension_polar hR hd (hp y) t
    change HasDerivAt (fun t => H (y,polarCoord.symm (R,t))) _ t at hdH
    rw [he] at hdH
    simpa only [b,hmY y hy,sub_zero,a] using
      hdH.unique (periodicPrimitive_hasDerivAt (hby y).continuous t)
  · intro y hy x
    change angularExtension R delta hd (periodicPrimitive (fun t => b (y,t))) x = 0
    rw [hbzero y hy]
    simp only [angularExtension,periodicPrimitive,intervalIntegral.integral_zero,mul_zero]

omit [FiniteDimensional ℝ P] in
theorem parameter_relative_finite_potential_correction {ι : Type*} [Fintype ι]
    {alpha : P × Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (Y : Set P) (R : ι → ℝ)
    (H : ι → P × Plane → ℝ) (hHs : ∀ i, ContDiff ℝ ∞ (H i))
    (hHc : ∀ i, HasCompactSupport (H i))
    (hself : ∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 →
      fderiv ℝ (fun x => H i (y,x)) p (-p.2,p.1) = alpha (y,p) (-p.2,p.1))
    (hother : ∀ i j, j ≠ i → ∀ y p, radiusSq p = (R i)^2 →
      fderiv ℝ (fun x => H j (y,x)) p = 0)
    (hHzero : ∀ i y, (∀ x, alpha (y,x) = 0) → ∀ x, H i (y,x) = 0) :
    ∃ beta : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ y p, planarCurl (fun x => beta (y,x)) p = planarCurl (fun x => alpha (y,x)) p) ∧
      (∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 → beta (y,p) (-p.2,p.1) = 0) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, beta (y,x) = 0 := by
  classical
  let F : P × Plane → ℝ := fun p => ∑ i, H i p
  have hFs : ContDiff ℝ ∞ F := ContDiff.sum (fun i _ => hHs i)
  have hFc : HasCompactSupport F := by
    have he : (∑ i, H i) = F := by funext p; simp [F]
    rw [← he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (f := H) (fun i _ => hHc i)
  have hFd (y : P) (p v : Plane) :
      fderiv ℝ (fun x => F (y,x)) p v = ∑ i, fderiv ℝ (fun x => H i (y,x)) p v := by
    change fderiv ℝ (fun x => ∑ i, H i (y,x)) p v = _
    have hHyi (i : ι) : DifferentiableAt ℝ (fun x : Plane => H i (y,x)) p :=
      (((hHs i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p
    rw [fderiv_fun_sum (fun i _ => hHyi i)]
    simp only [sum_apply]
  let beta : P × Plane → Plane →L[ℝ] ℝ := fun p => alpha p - fderiv ℝ (fun x => F (p.1,x)) p.2
  refine ⟨beta,ha.sub (fiber_fderiv_smooth hFs),hac.sub (fiber_fderiv_compact hFs hFc),?_,?_,?_⟩
  · intro y p
    exact planarCurl_sub_differential (ha.comp (contDiff_const.prodMk contDiff_id))
      (hFs.comp (contDiff_const.prodMk contDiff_id)) p
  · intro i y hy p hp
    change alpha (y,p) (-p.2,p.1) - fderiv ℝ (fun x => F (y,x)) p (-p.2,p.1) = 0
    rw [hFd,Finset.sum_eq_single i,hself i y hy p hp,sub_self]
    · intro j _ hj
      rw [hother i j hj y p hp]
      rfl
    · simp

  · intro y hy x
    have he : (fun x => F (y,x)) = fun _ => (0:ℝ) := by
      funext q
      exact Finset.sum_eq_zero (fun i _ => hHzero i y hy q)
    change alpha (y,x) - fderiv ℝ (fun x => F (y,x)) x = 0
    rw [hy x,he,fderiv_const_apply,sub_self]

theorem exists_parameter_relative_finite_circle_correction {ι : Type*} [Fintype ι]
    {alpha : P × Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hRi : Injective R)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (R i), planarCurl (fun x => alpha (y,x)) p) = 0) :
    ∃ beta : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ y p, planarCurl (fun x => beta (y,x)) p = planarCurl (fun x => alpha (y,x)) p) ∧
      (∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 → beta (y,p) (-p.2,p.1) = 0) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, beta (y,x) = 0 := by
  classical
  choose d hd hdR hdsep using exists_disjoint_radial_collars R hR hRi
  choose H hHs hHc hHspt hHt hHzero using fun i =>
    exists_parameter_relative_circle_primitive ha hac (hR i) (hd i) (hdR i) Y (hz i)
  apply parameter_relative_finite_potential_correction ha hac Y R H hHs hHc
      (hHzero := hHzero)
  · intro i y hy p hp
    obtain ⟨t,rfl⟩ := polar_surjective_circle (hR i) hp
    simpa only [circlePullback,polarCoord_symm_apply,neg_mul] using hHt i y hy t
  · intro i j hj y p hp
    apply fderiv_zero_outside_collar (hHspt j y)
    rw [hp]
    exact hdsep j i hj.symm


end

open scoped ContDiff Topology NNReal
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parameter_relative_density_transport {ι : Type*} {L : ℝ≥0}
    (X : C(ℝ × (P × Plane),Plane)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    (ρ : P → ℝ × Plane → ℝ) (hρ : ∀ y, ContDiff ℝ ∞ (ρ y))
    (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hPDE : ∀ y p v w, fderiv ℝ (ρ y) p (1,fiberField X y p) * B v w +
      ρ y p * (B (fderiv ℝ (fiberField X y) p (0,v)) w +
        B v (fderiv ℝ (fiberField X y) p (0,w))) = 0)
    (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (htan : ∀ i y, y ∈ Y → ∀ t x, radiusSq x = (R i)^2 → radialDrift (fiberField X y) (t,x) = 0)
    (t T : ℝ) : ∃ Φ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Φ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Φ p.1 p.2 - p.2) ∧
      (∀ y x v w, ρ y (t+T,Φ y x) * B (fderiv ℝ (Φ y) x v) (fderiv ℝ (Φ y) x w) =
        ρ y (t,x) * B v w) ∧
      (∀ i y, y ∈ Y → Φ y '' closedRoundDisk (R i) = closedRoundDisk (R i)) ∧
      ∀ y, (∀ t x, X (t,(y,x)) = 0) → ∀ x, Φ y x = x := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T/(N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ (y : P) := timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
    (fiberField_smooth X hXs y) hh t N
  have hK : IsCompact (Prod.snd '' tsupport X) := hXc.image continuous_snd
  have hfix (p : P × Plane) (hp : p ∉ Prod.snd '' tsupport X) : Φ p.1 p.2 = p.2 := by
    apply timeSteps_of_stationary
    intro s
    change X (s,p) = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(s,p),h,rfl⟩)
  refine ⟨Φ,(timeSteps_fiber_smooth X hX hXs hh t N).1,
    (timeSteps_fiber_smooth X hX hXs hh t N).2,
    HasCompactSupport.intro hK (fun p hp => sub_eq_zero.mpr (hfix p hp)),?_,?_,?_⟩
  · intro y x v w
    simpa only [he] using timeSteps_preserves_density (fiberField X y)
      (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y)
      (ρ y) (hρ y) B (hPDE y) hh t N x v w
  · intro i y hy
    apply homeomorph_image_closedRoundDisk
    intro x
    exact timeSteps_preserves_circle_iff (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (fiberField_compact X hXc y) (hR i) (htan i y hy) hh t N x

  · intro y hy x
    apply timeSteps_of_stationary
    intro s
    exact hy s x

theorem exists_parameter_relative_primitive {ι : Type*} [Fintype ι]
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : ∀ y, (∫ p, f (y,p)) = 0)
    (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (R i), f (y,p)) = 0) :
    ∃ U V : P × Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y p, deriv (fun x => V (y,(x,p.2))) p.1 -
        deriv (fun t => U (y,(p.1,t))) p.2 = f (y,p)) ∧
      (∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 → -p.2*U (y,p)+p.1*V (y,p) = 0) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, U (y,x) = 0 ∧ V (y,x) = 0 := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,huvzero⟩ := exists_parametric_compact_primitive hf hfc hf0
  let alpha : P × Plane → Plane →L[ℝ] ℝ := fun p =>
    coordinateForm (fun x => U (p.1,x)) (fun x => V (p.1,x)) p.2
  have has : ContDiff ℝ ∞ alpha :=
    (hU.smul contDiff_const).add (hV.smul contDiff_const)
  have hac : HasCompactSupport alpha := by
    apply HasCompactSupport.intro (hUc.union hVc)
    intro p hp
    have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
    have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
    change U p • _ + V p • _ = 0
    rw [hu,hv,zero_smul,zero_smul,zero_add]
  have hc (y : P) (p : Plane) : planarCurl (fun x => alpha (y,x)) p = f (y,p) :=
    (coordinateForm_curl (hU.comp (contDiff_const.prodMk contDiff_id))
      (hV.comp (contDiff_const.prodMk contDiff_id)) p).trans (hcurl y p)
  have hz' (i : ι) (y : P) (hy : y ∈ Y) : (∫ p in roundDisk (R i), planarCurl (fun x => alpha (y,x)) p) = 0 := by
    simp_rw [hc]
    exact hz i y hy
  obtain ⟨beta,hbs,hbc,hcurlb,hbt,hbzero⟩ :=
    exists_parameter_relative_finite_circle_correction has hac Y R hR hRi hz'
  let U' : P × Plane → ℝ := fun p => beta p (1,0)
  let V' : P × Plane → ℝ := fun p => beta p (0,1)
  have hUs : ContDiff ℝ ∞ U' := hbs.clm_apply contDiff_const
  have hVs : ContDiff ℝ ∞ V' := hbs.clm_apply contDiff_const
  have hU'c : HasCompactSupport U' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [U',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hV'c : HasCompactSupport V' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [V',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hUy (y : P) : ContDiff ℝ ∞ (fun x => U' (y,x)) := hUs.comp (contDiff_const.prodMk contDiff_id)
  have hVy (y : P) : ContDiff ℝ ∞ (fun x => V' (y,x)) := hVs.comp (contDiff_const.prodMk contDiff_id)
  have hby (y : P) : ContDiff ℝ ∞ (fun x => beta (y,x)) := hbs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨U',V',hUs,hVs,hU'c,hV'c,?_,?_,?_⟩
  · intro y p
    rw [plane_deriv_first ((hVy y).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
      plane_deriv_second ((hUy y).differentiable (by simp))]
    change fderiv ℝ (fun q => beta (y,q) (0,1)) p (1,0) -
      fderiv ℝ (fun q => beta (y,q) (1,0)) p (0,1) = f (y,p)
    rw [form_eval_fderiv (hby y),form_eval_fderiv (hby y)]
    exact (hcurlb y p).trans (hc y p)
  · intro i y hy p hp
    have he : (-p.2,p.1) = (-p.2) • ((1:ℝ),(0:ℝ)) + p.1 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    have ht := hbt i y hy p hp
    rw [he,map_add,map_smul,map_smul] at ht
    exact ht

  · intro y hy x
    have ha0 (q : Plane) : alpha (y,q) = 0 := by
      obtain ⟨hu,hv⟩ := huvzero y hy q
      simp only [alpha,coordinateForm,hu,hv,zero_smul,zero_add]
    have hb0 := hbzero y ha0 x
    simp only [U',V',hb0,zero_apply,and_self]

theorem exists_parameter_relative_background_moser {ι : Type*} [Fintype ι]
    {g f : P × Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : ∀ y, (∫ p, f (y,p)) = 0)
    (hgpos : ∀ p, 0 < g p) (hpos : ∀ p, 0 < g p+f p)
    (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (R i), f (y,p)) = 0) :
    ∃ Φ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Φ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Φ p.1 p.2-p.2) ∧
      (∀ y x v w, (g (y,Φ y x)+f (y,Φ y x)) *
        planarArea (fderiv ℝ (Φ y) x v) (fderiv ℝ (Φ y) x w) = g (y,x)*planarArea v w) ∧
      (∀ i y, y ∈ Y → Φ y '' closedRoundDisk (R i) = closedRoundDisk (R i)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, Φ y x = x := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,htan,huvzero⟩ :=
    exists_parameter_relative_primitive hf hfc hf0 Y R hR hRi hz
  let field : ℝ × (P × Plane) → Plane := fun p =>
    backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
      (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)
  have hXs : ContDiff ℝ ∞ field := parametric_backgroundField_smooth hg hf hU hV hgpos hpos
  have hXc : HasCompactSupport field := parametric_backgroundField_compact hUc hVc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let X : C(ℝ × (P × Plane),Plane) := ⟨field,hXs.continuous⟩
  have hgy (y : P) : ContDiff ℝ ∞ (fun x => g (y,x)) := hg.comp (contDiff_const.prodMk contDiff_id)
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hUy (y : P) : ContDiff ℝ ∞ (fun x => U (y,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
  have hVy (y : P) : ContDiff ℝ ∞ (fun x => V (y,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨Φ,hΦ,hΦi,hΦc,hΦarea,hΦdisk,hΦfix⟩ := exists_parameter_relative_density_transport X hL hXs hXc
    (fun y => backgroundDensity (fun x => g (y,x)) (fun x => f (y,x)))
    (fun y => backgroundDensity_smooth (hgy y) (hfy y)) planarArea
    (fun y => backgroundField_transport (hgy y) (hfy y) (hUy y) (hVy y)
      (fun x => hgpos (y,x)) (fun x => hpos (y,x)) (hcurl y)) Y R hR
    (fun i y hy => backgroundField_tangent (g := fun x => g (y,x))
      (f := fun x => f (y,x)) (htan i y hy)) 0 1
  refine ⟨Φ,hΦ,hΦi,hΦc,?_,hΦdisk,?_⟩
  · intro y x v w
    simpa only [zero_add,backgroundDensity,Real.smoothTransition.one,Real.smoothTransition.zero,
      one_mul,zero_mul,add_zero] using hΦarea y x v w
  · intro y hy x
    apply hΦfix y _ x
    intro t q
    obtain ⟨hu,hv⟩ := huvzero y hy q
    change backgroundField (fun x => g (y,x)) (fun x => f (y,x))
      (fun x => U (y,x)) (fun x => V (y,x)) (t,q) = 0
    simp only [backgroundField,hu,hv,mul_zero,zero_div]
    rfl



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_ParameterRelativeDiskMoser
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull_carrier _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull_radius _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parameter_relative_disk_moser {ι : Type*} [Fintype ι]
    {R : ℝ} (hR : 0 < R) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ univ ×ˢ roundDisk R)
    (hf0 : ∀ y, (∫ p, f (y,p)) = 0) (hpos : ∀ p, 0 < 1+f p)
    (Y : Set P) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (r i), f (y,p)) = 0) :
    ∃ Ψ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x v w, (1+f (y,Ψ y x)) *
        planarArea (fderiv ℝ (Ψ y) x v) (fderiv ℝ (Ψ y) x w) = planarArea v w) ∧
      (∀ i y, y ∈ Y → Ψ y '' closedRoundDisk (r i) = closedRoundDisk (r i)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, Ψ y x = x := by
  let c := radialDiskChart R
  have hcs : c.source = univ := radialDiskChart_source R
  have hct : c.target = roundDisk R := radialDiskChart_target hR
  have hc : ContDiff ℝ ∞ c := radialDiskChart_smooth R
  have hci : ContDiffOn ℝ ∞ c.symm c.target := by
    rw [hct]
    exact radialDiskChart_symm_smooth hR
  let g : P × Plane → ℝ := fun p => radialDiskDensity R p.2
  let F : P × Plane → ℝ := fun p => g p*f (p.1,c p.2)
  have hg : ContDiff ℝ ∞ g := (radialDiskDensity_smooth R).comp contDiff_snd
  have hF : ContDiff ℝ ∞ F := hg.mul (hf.comp (contDiff_fst.prodMk (hc.comp contDiff_snd)))
  have hFc : HasCompactSupport F := radialDisk_pullback_compact hR hfc hfs
  have hF0 (y : P) : (∫ p, F (y,p)) = 0 := by
    change (∫ p, radialDiskDensity R p * (fun x => f (y,x)) (radialDiskChart R p)) = 0
    rw [← radialDiskChart_integral hR (fun x => f (y,x))]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hf0 y]
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (f := f) (fun h => hx (hfs h).2)
  have hgpos (p : P × Plane) : 0 < g p := radialDiskDensity_pos hR p.2
  have hGFpos (p : P × Plane) : 0 < g p+F p := by
    change 0 < g p+g p*f (p.1,c p.2)
    nlinarith only [mul_pos (hgpos p) (hpos (p.1,c p.2))]
  let r' := fun i => diskChartRadius R (r i)
  have hr' (i : ι) : 0 < r' i := diskChartRadius_pos (hr i) (hrR i)
  have hri' : Injective r' := by
    intro i j hij
    apply hri
    exact (diskChartRadius_strictMonoOn hR).injOn ⟨(hr i).le,hrR i⟩ ⟨(hr j).le,hrR j⟩ hij
  have hz' (i : ι) (y : P) (hy : y ∈ Y) : (∫ p in roundDisk (r' i), F (y,p)) = 0 := by
    change (∫ p in roundDisk (diskChartRadius R (r i)),
      radialDiskDensity R p * (fun x => f (y,x)) (radialDiskChart R p)) = 0
    rw [← radialDiskChart_integral_inner hR (hr i).le (hrR i) (fun x => f (y,x))]
    exact hz i y hy
  obtain ⟨Φ,hΦ,hΦi,hΦc,hΦarea,hΦdisk,hΦzero⟩ :=
    exists_parameter_relative_background_moser hg hF hFc hF0 hgpos hGFpos Y r' hr' hri' hz'
  obtain ⟨Ψ,hΨeq,hΨ,hΨi,hΨc,hΨsupp⟩ :=
    Chart.exists_conjugate_family c hcs hc hci Φ hΦ hΦi hΦc
  have hΨfun (y : P) : (Ψ y : Plane → Plane) = Chart.conjugate c (Φ y) := funext (hΨeq y)
  have hΦy (y : P) : ContDiff ℝ ∞ (Φ y) := hΦ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨Ψ,hΨ,hΨi,hΨc,by simpa only [hct] using hΨsupp,?_,?_,?_⟩
  · intro y x v w
    by_cases hx : x ∈ c.target
    · let q := c.symm x
      let v' := fderiv ℝ c.symm x v
      let w' := fderiv ℝ c.symm x w
      have hcq : c q = x := c.right_inv hx
      have hv : fderiv ℝ c q v' = v := Chart.chart_fderiv_right_inverse c hc hci hx v
      have hw : fderiv ℝ c q w' = w := Chart.chart_fderiv_right_inverse c hc hci hx w
      have hΨx : Ψ y x = c (Φ y q) := by
        rw [hΨeq y x,Chart.conjugate_of_mem c _ hx]
      have hdv : fderiv ℝ (Ψ y) x v = fderiv ℝ c (Φ y q) (fderiv ℝ (Φ y) q v') := by
        calc
          _ = fderiv ℝ (Ψ y) (c q) (fderiv ℝ c q v') := by rw [hcq,hv]
          _ = _ := by rw [hΨfun]; exact Chart.conjugate_fderiv_chart c hcs hc hci (Φ y) (hΦy y) q v'
      have hdw : fderiv ℝ (Ψ y) x w = fderiv ℝ c (Φ y q) (fderiv ℝ (Φ y) q w') := by
        calc
          _ = fderiv ℝ (Ψ y) (c q) (fderiv ℝ c q w') := by rw [hcq,hw]
          _ = _ := by rw [hΨfun]; exact Chart.conjugate_fderiv_chart c hcs hc hci (Φ y) (hΦy y) q w'
      rw [hΨx,hdv,hdw,radialDiskChart_area hR]
      have hA := hΦarea y q v' w'
      have hB := radialDiskChart_area hR q v' w'
      change planarArea (fderiv ℝ c q v') (fderiv ℝ c q w') = g (y,q)*planarArea v' w' at hB
      rw [hv,hw] at hB
      rw [hB]
      convert hA using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [F,g]
      ring
    · have hn : (y,x) ∉ tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2) :=
        fun h => hx (hΨsupp h).2
      have he : Ψ y =ᶠ[𝓝 x] id := by
        have hnhood := (isClosed_tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2)).isOpen_compl.mem_nhds hn
        have hh := (continuous_const.prodMk continuous_id).tendsto x hnhood
        filter_upwards [hh] with z hz
        exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
          (f := fun p : P × Plane => Ψ p.1 p.2-p.2) hz)
      have hfx : f (y,x) = 0 := image_eq_zero_of_notMem_tsupport
        (f := f) (fun h => hx (by rw [hct]; exact (hfs h).2))
      rw [he.eq_of_nhds,he.fderiv_eq,fderiv_id,ContinuousLinearMap.id_apply,
        ContinuousLinearMap.id_apply, id_eq,hfx,add_zero,one_mul]
  · intro i y hy
    rw [hΨfun,← radialDiskChart_image_closed hR (hr i).le (hrR i),
      Chart.conjugate_image c hcs,hΦdisk i y hy]
  · intro y hy x
    have hFzero (p : Plane) : F (y,p) = 0 := by simp only [F,hy,mul_zero]
    have hid : (Φ y : Plane → Plane) = id := funext (hΦzero y hFzero)
    rw [hΨeq,hid,Chart.conjugate_id]



theorem exists_parameter_relative_corrected_disk_diffeomorphisms
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hφc : HasCompactSupport (fun p : P × Plane => φ p.1 p.2-p.2))
    (hφs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hpos : ∀ p : P × Plane, 0 < spatialJacobian (fun p => φ p.1 p.2) p)
    (Y : Set P) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (hz : ∀ i y, y ∈ Y → (∫ x in roundDisk (r i),
      spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x)-1) = 0) :
    ∃ ψ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × Plane => ψ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x v w, planarArea (fderiv ℝ (ψ y) x v) (fderiv ℝ (ψ y) x w) = planarArea v w) ∧
      (∀ i y, y ∈ Y → ψ y '' closedRoundDisk (r i) = φ y '' closedRoundDisk (r i)) ∧
      ∀ y, (∀ x, spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x) = 1) →
        ∀ x, ψ y x = φ y x := by
  let f : P × Plane → ℝ := fun p => spatialJacobian (fun p : P × Plane => φ p.1 p.2) p-1
  have hf : ContDiff ℝ ∞ f := (spatialJacobian_smooth hφ).sub contDiff_const
  have hfc : HasCompactSupport f :=
    hφc.of_isClosed_subset (isClosed_tsupport f) (spatialJacobian_support _)
  have hfs : tsupport f ⊆ univ ×ˢ roundDisk R := (spatialJacobian_support _).trans hφs
  have hf0 (y : P) : (∫ x, f (y,x)) = 0 := spatialJacobian_integral φ hφ hφs hpos y
  have hfpos (p : P × Plane) : 0 < 1+f p := by dsimp [f] <;> linarith [hpos p]
  obtain ⟨χ,hχ,hχi,hχc,hχs,hχarea,hχdisk,hχzero⟩ :=
    exists_parameter_relative_disk_moser hR hf hfc hfs hf0 hfpos Y r hr hrR hri hz
  let ψ : P → Plane ≃ₜ Plane := fun y => (χ y).trans (φ y)
  have hψ : ContDiff ℝ ∞ (fun p : P × Plane => ψ p.1 p.2) :=
    hφ.comp (contDiff_fst.prodMk hχ)
  have hψi : ContDiff ℝ ∞ (fun p : P × Plane => (ψ p.1).symm p.2) :=
    hχi.comp (contDiff_fst.prodMk hφi)
  have hs : tsupport (fun p : P × Plane => ψ p.1 p.2-p.2) ⊆
      tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ∪
      tsupport (fun p : P × Plane => χ p.1 p.2-p.2) := by
    apply closure_minimal _ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro p hp
    by_contra hn
    have ha := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => φ p.1 p.2-p.2) (fun h => hn (Or.inl h)))
    have hb := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => χ p.1 p.2-p.2) (fun h => hn (Or.inr h)))
    apply hp
    change φ p.1 (χ p.1 p.2)-p.2 = 0
    rw [hb,ha,sub_self]
  refine ⟨ψ,hψ,hψi,(hφc.union hχc).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (union_subset hφs hχs),?_,?_,?_⟩
  · intro y x v w
    have hdφ : Differentiable ℝ (φ y) := (hφ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hdχ : Differentiable ℝ (χ y) := (hχ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have he : fderiv ℝ (ψ y) x = (fderiv ℝ (φ y) (χ y x)).comp (fderiv ℝ (χ y) x) :=
      fderiv_comp x (hdφ (χ y x)) (hdχ x)
    rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,planarArea_map]
    have hh := hχarea y x v w
    have hnum : 1+f (y,χ y x) = (fderiv ℝ (φ y) (χ y x)).det := by
      dsimp only [f,spatialJacobian]
      ring
    rw [hnum] at hh
    exact hh
  · intro i y hy
    change (φ y ∘ χ y) '' closedRoundDisk (r i) = _
    rw [image_comp,hχdisk i y hy]
  · intro y hy x
    have hh := hχzero y (fun x => sub_eq_zero.mpr (hy x)) x
    change φ y (χ y x) = φ y x
    rw [hh]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem circle_volume_zero (R : ℝ) :
    volume {x : Plane | radiusSq x = R^2} = 0 := by
  change (volume.prod volume) {x : Plane | radiusSq x = R^2} = 0
  apply Measure.measure_prod_null_of_ae_null
    (isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  apply Filter.Eventually.of_forall
  intro x
  apply measure_mono_null (t := {Real.sqrt (R^2-x^2),-Real.sqrt (R^2-x^2)})
  · intro y hy
    change x^2+y^2 = R^2 at hy
    have hn : 0 ≤ R^2-x^2 := by nlinarith [sq_nonneg y]
    have he : y^2 = (Real.sqrt (R^2-x^2))^2 := by rw [Real.sq_sqrt hn]; linarith
    simpa only [mem_insert_iff,mem_singleton_iff] using sq_eq_sq_iff_eq_or_eq_neg.mp he
  · exact Set.Finite.measure_zero ((Set.finite_singleton _).insert _) volume

theorem roundDisk_ae_closedRoundDisk (R : ℝ) :
    roundDisk R =ᵐ[volume] closedRoundDisk R := by
  have hh : ∀ᵐ x : Plane ∂volume, x ∉ {x : Plane | radiusSq x = R^2} := by
    apply ae_iff.mpr
    simpa only [not_not,mem_ofPred_eq] using circle_volume_zero R
  filter_upwards [hh] with x hx
  change (radiusSq x < R^2) = (radiusSq x ≤ R^2)
  exact propext (lt_iff_le_and_ne.trans (and_iff_left hx))

theorem integral_roundDisk_eq_closedRoundDisk (f : Plane → ℝ) (R : ℝ) :
    (∫ x in roundDisk R, f x) = ∫ x in closedRoundDisk R, f x :=
  setIntegral_congr_set (roundDisk_ae_closedRoundDisk R)

theorem jacobian_defect_roundDisk_of_area (φ : Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ x, 0 < (fderiv ℝ φ x).det) (r : ℝ)
    (harea : volume (φ '' closedRoundDisk r) = volume (closedRoundDisk r)) :
    (∫ x in roundDisk r, (fderiv ℝ φ x).det-1) = 0 := by
  rw [integral_roundDisk_eq_closedRoundDisk]
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (closedRoundDisk_isCompact r).measurableSet
    (f' := fderiv ℝ φ)
    (fun x _ => ((hφ.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    φ.injective.injOn (fun _ : Plane => (1 : ℝ))
  simp only [smul_eq_mul,mul_one,abs_of_pos (hpos _)] at hi
  have ha : (∫ _ in φ '' closedRoundDisk r, (1:ℝ)) = ∫ _ in closedRoundDisk r, (1:ℝ) := by
    simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,Measure.real,harea]
  rw [ha] at hi
  rw [integral_sub]
  · exact sub_eq_zero.mpr hi.symm
  · have hd : Continuous (fun x => (fderiv ℝ φ x).det) :=
      ContinuousLinearMap.continuous_det.comp (hφ.fderiv_right (m := ∞) (by simp)).continuous
    exact hd.continuousOn.integrableOn_compact (closedRoundDisk_isCompact r)
  · exact integrableOn_const (closedRoundDisk_isCompact r).measure_lt_top.ne


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem familyGenerator_hasDerivAt
    (φ : P × ℝ → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : (P × ℝ) × Plane => φ p.1 p.2))
    (y : P) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => φ (y,s) x)
      (familyGenerator φ (0,1) ((y,t),φ (y,t) x)) t := by
  have hg : HasDerivAt (fun s : ℝ => ((y,s),x)) ((0,1),0) t :=
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t)).prodMk (hasDerivAt_const t x)
  have hh := (hφ.differentiable (by simp) ((y,t),x)).hasFDerivAt.comp_hasDerivAt t hg
  simpa only [familyGenerator,Homeomorph.symm_apply_apply,Function.comp_def] using hh

variable [FiniteDimensional ℝ P]

theorem exists_hamiltonian_disk_isotopy_bp240_oai
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (Φ : SupportedSmoothIsotopyFamily P Plane (roundDisk R))
    (Y : Set P) (hY : IsCompact Y)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (harea : ∀ i y, y ∈ Y → volume (Φ.map y 1 '' closedRoundDisk (r i)) =
      volume (closedRoundDisk (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) = Φ.map y 1 '' closedRoundDisk (r i) := by
  obtain ⟨Φ₀,hΦc,hΦeq⟩ := Φ.exists_joint_compact Y hY
  let φ : P × ℝ → Plane ≃ₜ Plane := fun q => Φ₀.map q.1 q.2
  have hφs : tsupport (fun p : (P × ℝ) × Plane => φ p.1 p.2-p.2) ⊆
      univ ×ˢ roundDisk R := Φ₀.joint_support.trans (prod_mono Subset.rfl Φ₀.support_subset)
  have hpos (p : (P × ℝ) × Plane) :
      0 < spatialJacobian (fun p => φ p.1 p.2) p :=
    (Φ₀.eval p.1.1).det_fderiv_pos p.1.2 p.2
  have hz (i : ι) (q : P × ℝ) (hq : q ∈ Y ×ˢ ({1} : Set ℝ)) :
      (∫ x in roundDisk (r i), spatialJacobian (fun p => φ p.1 p.2) (q,x)-1) = 0 := by
    have ht : q.2 = 1 := hq.2
    have he : φ q = Φ.map q.1 1 := by
      change Φ₀.map q.1 q.2 = _
      rw [ht,hΦeq q.1 hq.1 1 ⟨zero_le_one,le_rfl⟩]
    apply jacobian_defect_roundDisk_of_area (φ q) ((Φ₀.eval q.1).map_smooth q.2)
      (fun x => hpos (q,x)) (r i)
    rw [he]
    exact harea i q.1 hq.1
  obtain ⟨ψ,hψ,hψi,hψc,hψs,hψsp,hψdisk,hψzero⟩ :=
    exists_parameter_relative_corrected_disk_diffeomorphisms hR φ Φ₀.smooth
      Φ₀.inverse_smooth hΦc hφs hpos (Y ×ˢ ({1} : Set ℝ)) r hr hrR hri hz
  have hzero (y : P) : ψ (y,0) = Homeomorph.refl Plane := by
    apply Homeomorph.ext
    intro x
    have hJ (z : Plane) : spatialJacobian (fun p => φ p.1 p.2) ((y,0),z) = 1 := by
      dsimp only [spatialJacobian,φ]
      rw [Φ₀.zero y]
      simp [ContinuousLinearMap.det]
    rw [hψzero (y,0) hJ x]
    change Φ₀.map y 0 x = x
    rw [Φ₀.zero y]
    rfl
  let Ψ : SupportedSmoothIsotopyFamily P Plane (roundDisk R) := {
    map := fun y t => ψ (y,t)
    smooth := hψ
    inverse_smooth := hψi
    zero := hzero
    support := Prod.snd '' tsupport (fun p : (P × ℝ) × Plane => ψ p.1 p.2-p.2)
    compact_support := hψc.image continuous_snd
    support_subset := by rintro x ⟨p,hp,rfl⟩; exact (hψs hp).2
    fixed := by
      intro y t x hx
      exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
        (f := fun p : (P × ℝ) × Plane => ψ p.1 p.2-p.2)
        (fun hp => hx ⟨((y,t),x),hp,rfl⟩)) }
  obtain ⟨H,hH,hHc,hHs,hHd,_⟩ := exists_hamiltonian_of_symplectic_family ψ hψ hψi
    hψc hR hψs hψsp (0,1)
  refine ⟨{ isotopy := Ψ
            symplectic := fun y t => hψsp (y,t)
            hamiltonian := H
            smooth := hH
            compact := hHc
            support := hHs
            flow := ?_ },?_⟩
  · intro y t x
    have hd := hHd (y,t) (ψ (y,t) x)
    rw [hd.fderiv,planarHamiltonianField_neg_area]
    exact familyGenerator_hasDerivAt ψ hψ y t x
  · intro i y hy
    change ψ (y,1) '' closedRoundDisk (r i) = _
    rw [hψdisk i (y,1) ⟨hy,rfl⟩]
    change Φ₀.map y 1 '' closedRoundDisk (r i) = _
    rw [hΦeq y hy 1 ⟨zero_le_one,le_rfl⟩]


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240_oai.{u_1} := @OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_isotopy_bp240_oai.{u_1}
