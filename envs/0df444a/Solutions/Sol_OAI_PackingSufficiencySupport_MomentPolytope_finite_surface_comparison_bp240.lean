-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:22.885808+00:00
-- url     : https://prove2.me/submissions/1a5e75df-e7a6-47d6-847e-93d1cd79c9be

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_scaled_slice_rearrangement_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_CircleCorrection
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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


end

open scoped ContDiff



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ParametricMoser
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

theorem radiusSq_smul (a : ℝ) (p : Plane) : radiusSq (a • p) = a^2*radiusSq p := by
  change (a*p.1)^2+(a*p.2)^2 = a^2*(p.1^2+p.2^2)
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem hamiltonianField_contraction {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    (H : ℝ × E → ℝ) (p : ℝ × E) (w : E) :
    A (hamiltonianField A H p) w = -fderiv ℝ H p (0,w) := by
  exact congrArg (fun α : E →L[ℝ] ℝ => α w) (formMoserField_solve (fun _ => hA) p)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothInverse
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_inverse_on {f : E → F} {D : Set E} (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ f D) (hfi : InjOn f D)
    (hi : ∀ x ∈ D, (fderiv ℝ f x).IsInvertible) :
    IsOpen (f '' D) ∧ ContDiffOn ℝ ∞ (invFunOn f D) (f '' D) ∧
      (∀ x ∈ D, invFunOn f D (f x) = x) ∧
      (∀ y ∈ f '' D, f (invFunOn f D y) = y) := by
  have hlocal (x : E) (hx : x ∈ D) :
      f '' D ∈ 𝓝 (f x) ∧ ContDiffAt ℝ ∞ (invFunOn f D) (f x) := by
    have hfx : ContDiffAt ℝ ∞ f x := (hf x hx).contDiffAt (hD.mem_nhds hx)
    obtain ⟨A,hA⟩ := hi x hx
    have hd : HasFDerivAt f (A : E →L[ℝ] F) x := by
      rw [hA]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    let e := hfx.toOpenPartialHomeomorph f hd (by simp)
    have hex : x ∈ e.source := hfx.mem_toOpenPartialHomeomorph_source hd (by simp)
    have heq : (e : E → F) = f := rfl
    let V : Set F := e '' (e.source ∩ D)
    have hV : IsOpen V := e.isOpen_image_of_subset_source (e.open_source.inter hD) inter_subset_left
    have hxV : f x ∈ V := ⟨x,⟨hex,hx⟩,rfl⟩
    have hVD : V ⊆ f '' D := by
      rintro _ ⟨z,hz,rfl⟩
      exact ⟨z,hz.2,rfl⟩
    have hginv : invFunOn f D =ᶠ[𝓝 (f x)] e.symm := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      obtain ⟨z,hz,rfl⟩ := hy
      rw [e.left_inv hz.1]
      exact hfi.leftInvOn_invFunOn hz.2
    have hei : ContDiffAt ℝ ∞ (e.symm : F → E) (f x) :=
      hfx.to_localInverse hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact ⟨Filter.mem_of_superset (hV.mem_nhds hxV) hVD,hei.congr_of_eventuallyEq hginv⟩
  refine ⟨?_,?_,fun x hx => hfi.leftInvOn_invFunOn hx,?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (hlocal x hx).1
  · rintro _ ⟨x,hx,rfl⟩
    exact (hlocal x hx).2.contDiffWithinAt
  · intro y hy
    exact invFunOn_eq hy

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem clockGraph_linear_invertible (C : (Q × E) →L[ℝ] E)
    (hC : (C.comp (ContinuousLinearMap.inr ℝ Q E)).IsInvertible) :
    ((ContinuousLinearMap.fst ℝ Q E).prod C).IsInvertible := by
  let A := C.comp (ContinuousLinearMap.inr ℝ Q E)
  let B := (ContinuousLinearMap.fst ℝ Q E).prod C
  have hdecomp (p : Q × E) : C p = C (p.1,0) + A p.2 := by
    change C p = C (p.1,0) + C (0,p.2)
    rw [← map_add]
    congr 1
    ext <;> simp
  have hinj : Injective B := by
    intro p q he
    change (p.1,C p) = (q.1,C q) at he
    have ht := congrArg (fun z : Q × E => z.1) he
    have hx : C p = C q := congrArg (fun z : Q × E => z.2) he
    rw [hdecomp p,hdecomp q,ht] at hx
    have hs : p.2 = q.2 := hC.injective (add_left_cancel hx)
    exact Prod.ext ht hs
  have hsurj : Surjective B := by
    rintro ⟨t,x⟩
    refine ⟨(t,A.inverse (x-C (t,0))),?_⟩
    change (t,C (t,A.inverse (x-C (t,0)))) = (t,x)
    refine Prod.ext (by rfl) ?_
    change C (t,A.inverse (x-C (t,0))) = x
    rw [hdecomp,hC.self_apply_inverse]
    exact add_sub_cancel _ _
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj),rfl⟩

theorem parametric_inverse_on (f : Q × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set (Q × E)) (hD : IsOpen D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible) :
    ∃ (U : Set (Q × E)) (g : Q × E → E), IsOpen U ∧ ContDiffOn ℝ ∞ g U ∧
      U = (fun p => (p.1,f p)) '' D ∧
      (∀ p ∈ D, (p.1,f p) ∈ U ∧ g (p.1,f p) = p.2) ∧
      (∀ p ∈ U, (p.1,g p) ∈ D ∧ f (p.1,g p) = p.2) := by
  let F : Q × E → Q × E := fun p => (p.1,f p)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  have hFi : InjOn F D := by
    rintro ⟨t,x⟩ hp ⟨s,y⟩ hq he
    have ht : t = s := congrArg (fun z : Q × E => z.1) he
    cases ht
    have hx : f (t,x) = f (t,y) := congrArg (fun z : Q × E => z.2) he
    exact Prod.ext rfl (hinj t hp hq hx)
  have hFd (p : Q × E) : fderiv ℝ F p =
      (ContinuousLinearMap.fst ℝ Q E).prod (fderiv ℝ f p) := by
    exact (hasFDerivAt_fst.prodMk (hf.differentiable (by simp) p).hasFDerivAt).fderiv
  have hFiv (p : Q × E) (hp : p ∈ D) : (fderiv ℝ F p).IsInvertible := by
    rw [hFd]
    apply clockGraph_linear_invertible
    have hd : fderiv ℝ (fun x => f (p.1,x)) p.2 =
        (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ Q E) := by
      exact ((hf.differentiable (by simp) p).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
    rw [← hd]
    exact hi p hp
  obtain ⟨hU,hg,hleft,hright⟩ := smooth_inverse_on hD hF.contDiffOn hFi hFiv
  let g : Q × E → E := fun p => (invFunOn F D p).2
  refine ⟨F '' D,g,hU,hg.snd,rfl,?_,?_⟩
  · intro p hp
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    exact congrArg Prod.snd (hleft p hp)
  · intro p hp
    have he := hright p hp
    change ((invFunOn F D p).1,f (invFunOn F D p)) = p at he
    have hfirst := congrArg (fun z : Q × E => z.1) he
    have hmem := invFunOn_mem hp
    have hid : (p.1,g p) = invFunOn F D p := Prod.ext hfirst.symm rfl
    rw [hid]
    exact ⟨hmem,congrArg (fun z : Q × E => z.2) he⟩


end

open scoped ContDiff Topology NNReal
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SupportedSmoothIsotopy

 theorem mapsTo {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    MapsTo (Φ.map t) W W := by
  intro x hx
  by_contra hn
  have hn' : Φ.map t x ∉ Φ.support := fun h => hn (Φ.support_subset h)
  have he := Φ.fixed t (Φ.map t x) hn'
  exact hn (((Φ.map t).injective he).symm ▸ hx)

end SupportedSmoothIsotopy

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Topology
section
variable {ι : Type*} [Fintype ι]

theorem phaseArea_apply (v w : PlanePhase ι) :
    phaseArea v w = ∑ i, ((v i).1*(w i).2-(v i).2*(w i).1) := by
  simp [phaseArea]

theorem phaseArea_skew (v w : PlanePhase ι) : phaseArea v w = -phaseArea w v := by
  simp only [phaseArea_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [DecidableEq ι]

@[simp] theorem phaseArea_single_right (v : PlanePhase ι) (i : ι) (w : Plane) :
    phaseArea v (Pi.single i w) = planarArea (v i) w := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

@[simp] theorem phaseArea_single_left (i : ι) (v : Plane) (w : PlanePhase ι) :
    phaseArea (Pi.single i v) w = planarArea v (w i) := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

theorem phaseArea_injective : Injective (phaseArea : PlanePhase ι →L[ℝ] _) := by
  intro v w h
  funext i
  have h1 := congrArg (fun A : PlanePhase ι →L[ℝ] ℝ => A (Pi.single i (0,1))) h
  have h2 := congrArg (fun A : PlanePhase ι →L[ℝ] ℝ => A (Pi.single i (1,0))) h
  apply Prod.ext
  · simpa using h1
  · simpa using h2

theorem phase_decomposition (w : PlanePhase ι) :
    (∑ i, ((w i).1 • (Pi.single i ((1:ℝ),0) : PlanePhase ι) + (w i).2 • (Pi.single i ((0:ℝ),1) : PlanePhase ι))) = w := by
  funext j
  simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply]
  rw [Finset.sum_eq_single j]
  · ext <;> simp
  · intro b _ hbj
    simp [Ne.symm hbj]
  · simp

theorem phaseArea_surjective : Surjective (phaseArea : PlanePhase ι →L[ℝ] _) := by
  intro α
  let v : PlanePhase ι := fun i => (α (Pi.single i (0,1)),-α (Pi.single i (1,0)))
  refine ⟨v,?_⟩
  ext w
  rw [←phase_decomposition w]
  simp only [map_sum,map_add,map_smul,smul_eq_mul,
    phaseArea_single_right,planarArea_apply,v,mul_zero,mul_one,sub_zero,zero_sub,neg_neg]

theorem phaseArea_isInvertible : (phaseArea : PlanePhase ι →L[ℝ] _).IsInvertible :=
  ⟨(LinearEquiv.ofBijective (phaseArea : PlanePhase ι →L[ℝ] _).toLinearMap
    ⟨phaseArea_injective,phaseArea_surjective⟩).toContinuousLinearEquiv,rfl⟩

end
section

variable {ι : Type*} [Fintype ι]

@[simp] theorem phaseDot_J_right (z v : PlanePhase ι) :
    phaseDot z (phaseJ v) = -phaseArea z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseArea_J_right (z v : PlanePhase ι) :
    phaseArea z (phaseJ v) = phaseDot z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory

theorem areaRadius_sq {a : ℝ} (ha : 0 ≤ a) : (areaRadius a)^2 = a/Real.pi :=
  Real.sq_sqrt (div_nonneg ha Real.pi_pos.le)

theorem mem_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ closedRoundDisk (areaRadius a) ↔ radialArea x ≤ a := by
  change radiusSq x ≤ (areaRadius a)^2 ↔ Real.pi * radiusSq x ≤ a
  rw [areaRadius_sq ha,le_div_iff₀ Real.pi_pos,mul_comm]

theorem mem_roundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ roundDisk (areaRadius a) ↔ radialArea x < a := by
  change radiusSq x < (areaRadius a)^2 ↔ Real.pi * radiusSq x < a
  rw [areaRadius_sq ha,lt_div_iff₀ Real.pi_pos,mul_comm]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_PlanarRotation
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments
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

theorem planeRotate_hasDerivAt {θ : ℝ → ℝ} {t a : ℝ} (hθ : HasDerivAt θ a t) (v : Plane) :
    HasDerivAt (fun s => planeRotate (θ s) v)
      (a • (-(planeRotate (θ t) v).2,(planeRotate (θ t) v).1)) t := by
  have h1 := ((Real.hasDerivAt_cos (θ t)).comp t hθ).mul_const v.1
  have h2 := ((Real.hasDerivAt_sin (θ t)).comp t hθ).mul_const v.2
  have h3 := ((Real.hasDerivAt_sin (θ t)).comp t hθ).mul_const v.1
  have h4 := ((Real.hasDerivAt_cos (θ t)).comp t hθ).mul_const v.2
  apply ((h1.sub h2).prodMk (h3.add h4)).congr_deriv
  ext <;> dsimp [planeRotate] <;> ring

theorem radialArea_hasFDerivAt (x : Plane) :
    HasFDerivAt radialArea
      (Real.pi • ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have h₁ : HasFDerivAt (fun p : Plane => p.1^2)
      ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
    simpa using (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2
  have h₂ : HasFDerivAt (fun p : Plane => p.2^2)
      ((2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    simpa using (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2
  exact (h₁.add h₂).const_mul Real.pi

@[simp] theorem radialArea_fderiv (x v : Plane) :
    fderiv ℝ radialArea x v = 2*Real.pi*(x.1*v.1+x.2*v.2) := by
  rw [(radialArea_hasFDerivAt x).fderiv]
  change Real.pi * (2*x.1*v.1+2*x.2*v.2) = _
  ring


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_BallVolume
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical

namespace PackingSufficiencySupport

open MeasureTheory

namespace Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isClosed_convexFunctionSet (S : Set E) (hS : Convex ℝ S) :
    IsClosed (convexFunctionSet S hS) := by
  unfold convexFunctionSet
  simp only [Set.ofPred_forall]
  repeat' apply isClosed_iInter; intro
  exact isClosed_le (ContinuousMap.evalCLM ℝ _).continuous
    (((ContinuousMap.evalCLM ℝ _).continuous.const_mul _).add
      ((ContinuousMap.evalCLM ℝ _).continuous.const_mul _))

instance convexMaps_completeSpace (S : Set E) (hS : Convex ℝ S) [CompactSpace S] :
    CompleteSpace (ConvexMaps S hS) :=
  (isClosed_convexFunctionSet S hS).isComplete.completeSpace_coe

theorem exists_convex_fixedPoint {S : Set E} {hS : Convex ℝ S} [CompactSpace S]
    (Q : ConvexMaps S hS) (R : ConvexMaps S hS → ConvexMaps S hS)
    (hR : ∀ F G, dist (R F) (R G) ≤ dist F G)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    ∃ K : ConvexMaps S hS, R (affineStep lam hlam Q K) = K := by
  let T : ConvexMaps S hS → ConvexMaps S hS := fun F => R (affineStep lam hlam Q F)
  have hT : ContractingWith ⟨lam, hlam⟩ T := by
    refine ⟨hlam1, LipschitzWith.of_dist_le_mul ?_⟩
    intro F G
    apply (hR _ _).trans
    change dist (lam • (F : C(S, ℝ)) + (Q : C(S, ℝ)))
      (lam • (G : C(S, ℝ)) + (Q : C(S, ℝ))) ≤ lam * dist (F : C(S, ℝ)) (G : C(S, ℝ))
    rw [dist_add_right]
    simpa [Real.norm_eq_abs, abs_of_nonneg hlam] using dist_smul_le lam F.val G.val
  exact ⟨hT.fixedPoint T, hT.fixedPoint_isFixedPt⟩

theorem fixedPoint_negative_maximum {S : Set E} {hS : Convex ℝ S} [CompactSpace S]
    (h0 : (0 : E) ∈ S) (Q K : ConvexMaps S hS)
    (R : ConvexMaps S hS → ConvexMaps S hS) (μ : C(S, ℝ) →ₗ[ℝ] ℝ)
    (hμlower : ∀ (F : C(S, ℝ)) (c : ℝ), (∀ x, c ≤ F x) → c ≤ μ F)
    (hRmean : ∀ F, μ (R F).val = μ F.val)
    (hRmin : ∀ F x, (R F).val ⟨0, h0⟩ ≤ (R F).val x)
    (hRbound : ∀ F (c : ℝ), (∀ x, F.val x ≤ c) → ∀ x, (R F).val x ≤ c)
    {lam τ m d c MQ : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hdc : d < c)
    (hμQ : μ Q.val = -m) (hQbound : ∀ x, Q.val x ≤ MQ)
    (houter : ∀ x : S, (x : E) ∉ τ • S → Q.val x ≤ -c)
    (hgap : (1 - lam) * (d + MQ) < lam * (1 - τ) * (m - d))
    (hfix : R (affineStep lam hlam.le Q K) = K) :
    ∀ x, K.val x < -d / (1 - lam) := by
  let : Nonempty S := ⟨⟨0, h0⟩⟩
  have hden : 0 < 1 - lam := sub_pos.mpr hlam1
  have hmean : μ K.val = -m / (1 - lam) := by
    have heq := congrArg (fun F : ConvexMaps S hS => μ F.val) hfix
    rw [hRmean] at heq
    change μ (lam • K.val + Q.val) = μ K.val at heq
    rw [map_add, map_smul, hμQ] at heq
    apply (eq_div_iff hden.ne').mpr
    change lam * μ K.val + -m = μ K.val at heq
    nlinarith
  have hzero : K.val ⟨0, h0⟩ ≤ μ K.val := by
    apply hμlower
    intro x
    rw [← hfix]
    exact hRmin _ x
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set S).Nonempty) K.val.continuous.continuousOn
  have hmax (x : S) : K.val x ≤ K.val z := hz (Set.mem_univ x)
  have hmaxlt : K.val z < -d / (1 - lam) := by
    by_contra hh
    have hM : -d / (1 - lam) ≤ K.val z := le_of_not_gt hh
    have hlamM : lam * K.val z ≤ K.val z + d := by
      have := (div_le_iff₀ hden).mp hM
      nlinarith
    have hgap' : d + MQ < lam * ((1 - τ) * (m - d) / (1 - lam)) := by
      rw [← mul_div_assoc, lt_div_iff₀ hden]
      nlinarith [hgap]
    have hall (x : S) : (affineStep lam hlam.le Q K).val x < K.val z := by
      change lam * K.val x + Q.val x < K.val z
      by_cases hx : (x : E) ∈ τ • S
      · rcases hx with ⟨v, hv, hvx⟩
        have hcv : K.val x ≤ (1 - τ) * K.val ⟨0, h0⟩ + τ * K.val ⟨v, hv⟩ := by
          simpa [hvx] using K.property ⟨0, h0⟩ ⟨v, hv⟩ (1 - τ) τ
            (sub_nonneg.mpr hτ1.le) hτ.le (by ring)
        have hinner : K.val x ≤ K.val z - (1 - τ) * (m - d) / (1 - lam) := by
          calc
            K.val x ≤ (1 - τ) * (-m / (1 - lam)) + τ * K.val z :=
              hcv.trans (add_le_add
                (mul_le_mul_of_nonneg_left (hzero.trans_eq hmean) (sub_nonneg.mpr hτ1.le))
                (mul_le_mul_of_nonneg_left (hmax _) hτ.le))
            _ = K.val z - (1 - τ) * (K.val z + m / (1 - lam)) := by ring
            _ ≤ K.val z - (1 - τ) * ((m - d) / (1 - lam)) := by
              have hm : (m - d) / (1 - lam) ≤ K.val z + m / (1 - lam) := by
                rw [sub_div]
                have hM' := hM
                rw [neg_div] at hM'
                linarith
              exact sub_le_sub_left
                (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hτ1.le)) _
            _ = _ := by ring
        have hxmul := mul_le_mul_of_nonneg_left hinner hlam.le
        have hqx := hQbound x
        nlinarith
      · have hxmul := mul_le_mul_of_nonneg_left (hmax x) hlam.le
        have hqx := houter x hx
        linarith
    obtain ⟨w, _, hw⟩ := isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set S).Nonempty)
      (affineStep lam hlam.le Q K).val.continuous.continuousOn
    have hr := hRbound (affineStep lam hlam.le Q K)
      ((affineStep lam hlam.le Q K).val w) (fun x => hw (Set.mem_univ x)) z
    rw [hfix] at hr
    exact (not_lt_of_ge hr) (hall w)
  exact fun x => (hmax x).trans_lt hmaxlt

end Comparison
end PackingSufficiencySupport
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexRearrangement
attribute [-instance] _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport
open MeasureTheory
namespace Comparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem exists_gap_parameter {a b : ℝ} (ha : 0 < a) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ (1 - lam) * b < lam * a := by
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb : b ≤ B := le_max_left _ _
  have hden : 0 < B + 2 * a := by positivity
  refine ⟨(B + a) / (B + 2 * a), div_pos (by positivity) hden, ?_, ?_⟩
  · rw [div_lt_one hden]
    linarith
  · apply (mul_lt_mul_iff_left₀ hden).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hb ha.le]

theorem exists_rearranged_gap {S : Set E} {hS : Convex ℝ S} [CompactSpace S]
    (h0 : (0 : E) ∈ S) (Q : ConvexMaps S hS)
    (R : ConvexMaps S hS → ConvexMaps S hS) (μ : C(S, ℝ) →ₗ[ℝ] ℝ)
    (hRlip : ∀ F G, dist (R F) (R G) ≤ dist F G)
    (hμlower : ∀ (F : C(S, ℝ)) (c : ℝ), (∀ x, c ≤ F x) → c ≤ μ F)
    (hRmean : ∀ F, μ (R F).val = μ F.val)
    (hRmin : ∀ F x, (R F).val ⟨0, h0⟩ ≤ (R F).val x)
    (hRorder : ∀ F G, (∀ x, F.val x ≤ G.val x) → ∀ x, (R F).val x ≤ (R G).val x)
    (hRtrans : ∀ F c, R (translate F c) = translate (R F) c)
    (hRbound : ∀ F (c : ℝ), (∀ x, F.val x ≤ c) → ∀ x, (R F).val x ≤ c)
    {τ m c : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hm : 0 < m) (hc : 0 < c)
    (hμQ : μ Q.val = -m)
    (houter : ∀ x : S, (x : E) ∉ τ • S → Q.val x ≤ -c) :
    ∃ (K : ConvexMaps S hS) (d : ℝ), 0 < d ∧
      ∀ x, (R (affineStep 1 (by norm_num) Q K)).val x ≤ K.val x - d := by
  let : Nonempty S := ⟨⟨0, h0⟩⟩
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set S).Nonempty) Q.val.continuous.continuousOn
  let d := min m c / 2
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hdm : d < m := by
    have := min_le_left m c
    have := lt_min hm hc
    dsimp [d] <;> linarith
  have hdc : d < c := by
    have := min_le_right m c
    have := lt_min hm hc
    dsimp [d] <;> linarith
  obtain ⟨lam, hlam, hlam1, hgap⟩ := exists_gap_parameter
    (b := d + Q.val z) (mul_pos (sub_pos.mpr hτ1) (sub_pos.mpr hdm))
  obtain ⟨K, hfix⟩ := exists_convex_fixedPoint Q R hRlip hlam.le hlam1
  have hn := fixedPoint_negative_maximum h0 Q K R μ hμlower hRmean hRmin hRbound
    hlam hlam1 hτ hτ1 hdc hμQ (fun x => hz (Set.mem_univ x)) houter
    (by simpa only [mul_assoc] using hgap) hfix
  have hstep : ∀ x, (affineStep 1 (by norm_num) Q K).val x ≤
      (translate (affineStep lam hlam.le Q K) (-d)).val x := by
    intro x
    have hx := (lt_div_iff₀ (sub_pos.mpr hlam1)).mp (hn x)
    change 1 * K.val x + Q.val x ≤ lam * K.val x + Q.val x + -d
    nlinarith
  refine ⟨K, d, hd, fun x => ?_⟩
  have hr := hRorder _ _ hstep x
  rw [hRtrans, hfix] at hr
  exact hr

section Minimum
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

omit [CompactSpace X] in
theorem le_minimum (F : C(X, ℝ)) {c : ℝ} (h : ∀ x, c ≤ F x) : c ≤ minimum F :=
  le_csInf (Set.range_nonempty F) (by rintro y ⟨x, rfl⟩; exact h x)

theorem minimum_mono (F G : C(X, ℝ)) (h : ∀ x, F x ≤ G x) :
    minimum F ≤ minimum G :=
  le_minimum G (fun x => (minimum_le F x).trans (h x))

theorem minimum_add_const (F : C(X, ℝ)) (c : ℝ) :
    minimum (F + ContinuousMap.const X c) = minimum F + c := by
  obtain ⟨x, hx⟩ := minimum_attained F
  apply le_antisymm
  · calc
      _ ≤ (F + ContinuousMap.const X c) x := minimum_le _ x
      _ = _ := by simp [hx]
  · apply le_minimum
    intro y
    simpa [add_comm] using add_le_add_right (minimum_le F y) c

end Minimum

section SlicedDomain
variable (Y : Set E) (L : E → ℝ)

omit [NormedSpace ℝ E] in
theorem rearrange_mono (hL : ContinuousOn L Y) (F G : C(Slice Y L, ℝ))
    (hFG : ∀ x, F x ≤ G x) : ∀ x, rearrange Y L hL F x ≤ rearrange Y L hL G x := by
  intro x
  apply minimum_mono
  intro t
  exact max_le_max (hFG _) (hFG _)

omit [NormedSpace ℝ E] in
theorem rearrange_add_const (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ)) (c : ℝ) :
    rearrange Y L hL (F + ContinuousMap.const _ c) =
      rearrange Y L hL F + ContinuousMap.const _ c := by
  ext x
  have hv : (intervalValue Y L hL (F + ContinuousMap.const _ c)).curry x =
      (intervalValue Y L hL F).curry x + ContinuousMap.const _ c := by
    ext t
    exact max_add_add_right _ _ c
  change minimum _ = minimum _ + c
  rw [hv, minimum_add_const]

theorem convex_le_max_on_slice (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc))
    (x : Slice Y L) {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ L x.val.1)
    (hac : a ≤ c) (hcb : c ≤ b) :
    F.val (pointAtHeight Y L x c ⟨ha.trans hac, hcb.trans hb⟩) ≤
      max (F.val (pointAtHeight Y L x a ⟨ha, (hac.trans hcb).trans hb⟩))
        (F.val (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩)) := by
  by_cases hab : a = b
  · have hc : c = a := by linarith
    subst b; subst c
    exact le_max_left _ _
  have habpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hac.trans hcb) hab)
  let q := (c - a) / (b - a)
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hac) habpos.le
  have hq1 : q ≤ 1 := (div_le_one habpos).mpr (by linarith)
  have hsum : (1-q) + q = 1 := by ring
  have hgeom : (1-q)*a + q*b = c := by
    dsimp [q]
    field_simp
    ring
  have hf := F.property
    (pointAtHeight Y L x a ⟨ha, (hac.trans hcb).trans hb⟩)
    (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩)
    (1-q) q (sub_nonneg.mpr hq1) hq0 hsum
  have heq : (⟨(1-q) • (pointAtHeight Y L x a
        ⟨ha, (hac.trans hcb).trans hb⟩).val + q •
      (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩).val,
      (convex_sliceDomain Y L hc) (pointAtHeight Y L x a
        ⟨ha, (hac.trans hcb).trans hb⟩).property
        (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩).property
        (sub_nonneg.mpr hq1) hq0 hsum⟩ : Slice Y L) =
      pointAtHeight Y L x c ⟨ha.trans hac, hcb.trans hb⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · change (1-q) • x.val.1 + q • x.val.1 = x.val.1
      rw [← add_smul, hsum, one_smul]
    · exact hgeom
  rw [heq] at hf
  apply hf.trans
  calc
    _ ≤ (1-q) * max _ _ + q * max _ _ := add_le_add
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hq1))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hq0)
    _ = _ := by ring

theorem rearrange_monotone_height (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc))
    (x : Slice Y L) {h : ℝ} (hh0 : 0 ≤ h) (hhx : h ≤ x.val.2) :
    rearrange Y L hL F.val
      (pointAtHeight Y L x h ⟨hh0, hhx.trans x.property.2.2⟩) ≤
      rearrange Y L hL F.val x := by
  obtain ⟨a, ha, hax, hmin⟩ := rearrange_attained Y L hL F.val x
  let z := pointAtHeight Y L x h ⟨hh0, hhx.trans x.property.2.2⟩
  have haz : a + z.val.2 ≤ L z.val.1 := by
    change a + h ≤ L x.val.1
    linarith
  apply (rearrange_le_candidate Y L hL F.val z a ha haz).trans
  rw [hmin]
  apply max_le
  · exact le_max_left _ _
  · exact convex_le_max_on_slice Y L hc F x ha hax
      (by change a ≤ a + h; linarith) (by change a + h ≤ a + x.val.2; linarith)

omit [NormedSpace ℝ E] in

theorem rearrange_compare_slices (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x y : Slice Y L) (hxy : x.val.2 = y.val.2) (hLen : L y.val.1 ≤ L x.val.1)
    (hF : ∀ (a : ℝ) (ha : a ∈ Set.Icc 0 (L y.val.1)),
      F (pointAtHeight Y L x a ⟨ha.1, ha.2.trans hLen⟩) ≤
        F (pointAtHeight Y L y a ha)) :
    rearrange Y L hL F x ≤ rearrange Y L hL F y := by
  obtain ⟨a, ha, hay, hmin⟩ := rearrange_attained Y L hL F y
  have hax : a + x.val.2 ≤ L x.val.1 := by rw [hxy]; exact hay.trans hLen
  apply (rearrange_le_candidate Y L hL F x a ha hax).trans
  rw [hmin]
  apply max_le_max
  · exact hF a ⟨ha, by linarith [y.property.2.1]⟩
  · simpa only [intervalCandidate, hxy] using
      hF (a + y.val.2) ⟨by linarith [y.property.2.1], hay⟩

end SlicedDomain

namespace IntervalMinimum

theorem sublevel_volume_eq {D : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hconv : ConvexOn ℝ (Set.Icc 0 D) f)
    (hchar : ∀ h ∈ Set.Icc 0 D, ∀ c, g h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a + h ≤ D ∧ f a ≤ c ∧ f (a+h) ≤ c) (c : ℝ) :
    volume {h | h ∈ Set.Icc 0 D ∧ g h ≤ c} =
      volume {h | h ∈ Set.Icc 0 D ∧ f h ≤ c} := by
  let S : Set ℝ := {h | h ∈ Set.Icc 0 D ∧ f h ≤ c}
  have hcomp : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hc : Convex ℝ S := hconv.convex_le c
  by_cases hne : S.Nonempty
  · let a := sInf S
    let b := sSup S
    have hab : a ≤ b := by
      obtain ⟨u, hu⟩ := hne
      exact (csInf_le hcomp.bddBelow hu).trans (le_csSup hcomp.bddAbove hu)
    have hrepr : S = Set.Icc a b := eq_Icc_of_connected_compact (hc.isConnected hne) hcomp
    have haS : a ∈ S := by rw [hrepr]; exact ⟨le_rfl, hab⟩
    have hbS : b ∈ S := by rw [hrepr]; exact ⟨hab, le_rfl⟩
    have heq : {h | h ∈ Set.Icc 0 D ∧ g h ≤ c} = Set.Icc 0 (b-a) := by
      ext h
      constructor
      · rintro ⟨hh, hgc⟩
        obtain ⟨u, hu, huh, hfu, hfuh⟩ := (hchar h hh c).mp hgc
        have huS : u ∈ S := ⟨⟨hu, by linarith [hh.1]⟩, hfu⟩
        have huhS : u+h ∈ S := ⟨⟨by linarith [hh.1], huh⟩, hfuh⟩
        rw [hrepr] at huS huhS
        exact ⟨hh.1, by linarith [huS.1, huhS.2]⟩
      · intro hh
        have hhD : h ∈ Set.Icc 0 D := ⟨hh.1, by linarith [haS.1.1, hbS.1.2, hh.2]⟩
        refine ⟨hhD, (hchar h hhD c).mpr ⟨a, haS.1.1, ?_, haS.2, ?_⟩⟩
        · linarith [hbS.1.2, hh.2]
        · have hah : a+h ∈ S := by rw [hrepr]; constructor <;> linarith [hh.1, hh.2]
          exact hah.2
    rw [heq]
    change volume (Set.Icc 0 (b-a)) = volume S
    rw [hrepr, Real.volume_Icc, Real.volume_Icc, sub_zero]
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have heq : {h | h ∈ Set.Icc 0 D ∧ g h ≤ c} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro h ⟨hh, hgc⟩
      obtain ⟨a, ha, hah, hfa, _⟩ := (hchar h hh c).mp hgc
      exact hne ⟨a, ⟨ha, by linarith [hh.1]⟩, hfa⟩
    change volume _ = volume S
    rw [heq, hS]

theorem integral_eq {D : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hconv : ConvexOn ℝ (Set.Icc 0 D) f)
    (hchar : ∀ h ∈ Set.Icc 0 D, ∀ c, g h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a + h ≤ D ∧ f a ≤ c ∧ f (a+h) ≤ c) :
    ∫ h in Set.Icc 0 D, g h = ∫ h in Set.Icc 0 D, f h := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 D)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hm : μ.map g = μ.map f := by
    apply Measure.ext_of_Iic
    intro c
    rw [Measure.map_apply hg.measurable measurableSet_Iic,
      Measure.map_apply hf.measurable measurableSet_Iic]
    dsimp [μ]
    rw [Measure.restrict_apply (hg.measurable measurableSet_Iic),
      Measure.restrict_apply (hf.measurable measurableSet_Iic)]
    simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, and_comm] using
      sublevel_volume_eq hf hconv hchar c
  have h := congrArg (fun ν : Measure ℝ => ∫ t, t ∂ν) hm
  rw [integral_map (f := fun t : ℝ => t) hg.measurable.aemeasurable (by fun_prop),
    integral_map (f := fun t : ℝ => t) hf.measurable.aemeasurable (by fun_prop)] at h
  exact h

end IntervalMinimum

variable (Y : Set E) (L : E → ℝ)

omit [NormedSpace ℝ E] in
theorem sliceFunction_eq (F : C(Slice Y L, ℝ)) (x : Slice Y L)
    {h : ℝ} (hh : h ∈ Set.Icc 0 (L x.val.1)) :
    sliceFunction Y L F x h = F (pointAtHeight Y L x h hh) := by
  change F (pointAtHeight Y L x (max 0 (min (L x.val.1) h))
    ⟨le_max_left _ _, max_le (x.property.2.1.trans x.property.2.2) (min_le_left _ _)⟩) = _
  simp only [min_eq_right hh.2, max_eq_right hh.1]

theorem sliceFunction_convex (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) (x : Slice Y L) :
    ConvexOn ℝ (Set.Icc 0 (L x.val.1)) (sliceFunction Y L F.val x) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro a ha b hb p q hp hq hpq
  have hmid := (convex_Icc (0 : ℝ) (L x.val.1) : Convex ℝ _) ha hb hp hq hpq
  rw [sliceFunction_eq Y L F.val x hmid, sliceFunction_eq Y L F.val x ha,
    sliceFunction_eq Y L F.val x hb]
  have hf := F.property (pointAtHeight Y L x a ha) (pointAtHeight Y L x b hb)
    p q hp hq hpq
  have heq : (⟨p • (pointAtHeight Y L x a ha).val + q • (pointAtHeight Y L x b hb).val,
      (convex_sliceDomain Y L hc) (pointAtHeight Y L x a ha).property
        (pointAtHeight Y L x b hb).property hp hq hpq⟩ : Slice Y L) =
      pointAtHeight Y L x (p • a + q • b) hmid := by
    apply Subtype.ext
    apply Prod.ext
    · change p • x.val.1 + q • x.val.1 = x.val.1
      rw [← add_smul, hpq, one_smul]
    · rfl
  rw [heq] at hf
  exact hf

omit [NormedSpace ℝ E] in
theorem rearrange_slice_characterization (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) {h : ℝ} (hh : h ∈ Set.Icc 0 (L x.val.1)) (c : ℝ) :
    sliceFunction Y L (rearrange Y L hL F) x h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a+h ≤ L x.val.1 ∧
        sliceFunction Y L F x a ≤ c ∧ sliceFunction Y L F x (a+h) ≤ c := by
  rw [sliceFunction_eq Y L (rearrange Y L hL F) x hh]
  let z := pointAtHeight Y L x h hh
  constructor
  · intro hgc
    obtain ⟨a, ha, haz, hmin⟩ := rearrange_attained Y L hL F z
    have haI : a ∈ Set.Icc 0 (L x.val.1) := ⟨ha, by change a+h ≤ L x.val.1 at haz; linarith [hh.1]⟩
    have hahI : a+h ∈ Set.Icc 0 (L x.val.1) := ⟨by linarith [hh.1], haz⟩
    refine ⟨a, ha, haz, ?_, ?_⟩
    · rw [sliceFunction_eq Y L F x haI]
      exact (le_max_left _ _).trans (hmin.symm.le.trans hgc)
    · rw [sliceFunction_eq Y L F x hahI]
      exact (le_max_right _ _).trans (hmin.symm.le.trans hgc)
  · rintro ⟨a, ha, hah, hfa, hfah⟩
    have haI : a ∈ Set.Icc 0 (L x.val.1) := ⟨ha, by linarith [hh.1]⟩
    have hahI : a+h ∈ Set.Icc 0 (L x.val.1) := ⟨by linarith [hh.1], hah⟩
    rw [sliceFunction_eq Y L F x haI] at hfa
    rw [sliceFunction_eq Y L F x hahI] at hfah
    exact (rearrange_le_candidate Y L hL F z a ha hah).trans (max_le hfa hfah)

theorem rearrange_slice_integral (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) (x : Slice Y L) :
    ∫ h in Set.Icc 0 (L x.val.1), sliceFunction Y L (rearrange Y L hL F.val) x h =
      ∫ h in Set.Icc 0 (L x.val.1), sliceFunction Y L F.val x h := by
  apply IntervalMinimum.integral_eq (sliceFunction Y L F.val x).continuous
    (sliceFunction Y L (rearrange Y L hL F.val) x).continuous (sliceFunction_convex Y L hc F x)
  intro h hh c
  exact rearrange_slice_characterization Y L hL F.val x hh c

end Comparison
end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_PolytopeSlices
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_assemble _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}

theorem lower_closed (b : Fin N → Moments m) (c : Fin N → ℝ) (hb : ∀ ν j, 0 ≤ b ν j)
    {p q : Moments m} (hp : p ∈ region b c) (hq : ∀ j, 0 ≤ q j) (hqp : ∀ j, q j ≤ p j) :
    q ∈ region b c := by
  refine ⟨hq, fun ν => (Finset.sum_le_sum fun i _ => ?_).trans (hp.2 ν)⟩
  exact mul_le_mul_of_nonneg_left (hqp i) (hb ν i)

theorem assemble_zero_mem_iff (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) (y : Base j) :
    assemble j y 0 ∈ region b c ↔ y ∈ baseRegion b c j := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h.1 i, fun ν => by simpa [weighted_assemble] using h.2 ν⟩
  · intro h
    constructor
    · intro i
      by_cases hi : i = j
      · simp [assemble, hi]
      · simpa [assemble, hi] using h.1 ⟨i, hi⟩
    · intro ν; simpa [weighted_assemble] using h.2 ν

theorem baseRegion_eq_image (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j, 0 ≤ b ν j) (j : Fin m) :
    baseRegion b c j = (fun p : Moments m => fun i : {i : Fin m // i ≠ j} => p i) '' region b c := by
  ext y
  constructor
  · intro hy
    refine ⟨assemble j y 0, (assemble_zero_mem_iff b c j y).mpr hy, ?_⟩
    funext i; simp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun i => hp.1 i, fun ν => ?_⟩
    have h := hp.2 ν
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j] at h
    linarith [mul_nonneg (hb ν j) (hp.1 j)]

theorem isCompact_baseRegion (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j, 0 ≤ b ν j) (hcomp : IsCompact (region b c)) (j : Fin m) :
    IsCompact (baseRegion b c j) := by
  rw [baseRegion_eq_image b c hb j]
  exact hcomp.image (continuous_pi fun i => continuous_apply i.val)

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)

theorem length_antitone [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i) :
    Antitone (length b c j) := by
  intro y z hyz
  apply (le_length_iff b c j).mpr
  intro ν
  apply (length_le b c j ν z).trans
  apply div_le_div_of_nonneg_right _ ν.property.le
  apply sub_le_sub_left
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyz i) (hb ν i)

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

theorem coordRearrange_mono (F G : C(region b c, ℝ)) (hFG : F ≤ G) :
    coordRearrange b c j hb F ≤ coordRearrange b c j hb G := by
  intro p
  apply rearrange_mono
  intro x
  exact hFG _

theorem coordRearrange_add_const (F : C(region b c, ℝ)) (a : ℝ) :
    coordRearrange b c j hb (F + ContinuousMap.const _ a) =
      coordRearrange b c j hb F + ContinuousMap.const _ a := by
  have heq : onSlice b c j hb (F + ContinuousMap.const _ a) =
      onSlice b c j hb F + ContinuousMap.const _ a := by
    ext x
    rfl
  unfold coordRearrange
  rw [heq, rearrange_add_const]
  rfl

theorem coordRearrange_nonexpansive [CompactSpace (region b c)]
    (F G : C(region b c, ℝ)) :
    dist (coordRearrange b c j hb F) (coordRearrange b c j hb G) ≤ dist F G := by
  apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist F G)).mpr
  intro p
  have hFG : F ≤ G + ContinuousMap.const _ (dist F G) := by
    intro x
    have h := ContinuousMap.dist_apply_le_dist (f := F) (g := G) x
    rw [Real.dist_eq] at h
    have h' := (abs_le.mp h).2
    change F x ≤ G x + dist F G
    linarith
  have hGF : G ≤ F + ContinuousMap.const _ (dist F G) := by
    intro x
    have h := ContinuousMap.dist_apply_le_dist (f := F) (g := G) x
    rw [Real.dist_eq] at h
    have h' := (abs_le.mp h).1
    change G x ≤ F x + dist F G
    linarith
  have h1 := coordRearrange_mono b c j hb _ _ hFG p
  have h2 := coordRearrange_mono b c j hb _ _ hGF p
  rw [coordRearrange_add_const] at h1 h2
  change coordRearrange b c j hb F p ≤ coordRearrange b c j hb G p + dist F G at h1
  change coordRearrange b c j hb G p ≤ coordRearrange b c j hb F p + dist F G at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

variable (j : Fin m) [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

theorem coordRearrange_increasing (F : ConvexMaps (region b c) (convex_region b c)) :
    IncreasingIn b c j (coordRearrange b c j hb F.val) := by
  intro p q hpq heq
  let e := sliceEquiv b c j hb
  let Fs : ConvexMaps (sliceDomain (baseRegion b c j) (length b c j))
      (convex_sliceDomain _ _ (concave_length b c j)) :=
    ⟨onSlice b c j hb F.val, onSlice_convex b c j hb F⟩
  have hh : p.val j ∈ Set.Icc 0 (length b c j (e q).val.1) :=
    ⟨p.property.1 j, hpq.trans (e q).property.2.2⟩
  have he : pointAtHeight (baseRegion b c j) (length b c j) (e q) (p.val j) hh = e p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact (heq i i.property).symm
    · rfl
  change rearrange _ _ _ Fs.val (e p) ≤ rearrange _ _ _ Fs.val (e q)
  rw [← he]
  exact rearrange_monotone_height _ _ (continuous_length b c j).continuousOn
    (concave_length b c j) Fs (e q) (p.property.1 j) hpq

theorem coordRearrange_preserves_increasing (i : Fin m) (hij : i ≠ j)
    (F : C(region b c, ℝ)) (hF : IncreasingIn b c i F) :
    IncreasingIn b c i (coordRearrange b c j hb F) := by
  intro p q hpq heq
  let e := sliceEquiv b c j hb
  have hbase : (e p).val.1 ≤ (e q).val.1 := by
    intro l
    change p.val l ≤ q.val l
    by_cases hl : l.val = i
    · simpa [hl] using hpq
    · exact (heq l hl).le
  change rearrange _ _ _ (onSlice b c j hb F) (e p) ≤
    rearrange _ _ _ (onSlice b c j hb F) (e q)
  apply rearrange_compare_slices _ _ (continuous_length b c j).continuousOn _ (e p) (e q)
    (heq j hij.symm) (length_antitone b c j hb hbase)
  intro a ha
  apply hF
  · change assemble j (fun l => p.val l) a i ≤ assemble j (fun l => q.val l) a i
    simpa [assemble, hij] using hpq
  · intro l hli
    change assemble j (fun l => p.val l) a l = assemble j (fun l => q.val l) a l
    by_cases hlj : l = j
    · simp [assemble, hlj]
    · simpa [assemble, hlj] using heq l hli

theorem coordRearrange_bound (F : C(region b c, ℝ)) (a : ℝ) (hF : ∀ p, F p ≤ a) :
    ∀ p, coordRearrange b c j hb F p ≤ a := by
  intro p
  let e := sliceEquiv b c j hb
  change rearrange _ _ _ (onSlice b c j hb F) (e p) ≤ a
  have h := rearrange_le_candidate (baseRegion b c j) (length b c j)
    (continuous_length b c j).continuousOn (onSlice b c j hb F) (e p) 0 (by norm_num)
    (by simpa only [zero_add] using (e p).property.2.2)
  exact h.trans (max_le (hF _) (hF _))

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ} (j : Fin m)
open MeasureTheory

theorem measurePreserving_split : MeasurePreserving (split j) := by
  let : Unique {i : Fin m // ¬ i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (by simpa using i.property) }
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin m => ℝ) (fun i => i ≠ j)
  have h₂ := (MeasurePreserving.id (volume : Measure (Base j))).prod
    (volume_preserving_piUnique (fun _ : {i : Fin m // ¬ i ≠ j} => ℝ))
  exact h₂.comp h₁

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open MeasureTheory
variable {E : Type*} [TopologicalSpace E] [T2Space E]
variable [MeasurableSpace E] [BorelSpace E]

theorem integralMap_mono (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (F G : C(S, ℝ)) (hFG : F ≤ G) :
    integralMap μ S hS F ≤ integralMap μ S hS G := by
  apply integral_mono (zeroExtend_integrable μ S hS F) (zeroExtend_integrable μ S hS G)
  intro x
  by_cases hx : x ∈ S
  · simpa [zeroExtend, hx] using hFG ⟨x, hx⟩
  · simp [zeroExtend, hx]

theorem integralMap_const (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (a : ℝ) :
    integralMap μ S hS (ContinuousMap.const _ a) = (μ S).toReal * a := by
  change (∫ x, zeroExtend S (ContinuousMap.const _ a) x ∂μ) = _
  have heq : zeroExtend S (ContinuousMap.const _ a) = S.indicator (fun _ => a) := by
    ext x; by_cases hx : x ∈ S <;> simp [zeroExtend, hx]
  rw [heq, integral_indicator hS.measurableSet, integral_const]
  simp [measureReal_def]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Comparison
open MeasureTheory
variable {ι : Type*} [Fintype ι]
variable (Y : Set (ι → ℝ)) (L : (ι → ℝ) → ℝ)

theorem zeroExtend_slice (F : C(Slice Y L, ℝ)) (x : Slice Y L) :
    (fun h => zeroExtend (sliceDomain Y L) F (x.val.1, h)) =
      (Set.Icc 0 (L x.val.1)).indicator (sliceFunction Y L F x) := by
  funext h
  by_cases hh : h ∈ Set.Icc 0 (L x.val.1)
  · rw [Set.indicator_of_mem hh, sliceFunction_eq Y L F x hh]
    exact zeroExtend_coe _ _ (pointAtHeight Y L x h hh)
  · have hz : (x.val.1, h) ∉ sliceDomain Y L := fun hz => hh hz.2
    simp [zeroExtend, hz, Set.indicator_of_notMem hh]

theorem rearrange_integral (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (hS : IsCompact (sliceDomain Y L))
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) :
    integralMap volume (sliceDomain Y L) hS (rearrange Y L hL F.val) =
      integralMap volume (sliceDomain Y L) hS F.val := by
  change (∫ x, zeroExtend (sliceDomain Y L) (rearrange Y L hL F.val) x) =
    ∫ x, zeroExtend (sliceDomain Y L) F.val x
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ (zeroExtend_integrable volume _ hS (rearrange Y L hL F.val)),
    integral_prod _ (zeroExtend_integrable volume _ hS F.val)]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hx : ∃ h, (y,h) ∈ sliceDomain Y L
  · obtain ⟨h, hh⟩ := hx
    let x : Slice Y L := ⟨(y,h), hh⟩
    change (∫ s, zeroExtend (sliceDomain Y L) (rearrange Y L hL F.val) (x.val.1,s)) =
      ∫ s, zeroExtend (sliceDomain Y L) F.val (x.val.1,s)
    rw [zeroExtend_slice, zeroExtend_slice, integral_indicator measurableSet_Icc,
      integral_indicator measurableSet_Icc]
    exact rearrange_slice_integral Y L hL hc F x
  · have hnone (h : ℝ) : (y,h) ∉ sliceDomain Y L := fun hh => hx ⟨h, hh⟩
    simp [zeroExtend, hnone]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.MomentPolytope
open Comparison MeasureTheory
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

theorem zeroExtend_onSlice (F : C(region b c, ℝ)) (p : Moments m) :
    zeroExtend (region b c) F p =
      zeroExtend (sliceDomain (baseRegion b c j) (length b c j)) (onSlice b c j hb F) (split j p) := by
  by_cases hp : p ∈ region b c
  · let x : region b c := ⟨p,hp⟩
    change zeroExtend _ F x = zeroExtend _ (onSlice b c j hb F) (sliceEquiv b c j hb x)
    rw [zeroExtend_coe, zeroExtend_coe]
    exact congrArg F ((sliceEquiv b c j hb).symm_apply_apply x).symm
  · have hs : split j p ∉ sliceDomain (baseRegion b c j) (length b c j) := by
      intro hs
      rw [← image_split b c j hb] at hs
      obtain ⟨q,hq,heq⟩ := hs
      exact hp ((split j).injective heq ▸ hq)
    simp [zeroExtend, hp, hs]

theorem integralMap_onSlice (hcomp : IsCompact (region b c)) (F : C(region b c, ℝ)) :
    integralMap volume (region b c) hcomp F =
      integralMap volume (sliceDomain (baseRegion b c j) (length b c j))
        (isCompact_sliceDomain b c j hb hcomp) (onSlice b c j hb F) := by
  change (∫ p, zeroExtend (region b c) F p) = ∫ x, zeroExtend _ _ x
  simp_rw [zeroExtend_onSlice b c j hb]
  exact (measurePreserving_split j).integral_comp (split j).measurableEmbedding _

theorem coordRearrange_integral (hcomp : IsCompact (region b c))
    (F : ConvexMaps (region b c) (convex_region b c)) :
    integralMap volume (region b c) hcomp (coordRearrange b c j hb F.val) =
      integralMap volume (region b c) hcomp F.val := by
  rw [integralMap_onSlice b c j hb, integralMap_onSlice b c j hb]
  have heq : onSlice b c j hb (coordRearrange b c j hb F.val) =
      rearrange (baseRegion b c j) (length b c j) (continuous_length b c j).continuousOn
        (onSlice b c j hb F.val) := by
    ext x
    exact congrArg (rearrange (baseRegion b c j) (length b c j)
      (continuous_length b c j).continuousOn (onSlice b c j hb F.val))
      ((sliceEquiv b c j hb).apply_symm_apply x)
  rw [heq]
  exact rearrange_integral _ _ _ (concave_length b c j)
    (isCompact_sliceDomain b c j hb hcomp) ⟨_, onSlice_convex b c j hb F⟩

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison MeasureTheory
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
variable [∀ j, Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

theorem successive_nonexpansive [CompactSpace (region b c)] (js : List (Fin m))
    (F G : ConvexMaps (region b c) (convex_region b c)) :
    dist (successive b c hb js F) (successive b c hb js G) ≤ dist F G := by
  induction js generalizing F G with
  | nil => exact le_rfl
  | cons j js ih =>
    exact (ih _ _).trans (coordRearrange_nonexpansive b c j hb F.val G.val)

theorem successive_mono (js : List (Fin m))
    (F G : ConvexMaps (region b c) (convex_region b c)) (hFG : F.val ≤ G.val) :
    (successive b c hb js F).val ≤ (successive b c hb js G).val := by
  induction js generalizing F G with
  | nil => exact hFG
  | cons j js ih => exact ih _ _ (coordRearrange_mono b c j hb _ _ hFG)

theorem successive_translate (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) (a : ℝ) :
    successive b c hb js (translate F a) = translate (successive b c hb js F) a := by
  induction js generalizing F with
  | nil => rfl
  | cons j js ih =>
    have hd : coordOperator b c j hb (translate F a) = translate (coordOperator b c j hb F) a :=
      Subtype.ext (coordRearrange_add_const b c j hb F.val a)
    simp only [successive, hd, ih]

theorem successive_integral (hcomp : IsCompact (region b c)) (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) :
    integralMap volume (region b c) hcomp (successive b c hb js F).val =
      integralMap volume (region b c) hcomp F.val := by
  induction js generalizing F with
  | nil => rfl
  | cons j js ih =>
    exact (ih _).trans (coordRearrange_integral b c j hb hcomp F)

end PackingSufficiencySupport.MomentPolytope
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff ENNReal Pointwise Classical
open Comparison MeasureTheory
section
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
variable [∀ j, Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
theorem successive_bound (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) (a : ℝ) (hF : ∀ p, F.val p ≤ a) :
    ∀ p, (successive b c hb js F).val p ≤ a := by
  induction js generalizing F with
  | nil => exact hF
  | cons j js ih => exact ih _ (coordRearrange_bound b c j hb F.val a hF)

theorem successive_increasing (js : List (Fin m)) (i : Fin m)
    (F : ConvexMaps (region b c) (convex_region b c))
    (hi : i ∈ js ∨ IncreasingIn b c i F.val) :
    IncreasingIn b c i (successive b c hb js F).val := by
  induction js generalizing F with
  | nil => exact hi.resolve_left List.not_mem_nil
  | cons j js ih =>
    apply ih
    by_cases hij : i = j
    · subst i
      exact Or.inr (coordRearrange_increasing b c j hb F)
    · rcases hi with hmem | hinc
      · exact Or.inl ((List.mem_cons.mp hmem).resolve_left hij)
      · exact Or.inr (coordRearrange_preserves_increasing b c j hb i hij F.val hinc)

theorem fullRearrangement_increasing (F : ConvexMaps (region b c) (convex_region b c))
    (i : Fin m) : IncreasingIn b c i (fullRearrangement b c hb F).val :=
  successive_increasing b c hb _ i F (Or.inl (List.mem_finRange i))

end

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem increasing_min_at_zero (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 ≤ c ν)
    (F : C(region b c, ℝ)) (hF : ∀ i, IncreasingIn b c i F) (q : region b c) :
    F ⟨0, zero_mem b c hc⟩ ≤ F q := by
  let p (s : Finset (Fin m)) : region b c :=
    ⟨fun i => if i ∈ s then q.val i else 0,
      lower_closed b c hb q.property
        (fun i => by split_ifs <;> [exact q.property.1 i; exact le_rfl])
        (fun i => by split_ifs <;> [exact le_rfl; exact q.property.1 i])⟩
  have h (s : Finset (Fin m)) : F (p ∅) ≤ F (p s) := by
    induction s using Finset.induction_on with
    | empty => exact le_rfl
    | @insert i s hi ih =>
      apply ih.trans
      apply hF i
      · change (if i ∈ s then q.val i else 0) ≤
          if i ∈ insert i s then q.val i else 0
        simpa [hi] using q.property.1 i
      · intro l hli
        change (if l ∈ s then q.val l else 0) =
          if l ∈ insert i s then q.val l else 0
        simp [hli]
  have h0 : p ∅ = ⟨0, zero_mem b c hc⟩ := by ext i; simp [p]
  have h1 : p Finset.univ = q := by ext i; simp [p]
  simpa only [h0,h1] using h Finset.univ

theorem volume_region_pos (hc : ∀ ν, 0 < c ν) : 0 < volume (region b c) := by
  let U : Set (Moments m) := {p | ∀ ν, ∑ i, b ν i * p i < c ν}
  have hU : IsOpen U := by
    simpa only [U, Set.ofPred_forall] using
      isOpen_iInter_of_finite (fun ν => isOpen_lt
        (show Continuous (fun p : Moments m => ∑ i, b ν i * p i) by fun_prop)
        (continuous_const (y := c ν)))
  have hU0 : (0 : Moments m) ∈ U := by
    intro ν
    simpa using hc ν
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU 0 hU0
  let p : Moments m := fun _ => δ/2
  have hpU : p ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ δ/2)).mpr
      (fun i => by simp [p, Real.norm_eq_abs, abs_of_pos hδ]) |>.trans_lt (by linarith)
  let W : Set (Moments m) := {q | (∀ i, 0 < q i) ∧ q ∈ U}
  have hW : IsOpen W := by
    apply IsOpen.inter _ hU
    change IsOpen {q : Moments m | ∀ i, 0 < q i}
    simpa only [Set.ofPred_forall] using
      isOpen_iInter_of_finite (fun i : Fin m => isOpen_lt
        (continuous_const (y := (0 : ℝ))) (continuous_apply i))
  have hpW : p ∈ W := ⟨fun _ => half_pos hδ, hpU⟩
  have hsub : W ⊆ region b c := by
    intro q hq
    exact ⟨fun i => (hq.1 i).le, fun ν => (hq.2 ν).le⟩
  exact (hW.measure_pos volume ⟨p,hpW⟩).trans_le (measure_mono hsub)

theorem volume_region_toReal_pos (hc : ∀ ν, 0 < c ν) (hcomp : IsCompact (region b c)) :
    0 < (volume (region b c)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (volume_region_pos b c hc)) hcomp.measure_ne_top

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open scoped ContDiff ENNReal Pointwise Classical
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]
variable [MeasureSpace E] [BorelSpace E]
variable [IsFiniteMeasureOnCompacts (volume : Measure E)]

theorem averageMap_mono (S : Set E) (hS : IsCompact S) (F G : C(S, ℝ)) (hFG : F ≤ G) :
    averageMap S hS F ≤ averageMap S hS G := by
  exact mul_le_mul_of_nonneg_left (integralMap_mono volume S hS F G hFG) (by positivity)

theorem averageMap_const (S : Set E) (hS : IsCompact S) (hvol : 0 < (volume S).toReal) (a : ℝ) :
    averageMap S hS (ContinuousMap.const _ a) = a := by
  change (volume S).toReal⁻¹ * integralMap volume S hS (ContinuousMap.const _ a) = a
  rw [integralMap_const, ← mul_assoc, inv_mul_cancel₀ hvol.ne', one_mul]

theorem averageMap_lower (S : Set E) (hS : IsCompact S) (hvol : 0 < (volume S).toReal)
    (F : C(S, ℝ)) (a : ℝ) (hF : ∀ p, a ≤ F p) : a ≤ averageMap S hS F := by
  rw [← averageMap_const S hS hvol a]
  exact averageMap_mono S hS _ _ hF

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff ENNReal Pointwise Classical
open Comparison MeasureTheory

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem analytic_gap (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 < c ν)
    (hcomp : IsCompact (region b c))
    (Q : ConvexMaps (region b c) (convex_region b c))
    {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a)
    (hmean : averageMap (region b c) hcomp Q.val < 0)
    (houter : ∀ p : region b c, p.val ∉ τ • region b c → Q.val p ≤ -a) :
    letI : ∀ j, Nonempty (Active b j) := fun j => active_nonempty b c hb hc hcomp j
    ∃ (K : ConvexMaps (region b c) (convex_region b c)) (d : ℝ), 0 < d ∧
      ∀ p, (fullRearrangement b c hb (affineStep 1 (by norm_num) Q K)).val p ≤ K.val p - d := by
  let : CompactSpace (region b c) := isCompact_iff_compactSpace.mp hcomp
  let : ∀ j, Nonempty (Active b j) := fun j => active_nonempty b c hb hc hcomp j
  apply exists_rearranged_gap (zero_mem b c (fun ν => (hc ν).le)) Q
    (fullRearrangement b c hb) (averageMap (region b c) hcomp)
    (successive_nonexpansive b c hb (List.finRange m))
    (averageMap_lower _ _ (volume_region_toReal_pos b c hc hcomp))
  · intro F
    change (volume (region b c)).toReal⁻¹ * integralMap volume (region b c) hcomp
      (successive b c hb (List.finRange m) F).val =
        (volume (region b c)).toReal⁻¹ * integralMap volume (region b c) hcomp F.val
    rw [successive_integral]
  · intro F p
    exact increasing_min_at_zero b c hb (fun ν => (hc ν).le) _
      (fullRearrangement_increasing b c hb F) p
  · intro F G hFG
    exact successive_mono b c hb (List.finRange m) F G hFG
  · exact successive_translate b c hb (List.finRange m)
  · exact successive_bound b c hb (List.finRange m)
  · exact hτ
  · exact hτ1
  · exact neg_pos.mpr hmean
  · exact ha
  · exact (neg_neg _).symm
  · exact houter

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open scoped ContDiff ENNReal Pointwise Classical
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem smooth_approximation (S : Set E) (hS : IsCompact S) (F : C(S, ℝ))
    {ε : ℝ} (hε : 0 < ε) : ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧
      ∀ p : S, dist (f p.val) (F p) < ε := by
  obtain ⟨f,hf⟩ := ContinuousMap.exists_extension hS.isClosed.isClosedEmbedding_subtypeVal F
  have huc : UniformContinuousOn f (cthickening 1 S) :=
    hS.cthickening.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/2) (half_pos hε)
  obtain ⟨g,hg,hgf⟩ := f.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ)
  refine ⟨g,hg,fun p => ?_⟩
  have hdist : dist (g p.val) (f p.val) ≤ ε/2 := by
    apply hgf
    intro y hy
    rw [mem_ball, lt_min_iff] at hy
    exact (hfδ y (mem_cthickening_of_dist_le _ p.val _ _ p.property hy.1.le)
      p.val (self_subset_cthickening _ p.property) hy.2).le
  have heq : f p.val = F p := congrArg (fun H : C(S, ℝ) => H p) hf
  rw [heq] at hdist
  exact hdist.trans_lt (half_lt_self hε)

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem outerMoments_hasFDerivAt (j : ι) (z : PlanePhase ι) :
    HasFDerivAt (outerMoments j) (outerDifferential j z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=j
  · simpa only [outerMoments,hi,ite_true, if_true] using hasFDerivAt_const (c := (0:ℝ)) z
  · have hd := (radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
      (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt
    simpa only [outerMoments,hi,ite_false, if_false,Function.comp_def,ContinuousLinearMap.proj_apply] using hd

@[simp] theorem outerMoments_fderiv_apply (j : ι) (z v : PlanePhase ι) (i : ι) :
    fderiv ℝ (outerMoments j) z v i =
      if i=j then 0 else 2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2) := by
  rw [(outerMoments_hasFDerivAt j z).fderiv]
  dsimp [outerDifferential]
  split_ifs <;> simp

theorem outerMoments_fderiv_single (j i : ι) (z : PlanePhase ι) (w : Plane) :
    fderiv ℝ (outerMoments j) z (Pi.single i w) =
      if i=j then 0 else (2*Real.pi*((z i).1*w.1+(z i).2*w.2)) • Pi.single i (1:ℝ) := by
  funext k
  by_cases hi : i=j
  · subst i
    by_cases hk : k=j <;> simp [outerMoments_fderiv_apply,hk]
  · by_cases hk : k=i
    · subst k
      simp [outerMoments_fderiv_apply,hi]
    · by_cases hkj : k=j <;> simp [outerMoments_fderiv_apply,hi,hk,hkj]

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace HamiltonianDiskIsotopyFamily

theorem mapsTo_closed {R : ℝ} (Ψ : HamiltonianDiskIsotopyFamily P R) (y : P) (t : ℝ) :
    MapsTo (Ψ.isotopy.map y t) (closedRoundDisk R) (closedRoundDisk R) := by
  intro x hx
  by_cases hi : x ∈ roundDisk R
  · have hm := (Ψ.isotopy.eval y).mapsTo t hi
    change radiusSq (Ψ.isotopy.map y t x) < R^2 at hm
    exact hm.le
  · rw [Ψ.isotopy.fixed y t x (fun hs => hi (Ψ.isotopy.support_subset hs))]
    exact hx

end HamiltonianDiskIsotopyFamily

theorem radialArea_nonneg (x : Plane) : 0 ≤ radialArea x :=
  mul_nonneg Real.pi_pos.le (by dsimp [radiusSq] <;> positivity)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian

variable {m N : ℕ}

theorem fullBase_eq_image (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) :
    fullBase b c j = (fun y : Base j => assemble j y 0) '' baseRegion b c j := by
  ext y
  constructor
  · intro hy
    refine ⟨baseProjection j y,hy.2,?_⟩
    funext i
    by_cases hi : i=j
    · subst i; simpa using hy.1.symm
    · simp [assemble,hi,baseProjection]
  · rintro ⟨y,hy,rfl⟩
    exact ⟨by simp,by simpa using hy⟩

theorem fullBase_compact (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c)) : IsCompact (fullBase b c j) := by
  rw [fullBase_eq_image]
  exact (isCompact_baseRegion b c hb hK j).image (assemble_zero_smooth j).continuous

theorem fullBase_convex (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) :
    Convex ℝ (fullBase b c j) := by
  intro y hy z hz a d ha hd had
  refine ⟨by change a*y j+d*z j=0; simp [hy.1,hz.1],?_⟩
  exact (convex_baseRegion b c j) hy.2 hz.2 ha hd had

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) [Nonempty (Active b j)]

theorem concave_fullLength : ConcaveOn ℝ (fullBase b c j) (fullLength b c j) := by
  refine ⟨fullBase_convex b c j,?_⟩
  intro y hy z hz a d ha hd had
  exact (concave_length b c j).2 hy.2 hz.2 ha hd had

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem planeMoments_nonneg (z : PlanePhase ι) (i : ι) : 0 ≤ planeMoments z i :=
  radialArea_nonneg (z i)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerAreaForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem surfaceRemainder_gap {K H H₀ C : E → ℝ} {h : ι → E → ℝ} {ψ : E → E}
    {g ε : ℝ} {v : E} (hgap : g ≤ K (ψ v)-K v+H₀ v-C v)
    (harea : |H v-H₀ v| < 2*ε) (hcap : (∑ i, h i v)-C v < ε) :
    g-3*ε < surfaceRemainder K H h ψ v := by
  have ha := (abs_lt.mp harea).1
  dsimp [surfaceRemainder]
  linarith


end

open scoped ContDiff
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_ScaledPlanarMotion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[simp] theorem radialArea_smul (a : ℝ) (x : Plane) :
    radialArea (a • x) = a^2*radialArea x := by
  simp only [radialArea,radiusSq_smul]
  ring

theorem scaledPlanarTrace_smooth (Ψ : PlanarHamiltonianMotion P)
    (hΨ : ContDiff ℝ ∞ (fun p : (P × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2))
    {a χ : P → ℝ} (ha : ContDiff ℝ ∞ a) (hn : ∀ y, a y ≠ 0) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun p : (P × ℝ) × Plane => scaledPlanarTrace Ψ a χ p.1.1 p.1.2 p.2) := by
  unfold scaledPlanarTrace
  exact (ha.comp contDiff_fst.fst).smul (hΨ.comp
    ((contDiff_fst.fst.prodMk ((hχ.comp contDiff_fst.fst).mul
      (Real.smoothTransition.contDiff.comp contDiff_fst.snd))).prodMk
        (((ha.inv hn).comp contDiff_fst.fst).smul contDiff_snd)))

theorem scaledPlanarTrace_cutoff_zero (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (hχ : χ y = 0) (t : ℝ) (x : Plane) :
    scaledPlanarTrace Ψ a χ y t x = x := by
  simp only [scaledPlanarTrace,hχ,zero_mul,Ψ.zero]
  exact smul_inv_smul₀ ha x

theorem scaled_disk_fixed (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane)
    (hx : (a y)^2 ≤ radialArea x) : scaledPlanarTrace Ψ.motion a χ y t x = x := by
  have hs : (a y)⁻¹ • x ∉ roundDisk (areaRadius 1) := by
    rw [mem_roundDisk_areaRadius (by norm_num),radialArea_smul,not_lt]
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (a y)⁻¹)
    have he : (a y)⁻¹^2*(a y)^2 = 1 := by field_simp
    linarith
  dsimp only [scaledPlanarTrace,HamiltonianDiskIsotopyFamily.motion]
  rw [Ψ.isotopy.fixed y _ _ (fun h => hs (Ψ.isotopy.support_subset h))]
  exact smul_inv_smul₀ ha x

theorem scaled_disk_mapsTo (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane)
    (hx : radialArea x ≤ (a y)^2) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ (a y)^2 := by
  have hs : (a y)⁻¹ • x ∈ closedRoundDisk (areaRadius 1) := by
    rw [mem_closedRoundDisk_areaRadius (by norm_num),radialArea_smul]
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (a y)⁻¹)
    have he : (a y)⁻¹^2*(a y)^2 = 1 := by field_simp
    linarith
  have hm := Ψ.mapsTo_closed y (χ y*Real.smoothTransition t) hs
  rw [mem_closedRoundDisk_areaRadius (by norm_num)] at hm
  dsimp only [scaledPlanarTrace,HamiltonianDiskIsotopyFamily.motion]
  rw [radialArea_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (sq_nonneg (a y))

theorem scaled_disk_preserves_slice (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane) {L : ℝ}
    (hx : radialArea x ≤ L) (hfit : χ y ≠ 0 → (a y)^2 ≤ L) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L := by
  by_cases hc : χ y = 0
  · rw [scaledPlanarTrace_cutoff_zero Ψ.motion y ha hc]; exact hx
  · rcases le_total (radialArea x) ((a y)^2) with hl | hl
    · exact (scaled_disk_mapsTo Ψ y ha t x hl).trans (hfit hc)
    · rw [scaled_disk_fixed Ψ y ha t x hl]; exact hx

theorem HamiltonianDiskIsotopyFamily.exists_support_margin
    (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ p ∈ tsupport Ψ.hamiltonian, radialArea p.2 ≤ σ := by
  rcases (tsupport Ψ.hamiltonian).eq_empty_or_nonempty with he | hn
  · exact ⟨1/2,by norm_num,by norm_num,by simp [he]⟩
  obtain ⟨p,hp,hm⟩ := Ψ.compact.exists_isMaxOn hn
    (radialArea_smooth.continuous.comp continuous_snd).continuousOn
  have hp1 : radialArea p.2 < 1 :=
    (mem_roundDisk_areaRadius (by norm_num) _).mp (Ψ.support hp).2
  refine ⟨(radialArea p.2+1)/2,by linarith [radialArea_nonneg p.2],by linarith,?_⟩
  intro q hq
  have hh : radialArea q.2 ≤ radialArea p.2 := hm hq
  linarith

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_CartesianMomentSlices
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaled_disk_slice_iff (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane) {L : ℝ}
    (hfit : χ y ≠ 0 → (a y)^2 ≤ L) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L ↔ radialArea x ≤ L := by
  refine ⟨?_,fun hx => scaled_disk_preserves_slice Ψ y ha t x hx hfit⟩
  intro hx
  by_contra hn
  by_cases hc : χ y = 0
  · rw [scaledPlanarTrace_cutoff_zero Ψ.motion y ha hc] at hx
    exact hn hx
  · have hh : (a y)^2 ≤ radialArea x := (hfit hc).trans (le_of_not_ge hn)
    rw [scaled_disk_fixed Ψ y ha t x hh] at hx
    exact hn hx

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian Comparison

variable {m N : ℕ}

theorem planeRegion_mem_iff (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i) (z : PlanePhase (Fin m)) :
    z ∈ planeRegion b c ↔ outerMoments j z ∈ fullBase b c j ∧
      radialArea (z j) ≤ fullLength b c j (outerMoments j z) := by
  have hh := assemble_mem_iff b c j hb
    (baseProjection j (outerMoments j z)) (radialArea (z j))
  rw [assemble_outerMoments] at hh
  change planeMoments z ∈ region b c ↔ _
  simpa only [fullBase,mem_ofPred_eq,outerMoments_self,and_true,true_and,
    radialArea_nonneg,fullLength] using hh

theorem globalSliceFamily_convex (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (F : C(Moments m,ℝ)) (hF : ConvexOn ℝ (region b c) F)
    (y : Moments m) (hy : y ∈ fullBase b c j) :
    ConvexOn ℝ (Icc 0 (fullLength b c j y)) (fun h => globalSliceFamily F j (y,h)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro u hu v hv a d ha hd had
  have hu' := (assemble_mem_iff b c j hb _ u).mpr ⟨hy.2,hu⟩
  have hv' := (assemble_mem_iff b c j hb _ v).mpr ⟨hy.2,hv⟩
  have hh := hF.2 hu' hv' ha hd had
  change F (assemble j (baseProjection j y) (a*u+d*v)) ≤
    a*F (assemble j (baseProjection j y) u)+d*F (assemble j (baseProjection j y) v)
  have hey : a • baseProjection j y+d • baseProjection j y = baseProjection j y := by
    rw [←add_smul,had,one_smul]
  rw [←assemble_affine,hey] at hh
  exact hh

theorem globalSliceFamily_at_moments (F : C(Moments m,ℝ)) (j : Fin m)
    (z : PlanePhase (Fin m)) :
    globalSliceFamily F j (outerMoments j z,radialArea (z j)) = F (planeMoments z) := by
  change F (assemble j _ _) = _
  rw [assemble_outerMoments]

theorem coordRearrange_eq_intervalMinimum (b : Fin N → Moments m) (c : Fin N → ℝ)
    (j : Fin m) [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (F : C(Moments m,ℝ)) (p : region b c) :
    coordRearrange b c j hb (F.restrict (region b c)) p =
      intervalMinimum (fiberFunction (globalSliceFamily F j) p.val)
        (fullLength b c j p.val) (p.val j) := by
  unfold coordRearrange rearrange intervalMinimum
  apply congrArg minimum
  apply ContinuousMap.ext
  intro t
  simp only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,ContinuousMap.curry_apply,
    intervalValue,ContinuousMap.sup_apply,ContinuousMap.comp_apply,
    ContinuousMap.coe_mk,intervalEndpoint,onSlice,ContinuousMap.restrict_apply,
    fixedIntervalValue,fiberFunction,globalSliceFamily,zero_mul,one_mul,add_zero]
  rfl

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem liftArgument_fderiv (j : ι) (p q : ℝ × PlanePhase ι) :
    fderiv ℝ (liftArgument j) p q = ((fderiv ℝ (outerMoments j) p.2 q.2,q.1),q.2 j) := by
  have hd := (((outerMoments_smooth j).differentiable (by simp) p.2).hasFDerivAt.comp p
    (hasFDerivAt_snd (𝕜 := ℝ))).prodMk (hasFDerivAt_fst (𝕜 := ℝ))
  have he := hd.prodMk ((ContinuousLinearMap.proj j : PlanePhase ι →L[ℝ] Plane).hasFDerivAt.comp p
    (hasFDerivAt_snd (𝕜 := ℝ)))
  exact congrArg (fun A : (ℝ × PlanePhase ι) →L[ℝ] _ => A q) he.fderiv

theorem liftedHamiltonian_fderiv (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (p q : ℝ × PlanePhase ι) :
    fderiv ℝ (liftedHamiltonian j B) p q =
      fderiv ℝ B (liftArgument j p) ((fderiv ℝ (outerMoments j) p.2 q.2,q.1),q.2 j) := by
  rw [liftedHamiltonian,fderiv_comp p (hB.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    ((liftArgument_smooth j).differentiable (by simp) p)]
  rw [ContinuousLinearMap.comp_apply,liftArgument_fderiv]

omit [DecidableEq ι] in
theorem hamiltonian_slice_fderiv {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (y : ι → ℝ) (t : ℝ) (x w : Plane) :
    fderiv ℝ (fun z => B ((y,t),z)) x w = fderiv ℝ B ((y,t),x) ((0,0),w) := by
  have hd := (hB.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((y,t),x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (c := (y,t)) x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact congrArg (fun A : Plane →L[ℝ] ℝ => A w) hd.fderiv

theorem liftedHamiltonian_fderiv_inner (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (p : ℝ × PlanePhase ι) (w : Plane) :
    fderiv ℝ (liftedHamiltonian j B) p (0,Pi.single j w) =
      fderiv ℝ (fun z => B ((outerMoments j p.2,p.1),z)) (p.2 j) w := by
  rw [liftedHamiltonian_fderiv j hB,outerMoments_fderiv_single,hamiltonian_slice_fderiv hB]
  simp [liftArgument]

theorem liftedHamiltonian_fderiv_outer (j i : ι) (hij : i ≠ j)
    {B : ((ι → ℝ) × ℝ) × Plane → ℝ} (hB : ContDiff ℝ ∞ B)
    (p : ℝ × PlanePhase ι) (w : Plane) :
    fderiv ℝ (liftedHamiltonian j B) p (0,Pi.single i w) =
      liftedAngularSpeed j i B p*((p.2 i).1*w.1+(p.2 i).2*w.2) := by
  rw [liftedHamiltonian_fderiv j hB,outerMoments_fderiv_single]
  simp only [hij,ite_false, if_false,Pi.single_eq_of_ne (Ne.symm hij)]
  have he : (((2*Real.pi*((p.2 i).1*w.1+(p.2 i).2*w.2)) • Pi.single i (1:ℝ), (0:ℝ)), (0:Plane)) =
      (2*Real.pi*((p.2 i).1*w.1+(p.2 i).2*w.2)) • ((Pi.single i 1,0),0) := by
    simp
  rw [he,map_smul]
  dsimp [liftedAngularSpeed]
  ring

theorem liftedHamiltonian_field (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (p : ℝ × PlanePhase ι) (i : ι) :
    hamiltonianField phaseArea (liftedHamiltonian j B) p i =
      if i=j then planarHamiltonianField
        (fderiv ℝ (fun z => B ((outerMoments j p.2,p.1),z)) (p.2 j))
      else liftedAngularSpeed j i B p • (-(p.2 i).2,(p.2 i).1) := by
  have h₁ := hamiltonianField_contraction phaseArea_isInvertible (liftedHamiltonian j B) p
    (Pi.single i (0,1))
  have h₂ := hamiltonianField_contraction phaseArea_isInvertible (liftedHamiltonian j B) p
    (Pi.single i (1,0))
  simp only [phaseArea_single_right,planarArea_apply,mul_one,mul_zero,sub_zero,zero_sub] at h₁ h₂
  by_cases hij : i=j
  · subst i
    rw [ite_eq_left rfl]
    rw [liftedHamiltonian_fderiv_inner j hB] at h₁ h₂
    ext
    · exact h₁
    · dsimp [planarHamiltonianField]
      linarith
  · rw [ite_eq_right hij]
    rw [liftedHamiltonian_fderiv_outer j i hij hB] at h₁ h₂
    ext
    · dsimp
      nlinarith only [h₁]
    · dsimp
      nlinarith only [h₂]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_LiftedCompact
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem liftedHamiltonian_compact (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : HasCompactSupport B) : HasCompactSupport (liftedHamiltonian j B) := by
  obtain ⟨r,hr,hbound⟩ := hB.isBounded.exists_pos_norm_le
  let K : Set (ℝ × PlanePhase ι) := Icc (-r) r ×ˢ pi univ (fun _ => closedRoundDisk (2*r+1))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_univ_pi (fun i =>
    closedRoundDisk_isCompact _))
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hn
  have hb := hbound (liftArgument j p) (subset_closure hn)
  have hy : ‖outerMoments j p.2‖ ≤ r := (norm_fst_le _).trans ((norm_fst_le _).trans hb)
  have ht : ‖p.1‖ ≤ r := (norm_snd_le _).trans ((norm_fst_le _).trans hb)
  have hz : ‖p.2 j‖ ≤ r := (norm_snd_le _).trans hb
  apply hp
  refine ⟨?_,?_⟩
  · exact abs_le.mp ht
  · intro i _
    change radiusSq (p.2 i) ≤ (2*r+1)^2
    by_cases hij : i=j
    · subst i
      have h₁ : |(p.2 j).1| ≤ r := (norm_fst_le _).trans hz
      have h₂ : |(p.2 j).2| ≤ r := (norm_snd_le _).trans hz
      have hs₁ := (sq_le_sq₀ (abs_nonneg _) hr.le).mpr h₁
      have hs₂ := (sq_le_sq₀ (abs_nonneg _) hr.le).mpr h₂
      simp only [sq_abs] at hs₁ hs₂
      dsimp [radiusSq]
      nlinarith
    · have hpi : radialArea (p.2 i) ≤ r := by
        have hh := (norm_le_pi_norm (outerMoments j p.2) i).trans hy
        rw [outerMoments_other j p.2 hij,Real.norm_of_nonneg (by dsimp [radialArea,radiusSq] <;> positivity)] at hh
        exact hh
      have hs : 0 ≤ radiusSq (p.2 i) := by dsimp [radiusSq] <;> positivity
      have hpi1 : 1 ≤ Real.pi := (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)
      have he := mul_le_mul_of_nonneg_right hpi1 hs
      dsimp [radialArea] at hpi
      nlinarith

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaledPlanarHamiltonian_support (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : Continuous a) (hn : ∀ y, a y ≠ 0) {σ : ℝ}
    (hσ : ∀ p ∈ tsupport Ψ.hamiltonian, radialArea p.2 ≤ σ) :
    tsupport (scaledPlanarHamiltonian Ψ a χ) ⊆
      {p | p.1.1 ∈ tsupport χ ∧ radialArea p.2 ≤ σ*(a p.1.1)^2} := by
  apply closure_minimal
  · intro p hp
    have hc : χ p.1.1 ≠ 0 := by intro hz; apply hp; simp [scaledPlanarHamiltonian,hz]
    have hb : Ψ.hamiltonian ((p.1.1,χ p.1.1*Real.smoothTransition p.1.2),(a p.1.1)⁻¹ • p.2) ≠ 0 := by
      intro hz; apply hp; simp [scaledPlanarHamiltonian,hz]
    refine ⟨subset_tsupport χ hc,?_⟩
    have hh := mul_le_mul_of_nonneg_left (hσ _ (subset_tsupport _ hb)) (sq_nonneg (a p.1.1))
    rw [radialArea_smul] at hh
    have he : (a p.1.1)^2*((a p.1.1)⁻¹^2*radialArea p.2) = radialArea p.2 := by
      field_simp [hn p.1.1]
    rw [he] at hh
    simpa only [mul_comm] using hh
  · exact ((isClosed_tsupport χ).preimage continuous_fst.fst).inter
      (isClosed_le (radialArea_smooth.continuous.comp continuous_snd)
        (continuous_const.mul ((ha.comp continuous_fst.fst).pow 2)))

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem liftedHamiltonian_support_subset (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    : tsupport (liftedHamiltonian j B) ⊆
      {p : ℝ × PlanePhase ι | liftArgument j p ∈ tsupport B} := by
  apply closure_minimal
  · intro p hp
    exact subset_tsupport B hp
  · exact (isClosed_tsupport B).preimage (liftArgument_smooth j).continuous

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
open MeasureTheory
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trajectoryAngle_hasDerivAt (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (y : ι → ℝ) (x : Plane) (i : ι) (t : ℝ) :
    HasDerivAt (trajectoryAngle Ψ y x i) (trajectoryAngularSpeed Ψ y x i t) t := by
  have hc := trajectoryAngularSpeed_continuous Ψ y x i
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem liftedTrajectory_hasDerivAt (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) :
    HasDerivAt (liftedTrajectory Ψ j z)
      (hamiltonianField phaseArea (liftedHamiltonian j Ψ.hamiltonian)
        (t,liftedTrajectory Ψ j z t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  rw [liftedHamiltonian_field j Ψ.smooth,liftedTrajectory_moments]
  by_cases hij : i=j
  · subst i
    simp only [ite_true, if_true,liftedTrajectory_inner]
    exact Ψ.flow (outerMoments j z) t (z j)
  · rw [ite_eq_right hij]
    have hd := planeRotate_hasDerivAt
      (trajectoryAngle_hasDerivAt Ψ (outerMoments j z) (z j) i t) (z i)
    convert! hd using 1 <;> simp only [liftedAngularSpeed,liftArgument, liftedTrajectory_moments,trajectoryAngularSpeed,liftedTrajectory,hij,ite_false, if_false,ite_true, if_true]

theorem liftedTrajectory_continuous (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) : Continuous (liftedTrajectory Ψ j z) :=
  continuous_iff_continuousAt.mpr (fun t => (liftedTrajectory_hasDerivAt Ψ j z t).continuousAt)

end
section

variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem homeomorph_family_inverse_smooth (Φ : Q → E ≃ₜ E)
    (hΦ : ContDiff ℝ ∞ (fun p : Q × E => Φ p.1 p.2))
    (hi : ∀ q, ContDiff ℝ ∞ (Φ q).symm) :
    ContDiff ℝ ∞ (fun p : Q × E => (Φ p.1).symm p.2) := by
  obtain ⟨U,g,_,hg,hU,_,hright⟩ := parametric_inverse_on
    (fun p : Q × E => Φ p.1 p.2) hΦ (D := univ) isOpen_univ
    (fun q _ _ _ _ h => (Φ q).injective h)
    (fun p _ => homeomorph_fderiv_isInvertible (Φ p.1)
      ((hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hi p.1).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p.2)
  have hUall : U = univ := by
    rw [hU]
    apply eq_univ_of_forall
    intro p
    exact ⟨(p.1,(Φ p.1).symm p.2),mem_univ _,by simp⟩
  have he : g = fun p : Q × E => (Φ p.1).symm p.2 := by
    funext p
    apply (Φ p.1).injective
    rw [Homeomorph.apply_symm_apply]
    exact (hright p (hUall ▸ mem_univ p)).2
  rw [hUall] at hg
  rw [←he]
  exact contDiffOn_univ.mp hg

end
section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem trajectoryAngularSpeed_joint_smooth (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (i : ι) :
    ContDiff ℝ ∞ (fun p : ((ι → ℝ) × Plane) × ℝ =>
      trajectoryAngularSpeed Ψ p.1.1 p.1.2 i p.2) := by
  have hds : ContDiff ℝ ∞ (fun p => fderiv ℝ Ψ.hamiltonian p) :=
    Ψ.smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold trajectoryAngularSpeed
  exact contDiff_const.mul ((hds.comp
    ((contDiff_fst.fst.prodMk contDiff_snd).prodMk
      (hΨ.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)))).clm_apply
        contDiff_const)

theorem trajectoryAngle_joint_smooth (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (i : ι) :
    ContDiff ℝ ∞ (fun p : ((ι → ℝ) × Plane) × ℝ =>
      trajectoryAngle Ψ p.1.1 p.1.2 i p.2) :=
  contDiff_parameter_segment_integral (trajectoryAngularSpeed_joint_smooth Ψ hΨ i) 0

theorem liftedTrajectory_joint_smooth (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (j : ι) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => liftedTrajectory Ψ j p.2 p.1) := by
  apply contDiff_pi.mpr
  intro i
  have hm : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => outerMoments j p.2) :=
    (outerMoments_smooth j).comp contDiff_snd
  have hx : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => p.2 j) :=
    (contDiff_apply ℝ Plane j).comp contDiff_snd
  by_cases hij : i=j
  · subst i
    simp only [liftedTrajectory,ite_true, if_true]
    convert! hΨ.comp ((hm.prodMk contDiff_fst).prodMk hx) using 1
  · simp only [liftedTrajectory,hij,ite_false, if_false]
    have ha : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι =>
        trajectoryAngle Ψ (outerMoments j p.2) (p.2 j) i p.1) := by
      convert! (trajectoryAngle_joint_smooth Ψ hΨ i).comp
        ((hm.prodMk hx).prodMk contDiff_fst) using 1
      all_goals try with_reducible_and_instances rfl
    have hi : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => p.2 i) :=
      (contDiff_apply ℝ Plane i).comp contDiff_snd
    convert! planeRotate_smooth.comp (ha.prodMk hi) using 1
    all_goals try with_reducible_and_instances rfl

theorem exists_lifted_isotopy (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (j : ι) :
    ∃ Φ : ℝ → PlanePhase ι ≃ₜ PlanePhase ι,
      ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl _ ∧
      (∀ t z, z ∉ Prod.snd '' tsupport (liftedHamiltonian j Ψ.hamiltonian) → Φ t z = z) ∧
      (∀ t z v w, phaseArea (fderiv ℝ (Φ t) z v) (fderiv ℝ (Φ t) z w) = phaseArea v w) ∧
      (∀ t z, Φ t z = liftedTrajectory Ψ j z t) ∧
      (∀ t z, outerMoments j (Φ t z) = outerMoments j z) ∧
      (∀ t z, Φ t z j = Ψ.trace (outerMoments j z) t (z j)) := by
  have hex (t : ℝ) := exists_hamiltonian_endpoint
    phaseArea_isInvertible phaseArea_skew (liftedHamiltonian_smooth j Ψ.smooth)
    (liftedHamiltonian_compact j Ψ.compact) 0 t
  choose Φ _ hΦi hfix _ hsp hrec using hex
  have he (t : ℝ) (z : PlanePhase ι) : Φ t z = liftedTrajectory Ψ j z t := by
    simpa using hrec t (liftedTrajectory Ψ j z) (liftedTrajectory_continuous Ψ j z)
      (liftedTrajectory_hasDerivAt Ψ j z)
  have hs : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => Φ p.1 p.2) := by
    simpa only [he] using liftedTrajectory_joint_smooth Ψ hΨ j
  refine ⟨Φ,hs,homeomorph_family_inverse_smooth Φ hs hΦi,?_,hfix,hsp,he,?_,?_⟩
  · apply Homeomorph.ext
    intro z
    simpa using he 0 z
  · intro t z; rw [he]; exact liftedTrajectory_moments Ψ j z t
  · intro t z; rw [he]; exact liftedTrajectory_inner Ψ j z t

theorem exists_lifted_isotopy_object (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (j : ι) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea ι _),
      Φ.hamiltonian = liftedHamiltonian j Ψ.hamiltonian ∧
      (∀ t z, outerMoments j (Φ.map t z) = outerMoments j z) ∧
      (∀ t z, Φ.map t z j = Ψ.trace (outerMoments j z) t (z j)) := by
  obtain ⟨φ,hφ,hφi,hzero,hfix,hsp,he,hm,hj⟩ := exists_lifted_isotopy Ψ hΨ j
  refine ⟨{ map := φ
            smooth := hφ
            inverse_smooth := hφi
            zero := hzero
            hamiltonian := liftedHamiltonian j Ψ.hamiltonian
            hamiltonian_smooth := liftedHamiltonian_smooth j Ψ.smooth
            compact := liftedHamiltonian_compact j Ψ.compact
            flow := ?_
            symplectic := hsp
            fixed := hfix },rfl,hm,hj⟩
  intro t z
  simpa only [he] using liftedTrajectory_hasDerivAt Ψ j z t

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hamiltonianField_zero_off_support (A : E →L[ℝ] E →L[ℝ] ℝ)
    (H : ℝ × E → ℝ) {p : ℝ × E} (hp : p ∉ tsupport H) : hamiltonianField A H p = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hp (hamiltonianField_support A H h))

theorem exists_hamiltonian_support_collar (A : E →L[ℝ] E →L[ℝ] ℝ)
    {H : ℝ × E → ℝ} (hH : HasCompactSupport H) {q : E → ℝ} (hq : Continuous q)
    {c : ℝ} (hbelow : ∀ p ∈ tsupport H, q p.2 < c) :
    ∃ ρ > 0, ∀ t z, c-q z < ρ → hamiltonianField A H (t,z) = 0 := by
  rcases (tsupport H).eq_empty_or_nonempty with he | hn
  · refine ⟨1,zero_lt_one,fun t z _ => hamiltonianField_zero_off_support A H ?_⟩
    simp [he]
  · obtain ⟨p,hp,hmax⟩ := hH.exists_isMaxOn hn (hq.comp continuous_snd).continuousOn
    refine ⟨c-q p.2,sub_pos.mpr (hbelow p hp),?_⟩
    intro t z hz
    apply hamiltonianField_zero_off_support A H
    intro hm
    have hh : q z ≤ q p.2 := hmax hm
    linarith

end

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weightedMoment_fderiv (b : ι → ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (weightedMoment b) z v =
      ∑ i, b i*(2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2)) := by
  have hh (i : ι) := ((radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
    (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt).const_mul (b i)
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hh i)
  change fderiv ℝ (fun z => ∑ i, b i*radialArea (z i)) z v = _
  have hd' : HasFDerivAt (fun z : PlanePhase ι => ∑ i, b i*radialArea (z i))
      (∑ i, b i • (fderiv ℝ radialArea (z i)).comp (ContinuousLinearMap.proj i)) z := by
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
  rw [hd'.fderiv]
  simp

theorem lifted_field_commutes (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (b : ι → ℝ) (hb : b j=0) (p : ℝ × PlanePhase ι) :
    fderiv ℝ (weightedMoment b) p.2 (hamiltonianField phaseArea (liftedHamiltonian j B) p) = 0 := by
  rw [weightedMoment_fderiv]
  apply Finset.sum_eq_zero
  intro i _
  rw [liftedHamiltonian_field j hB]
  by_cases hi : i=j
  · subst i; simp [hb]
  · simp only [hi,ite_false, if_false,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian
open Comparison

variable {m N : ℕ}

theorem scaled_lift_support_below (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)]
    (Ψ : HamiltonianDiskIsotopyFamily (Moments m) (areaRadius 1))
    {a χ : Moments m → ℝ} (ha : Continuous a) (han : ∀ y, a y ≠ 0)
    (hfit : ∀ y ∈ tsupport χ, (a y)^2 < fullLength b c j y)
    (ν : Active b j) {p : ℝ × PlanePhase (Fin m)}
    (hp : p ∈ tsupport (liftedHamiltonian j (scaledPlanarHamiltonian Ψ.motion a χ))) :
    weightedMoment (b ν) p.2 < c ν := by
  obtain ⟨σ,hσ,hσ1,hs⟩ := Ψ.exists_support_margin
  have hp' := scaledPlanarHamiltonian_support Ψ.motion ha han hs
    (liftedHamiltonian_support_subset j hp)
  have hfit' := hfit (outerMoments j p.2) hp'.1
  have hrad : radialArea (p.2 j) < fullLength b c j (outerMoments j p.2) :=
    hp'.2.trans_lt ((mul_le_of_le_one_left (sq_nonneg _) hσ1.le).trans_lt hfit')
  have he := hrad.trans_le (length_le b c j ν (baseProjection j (outerMoments j p.2)))
  have hh := (lt_div_iff₀ ν.property).mp he
  change radialArea (p.2 j)*b ν j < c ν-∑ i : {i : Fin m // i ≠ j},
    b ν i.val*(baseProjection j (outerMoments j p.2)) i at hh
  rw [weightedMoment,Fintype.sum_eq_add_sum_subtype_ne _ j]
  have heq : ∑ i : {i : Fin m // i ≠ j}, b ν i.val*(baseProjection j (outerMoments j p.2)) i =
      ∑ i : {i : Fin m // i ≠ j}, b ν i.val*radialArea (p.2 i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [baseProjection,i.property]
  rw [heq] at hh
  linarith

theorem scaled_lift_face_collars (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (Ψ : HamiltonianDiskIsotopyFamily (Moments m) (areaRadius 1))
    {a χ : Moments m → ℝ} (ha : ContDiff ℝ ∞ a) (han : ∀ y, a y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hfit : ∀ y ∈ tsupport χ, (a y)^2 < fullLength b c j y) (ν : Fin N) :
    ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
      fderiv ℝ (weightedMoment (b ν)) z
        (hamiltonianField phaseArea (liftedHamiltonian j (scaledPlanarHamiltonian Ψ.motion a χ)) (t,z)) = 0 := by
  let H := liftedHamiltonian j (scaledPlanarHamiltonian Ψ.motion a χ)
  have hB := scaledPlanarHamiltonian_smooth Ψ.motion ha han hχ
  by_cases hj : 0 < b ν j
  · have hc : IsCompact (tsupport H) := liftedHamiltonian_compact j
      (scaledPlanarHamiltonian_compact Ψ.motion ha.continuous han hχc)
    have hbelow : ∀ p ∈ tsupport H, weightedMoment (b ν) p.2 < c ν := fun p hp =>
      scaled_lift_support_below b c j Ψ ha.continuous han hfit ⟨ν,hj⟩ hp
    obtain ⟨ρ,hρ,hzero⟩ := exists_hamiltonian_support_collar phaseArea hc
      (weightedMoment_smooth (b ν)).continuous hbelow
    refine ⟨ρ,hρ,?_⟩
    intro t z hz
    rw [hzero t z hz,map_zero]
  · have hj0 : b ν j=0 := le_antisymm (not_lt.mp hj) (hb ν j)
    exact ⟨1,zero_lt_one,fun t z _ => lifted_field_commutes j hB (b ν) hj0 (t,z)⟩

theorem exists_cartesian_lifted_rearrangement
    (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c))
    (F : C(Moments m,ℝ)) (hF : ConvexOn ℝ (region b c) F) {ε : ℝ} (he : 0 < ε) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _),
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (hz : z ∈ planeRegion b c), F (planeMoments (Φ.map 1 z)) ≤
        coordRearrange b c j hb (F.restrict (region b c)) ⟨planeMoments z,hz⟩+ε) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  obtain ⟨a,χ,Ψ,ha,hapos,hχ,hχc,hχrange,hfit,_,hest⟩ :=
    exists_scaled_slice_rearrangement_bp240 (fullBase_compact b c j hb hK)
      (continuous_fullLength b c j) (concave_fullLength b c j) (globalSliceFamily F j)
      (globalSliceFamily_convex b c j hb F hF) he
  let B := Ψ.motion.scaled a χ ha (fun y => (hapos y).ne') hχ hχc
  have hBs : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × Plane => B.trace p.1.1 p.1.2 p.2) :=
    scaledPlanarTrace_smooth Ψ.motion Ψ.isotopy.smooth ha (fun y => (hapos y).ne') hχ
  obtain ⟨Φ,hH,hm,hj⟩ := exists_lifted_isotopy_object B hBs j
  have hmem (t : ℝ) (z : PlanePhase (Fin m)) :
      Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c := by
    rw [planeRegion_mem_iff b c j hb,planeRegion_mem_iff b c j hb,hm,hj]
    apply and_congr_right
    intro _
    exact scaled_disk_slice_iff Ψ (outerMoments j z) (hapos _).ne' t (z j)
      (fun h => (hfit _ (subset_tsupport χ h)).le)
  refine ⟨Φ,hmem,?_,?_⟩
  · intro z hz
    have hzy := (planeRegion_mem_iff b c j hb z).mp hz
    have hh := hest (outerMoments j z) hzy.1 (z j) hzy.2
    have hfiber : fiberFunction (globalSliceFamily F j) (outerMoments j z) =
        fiberFunction (globalSliceFamily F j) (planeMoments z) := by
      apply ContinuousMap.ext
      intro h
      change F (assemble j (baseProjection j (outerMoments j z)) h) =
        F (assemble j (baseProjection j (planeMoments z)) h)
      rw [baseProjection_outerMoments]
    have hlen : fullLength b c j (outerMoments j z) = fullLength b c j (planeMoments z) := by
      unfold fullLength
      rw [baseProjection_outerMoments]
    rw [hfiber,hlen] at hh
    rw [←globalSliceFamily_at_moments F j (Φ.map 1 z),hm,hj,
      coordRearrange_eq_intervalMinimum b c j hb F ⟨planeMoments z,hz⟩]
    exact hh
  · intro ν
    rw [hH]
    exact scaled_lift_face_collars b c j hb Ψ ha (fun y => (hapos y).ne') hχ hχc hfit ν

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_DisjointClocks
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}
namespace CompactHamiltonianIsotopy

variable [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem concatMap_preserves (Φ Ψ : CompactHamiltonianIsotopy A) {S : Set E}
    (hΦ : ∀ t x, Φ.map t x ∈ S ↔ x ∈ S) (hΨ : ∀ t x, Ψ.map t x ∈ S ↔ x ∈ S)
    (t : ℝ) (x : E) : concatMap Φ Ψ t x ∈ S ↔ x ∈ S := by
  exact (hΦ _ _).trans (hΨ _ _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem concatHamiltonian_face (Φ Ψ : CompactHamiltonianIsotopy A) (q : E → ℝ)
    {c ρ : ℝ}
    (hΦ : ∀ t x, c-q x < ρ → fderiv ℝ q x (hamiltonianField A Φ.hamiltonian (t,x)) = 0)
    (hΨ : ∀ t x, c-q x < ρ → fderiv ℝ q x (hamiltonianField A Ψ.hamiltonian (t,x)) = 0)
    (t : ℝ) (x : E) (hx : c-q x < ρ) :
    fderiv ℝ q x (hamiltonianField A (concatHamiltonian Φ Ψ) (t,x)) = 0 := by
  rw [concatHamiltonian,hamiltonianField_add A
    (reparamHamiltonian_smooth Ψ.hamiltonian_smooth firstClock_smooth)
    (reparamHamiltonian_smooth Φ.hamiltonian_smooth secondClock_smooth),
    hamiltonianField_reparam A Ψ.hamiltonian_smooth firstClock_smooth,
    hamiltonianField_reparam A Φ.hamiltonian_smooth secondClock_smooth,map_add,map_smul,map_smul,
    hΦ _ _ hx,hΨ _ _ hx,smul_zero,smul_zero,zero_add]

end CompactHamiltonianIsotopy

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian Comparison
open scoped Pointwise
open MeasureTheory
section

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem exists_lifted_rearrangement_convex (j : Fin m) [Nonempty (Active b j)]
    (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c))
    (F : ConvexMaps (region b c) (convex_region b c)) {ε : ℝ} (he : 0 < ε) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _),
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (hz : z ∈ planeRegion b c), ∀ hz',
        F.val ⟨planeMoments (Φ.map 1 z),hz'⟩ ≤
          (coordOperator b c j hb F).val ⟨planeMoments z,hz⟩+ε) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  obtain ⟨f,hf⟩ := ContinuousMap.exists_extension hK.isClosed.isClosedEmbedding_subtypeVal F.val
  have heq (p : region b c) : f p.val = F.val p := congrArg (fun H : C(region b c,ℝ) => H p) hf
  have hconv : ConvexOn ℝ (region b c) f := by
    refine ⟨convex_region b c,?_⟩
    intro p hp q hq a d ha hd had
    simpa only [←heq,smul_eq_mul] using! F.property ⟨p,hp⟩ ⟨q,hq⟩ a d ha hd had
  obtain ⟨Φ,hmem,hest,hface⟩ := exists_cartesian_lifted_rearrangement b c j hb hK f hconv he
  refine ⟨Φ,hmem,?_,hface⟩
  intro z hz hz'
  have hext : f.restrict (region b c) = F.val := hf
  have hh := hest z hz
  rw [hext,heq ⟨_,hz'⟩] at hh
  exact hh

variable [∀ j, Nonempty (Active b j)]

theorem exists_successive_rearrangement (hb : ∀ ν i, 0 ≤ b ν i)
    (hK : IsCompact (region b c)) (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) {ε : ℝ} (he : 0 < ε) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _),
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (hz : z ∈ planeRegion b c), ∀ hz',
        F.val ⟨planeMoments (Φ.map 1 z),hz'⟩ ≤
          (successive b c hb js F).val ⟨planeMoments z,hz⟩+ε) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  induction js generalizing F ε with
  | nil =>
    refine ⟨CompactHamiltonianIsotopy.refl (@phaseArea (Fin m) _),?_,?_,?_⟩
    · intro t z
      rfl
    · intro z hz hz'
      change F.val ⟨planeMoments z,hz'⟩ ≤ F.val ⟨planeMoments z,hz⟩+ε
      exact le_add_of_nonneg_right he.le
    · intro ν
      refine ⟨1,zero_lt_one,fun _ _ _ => ?_⟩
      simp [CompactHamiltonianIsotopy.refl,hamiltonianField,formMoserField,spatialDifferential]
  | cons j js ih =>
    obtain ⟨Φ,hΦ,hΦest,hΦface⟩ := exists_lifted_rearrangement_convex b c j hb hK F (half_pos he)
    obtain ⟨Ψ,hΨ,hΨest,hΨface⟩ := ih (coordOperator b c j hb F) (half_pos he)
    let Γ := Φ.after phaseArea_isInvertible phaseArea_skew Ψ
    have hΓ (t : ℝ) (z : PlanePhase (Fin m)) : Γ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c :=
      Φ.concatMap_preserves Ψ hΦ hΨ t z
    refine ⟨Γ,hΓ,?_,?_⟩
    · intro z hz hz'
      have hy := (hΨ 1 z).mpr hz
      have hfirst := hΦest (Ψ.map 1 z) hy ((hΦ 1 _).mpr hy)
      have hsecond := hΨest z hz hy
      have hend : Γ.map 1 z = Φ.map 1 (Ψ.map 1 z) := Φ.concatMap_one Ψ z
      have hval : F.val ⟨planeMoments (Γ.map 1 z),hz'⟩ =
          F.val ⟨planeMoments (Φ.map 1 (Ψ.map 1 z)),(hΦ 1 _).mpr hy⟩ := by
        apply congrArg F.val
        apply Subtype.ext
        exact congrArg planeMoments hend
      rw [hval]
      change _ ≤ (successive b c hb js (coordOperator b c j hb F)).val ⟨planeMoments z,hz⟩+ε
      linarith
    · intro ν
      obtain ⟨a,ha,haf⟩ := hΦface ν
      obtain ⟨d,hd,hdf⟩ := hΨface ν
      refine ⟨min a d,lt_min ha hd,?_⟩
      intro t z hz
      exact Φ.concatHamiltonian_face Ψ (weightedMoment (b ν))
        (fun t z hz => haf t z (hz.trans_le (min_le_left _ _)))
        (fun t z hz => hdf t z (hz.trans_le (min_le_right _ _))) t z hz

end
section

variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

theorem hamiltonian_comparison (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 < c ν)
    (hcomp : IsCompact (region b c))
    (Q : ConvexMaps (region b c) (convex_region b c))
    {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a)
    (hmean : averageMap (region b c) hcomp Q.val < 0)
    (houter : ∀ p : region b c, p.val ∉ τ • region b c → Q.val p ≤ -a) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _)),
      ContDiff ℝ ∞ K ∧
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (_hz : z ∈ planeRegion b c), ∀ hz',
        K (planeMoments (Φ.map 1 z))+Q.val ⟨planeMoments (Φ.map 1 z),hz'⟩ < K (planeMoments z)) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  let : ∀ j, Nonempty (Active b j) := fun j => active_nonempty b c hb hc hcomp j
  obtain ⟨K,d,hd,hgap⟩ := analytic_gap b c hb hc hcomp Q hτ hτ1 ha hmean houter
  obtain ⟨Φ,hmem,hest,hface⟩ := exists_successive_rearrangement b c hb hcomp (List.finRange m)
    (affineStep 1 (by norm_num) Q K) (show 0 < d/4 by positivity)
  obtain ⟨k,hk,happrox⟩ := smooth_approximation (region b c) hcomp K.val (show 0 < d/4 by positivity)
  refine ⟨k,Φ,hk,hmem,?_,hface⟩
  intro z hz hz'
  have hout := happrox ⟨planeMoments (Φ.map 1 z),hz'⟩
  have hin := happrox ⟨planeMoments z,hz⟩
  rw [Real.dist_eq] at hout hin
  have ho := (abs_lt.mp hout).2
  have hi := (abs_lt.mp hin).1
  have he := hest z hz hz'
  have hg := hgap ⟨planeMoments z,hz⟩
  change (affineStep 1 (by norm_num) Q K).val ⟨planeMoments (Φ.map 1 z),hz'⟩ ≤
    (fullRearrangement b c hb (affineStep 1 (by norm_num) Q K)).val ⟨planeMoments z,hz⟩+d/4 at he
  simp only [affineStep, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, one_mul] at he hg
  linarith only [hd,ho,hi,he,hg]

end

theorem positive_hamiltonian_comparison {m N : ℕ}
    (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν i, 0 ≤ b ν i) (hc : ∀ ν, 0 < c ν)
    (hcomp : IsCompact (region b c))
    (P : Moments m → ℝ) (hP : ContinuousOn P (region b c))
    (hconc : ConcaveOn ℝ (region b c) P)
    (hmean : 0 < ∫ p in region b c, P p)
    {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a)
    (houter : ∀ p ∈ region b c, p ∉ τ • region b c → a ≤ P p) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _)),
      ContDiff ℝ ∞ K ∧
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z ∈ planeRegion b c,
        K (planeMoments (Φ.map 1 z))-P (planeMoments (Φ.map 1 z)) < K (planeMoments z)) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  let Q : ConvexMaps (region b c) (convex_region b c) :=
    ⟨⟨fun p => -P p, hP.domRestrict.neg⟩,by
      intro x y r s hr hs hrs
      change -P (r • (x : Moments m)+s • (y : Moments m)) ≤ r*(-P x)+s*(-P y)
      simpa only [Pi.neg_apply,smul_eq_mul] using
        (hconc.neg.2 x.property y.property hr hs hrs)⟩
  have he : zeroExtend (region b c) Q.val = (region b c).indicator (fun p => -P p) := by
    funext p
    by_cases hp : p ∈ region b c
    · simp only [zeroExtend,dite_eq_left hp,indicator_of_mem hp]
      rfl
    · simp [zeroExtend,hp]
  have hm : averageMap (region b c) hcomp Q.val < 0 := by
    change (volume (region b c)).toReal⁻¹ * (∫ p, zeroExtend (region b c) Q.val p) < 0
    rw [he,integral_indicator hcomp.measurableSet,integral_neg]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (volume_region_toReal_pos b c hc hcomp))
      (neg_neg_of_pos hmean)
  obtain ⟨K,Φ,hK,hmem,hgap,hface⟩ := hamiltonian_comparison b c hb hc hcomp Q
    hτ hτ1 ha hm (fun p hp => neg_le_neg (houter p p.property hp))
  refine ⟨K,Φ,hK,hmem,?_,hface⟩
  intro z hz
  have hg := hgap z hz ((hmem 1 z).2 hz)
  change K (planeMoments (Φ.map 1 z))+(-P (planeMoments (Φ.map 1 z))) < K (planeMoments z) at hg
  simpa only [sub_eq_add_neg] using hg

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function

variable {ι : Type*} [Fintype ι]

theorem isCompact_preimage_planeMoments {D : Set (ι → ℝ)} (hD : IsCompact D) :
    IsCompact (planeMoments ⁻¹' D) := by
  obtain ⟨R,hR⟩ := hD.isBounded.exists_norm_le
  have hp : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hclosed : IsClosed (planeMoments ⁻¹' D) :=
    hD.isClosed.preimage planeMoments_smooth.continuous
  apply (isCompact_closedBall (0 : PlanePhase ι) (|R|+1)).of_isClosed_subset hclosed
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ |R|+1)).2
  intro i
  have hm : planeMoments z i ≤ |R| :=
    (le_abs_self _).trans ((norm_le_pi_norm (planeMoments z) i).trans ((hR _ hz).trans (le_abs_self R)))
  have hs : (z i).1^2+(z i).2^2 ≤ planeMoments z i := by
    change (z i).1^2+(z i).2^2 ≤ Real.pi*((z i).1^2+(z i).2^2)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  apply max_le
  · nlinarith [sq_abs (z i).1,abs_nonneg (z i).1,sq_nonneg (z i).2,abs_nonneg R]
  · nlinarith [sq_abs (z i).2,abs_nonneg (z i).2,sq_nonneg (z i).1,abs_nonneg R]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff BigOperators
open Set Function
open Hamiltonian

theorem planeRegion_isCompact {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hC : IsCompact (region b c)) : IsCompact (planeRegion b c) :=
  isCompact_preimage_planeMoments hC

theorem planeRegion_nonempty {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hc : ∀ ν,0 ≤ c ν) : (planeRegion b c).Nonempty := by
  refine ⟨0,?_,⟩
  change (∀ j,0 ≤ planeMoments (0 : PlanePhase (Fin m)) j) ∧
    ∀ ν,∑ j,b ν j*planeMoments (0 : PlanePhase (Fin m)) j ≤ c ν
  refine ⟨fun j => planeMoments_nonneg _ _,fun ν => ?_⟩
  simpa [planeMoments,radialArea,radiusSq] using hc ν

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

theorem smoothUpperPositivePart_smooth {δ : ℝ} (hδ : 0<δ) :
    ContDiff ℝ ∞ (smoothUpperPositivePart δ) := by
  have hpos (x : ℝ) : 0<x^2+δ^2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hδ)
  apply (contDiff_id.add ((contDiff_id.pow 2).add contDiff_const |>.sqrt (fun x => ne_of_gt (hpos x)))).div_const

theorem smoothUpperPositivePart_bounds {δ : ℝ} (hδ : 0<δ) (x : ℝ) :
    max x 0 < smoothUpperPositivePart δ x ∧
      smoothUpperPositivePart δ x - max x 0 ≤ δ/2 := by
  have hp : 0 ≤ x^2+δ^2 := add_nonneg (sq_nonneg x) (sq_nonneg δ)
  have hroot := Real.sq_sqrt hp
  have hrootpos := Real.sqrt_nonneg (x^2+δ^2)
  have habs := sq_abs x
  have hgt : |x| < Real.sqrt (x^2+δ^2) := by nlinarith [sq_pos_of_pos hδ]
  have hle : Real.sqrt (x^2+δ^2) ≤ |x|+δ := by
    nlinarith [abs_nonneg x]
  rcases le_total 0 x with hx|hx
  · rw [max_eq_left hx,abs_of_nonneg hx] at *
    dsimp [smoothUpperPositivePart]
    constructor <;> linarith
  · rw [max_eq_right hx,abs_of_nonpos hx] at *
    dsimp [smoothUpperPositivePart]
    constructor <;> linarith

theorem exists_smooth_positive_caps {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (r : ι → ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ h : ι → (κ → ℝ) → ℝ,
      (∀ i, ContDiff ℝ ∞ (h i)) ∧
      (∀ i p, max (r i-∑ j, p j) 0 < h i p) ∧
      (∀ p, 0 < (∑ i, h i p)-(∑ i, max (r i-∑ j, p j) 0) ∧
        (∑ i, h i p)-(∑ i, max (r i-∑ j, p j) 0) < ε) := by
  classical
  let N : ℝ := Fintype.card ι
  have hN : 0<N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let δ := ε/N
  have hδ : 0<δ := div_pos hε hN
  let h : ι → (κ → ℝ) → ℝ := fun i p => smoothUpperPositivePart δ (r i-∑ j, p j)
  refine ⟨h,?_,?_,?_⟩
  · intro i
    exact (smoothUpperPositivePart_smooth hδ).comp (contDiff_const.sub (by fun_prop))
  · intro i p
    exact (smoothUpperPositivePart_bounds hδ _).1
  · intro p
    rw [←Finset.sum_sub_distrib]
    have hsum : (∑ i, (h i p-max (r i-∑ j, p j) 0)) ≤ N*(δ/2) := by
      calc
        _ ≤ ∑ _i : ι, δ/2 := Finset.sum_le_sum (fun i _ => (smoothUpperPositivePart_bounds hδ _).2)
        _ = N*(δ/2) := by simp [N]
    have hc : N*(δ/2)=ε/2 := by dsimp [δ]; field_simp
    refine ⟨Finset.sum_pos (fun i _ => sub_pos.mpr (smoothUpperPositivePart_bounds hδ _).1) Finset.univ_nonempty,?_⟩
    rw [hc] at hsum
    exact hsum.trans_lt (half_lt_self hε)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_SurfaceComparison
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators Pointwise
open Set Function MeasureTheory
open Hamiltonian Comparison

theorem compact_positive_lower {X : Type*} [TopologicalSpace X]
    {D : Set X} (hc : IsCompact D) (hne : D.Nonempty) {f : X → ℝ}
    (hf : ContinuousOn f D) (hp : ∀ x ∈ D,0<f x) :
    ∃ g>0, ∀ x ∈ D,g ≤ f x := by
  obtain ⟨x,hx,hm⟩ := hc.exists_isMinOn hne hf
  exact ⟨f x,hp x hx,hm⟩

theorem inverse_comparison_gap {m N : ℕ}
    (b : Fin N → Moments m) (c : Fin N → ℝ) (hc : ∀ ν,0 ≤ c ν)
    (hcomp : IsCompact (region b c))
    (K P : Moments m → ℝ) (hK : Continuous K) (hP : ContinuousOn P (region b c))
    (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _))
    (hmem : ∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c)
    (hgap : ∀ z ∈ planeRegion b c,
      K (planeMoments (Φ.map 1 z))-P (planeMoments (Φ.map 1 z)) < K (planeMoments z)) :
    ∃ g>0, ∀ v ∈ planeRegion b c,
      g ≤ K (planeMoments ((Φ.map 1).symm v))-K (planeMoments v)+P (planeMoments v) := by
  apply compact_positive_lower (planeRegion_isCompact b c hcomp) (planeRegion_nonempty b c hc)
  · exact ((hK.comp (planeMoments_smooth.continuous.comp (Φ.map 1).symm.continuous)).continuousOn.sub
      (hK.comp planeMoments_smooth.continuous).continuousOn).add
      (hP.comp planeMoments_smooth.continuous.continuousOn (fun _ hv => hv))
  · intro v hv
    have hg := hgap ((Φ.map 1).symm v) ((hmem 1 _).1 (by simpa using hv))
    simp only [Homeomorph.apply_symm_apply] at hg
    linarith

theorem finite_surface_comparison_bp240_oai {m N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j,0 ≤ b ν j) (hc : ∀ ν,0 < c ν) (hcomp : IsCompact (region b c))
    (H : Moments m → ℝ) (hH : ContinuousOn H (region b c))
    (hHpos : ∀ p ∈ region b c,0<H p) (r : ι → ℝ)
    (hconc : ConcaveOn ℝ (region b c) (fun p => H p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0 < ∫ p in region b c,H p-∑ i,max (r i-∑ j,p j) 0)
    {τ a : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (ha : 0<a)
    (houter : ∀ p ∈ region b c,p ∉ τ • region b c → a ≤ H p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ (K : Moments m → ℝ) (Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _))
      (g ε : ℝ) (h : ι → Moments m → ℝ),
      ContDiff ℝ ∞ K ∧ 0<g ∧ 0<ε ∧ 8*ε<g ∧
      (∀ p ∈ region b c,8*ε<H p) ∧
      (∀ i,ContDiff ℝ ∞ (h i)) ∧
      (∀ i p,max (r i-∑ j,p j) 0<h i p) ∧
      (∀ p,0<(∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0) ∧
        (∑ i,h i p)-(∑ i,max (r i-∑ j,p j) 0)<ε) ∧
      (∀ t z,Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ ν,∃ ρ>0,∀ t z,c ν-weightedMoment (b ν) z<ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z))=0) ∧
      (∀ Hstar : Moments m → ℝ,(∀ p ∈ region b c,|Hstar p-H p|<2*ε) →
        (∀ p ∈ region b c,0<Hstar p) ∧
        ∀ v ∈ planeRegion b c,g/2 < surfaceRemainder (K ∘ planeMoments)
          (Hstar ∘ planeMoments) (fun i => h i ∘ planeMoments) (Φ.map 1).symm v) := by
  have hcap : Continuous (fun p : Moments m => ∑ i,max (r i-∑ j,p j) 0) := by fun_prop
  obtain ⟨K,Φ,hK,hmem,hgap,hface⟩ := positive_hamiltonian_comparison b c hb hc hcomp
    (fun p => H p-∑ i,max (r i-∑ j,p j) 0) (hH.sub hcap.continuousOn)
    hconc hmean hτ hτ1 ha houter
  obtain ⟨g,hg,hgall⟩ := inverse_comparison_gap b c (fun ν => (hc ν).le) hcomp K _
    hK.continuous (hH.sub hcap.continuousOn) Φ hmem hgap
  have hne : (region b c).Nonempty := by
    refine ⟨0,?_,?_⟩
    · intro j; simp
    · intro ν; simpa using (hc ν).le
  obtain ⟨u,hu,huall⟩ := compact_positive_lower hcomp hne hH hHpos
  let ε := min g u/16
  have hε : 0<ε := div_pos (lt_min hg hu) (by norm_num)
  have he1 : 8*ε<g := by dsimp [ε]; have := min_le_left g u; nlinarith [lt_min hg hu]
  have he2 : 8*ε<u := by dsimp [ε]; have := min_le_right g u; nlinarith [lt_min hg hu]
  obtain ⟨h,hhs,hhu,hhe⟩ := exists_smooth_positive_caps (κ := Fin m) r hε
  refine ⟨K,Φ,g,ε,h,hK,hg,hε,he1,(fun p hp => he2.trans_le (huall p hp)),hhs,hhu,hhe,hmem,hface,?_⟩
  intro Hstar hstar
  refine ⟨?_,?_⟩
  · intro p hp
    have hs := (abs_lt.mp (hstar p hp)).1
    have hu' := huall p hp
    linarith
  · intro v hv
    have hg' := hgall v hv
    simp only [Pi.sub_apply] at hg'
    have heq : g ≤ K (planeMoments ((Φ.map 1).symm v))-K (planeMoments v)+
        H (planeMoments v)-(∑ i,max (r i-∑ j,planeMoments v j) 0) := by linarith
    have hr := surfaceRemainder_gap (ψ := (Φ.map 1).symm)
      (K := K ∘ planeMoments) (H := Hstar ∘ planeMoments)
      (H₀ := H ∘ planeMoments) (C := fun v => ∑ i,max (r i-∑ j,planeMoments v j) 0)
      (h := fun i => h i ∘ planeMoments) heq (hstar _ hv) (hhe (planeMoments v)).2
    exact (by linarith : g/2<g-3*ε).trans hr

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240_oai.{u_1} := @OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240_oai.{u_1}
