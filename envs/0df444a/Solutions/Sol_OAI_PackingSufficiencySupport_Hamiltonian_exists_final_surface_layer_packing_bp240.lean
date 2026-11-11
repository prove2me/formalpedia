-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:10.720747+00:00
-- url     : https://prove2.me/submissions/8282c0f4-c2e3-4d76-852f-27fbe4c57810

import Mathlib
import Definitions.Def_OAIQ240Bp010
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_thin_planar_embedding_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_BackgroundDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

theorem exists_smooth_compact_extension {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => χ x • f x) ∧
      HasCompactSupport (fun x => χ x • f x) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x • f x = f x) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU hKU
  have hg : ContDiff ℝ ∞ (fun x => χ x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hχU h)
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy,zero_smul,Pi.zero_apply]
  have hs : tsupport (fun x => χ x • f x) ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    apply hx
    change χ x • f x = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  refine ⟨χ,hχ,hχc,hχU,hχrange,hχ1,hg,
    hχc.of_isClosed_subset (isClosed_tsupport _) hs,?_⟩
  filter_upwards [hχ1] with x hx
  rw [hx,one_smul]

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


end

open scoped ContDiff Topology NNReal
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Kahler_PhaseArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseDiagonal_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseUnitDiagonal_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarCovector_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarDot_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialDiskChart_source _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_nonneg _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in

theorem inverse_chart_isEmbedding {f g : E → E} {U W : Set E}
    (hf : ContinuousOn f U) (hg : ContinuousOn g W)
    (himage : f '' U = W) (hl : ∀ x ∈ U, g (f x) = x)
    (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y) :
    Topology.IsEmbedding (fun y : W => g y) := by
  let e : PartialHomeomorph E E := {
    toFun := f
    invFun := g
    source := U
    target := W
    map_source' := fun x hx => himage ▸ mem_image_of_mem f hx
    map_target' := fun y hy => (hr y hy).1
    left_inv' := hl
    right_inv' := fun y hy => (hr y hy).2
    continuousOn_toFun := hf
    continuousOn_invFun := hg }
  exact e.symm.isEmbedding_restrict

theorem inverse_chart_pullback {f g : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ x ∈ U, ∀ v w,
      B (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w)
    {y : E} (hy : y ∈ W) (v w : E) :
    A (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) = B v w := by
  have hdf : DifferentiableAt ℝ f (g y) :=
    (hf.contDiffAt (hU.mem_nhds (hr y hy).1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdg : DifferentiableAt ℝ g y :=
    (hg.contDiffAt (hW.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : (f ∘ g) =ᶠ[𝓝 y] id :=
    Filter.eventually_of_mem (hW.mem_nhds hy) (fun z hz => (hr z hz).2)
  have hd : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ E := by
    rw [←fderiv_comp y hdf hdg,heq.fderiv_eq]
    exact fderiv_id
  calc
    A (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) =
      B (fderiv ℝ f (g y) (fderiv ℝ g y v))
        (fderiv ℝ f (g y) (fderiv ℝ g y w)) := (hform _ (hr y hy).1 _ _).symm
    _ = B v w := by
      change B ((fderiv ℝ f (g y)).comp (fderiv ℝ g y) v)
        ((fderiv ℝ f (g y)).comp (fderiv ℝ g y) w) = _
      rw [hd]
      rfl

theorem inverse_chart_composition_pullback {f g q : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ x ∈ U, ∀ v w,
      B (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w)
    (hq : ContDiff ℝ ∞ q)
    (hqform : ∀ x v w, B (fderiv ℝ q x v) (fderiv ℝ q x w) = B v w)
    {z : E} (hz : q z ∈ W) (v w : E) :
    A ((g ∘ q) z) (fderiv ℝ (g ∘ q) z v) (fderiv ℝ (g ∘ q) z w) = B v w := by
  have hdg : DifferentiableAt ℝ g (q z) :=
    (hg.contDiffAt (hW.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdq : DifferentiableAt ℝ q z := hq.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z
  rw [fderiv_comp z hdg hdq]
  simp only [ContinuousLinearMap.comp_apply,Function.comp_apply]
  rw [inverse_chart_pullback hU hW hf hg hr A B hform hz]
  exact hqform z v w

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
-- module Solutions.OAIQ240_BP.BallPacking_Layers_PlanarRotation
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem planarProduct_fderiv {q : Plane ≃ₜ Plane} (hq : ContDiff ℝ ∞ q)
    (p v : Plane × E) : fderiv ℝ (planarProduct q) p v = (fderiv ℝ q p.1 v.1,v.2) := by
  have hd := (((hq.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p.1).hasFDerivAt).comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (planarProduct q) _ p at hd
  rw [hd.fderiv]
  rfl

theorem planarProduct_pullback {q : Plane ≃ₜ Plane} (hq : ContDiff ℝ ∞ q)
    (hqs : ∀ x v w, planarArea (fderiv ℝ q x v) (fderiv ℝ q x w) = planarArea v w)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (p v w : Plane × E) :
    productForm B (fderiv ℝ (planarProduct q) p v) (fderiv ℝ (planarProduct q) p w) =
      productForm B v w := by
  rw [planarProduct_fderiv hq,planarProduct_fderiv hq]
  simp only [productForm_apply]
  rw [hqs]


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RearrangementBounds
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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

theorem radialArea_nonneg (x : Plane) : 0 ≤ radialArea x :=
  mul_nonneg Real.pi_pos.le (by dsimp [radiusSq] <;> positivity)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem planeMoments_nonneg (z : PlanePhase ι) (i : ι) : 0 ≤ planeMoments z i :=
  radialArea_nonneg (z i)

omit [DecidableEq ι] in
theorem planeMoments_hasFDerivAt (z : PlanePhase ι) :
    HasFDerivAt planeMoments (momentDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
    (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt

omit [DecidableEq ι] in
@[simp] theorem planeMoments_fderiv_apply (z v : PlanePhase ι) (i : ι) :
    fderiv ℝ planeMoments z v i = 2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2) := by
  rw [(planeMoments_hasFDerivAt z).fderiv]
  simp [momentDifferential]

theorem planeMoments_fderiv_single (i : ι) (z : PlanePhase ι) (w : Plane) :
    fderiv ℝ planeMoments z (Pi.single i w) =
      (2*Real.pi*((z i).1*w.1+(z i).2*w.2)) • Pi.single i (1:ℝ) := by
  funext j
  by_cases hji : j=i
  · subst j; simp
  · simp [hji]

theorem toricHamiltonian_fderiv_single {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) (i : ι) (w : Plane) :
    fderiv ℝ (toricHamiltonian F) p (0,Pi.single i w) =
      toricAngularSpeed F p.2 i*((p.2 i).1*w.1+(p.2 i).2*w.2) := by
  have hd := (hF.differentiable (by simp) (planeMoments p.2)).hasFDerivAt.comp p
    ((planeMoments_hasFDerivAt p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  change HasFDerivAt (toricHamiltonian F) _ p at hd
  rw [hd.fderiv]
  change fderiv ℝ F (planeMoments p.2) (momentDifferential p.2 (Pi.single i w)) = _
  rw [←(planeMoments_hasFDerivAt p.2).fderiv,planeMoments_fderiv_single,map_smul]
  dsimp [toricAngularSpeed]
  ring

theorem toricHamiltonian_field {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ × PlanePhase ι) (i : ι) :
    hamiltonianField phaseArea (toricHamiltonian F) p i =
      toricAngularSpeed F p.2 i • (-(p.2 i).2,(p.2 i).1) := by
  have h₁ := hamiltonianField_contraction phaseArea_isInvertible (toricHamiltonian F) p
    (Pi.single i (0,1))
  have h₂ := hamiltonianField_contraction phaseArea_isInvertible (toricHamiltonian F) p
    (Pi.single i (1,0))
  rw [phaseArea_single_right,toricHamiltonian_fderiv_single hF] at h₁ h₂
  simp only [planarArea_apply,mul_one,mul_zero,sub_zero,zero_sub,zero_add,add_zero] at h₁ h₂
  apply Prod.ext
  · change _ = toricAngularSpeed F p.2 i * -(p.2 i).2
    linarith
  · change _ = toricAngularSpeed F p.2 i * (p.2 i).1
    linarith

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_SmoothFormTransport
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_fderiv_apply_const {D G : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : D → G}
    (hf : ContDiff ℝ ∞ f) (p v w : D) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w = fderiv ℝ (fderiv ℝ f) p w v := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := (hfd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)
  rw [hh.fderiv]
  simp

theorem joint_spatial_fderiv {F : ℝ × E → E} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x v : E) :
    fderiv ℝ (fun y => F (t,y)) x v = fderiv ℝ F (t,x) (0,v) := by
  have hd := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (c := t) x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv

theorem joint_time_fderiv {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t) (p : ℝ × E) :
    fderiv ℝ F p (1,0) = X (p.1,F p) := by
  have hd := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.unique (hflow p.1 p.2)

theorem joint_flow_variation {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hX : ContDiff ℝ ∞ X)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    (t : ℝ) (x v : E) :
    HasDerivAt (fun s => fderiv ℝ F (s,x) (0,v))
      (fderiv ℝ X (t,F (t,x)) (0,fderiv ℝ F (t,x) (0,v))) t := by
  have hFd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV : ContDiff ℝ ∞ (fun p => fderiv ℝ F p (0,v)) := hFd.clm_apply contDiff_const
  have hd := (hV.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have he : (fun p => fderiv ℝ F p (1,0)) = fun p => X (p.1,F p) :=
    funext (joint_time_fderiv hF hflow)
  have hchain := (hX.differentiable (by simp) (t,F (t,x))).hasFDerivAt.comp (t,x)
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x))).prodMk
      (hF.differentiable (by simp) (t,x)).hasFDerivAt)
  have hc := congrArg (fun A : (ℝ × E) →L[ℝ] E => A (0,v)) hchain.fderiv
  change fderiv ℝ (fun p => X (p.1,F p)) (t,x) (0,v) = _ at hc
  have he' := congrArg (fun g : ℝ × E → E => fderiv ℝ g (t,x) (0,v)) he
  rw [smooth_fderiv_apply_const hF] at he'
  rw [hc] at he'
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply] at he'
  have hs := (hF.contDiffAt (x := (t,x))).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  apply hd.congr_deriv
  rw [smooth_fderiv_apply_const hF,hs.eq (1,0) (0,v)]
  exact he'

theorem smooth_flow_form_transport_on {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hX : ContDiff ℝ ∞ X)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω)
    {a b : ℝ} (hab : a ≤ b) (x v w : E)
    (hPDE : ∀ t ∈ Ioo a b, ∀ u z,
      fderiv ℝ Ω (t,F (t,x)) (1,X (t,F (t,x))) u z +
      Ω (t,F (t,x)) (fderiv ℝ X (t,F (t,x)) (0,u)) z +
      Ω (t,F (t,x)) u (fderiv ℝ X (t,F (t,x)) (0,z)) = 0) :
    Ω (b,F (b,x)) (fderiv ℝ (fun y => F (b,y)) x v)
      (fderiv ℝ (fun y => F (b,y)) x w) =
    Ω (a,F (a,x)) (fderiv ℝ (fun y => F (a,y)) x v)
      (fderiv ℝ (fun y => F (a,y)) x w) := by
  let V (s : ℝ) := fderiv ℝ F (s,x) (0,v)
  let W (s : ℝ) := fderiv ℝ F (s,x) (0,w)
  let G (s : ℝ) := Ω (s,F (s,x)) (V s) (W s)
  have hpath : Continuous (fun s => (s,F (s,x))) :=
    continuous_id.prodMk (hF.continuous.comp (continuous_id.prodMk continuous_const))
  have hFd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hVc : Continuous V := ((hFd.continuous.comp
    (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
  have hWc : Continuous W := ((hFd.continuous.comp
    (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
  have hGc : Continuous G := ((hΩ.continuous.comp hpath).clm_apply hVc).clm_apply hWc
  have hGd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt G 0 s := by
    have hdΩ := (hΩ.differentiable (by simp) (s,F (s,x))).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hflow s x))
    have hd := (hdΩ.clm_apply (joint_flow_variation hF hX hflow s x v)).clm_apply
      (joint_flow_variation hF hX hflow s x w)
    apply hd.congr_deriv
    simpa only [add_apply,Function.comp_apply,id_eq,V,W] using hPDE s hs (V s) (W s)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hGc.continuousOn hGd (intervalIntegrable_const (c := (0:ℝ)))
  have he : G b = G a := sub_eq_zero.mp (by simpa using hi.symm)
  simpa only [G,V,W,joint_spatial_fderiv hF] using he


end

section
open scoped ContDiff BigOperators
open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem toricFlow_time_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (toricFlow F t) := by
  convert! (toricFlow_smooth hF).comp (contDiff_const.prodMk contDiff_id) using 1
  all_goals try with_reducible_and_instances rfl

theorem toricFlow_hasDerivAt {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun s => toricFlow F s z)
      (hamiltonianField phaseArea (toricHamiltonian F) (t,toricFlow F t z)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hd := planeRotate_hasDerivAt ((hasDerivAt_id t).mul_const (toricAngularSpeed F z i)) (z i)
  apply hd.congr_deriv
  rw [toricHamiltonian_field hF,toricAngularSpeed_flow]
  simp only [one_mul,toricFlow,id_eq]

theorem toricFlow_symplectic {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z v w : PlanePhase ι) :
    phaseArea (fderiv ℝ (toricFlow F t) z v) (fderiv ℝ (toricFlow F t) z w) = phaseArea v w := by
  have hHs := toricHamiltonian_smooth hF
  have hXs := hamiltonianField_smooth phaseArea_isInvertible hHs
  have he (a b : ℝ) (hab : a ≤ b) :
      phaseArea (fderiv ℝ (toricFlow F b) z v) (fderiv ℝ (toricFlow F b) z w) =
      phaseArea (fderiv ℝ (toricFlow F a) z v) (fderiv ℝ (toricFlow F a) z w) := by
    apply smooth_flow_form_transport_on (toricFlow_smooth hF) hXs (toricFlow_hasDerivAt hF)
      (Ω := fun _ => phaseArea) contDiff_const hab z v w
    intro s _ u q
    simpa only [fderiv_const_apply,zero_apply,zero_add] using
      hamiltonianField_transport_equation phaseArea_isInvertible phaseArea_skew hHs
        (s,toricFlow F s z) u q
  have hzero : toricFlow F 0 = id := funext (toricFlow_zero F)
  by_cases ht : 0 ≤ t
  · simpa only [hzero,fderiv_id,ContinuousLinearMap.id_apply] using he 0 t ht
  · simpa only [hzero,fderiv_id,ContinuousLinearMap.id_apply] using (he t 0 (le_of_not_ge ht)).symm


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_flow_fderiv {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    (t τ : ℝ) (x v : E) :
    fderiv ℝ F (t,x) (τ,v) = τ • X (t,F (t,x)) +
      fderiv ℝ (fun y => F (t,y)) x v := by
  rw [show (τ,v) = τ • ((1,0) : ℝ × E) + (0,v) by ext <;> simp,
    map_add,map_smul,joint_time_fderiv hF hflow,joint_spatial_fderiv hF]

theorem suspension_form_identity {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hskew : ∀ v w, A v w = -A w v) {D : E →L[ℝ] E} {X : E} {η : E →L[ℝ] ℝ}
    (hsp : ∀ v w, A (D v) (D w) = A v w)
    (hX : ∀ v, A X (D v) = -η v) (v w : Plane × E) :
    productForm A (v.1,v.1.2 • X + D v.2) (w.1,w.1.2 • X + D w.2) =
      oneCovectorForm A 1 η v w := by
  have hXX : A X X = 0 := by have hh := hskew X X; linarith
  have hright : A (D v.2) X = η v.2 := by rw [hskew,hX,neg_neg]
  simp only [productForm_apply,oneCovectorForm_apply,planarArea_apply,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul,hXX,hsp,hX,hright]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem toricFlow_energy_differential {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (toricFunction F) (toricFlow F t z) (fderiv ℝ (toricFlow F t) z v) =
      fderiv ℝ (toricFunction F) z v := by
  have hs : ContDiff ℝ ∞ (toricFlow F t) := toricFlow_time_smooth hF t
  have he : toricFunction F ∘ toricFlow F t = toricFunction F := by
    funext z; simp [toricFunction]
  have hd := fderiv_comp z ((toricFunction_smooth hF).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    (hs.differentiable (by simp) _)
  rw [he] at hd
  exact (congrArg (fun L : PlanePhase ι →L[ℝ] ℝ => L v) hd).symm

theorem toricSuspension_fderiv {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p v : Plane × PlanePhase ι) :
    fderiv ℝ (toricSuspension F) p v =
      (v.1,v.1.2 • hamiltonianField phaseArea (toricHamiltonian F)
        (p.1.2,toricFlow F p.1.2 p.2) + fderiv ℝ (toricFlow F p.1.2) p.2 v.2) := by
  have hg := (toricFlow_smooth hF).differentiable (by simp)
  have hc := (hg (p.1.2,p.2)).hasFDerivAt.comp p
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
        (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hc
  change HasFDerivAt (toricSuspension F) _ p at hd
  rw [hd.fderiv]
  change (v.1,fderiv ℝ (fun q : ℝ × PlanePhase ι => toricFlow F q.1 q.2)
    (p.1.2,p.2) (v.1.2,v.2)) = _
  rw [joint_flow_fderiv (toricFlow_smooth hF) (toricFlow_hasDerivAt hF)]

theorem toricSuspension_pullback {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p v w : Plane × PlanePhase ι) :
    productForm phaseArea (fderiv ℝ (toricSuspension F) p v)
      (fderiv ℝ (toricSuspension F) p w) =
    oneCovectorForm phaseArea 1 (fderiv ℝ (toricFunction F) p.2) v w := by
  rw [toricSuspension_fderiv hF,toricSuspension_fderiv hF]
  apply suspension_form_identity phaseArea_skew (toricFlow_symplectic hF p.1.2 p.2)
  intro u
  rw [hamiltonianField_contraction phaseArea_isInvertible]
  have hh : fderiv ℝ (toricHamiltonian F) (p.1.2,toricFlow F p.1.2 p.2)
      (0,fderiv ℝ (toricFlow F p.1.2) p.2 u) =
      fderiv ℝ (toricFunction F) (toricFlow F p.1.2 p.2)
        (fderiv ℝ (toricFlow F p.1.2) p.2 u) := by
    have hd := ((toricFunction_smooth hF).differentiable (by simp) _).hasFDerivAt.comp
      (p.1.2,toricFlow F p.1.2 p.2) (hasFDerivAt_snd (𝕜 := ℝ))
    exact congrArg (fun L : (ℝ × PlanePhase ι) →L[ℝ] ℝ =>
      L (0,fderiv ℝ (toricFlow F p.1.2) p.2 u)) hd.fderiv
  rw [hh,toricFlow_energy_differential hF]


end

open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem layerForm_apply (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ)
    (p v w : Plane × PlanePhase ι) :
    layerForm F f p v w = phaseArea v.2 w.2 +
      (fderiv ℝ f p v + fderiv ℝ (toricFunction F) p.2 v.2)*w.1.2 -
      v.1.2*(fderiv ℝ f p w + fderiv ℝ (toricFunction F) p.2 w.2) := by
  simp [layerForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul,mul_add]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_LayerBallEmbedding
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem complexSplitPhase_capacity (m : ℕ) (z : Ambient (m+1)) :
    radialArea (complexSplitPhase m z).1 + ∑ j,planeMoments (complexSplitPhase m z).2 j = capacity z := by
  simp only [complexSplitPhase_apply,radialArea,radiusSq,planeMoments,capacity,Fin.sum_univ_succ,
    Complex.normSq_apply,Finset.mul_sum,mul_add,pow_two]

theorem complexSplitPhase_form (m : ℕ) (v w : Ambient (m+1)) :
    productForm phaseArea (complexSplitPhase m v) (complexSplitPhase m w)=standardForm v w := by
  simp only [productForm_apply,phaseArea_apply,complexSplitPhase_apply,standardForm,Fin.sum_univ_succ]
  rfl

@[simp] theorem complexSplitPhase_preimage_ball (m : ℕ) (r : ℝ) :
    complexSplitPhase m ⁻¹' splitCapacityBall r=closedBall (m+1) r := by
  ext z
  change radialArea (complexSplitPhase m z).1+∑ j,planeMoments (complexSplitPhase m z).2 j ≤ r ↔ capacity z ≤ r
  rw [complexSplitPhase_capacity]

theorem complex_ball_of_split_embedding {m : ℕ} {r : ℝ}
    {Ω : Plane × PlanePhase (Fin m) → (Plane × PlanePhase (Fin m)) →L[ℝ]
      (Plane × PlanePhase (Fin m)) →L[ℝ] ℝ}
    {N : Set (Plane × PlanePhase (Fin m))} {φ : Plane × PlanePhase (Fin m) → Plane × PlanePhase (Fin m)}
    (hN : IsOpen N) (hball : splitCapacityBall r ⊆ N) (hs : ContDiffOn ℝ ∞ φ N)
    (he : Topology.IsEmbedding (fun z : N => φ z))
    (hform : ∀ z ∈ N,∀ v w,Ω (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z w)=productForm phaseArea v w) :
    ∃ U : Set (Ambient (m+1)),IsOpen U ∧ closedBall (m+1) r ⊆ U ∧
      ContDiffOn ℝ ∞ (φ ∘ complexSplitPhase m) U ∧
      Topology.IsEmbedding (fun z : U => φ (complexSplitPhase m z)) ∧
      (∀ z ∈ U,φ (complexSplitPhase m z)∈φ '' N) ∧
      ∀ z ∈ U,∀ v w,Ω (φ (complexSplitPhase m z))
        (fderiv ℝ (φ ∘ complexSplitPhase m) z v) (fderiv ℝ (φ ∘ complexSplitPhase m) z w)=standardForm v w := by
  let e := complexSplitPhase m
  let U := e ⁻¹' N
  have hU : IsOpen U := hN.preimage e.continuous
  have hm : MapsTo e U N := fun _ hz => hz
  let j : U → N := fun z => ⟨e z,z.property⟩
  have hj : Topology.IsEmbedding j :=
    (e.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict N (fun z => z.property)
  refine ⟨U,hU,?_,hs.comp e.contDiff.contDiffOn hm,he.comp hj,?_,?_⟩
  · intro z hz
    apply hball
    have hz' : z∈e ⁻¹' splitCapacityBall r := by
      simpa only [e,complexSplitPhase_preimage_ball] using hz
    exact hz'
  · intro z hz
    exact mem_image_of_mem φ hz
  · intro z hz v w
    have hd := fderiv_comp z
      ((hs.contDiffAt (hN.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) e.differentiableAt
    rw [hd,e.fderiv]
    change Ω (φ (e z)) (fderiv ℝ φ (e z) (e v)) (fderiv ℝ φ (e z) (e w))=standardForm v w
    rw [hform (e z) hz,complexSplitPhase_form]


end

section
open scoped ContDiff Topology
open Set Function
variable {E F Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem parametric_inverse_on_local (f : Q × E → E)
    (D : Set (Q × E)) (hD : IsOpen D) (hf : ContDiffOn ℝ ∞ f D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible) :
    ∃ (U : Set (Q × E)) (g : Q × E → E), IsOpen U ∧ ContDiffOn ℝ ∞ g U ∧
      U = (fun p => (p.1,f p)) '' D ∧
      (∀ p ∈ D, (p.1,f p) ∈ U ∧ g (p.1,f p) = p.2) ∧
      (∀ p ∈ U, (p.1,g p) ∈ D ∧ f (p.1,g p) = p.2) := by
  let F : Q × E → Q × E := fun p => (p.1,f p)
  have hF : ContDiffOn ℝ ∞ F D := contDiffOn_fst.prodMk hf
  have hFi : InjOn F D := by
    rintro ⟨t,x⟩ hp ⟨s,y⟩ hq he
    have ht : t = s := congrArg (fun z : Q × E => z.1) he
    cases ht
    have hx : f (t,x) = f (t,y) := congrArg (fun z : Q × E => z.2) he
    exact Prod.ext rfl (hinj t hp hq hx)
  have hFd (p : Q × E) (hp : p∈D) : fderiv ℝ F p =
      (ContinuousLinearMap.fst ℝ Q E).prod (fderiv ℝ f p) := by
    exact (hasFDerivAt_fst.prodMk ((hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt).fderiv
  have hFiv (p : Q × E) (hp : p ∈ D) : (fderiv ℝ F p).IsInvertible := by
    rw [hFd p hp]
    apply clockGraph_linear_invertible
    have hd : fderiv ℝ (fun x => f (p.1,x)) p.2 =
        (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ Q E) := by
      exact (((hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
    rw [← hd]
    exact hi p hp
  obtain ⟨hU,hg,hleft,hright⟩ := smooth_inverse_on hD hF hFi hFiv
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

section
open scoped ContDiff Topology
open Set Function
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem monotone_strip_inverse_local {f : Q × ℝ → ℝ}
    {U : Set Q} (hU : IsOpen U) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Icc a b)) {h : Q → ℝ}
    (hderiv : ∀ q ∈ U, ∀ s ∈ Ioo a b, 0 < deriv (fun r => f (q,r)) s)
    (hlo : ∀ q ∈ U, f (q,a) = 0) (hhi : ∀ q ∈ U, h q < f (q,b)) :
    ∃ (W : Set (Q × ℝ)) (g : Q × ℝ → ℝ), IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = (fun p : Q × ℝ => (p.1,f p)) '' (U ×ˢ Ioo a b) ∧
      (∀ q ∈ U, ∀ x, 0 < x → x < h q → (q,x) ∈ W) ∧
      (∀ q ∈ U, ∀ s ∈ Ioo a b, g (q,f (q,s)) = s) ∧
      (∀ p ∈ W, p.1 ∈ U ∧ g p ∈ Ioo a b ∧ f (p.1,g p) = p.2) := by
  have hc (q : Q) (hq : q∈U) : ContinuousOn (fun s => f (q,s)) (Icc a b) :=
    hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => ⟨hq,hs⟩)
  have hm (q : Q) (hq : q ∈ U) : StrictMonoOn (fun s => f (q,s)) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) (hc q hq)
    simpa only [interior_Icc] using hderiv q hq
  have hinj (q : Q) : InjOn (fun s => f (q,s)) {s | (q,s) ∈ U ×ˢ Ioo a b} := by
    intro s hs t ht he
    exact (hm q hs.1).injOn ⟨hs.2.1.le,hs.2.2.le⟩ ⟨ht.2.1.le,ht.2.2.le⟩ he
  have hiv (p : Q × ℝ) (hp : p ∈ U ×ˢ Ioo a b) :
      (fderiv ℝ (fun s => f (p.1,s)) p.2).IsInvertible := by
    let c := deriv (fun s => f (p.1,s)) p.2
    have hc0 : c ≠ 0 := ne_of_gt (hderiv p.1 hp.1 p.2 hp.2)
    let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ c hc0).toContinuousLinearEquiv
    refine ⟨e,?_⟩
    ext
    simp [e,c]
  obtain ⟨W,g,hWo,hgs,hWe,hleft,hright⟩ := parametric_inverse_on_local f
    (U ×ˢ Ioo a b) (hU.prod isOpen_Ioo) (hf.mono (prod_mono_right Ioo_subset_Icc_self)) hinj hiv
  refine ⟨W,g,hWo,hgs,hWe,?_,?_,?_⟩
  · intro q hq x hx0 hxh
    have hh : x ∈ Ioo (f (q,a)) (f (q,b)) := ⟨by rwa [hlo q hq],hxh.trans (hhi q hq)⟩
    obtain ⟨s,hs,hse⟩ := intermediate_value_Ioo hab.le (hc q hq) hh
    rw [hWe]
    exact ⟨(q,s),⟨hq,hs⟩,Prod.ext rfl hse⟩
  · intro q hq s hs
    exact (hleft (q,s) ⟨hq,hs⟩).2
  · intro p hp
    exact ⟨(hright p hp).1.1,(hright p hp).1.2,(hright p hp).2⟩


end

open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem stripChart_inverse_local {f : Plane × E → ℝ}
    {V : Set E} (hV : IsOpen V) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V)) (H : E → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, H v < f ((b,T),v)) :
    ∃ (W : Set (Plane × E)) (g : Plane × E → Plane × E),
      IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = stripChart f '' ((Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V) ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → p.2 ∈ V → 0 < p.1.1 → p.1.1 < H p.2 → p ∈ W) ∧
      (∀ p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V, g (stripChart f p) = p) ∧
      (∀ p ∈ W, g p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V ∧ stripChart f (g p) = p) := by
  let e : (Plane × E) ≃L[ℝ] ((ℝ × E) × ℝ) := layerOrder
  let f' : (ℝ × E) × ℝ → ℝ := f ∘ e.symm
  have hf' : ContDiffOn ℝ ∞ f' ((Ioo (0:ℝ) 1 ×ˢ V) ×ˢ Icc a b) :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ hp => ⟨⟨hp.2,hp.1.1⟩,hp.1.2⟩)
  obtain ⟨W,g,hWo,hgs,hWe,havailable,hleft,hright⟩ := monotone_strip_inverse_local
    (isOpen_Ioo.prod hV) hab hf' (h := fun q : ℝ × E => H q.2)
    (fun q hq s hs => hderiv q.1 hq.1 q.2 hq.2 s hs)
    (fun q hq => hlo q.1 hq.1 q.2 hq.2)
    (fun q hq => hhi q.1 hq.1 q.2 hq.2)
  let G : Plane × E → Plane × E := fun p => ((g (e p),p.1.2),p.2)
  refine ⟨e ⁻¹' W,G,hWo.preimage e.continuous,?_,?_,?_,?_,?_⟩
  · have hg : ContDiffOn ℝ ∞ (fun p => g (e p)) (e ⁻¹' W) :=
      hgs.comp e.contDiff.contDiffOn (fun _ hp => hp)
    exact (hg.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn
  · ext p
    constructor
    · intro hp
      obtain ⟨q,hq,hqe⟩ := by simpa only [hWe] using hp
      refine ⟨e.symm q,⟨⟨hq.2,hq.1.1⟩,hq.1.2⟩,?_⟩
      apply e.injective
      change (q.1,f' q) = e p
      exact hqe
    · rintro ⟨q,hq,rfl⟩
      change e (stripChart f q) ∈ W
      rw [hWe]
      exact ⟨e q,⟨⟨hq.1.2,hq.2⟩,hq.1.1⟩,rfl⟩
  · intro p hpT hpV hp0 hpH
    exact havailable (p.1.2,p.2) ⟨hpT,hpV⟩ p.1.1 hp0 hpH
  · intro p hp
    have hh := hleft (p.1.2,p.2) ⟨hp.1.2,hp.2⟩ p.1.1 hp.1.1
    change ((g ((p.1.2,p.2),f p),p.1.2),p.2) = p
    change g ((p.1.2,p.2),f p) = p.1.1 at hh
    rw [hh]
  · intro p hp
    have hh := hright (e p) hp
    refine ⟨⟨⟨hh.2.1,hh.1.1⟩,hh.1.2⟩,?_⟩
    change ((f ((g (e p),p.1.2),p.2),p.1.2),p.2) = p
    have he : f ((g (e p),p.1.2),p.2) = p.1.1 := hh.2.2
    rw [he]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_LayerCoordinates
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem stripChart_fderiv_at {f : Plane × PlanePhase ι → ℝ} (p : Plane × PlanePhase ι) (hf : ContDiffAt ℝ ∞ f p)
    (v : Plane × PlanePhase ι) : fderiv ℝ (stripChart f) p v = ((fderiv ℝ f p v,v.1.2),v.2) := by
  have hd := (((hf.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt).prodMk
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (stripChart f) _ p at hd
  rw [hd.fderiv]
  rfl

theorem layerChart_pullback_at {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (p : Plane × PlanePhase ι) (hf : ContDiffAt ℝ ∞ f p) (v w : Plane × PlanePhase ι) :
    productForm phaseArea (fderiv ℝ (layerChart F f) p v)
      (fderiv ℝ (layerChart F f) p w) = layerForm F f p v w := by
  have hs : DifferentiableAt ℝ (stripChart f) p :=
    ((hf.prodMk (contDiffAt_snd.comp p contDiffAt_fst)).prodMk contDiffAt_snd).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [layerChart,fderiv_comp p ((toricSuspension_smooth hF).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    hs]
  simp only [ContinuousLinearMap.comp_apply]
  rw [toricSuspension_pullback hF,stripChart_fderiv_at p hf,stripChart_fderiv_at p hf,
    oneCovectorForm_apply,layerForm_apply]
  change phaseArea v.2 w.2 + 1*(fderiv ℝ f p v*w.1.2-v.1.2*fderiv ℝ f p w) +
    fderiv ℝ (toricFunction F) p.2 v.2*w.1.2-v.1.2*fderiv ℝ (toricFunction F) p.2 w.2 = _
  ring

theorem layerChart_inverse_local {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v)) :
    ∃ (W : Set (Plane × PlanePhase ι)) (g : Plane × PlanePhase ι → Plane × PlanePhase ι),
      IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = layerChart F f '' ((Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → planeMoments p.2 ∈ V →
        0 < p.1.1 → p.1.1 < H (planeMoments p.2) → p ∈ W) ∧
      (∀ p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V), g (layerChart F f p) = p) ∧
      (∀ p ∈ W, g p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V) ∧ layerChart F f (g p) = p) := by
  obtain ⟨W,g,hWo,hgs,hWe,hav,hl,hr⟩ := stripChart_inverse_local hV hab hf (H ∘ planeMoments) hderiv hlo hhi
  let e := toricSuspensionHomeomorph hF
  let G := g ∘ toricSuspensionInverse F
  have hpre : e.symm ⁻¹' W = e '' W := by
    ext p
    exact ⟨fun hp => ⟨e.symm p,hp,e.apply_symm_apply p⟩,by rintro ⟨p,hp,rfl⟩; simpa using hp⟩
  refine ⟨e '' W,G,e.isOpen_image.mpr hWo,?_,?_,?_,?_,?_⟩
  · apply hgs.comp (toricSuspensionInverse_smooth hF).contDiffOn
    intro p hp
    change p ∈ e.symm ⁻¹' W
    rw [hpre]
    exact hp
  · rw [hWe,←image_comp]
    rfl
  · intro p hpT hpV hp0 hpH
    refine ⟨e.symm p,?_,e.apply_symm_apply p⟩
    apply hav (e.symm p) hpT
    · change planeMoments (toricSuspensionInverse F p).2 ∈ V
      simpa only [toricSuspensionInverse_moments] using hpV
    · exact hp0
    · change p.1.1 < H (planeMoments (toricSuspensionInverse F p).2)
      simpa using hpH
  · intro p hp
    change g (toricSuspensionInverse F (toricSuspension F (stripChart f p))) = p
    rw [toricSuspensionInverse_left]
    exact hl p hp
  · rintro p ⟨z,hz,rfl⟩
    have hge : G (e z) = g z := by
      change g (toricSuspensionInverse F (toricSuspension F z)) = g z
      rw [toricSuspensionInverse_left]
    rw [hge]
    refine ⟨(hr z hz).1,?_⟩
    change toricSuspension F (stripChart f (g z)) = toricSuspension F z
    rw [(hr z hz).2]


end

section
open scoped ContDiff Topology BigOperators
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem inverse_layer_product_pullback_local {F : (ι → ℝ) → ℝ}
    {g : Plane × PlanePhase ι → Plane × PlanePhase ι}
    {f₀ : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {U W : Set (Plane × PlanePhase ι)} (hU : IsOpen U) (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f₀ U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ layerChart F f₀ (g y) = y)
    {q : Plane ≃ₜ Plane} (hqs : ContDiff ℝ ∞ q)
    (hqform : ∀ x v w, planarArea (fderiv ℝ q x v) (fderiv ℝ q x w) = planarArea v w)
    {z : Plane × PlanePhase ι} (hz : planarProduct q z ∈ W) (v w : Plane × PlanePhase ι) :
    layerForm F f₀ ((g ∘ planarProduct q) z)
      (fderiv ℝ (g ∘ planarProduct q) z v) (fderiv ℝ (g ∘ planarProduct q) z w) =
      productForm phaseArea v w := by
  exact inverse_chart_composition_pullback
    (E := Plane × PlanePhase ι) (f := layerChart F f₀) (g := g)
    (q := (planarProduct q : Plane × PlanePhase ι → Plane × PlanePhase ι))
    (U := U) (W := W) hU hW
    ((toricSuspension_smooth hF).contDiffOn.comp
      ((hf.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn) (fun _ _ => mem_univ _)) hg hr (layerForm F f₀) (productForm phaseArea)
    (fun x hx u t => layerChart_pullback_at hF x (hf.contDiffAt (hU.mem_nhds hx)) u t) (planarProduct_smooth (E := PlanePhase ι) (q := q) hqs)
    (fun x u t => planarProduct_pullback (E := PlanePhase ι) (q := q) hqs hqform (phaseArea (ι := ι)) x u t) hz v w

theorem exists_ball_in_layer_local {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v))
    {r r' : ℝ} (hr' : 0 ≤ r') (hrr : r' < r)
    (hsimplex : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) ≤ r' → p ∈ V)
    (hheight : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → p ∈ V → r-∑ i, p i ≤ H p) :
    ∃ (N : Set (Plane × PlanePhase ι)) (φ : Plane × PlanePhase ι → Plane × PlanePhase ι),
      IsOpen N ∧ splitCapacityBall r' ⊆ N ∧ ContDiffOn ℝ ∞ φ N ∧
      Topology.IsEmbedding (fun z : N => φ z) ∧
      (∀ z ∈ N, φ z ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ z ∈ N, ∀ v w, layerForm F f (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z w) =
        productForm phaseArea v w) := by
  let U := (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).prod hV
  have hfU : ContDiffOn ℝ ∞ f U := hf.mono
    (prod_mono (prod_mono Ioo_subset_Icc_self Subset.rfl) Subset.rfl)
  have hchart : ContDiffOn ℝ ∞ (layerChart F f) U :=
    (toricSuspension_smooth hF).contDiffOn.comp
      ((hfU.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn)
      (fun _ _ => mem_univ _)
  obtain ⟨W,g,hW,hg,himage,ha,hl,hr⟩ := layerChart_inverse_local hF hV hab hf H hderiv hlo hhi
  let δ := (r-r')/2
  have hδ : 0 < δ := by dsimp [δ] <;> linarith
  have hδr : r'+δ < r := by dsimp [δ] <;> linarith
  obtain ⟨q,hqs,_,hqform,hqbound⟩ := exists_thin_planar_embedding_bp240 hr' hδ
  let Q : (Plane × PlanePhase ι) ≃ₜ (Plane × PlanePhase ι) := planarProduct q
  have hQ : ContDiff ℝ ∞ Q := planarProduct_smooth hqs
  let N := Q ⁻¹' W
  let φ := g ∘ Q
  have hN : IsOpen N := hW.preimage Q.continuous
  have hball : splitCapacityBall r' ⊆ N := by
    intro z hz
    have hsum : 0 ≤ ∑ i, planeMoments z.2 i :=
      Finset.sum_nonneg (fun i _ => planeMoments_nonneg z.2 i)
    have hz' : radialArea z.1 + ∑ i, planeMoments z.2 i ≤ r' := hz
    have hrad : radialArea z.1 ≤ r' := by linarith
    have hps : (∑ i, planeMoments z.2 i) ≤ r' := by linarith [radialArea_nonneg z.1]
    have hpV := hsimplex (planeMoments z.2) (planeMoments_nonneg z.2) hps
    have hqb := hqbound z.1 hrad
    apply ha (Q z) hqb.2.2 hpV hqb.1
    change (q z.1).1 < H (planeMoments z.2)
    have hh := hheight (planeMoments z.2) (planeMoments_nonneg z.2) hpV
    linarith [hqb.2.1]
  have hsφ : ContDiffOn ℝ ∞ φ N := hg.comp hQ.contDiffOn (fun _ hz => hz)
  have hge : Topology.IsEmbedding (fun y : W => g y) :=
    inverse_chart_isEmbedding hchart.continuousOn
      hg.continuousOn himage.symm hl hr
  let j : N → W := fun z => ⟨Q z,z.property⟩
  have hje : Topology.IsEmbedding j :=
    (Q.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict W (fun z => z.property)
  refine ⟨N,φ,hN,hball,hsφ,hge.comp hje,?_,?_⟩
  · intro z hz
    exact (hr (Q z) hz).1
  · intro z hz v w
    exact inverse_layer_product_pullback_local hF hU hW hfU hg hr hqs hqform hz v w


end

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem finite_layer_packing_local {m : ℕ} {ι : Type*}
    (F H : ι → (Fin m → ℝ) → ℝ)
    (f : ι → Plane × PlanePhase (Fin m) → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i))
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    (a b r r' : ι → ℝ) (hab : ∀ i, a i < b i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i)
      ((Icc (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hderiv : ∀ i, ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo (a i) (b i),
      0 < deriv (fun u => f i ((u,T),v)) s)
    (hlo : ∀ i, ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f i ((a i,T),v) = 0)
    (hhi : ∀ i, ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V →
      H i (planeMoments v) < f i ((b i,T),v))
    (hr' : ∀ i, 0 ≤ r' i) (hrr : ∀ i, r' i < r i)
    (hsimplex : ∀ i, ∀ p : Fin m → ℝ, (∀ j, 0 ≤ p j) → (∑ j, p j) ≤ r' i → p ∈ V)
    (hheight : ∀ i, ∀ p : Fin m → ℝ, (∀ j, 0 ≤ p j) → p ∈ V → r i - ∑ j, p j ≤ H i p)
    (Ω : Plane × PlanePhase (Fin m) → (Plane × PlanePhase (Fin m)) →L[ℝ]
      (Plane × PlanePhase (Fin m)) →L[ℝ] ℝ)
    (hΩ : ∀ i, ∀ z ∈ (Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V),
      Ω z = layerForm (F i) (f i) z) :
    ∃ (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m)),
      (∀ i, IsOpen (U i)) ∧ (∀ i, closedBall (m+1) (r' i) ⊆ U i) ∧
      (∀ i, ContDiffOn ℝ ∞ (φ i) (U i)) ∧
      (∀ i, Topology.IsEmbedding (fun z : U i => φ i z)) ∧
      (∀ i, ∀ z ∈ U i, φ i z ∈ (Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i, ∀ z ∈ U i, ∀ v w, Ω (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z w) = standardForm v w) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
        (φ j '' closedBall (m+1) (r' j))) := by
  classical
  choose N q hN hb hq he him hfq using fun i =>
    exists_ball_in_layer_local (hF i) hV (hab i) (hf i) (H i)
      (hderiv i) (hlo i) (hhi i) (hr' i) (hrr i) (hsimplex i) (hheight i)
  choose U hU hBU hsU heU hiU hfU using fun i =>
    complex_ball_of_split_embedding (hN i) (hb i) (hq i) (he i) (hfq i)
  let φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m) := fun i => q i ∘ complexSplitPhase m
  have himage : ∀ i, ∀ z ∈ U i,
      φ i z ∈ (Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V) := by
    intro i z hz
    obtain ⟨y,hy,heq⟩ := hiU i z hz
    change q i (complexSplitPhase m z) ∈ _
    rw [←heq]
    exact him i y hy
  refine ⟨U,φ,hU,hBU,hsU,heU,himage,?_,?_⟩
  · intro i z hz v w
    rw [hΩ i _ (himage i z hz)]
    exact hfU i z hz v w
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    have hi := himage i x (hBU i hx)
    have hj := himage j y (hBU j hy)
    rw [heq] at hj
    exact Set.disjoint_left.mp (hdis hij) hi.1.1 hj.1.1


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffAt_parameter_segment_integral {f : P × ℝ → ℝ} {U : Set (P × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a : ℝ) (p : P × ℝ)
    (hseg : ∀ s ∈ Icc (0:ℝ) 1, (p.1,a+s*(p.2-a)) ∈ U) :
    ContDiffAt ℝ ∞ (fun q : P × ℝ => ∫ x in a..q.2, f (q.1,x)) p := by
  let K : Set (P × ℝ) := (fun s : ℝ => (p.1,a+s*(p.2-a))) '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_const.prodMk (continuous_const.add (continuous_id.mul continuous_const)))
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK hU
    (by rintro _ ⟨s,hs,rfl⟩; exact hseg s hs) hf
  let g : P × ℝ → ℝ := fun q => χ q • f q
  have hnear : ∀ᶠ q in 𝓝 p, ∀ s ∈ Icc (0:ℝ) 1,
      g (q.1,a+s*(q.2-a)) = f (q.1,a+s*(q.2-a)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hc : Continuous (fun z : (P × ℝ) × ℝ => (z.1.1,a+z.2*(z.1.2-a))) :=
      (continuous_fst.fst).prodMk
        (continuous_const.add (continuous_snd.mul (continuous_fst.snd.sub continuous_const)))
    have hk : (p.1,a+s*(p.2-a)) ∈ K := ⟨s,hs,rfl⟩
    exact (hc.continuousAt (x := (p,s))).eventually (he.filter_mono (nhds_le_nhdsSet hk))
  apply (contDiff_parameter_segment_integral hg a).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ segment ℝ a q.2 := by simpa only [segment_eq_uIcc] using hx
  rw [segment_eq_image' ℝ a q.2] at hx'
  obtain ⟨s,hs,rfl⟩ := hx'
  exact (hq s hs).symm

theorem contDiffOn_parameter_segment_integral {f : P × ℝ → ℝ} {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) (a : ℝ) (ha : a ∈ I)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun q : P × ℝ => ∫ x in a..q.2, f (q.1,x)) (V ×ˢ I) := by
  intro p hp
  apply (contDiffAt_parameter_segment_integral (hV.prod hI) hf a p ?_).contDiffWithinAt
  intro s hs
  refine ⟨hp.1,?_⟩
  have hm := hc ha hp.2 (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  simp only [smul_eq_mul]
  ring


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem layerAreaIntegral_smooth {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {ℓ : Plane → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1)) :
    ContDiffOn ℝ ∞ (layerAreaIntegral ℓ a) (I ×ˢ Ioo (0:ℝ) 1) := by
  have hs : ContDiffOn ℝ ∞ (fun q : Plane => ℓ (q.2,q.1)) (Ioo (0:ℝ) 1 ×ˢ I) :=
    hℓ.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)
  exact (contDiffOn_parameter_segment_integral isOpen_Ioo hI hc a ha hs).comp
    (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => ⟨hq.2,hq.1⟩)

theorem layerAreaIntegral_hasDerivAt {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a s T : ℝ} (ha : a∈I) (hs : s∈I) (hT : T∈Ioo (0:ℝ) 1) {ℓ : Plane → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1)) :
    HasDerivAt (fun r => layerAreaIntegral ℓ a (r,T)) (ℓ (s,T)) s := by
  have hcs : ContinuousOn (fun r => ℓ (r,T)) I :=
    hℓ.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr,hT⟩)
  have hseg : uIcc a s ⊆ I := by simpa only [segment_eq_uIcc] using hc.segment_subset ha hs
  exact intervalIntegral.integral_hasDerivAt_right
    (hcs.mono hseg).intervalIntegrable (hcs.stronglyMeasurableAtFilter hI s hs)
    (hcs.continuousAt (hI.mem_nhds hs))

theorem layerAreaIntegral_pos {I : Set ℝ} (hc : Convex ℝ I)
    {a b T : ℝ} (ha : a∈I) (hb : b∈I) (hab : a<b) (hT : T∈Ioo (0:ℝ) 1)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<ℓ q) :
    0<layerAreaIntegral ℓ a (b,T) := by
  have hseg : Icc a b ⊆ I := by
    simpa only [segment_eq_uIcc,uIcc_of_le hab.le] using hc.segment_subset ha hb
  apply intervalIntegral.integral_pos hab
    (hℓ.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hseg hr,hT⟩))
  · intro s hs
    exact (hpos (s,T) ⟨hseg ⟨hs.1.le,hs.2⟩,hT⟩).le
  · exact ⟨a,⟨le_rfl,hab.le⟩,hpos (a,T) ⟨ha,hT⟩⟩

variable {ι : Type*} [Fintype ι]

theorem areaLayerCoordinate_data {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a b : ℝ} (ha : a∈I) (hb : b∈I) (hab : a<b)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<ℓ q)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρpos : ∀ s,0≤deriv ρ s) (hρa : ρ a=0) (hρb : ρ b=1)
    {H : (ι → ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    {V : Set (ι → ℝ)} (hHp : ∀ p∈V,0≤H p) :
    ContDiffOn ℝ ∞ (areaLayerCoordinate ℓ a ρ H)
      ((Icc a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
    (∀ T∈Ioo (0:ℝ) 1,∀ v,planeMoments v∈V→∀ s∈Ioo a b,
      0<deriv (fun r => areaLayerCoordinate ℓ a ρ H ((r,T),v)) s) ∧
    (∀ T∈Ioo (0:ℝ) 1,∀ v,planeMoments v∈V→areaLayerCoordinate ℓ a ρ H ((a,T),v)=0) ∧
    (∀ T∈Ioo (0:ℝ) 1,∀ v,planeMoments v∈V→H (planeMoments v)<areaLayerCoordinate ℓ a ρ H ((b,T),v)) := by
  have hseg : Icc a b⊆I := by
    simpa only [segment_eq_uIcc,uIcc_of_le hab.le] using hc.segment_subset ha hb
  refine ⟨?_,?_,?_,?_⟩
  · exact ((layerAreaIntegral_smooth hI hc ha hℓ).comp contDiff_fst.contDiffOn
      (fun _ hp => ⟨hseg hp.1.1,hp.1.2⟩)).add
      (((hρ.comp (contDiff_fst.comp contDiff_fst)).mul
        (hH.comp (planeMoments_smooth.comp contDiff_snd))).contDiffOn)
  · intro T hT v hv s hs
    have hd := (layerAreaIntegral_hasDerivAt hI hc ha (hseg ⟨hs.1.le,hs.2.le⟩) hT hℓ).add
      (((hρ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) s).hasDerivAt).mul_const (H (planeMoments v)))
    change HasDerivAt (fun r => areaLayerCoordinate ℓ a ρ H ((r,T),v)) _ s at hd
    rw [hd.deriv]
    exact add_pos_of_pos_of_nonneg (hpos (s,T) ⟨hseg ⟨hs.1.le,hs.2.le⟩,hT⟩)
      (mul_nonneg (hρpos s) (hHp _ hv))
  · intro T _ v _
    simp only [areaLayerCoordinate,layerAreaIntegral,intervalIntegral.integral_same,hρa,zero_mul,add_zero]
  · intro T hT v _
    simp only [areaLayerCoordinate,hρb,one_mul]
    exact lt_add_of_pos_left _ (layerAreaIntegral_pos hc ha hb hab hT hℓ hpos)


end

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem horizontalOneForm_fderiv {A B : Plane × E → ℝ} {x : Plane × E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v w : Plane × E) :
    fderiv ℝ (horizontalOneForm A B) x v w =
      fderiv ℝ A x v*w.1.1+fderiv ℝ B x v*w.1.2 := by
  rw [←fderiv_clm_eval ((hA.smul_const _).add (hB.smul_const _))]
  simp only [horizontalOneForm_apply]
  change fderiv ℝ ((fun y => A y*w.1.1)+(fun y => B y*w.1.2)) x v = _
  rw [fderiv_add (hA.mul_const _) (hB.mul_const _),fderiv_mul_const hA,fderiv_mul_const hB]
  simp only [add_apply,smul_apply,smul_eq_mul,mul_comm]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_BaseHorizontalForms
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_manifold _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_manifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

theorem circleBand_compact {a b : ℝ} :
    IsCompact (circleTurn '' Icc a b) := isCompact_Icc.image circleTurn_smooth.continuous

theorem intervalClock_monotone {a b : ℝ} (hab : a < b) : Monotone (intervalClock a b) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_nonneg.mpr hab.le))

theorem intervalClock_deriv_nonneg {a b : ℝ} (hab : a < b) (s : ℝ) :
    0 ≤ deriv (intervalClock a b) s := (intervalClock_monotone hab).deriv_nonneg

theorem intervalClock_zero {a b s : ℝ} (hab : a < b) (hs : s ≤ a) : intervalClock a b s=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_nonneg.mpr hab.le))

theorem intervalClock_one {a b s : ℝ} (hab : a < b) (hs : b ≤ s) : intervalClock a b s=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).2 (by linarith))

theorem intervalClock_bounds (a b s : ℝ) : 0 ≤ intervalClock a b s ∧ intervalClock a b s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem exists_ordered_smooth_clocks (N : ℕ) {a b : ℝ} (hab : a < b) :
    ∃ lo hi : Fin N → ℝ, ∃ ρ : Fin N → ℝ → ℝ,
      (∀ i, a < lo i ∧ lo i < hi i ∧ hi i < b) ∧
      (∀ i j, i < j → hi i < lo j) ∧
      (∀ i, ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s, 0 ≤ ρ i s ∧ ρ i s ≤ 1 ∧ 0 ≤ deriv (ρ i) s) ∧
      (∀ i, ∃ δ : ℝ, 0 < δ ∧
        (∀ s, s ≤ lo i+δ → ρ i s=0) ∧
        (∀ s, hi i-δ ≤ s → ρ i s=1)) := by
  let D : ℝ := (b-a)/(3*(N : ℝ)+1)
  have hden : 0 < 3*(N : ℝ)+1 := by positivity
  have hD : 0 < D := div_pos (sub_pos.mpr hab) hden
  have hDeq : D*(3*(N : ℝ)+1)=b-a := by dsimp [D]; field_simp
  let lo : Fin N → ℝ := fun i => a+D*(3*(i.val : ℝ)+1)
  let hi : Fin N → ℝ := fun i => a+D*(3*(i.val : ℝ)+2)
  let ρ : Fin N → ℝ → ℝ := fun i => intervalClock (lo i+D/4) (hi i-D/4)
  have hbetween (i : Fin N) : lo i+D/4 < hi i-D/4 := by dsimp [lo,hi] <;> nlinarith
  refine ⟨lo,hi,ρ,?_,?_,?_,?_,?_⟩
  · intro i
    have hiN : (i.val : ℝ)+1 ≤ N := by exact_mod_cast i.isLt
    have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    dsimp [lo,hi]
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith
  · intro i j hij
    have hv : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast hij
    dsimp [lo,hi]
    nlinarith
  · intro i
    exact ⟨intervalClock_smooth _ _,intervalClock_monotone (hbetween i)⟩
  · intro i s
    exact ⟨(intervalClock_bounds _ _ _).1,(intervalClock_bounds _ _ _).2,
      intervalClock_deriv_nonneg (hbetween i) s⟩
  · intro i
    exact ⟨D/4,by positivity,fun _ hs => intervalClock_zero (hbetween i) hs,
      fun _ hs => intervalClock_one (hbetween i) hs⟩

theorem intervalClock_deriv_smooth (a b : ℝ) : ContDiff ℝ ∞ (deriv (intervalClock a b)) :=
  (contDiff_infty_iff_deriv.mp (intervalClock_smooth a b)).2

theorem intervalClock_deriv_zero_left {a b s : ℝ} (hab : a<b) (hs : s<a) :
    deriv (intervalClock a b) s=0 := by
  have he : intervalClock a b =ᶠ[𝓝 s] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
    exact intervalClock_zero hab ht.le
  rw [he.deriv_eq,deriv_const]

theorem intervalClock_deriv_zero_right {a b s : ℝ} (hab : a<b) (hs : b < s) :
    deriv (intervalClock a b) s=0 := by
  have he : intervalClock a b =ᶠ[𝓝 s] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact intervalClock_one hab ht.le
  rw [he.deriv_eq,deriv_const]

theorem circleClockDensity_support {b : ℝ} (hb : 0<b) :
    support (circleClockDensity b) ⊆ circleTurn '' Icc (-b) b := by
  intro z hz
  refine ⟨shortCircleArgument z,?_,circleTurn_shortCircleArgument z⟩
  have hab : -b<b := by linarith
  constructor
  · by_contra hn
    exact hz (intervalClock_deriv_zero_left hab (lt_of_not_ge hn))
  · by_contra hn
    exact hz (intervalClock_deriv_zero_right hab (lt_of_not_ge hn))

theorem circleClockDensity_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (circleClockDensity b) := by
  intro z
  by_cases hz : z∈circleTurn '' Icc (-b) b
  · obtain ⟨s,hs,rfl⟩ := hz
    have hin : s∈Ioo (-(1/2):ℝ) (1/2) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    exact (intervalClock_deriv_smooth (-b) b).contMDiff.contMDiffAt.comp _
      (shortCircleArgument_smooth_at (circleTurn_short_slit hin))
  · apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [circleBand_compact.isClosed.isOpen_compl.mem_nhds hz] with w hw
    by_contra hs
    exact hw (circleClockDensity_support hb hs)

theorem circleClockDensity_turn {b s : ℝ} (hs : s∈Ioo (-(1/2):ℝ) (1/2)) :
    circleClockDensity b (circleTurn s)=deriv (intervalClock (-b) b) s := by
  unfold circleClockDensity
  rw [shortCircleArgument_turn hs]

 theorem expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (x⁻¹^2*expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x

 theorem smoothTransition_deriv_pos {x : ℝ} (hx : x∈Ioo (0:ℝ) 1) :
    0<deriv Real.smoothTransition x := by
  have hA := expNegInvGlue_hasDerivAt x
  have hB := (expNegInvGlue_hasDerivAt (1-x)).comp x ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
  have hd := hA.div (hA.add hB) (ne_of_gt (Real.smoothTransition.pos_denom x))
  change HasDerivAt Real.smoothTransition _ x at hd
  rw [hd.deriv]
  have h₁ := expNegInvGlue.pos_of_pos hx.1
  have h₂ := expNegInvGlue.pos_of_pos (sub_pos.mpr hx.2)
  apply div_pos _ (sq_pos_of_pos (Real.smoothTransition.pos_denom x))
  have h₃ : 0<x⁻¹^2 := sq_pos_of_pos (inv_pos.mpr hx.1)
  have h₄ : 0<(1-x)⁻¹^2 := sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr hx.2))
  have he : x⁻¹^2*expNegInvGlue x*(expNegInvGlue x+expNegInvGlue (1-x))-
      expNegInvGlue x*(x⁻¹^2*expNegInvGlue x+((1-x)⁻¹^2*expNegInvGlue (1-x))*(0-1))=
      expNegInvGlue x*expNegInvGlue (1-x)*(x⁻¹^2+(1-x)⁻¹^2) := by ring
  dsimp only [Pi.add_apply,Function.comp_apply]
  rw [he]
  positivity

 theorem intervalClock_deriv_pos {a b s : ℝ} (hab : a<b) (hs : s∈Ioo a b) :
    0<deriv (intervalClock a b) s := by
  have hx : (s-a)/(b-a)∈Ioo (0:ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hs.1) (sub_pos.mpr hab)
    · exact (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hs.2])
  have htr : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd := (htr.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((s-a)/(b-a))).hasDerivAt.comp s
    (((hasDerivAt_id s).sub_const a).div_const (b-a))
  change HasDerivAt (intervalClock a b) _ s at hd
  rw [hd.deriv]
  exact mul_pos (smoothTransition_deriv_pos hx) (div_pos zero_lt_one (sub_pos.mpr hab))

 theorem intervalClock_strictMonoOn {a b : ℝ} (hab : a<b) :
    StrictMonoOn (intervalClock a b) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (intervalClock_smooth a b).continuous.continuousOn
  simpa only [interior_Icc] using (fun s hs => intervalClock_deriv_pos hab (s := s) hs)

 theorem intervalClock_image {a b : ℝ} (hab : a<b) :
    intervalClock a b '' Ioo a b=Ioo (0:ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨s,hs,rfl⟩
    have hm := intervalClock_strictMonoOn hab
    constructor
    · simpa only [intervalClock_zero hab le_rfl] using hm ⟨le_rfl,hab.le⟩ ⟨hs.1.le,hs.2.le⟩ hs.1
    · simpa only [intervalClock_one hab le_rfl] using hm ⟨hs.1.le,hs.2.le⟩ ⟨hab.le,le_rfl⟩ hs.2
  · intro T hT
    apply intermediate_value_Ioo hab.le (intervalClock_smooth a b).continuous.continuousOn
    simpa only [intervalClock_zero hab le_rfl,intervalClock_one hab le_rfl] using hT

 theorem intervalClock_smooth_inverse {a b : ℝ} (hab : a<b) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1) ∧
      (∀ s∈Ioo a b,g (intervalClock a b s)=s) ∧
      (∀ T∈Ioo (0:ℝ) 1,g T∈Ioo a b ∧ intervalClock a b (g T)=T) := by
  have hm : InjOn (intervalClock a b) (Ioo a b) :=
    (intervalClock_strictMonoOn hab).injOn.mono Ioo_subset_Icc_self
  have hi (s : ℝ) (hs : s∈Ioo a b) : (fderiv ℝ (intervalClock a b) s).IsInvertible := by
    let c := deriv (intervalClock a b) s
    let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ c (ne_of_gt (intervalClock_deriv_pos hab hs))).toContinuousLinearEquiv
    refine ⟨e,?_⟩
    ext
    simp [e,c]
  obtain ⟨_,hsm,hl,hr⟩ := smooth_inverse_on isOpen_Ioo (intervalClock_smooth a b).contDiffOn hm hi
  rw [intervalClock_image hab] at hsm hr
  refine ⟨invFunOn (intervalClock a b) (Ioo a b),hsm,hl,?_⟩
  intro T hT
  exact ⟨invFunOn_mem (show T∈intervalClock a b '' Ioo a b from (intervalClock_image hab).symm ▸ hT),hr T hT⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_CylinderAnnularNormalization
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply
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

theorem positiveCircleClock_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (positiveCircleClock b) :=
  (circleClockDensity_smooth hb hsmall).comp (contMDiff_id.div contMDiff_const)

theorem positiveCircleClock_turn {b s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    positiveCircleClock b (circleTurn s)=deriv (intervalClock (-b) b) (s-1/2) := by
  unfold positiveCircleClock
  rw [←circleTurn_sub,circleClockDensity_turn (show s-1/2∈Ioo (-(1/2):ℝ) (1/2) by
    constructor <;> linarith [hs.1,hs.2])]


end

section
open scoped ContDiff Topology
open Set Function

theorem positiveCircleClock_inverse {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1) ∧
      (∀ T∈Ioo (0:ℝ) 1,g T∈Ioo (1/2-b) (1/2+b)) ∧
      (∀ t∈Ioo (1/2-b) (1/2+b),g (intervalClock (-b) b (t-1/2))=t) ∧
      (∀ T∈Ioo (0:ℝ) 1,intervalClock (-b) b (g T-1/2)=T) ∧
      (∀ T∈Ioo (0:ℝ) 1,0<deriv g T ∧
        positiveCircleClock b (circleTurn (g T))*deriv g T=1) := by
  have hab : -b<b := by linarith
  obtain ⟨g,hg,hl,hr⟩ := intervalClock_smooth_inverse hab
  let G : ℝ → ℝ := fun T => g T+1/2
  have hGs : ContDiffOn ℝ ∞ G (Ioo (0:ℝ) 1) := hg.add contDiffOn_const
  have hmem (T : ℝ) (hT : T∈Ioo (0:ℝ) 1) : G T∈Ioo (1/2-b) (1/2+b) := by
    have hh := (hr T hT).1
    dsimp [G]
    constructor <;> linarith [hh.1,hh.2]
  refine ⟨G,hGs,hmem,?_,?_,?_⟩
  · intro t ht
    dsimp [G]
    rw [hl _ (show t-1/2∈Ioo (-b) b from ⟨by linarith [ht.1],by linarith [ht.2]⟩)]
    ring
  · intro T hT
    simpa only [G,add_sub_cancel_right] using (hr T hT).2
  · intro T hT
    have hpos := intervalClock_deriv_pos hab (hr T hT).1
    have he : ∀ᶠ S in 𝓝 T,intervalClock (-b) b (g S)=S := by
      filter_upwards [isOpen_Ioo.mem_nhds hT] with S hS
      exact (hr S hS).2
    have hd := HasDerivAt.of_local_left_inverse
      (hg.contDiffAt (isOpen_Ioo.mem_nhds hT)).continuousAt
      ((intervalClock_smooth (-b) b).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (g T)).hasDerivAt
      (ne_of_gt hpos) he
    have hGd : HasDerivAt G (deriv (intervalClock (-b) b) (g T))⁻¹ T := hd.add_const (1/2)
    rw [hGd.deriv]
    refine ⟨inv_pos.mpr hpos,?_⟩
    rw [positiveCircleClock_turn (show G T∈Ioo (0:ℝ) 1 by
      have hm := hmem T hT
      constructor <;> linarith [hm.1,hm.2])]
    simp only [G,add_sub_cancel_right,mul_inv_cancel₀ (ne_of_gt hpos)]


end


open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem angularReparam_fderiv {g : ℝ → ℝ} {p : Plane × E}
    (hg : DifferentiableAt ℝ g p.1.2) (v : Plane × E) :
    fderiv ℝ (angularReparam g) p v=((v.1.1,deriv g p.1.2*v.1.2),v.2) := by
  have hd := (((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
    (hg.hasDerivAt.comp_hasFDerivAt p ((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (angularReparam g) _ p at hd
  rw [hd.fderiv]
  rfl

theorem baseCoefficient_fderiv_at {a : Plane → ℝ} {p : Plane × E}
    (ha : DifferentiableAt ℝ a p.1) (v : Plane × E) :
    fderiv ℝ (baseCoefficient a) p v=fderiv ℝ a p.1 v.1 := by
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v)
    ((ha.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).fderiv)

theorem firstBaseCoefficient_fderiv_at {a : ℝ × E → ℝ} {p : Plane × E}
    (ha : DifferentiableAt ℝ a (p.1.1,p.2)) (v : Plane × E) :
    fderiv ℝ (firstBaseCoefficient a) p v=fderiv ℝ a (p.1.1,p.2) (v.1.1,v.2) := by
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v)
    ((ha.hasFDerivAt.comp p (((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))).fderiv)

theorem weightedSecondCoefficient_fderiv_at {b w : Plane → ℝ} {G : ℝ × E → ℝ}
    {p : Plane × E} (hb : DifferentiableAt ℝ b p.1) (hw : DifferentiableAt ℝ w p.1)
    (hG : DifferentiableAt ℝ G (p.1.1,p.2)) (v : Plane × E) :
    fderiv ℝ (weightedSecondCoefficient b w G) p v =
      fderiv ℝ b p.1 v.1+fderiv ℝ w p.1 v.1*G (p.1.1,p.2)+
        w p.1*fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2) := by
  have hbD : DifferentiableAt ℝ (baseCoefficient b) p := hb.comp p differentiableAt_fst
  have hwD : DifferentiableAt ℝ (baseCoefficient w) p := hw.comp p differentiableAt_fst
  have hcoord : DifferentiableAt ℝ (fun q : Plane × E => (q.1.1,q.2)) p := by fun_prop
  have hgD : DifferentiableAt ℝ (firstBaseCoefficient G) p := hG.comp p hcoord
  change fderiv ℝ (baseCoefficient b+baseCoefficient w*firstBaseCoefficient G) p v = _
  rw [fderiv_add hbD (hwD.mul hgD),fderiv_mul hwD hgD]
  simp only [add_apply,smul_apply,smul_eq_mul,baseCoefficient_fderiv_at hb,
    baseCoefficient_fderiv_at hw,firstBaseCoefficient_fderiv_at hG,baseCoefficient,firstBaseCoefficient]
  ring

theorem plane_covector_decomp (L : Plane →L[ℝ] ℝ) (v : Plane) :
    L v=v.1*L (1,0)+v.2*L (0,1) := by
  have he : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul]

theorem angularReparam_weighted_pullback (Ω : E →L[ℝ] E →L[ℝ] ℝ)
    {A B : Plane → ℝ} {w g : ℝ → ℝ} {G : ℝ × E → ℝ} {p : Plane × E}
    (hA : DifferentiableAt ℝ A (p.1.1,g p.1.2))
    (hB : DifferentiableAt ℝ B (p.1.1,g p.1.2))
    (hw : DifferentiableAt ℝ w (g p.1.2)) (hg : DifferentiableAt ℝ g p.1.2)
    (hG : DifferentiableAt ℝ G (p.1.1,p.2)) (hnorm : w (g p.1.2)*deriv g p.1.2=1)
    (v z : Plane × E) :
    horizontalCoupling Ω (baseCoefficient A) (weightedSecondCoefficient B (fun q => w q.2) G)
      (angularReparam g p) (fderiv ℝ (angularReparam g) p v) (fderiv ℝ (angularReparam g) p z) =
      Ω v.2 z.2+normalizedAreaDensity A B g p.1*(v.1.1*z.1.2-v.1.2*z.1.1)+
        fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2)*z.1.2-
        v.1.2*fderiv ℝ G (p.1.1,p.2) (z.1.1,z.2) := by
  have hwp : DifferentiableAt ℝ (fun q : Plane => w q.2) (p.1.1,g p.1.2) := hw.comp (p.1.1,g p.1.2) differentiableAt_snd
  have hAp : DifferentiableAt ℝ (baseCoefficient A) (angularReparam g p) := hA.comp (angularReparam g p) differentiableAt_fst
  have hcoord : DifferentiableAt ℝ (fun q : Plane × E => (q.1.1,q.2)) (angularReparam g p) := by fun_prop
  have hBw : DifferentiableAt ℝ (baseCoefficient B) (angularReparam g p) :=
    hB.comp (angularReparam g p) differentiableAt_fst
  have hww : DifferentiableAt ℝ (baseCoefficient (fun q => w q.2)) (angularReparam g p) := by
    exact (hw.hasDerivAt.comp_hasFDerivAt (angularReparam g p)
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (p.1.1,g p.1.2))).comp (angularReparam g p)
        (hasFDerivAt_fst (𝕜 := ℝ) (p := angularReparam g p)))).differentiableAt
  have hGw : DifferentiableAt ℝ (firstBaseCoefficient G) (angularReparam g p) :=
    hG.comp (angularReparam g p) hcoord
  have hBp : DifferentiableAt ℝ (weightedSecondCoefficient B (fun q => w q.2) G) (angularReparam g p) :=
    hBw.add (hww.mul hGw)
  have hwd (u : Plane) : fderiv ℝ (fun q : Plane => w q.2) (p.1.1,g p.1.2) u=deriv w (g p.1.2)*u.2 := by
    have hd : HasFDerivAt (fun q : Plane => w q.2)
        (deriv w (g p.1.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) (p.1.1,g p.1.2) :=
      hw.hasDerivAt.comp_hasFDerivAt (p.1.1,g p.1.2) (hasFDerivAt_snd (𝕜 := ℝ) (p := (p.1.1,g p.1.2)))
    exact congrArg (fun L : Plane →L[ℝ] ℝ => L u) hd.fderiv
  rw [angularReparam_fderiv hg,angularReparam_fderiv hg]
  simp only [horizontalCoupling,add_apply,ContinuousLinearMap.bilinearComp_apply,
    euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    horizontalOneForm_fderiv hAp hBp]
  change Ω v.2 z.2 + _ = _
  rw [baseCoefficient_fderiv_at (p := angularReparam g p) hA,
    baseCoefficient_fderiv_at (p := angularReparam g p) hA,
    weightedSecondCoefficient_fderiv_at (p := angularReparam g p) hB hwp hG,
    weightedSecondCoefficient_fderiv_at (p := angularReparam g p) hB hwp hG]
  simp only [angularReparam,hwd,normalizedAreaDensity]
  rw [plane_covector_decomp (fderiv ℝ A (p.1.1,g p.1.2)) (v.1.1,deriv g p.1.2*v.1.2),
    plane_covector_decomp (fderiv ℝ A (p.1.1,g p.1.2)) (z.1.1,deriv g p.1.2*z.1.2),
    plane_covector_decomp (fderiv ℝ B (p.1.1,g p.1.2)) (v.1.1,deriv g p.1.2*v.1.2),
    plane_covector_decomp (fderiv ℝ B (p.1.1,g p.1.2)) (z.1.1,deriv g p.1.2*z.1.2)]
  linear_combination (fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2)*z.1.2-
    v.1.2*fderiv ℝ G (p.1.1,p.2) (z.1.1,z.2))*hnorm



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

open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem scalar_area_slice {L : Plane → ℝ} {q : Plane} {c : ℝ}
    (hL : DifferentiableAt ℝ L q) (hc : HasDerivAt (fun s => L (s,q.2)) c q.1) :
    fderiv ℝ L q (1,0)=c := by
  have hline := (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hL.hasFDerivAt.comp_hasDerivAt q.1 hline).unique hc

omit [DecidableEq ι] in
theorem areaLayerForm_apply {I : Set ℝ} (hI : IsOpen I) (hconv : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {ℓ : Plane → ℝ}
    (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    {F H : (ι → ℝ) → ℝ} {ρ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (hρ : ContDiff ℝ ∞ ρ)
    {p : Plane × PlanePhase ι} (hp : p.1∈I ×ˢ Ioo (0:ℝ) 1) (v w : Plane × PlanePhase ι) :
    layerForm F (areaLayerCoordinate ℓ a ρ H) p v w=phaseArea v.2 w.2+
      ℓ p.1*(v.1.1*w.1.2-v.1.2*w.1.1)+
      fderiv ℝ (layerHamiltonian F H ρ) (p.1.1,p.2) (v.1.1,v.2)*w.1.2-
      v.1.2*fderiv ℝ (layerHamiltonian F H ρ) (p.1.1,p.2) (w.1.1,w.2) := by
  let L := layerAreaIntegral ℓ a
  let K : ℝ × PlanePhase ι → ℝ := fun q => ρ q.1*H (planeMoments q.2)
  have hL : DifferentiableAt ℝ L p.1 :=
    ((layerAreaIntegral_smooth hI hconv ha hℓ).contDiffAt ((hI.prod isOpen_Ioo).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hK : Differentiable ℝ K := ((hρ.comp contDiff_fst).mul
    (hH.comp (planeMoments_smooth.comp contDiff_snd))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hFs : Differentiable ℝ (toricFunction F) := (hF.comp planeMoments_smooth).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hpart : fderiv ℝ L p.1 (1,0)=ℓ p.1 :=
    scalar_area_slice hL (layerAreaIntegral_hasDerivAt hI hconv ha hp.1 hp.2 hℓ)
  have hfd (u : Plane × PlanePhase ι) : fderiv ℝ (areaLayerCoordinate ℓ a ρ H) p u=
      fderiv ℝ L p.1 u.1+fderiv ℝ K (p.1.1,p.2) (u.1.1,u.2) := by
    change fderiv ℝ (baseCoefficient L+firstBaseCoefficient K) p u=_
    have hLD : DifferentiableAt ℝ (baseCoefficient L) p := hL.comp p differentiableAt_fst
    have hKD : DifferentiableAt ℝ (firstBaseCoefficient K) p :=
      (hK _).comp p ((differentiableAt_fst.fst).prodMk differentiableAt_snd)
    rw [fderiv_add hLD hKD]
    simp only [add_apply,baseCoefficient_fderiv_at hL,firstBaseCoefficient_fderiv_at (hK _)]
  have hgd (u : ℝ × PlanePhase ι) : fderiv ℝ (layerHamiltonian F H ρ) (p.1.1,p.2) u=
      fderiv ℝ (toricFunction F) p.2 u.2+fderiv ℝ K (p.1.1,p.2) u := by
    change fderiv ℝ ((toricFunction F ∘ Prod.snd)+K) (p.1.1,p.2) u=_
    rw [fderiv_add ((hFs _).comp _ differentiableAt_snd) (hK _),
      fderiv_comp _ (hFs _) differentiableAt_snd]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_snd]
    rfl
  rw [layerForm_apply,hfd,hfd,hgd,hgd,plane_covector_decomp (fderiv ℝ L p.1) v.1,
    plane_covector_decomp (fderiv ℝ L p.1) w.1,hpart]
  ring


end

section

open scoped ContDiff Topology BigOperators
open Set Function

theorem areaHamiltonianForm_layer {m : ℕ} {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a b : ℝ} (ha : a∈I) (hb : b∈I) (hab : a<b)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    {F H : (Fin m → ℝ) → ℝ} {ρ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (hρ : ContDiff ℝ ∞ ρ)
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    {G : ℝ × PlanePhase (Fin m) → ℝ}
    (he : ∀ s∈Ioo a b,∀ v,planeMoments v∈V→G (s,v)=layerHamiltonian F H ρ (s,v))
    {p : Plane × PlanePhase (Fin m)}
    (hp : p∈(Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) :
    areaHamiltonianForm ℓ G p=layerForm F (areaLayerCoordinate ℓ a ρ H) p := by
  have hseg : Icc a b⊆I := by
    simpa only [segment_eq_uIcc,uIcc_of_le hab.le] using hc.segment_subset ha hb
  have hgerm : G =ᶠ[nhds (p.1.1,p.2)] layerHamiltonian F H ρ := by
    filter_upwards [(isOpen_Ioo.prod hV).mem_nhds ⟨hp.1.1,hp.2⟩] with q hq
    exact he q.1 hq.1 q.2 hq.2
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [areaHamiltonianForm_apply,areaLayerForm_apply hI hc ha hℓ hF hH hρ
    ⟨hseg ⟨hp.1.1.1.le,hp.1.1.2.le⟩,hp.1.2⟩,hgerm.fderiv_eq]

theorem finite_area_layer_packing {m : ℕ} {ι : Type*}
    {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {ℓ : Plane → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (I ×ˢ Ioo (0:ℝ) 1))
    (hpos : ∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<ℓ q)
    (F H : ι → (Fin m → ℝ) → ℝ) (ρ : ι → ℝ → ℝ)
    (hF : ∀ i,ContDiff ℝ ∞ (F i)) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    (hρ : ∀ i,ContDiff ℝ ∞ (ρ i)) (hρpos : ∀ i s,0≤deriv (ρ i) s)
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    (hHp : ∀ i p,p∈V→0≤H i p)
    (a b r r' : ι → ℝ) (ha : ∀ i,a i∈I) (hb : ∀ i,b i∈I) (hab : ∀ i,a i<b i)
    (hρa : ∀ i,ρ i (a i)=0) (hρb : ∀ i,ρ i (b i)=1)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j)→(∑ j,p j) ≤ r' i→p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p)
    (G : ℝ × PlanePhase (Fin m) → ℝ)
    (he : ∀ i,∀ s∈Ioo (a i) (b i),∀ v,planeMoments v∈V→
      G (s,v)=layerHamiltonian (F i) (H i) (ρ i) (s,v)) :
    ∃ (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m)),
      (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
      (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
      (∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v w,areaHamiltonianForm ℓ G (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z w)=standardForm v w) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
        (φ j '' closedBall (m+1) (r' j))) := by
  have hd i := areaLayerCoordinate_data hI hc (ha i) (hb i) (hab i) hℓ hpos
    (hρ i) (hρpos i) (hρa i) (hρb i) (hH i) (hHp i)
  exact finite_layer_packing_local F H (fun i => areaLayerCoordinate ℓ (a i) (ρ i) (H i))
    hF hV a b r r' hab (fun i => (hd i).1) hdis (fun i => (hd i).2.1)
    (fun i => (hd i).2.2.1) (fun i => (hd i).2.2.2) hr' hrr hsimplex hheight
    (areaHamiltonianForm ℓ G) (fun i _ hp => areaHamiltonianForm_layer hI hc (ha i) (hb i)
      (hab i) hℓ (hF i) (hH i) (hρ i) hV (he i) hp)


end

section
open scoped ContDiff Topology
open Set Function

theorem normalizedAreaDensity_smooth {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {A B : Plane → ℝ} (hA : ContDiffOn ℝ ∞ A (I ×ˢ J)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ J))
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1))
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) :
    ContDiffOn ℝ ∞ (normalizedAreaDensity A B g) (I ×ˢ Ioo (0:ℝ) 1) := by
  have hq : ContDiffOn ℝ ∞ (fun q : Plane => (q.1,g q.2)) (I ×ˢ Ioo (0:ℝ) 1) :=
    contDiffOn_fst.prodMk (hg.comp contDiffOn_snd (fun _ h => h.2))
  have hqm : MapsTo (fun q : Plane => (q.1,g q.2)) (I ×ˢ Ioo (0:ℝ) 1) (I ×ˢ J) :=
    fun _ h => ⟨h.1,hmap h.2⟩
  exact ((((hB.fderiv_of_isOpen (hI.prod hJ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp hq hqm).clm_apply contDiffOn_const).sub
    (((hA.fderiv_of_isOpen (hI.prod hJ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp hq hqm).clm_apply contDiffOn_const)).mul
    ((hg.deriv_of_isOpen isOpen_Ioo (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiffOn_snd (fun _ h => h.2))

theorem normalizedAreaDensity_pos {I J : Set ℝ} {A B : Plane → ℝ} {g : ℝ → ℝ}
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) (hg : ∀ T∈Ioo (0:ℝ) 1,0<deriv g T)
    (hbase : ∀ q∈I ×ˢ J,0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    {q : Plane} (hq : q∈I ×ˢ Ioo (0:ℝ) 1) : 0<normalizedAreaDensity A B g q :=
  mul_pos (hbase _ ⟨hq.1,hmap hq.2⟩) (hg _ hq.2)

theorem exists_normalized_positive_area {b : ℝ} (hb : 0<b) (hsmall : b<1/2)
    {I : Set ℝ} (hI : IsOpen I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ Ioo (1/2-b) (1/2+b)))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ Ioo (1/2-b) (1/2+b)))
    (hbase : ∀ q∈I ×ˢ Ioo (1/2-b) (1/2+b),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1)) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1) ∧
      MapsTo g (Ioo (0:ℝ) 1) (Ioo (1/2-b) (1/2+b)) ∧
      (∀ t∈Ioo (1/2-b) (1/2+b),g (intervalClock (-b) b (t-1/2))=t) ∧
      (∀ T∈Ioo (0:ℝ) 1,intervalClock (-b) b (g T-1/2)=T) ∧
      (∀ T∈Ioo (0:ℝ) 1,positiveCircleClock b (circleTurn (g T))*deriv g T=1) ∧
      ContDiffOn ℝ ∞ (normalizedAreaDensity A B g) (I ×ˢ Ioo (0:ℝ) 1) ∧
      (∀ q∈I ×ˢ Ioo (0:ℝ) 1,0<normalizedAreaDensity A B g q) := by
  obtain ⟨g,hg,hm,hl,hr,hd⟩ := positiveCircleClock_inverse hb hsmall
  refine ⟨g,hg,fun _ h => hm _ h,hl,hr,fun T hT => (hd T hT).2,
    normalizedAreaDensity_smooth hI isOpen_Ioo hA hB hg (fun _ h => hm _ h),?_⟩
  intro q hq
  exact normalizedAreaDensity_pos (fun _ h => hm _ h) (fun T hT => (hd T hT).1) hbase hq


end

section

open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem angularReparam_smoothOn {g : ℝ → ℝ} {J : Set ℝ} (hg : ContDiffOn ℝ ∞ g J)
    {U : Set (Plane × E)} (hU : ∀ p∈U,p.1.2∈J) : ContDiffOn ℝ ∞ (angularReparam g) U :=
  ((contDiff_fst.comp contDiff_fst).contDiffOn.prodMk
    (hg.comp (contDiff_snd.comp contDiff_fst).contDiffOn hU)).prodMk contDiff_snd.contDiffOn

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem angularReparam_injOn {g C : ℝ → ℝ} {J : Set ℝ}
    (hinv : ∀ T∈J,C (g T)=T) {U : Set (Plane × E)} (hU : ∀ p∈U,p.1.2∈J) :
    InjOn (angularReparam g) U := by
  intro p hp q hq he
  have hh := congrArg (angularReparam (E := E) C) he
  change ((p.1.1,C (g p.1.2)),p.2)=((q.1.1,C (g q.1.2)),q.2) at hh
  simpa only [hinv _ (hU _ hp),hinv _ (hU _ hq)] using hh


end

section

open scoped ContDiff Topology BigOperators
open Set Function

theorem angular_packing_transport {m : ℕ} {ι : Type*} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ J)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ J))
    {w g C : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hg : ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1))
    (hmap : MapsTo g (Ioo (0:ℝ) 1) J) (hC : Continuous C)
    (hinv : ∀ T∈Ioo (0:ℝ) 1,C (g T)=T)
    (hnorm : ∀ T∈Ioo (0:ℝ) 1,w (g T)*deriv g T=1)
    {G : ℝ × PlanePhase (Fin m) → ℝ} (hG : ContDiff ℝ ∞ G)
    (a b r : ι → ℝ) (ha : ∀ i,Ioo (a i) (b i)⊆I) {V : Set (Fin m → ℝ)}
    (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m))
    (hU : ∀ i,IsOpen (U i)) (hBU : ∀ i,closedBall (m+1) (r i)⊆U i)
    (hφ : ∀ i,ContDiffOn ℝ ∞ (φ i) (U i))
    (hemb : ∀ i,Topology.IsEmbedding (fun z : U i => φ i z))
    (him : ∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V))
    (hform : ∀ i,∀ z∈U i,∀ v u,
      areaHamiltonianForm (normalizedAreaDensity A B g) G (φ i z)
        (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u)
    (hdis : Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r i))
      (φ j '' closedBall (m+1) (r j)))) :
    ∃ ψ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m),
      (∀ i,ContDiffOn ℝ ∞ (ψ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => ψ i z)) ∧
      (∀ i,∀ z∈U i,ψ i z∈(Ioo (a i) (b i) ×ˢ J) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v u,
        horizontalCoupling phaseArea (baseCoefficient A) (weightedSecondCoefficient B (fun q => w q.2) G)
          (ψ i z) (fderiv ℝ (ψ i) z v) (fderiv ℝ (ψ i) z u)=standardForm v u) ∧
      Pairwise (fun i j => Disjoint (ψ i '' closedBall (m+1) (r i))
        (ψ j '' closedBall (m+1) (r j))) := by
  let S : Set (Plane × PlanePhase (Fin m)) := (I ×ˢ Ioo (0:ℝ) 1) ×ˢ (Set.univ : Set (PlanePhase (Fin m)))
  have hS : IsOpen S := (hI.prod isOpen_Ioo).prod isOpen_univ
  have hmS : ∀ i,MapsTo (φ i) (U i) S := fun i z hz =>
    ⟨⟨ha i (him i z hz).1.1,(him i z hz).1.2⟩,mem_univ _⟩
  have hgs : ContDiffOn ℝ ∞ (angularReparam g) S := angularReparam_smoothOn hg (fun _ h => h.1.2)
  let ψ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m) := fun i => angularReparam g ∘ φ i
  have hψ : ∀ i,ContDiffOn ℝ ∞ (ψ i) (U i) := fun i => hgs.comp (hφ i) (hmS i)
  have hCs : Continuous (angularReparam (E := PlanePhase (Fin m)) C) :=
    (continuous_fst.fst.prodMk (hC.comp continuous_fst.snd)).prodMk continuous_snd
  refine ⟨ψ,hψ,?_,?_,?_,?_⟩
  · intro i
    have he : angularReparam (E := PlanePhase (Fin m)) C ∘ (fun z : U i => ψ i z)=
        (fun z : U i => φ i z) := by
      funext z
      change (((φ i z).1.1,C (g (φ i z).1.2)),(φ i z).2)=φ i z
      rw [hinv _ (him i z z.property).1.2]
    apply Topology.IsEmbedding.of_comp (hψ i).continuousOn.domRestrict hCs
    change Topology.IsEmbedding (angularReparam C ∘ (fun z : U i => ψ i z))
    rw [he]
    exact hemb i
  · intro i z hz
    exact ⟨⟨(him i z hz).1.1,hmap (him i z hz).1.2⟩,(him i z hz).2⟩
  · intro i z hz v u
    have hp := hmS i hz
    have hq : ((φ i z).1.1,g (φ i z).1.2)∈I ×ˢ J := ⟨hp.1.1,hmap hp.1.2⟩
    have hgd := (hg.contDiffAt (isOpen_Ioo.mem_nhds hp.1.2)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hψd : fderiv ℝ (ψ i) z=
        (fderiv ℝ (angularReparam g) (φ i z)).comp (fderiv ℝ (φ i) z) :=
      fderiv_comp z ((hgs.contDiffAt (hS.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (((hφ i).contDiffAt ((hU i).mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    rw [hψd]
    simp only [ContinuousLinearMap.comp_apply]
    dsimp only [ψ,Function.comp_apply]
    rw [angularReparam_weighted_pullback phaseArea
      ((hA.contDiffAt ((hI.prod hJ).mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hB.contDiffAt ((hI.prod hJ).mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hw.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) hgd (hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hnorm _ hp.1.2)]
    simpa only [areaHamiltonianForm_apply] using hform i z hz v u
  · intro i j hij
    rw [show ψ i=angularReparam g ∘ φ i from rfl,show ψ j=angularReparam g ∘ φ j from rfl,
      Set.image_comp,Set.image_comp]
    apply (hdis hij).image (angularReparam_injOn hinv (fun _ hp => hp.1.2) (U := S))
    · rintro _ ⟨z,hz,rfl⟩
      exact hmS i (hBU i hz)
    · rintro _ ⟨z,hz,rfl⟩
      exact hmS j (hBU j hz)

theorem finite_weighted_layer_packing {m : ℕ} {ι : Type*}
    {δ : ℝ} (hδ : 0<δ) (hsmall : δ<1/2)
    {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hbase : ∀ q∈I ×ˢ Ioo (1/2-δ) (1/2+δ),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    (F H : ι → (Fin m → ℝ) → ℝ) (ρ : ι → ℝ → ℝ)
    (hF : ∀ i,ContDiff ℝ ∞ (F i)) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    (hρ : ∀ i,ContDiff ℝ ∞ (ρ i)) (hρpos : ∀ i s,0≤deriv (ρ i) s)
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V))
    (hHp : ∀ i p,p∈V→0≤H i p)
    (a b r r' : ι → ℝ) (ha : ∀ i,a i∈I) (hb : ∀ i,b i∈I) (hab : ∀ i,a i<b i)
    (hρa : ∀ i,ρ i (a i)=0) (hρb : ∀ i,ρ i (b i)=1)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p)
    (G : ℝ × PlanePhase (Fin m) → ℝ) (hG : ContDiff ℝ ∞ G)
    (he : ∀ i,∀ s∈Ioo (a i) (b i),∀ v,planeMoments v∈V →
      G (s,v)=layerHamiltonian (F i) (H i) (ρ i) (s,v)) :
    ∃ (U : ι → Set (Ambient (m+1))) (φ : ι → Ambient (m+1) → Plane × PlanePhase (Fin m)),
      (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
      (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
      (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
      (∀ i,∀ z∈U i,φ i z∈(Ioo (a i) (b i) ×ˢ Ioo (1/2-δ) (1/2+δ)) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ i,∀ z∈U i,∀ v u,
        horizontalCoupling phaseArea (baseCoefficient A)
          (weightedSecondCoefficient B (fun q => positiveCircleClock δ (circleTurn q.2)) G)
          (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
        (φ j '' closedBall (m+1) (r' j))) := by
  obtain ⟨g,hg,hm,_,hinv,hnorm,hℓ,hpos⟩ := exists_normalized_positive_area hδ hsmall hI hA hB hbase
  obtain ⟨U,φ,hU,hBU,hφ,hemb,him,hform,hdi⟩ := finite_area_layer_packing hI hc hℓ hpos F H ρ
    hF hH hρ hρpos hV hHp a b r r' ha hb hab hρa hρb hdis hr' hrr hsimplex hheight G he
  have hw : ContDiff ℝ ∞ (fun t => positiveCircleClock δ (circleTurn t)) :=
    ((positiveCircleClock_smooth hδ hsmall).comp circleTurn_smooth).contDiff
  have hC : Continuous (fun t => intervalClock (-δ) δ (t-1/2)) :=
    (intervalClock_smooth (-δ) δ).continuous.comp (continuous_id.sub continuous_const)
  have hasub : ∀ i,Ioo (a i) (b i)⊆I := by
    intro i
    have hseg : Icc (a i) (b i)⊆I := by
      simpa only [segment_eq_uIcc,uIcc_of_le (hab i).le] using hc.segment_subset (ha i) (hb i)
    exact Ioo_subset_Icc_self.trans hseg
  obtain ⟨ψ,hψ,heψ,hiψ,hfψ,hdψ⟩ := angular_packing_transport hI isOpen_Ioo hA hB hw hg hm hC
    hinv hnorm hG a b r' hasub U φ hU hBU hφ hemb him hform hdi
  exact ⟨U,ψ,hU,hBU,hψ,heψ,hiψ,hfψ,hdψ⟩


end

open scoped ContDiff
open Set Function

theorem surfaceFinalLayer_on_ordered_interval {N : ℕ} {E : Type*}
    (J R : E → ℝ) (h : Fin N → E → ℝ)
    {lo hi : Fin (N+1) → ℝ} {ρ : Fin (N+1) → ℝ → ℝ}
    (hord : ∀ i j, i < j → hi i < lo j)
    (hends : ∀ i, (∀ s, s ≤ lo i → ρ i s=0) ∧ (∀ s, hi i ≤ s → ρ i s=1))
    (i : Fin N) {s : ℝ} (hs : s ∈ Icc (lo i.castSucc) (hi i.castSucc)) (v : E) :
    surfaceFinalLayer J h R (fun j => ρ j.castSucc) (ρ (Fin.last N)) (s,v)=
      J v+(∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), h j v)+ρ i.castSucc s*h i v := by
  classical
  have hlast : ρ (Fin.last N) s=0 := (hends _).1 s (hs.2.trans (hord _ _ (by simp)).le)
  have he (j : Fin N) : ρ j.castSucc s*h j v =
      (if j < i then h j v else 0)+(if j=i then ρ i.castSucc s*h i v else 0) := by
    rcases lt_trichotomy j i with hj | hj | hj
    · have hr : ρ j.castSucc s=1 := (hends _).2 s ((hord _ _ (by simpa using hj)).le.trans hs.1)
      simp [hj,ne_of_lt hj,hr]
    · subst j
      simp
    · have hr : ρ j.castSucc s=0 := (hends _).1 s (hs.2.trans (hord _ _ (by simpa using hj)).le)
      simp [not_lt.mpr hj.le,ne_of_gt hj,hr]
  unfold surfaceFinalLayer
  rw [hlast,zero_mul,add_zero]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => he j)]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_filter]
  simp
  ring

theorem exists_surface_layer_clocks (N : ℕ) {a b : ℝ} (hab : a < b) :
    ∃ lo hi : Fin (N+1) → ℝ, ∃ ρ : Fin (N+1) → ℝ → ℝ,
      (∀ i, a<lo i ∧ lo i<hi i ∧ hi i<b) ∧
      (∀ i j, i < j → hi i < lo j) ∧
      (∀ i, ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s, 0 ≤ ρ i s ∧ ρ i s ≤ 1 ∧ 0 ≤ deriv (ρ i) s) ∧
      (∀ i, ∃ δ : ℝ, 0<δ ∧
        (∀ s, s ≤ lo i+δ → ρ i s=0) ∧ (∀ s, hi i-δ ≤ s → ρ i s=1)) ∧
      (∀ (E : Type) (J R : E → ℝ) (h : Fin N → E → ℝ) (i : Fin N) s,
        s ∈ Icc (lo i.castSucc) (hi i.castSucc) → ∀ v,
        surfaceFinalLayer J h R (fun j => ρ j.castSucc) (ρ (Fin.last N)) (s,v)=
          J v+(∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), h j v)+ρ i.castSucc s*h i v) := by
  obtain ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol⟩ := exists_ordered_smooth_clocks (N+1) hab
  refine ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol,?_⟩
  intro E J R h i s hs v
  apply surfaceFinalLayer_on_ordered_interval J R h hord _ i hs v
  intro j
  obtain ⟨δ,hδ,hz,ho⟩ := hcol j
  exact ⟨fun s hs => hz s (by linarith),fun s hs => ho s (by linarith)⟩



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ConstructedSurfaceLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Topology BigOperators
open Set Function

theorem exists_final_surface_layer_packing_bp240_oai {m N : ℕ}
    {δ α β : ℝ} (hδ : 0<δ) (hsmall : δ<1/2) (hαβ : α<β)
    {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hbase : ∀ q∈Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    (J : (Fin m → ℝ) → ℝ) (R : PlanePhase (Fin m) → ℝ) (H : Fin N → (Fin m → ℝ) → ℝ)
    (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) (hHp : ∀ i p,p∈V → 0≤H i p)
    (r r' : Fin N → ℝ) (hr' : ∀ i,0 ≤ r' i) (hrr : ∀ i,r' i < r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j) ≤ r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p) :
    ∃ lo hi : Fin (N+1) → ℝ, ∃ ρ : Fin (N+1) → ℝ → ℝ,
      (∀ i,α<lo i ∧ lo i<hi i ∧ hi i<β) ∧
      (∀ i j,i<j → hi i<lo j) ∧
      (∀ i,ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s,0≤ρ i s ∧ ρ i s≤1 ∧ 0≤deriv (ρ i) s) ∧
      (∀ i, ∃ ε : ℝ, 0 < ε ∧ (∀ s, s ≤ lo i + ε → ρ i s = 0) ∧ (∀ s, hi i - ε ≤ s → ρ i s = 1)) ∧
      ∃ (U : Fin N → Set (Ambient (m+1))) (φ : Fin N → Ambient (m+1) → Plane × PlanePhase (Fin m)),
        (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
        (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
        (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
        (∀ i,∀ z∈U i,φ i z∈(Ioo (lo i.castSucc) (hi i.castSucc) ×ˢ Ioo (1/2-δ) (1/2+δ)) ×ˢ
          (planeMoments ⁻¹' V)) ∧
        (∀ i,∀ z∈U i,∀ v u,
          horizontalCoupling phaseArea (baseCoefficient A)
            (weightedSecondCoefficient B (fun q => positiveCircleClock δ (circleTurn q.2))
              (surfaceFinalLayer (J ∘ planeMoments) (fun j => H j ∘ planeMoments) R
                (fun j => ρ j.castSucc) (ρ (Fin.last N))))
            (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
          (φ j '' closedBall (m+1) (r' j))) := by
  classical
  obtain ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol,hiso⟩ := exists_surface_layer_clocks N hαβ
  let F : Fin N → (Fin m → ℝ) → ℝ := fun i p => J p+∑ j ∈ Finset.univ.filter (fun j => j < i),H j p
  have hF : ∀ i,ContDiff ℝ ∞ (F i) := by
    intro i
    exact hJ.add (ContDiff.sum (fun j _ => hH j))
  have he0 : ∀ i,ρ i (lo i)=0 := by
    intro i
    obtain ⟨ε,hε,hlo,_⟩ := hcol i
    exact hlo _ (by linarith)
  have he1 : ∀ i,ρ i (hi i)=1 := by
    intro i
    obtain ⟨ε,hε,_,hhi⟩ := hcol i
    exact hhi _ (by linarith)
  have hdis : Pairwise (fun i j : Fin N => Disjoint (Ioo (lo i.castSucc) (hi i.castSucc))
      (Ioo (lo j.castSucc) (hi j.castSucc))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · apply Set.disjoint_left.mpr
      intro s hs ht
      have hh := hord i.castSucc j.castSucc (by simpa using hij)
      linarith [hs.2,ht.1]
    · apply Set.disjoint_left.mpr
      intro s hs ht
      have hh := hord j.castSucc i.castSucc (by simpa using hij)
      linarith [ht.2,hs.1]
  let G := surfaceFinalLayer (J ∘ planeMoments) (fun j => H j ∘ planeMoments) R
    (fun j => ρ j.castSucc) (ρ (Fin.last N))
  have hG : ContDiff ℝ ∞ G := surfaceFinalLayer_smooth (hJ.comp planeMoments_smooth) hR
    (fun j => (hH j).comp planeMoments_smooth) (fun j => (hsm j.castSucc).1) (hsm _).1
  have he : ∀ i : Fin N,∀ s∈Ioo (lo i.castSucc) (hi i.castSucc),∀ v,planeMoments v∈V →
      G (s,v)=layerHamiltonian (F i) (H i) (ρ i.castSucc) (s,v) := by
    intro i s hs v _
    exact hiso _ (J ∘ planeMoments) R (fun j => H j ∘ planeMoments) i s ⟨hs.1.le,hs.2.le⟩ v
  have hlo : ∀ i : Fin N,lo i.castSucc∈Ioo α β := fun i =>
    ⟨(hbd _).1,lt_trans (hbd _).2.1 (hbd _).2.2⟩
  have hhi : ∀ i : Fin N,hi i.castSucc∈Ioo α β := fun i =>
    ⟨lt_trans (hbd _).1 (hbd _).2.1,(hbd _).2.2⟩
  obtain ⟨U,φ,hU,hBU,hφ,hemb,him,hform,hd⟩ := finite_weighted_layer_packing hδ hsmall
    isOpen_Ioo (convex_Ioo _ _) hA hB hbase F H (fun i => ρ i.castSucc) hF hH
    (fun i => (hsm _).1) (fun i s => (hpos _ s).2.2) hV hHp
    (fun i => lo i.castSucc) (fun i => hi i.castSucc) r r' hlo hhi (fun i => (hbd _).2.1)
    (fun i => he0 i.castSucc) (fun i => he1 i.castSucc) hdis hr' hrr hsimplex hheight G hG he
  exact ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol,U,φ,hU,hBU,hφ,hemb,him,hform,hd⟩


end

open scoped ContDiff
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_final_surface_layer_packing_bp240_oai
