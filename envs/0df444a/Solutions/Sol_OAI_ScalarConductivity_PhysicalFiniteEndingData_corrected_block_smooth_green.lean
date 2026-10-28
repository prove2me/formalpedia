-- Prove2me | solution 1 for OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:20:59.586735+00:00
-- url     : https://prove2.me/submissions/3f3e5d3c-8fdd-4933-945c-058d9396393a

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C008
import Theorems.Thm_OAI_ScalarConductivity_attachedPeriodicFlux_smooth_green
import Theorems.Thm_OAI_ScalarConductivity_fullAttachedEnd_smooth_green_neg
import Theorems.Thm_OAI_ScalarConductivity_fullAttachedEnd_smooth_green_pos
import Theorems.Thm_OAI_ScalarConductivity_splicedAttached_energy_ae

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma local_iteratedFDeriv_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i)
    (n : ℕ) {x : E} (hx : x∈s) :
    iteratedFDeriv ℝ n (fun x => ∑' i, f i x) x = ∑' i, iteratedFDeriv ℝ n (f i) x := by
  have ht := (local_smooth_taylor hs hsc hf v hv hbound).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)) (hs.uniqueDiffOn) hx
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at ht
  exact ht.symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierSmooth
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma flatFourier_iterated {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h, |a h|≤B)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    iteratedFDeriv ℝ n (flatFourier s a phase) x =
      ∑' h, iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x := by
  apply local_iteratedFDeriv_tsum (axial_halfspace_open (x 0/2)) (axial_halfspace_connected (x 0/2))
    (fun h => contDiff_const.mul (flatPhaseMode_smooth s h (phase h)))
    (fun n h => B*((torusRate s h+torusSize h)^n*exp (-(x 0/2)*torusRate s h)))
  · intro n
    exact (flatMode_derivative_summable hs n (by linarith)).mul_left B
  · intro n h y hy
    exact weighted_phase_halfspace_bound ha n h hy.le
  · change x 0/2<x 0
    linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CylinderSlopeGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma complex_linear_axis_deriv (r : ℝ) :
    deriv (fun t : ℝ => (r:ℂ)*(t:ℂ))=(fun _ => (r:ℂ)) := by
  funext t
  exact ((hasDerivAt_id t).ofReal_comp.const_mul (r:ℂ)).deriv.trans (by simp)

lemma cylinderSlopeJet_derivative (r R : ℝ) :
    cylinderSlopeJet r R 1=cylinderMode (FiniteAxisMeasure R) 0
      (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R) := by
  change cylinderMode _ _ (smoothFiniteAxisLp (q:=deriv (fun t : ℝ => (r:ℂ)*(t:ℂ))) _ _) = _
  congr 1
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae ((complex_linear_axis_smooth r).continuous_deriv (by simp)) R,
    smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R] with t ht hu
  rw [ht,hu,complex_linear_axis_deriv]

lemma cylinderSlopeJet_angular (r R : ℝ) : cylinderSlopeJet r R 2=0 ∧ cylinderSlopeJet r R 3=0 := by
  simp [cylinderSlopeJet,smoothCylinderModeJet]

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndPoissonDifferential
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma endFlatPoisson_real_derivative_axis (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) (j : Fin 3) :
    fderiv ℝ (fun y => (endFlatPoisson s f y).re) x (Pi.single j 1)=
      (endPoissonField s f j.succ (x 0,torusAngles x)).re := by
  have he := endFlatPoisson_hasFDeriv s hs f hx
  have hr := (Complex.reCLM.hasFDerivAt.comp x he).fderiv
  calc
    _ = ((∑' h,endFlatMode s h (f.val 0 h) x • endFrequency s h) (Pi.single j 1)).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hr
    _ = (fderiv ℝ (endFlatPoisson s f) x (Pi.single j 1)).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℂ => (L (Pi.single j 1)).re) he.fderiv.symm
    _ = _ := congrArg Complex.re (endFlatPoisson_derivative_axis s hs f hx j)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralLocalAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

lemma centralFullJetCLM_smooth_ae (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      centralFullJetCLM s (centralEmbedL s f) x=
        piSmoothJet (fun y => f (sourcePairCoordinates y)) (WithLp.ofLp x) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralPhysicalWholeCLM_smooth_ae f i))
  filter_upwards [physicalFourJetCLM_ae (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)),
    ae_all_iff.mpr hi] with x hx hi
  intro hy
  simp only [Function.comp_apply] at hi
  change physicalFourJetCLM (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)) x=_
  rw [hx]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [indicator_of_mem hy,piSmoothJet,PiLp.toLp_apply,Fin.cases_zero,
      centralJetField,Matrix.cons_val_zero] using hi 0
  · change centralPhysicalWholeCLM (centralSmoothJet f j.succ) (WithLp.ofLp x)=_
    rw [hi j.succ,indicator_of_mem hy,central_parent_partial]
    rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedFlatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFlatTensor_energy_density (s : Fin 3 → ℝ) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v w : Fin 3 → ℝ) :
    |(sourceCollarJacobian i j x).det| *((attachedCartesianMatrix a i j x*ᵥv) ⬝ᵥ
      (attachedFlatTensor s a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥw)))=
        |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
          (v ⬝ᵥ (flatCylinderMatrix s*ᵥw)) := by
  rw [attachedFlatTensor_energy s ha i j hx,sourceFlatDensity,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx)]

lemma attachedCartesianMatrix_poisson_derivative (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b : ℝ) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) (sourceCollarPiece i j x) v=
      (attachedCartesianMatrix a i j x*ᵥ(fun k : Fin 3 =>
        (endPoissonField s f k.succ (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)) ⬝ᵥ v := by
  rw [attachedEndPoisson_real_fderiv s hs f a b i j hx ht]
  have hfield (k : Fin 3) : attachedEndPoissonField s f a b k.succ (sourceCollarPiece i j x)=
      endPoissonField s f k.succ (a*(x 0-b),torusAngles (sourceFaceAngles i j x)) := by
    obtain ⟨htx,hi,hj⟩ := mem_sourceExtendedBox.mp (sourceCollarOpenBox_subset hx)
    rw [←sourceFaceAngles_physical i j hi hj,attachedEndPoissonField_angular s f a b k.succ htx]
  simp_rw [hfield]
  rw [attachedCartesianMatrix,Matrix.mulVec_mulVec]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalTensorPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFaceTensorList_local (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧
      attachedFaceTensorList s a ks y=attachedPhysicalFlatTensor s a k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · refine ⟨k,List.mem_cons_self,hk,?_⟩
      simp only [attachedFaceTensorList,List.foldr_cons,ite_eq_left hk,attachedPatchTensor]
    · obtain ⟨l,hl,hy⟩ := hy
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,(List.mem_cons.mp hl).resolve_left
        (fun e => hk (e ▸ hy)),hy⟩
      refine ⟨l,List.mem_cons_of_mem k hl,hly,?_⟩
      simpa only [attachedFaceTensorList,List.foldr_cons,ite_eq_right hk] using he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma squareFace_interior_unique (i k : Fin 4) {a b : ℝ} (ha : |a|<1)
    (he : squareFace i a=squareFace k b) : i=k := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  fin_cases i <;> fin_cases k <;>
    simp [squareFace,squareFaceBase,squareFaceDirection] at h0 h1 ⊢ <;> linarith

lemma sourceCollarPiece_open_unique (i j k l : Fin 4) {x z : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox)
    (hz : z∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (he : sourceCollarPiece i j x=sourceCollarPiece k l z) : i=k ∧ j=l := by
  obtain ⟨hzt,hza,hzb⟩ := mem_sourceExtendedBox.mp hz
  have hx' := sourceCollarOpenBox_subset hx
  obtain ⟨hxt,hxa,hxb⟩ := mem_sourceExtendedBox.mp hx'
  have hxR : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j hxt hxb).1
  have hzR : 0 < sourceCollarRadius l (z 0) (z 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended l hzt hzb).1
  have hR : sourceCollarRadius j (x 0) (x 2)=sourceCollarRadius l (z 0) (z 2) := by
    have hh := congrArg sourceRadial he
    rwa [sourceCollarPiece_radial_pos i j hxR.le hxa,
      sourceCollarPiece_radial_pos k l hzR.le hza] at hh
  have ht : x 0=z 0 := by
    have hh := congrArg sourceCollarTime he
    rwa [sourceCollarPiece_time_pos i j hxR.le (by linarith [hxt.2]) hxa hxb,
      sourceCollarPiece_time_pos k l hzR.le (by linarith [hzt.2]) hza hzb] at hh
  constructor
  · apply squareFace_interior_unique i k hx.2.1
    have hh := congrArg (fun y : Fin 3 → ℝ => ![y 0/sourceLength,y 1]) he
    rw [sourceCollarPiece_angular,sourceCollarPiece_angular,←hR] at hh
    exact smul_right_injective (Fin 2 → ℝ) hxR.ne' hh
  · apply squareFace_interior_unique j l hx.2.2
    have hh := congrArg sourceCrossCoordinates he
    rw [sourceCollarPiece_cross_pos i j hxR.le hxa,
      sourceCollarPiece_cross_pos k l hzR.le hza,←ht] at hh
    exact smul_right_injective (Fin 2 → ℝ) (by linarith [hxt.2] : 1-x 0≠0) hh

lemma attachedFaceTensorList_unique (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    attachedFaceTensorList s a ks (sourceCollarPiece i j x)=
      attachedPhysicalFlatTensor s a i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := attachedFaceTensorList_local s a ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma attachedCollarTensor_open (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    attachedCollarTensor s a (sourceCollarPiece i j x)=
      attachedFlatTensor s a i j x := by
  rw [attachedCollarTensor,attachedFaceTensorList_unique s a _ i j hx (by simp)]
  simp only [attachedPhysicalFlatTensor,sourceCollarInverse_point i j hx]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma clm_eq_coordinate_dot (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    L v=(fun k => L (Pi.single k 1)) ⬝ᵥ v := by
  have hv : v=∑ k : Fin 3,v k • Pi.single k (1:ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul,smul_eq_mul,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma attachedFlatTestCovector_transport (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    attachedCartesianMatrix a i j x*ᵥattachedFlatTestCovector φ a i j x=
      physicalTestCovector φ (sourceCollarPiece i j x) := by
  rw [attachedFlatTestCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]

lemma physicalTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ)
    (i j : Fin 4) (x : Fin 3 → ℝ)
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      (sourceCollarJacobian i j x)ᵀ *ᵥ physicalTestCovector φ (sourceCollarPiece i j x) := by
  ext k
  rw [physicalTestCovector,(hφ.hasFDerivAt.comp x (sourceCollarPiece_hasFDeriv i j x)).fderiv]
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarDerivative i j x (Pi.single k 1))=_
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarJacobian i j x*ᵥPi.single k 1)=_
  rw [Matrix.mulVec_single_one,clm_eq_coordinate_dot]
  simp only [physicalTestCovector,Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  simp [Matrix.col,mul_comm]

theorem attachedFlatTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      sourceFaceAngleMatrix i j x*ᵥ(endAxialMatrix a*ᵥattachedFlatTestCovector φ a i j x) := by
  rw [physicalTestCovector_chain φ i j x hφ,
    ←attachedFlatTestCovector_transport φ ha i j hx,attachedCartesianMatrix,
    ←Matrix.mulVec_mulVec,sourceCartesianGradient_chain i j hx]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ParentFullEndH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma sourceCollarTime_local_inverse (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    sourceCollarTime=ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => sourceCollarInverse i j y 0) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),sourceCollarTime y=sourceCollarInverse i j y 0
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi,sourceCollarPiece_time_open hy]

lemma sourceCollarTime_differentiable_open (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) :
    DifferentiableAt ℝ sourceCollarTime (sourceCollarPiece i j x) := by
  have hd := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt.differentiableAt
  exact ((differentiableAt_pi.mp hd) 0).congr_of_eventuallyEq
    (sourceCollarTime_local_inverse i j hx)

lemma attachedCartesianMatrix_axial_derivative (a b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    physicalTestCovector (fun y => a*(sourceCollarTime y-b)) (sourceCollarPiece i j x)=
      attachedCartesianMatrix a i j x*ᵥPi.single 0 1 := by
  let F : (Fin 3 → ℝ) → ℝ := fun y => a*(sourceCollarTime y-b)
  have hd : DifferentiableAt ℝ F (sourceCollarPiece i j x) :=
    ((sourceCollarTime_differentiable_open i j hx).sub_const b).const_mul a
  have he : (F ∘ sourceCollarPiece i j)=ᶠ[𝓝 x] (fun y => a*(y 0-b)) := by
    filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx] with y hy
    simp only [Function.comp_apply,F,sourceCollarPiece_time_open hy]
  have hf : physicalTestCovector (F ∘ sourceCollarPiece i j) x=Pi.single 0 a := by
    ext k
    rw [physicalTestCovector,he.fderiv_eq,
      (((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).sub_const b).const_mul a).fderiv]
    fin_cases k <;> simp
  have hc := physicalTestCovector_chain F i j x hd
  have ht : (sourceCollarJacobian i j x)ᵀ *ᵥ
      (attachedCartesianMatrix a i j x*ᵥPi.single 0 1)=Pi.single 0 a := by
    rw [attachedCartesianMatrix,←Matrix.mulVec_mulVec,
      sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    ext k
    fin_cases k <;> simp [sourceFaceAngleMatrix,endAxialMatrix,Matrix.mulVec_diagonal]
  have hn : IsUnit (sourceCollarJacobian i j x)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j (sourceCollarOpenBox_subset hx))
  have hh := congrArg (fun v => (sourceCollarJacobian i j x)ᵀ⁻¹*ᵥv)
    (hc.symm.trans (hf.trans ht.symm))
  simpa only [Matrix.mulVec_mulVec,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hn,
    Matrix.one_mulVec,Matrix.one_mul] using hh

lemma fullAttachedEndGradient_transport (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (a b κ : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x)=
      attachedCartesianMatrix a i j x*ᵥ
        fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) := by
  have hp : physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)=attachedCartesianMatrix a i j x*ᵥ
        (fun k : Fin 3 => (endPoissonField s f k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re) := by
    ext k
    simp only [physicalTestCovector,attachedCartesianMatrix_poisson_derivative s hs f a b i j hx ht,
      dotProduct_single,mul_one]
  change physicalTestCovector (fun y => (attachedEndPoissonField s f a b 0 y).re)
      (sourceCollarPiece i j x)+κ •
        physicalTestCovector (fun y => a*(sourceCollarTime y-b)) (sourceCollarPiece i j x)=_
  rw [hp,attachedCartesianMatrix_axial_derivative a b i j hx,fullEndFlatCovector,
    Matrix.mulVec_add,Matrix.mulVec_smul]

theorem fullAttachedEnd_test_energy (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) (φ : (Fin 3 → ℝ) → ℝ)
    {a b : ℝ} (ha : a≠0) (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    |(sourceCollarJacobian i j x).det| *
      (fullAttachedEndGradient s f a b κ (sourceCollarPiece i j x) ⬝ᵥ
        (attachedCollarTensor s a (sourceCollarPiece i j x)*ᵥ
          physicalTestCovector φ (sourceCollarPiece i j x)))=
      |a| *angularArea*faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)*
        (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
          (flatCylinderMatrix s*ᵥattachedFlatTestCovector φ a i j x)) := by
  rw [fullAttachedEndGradient_transport s hs f a b κ i j hx ht,
    attachedCollarTensor_open s a i j hx,
    ←attachedFlatTestCovector_transport φ ha i j (sourceCollarOpenBox_subset hx)]
  exact attachedFlatTensor_energy_density s ha i j (sourceCollarOpenBox_subset hx) _ _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullEndClosedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceExtendedBox_interior_axial {l r : ℝ} {x : Fin 3 → ℝ}
    (hx : x∈interior (sourceExtendedBox l r)) : x 0∈Ioo l r := by
  have hbox : sourceExtendedBox l r=
      (univ : Set (Fin 3)).pi (fun k => Icc (![l,-1,-1] k) (![r,1,1] k)) := by
    ext x
    simp only [sourceExtendedBox,mem_Icc,Set.mem_pi,mem_univ,true_implies,Pi.le_def]
    simp only [forall_and]
  rw [hbox,interior_pi_set (finite_univ)] at hx
  have ht := hx 0 (mem_univ 0)
  simpa only [interior_Icc,Matrix.cons_val_zero] using ht

lemma sourceExtendedBox_axial_strict_ae (l r : ℝ) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x 0∈Ioo l r := by
  have hB : volume (frontier (sourceExtendedBox l r))=0 :=
    (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier (sourceExtendedBox l r) := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc)] with x hx hm
  apply sourceExtendedBox_interior_axial
  by_contra hi
  exact hx ⟨subset_closure hm,hi⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPeriodization
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma AngularPeriodic.fderiv {T : ℝ} {f : Coord3 → E} (hf : AngularPeriodic T f) :
    AngularPeriodic T (fderiv ℝ f) := by
  intro n x
  have he : (fun y => f (y+angularShift T n))=f := funext (hf n)
  rw [←fderiv_comp_add_right,he]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusBoxFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma coordinateDivergence_congr_nhds {F G : Coord3 → Coord3} {x : Coord3}
    (h : F=ᶠ[𝓝 x] G) : coordinateDivergence F x=coordinateDivergence G x := by
  unfold coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => F y i)=ᶠ[𝓝 x] (fun y => G y i) := h.mono (fun y hy => congrFun hy i)
  rw [he.fderiv_eq]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_FlatTorusPDE
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma expCosLinear_deriv (L K : E →L[ℝ] ℝ) (p : ℝ) (x : E) :
    HasFDerivAt (expCosLinear L K p)
      (expCosLinear L K p x • L + expCosLinear L K (p+Real.pi/2) x • K) x := by
  have hh := (L.hasFDerivAt (x := x)).exp.mul ((K.hasFDerivAt.add_const p).cos)
  convert hh using 1 <;> ext v <;>
    simp [smul_eq_mul,expCosLinear,Pi.mul_apply,←add_assoc,cos_add_pi_div_two]
  ring

lemma expCosLinear_fderiv (L K : E →L[ℝ] ℝ) (p : ℝ) (x v : E) :
    fderiv ℝ (expCosLinear L K p) x v =
      expCosLinear L K p x*L v+expCosLinear L K (p+Real.pi/2) x*K v := by
  rw [(expCosLinear_deriv L K p x).fderiv]
  rfl

lemma expCosLinear_hessian (L K : E →L[ℝ] ℝ) (p : ℝ) (x v w : E) :
    (iteratedFDeriv ℝ 2 (expCosLinear L K p) x) ![v,w] =
      (L v*L w-K v*K w)*expCosLinear L K p x+
      (L v*K w+K v*L w)*expCosLinear L K (p+Real.pi/2) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (expCosLinear L K p)) x := by
    have hc : ContDiff ℝ 2 (expCosLinear L K p) := by unfold expCosLinear; fun_prop
    exact (hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he := fderiv_clm_apply (c := fderiv ℝ (expCosLinear L K p)) hd
    (differentiableAt_const (c := w))
  have hfun : (fun y => fderiv ℝ (expCosLinear L K p) y w)=
      fun y => expCosLinear L K p y*L w+expCosLinear L K (p+Real.pi/2) y*K w := by
    funext y
    exact expCosLinear_fderiv L K p y w
  rw [hfun] at he
  have hh := ((expCosLinear_deriv L K p x).mul_const (L w)).add
    ((expCosLinear_deriv L K (p+Real.pi/2) x).mul_const (K w))
  have hhe := hh.fderiv
  change fderiv ℝ (fun y => expCosLinear L K p y*L w+
    expCosLinear L K (p+Real.pi/2) y*K w) x=_ at hhe
  rw [hhe] at he
  have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) he
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    smul_eq_mul] at hv
  rw [←hv]
  have hp : p+Real.pi/2+Real.pi/2=p+Real.pi := by ring
  simp only [expCosLinear,hp,←add_assoc,cos_add_pi]
  ring

lemma flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (flatPhaseMode s h p) x=0 := by
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ := -torusRate s h • ContinuousLinearMap.proj 0
  have hf : flatPhaseMode s h p=expCosLinear L (torusAngular h) p := rfl
  have hsq : torusRate s h^2=torusQuadratic s h := by
    apply sq_sqrt
    exact (by positivity : 0≤(1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2)).trans (hs _ _)
  rw [flatTensorLaplacian,hf]
  simp only [flatTensorLaplacianCLM,add_apply,
    smul_apply,ContinuousMultilinearMap.apply_apply,smul_eq_mul,
    expCosLinear_hessian]
  simp only [L,torusAngular,add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,flatAxis,Pi.single_apply,smul_eq_mul]
  simp only [show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,
    show (2:Fin 3)≠1 by decide,show (2:Fin 3)≠0 by decide,
    show (0:Fin 3)≠1 by decide,show (1:Fin 3)≠0 by decide,
    ite_true,ite_false,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero,
    zero_sub,neg_mul,neg_neg,mul_neg]
  dsimp [torusQuadratic] at hsq
  have hm := congrArg (fun r => r*expCosLinear L (torusAngular h) p x) hsq
  dsimp [L,torusAngular] at hm
  linear_combination hm

lemma weighted_flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p a : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (fun y => a*flatPhaseMode s h p y) x=0 := by
  change flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2 (a • flatPhaseMode s h p) x)=0
  rw [iteratedFDeriv_const_smul_apply
    (((contDiff_infty.mp (flatPhaseMode_smooth s h p)) 2).contDiffAt),map_smul]
  change a • flatTensorLaplacian s (flatPhaseMode s h p) x=0
  rw [flatPhaseMode_harmonic hs,smul_zero]

theorem flatFourier_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    flatTensorLaplacian s (flatFourier s a phase) x=0 := by
  have hb := (flatMode_derivative_summable hs 2 hx).mul_left B
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ 2
      (fun y => a h*flatPhaseMode s h (phase h) y) x‖) :=
    Summable.of_nonneg_of_le (fun h => norm_nonneg _)
      (fun h => weighted_phase_halfspace_bound ha 2 h le_rfl) hb
  rw [flatTensorLaplacian,flatFourier_iterated hs ha 2 hx,
    (flatTensorLaplacianCLM s).map_tsum hn.of_norm]
  have hz (h : Fin 2 → ℤ) : flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2
      (fun y => a h*flatPhaseMode s h (phase h) y) x)=0 :=
    weighted_flatPhaseMode_harmonic hs h (phase h) (a h) x
  simp only [hz,tsum_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FlatFourierFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatModeFlux_smoothOn {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {U : Set Coord3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatModeFlux s f) U := by
  have hd := hf.fderiv_of_isOpen hU (m:=↑(⊤:ℕ∞)) (by simp)
  have he (i : Fin 3) := hd.clm_apply (contDiffOn_const (c:=flatAxis i))
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact he 0
  · exact (contDiffOn_const.mul (he 1)).add (contDiffOn_const.mul (he 2))
  · exact (contDiffOn_const.mul (he 1)).add (contDiffOn_const.mul (he 2))

lemma flatModeFlux_divergence {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) :
    coordinateDivergence (flatModeFlux s f) x=flatTensorLaplacian s f x := by
  have hd := (hf.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))).differentiableAt (by simp)
  have he (i : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ f y (flatAxis i)) x=(fderiv ℝ (fderiv ℝ f) x).flip (flatAxis i) := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have he' (i : Fin 3) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (flatAxis i)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hsum := hf.isSymmSndFDerivAt (by simp)
  unfold coordinateDivergence
  rw [Fin.sum_univ_three]
  change fderiv ℝ (fun y => fderiv ℝ f y (flatAxis 0)) x (flatAxis 0)+
    fderiv ℝ (fun y => s 0*fderiv ℝ f y (flatAxis 1)+s 1*fderiv ℝ f y (flatAxis 2)) x (flatAxis 1)+
    fderiv ℝ (fun y => s 1*fderiv ℝ f y (flatAxis 1)+s 2*fderiv ℝ f y (flatAxis 2)) x (flatAxis 2)=_
  rw [fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _),
    fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _)]
  simp only [fderiv_const_mul (he' _),he,_root_.add_apply,
    _root_.smul_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hsum.eq (flatAxis 2) (flatAxis 1)]
  ring

lemma flatModeFlux_periodic {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {T : ℝ}
    (hf : AngularPeriodic T f) : AngularPeriodic T (flatModeFlux s f) := by
  intro n x
  unfold flatModeFlux
  rw [hf.fderiv n x]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusFluxDecay
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma coordinateDivergence_sub_at {F G : Coord3 → Coord3} {x : Coord3}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    coordinateDivergence (fun y => F y-G y) x=coordinateDivergence F x-coordinateDivergence G x := by
  unfold coordinateDivergence
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => F y i-G y i) x _=_
  rw [fderiv_fun_sub ((hasFDerivAt_pi'.mp hF.hasFDerivAt i).differentiableAt)
    ((hasFDerivAt_pi'.mp hG.hasFDerivAt i).differentiableAt)]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_WeakFluxClassicalC1
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_C1_continuous {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) : Continuous (coordinateDivergence F) := by
  apply continuous_finsetSum
  intro i _
  exact (((contDiff_pi.mp hF) i).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem coordinateDivergence_C1_weak {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F)
    (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hc : HasCompactSupport ψ) :
    (∫ x,fderiv ℝ ψ x (F x))= -(∫ x,ψ x*coordinateDivergence F x) := by
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    contDiff_pi.mp hF i
  have hdψ (i : Fin 3) : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdF (i : Fin 3) : Continuous (fun x => fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    ((hFi i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi₁ (i : Fin 3) : Integrable (fun x => F x i*fderiv ℝ ψ x (Pi.single i 1)) :=
    ((hFi i).continuous.mul (hdψ i)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ _).mul_left
  have hi₂ (i : Fin 3) : Integrable (fun x => ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) :=
    (hψ.continuous.mul (hdF i)).integrable_of_hasCompactSupport hc.mul_right
  have he (i : Fin 3) : (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1))=
      -(∫ x,ψ x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)) := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Coord3))
      (f := ψ) (g := fun x => F x i) (v := Pi.single i 1)
      (by simpa only [mul_comm] using hi₁ i) (hi₂ i)
      ((hψ.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => hψ.differentiable (by norm_num) x)
      (fun x _ => (hFi i).differentiable (by norm_num) x)
    have hh' : (∫ x,fderiv ℝ ψ x (Pi.single i 1)*F x i)=
        (∫ x,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
    rw [hh'] at hh
    linarith
  have hex : (fun x => fderiv ℝ ψ x (F x))=
      (fun x => ∑ i : Fin 3,F x i*fderiv ℝ ψ x (Pi.single i 1)) := by
    funext x
    exact coordinate_fderiv_expansion ψ x (F x)
  rw [hex]
  simp only [coordinateDivergence,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),integral_finsetSum _ (fun i _ => hi₂ i)]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib]

lemma C1_flux_divergence_zero {F : Coord3 → Coord3} {U : Set Coord3}
    (hF : ContDiff ℝ 1 F) (hU : IsOpen U)
    (hw : ∀ (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0) :
    ∀ x∈U,coordinateDivergence F x=0 := by
  have hd := coordinateDivergence_C1_continuous hF
  have hz : ∀ᵐ x : Coord3,x∈U → coordinateDivergence F x=0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hd.locallyIntegrable.locallyIntegrableOn U) (by
        intro ψ hψ hc hs
        have hh := coordinateDivergence_C1_weak hF ψ hψ hc
        have he := hw ⟨ψ,hψ⟩ hc hs
        change (∫ x,ψ x*coordinateDivergence F x)=0
        change (∫ x,fderiv ℝ ψ x (F x))=0 at he
        linarith)
  have he : coordinateDivergence F=ᵐ[volume.restrict U] (fun _ => (0:ℝ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hz
  exact Measure.eqOn_open_of_ae_eq he hU hd.continuousOn continuous_const.continuousOn

namespace WeakFiniteTensorPair

lemma flux_periodic {U : Set Coord3} (w : WeakFiniteTensorPair U) {T : ℝ}
    (hv : AngularPeriodic T w.v) (hE : AngularPeriodic T w.E) : AngularPeriodic T w.G := by
  intro n
  have hae : (fun x => w.G (x+angularShift T n))=ᵐ[volume] w.G := by
    filter_upwards [w.constitution,
      (measurePreserving_add_right volume (angularShift T n)).quasiMeasurePreserving.ae w.constitution]
      with x hx hxn
    rw [←hx,←hxn,hE n x,hv.fderiv n x]
  exact fun x => congrFun (Measure.eq_of_ae_eq hae
    (w.flux_C1.continuous.comp (continuous_id.add continuous_const)) w.flux_C1.continuous) x

lemma flux_divergence {U : Set Coord3} (w : WeakFiniteTensorPair U) (hU : IsOpen U)
    (j : Fin 2) : ∀ x∈U,coordinateDivergence (fun y => (w.G y).col j) x=0 := by
  apply C1_flux_divergence_zero _ hU (w.weak j)
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp w.flux_C1)

end WeakFiniteTensorPair
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AffineFourierField
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatTensorLaplacian_add {s : Fin 3→ℝ} {f g : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    flatTensorLaplacian s (fun y => f y+g y) x=
      flatTensorLaplacian s f x+flatTensorLaplacian s g x := by
  unfold flatTensorLaplacian
  rw [fun_iteratedFDeriv_add_apply hf hg,map_add]

lemma axial_affine_fderiv (α β : ℝ) (x : Coord3) :
    fderiv ℝ (fun y : Coord3 => α*y 0+β) x=α • ContinuousLinearMap.proj 0 := by
  have hh := (((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x:=x)).const_mul α).add_const β
  exact hh.fderiv

lemma flatTensorLaplacian_axial_affine (s : Fin 3→ℝ) (α β : ℝ) (x : Coord3) :
    flatTensorLaplacian s (fun y => α*y 0+β) x=0 := by
  have he : fderiv ℝ (fun y : Coord3 => α*y 0+β)=fun _ => α • ContinuousLinearMap.proj 0 :=
    funext (axial_affine_fderiv α β)
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,he,
    fderiv_fun_const,Pi.zero_apply,_root_.zero_apply,mul_zero,add_zero]

lemma affineFourierField_smooth {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (affineFourierField s a phase α β) {x | 0<x 0} :=
  (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => α*x 0+β) by fun_prop).contDiffOn.add
    (flatFourier_smooth hs ha)

lemma affineFourierField_harmonic {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ)
    {x : Coord3} (hx : 0<x 0) : flatTensorLaplacian s (affineFourierField s a phase α β) x=0 := by
  have hf := (flatFourier_smooth (phase:=phase) hs ha).contDiffAt ((axial_halfspace_open 0).mem_nhds hx)
  unfold affineFourierField
  rw [flatTensorLaplacian_add (by fun_prop)
    (hf.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))),
    flatTensorLaplacian_axial_affine,flatFourier_harmonic hs ha hx,add_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusLeadingRealMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Real Complex

lemma torusQuadratic_neg_mode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusQuadratic s (-h)=torusQuadratic s h := by
  simp only [torusQuadratic,Pi.neg_apply,Int.cast_neg]
  ring

lemma torusRate_neg_mode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusRate s (-h)=torusRate s h := by
  simp only [torusRate,torusQuadratic_neg_mode]

lemma torusAngular_neg_mode (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    torusAngular (-h) x= -torusAngular h x := by
  simp only [torusAngular,Pi.neg_apply,Int.cast_neg,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  ring

lemma polar_real_cosine (c : ℂ) (t : ℝ) :
    ‖c‖*Real.cos (t+c.arg)=c.re*Real.cos t-c.im*Real.sin t := by
  by_cases hc : c=0
  · simp [hc]
  · rw [Real.cos_add,Complex.cos_arg hc,Complex.sin_arg]
    field_simp

lemma realTorusCoeff_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    ‖realTorusCoeff f h‖≤‖f‖ := by
  unfold realTorusCoeff
  rw [norm_div]
  change ‖mFourierCoeff f h+star (mFourierCoeff f (-h))‖ / ‖(2:ℂ)‖ ≤ ‖f‖

  have hh := norm_add_le (mFourierCoeff f h) (star (mFourierCoeff f (-h)))
  have ha := torusFourierCoeff_bound f h
  have hb := torusFourierCoeff_bound f (-h)
  simp only [norm_star] at hh
  norm_num only [Complex.norm_ofNat] at *
  linarith

lemma realTorusCoeff_polar_mode (s : Fin 3 → ℝ) (f : TorusL2)
    (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f h‖*flatPhaseMode s h (realTorusCoeff f h).arg x=
      (((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*
        Complex.exp ((torusAngular h x:ℂ)*Complex.I)).re+
       ((Real.exp (-torusRate s (-h)*x 0):ℂ)*mFourierCoeff f (-h)*
        Complex.exp ((torusAngular (-h) x:ℂ)*Complex.I)).re)/2 := by
  rw [torusRate_neg_mode,torusAngular_neg_mode]
  rw [complex_mode_real,complex_mode_real]
  simp only [flatPhaseMode,Real.cos_add_pi_div_two,Real.cos_neg,Real.sin_neg]
  rw [←mul_assoc,mul_comm ‖realTorusCoeff f h‖,mul_assoc,polar_real_cosine]
  simp only [realTorusCoeff,Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.add_re,
    Complex.add_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma torusRealContinuation_polar {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=
      flatFourier s (fun h => ‖realTorusCoeff f h‖) (fun h => (realTorusCoeff f h).arg) x := by
  let F := fun h : Fin 2 → ℤ =>
    (((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h)*
      Complex.exp ((torusAngular h x:ℂ)*Complex.I)).re
  have hc := (ContinuousMap.evalCLM ℂ (torusAngles x)).hasSum
    (poisson_series_norm_summable hs hx f).of_norm.hasSum
  have hr := Complex.reCLM.hasSum hc
  change HasSum (fun h => ((Real.exp (-torusRate s h*x 0):ℂ)*mFourierCoeff f h*
    mFourier h (torusAngles x)).re) (torusRealContinuation s f x) at hr
  simp_rw [mFourier_torusAngles] at hr
  change HasSum F (torusRealContinuation s f x) at hr
  have hn : HasSum (fun h => F (-h)) (torusRealContinuation s f x) :=
    (Equiv.neg (Fin 2 → ℤ)).hasSum_iff.mpr hr
  have hh := (hr.add hn).div_const 2
  have he : (torusRealContinuation s f x+torusRealContinuation s f x)/2=
      torusRealContinuation s f x := by ring
  rw [he] at hh
  exact hh.tsum_eq.symm.trans (by
    unfold flatFourier
    apply tsum_congr
    intro h
    exact (realTorusCoeff_polar_mode s f h x).symm)

lemma realTorusCoeff_zero_re (f : TorusL2) :
    (realTorusCoeff f 0).re=(mFourierCoeff f 0).re := by
  simp only [realTorusCoeff,neg_zero,Complex.div_ofNat_re,Complex.add_re,
    Complex.star_def,Complex.conj_re]
  ring

lemma realTorusCoeff_polar_zero (s : Fin 3 → ℝ) (f : TorusL2) (x : Fin 3 → ℝ) :
    ‖realTorusCoeff f 0‖*flatPhaseMode s 0 (realTorusCoeff f 0).arg x=
      (mFourierCoeff f 0).re := by
  simp [flatPhaseMode,torusRate,torusQuadratic,torusAngular,realTorusCoeff_zero_re]

lemma realTorusAmplitude_bound (f : TorusL2) (h : Fin 2 → ℤ) :
    |realTorusAmplitude f h|≤‖f‖ := by
  unfold realTorusAmplitude
  split_ifs
  · simp
  · simpa only [abs_of_nonneg (norm_nonneg _)] using realTorusCoeff_bound f h

lemma torusRealContinuation_mean_free {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    torusRealContinuation s f x=(mFourierCoeff f 0).re+
      flatFourier s (realTorusAmplitude f) (realTorusPhase f) x := by
  classical
  rw [torusRealContinuation_polar hs f hx]
  have hb (h) : |‖realTorusCoeff f h‖|≤‖f‖ := by
    simpa only [abs_of_nonneg (norm_nonneg _)] using realTorusCoeff_bound f h
  rw [flatFourier,(flatFourier_summable hs hb hx).tsum_eq_add_tsum_ite 0,
    realTorusCoeff_polar_zero]
  congr 1
  unfold flatFourier
  apply tsum_congr
  intro h
  simp only [realTorusAmplitude,realTorusPhase]
  split_ifs <;> simp

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusDirectionalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma torusRealProjection_add (x y : TorusRealPlane) :
    torusRealProjection (x+y)=torusRealProjection x+torusRealProjection y := by
  ext j
  simp [torusRealProjection]

lemma torusRealProjection_direction (j : Fin 2) (t : ℝ) :
    torusRealProjection (t • Pi.single j (1:ℝ))=torusCoordinateShift j t := by
  ext i
  by_cases hij : i=j <;> simp [torusRealProjection,torusCoordinateShift,hij]

lemma torusDirectionalDerivative_eq (f : UnitAddTorus (Fin 2) → ℂ) (j : Fin 2)
    (θ : UnitAddTorus (Fin 2)) :
    torusDirectionalDerivative f j θ=deriv (fun t => f (θ+torusCoordinateShift j t)) 0 := by
  unfold torusDirectionalDerivative lineDeriv
  congr 2
  ext t
  change f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=_
  rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderProbabilityMeasure
lemma sourceAngularLpJet_ae {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (j : Fin 4) :
    sourceAngularLpJet hf a b R j =ᵐ[(FiniteAxisMeasure R).prod volume]
      sourceAngularJet f a b j :=
  (sourceAngularJet_memLp hf a b R j).coeFn_toLp

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma hasDerivAt_outer_of_strict_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {g : ℝ → ℝ} {x d : ℝ} {v : E}
    (hg : HasStrictDerivAt g d x) (hd : d≠0)
    (hF : HasDerivAt (F ∘ g) v x) : HasDerivAt F (d⁻¹ • v) (g x) := by
  let q := hg.localInverse g d x hd
  have hq : q (g x)=x := hg.eventually_left_inverse hd |>.self_of_nhds
  have h := hF.scomp_of_eq (g x) (hg.to_localInverse hd).hasDerivAt hq.symm
  apply h.congr_of_eventuallyEq
  filter_upwards [hg.eventually_right_inverse hd] with y hy
  exact congrArg F hy.symm

lemma hasStrictDerivAt_faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) :
    HasStrictDerivAt (faceRayAngle w j) (faceRayDensity w j b) b :=
  hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (Filter.Eventually.of_forall fun x => hasDerivAt_faceRayAngle w j x)
    (continuous_faceRayDensity w j).continuousAt

lemma faceRayDensity_pos' {w : ℝ} (hw : 0<w) (j : Fin 4) (b : ℝ) :
    0<faceRayDensity w j b := by
  fin_cases j <;> dsimp [faceRayDensity] <;> positivity

lemma torusDirectionalDerivative_of_face (F : UnitAddTorus (Fin 2) → ℂ)
    (θ : UnitAddTorus (Fin 2)) (k : Fin 2) {w : ℝ} (hw : 0<w)
    (i : Fin 4) (b : ℝ) (v : ℂ)
    (hF : HasDerivAt (fun u => F (θ+torusCoordinateShift k
      (faceRayAngle w i u-faceRayAngle w i b))) v b) :
    torusDirectionalDerivative F k θ=(faceRayDensity w i b)⁻¹ • v := by
  have h := hasDerivAt_outer_of_strict_comp (F:=fun t => F (θ+torusCoordinateShift k t))
    ((hasStrictDerivAt_faceRayAngle w i b).sub_const (faceRayAngle w i b))
    (faceRayDensity_pos' hw i b).ne' hF
  simpa only [sub_self,torusDirectionalDerivative_eq] using h.deriv

lemma hasDerivAt_coordinate_update (x : Fin 3 → ℝ) (k : Fin 3) :
    HasDerivAt (fun u => Function.update x k u) (Pi.single k 1) (x k) := by
  apply hasDerivAt_pi.mpr
  intro l
  by_cases hl : l=k
  · subst l
    simp only [Function.update_self,Pi.single_eq_same]
    exact hasDerivAt_id' (x k)
  · simpa [Function.update_of_ne hl,Pi.single_apply,hl] using hasDerivAt_const (x k) (x l)

lemma physicalTestCovector_update {f : (Fin 3 → ℝ) → ℝ} {point : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f point) (k : Fin 3) :
    HasDerivAt (fun u => f (Function.update point k u)) (physicalTestCovector f point k) (point k) := by
  simpa only [Function.update_eq_self,Function.comp_def,physicalTestCovector] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (point k) (hasDerivAt_coordinate_update point k)
      (Function.update_eq_self k point).symm

lemma sourceAngularTest_face0 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|≤1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity 1 i (x 1))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 1 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num) i (x 1)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 1).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 1), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h1
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 0 (faceRayAngle 1 i u-faceRayAngle 1 i (x 1))=
      ![((faceRayAngle 1 i u:ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ hu.le h2]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularTest_face1 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|<1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity sourceRadialWidth j (x 2))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 2 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 2).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 2), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h2
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 1 (faceRayAngle sourceRadialWidth j u-faceRayAngle sourceRadialWidth j (x 2))=
      ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j u:ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ h1 hu.le]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularAxial_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|≤1) :
    sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))=
      (a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0 : ℝ) := by
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 0).comp_of_eq t
      (((hasDerivAt_id t).const_mul a).add_const b) hx.symm
  have he : (fun u => f (sourceAngularCollar (a*u+b) (torusAngles (sourceFaceAngles i j x))))=
      (fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 (a*u+b))) := by
    funext u
    dsimp only [Function.comp_def]
    rw [sourceFaceAngles_torus,sourceAngular_face _ _ _ _ _ h1 h2]
    congr 2
    ext k
    fin_cases k <;> simp
  unfold sourceAngularAxial
  rw [he]
  change ((deriv ((fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 u)) ∘
    (fun u => a*u+b)) t : ℝ) : ℂ)=_
  have hd' := hd.deriv
  simpa only [id_eq,mul_one,mul_comm] using congrArg Complex.ofReal hd'

theorem sourceAngularJet_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|<1) :
    (fun k : Fin 3 => (sourceAngularJet f a b k.succ
      (t,torusAngles (sourceFaceAngles i j x))).re)=
      ![a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0,
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1)),
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))] := by
  ext k
  fin_cases k
  · change (sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))).re=_
    exact congrArg Complex.re (sourceAngularAxial_face hf a b t i j hx h1.le h2.le)
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))
    rw [sourceAngularTest_face0 hf a b t i j hx h1 h2.le]
    rw [Complex.real_smul]
    norm_cast
    ring
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))
    rw [sourceAngularTest_face1 hf a b t i j hx h1.le h2]
    rw [Complex.real_smul]
    norm_cast
    ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

lemma torusAngles_shift (n : Fin 2 → ℤ) (x : Coord3) :
    torusAngles (x+angularShift (2*Real.pi) n)=torusAngles x := by
  have hπ : 2*Real.pi≠0 := by positivity
  ext i
  fin_cases i <;> simp [torusAngles,angularShift,add_div,hπ,mul_div_cancel_left₀]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusAffineField
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusAffineField_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (torusAffineField s κ f) {x | 0<x 0} :=
  (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => κ*x 0) by fun_prop).contDiffOn.add
    (torusRealContinuation_smooth hs f)

lemma torusAffineField_periodic (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) :
    AngularPeriodic (2*Real.pi) (torusAffineField s κ f) := by
  intro n x
  simp only [torusAffineField,torusRealContinuation,torusAngles_shift]
  simp [angularShift]

lemma torusAffineField_polar_eventually {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusAffineField s κ f=ᶠ[𝓝 x]
      affineFourierField s (realTorusAmplitude f) (realTorusPhase f) κ (mFourierCoeff f 0).re := by
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  simp only [torusAffineField,affineFourierField,torusRealContinuation_mean_free hs f hy]
  ring

lemma torusAffineField_flux_divergence {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) {x : Coord3} (hx : 0<x 0) :
    coordinateDivergence (flatModeFlux s (torusAffineField s κ f)) x=0 := by
  have he := torusAffineField_polar_eventually hs κ f hx
  have hf : flatModeFlux s (torusAffineField s κ f)=ᶠ[𝓝 x]
      flatModeFlux s (affineFourierField s (realTorusAmplitude f) (realTorusPhase f) κ (mFourierCoeff f 0).re) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    simp only [flatModeFlux,hy]
  rw [coordinateDivergence_congr_nhds hf,flatModeFlux_divergence
    ((affineFourierField_smooth hs (realTorusAmplitude_bound f) κ (mFourierCoeff f 0).re).contDiffAt
      ((axial_halfspace_open 0).mem_nhds hx)),
    affineFourierField_harmonic hs (realTorusAmplitude_bound f) κ (mFourierCoeff f 0).re hx]

lemma flatModeFlux_tensor (s : Fin 3 → ℝ) (f : Coord3 → ℝ) (x : Coord3) :
    flatModeFlux s f x=flatBackgroundTensor s*ᵥ(fun i => fderiv ℝ f x (Pi.single i 1)) := by
  ext i
  fin_cases i <;> simp [flatModeFlux,flatBackgroundTensor,Matrix.mulVec,dotProduct,Fin.sum_univ_three,flatAxis]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RankProjectionFirst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma linearTensorPullback_refl (E : Coord3 → Mat3) :
    linearTensorPullback (ContinuousLinearEquiv.refl ℝ Coord3) E=E := by
  funext x
  change operatorMatrix (ContinuousLinearMap.id ℝ Coord3)*E x*
    (operatorMatrix (ContinuousLinearMap.id ℝ Coord3))ᵀ=E x
  rw [operatorMatrix_id,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one]

namespace WeakFiniteTensorPair

@[simp] lemma output_E {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (b : Fin 2 → ℝ) :
    (w.output Q b).E=w.E := by
  funext x
  change linearTensorPullback (ContinuousLinearEquiv.refl ℝ Coord3) w.E (x-0)=_
  rw [linearTensorPullback_refl,sub_zero]

end WeakFiniteTensorPair

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialExtension
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_self {d e : ℝ} {f : Coord3 → E} {x : Coord3}
    (hx : d+e/2<x 0) : axialZeroExtension d e f=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx] with y hy
  exact ite_eq_left hy

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_eventually_zero {d e : ℝ} (he : 0<e) {f : Coord3 → E}
    (hf : ∀ x,x 0∈Icc d (d+e) → f x=0) {x : Coord3} (hx : x 0<d+e) :
    axialZeroExtension d e f=ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [(isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hx] with y hy
  dsimp only [axialZeroExtension]
  split_ifs with hh
  · exact hf y ⟨by linarith only [he,hh],hy.le⟩
  · rfl

lemma axialZeroExtension_contDiff {n : WithTop ℕ∞} {d e : ℝ} (he : 0<e)
    {f : Coord3 → E} (hf : ContDiffOn ℝ n f {x | d<x 0})
    (hz : ∀ x,x 0∈Icc d (d+e) → f x=0) : ContDiff ℝ n (axialZeroExtension d e f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x 0<d+e
  · exact contDiffAt_const.congr_of_eventuallyEq (axialZeroExtension_eventually_zero he hz hx)
  · have hx' : d+e/2<x 0 := by linarith
    exact (hf.contDiffAt ((axial_halfspace_open d).mem_nhds (show d<x 0 by linarith))).congr_of_eventuallyEq
      (axialZeroExtension_eventually_self hx')

omit [NormedSpace ℝ E] in
lemma axialZeroExtension_periodic {T d e : ℝ} {f : Coord3 → E}
    (hf : AngularPeriodic T f) : AngularPeriodic T (axialZeroExtension d e f) := by
  intro n x
  change (if d+e/2<x 0+0 then f (x+angularShift T n) else 0)=_
  rw [add_zero,hf n x]
  rfl

lemma axialZeroExtension_divergence {d e : ℝ} (he : 0<e) {F : Coord3 → Coord3}
    (hz : ∀ x,x 0∈Icc d (d+e) → F x=0)
    (hd : ∀ x,d<x 0 → coordinateDivergence F x=0) (x : Coord3) :
    coordinateDivergence (axialZeroExtension d e F) x=0 := by
  by_cases hx : x 0<d+e
  · rw [coordinateDivergence_congr_nhds (axialZeroExtension_eventually_zero he hz hx)]
    simp [coordinateDivergence]
  · rw [coordinateDivergence_congr_nhds (axialZeroExtension_eventually_self (by linarith : d+e/2<x 0))]
    exact hd x (by linarith)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WeakPairOverlap
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma WeakFiniteTensorPair.component_flux_C1 {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (j : Fin 2) : ContDiff ℝ 1 (fun y => (w.G y).col j) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp w.flux_C1)

lemma WeakFiniteTensorPair.flux_on_constant_patch {U V : Set Coord3}
    (w : WeakFiniteTensorPair U) (hV : IsOpen V) (K : Mat3)
    (hK : ∀ x∈V,w.E x=K) (f : Coord3 → Fin 2 → ℝ)
    (_ : ContDiffOn ℝ 2 f V) (hw : ∀ x∈V,w.v x=f x) :
    ∀ x∈V,w.G x=K*gradientColumns (fderiv ℝ f x) := by
  have ha : w.G=ᵐ[volume.restrict V] (fun x => K*gradientColumns (fderiv ℝ w.v x)) := by
    filter_upwards [ae_restrict_of_ae w.constitution,ae_restrict_mem hV.measurableSet] with x hx hxV
    rw [←hx,hK x hxV]
  have hd : Continuous (fun x => K*gradientColumns (fderiv ℝ w.v x)) := by
    have hh := w.smooth.continuous_fderiv (by norm_num)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun x => ∑ k : Fin 3,K i k*(fderiv ℝ w.v x (Pi.single k 1)) j)
    apply continuous_finsetSum
    intro k _
    exact continuous_const.mul ((continuous_apply j).comp (hh.clm_apply continuous_const))
  have he := Measure.eqOn_open_of_ae_eq ha hV w.flux_C1.continuous.continuousOn hd.continuousOn
  intro x hx
  rw [he hx]
  have hv : w.v=ᶠ[𝓝 x] f := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hw y hy
  dsimp only
  rw [hv.fderiv_eq (𝕜 := ℝ)]

lemma WeakFiniteTensorPair.flux_on_flat_patch {U V : Set Coord3}
    (w : WeakFiniteTensorPair U) (hV : IsOpen V) (s : Fin 3 → ℝ)
    (hE : ∀ x∈V,w.E x=flatBackgroundTensor s) (f : Coord3 → Fin 2 → ℝ)
    (hf : ContDiffOn ℝ 2 f V) (hw : ∀ x∈V,w.v x=f x) (j : Fin 2) :
    ∀ x∈V,(w.G x).col j=flatModeFlux s (fun y => f y j) x := by
  intro x hx
  rw [w.flux_on_constant_patch hV _ hE f hf hw x hx,flatModeFlux_tensor]
  change flatBackgroundTensor s*ᵥ(gradientColumns (fderiv ℝ f x)).col j = _
  congr 1
  ext i
  rw [(hasFDerivAt_pi'.mp ((hf.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt j).fderiv]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_TorusEndingCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusEndingFluxCorrection_C1 {d e : ℝ} (he : 0<e) {G F : Coord3 → Coord3}
    (hG : ContDiff ℝ 1 G) (hF : ContDiffOn ℝ 1 F {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x) :
    ContDiff ℝ 1 (torusEndingFluxCorrection d e G F) := by
  apply axialZeroExtension_contDiff (by linarith : 0<e/2)
  · exact (hG.contDiffOn.sub hF).mono (fun x hx => by dsimp at hx ⊢; linarith)
  · intro x hx
    change G x-F x=0
    exact sub_eq_zero.mpr (hz x ⟨by linarith [hx.1],by linarith [hx.2]⟩)

lemma torusEndingFluxCorrection_periodic {T d e : ℝ} {G F : Coord3 → Coord3}
    (hG : AngularPeriodic T G) (hF : AngularPeriodic T F) :
    AngularPeriodic T (torusEndingFluxCorrection d e G F) := by
  apply axialZeroExtension_periodic
  intro n x
  change G (x+angularShift T n)-F (x+angularShift T n)=G x-F x
  rw [hG n x,hF n x]

lemma torusEndingFluxCorrection_divergence {d e : ℝ} (he : 0<e) {G F : Coord3 → Coord3}
    (hG : ContDiff ℝ 1 G) (hF : ContDiffOn ℝ 1 F {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x)
    (hdG : ∀ x,d<x 0 → coordinateDivergence G x=0)
    (hdF : ∀ x,d<x 0 → coordinateDivergence F x=0) (x : Coord3) :
    coordinateDivergence (torusEndingFluxCorrection d e G F) x=0 := by
  apply axialZeroExtension_divergence (by linarith : 0<e/2) _ _ x
  · intro y hy
    change G y-F y=0
    exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)
  · intro y hy
    have hyd : d<y 0 := by linarith
    change coordinateDivergence (fun x => G x-F x) y=0
    rw [coordinateDivergence_sub_at (hG.differentiable (by norm_num) y)
      ((hF.contDiffAt ((axial_halfspace_open d).mem_nhds hyd)).differentiableAt (by norm_num)),
      hdG y hyd,hdF y hyd,sub_self]

lemma torusEndingFluxCorrection_initial_zero {d e : ℝ} (he : 0<e)
    {G F : Coord3 → Coord3} (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x)
    {x : Coord3} (hx : x 0<d+3*e/4) :
    torusEndingFluxCorrection d e G F=ᶠ[𝓝 x] (fun _ => 0) := by
  apply axialZeroExtension_eventually_zero (by linarith : 0<e/2) _ (by linarith)
  intro y hy
  change G y-F y=0
  exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)

lemma torusEndingFluxCorrection_terminal {d e : ℝ} {G F : Coord3 → Coord3}
    {x : Coord3} (hx : d+e/2<x 0) :
    torusEndingFluxCorrection d e G F=ᶠ[𝓝 x] (G-F) :=
  axialZeroExtension_eventually_self (by linarith)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma torusInitialPair_eq (s : Fin 3 → ℝ) (f : Fin 2 → TorusL2) (x : Coord3) :
    torusInitialPair s f x=![x 0+torusRealContinuation s (f 0) x,torusRealContinuation s (f 1) x] := by
  ext j
  fin_cases j <;> simp [torusInitialPair,torusAffineField,normalizedSlope]

namespace TorusEndingData
variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (z : TorusEndingData s f)

lemma initial_field (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    z.w.v x=torusInitialPair s f x := by
  rw [z.initial_v x ⟨hx.1.le,hx.2.le⟩,torusInitialPair_eq]

end TorusEndingData
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSpectralContinuation
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusSpectralSynthesis_coeff (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (h : Fin 2 → ℤ) :
    mFourierCoeff (torusSpectralSynthesis s f) h=f.val 0 h := by
  rw [←mFourierBasis_repr]
  change (mFourierBasis (d:=Fin 2)).repr ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) h=_
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma torusRealContinuation_spectral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f) x=
      (endPoissonField s f 0 (x 0,torusAngles x)).re := by
  unfold torusRealContinuation
  congr 1
  rw [torusPoissonContinuous_apply hs hx]
  unfold endPoissonField
  apply tsum_congr
  intro h
  simp [endPoissonModeField,endModeCoefficient,torusSpectralSynthesis_coeff]

lemma mFourierCoeff_Lp_add (f g : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (f+g) h=mFourierCoeff f h+mFourierCoeff g h := by
  simp only [←mFourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply]

lemma mFourierCoeff_Lp_neg (f : TorusL2) (h : Fin 2 → ℤ) :
    mFourierCoeff (-f) h= -mFourierCoeff f h := by
  simp only [←mFourierBasis_repr,map_neg,lp.coeFn_neg,Pi.neg_apply]

lemma torusPoissonContinuous_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {t : ℝ} (ht : 0<t) (f g : TorusL2) :
    torusPoissonContinuous s t (f+g)=torusPoissonContinuous s t f+torusPoissonContinuous s t g := by
  unfold torusPoissonContinuous
  simp only [mFourierCoeff_Lp_add,mul_add]
  calc
    _ = ∑' h, (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h+
        ((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff g h) • mFourier h) := by
      apply tsum_congr
      intro h
      exact _root_.add_smul (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h))
        (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff g h)) (mFourier h)
    _ = _ := (poisson_series_norm_summable hs ht f).of_norm.tsum_add
      (poisson_series_norm_summable hs ht g).of_norm

lemma torusPoissonContinuous_neg (s : Fin 3 → ℝ) (t : ℝ) (f : TorusL2) :
    torusPoissonContinuous s t (-f)= -torusPoissonContinuous s t f := by
  unfold torusPoissonContinuous
  simp only [mFourierCoeff_Lp_neg,mul_neg]
  calc
    _ = ∑' h, - (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h) • mFourier h) := by
      apply tsum_congr
      intro h
      exact _root_.neg_smul (((Real.exp (-torusRate s h*t):ℂ)*mFourierCoeff f h)) (mFourier h)
    _ = _ := tsum_neg

lemma torusRealContinuation_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f g : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (f+g) x=torusRealContinuation s f x+torusRealContinuation s g x := by
  simp only [torusRealContinuation,torusPoissonContinuous_add hs hx,
    ContinuousMap.add_apply,Complex.add_re]

lemma torusRealContinuation_neg (s : Fin 3 → ℝ) (f : TorusL2) (x : Coord3) :
    torusRealContinuation s (-f) x= -torusRealContinuation s f x := by
  simp only [torusRealContinuation,torusPoissonContinuous_neg,ContinuousMap.neg_apply,Complex.neg_re]

lemma torusRealContinuation_sub {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f g : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (f-g) x=torusRealContinuation s f x-torusRealContinuation s g x := by
  simp only [sub_eq_add_neg,torusRealContinuation_add hs f (-g) hx,torusRealContinuation_neg]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchOutputNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

variable {E : Type*} [AddCommGroup E]

variable [Module ℝ E]

lemma branchNormalize_basis_slopes (i : Fin 3) :
    branchNormalize i (fun j => centralBasisSlopes j i)=normalizedSlope := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [branchNormalize,centralBasisSlopes,normalizedSlope]

lemma branchNormalize_normalized_slope (i : Fin 3) :
    branchNormalize i normalizedSlope=(fun j => centralBasisSlopes j i) := by
  rw [←branchNormalize_basis_slopes i,branchNormalize_involutive i]

lemma branchNormalize_affineField {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (κ : Fin 2 → ℝ) (f : Fin 2 → TorusL2) {x : Coord3} (hx : 0<x 0) :
    branchNormalize i (fun j => torusAffineField s (κ j) (f j) x)=
      fun j => torusAffineField s (branchNormalize i κ j) (branchNormalize i f j) x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [branchNormalize,torusAffineField,torusRealContinuation_neg,
      torusRealContinuation_sub hs _ _ hx] <;> ring

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

namespace TorusEndingData
variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (z : TorusEndingData s f)

lemma terminal_component (j : Fin 2) (x : Coord3) (hx : z.R≤x 0) :
    z.w.v x j=normalizedSlope j*x 0+(mFourierCoeff (f j) 0).re := by
  rw [z.terminal_v x hx]
  fin_cases j <;> simp [normalizedSlope]

lemma terminal_gradient (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    (gradientColumns (fderiv ℝ z.w.v x)).col j=normalizedSlope j • Pi.single 0 1 := by
  have he : (fun x => z.w.v x j)=ᶠ[𝓝 x]
      (fun x => normalizedSlope j*x 0+(mFourierCoeff (f j) 0).re) := by
    filter_upwards [(axial_halfspace_open z.R).mem_nhds hx] with y hy
    exact z.terminal_component j y hy.le
  have hd := (((ContinuousLinearMap.proj (0 : Fin 3) : Coord3 →L[ℝ] ℝ).hasFDerivAt
    (x:=x)).const_mul (normalizedSlope j)).add_const ((mFourierCoeff (f j) 0).re)
  ext i
  change fderiv ℝ z.w.v x (Pi.single i 1) j=normalizedSlope j*((Pi.single (0:Fin 3) (1:ℝ) : Coord3) i)
  rw [←potential_component_fderiv (z.w.smooth.differentiable (by norm_num)) j,
    he.fderiv_eq (𝕜 := ℝ)]
  change fderiv ℝ (fun x => normalizedSlope j *
    (ContinuousLinearMap.proj (0 : Fin 3) : Coord3 →L[ℝ] ℝ) x +
      (mFourierCoeff (f j) 0).re) x (Pi.single i 1)=_
  rw [hd.fderiv]
  fin_cases i <;> simp

lemma terminal_flux (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    (z.w.G x).col j=normalizedSlope j • Pi.single 0 1 := by
  have ha : (fun x => (z.w.G x).col j)=ᵐ[volume.restrict {x : Coord3 | z.R<x 0}]
      (fun _ => normalizedSlope j • Pi.single 0 1) := by
    filter_upwards [ae_restrict_of_ae z.w.constitution,
      ae_restrict_mem (axial_halfspace_open z.R).measurableSet] with y hy hyR
    rw [←hy]
    change z.w.E y*ᵥ(gradientColumns (fderiv ℝ z.w.v y)).col j=_
    rw [z.terminal_gradient j y hyR,Matrix.mulVec_smul,z.terminal_E y hyR.le]
  exact (Measure.eqOn_open_of_ae_eq ha (axial_halfspace_open z.R)
    (z.w.component_flux_C1 j).continuous.continuousOn continuous_const.continuousOn) hx

end TorusEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_BranchFiniteEnding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma branchFinitePair_v {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) :
    (branchFinitePair i z).v x=branchNormalize i (z.w.v x) := by
  simp [branchFinitePair]

lemma branchFinitePair_flux {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) (j : Fin 2) :
    ((branchFinitePair i z).G x).col j=branchNormalize i (fun k => (z.w.G x).col k) j := by
  change (linearColumnsPullback (ContinuousLinearEquiv.refl ℝ Coord3)
    (branchNormalizeEquiv i) z.w.G (x-0)).col j=_
  rw [sub_zero,linearColumnsPullback_col]
  ext k
  fin_cases i <;> fin_cases j <;>
    simp [operatorMatrix,branchNormalizeEquiv_apply,branchNormalize,linearFluxPullback,
      Fin.sum_univ_two,Pi.single_apply,Matrix.col_apply]
  ring

lemma branchFinitePair_initial {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {f : Fin 2 → TorusL2} (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    (branchFinitePair i z).v x=fun j => torusAffineField s (centralBasisSlopes j i) (f j) x := by
  rw [branchFinitePair_v,z.initial_field x hx]
  change branchNormalize i (fun j => torusAffineField s (normalizedSlope j)
    (branchNormalize i f j) x)=_
  rw [branchNormalize_affineField hs i normalizedSlope (branchNormalize i f) (z.d_pos.trans hx.1),
    branchNormalize_normalized_slope,branchNormalize_involutive]

lemma branchFinitePair_terminal_flux {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) (hx : z.R<x 0) (j : Fin 2) :
    ((branchFinitePair i z).G x).col j=centralBasisSlopes j i • Pi.single 0 1 := by
  rw [branchFinitePair_flux]
  have he : (fun k => (z.w.G x).col k)=(fun k => normalizedSlope k • Pi.single 0 1) :=
    funext fun k => z.terminal_flux k x hx
  rw [he]
  fin_cases i <;> fin_cases j <;> simp [branchNormalize,normalizedSlope,centralBasisSlopes]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchFinitePair_periodic_v : AngularPeriodic (2*Real.pi) (branchFinitePair i z).v := by
  intro n x
  simp only [branchFinitePair_v,z.periodic_v n x]

lemma branchFinitePair_initial_E (x : Coord3) (hx : x 0∈Icc z.d (z.d+z.e)) :
    (branchFinitePair i z).E x=flatBackgroundTensor s := by
  simpa only [branchFinitePair,WeakFiniteTensorPair.output_E] using z.initial_E x hx

lemma branchFinitePair_periodic_E : AngularPeriodic (2*Real.pi) (branchFinitePair i z).E := by
  simpa only [branchFinitePair,WeakFiniteTensorPair.output_E] using z.periodic_E

lemma branchFinitePair_initial_flux
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    ((branchFinitePair i z).G x).col j=
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x := by
  apply (branchFinitePair i z).flux_on_flat_patch
    (V:={x : Coord3 | x 0∈Ioo z.d (z.d+z.e)})
    (isOpen_Ioo.preimage (continuous_apply 0)) s
    (fun x hx => branchFinitePair_initial_E i z x ⟨hx.1.le,hx.2.le⟩)
    (fun x j => torusAffineField s (centralBasisSlopes j i) (f j) x)
    (contDiffOn_pi.mpr fun j => ((torusAffineField_smooth hs _ _).of_le
      (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun y hy => z.d_pos.trans hy.1))
    (fun x hx => branchFinitePair_initial hs i z x hx) j x hx

lemma branchFluxCorrection_C1
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 1 (branchFluxCorrection i z j) := by
  exact torusEndingFluxCorrection_C1 z.e_pos ((branchFinitePair i z).component_flux_C1 j)
    (((flatModeFlux_smoothOn (axial_halfspace_open 0) (torusAffineField_smooth hs _ _)).of_le
      (show (1 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => branchFinitePair_initial_flux i z hs j x hx)

lemma branchFluxCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchFluxCorrection i z j) := by
  exact torusEndingFluxCorrection_periodic
    (fun n x => congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j)
      ((branchFinitePair i z).flux_periodic (branchFinitePair_periodic_v i z)
        (branchFinitePair_periodic_E i z) n x))
    (flatModeFlux_periodic (torusAffineField_periodic _ _ _))

lemma branchFluxCorrection_divergence
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) : coordinateDivergence (branchFluxCorrection i z j) x=0 := by
  exact torusEndingFluxCorrection_divergence z.e_pos ((branchFinitePair i z).component_flux_C1 j)
    (((flatModeFlux_smoothOn (axial_halfspace_open 0) (torusAffineField_smooth hs _ _)).of_le
      (show (1 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => branchFinitePair_initial_flux i z hs j x hx)
    (fun x hx => (branchFinitePair i z).flux_divergence (axial_halfspace_open z.d) j x hx)
    (fun x hx => torusAffineField_flux_divergence hs _ _ (z.d_pos.trans hx)) x

lemma branchFluxCorrection_zero
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0=0) : branchFluxCorrection i z j x=0 := by
  exact (torusEndingFluxCorrection_initial_zero z.e_pos
    (fun y hy => branchFinitePair_initial_flux i z hs j y hy)
    (by rw [hx]; linarith [z.d_pos,z.e_pos])).eq_of_nhds

lemma branchFluxCorrection_terminal (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    branchFluxCorrection i z j x=centralBasisSlopes j i • Pi.single 0 1-
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x := by
  rw [show branchFluxCorrection i z j x=((branchFinitePair i z).G x).col j-
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x from
    (torusEndingFluxCorrection_terminal (by linarith [z.e_pos,z.overlap_lt] : z.d+z.e/2<x 0)).eq_of_nhds,
    branchFinitePair_terminal_flux i z x hx j]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalChildTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceChildTensorPush_mixed (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y g v : Fin 3 → ℝ) :
    sourceScale^3 *
      ((fun i => sourceScale⁻¹*g (childAxis i)) ⬝ᵥ
        (sourceChildTensorPush k A (sourceChildCoordinates (actualChildSign k) y)*ᵥv))=
      g ⬝ᵥ (A y*ᵥ(fun i => sourceScale*v (childAxis i))) := by
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  simp only [sourceChildTensorPush,he,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  have h₀ : childAxis 0=1 := rfl
  have h₁ : childAxis 1=0 := rfl
  have h₂ : childAxis 2=2 := rfl
  simp only [h₀,h₁,h₂]
  norm_num [sourceScale]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalChildIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceChild_integral (σ : ℝ) {D : Set (Fin 3 → ℝ)}
    (hD : MeasurableSet D) (g : (Fin 3 → ℝ) → ℝ) :
    (∫ y in sourceChildCoordinates σ '' D,g y)=
      ∫ y in D,sourceScale^3*g (sourceChildCoordinates σ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (fun x _ => (sourceChildCoordinates_hasFDeriv σ x).hasFDerivWithinAt)
    (sourceChildHomeomorph σ).injective.injOn g
  change (∫ y in sourceChildCoordinates σ '' D,g y)=
    ∫ y in D,|sourceChildDerivative.det| • g (sourceChildCoordinates σ y) at h
  simpa only [sourceChildDerivative_det,abs_neg,abs_pow,
    abs_of_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale]),smul_eq_mul] using h

lemma originalPiGradient_memLp_on_ball {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1) (k : Fin 3) :
    MemLp (fun y => originalPiGradient u y k) 2 (volume.restrict D) := by
  have he := ballWholePiComponentCLM_ae_of_ae k.succ u.val
    (fun y => u.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl)
  apply MemLp.ae_eq ?_ ((Lp.memLp (ballWholePiComponentCLM k.succ u.val)).restrict D)
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem hD] with y hy hm
  rw [hy,ite_eq_left (hb y hm)]
  rfl

lemma originalPiGradient_eq_on_ball {D : Set (Fin 3 → ℝ)}
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u : H1)
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → ∀ k,
      weakGradient u x k=G (WithLp.ofLp x) k) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient u y=G y := by
  have hh := (ae_restrict_iff' (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)).mp he
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hp] with y hy hm
  ext k
  exact hy (hb y hm) hm k

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalBlockRegion_compact : IsCompact physicalBlockRegion :=
  centralPhysical_compact.union (isCompact_iUnion physicalEndRegion_compact)

lemma physicalBlockRegion_subset_ball {y : Fin 3 → ℝ} (hy : y∈physicalBlockRegion) :
    WithLp.toLp 2 y∈ball := by
  rcases hy with hc|he
  · exact centralPhysical_subset_ball hc
  · obtain ⟨i,hi⟩ := mem_iUnion.mp he
    exact physicalEndRegion_subset_ball i hi

lemma physicalEndRegion_mem_block (i : Fin 3) : physicalEndRegion i⊆physicalBlockRegion :=
  fun _ hy => Or.inr (mem_iUnion.mpr ⟨i,hy⟩)

lemma physicalBlockRegion_central_end_exclusive_ae :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),
      y∈centralPhysical → ∀ i : Fin 3,y∉physicalEndRegion i := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy i hi
  have ht := (centralPhysical_time_iff y).mp hy
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₀ (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₁ (le_antisymm (ht.2 1) hi.1)

lemma physicalBlockRegion_indicator_ae (f : (Fin 3 → ℝ) → ℝ) :
    physicalBlockRegion.indicator f=ᵐ[volume]
      (fun y => centralPhysical.indicator f y+
        ∑ i : Fin 3,(physicalEndRegion i).indicator f y) := by
  classical
  filter_upwards [physicalBlockRegion_central_end_exclusive_ae] with y he
  by_cases hc : y∈centralPhysical
  · have hb : y∈physicalBlockRegion := Or.inl hc
    rw [indicator_of_mem hb,indicator_of_mem hc]
    have hsum : (∑ i : Fin 3,(physicalEndRegion i).indicator f y)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (he hc i) _
    rw [hsum,add_zero]
  · rw [indicator_of_notMem hc]
    by_cases hend : ∃ i : Fin 3,y∈physicalEndRegion i
    · obtain ⟨i,hi⟩ := hend
      have hb : y∈physicalBlockRegion := physicalEndRegion_mem_block i hi
      rw [indicator_of_mem hb,zero_add]
      symm
      calc
        _ = (physicalEndRegion i).indicator f y := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact indicator_of_notMem (fun hj =>
              disjoint_left.mp (physicalEndRegion_pairwise_disjoint hji) hj hi) _
          · simp
        _ = f y := indicator_of_mem hi f
    · have hb : y∉physicalBlockRegion := by
        rintro (hh|hh)
        · exact hc hh
        · exact hend (mem_iUnion.mp hh)
      rw [indicator_of_notMem hb,zero_add]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi => hend ⟨i,hi⟩) _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma physicalBlockRegion_integral (f : (Fin 3 → ℝ) → ℝ)
    (hc : IntegrableOn f centralPhysical volume)
    (he : ∀ i : Fin 3,IntegrableOn f (physicalEndRegion i) volume) :
    (∫ y in physicalBlockRegion,f y)=(∫ y in centralPhysical,f y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,f y := by
  have hci := hc.integrable_indicator centralPhysical_compact.measurableSet
  have hei (i : Fin 3) := (he i).integrable_indicator (physicalEndRegion_compact i).measurableSet
  rw [←integral_indicator physicalBlockRegion_compact.measurableSet]
  rw [integral_congr_ae (physicalBlockRegion_indicator_ae f)]
  rw [integral_add hci (integrable_finsetSum _ (fun i _ => hei i)),
    integral_finsetSum _ (fun i _ => hei i),
    integral_indicator centralPhysical_compact.measurableSet]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator (physicalEndRegion_compact i).measurableSet

end ScalarConductivity

end


end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExtendedBox_mono {l r l' r' : ℝ} (hl : l'≤l) (hr : r ≤ r') :
    sourceExtendedBox l r ⊆ sourceExtendedBox l' r' := by
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩

lemma sourceCollarPieces_aedisjoint {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Pairwise (fun k m : Fin 4 × Fin 4 => AEDisjoint volume
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r)
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r)) := by
  intro k m hkm
  have hn : ∀ᵐ y : Fin 3 → ℝ, y∉
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r) ∩
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r) := by
    filter_upwards [sourceCollar_open_charts_ae] with y hy hm
    obtain ⟨⟨z,hz,hzy⟩,w,hw,hwy⟩ := hm
    have hyb := sourceCollarClosedPiece_subset (l:=-(1:ℝ)/100) (r:=1/100)
      le_rfl le_rfl k.1 k.2 ⟨z,sourceExtendedBox_mono hl hr hz,hzy⟩
    obtain ⟨i,j,x,hx,hxy⟩ := hy hyb
    obtain ⟨hik,hjk⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx
      (sourceExtendedBox_mono hl hr hz) (hxy.trans hzy.symm)
    obtain ⟨him,hjm⟩ := sourceCollarPiece_open_unique i j m.1 m.2 hx
      (sourceExtendedBox_mono hl hr hw) (hxy.trans hwy.symm)
    exact hkm (Prod.ext (hik.symm.trans him) (hjk.symm.trans hjm))
  simpa only [AEDisjoint,ae_iff,not_not,Set.ofPred_mem_eq] using hn

theorem sourceClosedCollarBand_measure_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r)=
      ∑ i : Fin 4,∑ j : Fin 4,
        volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  have he : (⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)=
      ⋃ k : Fin 4 × Fin 4,sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r := by
    ext x
    simp
  rw [he,Measure.restrict_iUnion_ae (sourceCollarPieces_aedisjoint hl hr)
    (fun k => (sourceCollarClosedPiece_measurable l r k.1 k.2).nullMeasurableSet),
    Measure.sum_fintype,Fintype.sum_prod_type]

lemma integral_sourceClosedCollarBand_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {F : (Fin 3 → ℝ) → ℝ}
    (hF : IntegrableOn F (sourceClosedCollarBand l r) volume) :
    (∫ y in sourceClosedCollarBand l r,F y)=
      ∑ i : Fin 4,∑ j : Fin 4,
        ∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,F y := by
  have hi (i j : Fin 4) := hF.mono_set (sourceCollarClosedPiece_subset hl hr i j)
  rw [sourceClosedCollarBand_measure_faces hl hr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hi i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hi _ j)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTerminalL2
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma spectralTerminalDensity_pair (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f g : spectralTraceGraph (torusRate s)) :
    inner ℂ (spectralTerminalDensity s hR f) (g.val 0)=
      spectralWeightedPairL s (spectralEndWeight s R f) g := by
  change inner ℂ (spectralTerminalDensity s hR f) (g.val 0)=
    inner ℂ (spectralEndWeight s R f) (g.val 1)
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro h
  change inner ℂ (((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ)*f.val 1 h)
    (g.val 0 h)=inner ℂ ((Real.exp (-torusRate s h*|R|):ℂ)*f.val 1 h) (g.val 1 h)
  rw [g.property h,abs_of_pos hR]
  simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalSmoothTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma piSmoothH1_gradient {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {D : Set (Fin 3 → ℝ)} (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    ∀ᵐ y : Fin 3 → ℝ,y∈D → originalPiGradient (piSmoothH1 hφ) y=physicalTestCovector φ y := by
  apply originalPiGradient_eq_on_ball hb (piSmoothH1 hφ) _
  filter_upwards [piSmoothH1_jet hφ] with x hx _ j
  exact congrArg (fun v : JetFiber => v j.succ) hx

lemma physicalSmoothCentral_jet {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    H1JetOn (piSmoothH1 hφ) centralPhysical (centralFullJetCLM s (physicalSmoothCentral s hφ).val) := by
  let f : centralSmoothFunctions := ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩
  have he : (fun y => f (sourcePairCoordinates y))=φ := by
    funext y
    exact congrArg φ (sourcePairCLE.symm_apply_apply y)
  filter_upwards [piSmoothH1_jet hφ,centralFullJetCLM_smooth_ae s f] with x hx hc hy
  change _=centralFullJetCLM s (centralEmbedL s f) x
  rw [hc hy,he,hx]

lemma physicalSmoothCentral_parent_trace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    centralT s 0 (physicalSmoothCentral s hφ)=smoothCollarTrace s centralThickness hφ := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩ 0).val 0=_
  rw [centralSmoothTrace_fst]
  ext h
  rw [centralTraceFourier_apply,smoothCollarTrace_fst]
  congr 1

lemma physicalSmoothCentral_child_trace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    centralT s k.succ (physicalSmoothCentral s hφ)=smoothCollarTrace s (-centralThickness)
      (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) := by
  apply spectralTraceGraph_fst_injective (torusRate s)
  change (centralSmoothTrace s ⟨φ ∘ sourcePairCLE.symm,hφ.comp sourcePairCLE.symm.contDiff⟩ k.succ).val 0=_
  rw [centralSmoothTrace_fst]
  ext h
  rw [centralTraceFourier_apply,smoothCollarTrace_fst]
  congr 1
  funext θ
  fin_cases k <;> rfl

lemma physicalTestCovector_child {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (σ : ℝ) (y : Fin 3 → ℝ) :
    physicalTestCovector (φ ∘ sourceChildCoordinates σ) y=
      (fun i => sourceScale*physicalTestCovector φ (sourceChildCoordinates σ y) (childAxis i)) := by
  ext i
  change fderiv ℝ (φ ∘ sourceChildCoordinates σ) y (Pi.single i 1)=_
  rw [((hφ.differentiable (by simp) _).hasFDerivAt.comp y
    (sourceChildCoordinates_hasFDeriv σ y)).fderiv,ContinuousLinearMap.comp_apply]
  have he : sourceChildDerivative (Pi.single i 1)=sourceScale • Pi.single (childAxis i) 1 := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [sourceChildDerivative_apply,childAxis]
  rw [he,map_smul]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineCylinderIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.affineCylinderIntegralMeasureSpace
local instance affineCylinderIntegralProbabilityMeasure_r8ef6ae_1 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma integrable_affineEndCoordinates {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    Integrable (F ∘ affineEndCoordinates a b) ((volume.restrict (Ioc l r)).prod volume) := by
  have hle := affineEndCoordinates_interval_le ha hT
  have hν : sourceCylinderMeasure 0 R=(FiniteAxisMeasure R).prod volume := by
    rfl
  have hμ : sourceCylinderMeasure l r=(volume.restrict (Ioc l r)).prod volume := by
    rfl
  rw [hν,hμ] at hle
  have h := (hF.smul_measure (c:=ENNReal.ofReal |a⁻¹|) ENNReal.ofReal_ne_top).mono_measure hle
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_affineEndCoordinates a b).aemeasurable).mp h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularPhysicalTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

theorem sourceAngularJet_attachedCovector {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {a : ℝ} (ha : a≠0) (b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    (fun k : Fin 3 => (sourceAngularJet f a⁻¹ b k.succ
      (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)=
      attachedFlatTestCovector f a i j x := by
  have h1 : |x 1|<1 := by exact hx.2.1
  have h2 : |x 2|<1 := by exact hx.2.2
  have ht : a⁻¹*(a*(x 0-b))+b=x 0 := by field_simp; ring
  rw [sourceAngularJet_face hf a⁻¹ b (a*(x 0-b)) i j ht h1 h2]
  have h := attachedFlatTestCovector_chain f ha i j (sourceCollarOpenBox_subset hx)
    ((hf.differentiable (by simp)).differentiableAt)
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  have h2' := congrFun h 2
  simp only [sourceFaceAngleMatrix,endAxialMatrix,mulVec_diagonal] at h0 h1' h2'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=
    1*(a*attachedFlatTestCovector f a i j x 0) at h0
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1=
    (2*Real.pi*faceRayDensity 1 i (x 1))*(1*attachedFlatTestCovector f a i j x 1) at h1'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2=
    (2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))*(1*attachedFlatTestCovector f a i j x 2) at h2'
  ext k
  fin_cases k
  · change a⁻¹*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=_
    rw [h0]; field_simp [ha]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))=_
    rw [h1']
    field_simp [(faceRayDensity_pos' (w:=1) (by norm_num) i (x 1)).ne',Real.pi_ne_zero]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))=_
    rw [h2']
    field_simp [(faceRayDensity_pos' (w:=sourceRadialWidth) (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)).ne',Real.pi_ne_zero]; rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma deriv_ofReal_im_zero (f : ℝ → ℝ) (t : ℝ) :
    (deriv (fun x => (f x : ℂ)) t).im=0 := by
  by_cases h : DifferentiableAt ℝ (fun x => (f x:ℂ)) t
  · have hh := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t h.hasDerivAt
    have he := hh.deriv
    have heq : Complex.imCLM ∘ (fun x => (f x:ℂ)) = fun _ => (0:ℝ) := by
      funext x; rfl
    rw [heq,deriv_const] at he
    exact he.symm
  · rw [deriv_zero_of_not_differentiableAt h,Complex.zero_im]

lemma sourceAngularJet_im (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (j : Fin 4) (z : ℝ × UnitAddTorus (Fin 2)) :
    (sourceAngularJet f a b j z).im=0 := by
  have hd (k : Fin 2) : (torusDirectionalDerivative
      (fun θ => sourceAngularTest f a b (z.1,θ)) k z.2).im=0 :=
    deriv_ofReal_im_zero _ _
  fin_cases j
  · rfl
  · rfl
  · change (torusDirectionalDerivative _ 0 z.2 / (2*Real.pi:ℂ)).im=0
    simp [Complex.div_im,hd]
  · change (torusDirectionalDerivative _ 1 z.2 / (2*Real.pi:ℂ)).im=0
    simp [Complex.div_im,hd]

lemma flatCylinderMatrix_mixed (s u v : Fin 3 → ℝ) :
    u ⬝ᵥ (flatCylinderMatrix s*ᵥv)=
      u 0*v 0+s 0*(u 1*v 1)+s 1*(u 1*v 2+u 2*v 1)+s 2*(u 2*v 2) := by
  simp [flatCylinderMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

attribute [local instance] OAI.ScalarConductivity.cylinderPointEnergyMeasureSpace
local instance cylinderPointEnergyIsProbabilityMeasure_r8ef6ae_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma cylinderSlopeJet_covector_ae (r R : ℝ) (k : Fin 3) :
    cylinderSlopeJet r R k.succ=ᵐ[(FiniteAxisMeasure R).prod volume]
      fun _ => ((r • Pi.single 0 (1:ℝ)) k : ℂ) := by
  fin_cases k
  · change (cylinderSlopeJet r R 1)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (0:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,ite_true,smul_eq_mul,mul_one]
    rw [cylinderSlopeJet_derivative]
    have h1 := cylinderTensor_ae
      (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R) (mFourierLp 2 0)
    have h2 := (Measure.quasiMeasurePreserving_fst (μ:=FiniteAxisMeasure R)
      (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R)
    have h3 := (Measure.quasiMeasurePreserving_snd (μ:=FiniteAxisMeasure R)
      (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae (coeFn_mFourierLp 2 0)
    filter_upwards [h1,h2,h3] with z hz ht hθ
    change cylinderTensor _ _ z=_
    rw [hz,ht,hθ]
    simp [mFourier]
  · change (cylinderSlopeJet r R 2)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (1:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,show (1:Fin 3)≠0 by decide,
      ite_false,smul_eq_mul,mul_zero,Complex.ofReal_zero]
    rw [(cylinderSlopeJet_angular r R).1]
    filter_upwards [Lp.coeFn_zero (ℂ) 2 ((FiniteAxisMeasure R).prod volume)] with z hz
    exact hz
  · change (cylinderSlopeJet r R 3)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (2:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,show (2:Fin 3)≠0 by decide,
      ite_false,smul_eq_mul,mul_zero,Complex.ofReal_zero]
    rw [(cylinderSlopeJet_angular r R).2]
    filter_upwards [Lp.coeFn_zero (ℂ) 2 ((FiniteAxisMeasure R).prod volume)] with z hz
    exact hz

lemma cylinderEndJet_covector_ae (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) :
    ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (fun k : Fin 3 => (cylinderEndJet s hs r R hR f k.succ z).re)=
        fullEndFlatCovector s f r z.1 z.2 := by
  have h (k : Fin 3) : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (cylinderEndJet s hs r R hR f k.succ z).re=fullEndFlatCovector s f r z.1 z.2 k := by
    filter_upwards [Lp.coeFn_add (endPoissonJet s hs R hR f k.succ)
      (cylinderSlopeJet r R k.succ),endPoissonJet_ae s hs R hR f k.succ,
      cylinderSlopeJet_covector_ae r R k] with z hz hp hr
    change ((endPoissonJet s hs R hR f k.succ+cylinderSlopeJet r R k.succ) z).re=_
    rw [hz]
    simp only [Pi.add_apply,hp,hr,Complex.add_re,Complex.ofReal_re,fullEndFlatCovector]
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact funext hz

lemma flatCylinderEnergy_real_integral (s : Fin 3 → ℝ) {R : ℝ}
    (u v : FiniteCylinderJets R)
    (hv : ∀ k : Fin 3,∀ᵐ z∂(FiniteAxisMeasure R).prod volume,(v k.succ z).im=0) :
    Integrable (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re)))
        ((FiniteAxisMeasure R).prod volume) ∧
    (flatCylinderEnergy s u v).re=
      ∫ z,(fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))
          ∂(FiniteAxisMeasure R).prod volume := by
  let P (i j : Fin 4) := fun z => inner ℂ (u i z) (v j z)
  have hP (i j : Fin 4) : Integrable (P i j) ((FiniteAxisMeasure R).prod volume) :=
    L2.integrable_inner (𝕜:=ℂ) _ _
  let F := fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z+
    (s 1:ℂ)*(P 2 3 z+P 3 2 z)+(s 2:ℂ)*P 3 3 z
  have hF : Integrable F ((FiniteAxisMeasure R).prod volume) :=
    (((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ))).add
      (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ))).add ((hP 3 3).const_mul (s 2:ℂ))
  have he : (fun z => (F z).re)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))) := by
    filter_upwards [hv 0,hv 1,hv 2] with z h1 h2 h3
    change (v 1 z).im=0 at h1
    change (v 2 z).im=0 at h2
    change (v 3 z).im=0 at h3
    rw [flatCylinderMatrix_mixed]
    simp [F,P,RCLike.inner_apply,Complex.mul_re,h1,h2,h3]
    ring
  refine ⟨hF.re.congr he,?_⟩
  rw [←integral_congr_ae he]
  change _ = ∫ z,RCLike.re (F z) ∂(FiniteAxisMeasure R).prod volume
  rw [integral_re hF]
  congr 1
  change flatCylinderEnergy s u v = ∫ z,F z ∂(FiniteAxisMeasure R).prod volume
  unfold F
  rw [integral_add (f:=fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z+
      (s 1:ℂ)*(P 2 3 z+P 3 2 z)) (g:=fun z => (s 2:ℂ)*P 3 3 z)
      (((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ))).add
        (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ))) ((hP 3 3).const_mul (s 2:ℂ)),
    integral_add (f:=fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z)
      (g:=fun z => (s 1:ℂ)*(P 2 3 z+P 3 2 z))
      ((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ)))
      (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ)),
    integral_add (f:=P 1 1) (g:=fun z => (s 0:ℂ)*P 2 2 z)
      (hP 1 1) ((hP 2 2).const_mul (s 0:ℂ)),integral_const_mul,
    integral_const_mul,integral_const_mul,integral_add (hP 2 3) (hP 3 2)]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_EndPointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.endPointEnergyMeasureSpaceUnitAddCircle
local instance endPointEnergyIsProbabilityMeasure_r8ef6ae_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma sourceEndSmoothDensity_cylinder (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ a b R : ℝ) (hR : 0≤R)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (sourceEndSmoothDensity s f κ a b φ) ((FiniteAxisMeasure R).prod volume) ∧
    (∫ z,sourceEndSmoothDensity s f κ a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (flatCylinderEnergy s (cylinderEndJet s hs κ R hR f)
        (sourceAngularLpJet hφ a b R)).re := by
  let u := cylinderEndJet s hs κ R hR f
  let v := sourceAngularLpJet hφ a b R
  have hv (k : Fin 3) : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,(v k.succ z).im=0 := by
    filter_upwards [sourceAngularLpJet_ae hφ a b R k.succ] with z hz
    change (sourceAngularLpJet hφ a b R k.succ z).im=0
    rw [hz]
    exact sourceAngularJet_im φ a b k.succ z
  obtain ⟨hi,he⟩ := flatCylinderEnergy_real_integral s u v hv
  have hve : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (fun k : Fin 3 => (v k.succ z).re)=
        (fun k : Fin 3 => (sourceAngularJet φ a b k.succ z).re) := by
    filter_upwards [ae_all_iff.mpr (fun k : Fin 3 => sourceAngularLpJet_ae hφ a b R k.succ)] with z hz
    exact funext (fun k => congrArg Complex.re (hz k))
  have hd : (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re)))=ᵐ[(FiniteAxisMeasure R).prod volume]
        sourceEndSmoothDensity s f κ a b φ := by
    filter_upwards [cylinderEndJet_covector_ae s hs κ R hR f,hve] with z hu hv
    change (fun k : Fin 3 => (cylinderEndJet s hs κ R hR f k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))=_
    rw [hu,hv]
    rfl
  exact ⟨hi.congr hd,(integral_congr_ae hd).symm.trans he.symm⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularMeasureExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_faceRayCircle (w : ℝ) (j : Fin 4) :
    Continuous (fun b : ℝ => ((faceRayAngle w j b:ℝ):UnitAddCircle)) :=
  (AddCircle.continuous_mk' 1).comp
    (continuous_iff_continuousAt.mpr fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.sourceFaceMeasureCircleMeasureSpace
local instance sourceFaceMeasureCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma continuous_sourceFaceParameter (i j : Fin 4) : Continuous (sourceFaceParameter i j) := by
  unfold sourceFaceParameter
  simp_rw [sourceFaceAngles_torus]
  apply (continuous_apply 0).prodMk
  apply continuous_pi
  intro k
  fin_cases k
  · exact (continuous_faceRayCircle 1 i).comp (continuous_apply 1)
  · exact (continuous_faceRayCircle sourceRadialWidth j).comp (continuous_apply 2)

lemma continuous_sourceFaceWeight (i j : Fin 4) : Continuous (sourceFaceWeight i j) :=
  ((continuous_faceRayDensity 1 i).comp (continuous_apply 1)).mul
    ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))

lemma sourceFaceWeight_pos (i j : Fin 4) (x : Fin 3 → ℝ) : 0 < sourceFaceWeight i j x :=
  mul_pos (faceRayDensity_pos' (by norm_num) i (x 1))
    (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))

instance finite_sourceFaceMeasure (l r : ℝ) (i j : Fin 4) :
    IsFiniteMeasure (sourceFaceMeasure l r i j) := by
  have h : IntegrableOn (sourceFaceWeight i j) (sourceExtendedBox l r) volume :=
    (continuous_sourceFaceWeight i j).continuousOn.integrableOn_compact isCompact_Icc
  have := isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral
  unfold sourceFaceMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_sourceFaceMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l r : ℝ) (i j : Fin 4) {F : ℝ × UnitAddTorus (Fin 2) → E}
    (hF : AEStronglyMeasurable F (sourceFaceMeasure l r i j)) :
    (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ x in sourceExtendedBox l r,sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  rw [sourceFaceMeasure,integral_map (continuous_sourceFaceParameter i j).aemeasurable hF,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (sourceFaceWeight_pos i j x).le]

lemma integral_sourceFaceWeight_continuous {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in sourceExtendedBox l r,sourceFaceWeight i j x * F (sourceFaceParameter i j x))=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
  rw [integral_sourceExtendedBox (g:=fun x => sourceFaceWeight i j x * F (sourceFaceParameter i j x)) ((continuous_sourceFaceWeight i j).mul
    (hF.comp (continuous_sourceFaceParameter i j))) hlr]
  congr 1
  funext t
  congr 1
  funext a
  rw [←intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro b _
  simp only [sourceFaceWeight,sourceFaceParameter,sourceFaceAngles_torus,torusFaceTerm,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  ring

lemma continuous_sourceFaceIntegral {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) :
    Continuous (fun t => ∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a) := by
  apply continuous_parametric_unitInterval
  apply Continuous.mul
  · apply continuous_parametric_unitInterval
    unfold torusFaceTerm
    apply Continuous.mul
    · apply hF.comp
      apply continuous_fst.fst.prodMk
      apply continuous_pi
      intro k
      fin_cases k
      · exact (continuous_faceRayCircle 1 i).comp continuous_fst.snd
      · exact (continuous_faceRayCircle sourceRadialWidth j).comp continuous_snd
    · exact (continuous_faceRayDensity sourceRadialWidth j).comp continuous_snd
  · exact (continuous_faceRayDensity 1 i).comp continuous_snd

theorem sourceCylinderMeasure_eq_faces {l r : ℝ} (hlr : l ≤ r) :
    (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))=
      ∑ i : Fin 4,∑ j : Fin 4,sourceFaceMeasure l r i j := by
  have : ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  have hi : Integrable (fun z => F z)
      ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))) := F.integrable
  rw [integral_prod _ hi,←intervalIntegral.integral_of_le hlr]
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => F.integrable))]
  simp_rw [integral_finsetSum_measure (fun j _ => F.integrable)]
  have hh (i j : Fin 4) : (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
    rw [integral_sourceFaceMeasure (F:=fun z => F z) l r i j F.continuous.aestronglyMeasurable]
    exact integral_sourceFaceWeight_continuous F.continuous i j hlr
  simp_rw [hh]
  have he (t : ℝ) := integral_unitTorus_faces (w₀:=1) (w₁:=sourceRadialWidth)
    (F:=fun θ => F (t,θ)) (by norm_num) (by norm_num [sourceRadialWidth,sourceHole])
    (F.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun θ => F (t,θ)))
  simp only [volume_pi,unitCircle_volume_eq_haar] at he
  trans ∫ t in l..r,∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a
  · apply intervalIntegral.integral_congr
    intro t _
    exact he t
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j)).intervalIntegrable l r)]
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral.integral_finsetSum (fun j _ =>
    (continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j).intervalIntegrable l r)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.sourceFaceIntegralCircleMeasureSpace
local instance sourceFaceIntegralCircleIsProbabilityMeasure_r8ef6ae_1 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma sourceFaceMeasure_le_cylinder {l r : ℝ} (hlr : l ≤ r) (i j : Fin 4) :
    sourceFaceMeasure l r i j ≤
      (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [sourceCylinderMeasure_eq_faces hlr]
  exact le_trans (Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun face => ∑ patch,sourceFaceMeasure l r face patch)
      (fun _ _ => Measure.zero_le _) (Finset.mem_univ i))

lemma integrable_sourceFacePullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l ≤ r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) (i j : Fin 4) :
    IntegrableOn (fun x => sourceFaceWeight i j x • F (sourceFaceParameter i j x))
      (sourceExtendedBox l r) volume := by
  have hf := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  have hg := (integrable_map_measure hf.aestronglyMeasurable
    (continuous_sourceFaceParameter i j).aemeasurable).mp hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg
  simpa only [IntegrableOn,Function.comp_apply,ENNReal.toReal_ofReal (sourceFaceWeight_pos i j _).le] using hh

theorem integral_sourceCylinder_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l ≤ r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) :
    (∫ z,F z ∂(volume.restrict (Ioc l r)).prod volume)=
      ∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceExtendedBox l r,
        sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  have hf (i j : Fin 4) := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  rw [sourceCylinderMeasure_eq_faces hlr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hf i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hf _ j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_sourceFaceMeasure l r i j (hf i j).aestronglyMeasurable

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalEndSmoothEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.physicalEndSmoothEnergyMeasureSpace
local instance physicalEndSmoothEnergyIsProbabilityMeasure_r8ef6ae_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem fullAttachedEnd_smooth_energy_pullback (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a b l r R : ℝ} (ha : a≠0) (hlr : l ≤ r) (hR : 0≤R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    IntegrableOn (fun y => fullAttachedEndGradient s f a b κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)) (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a b κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      |a| *angularArea*(∫ z,sourceEndSmoothDensity s f κ a⁻¹ b φ
        (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume) := by
  let F := sourceEndSmoothDensity s f κ a⁻¹ b φ
  let G := fun y => fullAttachedEndGradient s f a b κ y ⬝ᵥ
    (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)
  have hF := (sourceEndSmoothDensity_cylinder s hs f κ a⁻¹ b R hR hφ).1
  have hg := integrable_affineEndCoordinates ha hT hF
  have he (i j : Fin 4) :
      (fun x => |(sourceCollarDerivative i j x).det| • G (sourceCollarPiece i j x))=ᵐ[
        volume.restrict (sourceExtendedBox l r)]
      (fun x => (|a| *angularArea)*(sourceFaceWeight i j x •
        F (affineEndCoordinates a b (sourceFaceParameter i j x)))) := by
    filter_upwards [sourceExtendedBox_open_ae hl hr,sourceExtendedBox_axial_strict_ae l r]
      with x hx hm
    dsimp only [G]
    rw [smul_eq_mul,sourceCollarDerivative_det,←sourceCollarJacobian_det,
      fullAttachedEnd_test_energy s hs f κ φ ha i j hx (ht (x 0) hm)]
    have hj := sourceAngularJet_attachedCovector hφ ha b i j hx
    change _=(|a| *angularArea)*(sourceFaceWeight i j x *
      (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (sourceAngularJet φ a⁻¹ b k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re))))
    rw [hj]
    unfold sourceFaceWeight
    ring
  have hi (i j : Fin 4) : IntegrableOn G
      (sourceCollarPiece i j '' sourceExtendedBox l r) volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_Icc
      (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
      (sourceExtendedBox_injOn i j hl hr) G).mpr
    exact ((integrable_sourceFacePullback hlr hg i j).const_mul (|a| *angularArea)).congr (he i j).symm
  have hG : IntegrableOn G (sourceClosedCollarBand l r) volume := by
    unfold IntegrableOn
    rw [sourceClosedCollarBand_measure_faces hl hr]
    exact integrable_finsetSum_measure.mpr (fun i _ =>
      integrable_finsetSum_measure.mpr fun j _ => hi i j)
  refine ⟨hG,?_⟩
  change (∫ y in sourceClosedCollarBand l r,G y)=_
  rw [integral_sourceClosedCollarBand_faces hl hr hG,
    integral_sourceCylinder_faces (F:=fun z => sourceEndSmoothDensity s f κ a⁻¹ b φ
      (affineEndCoordinates a b z)) hlr hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceExtended_integral i j hl hr G,integral_congr_ae (he i j),integral_const_mul]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CentralPhysicalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma centralPhysicalWholeCLM_ae (f : CentralL2) :
    centralPhysicalWholeCLM f=ᵐ[volume]
      (fun y => centralPhysical.indicator (fun y => f (sourcePairCoordinates y)) y) := by
  apply (Lp.coeFn_compMeasurePreserving _ sourcePair_volume).trans
  have he := sourcePair_volume.quasiMeasurePreserving.ae_eq_comp
    (lpZeroExtensionCLM_ae centralClosed_compact.measurableSet f)
  apply he.trans
  filter_upwards [] with y
  by_cases h : sourcePairCoordinates y∈centralClosed <;>
    simp [sourcePairMeasurable_apply,centralPhysical,h]
  rfl

lemma centralPhysicalWholeCLM_integral (f g : CentralL2) :
    IntegrableOn (fun y => centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y)
      centralPhysical volume ∧
    (∫ y in centralPhysical,centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y)=
      inner ℝ f g := by
  have hi := (Lp.memLp (centralPhysicalWholeCLM f)).integrable_mul
    (Lp.memLp (centralPhysicalWholeCLM g))
  refine ⟨hi.integrableOn,?_⟩
  rw [←centralPhysicalWholeLI.inner_map_map f g,L2.inner_def,
    ←integral_indicator centralPhysical_compact.measurableSet]
  apply integral_congr_ae
  filter_upwards [centralPhysicalWholeCLM_ae f,centralPhysicalWholeCLM_ae g] with y hf hg
  change centralPhysical.indicator
    (fun y => centralPhysicalWholeCLM f y*centralPhysicalWholeCLM g y) y=
      inner ℝ (centralPhysicalWholeCLM f y) (centralPhysicalWholeCLM g y)
  rw [Real.inner_apply]
  by_cases hy : y∈centralPhysical
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy,hf,hg,indicator_of_notMem hy,indicator_of_notMem hy]; ring

lemma H1JetOn.central_gradient {s : Fin 3 → ℝ} {p : centralEnergySpace s} {w : H1}
    (hw : H1JetOn w centralPhysical (centralFullJetCLM s p.val)) :
    ∀ᵐ y : Fin 3 → ℝ,y∈centralPhysical → originalPiGradient w y=
      (fun i : Fin 3 => centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y) := by
  apply originalPiGradient_eq_on_ball (fun _ => centralPhysical_subset_ball) w _
  filter_upwards [hw,physicalFourJetCLM_ae
    (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p.val))] with x hx he hy
  have h := (hx hy).trans he
  intro i
  exact congrArg (fun v : JetFiber => v i.succ) h

lemma central_physical_energy {s : Fin 3 → ℝ} (p q : centralEnergySpace s) (w v : H1)
    (hw : H1JetOn w centralPhysical (centralFullJetCLM s p.val))
    (hv : H1JetOn v centralPhysical (centralFullJetCLM s q.val)) :
    (∫ y in centralPhysical,originalPiGradient w y ⬝ᵥ originalPiGradient v y)=
      inner ℝ (centralD s p) (centralD s q) := by
  calc
    _ = ∫ y in centralPhysical,∑ i : Fin 3,
        centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y*
          centralPhysicalWholeCLM (centralAmbientComponent s i.succ q.val) y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hw.central_gradient,ae_restrict_of_ae hv.central_gradient,
        ae_restrict_mem centralPhysical_compact.measurableSet] with y hp hq hy
      rw [hp hy,hq hy]
      rfl
    _ = ∑ i : Fin 3,inner ℝ (centralAmbientComponent s i.succ p.val)
        (centralAmbientComponent s i.succ q.val) := by
      rw [integral_finsetSum (f:=fun i : Fin 3 => fun y =>
        centralPhysicalWholeCLM (centralAmbientComponent s i.succ p.val) y*
          centralPhysicalWholeCLM (centralAmbientComponent s i.succ q.val) y) Finset.univ (fun i _ =>
        (centralPhysicalWholeCLM_integral (centralAmbientComponent s i.succ p.val)
          (centralAmbientComponent s i.succ q.val)).1)]
      exact Finset.sum_congr rfl (fun i _ =>
        (centralPhysicalWholeCLM_integral (centralAmbientComponent s i.succ p.val)
          (centralAmbientComponent s i.succ q.val)).2)
    _ = _ := by rw [PiLp.inner_apply]; rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalOuterTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.instMeasureSpaceUnitAddCircle_solutions_9
attribute [local instance] OAI.ScalarConductivity.instIsProbabilityMeasureUnitAddCircleVolume_solutions_9
lemma smoothOuterFourierL_apply (i : Fin 3) (φ : SmoothScalar (Fin 3 → ℝ)) (h : TorusModes) :
    smoothOuterFourierL i φ h=mFourierCoeff (fun θ => (φ.val (physicalOuterBoundary i θ):ℂ)) h := by
  change (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (smoothOuterContinuousL i φ)) h=_
  rw [mFourierBasis_repr,mFourierCoeff_toLp]
  rfl

lemma physicalOuterTrace_smooth (i : Fin 3) {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (s : Fin 3 → ℝ) :
    physicalOuterTraceCLM i (piSmoothH1 hφ)=(physicalSmoothOuterTrace s hφ i).val 0 := by
  have he := (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose_spec ⟨φ,hφ⟩
  change physicalOuterTraceCLM i (piSmoothH1 hφ)=smoothOuterFourierL i ⟨φ,hφ⟩ at he
  rw [he]
  ext h
  rw [smoothOuterFourierL_apply]
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (smoothCollarTrace_fst s 0 hφ h).symm
  · exact (smoothCollarTrace_fst s 0 (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) h).symm

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalFiniteEndingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma end_length (i : Fin 3) : physicalEndLength z.compression i=(z.ending i).R+1 := by
  unfold physicalEndLength compression
  split_ifs <;>
    rw [abs_div,abs_of_pos (show 0 < centralThickness by norm_num [centralThickness])]
  · rw [abs_neg,abs_of_pos (by linarith [z.ending_R_pos i])]
    exact div_mul_cancel₀ _ (by norm_num [centralThickness])
  · rw [abs_of_pos (by linarith [z.ending_R_pos i])]
    exact div_mul_cancel₀ _ (by norm_num [centralThickness])

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_VariableBlockEnergy
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma variableBlockTensor_central_ae (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),y∈centralPhysical → variableBlockTensor K a y=1 := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy
  apply variableBlockTensorList_outside
  intro i _ hi
  have ht := (centralPhysical_time_iff y).mp hy
  have hn (k : Fin 2) : sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≠-centralThickness := by
    fin_cases k
    · exact hc₀
    · exact hc₁
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 0 (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hn 1 (le_antisymm (ht.2 1) hi.1)

attribute [local instance] OAI.ScalarConductivity.variableBlockEnergyMeasurableSpace
local instance variableBlockEnergyBorelSpace_r8ef6ae_1 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))
lemma variableBlockTensor_entry_memLp (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (i j : Fin 3) :
    MemLp (fun y => variableBlockTensor K a y i j) ∞
      (volume : Measure (Fin 3 → ℝ)) := by
  have h := variableBlockTensor_properties K a hK ha
  let heval : (Matrix (Fin 3) (Fin 3) ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj j) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      ((ContinuousLinearMap.proj i) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 3 → ℝ))
  exact heval.comp_memLp' h.2.1

theorem variableBlockTensor_weak_integrable (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y)) (volume.restrict D) := by
  have hrow (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3,
      variableBlockTensor K a y i j*originalPiGradient v y j) 2 (volume.restrict D) := by
    apply memLp_finsetSum
    intro j _
    exact (originalPiGradient_memLp_on_ball hD hb v j).mul (r := 2)
      ((variableBlockTensor_entry_memLp K a hK ha i j).restrict D)
  change Integrable (fun y => ∑ i : Fin 3,originalPiGradient u y i*
    ∑ j : Fin 3,variableBlockTensor K a y i j*originalPiGradient v y j) _
  apply integrable_finsetSum
  intro i _
  exact (originalPiGradient_memLp_on_ball hD hb u i).integrable_mul (hrow i)

lemma variableBlockTensor_end_energy (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3)
    {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D) (hsub : D⊆physicalEndRegion i)
    (u v : H1) :
    (∫ y in D,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y))=
    ∫ y in D,originalPiGradient u y ⬝ᵥ
      (variableEndTensor K a i y*ᵥoriginalPiGradient v y) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hD] with y hy
  rw [variableBlockTensor_local K a i (hsub hy)]

lemma variableBlockTensor_central_energy (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (u v : H1) :
    (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y))=
    ∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (variableBlockTensor_central_ae K a),
    ae_restrict_mem centralPhysical_compact.measurableSet] with y he hy
  rw [he hy,Matrix.one_mulVec]

theorem variableBlockTensor_energy_sum (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0 < c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (u v : H1) :
    Integrable (fun y => originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y)) (volume.restrict physicalBlockRegion) ∧
    (∫ y in physicalBlockRegion,originalPiGradient u y ⬝ᵥ
      (variableBlockTensor K a y*ᵥoriginalPiGradient v y))=
      (∫ y in centralPhysical,originalPiGradient u y ⬝ᵥ originalPiGradient v y)+
      ∑ i : Fin 3,∫ y in physicalEndRegion i,originalPiGradient u y ⬝ᵥ
        (variableEndTensor K a i y*ᵥoriginalPiGradient v y) := by
  refine ⟨variableBlockTensor_weak_integrable K a hK ha
    physicalBlockRegion_compact.measurableSet (fun _ => physicalBlockRegion_subset_ball) u v,?_⟩
  rw [physicalBlockRegion_integral _
    (variableBlockTensor_weak_integrable K a hK ha centralPhysical_compact.measurableSet
      (fun _ => centralPhysical_subset_ball) u v)
    (fun i => variableBlockTensor_weak_integrable K a hK ha
      (physicalEndRegion_compact i).measurableSet
        (fun _ => physicalEndRegion_subset_ball i) u v),
    variableBlockTensor_central_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact variableBlockTensor_end_energy K a i (physicalEndRegion_compact i).measurableSet
    Subset.rfl u v

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralAffineCovector
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusRealContinuation_spectral_eventually {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f)=ᶠ[𝓝 x]
      (fun y => (endFlatPoisson s f y).re) := by
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  rw [torusRealContinuation_spectral hs f hy,endFlatPoisson_eq]

lemma torusAffineField_spectral_covector {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) {x : Coord3} (hx : 0<x 0) :
    (fun k => fderiv ℝ (torusAffineField s κ (torusSpectralSynthesis s f)) x (Pi.single k 1))=
      fullEndFlatCovector s f κ (x 0) (torusAngles x) := by
  have he := torusRealContinuation_spectral_eventually hs f hx
  have hd := ((torusRealContinuation_smooth hs (torusSpectralSynthesis s f)).contDiffAt
    ((axial_halfspace_open 0).mem_nhds hx)).differentiableAt (by norm_num)
  have ha := ((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).const_mul κ)
  ext k
  change fderiv ℝ ((fun y : Coord3 => κ*y 0)+torusRealContinuation s (torusSpectralSynthesis s f)) x
    (Pi.single k 1)=(endPoissonField s f k.succ (x 0,torusAngles x)).re+κ*(Pi.single (0:Fin 3) (1:ℝ) : Coord3) k
  rw [(ha.add hd.hasFDerivAt).fderiv]
  change κ*(Pi.single k (1:ℝ) : Coord3) 0+fderiv ℝ (torusRealContinuation s (torusSpectralSynthesis s f)) x (Pi.single k 1)=_
  rw [he.fderiv_eq,endFlatPoisson_real_derivative_axis s hs f hx k]
  fin_cases k <;> simp
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FluxCylinder
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.sourceFluxCylinderMeasureSpace
local instance sourceFluxCylinderIsProbabilityMeasure_r8ef6ae_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma torusSpectralSynthesis_smoothCollar_ae (s : Fin 3 → ℝ) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    torusSpectralSynthesis s (smoothCollarTrace s b hφ)=ᵐ[volume]
      fun θ => (φ (sourceAngularCollar b θ):ℂ) := by
  have he : (smoothCollarTrace s b hφ).val 0=smoothCollarTraceFourier b hφ := by
    apply lp.ext
    funext h
    rw [smoothCollarTrace_fst,smoothCollarTraceFourier_apply]
  change (mFourierBasis (d:=Fin 2)).repr.symm ((smoothCollarTrace s b hφ).val 0)=ᵐ[volume] _
  rw [he,smoothCollarTraceFourier,LinearIsometryEquiv.symm_apply_apply]
  exact ContinuousMap.coeFn_toLp volume _

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SpectralTerminalIntegral
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.spectralTerminalIntegralMeasureSpace
local instance spectralTerminalIntegralIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma spectralTerminalDensity_coeff (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f : spectralTraceGraph (torusRate s)) (h : TorusModes) :
    spectralTerminalDensity s hR f h=
      (torusRate s h:ℂ)*(Real.exp (-torusRate s h*R):ℂ)*f.val 0 h := by
  change ((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ)*f.val 1 h=_
  rw [f.property h]
  have he : (Real.sqrt (torusRate s h):ℂ)^2=(torusRate s h:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Real.sqrt_nonneg _)
  simp only [Complex.ofReal_mul]
  calc
    _ = (Real.sqrt (torusRate s h):ℂ)^2*(Real.exp (-torusRate s h*R):ℂ)*f.val 0 h := by ring
    _ = _ := by rw [he]

lemma spectralTerminalDensity_synthesis_ae {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) :
    (mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)=ᵐ[volume]
      fun θ => -endPoissonField s f 1 (R,θ) := by
  let u := (mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)
  have hc (h : TorusModes) : mFourierCoeff u h=spectralTerminalDensity s hR f h := by
    rw [←mFourierBasis_repr]
    change (mFourierBasis (d:=Fin 2)).repr ((mFourierBasis (d:=Fin 2)).repr.symm _) h=_
    rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp_hasSum_ae_unique (hasSum_mFourier_series_L2 u)
    (a:=fun h θ => -endPoissonModeField s h (f.val 0 h) 1 (R,θ))
  · intro h
    filter_upwards [Lp.coeFn_smul (mFourierCoeff u h) (mFourierLp 2 h),coeFn_mFourierLp 2 h]
      with θ h1 h2
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul,h2,hc,spectralTerminalDensity_coeff]
    simp [endPoissonModeField,endModeCoefficient,mul_assoc,mul_left_comm,mul_comm]
  · exact Filter.Eventually.of_forall (fun θ => (endPoissonField_hasSum s hs f 1 hR).neg)

lemma smoothCollarTrace_mean_integral (s : Fin 3 → ℝ) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    spectralGraphMean (torusRate s) (smoothCollarTrace s b hφ)=
      ∫ θ,φ (sourceAngularCollar b θ) := by
  change ((smoothCollarTrace s b hφ).val 0 0).re=_
  rw [smoothCollarTrace_fst]
  simp only [mFourierCoeff,neg_zero,mFourier_zero,ContinuousMap.one_apply,one_smul]
  have hc : Continuous (fun θ => (φ (sourceAngularCollar b θ):ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_sourceAngularCollar b))
  simpa using (Complex.reCLM.integral_comp_comm
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

lemma spectralTerminalDensity_smooth_pair {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (fun θ => (endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ)) ∧
    (∫ θ,(endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ))=
      -(spectralWeightedPairL s (spectralEndWeight s R f) (smoothCollarTrace s b hφ)).re := by
  let u := (mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)
  let v := torusSpectralSynthesis s (smoothCollarTrace s b hφ)
  have hi := L2.integrable_inner (𝕜:=ℂ) u v
  have he : (fun θ => -(inner ℂ (u θ) (v θ)).re)=ᵐ[volume]
      (fun θ => (endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ)) := by
    filter_upwards [spectralTerminalDensity_synthesis_ae hs hR f,
      torusSpectralSynthesis_smoothCollar_ae s b hφ] with θ hu hv
    change -(inner ℂ (((mFourierBasis (d:=Fin 2)).repr.symm (spectralTerminalDensity s hR f)) θ)
      (torusSpectralSynthesis s (smoothCollarTrace s b hφ) θ)).re=_
    rw [hu,hv]
    simp [RCLike.inner_apply,Complex.mul_re,mul_comm]
  refine ⟨hi.re.neg.congr he,?_⟩
  rw [←integral_congr_ae he,integral_neg]
  have hinner : inner ℂ u v=inner ℂ (spectralTerminalDensity s hR f)
      ((smoothCollarTrace s b hφ).val 0) :=
    (mFourierBasis (d:=Fin 2)).repr.symm.inner_map_map _ _
  rw [←spectralTerminalDensity_pair s hR f (smoothCollarTrace s b hφ),←hinner,L2.inner_def]
  congr 1
  exact Complex.reCLM.integral_comp_comm hi

lemma fullEndFlatCovector_terminal_integral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {R : ℝ} (hR : 0<R) (f : spectralTraceGraph (torusRate s)) (κ b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (fun θ => fullEndFlatCovector s f κ R θ 0*φ (sourceAngularCollar b θ)) ∧
    (∫ θ,fullEndFlatCovector s f κ R θ 0*φ (sourceAngularCollar b θ))=
      cylinderTerminalFlux s κ R f (smoothCollarTrace s b hφ) := by
  obtain ⟨hi,he⟩ := spectralTerminalDensity_smooth_pair hs hR f b hφ
  have hq : Integrable (fun θ => φ (sourceAngularCollar b θ)) :=
    (hφ.continuous.comp (continuous_sourceAngularCollar b)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hp : (fun θ => fullEndFlatCovector s f κ R θ 0*φ (sourceAngularCollar b θ))=
      (fun θ => (endPoissonField s f 1 (R,θ)).re*φ (sourceAngularCollar b θ)+
        κ*φ (sourceAngularCollar b θ)) := by
    funext θ
    simp [fullEndFlatCovector,add_mul]
  rw [hp]
  refine ⟨hi.add (hq.const_mul κ),?_⟩
  rw [integral_add hi (hq.const_mul κ),integral_const_mul,he,cylinderTerminalFlux,
    smoothCollarTrace_mean_integral]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_BranchTerminalFluxIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.branchTerminalFluxIntegralMeasureSpace
local instance branchTerminalFluxIntegralProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusAffineField_flux_normal {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) {R : ℝ} (hR : 0<R)
    (θ : UnitAddTorus (Fin 2)) :
    torusPeriodicDescent (flatModeFlux s (torusAffineField s κ (torusSpectralSynthesis s f))) (R,θ) 0=
      fullEndFlatCovector s f κ R θ 0 := by
  let x : Coord3 := ![R,2*Real.pi*torusRealRepresentative θ 0,2*Real.pi*torusRealRepresentative θ 1]
  have hx : 0<x 0 := hR
  change flatModeFlux s (torusAffineField s κ (torusSpectralSynthesis s f)) x 0=_
  rw [flatModeFlux_tensor,torusAffineField_spectral_covector hs f κ hx]
  have ha : torusAngles x=θ := (torusAngles_scaled R (torusRealRepresentative θ)).trans
    (torusRealProjection_representative θ)
  rw [ha]
  simp [flatBackgroundTensor,Matrix.mulVec,dotProduct,Fin.sum_univ_three,x]

lemma branchFluxCorrection_initial_integral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {f : Fin 2 → TorusL2} (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    (j : Fin 2) (b : ℝ) (φ : Coord3 → ℝ) :
    (∫ θ,torusPeriodicDescent (branchFluxCorrection i z j) (0,θ) 0*φ (sourceAngularCollar b θ))=0 := by
  have he (θ : UnitAddTorus (Fin 2)) : torusPeriodicDescent (branchFluxCorrection i z j) (0,θ)=0 :=
    branchFluxCorrection_zero i z hs j _ rfl
  simp only [he,Pi.zero_apply,zero_mul,integral_zero]

lemma branchFluxCorrection_terminal_integral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) {R : ℝ} (hR : 0<R) (hz : z.R<R) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ θ,torusPeriodicDescent (branchFluxCorrection i z j) (R,θ) 0*φ (sourceAngularCollar b θ))=
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s b hφ)-
        cylinderTerminalFlux s (centralBasisSlopes j i) R (f j) (smoothCollarTrace s b hφ) := by
  have he (θ : UnitAddTorus (Fin 2)) : torusPeriodicDescent (branchFluxCorrection i z j) (R,θ) 0=
      centralBasisSlopes j i-fullEndFlatCovector s (f j) (centralBasisSlopes j i) R θ 0 := by
    change branchFluxCorrection i z j ![R,2*Real.pi*torusRealRepresentative θ 0,
      2*Real.pi*torusRealRepresentative θ 1] 0=_
    rw [branchFluxCorrection_terminal i z j _ hz]
    change centralBasisSlopes j i*(Pi.single (0:Fin 3) (1:ℝ) : Coord3) 0-
      torusPeriodicDescent (flatModeFlux s (torusAffineField s (centralBasisSlopes j i)
        (torusSpectralSynthesis s (f j)))) (R,θ) 0=_
    rw [Pi.single_eq_same,mul_one,torusAffineField_flux_normal hs (f j) _ hR]
  simp_rw [he,sub_mul]
  have hq : Integrable (fun θ => φ (sourceAngularCollar b θ)) :=
    (hφ.continuous.comp (continuous_sourceAngularCollar b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hi,hI⟩ := fullEndFlatCovector_terminal_integral hs hR (f j) (centralBasisSlopes j i) b hφ
  rw [integral_sub (hq.const_mul _) hi,integral_const_mul,hI,smoothCollarTrace_mean_integral]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_AttachedSplicedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal

local instance attachedSplicedGreenMeasureSpace_r8ef6ae_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {s : Fin 3 → ℝ} (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))

lemma splicedAttached_smooth_green_pos
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : 0<a) (hlr : l < r) (hR : a*(r-l)=R) (hz : z.R<R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    IntegrableOn (fun y => splicedAttachedGradient f i z j a l y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a l y*ᵥphysicalTestCovector φ y))
        (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,splicedAttachedGradient f i z j a l y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a l y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (f j))
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s l hφ))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s l hφ)+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos ha (sub_pos.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a l t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg ha.le (sub_nonneg.mpr ht.1)
    · rw [←hR]; exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) ha.le
  have ht : ∀ t∈Ioo l r,0<a*(t-l) := fun t ht => mul_pos ha (sub_pos.mpr ht.1)
  have hO := (fullAttachedEnd_smooth_energy_pullback s hs (f j) (centralBasisSlopes j i) hφ
    ha.ne' hlr.le hRp.le hl hr hT ht).1
  obtain ⟨hC,hCI⟩ := attachedPeriodicFlux_smooth_green (branchFluxCorrection_C1 i z hs j)
    (branchFluxCorrection_periodic i z j) hφ ha.ne' hlr.le hRp.le hl hr hT
    (Or.inl ⟨ha,by ring,hR⟩) (fun x _ => branchFluxCorrection_divergence i z hs j x)
  have he := splicedAttached_energy_ae f i z hs j φ ha.ne' hl hr ht
  refine ⟨(hO.add hC).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hO hC,
    fullAttachedEnd_smooth_green_pos s hs (f j) (centralBasisSlopes j i) hφ ha hlr hR hl hr,hCI,
    branchFluxCorrection_initial_integral hs i z j,
    branchFluxCorrection_terminal_integral hs f i z j hRp hz _ hφ]
  have hend : a⁻¹*R+l=r := by rw [←hR]; field_simp [ha.ne']; ring
  rw [hend]
  ring

lemma splicedAttached_smooth_green_neg
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : a<0) (hlr : l < r) (hR : a*(l-r)=R) (hz : z.R<R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    IntegrableOn (fun y => splicedAttachedGradient f i z j a r y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a r y*ᵥphysicalTestCovector φ y))
        (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,splicedAttachedGradient f i z j a r y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a r y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (f j))
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s r hφ))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s l hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos_of_neg_of_neg ha (sub_neg.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a r t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr ht.2)
    · rw [←hR]; exact mul_le_mul_of_nonpos_left (sub_le_sub_right ht.1 r) ha.le
  have ht : ∀ t∈Ioo l r,0<a*(t-r) := fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr ht.2)
  have hO := (fullAttachedEnd_smooth_energy_pullback s hs (f j) (centralBasisSlopes j i) hφ
    ha.ne hlr.le hRp.le hl hr hT ht).1
  obtain ⟨hC,hCI⟩ := attachedPeriodicFlux_smooth_green (branchFluxCorrection_C1 i z hs j)
    (branchFluxCorrection_periodic i z j) hφ ha.ne hlr.le hRp.le hl hr hT
    (Or.inr ⟨ha,hR,by ring⟩) (fun x _ => branchFluxCorrection_divergence i z hs j x)
  have he := splicedAttached_energy_ae f i z hs j φ ha.ne hl hr ht
  refine ⟨(hO.add hC).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hO hC,
    fullAttachedEnd_smooth_green_neg s hs (f j) (centralBasisSlopes j i) hφ ha hlr hR hl hr,hCI,
    branchFluxCorrection_initial_integral hs i z j,
    branchFluxCorrection_terminal_integral hs f i z j hRp hz _ hφ]
  have hend : a⁻¹*R+r=l := by rw [←hR]; field_simp [ha.ne]; ring
  rw [hend]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_PhysicalSplicedGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma correctedEndJet_parent (j : Fin 2) (y : Coord3) :
    (fun k : Fin 3 => z.correctedEndJet j 0 (WithLp.toLp 2 y) k.succ)=
      splicedAttachedGradient (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) j
        (z.compression 0) centralThickness y := by
  ext k
  rfl

lemma correctedEndJet_child (j : Fin 2) (n : Fin 2) (y : Coord3) :
    (fun k : Fin 3 => z.correctedEndJet j n.succ (WithLp.toLp 2 y) k.succ)=
      fun k => sourceScale⁻¹*splicedAttachedGradient (fun j => centralT s n.succ (z.p j))
        n.succ (z.ending n.succ) j (z.compression n.succ) (-centralThickness)
        ((sourceChildHomeomorph (actualChildSign n)).symm y) (childAxis k) := by
  ext k
  dsimp [correctedEndJet,attachedPhysicalJet,periodicCorrectionJet,physicalJet,splicedAttachedGradient]
  ring

lemma corrected_child_energy_pullback (j : Fin 2)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,
      (fun n : Fin 3 => z.correctedEndJet j k.succ (WithLp.toLp 2 y) n.succ) ⬝ᵥ
        (variableEndTensor z.flatTensor z.compression k.succ y*ᵥphysicalTestCovector φ y))=
      ∫ y in sourceClosedCollarBand (-centralThickness) 0,
        splicedAttachedGradient (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) j
          (z.compression k.succ) (-centralThickness) y ⬝ᵥ
          (variableCollarTensor (z.flatTensor k.succ) (z.compression k.succ) (-centralThickness) y*ᵥ
            physicalTestCovector (φ ∘ sourceChildCoordinates (actualChildSign k)) y) := by
  have hreg : physicalEndRegion k.succ=sourceChildCoordinates (actualChildSign k) ''
      sourceClosedCollarBand (-centralThickness) 0 := by
    change (sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' _=_
    ext y
    constructor
    · intro hy
      exact ⟨(sourceChildHomeomorph (actualChildSign k)).symm y,hy,
        (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      change (sourceChildHomeomorph (actualChildSign k)).symm
        ((sourceChildHomeomorph (actualChildSign k)) x)∈sourceClosedCollarBand (-centralThickness) 0
      simpa only [Homeomorph.symm_apply_apply] using hx
  conv_lhs => rw [hreg]
  conv_lhs => rw [sourceChild_integral (actualChildSign k) childEndBand_measurable]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [z.correctedEndJet_child]
  have hv : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  rw [hv]
  change sourceScale^3*((fun n => sourceScale⁻¹*splicedAttachedGradient _ _ _ _ _ _ y (childAxis n)) ⬝ᵥ
    (sourceChildTensorPush k _ (sourceChildCoordinates (actualChildSign k) y)*ᵥ
      physicalTestCovector φ (sourceChildCoordinates (actualChildSign k) y)))=_
  rw [sourceChildTensorPush_mixed,physicalTestCovector_child hφ]

lemma corrected_parent_jet_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalEndRegion 0,(fun k : Fin 3 => z.correctedEndJet j 0 (WithLp.toLp 2 y) k.succ) ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression 0 y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s 0 (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j 0*spectralGraphMean (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ))+
      centralBasisSlopes j 0*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ 0)) := by
  simp_rw [z.correctedEndJet_parent]
  change (∫ y in sourceClosedCollarBand 0 centralThickness,splicedAttachedGradient _ _ _ _ _ _ _ ⬝ᵥ
    (variableCollarTensor _ _ _ _*ᵥphysicalTestCovector φ y))=_
  dsimp only [flatTensor]
  rw [(splicedAttached_smooth_green_neg (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) hs j hφ
    (l:=0) (r:=centralThickness) z.compression_parent (by norm_num [centralThickness]) (R:=physicalEndLength z.compression 0)
    (by dsimp [physicalEndLength]; rw [abs_of_neg z.compression_parent]; ring)
    (by rw [z.end_length]; linarith)
    (by norm_num) (by norm_num [centralThickness])).2,physicalSmoothCentral_parent_trace s hφ]
  rfl

lemma corrected_child_jet_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,(fun n : Fin 3 => z.correctedEndJet j k.succ (WithLp.toLp 2 y) n.succ) ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression k.succ y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s k.succ (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j k.succ*spectralGraphMean (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ))+
      centralBasisSlopes j k.succ*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ k.succ)) := by
  rw [z.corrected_child_energy_pullback j hφ k]
  dsimp only [flatTensor]
  rw [(splicedAttached_smooth_green_pos (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) hs j
    (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k)))
    (l:= -centralThickness) (r:=0) (z.compression_child k) (by norm_num [centralThickness]) (R:=physicalEndLength z.compression k.succ)
    (by dsimp [physicalEndLength]; rw [abs_of_pos (z.compression_child k)]; ring)
    (by rw [z.end_length]; linarith)
    (by norm_num [centralThickness]) (by norm_num)).2,physicalSmoothCentral_child_trace s hφ k]
  rfl

lemma corrected_jet_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,(fun n : Fin 3 => z.correctedEndJet j i (WithLp.toLp 2 y) n.succ) ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression i y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i)) :=
  Fin.cases (z.corrected_parent_jet_green hs j hφ) (fun k => z.corrected_child_jet_green hs j hφ k) i

end PhysicalFiniteEndingData
end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma constantTerminalFlux_smooth (s κ : Fin 3 → ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    constantTerminalFluxCLM κ (piSmoothH1 hφ)=angularArea*∑ i : Fin 3,
      κ i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i) := by
  simp only [constantTerminalFluxCLM,_root_.smul_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalOuterTrace_smooth i hφ s]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma corrected_gradient (j : Fin 2) (i : Fin 3) {w : H1}
    (hw : H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i)) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → originalPiGradient w y=
      (fun k => z.correctedEndJet j i (WithLp.toLp 2 y) k.succ) := by
  apply originalPiGradient_eq_on_ball (fun _ => physicalEndRegion_subset_ball i) w _
  filter_upwards [hw] with x hx hy k
  exact congrArg (fun v : JetFiber => v k.succ) (hx hy)

lemma corrected_end_smooth_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {w : H1} (hw : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i))
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i)) := by
  have he : (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      ∫ y in physicalEndRegion i,(fun n => z.correctedEndJet j i (WithLp.toLp 2 y) n.succ) ⬝ᵥ
        (variableEndTensor z.flatTensor z.compression i y*ᵥphysicalTestCovector φ y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (z.corrected_gradient j i (hw i)),
      ae_restrict_of_ae (piSmoothH1_gradient hφ (fun _ => physicalEndRegion_subset_ball i)),
      ae_restrict_mem (physicalEndRegion_compact i).measurableSet] with y hw hv hy
    rw [hw hy,hv hy]
  exact he.trans (z.corrected_jet_green hs j hφ i)

lemma corrected_block_smooth_green_oai
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i))
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      constantTerminalFluxCLM (centralBasisSlopes j) (piSmoothH1 hφ) := by
  rw [(variableBlockTensor_energy_sum z.flatTensor z.compression (z.flatTensor_properties hs)
    z.compression_ne w (piSmoothH1 hφ)).2,
    central_physical_energy (z.p j) (physicalSmoothCentral s hφ) w (piSmoothH1 hφ) hwc
      (physicalSmoothCentral_jet s hφ),constantTerminalFlux_smooth s]
  simp_rw [z.corrected_end_smooth_green hs j hwe hφ]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hv := z.variational j (physicalSmoothCentral s hφ)
  nlinarith

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green_oai := @OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green_oai
