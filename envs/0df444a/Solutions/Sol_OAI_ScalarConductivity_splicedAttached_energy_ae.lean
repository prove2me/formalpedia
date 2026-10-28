-- Prove2me | solution 1 for OAI.ScalarConductivity.splicedAttached_energy_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:26:05.691415+00:00
-- url     : https://prove2.me/submissions/86b7f668-1434-489b-b3d0-ad2fbfd0bf1e

import Mathlib
import Definitions.Def_OAIQ059C008

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
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CentralCylinderGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma flatCylinderMatrix_symmetric (s : Fin 3 → ℝ) :
    (flatCylinderMatrix s)ᵀ=flatCylinderMatrix s := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

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

lemma attachedFlatTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (x : Fin 3 → ℝ) : (attachedFlatTensor s a i j x)ᵀ=attachedFlatTensor s a i j x := by
  simp only [attachedFlatTensor,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose,flatCylinderMatrix_symmetric,Matrix.mul_assoc]

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
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AttachedFlatTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedPhysicalFlatTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) :
    (attachedPhysicalFlatTensor s a i j y)ᵀ=attachedPhysicalFlatTensor s a i j y :=
  attachedFlatTensor_symmetric s a i j _

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

lemma attachedPatchTensor_symmetric (s : Fin 3 → ℝ) (a : ℝ) (i j : Fin 4)
    (y : Fin 3 → ℝ) : (attachedPatchTensor s a i j y)ᵀ=attachedPatchTensor s a i j y := by
  classical
  unfold attachedPatchTensor
  split_ifs
  · exact attachedPhysicalFlatTensor_symmetric s a i j y
  · exact Matrix.transpose_one

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma attachedFaceTensorList_cons (s : Fin 3 → ℝ) (a : ℝ)
    (k : Fin 4 × Fin 4) (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ) :
    attachedFaceTensorList s a (k::ks) y=
      (by classical exact if y∈sourceFlatPatch k.1 k.2 then attachedPatchTensor s a k.1 k.2 y
        else attachedFaceTensorList s a ks y) := by
  classical
  rfl

lemma attachedFaceTensorList_symmetric (s : Fin 3 → ℝ) (a : ℝ)
    (ks : List (Fin 4 × Fin 4)) (y : Fin 3 → ℝ) :
    (attachedFaceTensorList s a ks y)ᵀ=attachedFaceTensorList s a ks y := by
  classical
  induction ks with
  | nil => exact Matrix.transpose_one
  | cons k ks ih =>
    simp only [attachedFaceTensorList_cons]
    split_ifs
    · exact attachedPatchTensor_symmetric s a k.1 k.2 y
    · exact ih

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

lemma faceRayDensity_pos' {w : ℝ} (hw : 0<w) (j : Fin 4) (b : ℝ) :
    0<faceRayDensity w j b := by
  fin_cases j <;> dsimp [faceRayDensity] <;> positivity

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

lemma torusEndingCorrection_C2 {d e : ℝ} (he : 0<e) {v f : Coord3 → ℝ}
    (hv : ContDiff ℝ 2 v) (hf : ContDiffOn ℝ 2 f {x | d<x 0})
    (hz : ∀ x,x 0∈Ioo d (d+e) → v x=f x) :
    ContDiff ℝ 2 (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_contDiff (by linarith : 0<e/2)
  · exact (hv.contDiffOn.sub hf).mono (fun x hx => by dsimp at hx ⊢; linarith)
  · intro x hx
    change v x-f x=0
    exact sub_eq_zero.mpr (hz x ⟨by linarith [hx.1],by linarith [hx.2]⟩)

lemma torusEndingCorrection_periodic {T d e : ℝ} {v f : Coord3 → ℝ}
    (hv : AngularPeriodic T v) (hf : AngularPeriodic T f) :
    AngularPeriodic T (torusEndingCorrection d e v f) := by
  apply axialZeroExtension_periodic
  intro n x
  change v (x+angularShift T n)-f (x+angularShift T n)=v x-f x
  rw [hv n x,hf n x]

lemma torusEndingFluxCorrection_initial_zero {d e : ℝ} (he : 0<e)
    {G F : Coord3 → Coord3} (hz : ∀ x,x 0∈Ioo d (d+e) → G x=F x)
    {x : Coord3} (hx : x 0<d+3*e/4) :
    torusEndingFluxCorrection d e G F=ᶠ[𝓝 x] (fun _ => 0) := by
  apply axialZeroExtension_eventually_zero (by linarith : 0<e/2) _ (by linarith)
  intro y hy
  change G y-F y=0
  exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)

lemma torusEndingCorrection_initial_zero {d e : ℝ} (he : 0<e)
    {v f : Coord3 → ℝ} (hz : ∀ x,x 0∈Ioo d (d+e) → v x=f x)
    {x : Coord3} (hx : x 0<d+3*e/4) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (fun _ => 0) := by
  apply axialZeroExtension_eventually_zero (by linarith : 0<e/2) _ (by linarith)
  intro y hy
  change v y-f y=0
  exact sub_eq_zero.mpr (hz y ⟨by linarith [hy.1],by linarith [hy.2]⟩)

lemma torusEndingCorrection_terminal {d e : ℝ} {v f : Coord3 → ℝ}
    {x : Coord3} (hx : d+e/2<x 0) :
    torusEndingCorrection d e v f=ᶠ[𝓝 x] (v-f) :=
  axialZeroExtension_eventually_self (by linarith)

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
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FiniteEndPhysicalDescent
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma sourceRealFlat_angles (y : Coord3) :
    torusAngles (sourceRealFlat y)=sourcePhysicalAngles y := by
  ext i
  fin_cases i <;> rfl

lemma physicalPeriodicField_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    physicalPeriodicField f (sourceCollarPiece i j x)=f (sourceFaceAngles i j x) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb]
  apply hp.eq_of_angles
  · exact sourceAngular_time ht _
  · rw [sourceRealFlat_angles]
    exact congrArg Prod.snd (sourcePhysicalCoordinates_angular ht _)

lemma physicalPeriodicField_piece_local_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) :
    physicalPeriodicField f =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => f (sourceFaceAngles i j (sourceCollarInverse i j y))) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),physicalPeriodicField f y=
    f (sourceFaceAngles i j (sourceCollarInverse i j y))
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi]
  exact physicalPeriodicField_piece hp i j (sourceCollarOpenBox_subset hy)

theorem physicalPeriodicField_hasFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    HasFDerivAt (physicalPeriodicField f)
      ((fderiv ℝ f (sourceFaceAngles i j x)).comp
        (((Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap).comp
          (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap))
      (sourceCollarPiece i j x) := by
  have h1 := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt
  have he := sourceCollarInverse_point i j hx
  have h2 : HasFDerivAt (sourceFaceAngles i j)
      (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap
      (sourceCollarInverse i j (sourceCollarPiece i j x)) := by
    simpa only [he] using sourceFaceAngles_hasFDeriv i j x
  have h3 : HasFDerivAt f (fderiv ℝ f (sourceFaceAngles i j x))
      (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x))) := by
    simpa only [he] using (hf (sourceFaceAngles i j x)).hasFDerivAt
  have hh := h2.comp (sourceCollarPiece i j x) h1
  exact (h3.comp (sourceCollarPiece i j x) hh).congr_of_eventuallyEq
    (physicalPeriodicField_piece_local_eq hp i j hx)

theorem physicalPeriodicField_fderiv {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (v : Coord3) :
    fderiv ℝ (physicalPeriodicField f) (sourceCollarPiece i j x) v =
      (sourceCartesianGradientMatrix i j x *ᵥ
        (fun k => direction (Pi.single k 1) f (sourceFaceAngles i j x))) ⬝ᵥ v := by
  let T := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  let r : Coord3 := fun k => direction (Pi.single k 1) f (sourceFaceAngles i j x)
  let w := T.symm v
  have hw : sourceCollarJacobian i j x *ᵥ w=v := T.apply_symm_apply v
  have hd : (sourceFaceAngleMatrix i j x)ᵀ=sourceFaceAngleMatrix i j x :=
    Matrix.diagonal_transpose _
  calc
    _ = fderiv ℝ f (sourceFaceAngles i j x) (sourceFaceAngleMatrix i j x *ᵥ w) :=
      congrArg (fun L : Coord3 →L[ℝ] ℝ => L v) (physicalPeriodicField_hasFDeriv hp hf i j hx).fderiv
    _ = r ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ w) := realCLM_apply_basis _ _
    _ = w ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ r) := by
      rw [←Matrix.dotProduct_transpose_mulVec,hd]
    _ = w ⬝ᵥ ((sourceCollarJacobian i j x)ᵀ *ᵥ
        (sourceCartesianGradientMatrix i j x *ᵥ r)) := by
      rw [sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    _ = (sourceCartesianGradientMatrix i j x *ᵥ r) ⬝ᵥ
        (sourceCollarJacobian i j x *ᵥ w) := Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by rw [hw]

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

lemma branchCorrection_C2
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 2 (branchCorrection i z j) := by
  exact torusEndingCorrection_C2 z.e_pos (contDiff_pi.mp (branchFinitePair i z).smooth j)
    (((torusAffineField_smooth hs _ _).of_le
      (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => congrFun (branchFinitePair_initial hs i z x hx) j)

lemma branchCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchCorrection i z j) := by
  exact torusEndingCorrection_periodic
    (fun n x => congrFun (branchFinitePair_periodic_v i z n x) j)
    (torusAffineField_periodic _ _ _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FlatEndingSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchSplicedField_initial
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {x : Coord3} (hx : x 0<z.d+3*z.e/4) :
    branchSplicedField i z j=ᶠ[𝓝 x] torusAffineField s (centralBasisSlopes j i) (f j) := by
  filter_upwards [torusEndingCorrection_initial_zero z.e_pos
    (fun y hy => congrFun (branchFinitePair_initial hs i z y hy) j) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy,add_zero]

lemma branchSplicedFlux_initial
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {x : Coord3} (hx : x 0<z.d+3*z.e/4) :
    branchSplicedFlux i z j=ᶠ[𝓝 x]
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) := by
  filter_upwards [torusEndingFluxCorrection_initial_zero z.e_pos
    (fun y hy => branchFinitePair_initial_flux i z hs j y hy) hx] with y hy
  change _+torusEndingFluxCorrection _ _ _ _ y=_
  rw [hy,add_zero]

lemma branchSplicedField_final (j : Fin 2) {x : Coord3} (hx : z.d+z.e/2<x 0) :
    branchSplicedField i z j=ᶠ[𝓝 x] (fun y => (branchFinitePair i z).v y j) := by
  filter_upwards [torusEndingCorrection_terminal
    (v:=fun y => (branchFinitePair i z).v y j)
    (f:=torusAffineField s (centralBasisSlopes j i) (f j)) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy]
  change torusAffineField s (centralBasisSlopes j i) (f j) y+
    ((branchFinitePair i z).v y j-torusAffineField s (centralBasisSlopes j i) (f j) y)=_
  ring

lemma branchSplicedFlux_final (j : Fin 2) {x : Coord3} (hx : z.d+z.e/2<x 0) :
    branchSplicedFlux i z j=ᶠ[𝓝 x] (fun y => ((branchFinitePair i z).G y).col j) := by
  filter_upwards [torusEndingFluxCorrection_terminal
    (G:=fun y => ((branchFinitePair i z).G y).col j)
    (F:=flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j))) hx] with y hy
  change _+torusEndingFluxCorrection _ _ _ _ y=_
  rw [hy]
  change flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) y+
    (((branchFinitePair i z).G y).col j-flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) y)=_
  abel

lemma branchSpliced_constitution
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (j : Fin 2) :
    ∀ᵐ x : Coord3,branchSplicedTensor i z x*ᵥ
      (fun k => fderiv ℝ (branchSplicedField i z j) x (Pi.single k 1))=
        branchSplicedFlux i z j x := by
  filter_upwards [(branchFinitePair i z).constitution] with x hx
  by_cases ht : x 0<z.d+5*z.e/8
  · have ht' : x 0<z.d+3*z.e/4 := by linarith [z.e_pos]
    rw [branchSplicedTensor,ite_eq_left ht,
      (branchSplicedField_initial i z hs j ht').fderiv_eq,
      (branchSplicedFlux_initial i z hs j ht').eq_of_nhds,flatModeFlux_tensor]
  · have ht' : z.d+z.e/2<x 0 := by linarith [z.e_pos,not_lt.mp ht]
    rw [branchSplicedTensor,ite_eq_right ht,
      (branchSplicedField_final i z j ht').fderiv_eq,
      (branchSplicedFlux_final i z j ht').eq_of_nhds]
    have hj := congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j) hx
    change _*ᵥ((gradientColumns (fderiv ℝ (branchFinitePair i z).v x)).col j)=_ at hj
    have he : (gradientColumns (fderiv ℝ (branchFinitePair i z).v x)).col j=
        (fun k => fderiv ℝ (branchFinitePair i z).v x (Pi.single k 1) j) := by
      ext k
      rfl
    rw [he] at hj
    simpa only [potential_component_fderiv
      ((branchFinitePair i z).smooth.differentiable (by norm_num)) j] using hj

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FacePasting
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

lemma sourceFacePasteList_local (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧ sourceFacePasteList B v ks y=B k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · exact ⟨k,List.mem_cons_self,hk,by rw [sourceFacePasteList_cons,ite_eq_left hk]⟩
    · obtain ⟨l,hl,hly⟩ := hy
      have hl' : l∈ks := (List.mem_cons.mp hl).resolve_left (by rintro rfl; exact hk hly)
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,hl',hly⟩
      exact ⟨l,List.mem_cons_of_mem _ hl,hly,by rw [sourceFacePasteList_cons,ite_eq_right hk,he]⟩

lemma sourceFacePasteList_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    sourceFacePasteList B v ks (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := sourceFacePasteList_local B v ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma sourceFacePaste_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    sourceFacePaste B v (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) :=
  sourceFacePasteList_open B v _ i j hx (by simp)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_NonzeroJacobianAE
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

lemma ae_comp_of_nonzero_jacobian {f : Coord3 → Coord3}
    {D : Coord3 → Coord3 →L[ℝ] Coord3}
    (hf : ∀ x,HasFDerivAt f (D x) x) (hi : Function.Injective f)
    (hm : Measurable (fun x => ENNReal.ofReal |(D x).det|))
    (hn : ∀ x,(D x).det≠0) {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) :
    ∀ᵐ x ∂volume,P (f x) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have he := map_withDensity_abs_det_fderiv_eq_addHaar (μ:=volume)
    (s:=univ) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hi.injOn
  simp only [Measure.restrict_univ] at he
  have hp : ∀ᵐ y ∂Measure.map f (volume.withDensity (fun x => ENNReal.ofReal |(D x).det|)),P y := by
    rw [he]
    exact ae_restrict_of_ae hP
  have h := ae_of_ae_map hc.measurable.aemeasurable hp
  rw [ae_withDensity_iff hm] at h
  filter_upwards [h] with x hx
  exact hx (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,abs_nonpos_iff] using hn x)

lemma faceRayAngle_injective {w : ℝ} (hw : 0<w) (i : Fin 4) :
    Function.Injective (faceRayAngle w i) :=
  (strictMono_of_hasDerivAt_pos (hasDerivAt_faceRayAngle w i)
    (faceRayDensity_pos' hw i)).injective

lemma sourceFaceAngles_injective (i j : Fin 4) : Function.Injective (sourceFaceAngles i j) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [sourceFaceAngles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
  have hπ : 2*Real.pi≠0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have h1' := faceRayAngle_injective (by norm_num : (0:ℝ)<1) i (mul_left_cancel₀ hπ h1)
  have h2' := faceRayAngle_injective (by norm_num [sourceRadialWidth,sourceHole] : (0:ℝ) < sourceRadialWidth)
    j (mul_left_cancel₀ hπ h2)
  ext k
  fin_cases k <;> assumption

lemma sourceFaceAngles_ae {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) (i j : Fin 4) :
    ∀ᵐ x ∂volume,P (sourceFaceAngles i j x) := by
  apply ae_comp_of_nonzero_jacobian (sourceFaceAngles_hasFDeriv i j)
    (sourceFaceAngles_injective i j) _ _ hP
  · change Measurable (fun x : Coord3 => ENNReal.ofReal |(Matrix.toLin' (sourceFaceAngleMatrix i j x)).det|)
    simp only [LinearMap.det_toLin',sourceFaceAngleMatrix_det]
    exact (((continuous_const.mul ((continuous_faceRayDensity 1 i).comp (continuous_apply 1))).mul
      ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))).abs.measurable.ennreal_ofReal)
  · intro x
    change (Matrix.toLin' (sourceFaceAngleMatrix i j x)).det≠0
    rw [LinearMap.det_toLin']
    rw [sourceFaceAngleMatrix_det]
    exact (mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one angularArea_ge_one)
      (faceRayDensity_pos' (by norm_num) i (x 1)))
      (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))).ne'

end ScalarConductivity

end
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

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalNullTransport
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma flatEndCoordinates_ae {a : ℝ} (ha : a≠0) (b : ℝ)
    {P : Coord3 → Prop} (hP : ∀ᵐ y ∂volume,P y) :
    ∀ᵐ x ∂volume,P (flatEndCoordinates a b x) := by
  apply ae_comp_of_nonzero_jacobian (endAxialAffine_hasFDeriv a b) _ _ _ hP
  · intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [endAxialAffine,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at h0 h1 h2
    have h0' : x 0=y 0 := by linarith [mul_left_cancel₀ ha h0]
    ext k
    fin_cases k <;> assumption
  · exact measurable_const
  · intro x
    change (Matrix.toLin' (endAxialMatrix a)).det≠0
    simpa [LinearMap.det_toLin',endAxialMatrix,Matrix.det_diagonal,Fin.prod_univ_succ] using ha

lemma ae_image_of_differentiable {f : Coord3 → Coord3} {S : Set Coord3}
    (hS : MeasurableSet S) (hI : MeasurableSet (f '' S)) (hf : DifferentiableOn ℝ f S) {P : Coord3 → Prop}
    (hP : ∀ᵐ x ∂volume.restrict S,P (f x)) :
    ∀ᵐ y ∂volume.restrict (f '' S),P y := by
  have hn : volume {x | x∈S ∧ ¬ P (f x)}=0 := by
    rw [ae_restrict_iff' hS,ae_iff] at hP
    simpa using hP
  have hn' := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hf.mono (show {x | x∈S ∧ ¬ P (f x)}⊆S from fun x hx => hx.1)) hn
  rw [ae_iff,Measure.restrict_apply' hI]
  apply le_antisymm _ bot_le
  have he : {y | ¬P y} ∩ f '' S ⊆ f '' {x | x∈S ∧ ¬P (f x)} := by
    rintro y ⟨hy,x,hx,rfl⟩
    exact ⟨x,⟨hx,hy⟩,rfl⟩
  exact (measure_mono he).trans hn'.le

lemma sourceClosedCollarBand_ae_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {P : Coord3 → Prop}
    (hP : ∀ i j : Fin 4,∀ᵐ x ∂volume.restrict (sourceExtendedBox l r),
      P (sourceCollarPiece i j x)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),P y := by
  rw [sourceClosedCollarBand_measure_faces hl hr]
  simp only [ae_finsetSum_measure_iff,Finset.mem_univ,true_implies]
  intro i j
  exact ae_image_of_differentiable measurableSet_Icc (sourceCollarClosedPiece_measurable l r i j)
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).differentiableAt.differentiableWithinAt)
    (hP i j)

end ScalarConductivity

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
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedPeriodicFlux
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

lemma attachedPeriodicFlux_open (F : Coord3 → Coord3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    attachedPeriodicFlux F a b (sourceCollarPiece i j x)=
      (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ
        F (flatEndCoordinates a b (sourceFaceAngles i j x))) := by
  rw [attachedPeriodicFlux,sourceFacePaste_open _ _ i j hx]
  simp only [attachedPeriodicFluxFace,sourceCollarInverse_point i j hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_VariableCollarTensor
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
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

lemma variableCollarTensor_open (K : Coord3 → Mat3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    variableCollarTensor K a b (sourceCollarPiece i j x)=
      attachedVariableTensor (fun y => K (flatEndCoordinates a b (sourceFaceAngles i j y))) a i j x := by
  rw [variableCollarTensor,sourceFacePaste_open _ _ i j hx]
  simp only [variableFaceTensor,sourceCollarInverse_point i j hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_FiniteEndPhysicalH1
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

lemma flatEndCoordinates_shift (a b T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    flatEndCoordinates a b (x+angularShift T n)=flatEndCoordinates a b x+angularShift T n := by
  ext i
  fin_cases i <;> simp [flatEndCoordinates,angularShift]

lemma AngularPeriodic.flatEnd {E : Type*} {f : Coord3 → E} {T : ℝ}
    (hp : AngularPeriodic T f) (a b : ℝ) :
    AngularPeriodic T (fun x => f (flatEndCoordinates a b x)) := by
  intro n x
  change f (flatEndCoordinates a b (x+angularShift T n))=f (flatEndCoordinates a b x)
  rw [flatEndCoordinates_shift,hp n (flatEndCoordinates a b x)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedPeriodicDerivative
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

lemma flatEndCoordinates_covector {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (a b : ℝ) (x : Coord3) :
    (fun k => direction (Pi.single k 1) (fun y => f (flatEndCoordinates a b y)) x)=
      endAxialMatrix a*ᵥ(fun k => fderiv ℝ f (flatEndCoordinates a b x) (Pi.single k 1)) := by
  have he := (hf (flatEndCoordinates a b x)).hasFDerivAt.comp x (endAxialAffine_hasFDeriv a b x)
  ext k
  change fderiv ℝ (f ∘ flatEndCoordinates a b) x (Pi.single k 1)=_
  rw [he.fderiv]
  change fderiv ℝ f (flatEndCoordinates a b x) (endAxialMatrix a*ᵥPi.single k 1)=_
  simp only [endAxialMatrix, Matrix.diagonal_mulVec_single, Matrix.mulVec_diagonal]
  rw [show Pi.single k (![a,1,1] k * (1:ℝ)) =
      ![a,1,1] k • (Pi.single k (1:ℝ) : Coord3) by
    ext j
    by_cases hj : j=k
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]]
  rw [map_smul]
  rfl

lemma attachedPeriodicField_fderiv {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (a b : ℝ) (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (v : Coord3) :
    fderiv ℝ (attachedPeriodicField f a b) (sourceCollarPiece i j x) v=
      (attachedCartesianMatrix a i j x*ᵥ(fun k => fderiv ℝ f
        (flatEndCoordinates a b (sourceFaceAngles i j x)) (Pi.single k 1))) ⬝ᵥ v := by
  rw [attachedPeriodicField,physicalPeriodicField_fderiv (hp.flatEnd a b)
    (hf.comp ((contDiff_flatEndCoordinates a b).differentiable (by norm_num))) i j hx v,
    flatEndCoordinates_covector hf,attachedCartesianMatrix,Matrix.mulVec_mulVec]

lemma attachedPeriodicField_covector {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (a b : ℝ) (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    (fun k => lineDeriv ℝ (attachedPeriodicField f a b) (sourceCollarPiece i j x) (Pi.single k 1))=
      attachedCartesianMatrix a i j x*ᵥ(fun k => fderiv ℝ f
        (flatEndCoordinates a b (sourceFaceAngles i j x)) (Pi.single k 1)) := by
  have hd := (physicalPeriodicField_hasFDeriv (hp.flatEnd a b)
    (hf.comp ((contDiff_flatEndCoordinates a b).differentiable (by norm_num))) i j hx).differentiableAt
  change DifferentiableAt ℝ (attachedPeriodicField f a b) (sourceCollarPiece i j x) at hd
  ext k
  rw [hd.lineDeriv_eq_fderiv,attachedPeriodicField_fderiv hp hf a b i j hx]
  simp

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_AttachedSplicedConstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma attachedVariableTensor_flux (K : Coord3 → Mat3) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v : Coord3) :
    attachedVariableTensor K a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥv)=
      (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ(K x*ᵥv)) := by
  have he : (attachedCartesianMatrix a i j x)⁻¹*ᵥ
      (attachedCartesianMatrix a i j x*ᵥv)=v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]
  simp only [attachedVariableTensor,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,he]

lemma correctedEndGradient_transport {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      (fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b)
        (sourceCollarPiece m n x) (Pi.single k 1))=
      attachedCartesianMatrix a m n x*ᵥ(fun k => fderiv ℝ (branchSplicedField i z j)
        (flatEndCoordinates a b (sourceFaceAngles m n x)) (Pi.single k 1)) := by
  let y := flatEndCoordinates a b (sourceFaceAngles m n x)
  have hy : 0<y 0 := ht
  have hd := ((torusAffineField_smooth hs (centralBasisSlopes j i)
    (torusSpectralSynthesis s (f j))).contDiffAt
      ((axial_halfspace_open 0).mem_nhds hy)).differentiableAt (by norm_num)
  have hg := (branchCorrection_C2 i z hs j).differentiable (by norm_num)
  rw [fullAttachedEndGradient_transport s hs (f j) a b (centralBasisSlopes j i) m n hx ht,
    attachedPeriodicField_covector (branchCorrection_periodic i z j) hg a b m n hx,
    ←Matrix.mulVec_add]
  congr 1
  have he := torusAffineField_spectral_covector hs (f j) (centralBasisSlopes j i) hy
  have ha : torusAngles y=torusAngles (sourceFaceAngles m n x) :=
    torusAngles_endAxialAffine a b _
  rw [ha] at he
  change fullEndFlatCovector s (f j) (centralBasisSlopes j i) (y 0)
    (torusAngles (sourceFaceAngles m n x)) + _ = _
  rw [←he]
  ext k
  change fderiv ℝ (torusAffineField s (centralBasisSlopes j i) (torusSpectralSynthesis s (f j))) y
    (Pi.single k 1)+fderiv ℝ (branchCorrection i z j) y (Pi.single k 1)=_
  change _ = fderiv ℝ ((torusAffineField s (centralBasisSlopes j i)
    (torusSpectralSynthesis s (f j)))+branchCorrection i z j) y (Pi.single k 1)
  rw [fderiv_add hd (hg y)]
  rfl

lemma fullAttachedEnd_flat_flux {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) {a b : ℝ} (ha : a≠0)
    (m n : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    attachedCollarTensor s a (sourceCollarPiece m n x)*ᵥ
      fullAttachedEndGradient s f a b κ (sourceCollarPiece m n x)=
      (|a| *sourceFlatDensity m n x) • ((attachedCartesianMatrix a m n x)⁻¹ᵀ*ᵥ
        flatModeFlux s (torusAffineField s κ (torusSpectralSynthesis s f))
          (flatEndCoordinates a b (sourceFaceAngles m n x))) := by
  rw [attachedCollarTensor_open s a m n hx,
    fullAttachedEndGradient_transport s hs f a b κ m n hx ht]
  change attachedVariableTensor (fun _ => flatBackgroundTensor s) a m n x*ᵥ
    (attachedCartesianMatrix a m n x*ᵥ_) = _
  rw [attachedVariableTensor_flux _ ha m n (sourceCollarOpenBox_subset hx),flatModeFlux_tensor]
  have he := torusAffineField_spectral_covector hs f κ
    (show 0<(flatEndCoordinates a b (sourceFaceAngles m n x)) 0 from ht)
  have ha' : torusAngles (flatEndCoordinates a b (sourceFaceAngles m n x))=
      torusAngles (sourceFaceAngles m n x) := torusAngles_endAxialAffine a b _
  rw [ha'] at he
  rw [he]
  rfl

lemma attachedSpliced_constitution_point {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) {a b : ℝ} (ha : a≠0) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b))
    (hE : branchSplicedTensor i z (flatEndCoordinates a b (sourceFaceAngles m n x))*ᵥ
      (fun k => fderiv ℝ (branchSplicedField i z j)
        (flatEndCoordinates a b (sourceFaceAngles m n x)) (Pi.single k 1))=
      branchSplicedFlux i z j (flatEndCoordinates a b (sourceFaceAngles m n x))) :
    variableCollarTensor (branchSplicedTensor i z) a b (sourceCollarPiece m n x)*ᵥ
      (fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
        (fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b)
          (sourceCollarPiece m n x) (Pi.single k 1)))=
      attachedCollarTensor s a (sourceCollarPiece m n x)*ᵥ
        fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      attachedPeriodicFlux (branchFluxCorrection i z j) a b (sourceCollarPiece m n x) := by
  rw [correctedEndGradient_transport hs f i z j a b m n hx ht,
    variableCollarTensor_open _ a b m n hx,attachedVariableTensor_flux _ ha m n (sourceCollarOpenBox_subset hx),hE,
    branchSplicedFlux,Matrix.mulVec_add,smul_add,
    fullAttachedEnd_flat_flux hs (f j) (centralBasisSlopes j i) ha m n hx ht,
    attachedPeriodicFlux_open _ a b m n hx]

lemma attachedSpliced_constitution_ae {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) {a b l r : ℝ} (ha : a≠0) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),
    variableCollarTensor (branchSplicedTensor i z) a b y*ᵥ
      (fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
        fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b) y (Pi.single k 1))=
      attachedCollarTensor s a y*ᵥfullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicFlux (branchFluxCorrection i z j) a b y := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  have he := sourceFaceAngles_ae
    (flatEndCoordinates_ae ha b (branchSpliced_constitution i z hs j)) m n
  filter_upwards [ae_restrict_of_ae he,sourceExtendedBox_open_ae hl hr,
    sourceExtendedBox_axial_strict_ae l r] with x hx hxo hxt
  exact attachedSpliced_constitution_point hs f i z j ha m n hxo (hT _ hxt) hx

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

lemma symmetric_dotProduct_mulVec_swap {A : Mat3} (hA : A.IsSymm) (u v : Coord3) :
    u ⬝ᵥ(A*ᵥv)=(A*ᵥu) ⬝ᵥv := by
  rw [←hA,Matrix.dotProduct_transpose_mulVec,dotProduct_comm,hA]

local instance attachedSplicedGreenMeasureSpace_rcaa16b_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {s : Fin 3 → ℝ} (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))

lemma splicedAttached_energy_ae_oai
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (φ : Coord3 → ℝ) {a b l r : ℝ} (ha : a≠0)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    (fun y => splicedAttachedGradient f i z j a b y ⬝ᵥ
       (variableCollarTensor (branchSplicedTensor i z) a b y*ᵥphysicalTestCovector φ y))=ᵐ[
         volume.restrict (sourceClosedCollarBand l r)]
      fun y => fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y ⬝ᵥ
        (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)+
          attachedPeriodicFlux (branchFluxCorrection i z j) a b y ⬝ᵥphysicalTestCovector φ y := by
  filter_upwards [attachedSpliced_constitution_ae hs f i z j ha hl hr ht] with y hy
  rw [symmetric_dotProduct_mulVec_swap (variableCollarTensor_symm (branchSplicedTensor_symm i z) a b y),
    show variableCollarTensor (branchSplicedTensor i z) a b y*ᵥsplicedAttachedGradient f i z j a b y=
      attachedCollarTensor s a y*ᵥfullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicFlux (branchFluxCorrection i z j) a b y from hy,add_dotProduct,
    symmetric_dotProduct_mulVec_swap (A:=attachedCollarTensor s a y)
      (attachedFaceTensorList_symmetric s a _ y)]

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.splicedAttached_energy_ae_oai := @OAI.ScalarConductivity.splicedAttached_energy_ae_oai
