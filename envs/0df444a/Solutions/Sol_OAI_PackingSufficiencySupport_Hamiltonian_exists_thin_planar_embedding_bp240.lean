-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_thin_planar_embedding_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:14.146699+00:00
-- url     : https://prove2.me/submissions/e6ce9e33-44b1-44ff-910b-7483d367afba

import Mathlib
import Definitions.Def_OAIQ240Bp010
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_isotopy_bp240

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
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
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
open Set Function

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem timeStep_comp_smooth {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h t : Q → ℝ} {x : Q → E} (hhs : ContDiff ℝ ∞ h)
    (hts : ContDiff ℝ ∞ t) (hxs : ContDiff ℝ ∞ x)
    (hh : ∀ q, ‖h q‖ * L < 1) :
    ContDiff ℝ ∞ (fun q => timeStep X hX (h q) (t q) (x q)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have hloc := (localPath_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs)).contDiffAt ((picardDomain_open L).mem_nhds
      (show ((t q,x q),h q) ∈ picardDomain L from hh q))
  have hc := hloc.comp q ((hts.prodMk hxs).prodMk hhs).contDiffAt
  exact ((ContinuousMap.evalCLM (M := ℝ × E) ℝ (⟨1,by simp⟩ : Time)).contDiff.contDiffAt.comp q hc).snd

theorem timeSteps_variable_smooth {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h t : Q → ℝ} (hhs : ContDiff ℝ ∞ h) (hts : ContDiff ℝ ∞ t)
    (hh : ∀ q, ‖h q‖ * L < 1) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : Q × E => timeSteps X hX hXs (hh p.1) (t p.1) N p.2) ∧
    ContDiff ℝ ∞ (fun p : Q × E => (timeSteps X hX hXs (hh p.1) (t p.1) N).symm p.2) := by
  induction N with
  | zero => exact ⟨contDiff_snd,contDiff_snd⟩
  | succ N ih =>
    constructor
    · exact timeStep_comp_smooth X hX hXs (hhs.comp contDiff_fst)
        ((hts.add (contDiff_const.mul hhs)).comp contDiff_fst) ih.1 (fun p => hh p.1)
    · have hg : ContDiff ℝ ∞ (fun p : Q × E =>
          timeStep X hX (-h p.1) ((t p.1+N*h p.1)+h p.1) p.2) :=
        timeStep_comp_smooth X hX hXs (hhs.neg.comp contDiff_fst)
          (((hts.add (contDiff_const.mul hhs)).add hhs).comp contDiff_fst)
          contDiff_snd (fun p => by simpa only [norm_neg] using hh p.1)
      exact ih.2.comp (contDiff_fst.prodMk hg)


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

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem exists_compact_time_isotopy {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (S : Set E) (hs : ∀ t x, x ∉ S → X (t,x) = 0) :
    ∃ Φ : ℝ → E ≃ₜ E,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ (u : ℝ → E), Continuous u →
        (∀ t, HasDerivAt u (X (t,u t)) t) →
        ∀ t, Φ t (u 0) = u (Real.smoothTransition t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (L:ℝ)
  have hN0 : (0:ℝ) < N := L.coe_nonneg.trans_lt hN
  let h : ℝ → ℝ := fun t => Real.smoothTransition t / N
  have hh (t : ℝ) : ‖h t‖ * L < 1 := by
    change ‖Real.smoothTransition t / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg t),div_mul_eq_mul_div]
    apply (div_lt_one hN0).mpr
    exact (mul_le_of_le_one_left L.coe_nonneg (Real.smoothTransition.le_one t)).trans_lt hN
  have hhs : ContDiff ℝ ∞ h := Real.smoothTransition.contDiff.div_const N
  let Φ : ℝ → E ≃ₜ E := fun t => timeSteps X hX hXs (hh t) 0 N
  have hsm := timeSteps_variable_smooth X hX hXs hhs (contDiff_const (c := (0:ℝ))) hh N
  refine ⟨Φ,hsm.1,hsm.2,?_,?_,?_⟩
  · ext x
    change timeSteps X hX hXs (hh 0) 0 N x = x
    have hh0 : h 0 = 0 := by simp [h,Real.smoothTransition.zero_of_nonpos (le_refl 0)]
    simpa only [hh0] using timeSteps_zero X hX hXs 0 N x
  · intro t x hx
    exact timeSteps_of_stationary X hX hXs (hh t) 0 N (fun r => hs r x hx)
  · intro u hu hud t
    have he : (N:ℝ) * h t = Real.smoothTransition t := by dsimp [h]; field_simp
    simpa only [zero_add,he] using timeSteps_eq_solution X hX hXs (hh t) u hu hud 0 N

theorem exists_isotopy_extension
    (f g : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (K : Set E) (hK : IsCompact K) (W : Set E)
    (hUW : ∀ p ∈ U, p.2 ∈ W)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, (t,f (t,a)) ∈ U)
    (hinv : ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, g (t,f (t,a)) = a)
    (hstationary : ∀ t ∉ Ioo (0:ℝ) 1, ∀ a, fderiv ℝ f (t,a) (1,0) = 0) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ t a, a ∈ K → Φ t (f (0,a)) = f (Real.smoothTransition t,a)) := by
  let V : ℝ × E → E := fun p => fderiv ℝ f (p.1,g p) (1,0)
  have hV : ContDiffOn ℝ ∞ V U := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact (hd.comp_contDiffOn (contDiffOn_fst.prodMk hg)).clm_apply contDiffOn_const
  let C : Set (ℝ × E) := (fun p : ℝ × E => (p.1,f p)) '' (Icc (0:ℝ) 1 ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image (continuous_fst.prodMk hf.continuous)
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨t,a⟩,⟨ht,ha⟩,rfl⟩
    exact htrack t ht a ha
  obtain ⟨χ,hχ,hχc,hχU,_,hχ1,hXs,hXc,_⟩ :=
    exists_smooth_compact_extension hC hU hCU hV
  let X : C(ℝ × E,E) := ⟨fun p => χ p • V p,hXs.continuous⟩
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.image continuous_snd
  have hSW : S ⊆ W := by
    rintro _ ⟨p,hp,rfl⟩
    exact hUW p (hχU hp)
  have hs (t : ℝ) (x : E) (hx : x ∉ S) : X (t,x) = 0 := by
    have hn : (t,x) ∉ tsupport χ := fun hp => hx ⟨(t,x),hp,rfl⟩
    change χ (t,x) • V (t,x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨Φ,hΦ,hΦi,hΦ0,hΦs,hΦu⟩ := exists_compact_time_isotopy X hL hXs S hs
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro t a ha
  apply hΦu (fun t => f (t,a)) (hf.continuous.comp (continuous_id.prodMk continuous_const))
  intro r
  have hd : HasDerivAt (fun t => f (t,a)) (fderiv ℝ f (r,a) (1,0)) r :=
    (hf.differentiable (by simp) (r,a)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r a))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  by_cases hr : r ∈ Ioo (0:ℝ) 1
  · have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
    have he : (r,f (r,a)) ∈ C := ⟨(r,a),⟨hr',ha⟩,rfl⟩
    have hχr : χ (r,f (r,a)) = 1 := hχ1.self_of_nhdsSet _ he
    change χ (r,f (r,a)) • fderiv ℝ f (r,g (r,f (r,a))) (1,0) = _
    rw [hχr,one_smul,hinv r hr' a ha]
  · change χ (r,f (r,a)) • fderiv ℝ f (r,g (r,f (r,a))) (1,0) = _
    rw [hstationary r hr,hstationary r hr,smul_zero]

theorem exists_embedding_isotopy_extension
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set (ℝ × E)) (hD : IsOpen D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible)
    (K : Set E) (hK : IsCompact K) (W : Set E)
    (hDW : ∀ p ∈ D, f p ∈ W)
    (htrack : Icc (0:ℝ) 1 ×ˢ K ⊆ D)
    (hstationary : ∀ t ∉ Ioo (0:ℝ) 1, ∀ a, fderiv ℝ f (t,a) (1,0) = 0) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ t a, a ∈ K → Φ t (f (0,a)) = f (Real.smoothTransition t,a)) := by
  obtain ⟨U,g,hU,hg,himage,hleft,_⟩ := parametric_inverse_on f hf D hD hinj hi
  apply exists_isotopy_extension f g hf U hU hg K hK W
  · intro p hp
    rw [himage] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact hDW q hq
  · intro t ht a ha
    exact (hleft (t,a) (htrack ⟨ht,ha⟩)).1
  · intro t ht a ha
    exact (hleft (t,a) (htrack ⟨ht,ha⟩)).2
  · exact hstationary


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeSteps_fiber_variable_smooth {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ → ℝ} (hhs : ContDiff ℝ ∞ h) (hh : ∀ t, ‖h t‖ * L < 1) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : (P × ℝ) × E => timeSteps (fiberField X p.1.1)
      (fiberField_lipschitz X hX p.1.1) (fiberField_smooth X hXs p.1.1) (hh p.1.2) 0 N p.2) ∧
    ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (timeSteps (fiberField X p.1.1)
      (fiberField_lipschitz X hX p.1.1) (fiberField_smooth X hXs p.1.1) (hh p.1.2) 0 N).symm p.2) := by
  let Φ : P → ℝ → E ≃ₜ E := fun y t => timeSteps (fiberField X y)
    (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) 0 N
  let Ψ : ℝ → (P × E) ≃ₜ (P × E) := fun t => timeSteps (parameterField X)
    (parameterField_lipschitz X hX) (parameterField_smooth X hXs) (hh t) 0 N
  have hΨ : ContDiff ℝ ∞ (fun p : ℝ × (P × E) => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (P × E) => (Ψ p.1).symm p.2) :=
    timeSteps_variable_smooth (E := P × E) (Q := ℝ) (L := L)
      (parameterField X) (parameterField_lipschitz X hX)
      (parameterField_smooth X hXs) (h := h) (t := fun _ : ℝ => 0)
      hhs contDiff_const hh N
  have he (t : ℝ) (p : P × E) : Ψ t p = (p.1,Φ p.1 t p.2) :=
    timeSteps_fiber X hX hXs (hh t) 0 N p.1 p.2
  have hei (t : ℝ) (p : P × E) : (Ψ t).symm p = (p.1,(Φ p.1 t).symm p.2) := by
    apply (Ψ t).injective
    rw [(Ψ t).apply_symm_apply,he,(Φ p.1 t).apply_symm_apply]
  have hswap : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (p.1.2,(p.1.1,p.2))) :=
    contDiff_fst.snd.prodMk (contDiff_fst.fst.prodMk contDiff_snd)
  constructor
  · have hhsm := (hΨ.1.comp hswap).snd
    convert hhsm using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (congrArg Prod.snd (he p.1.2 (p.1.1,p.2))).symm
  · have hhsm := (hΨ.2.comp hswap).snd
    convert hhsm using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (congrArg Prod.snd (hei p.1.2 (p.1.1,p.2))).symm

theorem exists_parametric_time_isotopy {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (S : Set E) (hs : ∀ t y x, x ∉ S → X (t,(y,x)) = 0) :
    ∃ Φ : P → ℝ → E ≃ₜ E,
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y (u : ℝ → E), Continuous u →
        (∀ t, HasDerivAt u (X (t,(y,u t))) t) →
        ∀ t, Φ y t (u 0) = u (Real.smoothTransition t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (L:ℝ)
  have hN0 : (0:ℝ) < N := L.coe_nonneg.trans_lt hN
  let h : ℝ → ℝ := fun t => Real.smoothTransition t / N
  have hh (t : ℝ) : ‖h t‖ * L < 1 := by
    change ‖Real.smoothTransition t / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg t),div_mul_eq_mul_div]
    apply (div_lt_one hN0).mpr
    exact (mul_le_of_le_one_left L.coe_nonneg (Real.smoothTransition.le_one t)).trans_lt hN
  have hhs : ContDiff ℝ ∞ h := Real.smoothTransition.contDiff.div_const N
  let Φ : P → ℝ → E ≃ₜ E := fun y t => timeSteps (fiberField X y)
    (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) 0 N
  have hΦ := timeSteps_fiber_variable_smooth X hX hXs hhs hh N
  refine ⟨Φ,hΦ.1,hΦ.2,?_,?_,?_⟩
  · intro y
    ext x
    change timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (hh 0) 0 N x = x
    have hh0 : h 0 = 0 := by simp [h,Real.smoothTransition.zero_of_nonpos (le_refl 0)]
    simpa only [hh0] using timeSteps_zero (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) 0 N x
  · intro y t x hx
    exact timeSteps_of_stationary (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (hh t) 0 N (fun r => hs r y x hx)
  · intro y u hu hud t
    have heh : (N:ℝ) * h t = Real.smoothTransition t := by dsimp [h]; field_simp
    simpa only [zero_add,heh] using timeSteps_eq_solution (fiberField X y)
      (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) u hu hud 0 N

theorem exists_parametric_isotopy_extension
    (f g : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set ((P × ℝ) × E)) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (Y : Set P) (hY : IsCompact Y) (K : Set E) (hK : IsCompact K) (W : Set E)
    (hUW : ∀ p ∈ U, p.2 ∈ W)
    (htrack : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, ((y,t),f ((y,t),a)) ∈ U)
    (hinv : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, g ((y,t),f ((y,t),a)) = a)
    (hstationary : ∀ y t, t ∉ Ioo (0:ℝ) 1 → ∀ a,
      fderiv ℝ f ((y,t),a) ((0,1),0) = 0) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ t a, a ∈ K → Φ y t (f ((y,0),a)) =
        f ((y,Real.smoothTransition t),a)) := by
  let V : (P × ℝ) × E → E := fun p => fderiv ℝ f (p.1,g p) ((0,1),0)
  have hV : ContDiffOn ℝ ∞ V U := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact (hd.comp_contDiffOn (contDiffOn_fst.prodMk hg)).clm_apply contDiffOn_const
  let C : Set ((P × ℝ) × E) := (fun p : (P × ℝ) × E => (p.1,f p)) ''
    ((Y ×ˢ Icc (0:ℝ) 1) ×ˢ K)
  have hC : IsCompact C := ((hY.prod isCompact_Icc).prod hK).image
    (continuous_fst.prodMk hf.continuous)
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨⟨y,t⟩,a⟩,⟨⟨hy,ht⟩,ha⟩,rfl⟩
    exact htrack y hy t ht a ha
  obtain ⟨χ,_,hχc,hχU,_,hχ1,hVs,hVc,_⟩ :=
    exists_smooth_compact_extension hC hU hCU hV
  let σ : ℝ × (P × E) → (P × ℝ) × E := fun p => ((p.2.1,p.1),p.2.2)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_snd.fst.prodMk contDiff_fst).prodMk contDiff_snd.snd
  let X : C(ℝ × (P × E),E) := ⟨fun p => χ (σ p) • V (σ p),(hVs.comp hσ).continuous⟩
  have hXs : ContDiff ℝ ∞ X := hVs.comp hσ
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.image continuous_snd
  have hSW : S ⊆ W := by
    rintro _ ⟨p,hp,rfl⟩
    exact hUW p (hχU hp)
  have hs (t : ℝ) (y : P) (x : E) (hx : x ∉ S) : X (t,(y,x)) = 0 := by
    have hn : ((y,t),x) ∉ tsupport χ := fun hp => hx ⟨((y,t),x),hp,rfl⟩
    change χ ((y,t),x) • V ((y,t),x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hVs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hσL : LipschitzWith 1 σ := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [NNReal.coe_one,one_mul,σ,Prod.dist_eq]
    exact le_of_eq (by ac_rfl)
  have hXL : LipschitzWith L X := by
    change LipschitzWith L ((fun p => χ p • V p) ∘ σ)
    simpa only [mul_one] using hL.comp hσL
  obtain ⟨Φ,hΦ,hΦi,hΦ0,hΦs,hΦu⟩ := exists_parametric_time_isotopy X hXL hXs S hs
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro y hy t a ha
  apply hΦu y (fun t => f ((y,t),a))
    (hf.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const))
  intro r
  have hd : HasDerivAt (fun t => f ((y,t),a))
      (fderiv ℝ f ((y,r),a) ((0,1),0)) r :=
    (hf.differentiable (by simp) ((y,r),a)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_const r y).prodMk (hasDerivAt_id r)).prodMk (hasDerivAt_const r a))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  by_cases hr : r ∈ Ioo (0:ℝ) 1
  · have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
    have he : ((y,r),f ((y,r),a)) ∈ C := ⟨((y,r),a),⟨⟨hy,hr'⟩,ha⟩,rfl⟩
    have hχr : χ ((y,r),f ((y,r),a)) = 1 := hχ1.self_of_nhdsSet _ he
    change χ ((y,r),f ((y,r),a)) •
      fderiv ℝ f ((y,r),g ((y,r),f ((y,r),a))) ((0,1),0) = _
    rw [hχr,one_smul,hinv y hy r hr' a ha]
  · change χ ((y,r),f ((y,r),a)) •
      fderiv ℝ f ((y,r),g ((y,r),f ((y,r),a))) ((0,1),0) = _
    rw [hstationary y r hr,hstationary y r hr,smul_zero]

theorem exists_parametric_embedding_isotopy_extension
    (f : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set ((P × ℝ) × E)) (hD : IsOpen D)
    (hinj : ∀ q, InjOn (fun x => f (q,x)) {x | (q,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (K : Set E) (hK : IsCompact K) (W : Set E)
    (hDW : ∀ p ∈ D, f p ∈ W)
    (htrack : (Y ×ˢ Icc (0:ℝ) 1) ×ˢ K ⊆ D)
    (hstationary : ∀ y t, t ∉ Ioo (0:ℝ) 1 → ∀ a,
      fderiv ℝ f ((y,t),a) ((0,1),0) = 0) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ t a, a ∈ K → Φ y t (f ((y,0),a)) =
        f ((y,Real.smoothTransition t),a)) := by
  obtain ⟨U,g,hU,hg,himage,hleft,_⟩ := parametric_inverse_on f hf D hD hinj hi
  apply exists_parametric_isotopy_extension f g hf U hU hg Y hY K hK W
  · intro p hp
    rw [himage] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact hDW q hq
  · intro y hy t ht a ha
    exact (hleft ((y,t),a) (htrack ⟨⟨hy,ht⟩,ha⟩)).1
  · intro y hy t ht a ha
    exact (hleft ((y,t),a) (htrack ⟨⟨hy,ht⟩,ha⟩)).2
  · exact hstationary


end

open scoped ContDiff Topology NNReal
open Set Function

theorem smoothTransition_deriv_eq_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have hm : IsLocalMin Real.smoothTransition x := by
      apply IsMinOn.isLocalMin (s := univ) _ (by simp)
      intro y _
      rw [Real.smoothTransition.zero_of_nonpos hx]
      exact Real.smoothTransition.nonneg y
    exact hm.deriv_eq_zero
  · have hm : IsLocalMax Real.smoothTransition x := by
      apply IsMaxOn.isLocalMax (s := univ) _ (by simp)
      intro y _
      rw [Real.smoothTransition.one_of_one_le hx]
      exact Real.smoothTransition.le_one y
    exact hm.deriv_eq_zero



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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
 theorem flat_isotopy_stationary {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (ht : t ∉ Ioo (0:ℝ) 1) (x : E) :
    fderiv ℝ (fun p : ℝ × E => f (Real.smoothTransition p.1,p.2)) (t,x) (1,0) = 0 := by
  have hst : deriv Real.smoothTransition t = 0 :=
    smoothTransition_deriv_eq_zero (by simpa only [mem_Ioo,not_and_or,not_lt] using ht)
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hsm.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt
  have hi := (hs.hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,x)))
  have hd := ((hf.differentiable (by simp) _).hasFDerivAt.comp (t,x) hi).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [hst]
  exact map_zero _

theorem exists_flat_embedding_extension
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f (t,x)) U)
    (hi : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f (t,x)) x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f (t,x) ∈ W) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ x ∈ K, Φ 1 (f (0,x)) = f (1,x)) := by
  let F : ℝ × E → E := fun p => f (Real.smoothTransition p.1,p.2)
  have hF : ContDiff ℝ ∞ F :=
    hf.comp ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  let D : Set (ℝ × E) := Prod.snd ⁻¹' U ∩ F ⁻¹' W
  have hD : IsOpen D := (hU.preimage continuous_snd).inter (hW.preimage hF.continuous)
  have hstep (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_embedding_isotopy_extension F hF D hD
      (fun t => (hinj _ (hstep t)).mono (fun _ hx => hx.1))
      (fun p hp => hi _ (hstep p.1) _ hp.1) K hK W (fun _ hp => hp.2)
      (fun p hp => ⟨hKU hp.2,htrack _ (hstep p.1) _ hp.2⟩)
      (flat_isotopy_stationary hf)
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro x hx
  simpa only [F,Real.smoothTransition.zero_of_nonpos (le_refl 0),
    Real.smoothTransition.one_of_one_le (le_refl 1)] using hΦf 1 x hx

end
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

namespace SmoothlyAmbientRelated

 theorem trans {W K : Set E} {f g h : E → E}
    (hfg : SmoothlyAmbientRelated W K f g) (hgh : SmoothlyAmbientRelated W K g h) :
    SmoothlyAmbientRelated W K f h := by
  obtain ⟨Φ,hΦ⟩ := hfg
  obtain ⟨Ψ,hΨ⟩ := hgh
  refine ⟨Φ.trans Ψ,?_⟩
  intro x hx
  change Ψ.map 1 (Φ.map 1 (f x)) = h x
  rw [hΦ x hx,hΨ x hx]

 theorem symm {W K : Set E} {f g : E → E} (hfg : SmoothlyAmbientRelated W K f g) :
    SmoothlyAmbientRelated W K g f := by
  obtain ⟨Φ,hΦ⟩ := hfg
  refine ⟨Φ.symm,?_⟩
  intro x hx
  change (Φ.map 1).symm (g x) = f x
  rw [← hΦ x hx,(Φ.map 1).symm_apply_apply]

end SmoothlyAmbientRelated

variable [CompleteSpace E] [FiniteDimensional ℝ E]

 theorem smoothlyAmbientRelated_of_path
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f (t,x)) U)
    (hi : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f (t,x)) x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f (t,x) ∈ W) :
    SmoothlyAmbientRelated W K (fun x => f (0,x)) (fun x => f (1,x)) := by
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_flat_embedding_extension f hf U W hU hW hinj hi K hK hKU htrack
  exact ⟨⟨Φ,hΦ,hΦi,hΦ0,S,hS,hSW,hΦs⟩,hΦf⟩

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem parametric_flat_isotopy_stationary {f : (P × ℝ) × E → E} (hf : ContDiff ℝ ∞ f)
    (y : P) (t : ℝ) (ht : t ∉ Ioo (0:ℝ) 1) (x : E) :
    fderiv ℝ (fun p : (P × ℝ) × E => f ((p.1.1,Real.smoothTransition p.1.2),p.2))
      ((y,t),x) ((0,1),0) = 0 := by
  have hst : deriv Real.smoothTransition t = 0 :=
    smoothTransition_deriv_eq_zero (by simpa only [mem_Ioo,not_and_or,not_lt] using ht)
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hsm.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt
  have hp := hasFDerivAt_fst (𝕜 := ℝ) (p := ((y,t),x))
  have hy := (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,t))).comp ((y,t),x) hp
  have ht' := (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,t))).comp ((y,t),x) hp
  have hi := (hy.prodMk (hs.hasFDerivAt.comp ((y,t),x) ht')).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((y,t),x)))
  have hd := ((hf.differentiable (by simp) _).hasFDerivAt.comp ((y,t),x) hi).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [hst]
  exact map_zero _

variable [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_parametric_flat_embedding_extension
    (f : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (O : Set P) (hO : IsOpen O) (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f ((y,t),x)) U)
    (hi : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f ((y,t),x)) x).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (hYO : Y ⊆ O)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f ((y,t),x) ∈ W) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ x ∈ K, Φ y 1 (f ((y,0),x)) = f ((y,1),x)) := by
  let F : (P × ℝ) × E → E := fun p => f ((p.1.1,Real.smoothTransition p.1.2),p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp
    ((contDiff_fst.fst.prodMk (Real.smoothTransition.contDiff.comp contDiff_fst.snd)).prodMk contDiff_snd)
  let D : Set ((P × ℝ) × E) := (fun p => p.1.1) ⁻¹' O ∩ (Prod.snd ⁻¹' U ∩ F ⁻¹' W)
  have hD : IsOpen D := (hO.preimage continuous_fst.fst).inter
    ((hU.preimage continuous_snd).inter (hW.preimage hF.continuous))
  have hstep (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_parametric_embedding_isotopy_extension F hF D hD
      (fun q => by
        intro x hx z hz he
        exact hinj q.1 hx.1 _ (hstep q.2) hx.2.1 hz.2.1 he)
      (fun p hp => hi _ hp.1 _ (hstep p.1.2) _ hp.2.1) Y hY K hK W (fun _ hp => hp.2.2)
      (fun p hp => ⟨hYO hp.1.1,hKU hp.2,htrack _ hp.1.1 _ (hstep p.1.2) _ hp.2⟩)
      (parametric_flat_isotopy_stationary hf)
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro y hy x hx
  simpa only [F,Real.smoothTransition.zero_of_nonpos (le_refl 0),
    Real.smoothTransition.one_of_one_le (le_refl 1)] using hΦf y hy 1 x hx

end
section

universe u
variable {P E F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_fixed_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => ∫ t in (0:ℝ)..1, f (t,p)) := by
  let τ : C(Time,ℝ × P) := ⟨fun t => ((t:ℝ),0),continuous_subtype_val.prodMk continuous_const⟩
  let v : P → C(Time,ℝ × P) := fun p => τ + constantPath (0,p)
  have hv : ContDiff ℝ ∞ v := contDiff_const.add
    ((constantPath (E := ℝ × P)).contDiff.comp (contDiff_const.prodMk contDiff_id))
  let I : C(Time,F) →L[ℝ] F := (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : Time)).comp pathIntegral
  have he : (fun p => ∫ t in (0:ℝ)..1, f (t,p)) =
      fun p => I ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) := by
    funext p
    change _ = ∫ t in (0:ℝ)..1, extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [show extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t =
      ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) ⟨t,ht⟩ from extendPath_coe _ ⟨t,ht⟩]
    change f (t,p) = f ((t,0)+(0,p))
    simp
  rw [he]
  exact I.contDiff.comp ((postcomp_contDiff hf).comp hv)

 theorem smoothBlowup_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothBlowup f) := by
  unfold smoothBlowup
  apply contDiff_fixed_integral (f := fun q : ℝ × (ℝ × E) =>
    fderiv ℝ f ((q.1*q.2.1) • q.2.2) q.2.2)
  exact ((hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp
    ((contDiff_fst.mul contDiff_snd.fst).smul contDiff_snd.snd)).clm_apply contDiff_snd.snd

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_zero (f : E → F) (x : E) :
    smoothBlowup f (0,x) = fderiv ℝ f 0 x := by
  simp [smoothBlowup]

omit [FiniteDimensional ℝ E] in
 theorem smul_smoothBlowup {f : E → F} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    t • smoothBlowup f (t,x) = f (t • x)-f 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => f ((r*t) • x))
      (t • fderiv ℝ f ((s*t) • x) x) s := by
    simpa only [Function.comp_def,id_eq,one_mul,map_smul] using
      (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).mul_const t).smul_const x)
  have hc : Continuous (fun s : ℝ => t • fderiv ℝ f ((s*t) • x) x) :=
    continuous_const.smul (((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      ((continuous_id.mul continuous_const).smul continuous_const)).clm_apply continuous_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_smul,one_mul,zero_mul,zero_smul,smoothBlowup] using hi

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_eq {f : E → F} (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ≠ 0) (x : E) :
    smoothBlowup f (t,x) = t⁻¹ • (f (t • x)-f 0) := by
  rw [← smul_smoothBlowup hf t x,smul_smul,inv_mul_cancel₀ ht,one_smul]

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_injOn {f : E → F} (hf : ContDiff ℝ ∞ f)
    {U : Set E} (hinj : InjOn f U) (hi0 : Injective (fderiv ℝ f 0)) (t : ℝ) :
    InjOn (fun x => smoothBlowup f (t,x)) {x | t • x ∈ U} := by
  intro x hx y hy he
  by_cases ht : t = 0
  · subst t
    simp only [smoothBlowup_zero] at he
    exact hi0 he
  · have h := congrArg (fun z : F => t • z) he
    rw [smul_smoothBlowup hf,smul_smoothBlowup hf,sub_left_inj] at h
    exact (smul_right_injective E ht) (hinj hx hy h)

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_hasFDerivAt {f : E → F} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    HasFDerivAt (fun x => smoothBlowup f (t,x)) (fderiv ℝ f (t • x)) x := by
  by_cases ht : t = 0
  · subst t
    simpa only [smoothBlowup_zero,zero_smul] using (fderiv ℝ f 0).hasFDerivAt
  · have he : (fun x => smoothBlowup f (t,x)) = fun x => t⁻¹ • (f (t • x)-f 0) :=
      funext (smoothBlowup_eq hf ht)
    rw [he]
    have hd := (((hf.differentiable (by simp) (t • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul t)).sub_const (f 0)).const_smul t⁻¹
    have hde : t⁻¹ • (fderiv ℝ f (t • x)).comp (t • ContinuousLinearMap.id ℝ E) =
        fderiv ℝ f (t • x) := by
      ext v
      change t⁻¹ • fderiv ℝ f (t • x) (t • v) = fderiv ℝ f (t • x) v
      rw [map_smul,smul_smul,inv_mul_cancel₀ ht,one_smul]
    refine hd.congr_fderiv (Eq.symm ?_)
    · exact hde.symm

end

 theorem realLinear_complex_decomposition (A : ℂ →L[ℝ] ℂ) :
    A = complexPair ((A 1-Complex.I*A Complex.I)/2) ((A 1+Complex.I*A Complex.I)/2) := by
  ext z
  have hz : z = z.re • (1:ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_one,mul_one] using
      (Complex.re_add_im z).symm
  conv_lhs => rw [hz,map_add,map_smul,map_smul]
  simp only [complexPair_apply,Complex.real_smul]
  apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring

 theorem complex_decomposition_orientation (A : ℂ →L[ℝ] ℂ) :
    Complex.normSq ((A 1-Complex.I*A Complex.I)/2) -
      Complex.normSq ((A 1+Complex.I*A Complex.I)/2) =
      (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

 theorem complexPair_invertible {a b : ℂ} (h : ‖b‖ < ‖a‖) :
    (complexPair a b).IsInvertible := by
  have hi : Injective (complexPair a b) := by
    apply (injective_iff_map_eq_zero (complexPair a b)).mpr
    intro z hz
    change a*z+b*conj z = 0 at hz
    have hn := congrArg norm (eq_neg_of_add_eq_zero_left hz)
    rw [norm_mul,norm_neg,norm_mul,Complex.norm_conj] at hn
    have hz0 : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp hz0
  have hs := (LinearMap.injective_iff_surjective (f := (complexPair a b).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (complexPair a b)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem exists_positive_complex_linear_path (A : ℂ →L[ℝ] ℂ)
    (hA : 0 < (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re) :
    ∃ L : ℝ → ℂ →L[ℝ] ℂ, ContDiff ℝ ∞ L ∧
      (∀ t, (L t).IsInvertible) ∧ L 0 = ContinuousLinearMap.id ℝ ℂ ∧ L 1 = A ∧
      (∀ t ≤ 0, L t = ContinuousLinearMap.id ℝ ℂ) ∧ (∀ t, 1 ≤ t → L t = A) := by
  let a := (A 1-Complex.I*A Complex.I)/2
  let b := (A 1+Complex.I*A Complex.I)/2
  have hab : ‖b‖ < ‖a‖ := by
    have he := complex_decomposition_orientation A
    change Complex.normSq a-Complex.normSq b = _ at he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg a,norm_nonneg b]
  have ha : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg b).trans_lt hab)
  let s : ℝ → ℝ := fun t => Real.smoothTransition (2*t)
  let r : ℝ → ℝ := fun t => Real.smoothTransition (2*t-1)
  let α : ℝ → ℂ := fun t => Complex.exp (s t • Complex.log a)
  let β : ℝ → ℂ := fun t => r t • b
  let L : ℝ → ℂ →L[ℝ] ℂ := fun t => complexPair (α t) (β t)
  have hs : ContDiff ℝ ∞ s := Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hr : ContDiff ℝ ∞ r := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hα : ContDiff ℝ ∞ α := (hs.smul contDiff_const).cexp
  have hβ : ContDiff ℝ ∞ β := hr.smul contDiff_const
  have hL : ContDiff ℝ ∞ L := (hα.smul contDiff_const).add (hβ.smul contDiff_const)
  have hαa (t : ℝ) (ht : 1 ≤ 2*t) : α t = a := by
    dsimp [α,s]
    simp only [Real.smoothTransition.one_of_one_le ht,Complex.ofReal_one,one_mul,Complex.exp_log ha]
  have hL0 (t : ℝ) (ht : t ≤ 0) : L t = ContinuousLinearMap.id ℝ ℂ := by
    have ht0 : 2*t ≤ 0 := by linarith
    have ht1 : 2*t-1 ≤ 0 := by linarith
    ext z
    simp [L,α,β,s,r,Real.smoothTransition.zero_of_nonpos ht0,
      Real.smoothTransition.zero_of_nonpos ht1]
  have hL1 (t : ℝ) (ht : 1 ≤ t) : L t = A := by
    have ht1 : 1 ≤ 2*t-1 := by linarith
    have ht0 : 1 ≤ 2*t := by linarith
    change complexPair (α t) (r t • b) = A
    rw [hαa t ht0,show r t = 1 from Real.smoothTransition.one_of_one_le ht1,one_smul]
    exact (realLinear_complex_decomposition A).symm
  refine ⟨L,hL,?_,hL0 0 le_rfl,hL1 1 le_rfl,hL0,hL1⟩
  intro t
  apply complexPair_invertible
  by_cases ht : 2*t-1 ≤ 0
  · have hr0 : r t = 0 := Real.smoothTransition.zero_of_nonpos ht
    change ‖r t • b‖ < ‖Complex.exp (s t • Complex.log a)‖
    rw [hr0,zero_smul,norm_zero]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  · have ht0 : 1 ≤ 2*t := by linarith
    change ‖r t • b‖ < ‖α t‖
    rw [hαa t ht0,norm_smul,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg b) (Real.smoothTransition.le_one _)).trans_lt hab

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem exists_small_positive_perturbation {K : Set P} (hK : IsCompact K)
    {F : ℝ × P → E} (hF : Continuous F) {W : Set E} (hW : IsOpen W)
    (h0 : ∀ p ∈ K, F (0,p) ∈ W) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ p ∈ K, F (ε,p) ∈ W := by
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ F ⁻¹' W := by
    rintro ⟨ε,p⟩ ⟨hε,hp⟩
    have he : ε = 0 := hε
    subst ε
    exact h0 p hp
  obtain ⟨U,V,hU,_,h0U,hKV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hW.preimage hF) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  refine ⟨δ,hδ,?_⟩
  intro ε hε p hp
  exact hUV ⟨hδU (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hε),hKV hp⟩

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

theorem tanh_smooth : ContDiff ℝ ∞ Real.tanh := by
  have ht : Real.tanh = fun y => Real.sinh y / Real.cosh y :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [ht]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun y => (Real.cosh_pos y).ne')

theorem tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have ht : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  have he : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  simpa only [← ht,he] using h

theorem squareSqueeze_smooth (k : ℝ) : ContDiff ℝ ∞ (squareSqueeze k) := by
  exact (tanh_smooth.comp (contDiff_const.mul contDiff_fst)).prodMk
    (tanh_smooth.comp (contDiff_const.mul contDiff_snd))

theorem squareSqueeze_injective {k : ℝ} (hk : k ≠ 0) : Injective (squareSqueeze k) := by
  intro x y h
  have ha := Real.tanh_injective (congrArg Prod.fst h)
  have hb := Real.tanh_injective (congrArg Prod.snd h)
  exact Prod.ext (mul_left_cancel₀ hk ha) (mul_left_cancel₀ hk hb)

theorem squareSqueeze_fderiv (k : ℝ) (x v : Plane) :
    fderiv ℝ (squareSqueeze k) x v =
      (k/(Real.cosh (k*x.1))^2*v.1,k/(Real.cosh (k*x.2))^2*v.2) := by
  have h1 := (tanh_hasDerivAt (k*x.1)).comp_hasFDerivAt x
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul k)
  have h2 := (tanh_hasDerivAt (k*x.2)).comp_hasFDerivAt x
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).const_mul k)
  change fderiv ℝ (fun z : Plane => (Real.tanh (k*z.1),Real.tanh (k*z.2))) x v = _
  erw [(h1.prodMk h2).fderiv]
  ext <;> simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem squareSqueeze_det_pos {k : ℝ} (hk : 0 < k) (x : Plane) :
    0 < (fderiv ℝ (squareSqueeze k) x).det := by
  rw [planar_det]
  simp only [squareSqueeze_fderiv]
  change 0 < (k/(Real.cosh (k*x.1))^2*1)*(k/(Real.cosh (k*x.2))^2*1) -
    (k/(Real.cosh (k*x.2))^2*0)*(k/(Real.cosh (k*x.1))^2*0)
  simp only [mul_one,mul_zero,sub_zero]
  exact mul_pos (div_pos hk (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))
    (div_pos hk (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))

theorem squeezedDisk_compact (k : ℝ) : IsCompact (squeezedDisk k) :=
  (closedRoundDisk_isCompact 1).image (squareSqueeze_smooth k).continuous

theorem squeezedDisk_subset (k : ℝ) : squeezedDisk k ⊆ Ioo (-1) 1 ×ˢ Ioo (-1) 1 := by
  rintro _ ⟨x,_,rfl⟩
  exact ⟨⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩,
    ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩⟩

theorem exists_squeezedDisk_contains {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ k : ℝ, 0 < k ∧ Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k := by
  let M := max |Real.artanh (-q)| |Real.artanh q|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  let k := 2*(M+1)
  have hk : 0 < k := by dsimp [k] <;> positivity
  have hb (a : ℝ) (ha : a ∈ Icc (-q) q) : |Real.artanh a| ≤ M := by
    have hlo := Real.artanh_le_artanh (by linarith : -1 < -q) (by linarith [ha.2] : a < 1) ha.1
    have hhi := Real.artanh_le_artanh (by linarith [ha.1] : -1 < a) hq1 ha.2
    apply abs_le.mpr
    constructor
    · exact ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)).trans hlo
    · exact hhi.trans ((le_abs_self _).trans (le_max_right _ _))
  refine ⟨k,hk,?_⟩
  intro x hx
  refine ⟨(Real.artanh x.1/k,Real.artanh x.2/k),?_,?_⟩
  · have h1 := hb x.1 hx.1
    have h2 := hb x.2 hx.2
    have hb1 : |Real.artanh x.1/k| < 1/2 := by
      rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk]
      dsimp [k] <;> linarith
    have hb2 : |Real.artanh x.2/k| < 1/2 := by
      rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk]
      dsimp [k] <;> linarith
    change (Real.artanh x.1/k)^2+(Real.artanh x.2/k)^2 ≤ 1^2
    have ha1 := (abs_lt.mp hb1)
    have ha2 := (abs_lt.mp hb2)
    nlinarith [sq_nonneg (Real.artanh x.1/k),sq_nonneg (Real.artanh x.2/k)]
  · ext <;> simp only [squareSqueeze,mul_div_cancel₀ _ hk.ne']
    · exact Real.tanh_artanh ⟨by linarith [hx.1.1],by linarith [hx.1.2]⟩
    · exact Real.tanh_artanh ⟨by linarith [hx.2.1],by linarith [hx.2.2]⟩

theorem squeezedArea_nonneg (k : ℝ) : 0 ≤ squeezedArea k := ENNReal.toReal_nonneg

theorem planar_closed_square_volume {q : ℝ} (hq : 0 ≤ q) :
    volume (Icc (-q) q ×ˢ Icc (-q) q : Set Plane) = ENNReal.ofReal (4*q^2) := by
  change (volume.prod volume) (Icc (-q) q ×ˢ Icc (-q) q) = _
  rw [Measure.prod_prod,Real.volume_Icc,← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

theorem squeezedArea_le (k : ℝ) : squeezedArea k ≤ 4 := by
  have hm : volume (squeezedDisk k) ≤ volume (Ioo (-1) 1 ×ˢ Ioo (-1) 1 : Set Plane) :=
    measure_mono (squeezedDisk_subset k)
  have hv : volume (Ioo (-1) 1 ×ˢ Ioo (-1) 1 : Set Plane) = ENNReal.ofReal 4 := by
    change (volume.prod volume) (Ioo (-1) 1 ×ˢ Ioo (-1) 1) = _
    rw [Measure.prod_prod,Real.volume_Ioo]
    norm_num
  rw [hv] at hm
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  simpa only [squeezedArea,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4)] using hh

theorem squeezedArea_lower {q k : ℝ} (hq : 0 ≤ q)
    (hsub : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) : 4*q^2 ≤ squeezedArea k := by
  have hm : volume (Icc (-q) q ×ˢ Icc (-q) q : Set Plane) ≤ volume (squeezedDisk k) :=
    measure_mono hsub
  rw [planar_closed_square_volume hq] at hm
  have hh := ENNReal.toReal_mono (squeezedDisk_compact k).measure_ne_top hm
  simpa only [squeezedArea,ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*q^2)] using hh

theorem exists_rounded_square {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ k : ℝ, 0 < k ∧ Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧
      0 < squeezedArea k ∧ 4*q^2 ≤ squeezedArea k ∧ squeezedArea k ≤ 4 := by
  obtain ⟨k,hk,hs⟩ := exists_squeezedDisk_contains hq0.le hq1
  have hl := squeezedArea_lower hq0.le hs
  exact ⟨k,hk,hs,lt_of_lt_of_le (by positivity) hl,hl,squeezedArea_le k⟩

@[simp] theorem diagonalScale_det (a b : ℝ) : (diagonalScale a b).det = a*b := by
  rw [planar_det]
  simp [planarArea_apply]

theorem affineRectangle_image_volume (c : Plane) (a b : ℝ) (S : Set Plane) :
    volume (affineRectangle c a b '' S) = ENNReal.ofReal |a*b| * volume S := by
  change volume (((fun x : Plane => c+x) ∘ diagonalScale a b) '' S) = _
  rw [Set.image_comp]
  simp only [image_add_left,MeasureTheory.measure_preimage_add]
  rw [Measure.addHaar_image_continuousLinearMap]
  change ENNReal.ofReal |(diagonalScale a b).det| * volume S = _
  rw [diagonalScale_det]

theorem affineRectangle_squeezedArea {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c : Plane) (k : ℝ) :
    (volume (affineRectangle c a b '' squeezedDisk k)).toReal = a*b*squeezedArea k := by
  rw [affineRectangle_image_volume,ENNReal.toReal_mul,abs_of_nonneg (mul_nonneg ha hb),
    ENNReal.toReal_ofReal (mul_nonneg ha hb)]
  rfl

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem exists_rounded_square_with_control {Y : Set P} (hY : IsCompact Y)
    {F : Plane × P → E} (hF : Continuous F) {W : Set E} (hW : IsOpen W)
    (hbase : ∀ y ∈ Y, F ((1,1),y) ∈ W) :
    ∃ q k : ℝ, 0 < q ∧ q < 1 ∧ 0 < k ∧
      Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧
      0 < squeezedArea k ∧
      ∀ y ∈ Y, F ((q,4/squeezedArea k),y) ∈ W := by
  have hsub : ({(1,1)} : Set Plane) ×ˢ Y ⊆ F ⁻¹' W := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have he : x = (1,1) := hx
    subst x
    exact hbase y hy
  obtain ⟨U,V,hU,_,h1U,hYV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hY (hW.preimage hF) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h1U rfl))
  have hqcont : ContinuousAt (fun q : ℝ => 1/q^2) 1 :=
    continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
  have hevent : ∀ᶠ q : ℝ in 𝓝 1,
      0 < q ∧ |q-1| < δ ∧ |1/q^2-1| < δ := by
    have ha : ∀ᶠ q : ℝ in 𝓝 1, 0 < q := isOpen_Ioi.mem_nhds (by norm_num)
    have hb : ∀ᶠ q : ℝ in 𝓝 1, |q-1| < δ := by
      filter_upwards [Metric.ball_mem_nhds (1:ℝ) hδ] with q hq
      exact hq
    have hc : ∀ᶠ q : ℝ in 𝓝 1, |1/q^2-1| < δ := by
      have hct : Tendsto (fun q : ℝ => 1/q^2) (𝓝 1) (𝓝 1) := by
        simpa only [one_pow,div_one] using hqcont.tendsto
      filter_upwards [hct.eventually (Metric.ball_mem_nhds (1:ℝ) hδ)] with q hq
      exact hq
    filter_upwards [ha,hb,hc] with q ha hb hc using ⟨ha,hb,hc⟩
  obtain ⟨q,hq,hq1⟩ := ((hevent.filter_mono
    (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  obtain ⟨k,hk,hs,hA,hAl,hAu⟩ := exists_rounded_square hq.1 hq1
  have htlo : 1 ≤ 4/squeezedArea k := (le_div_iff₀ hA).mpr (by simpa using hAu)
  have hthi : 4/squeezedArea k ≤ 1/q^2 := by
    apply (div_le_div_iff₀ hA (sq_pos_of_pos hq.1)).mpr
    simpa using hAl
  have htd : |4/squeezedArea k-1| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr htlo)]
    exact (sub_le_sub_right hthi 1).trans_lt ((le_abs_self _).trans_lt hq.2.2)
  refine ⟨q,k,hq.1,hq1,hk,hs,hA,?_⟩
  intro y hy
  apply hUV ⟨hδU ?_,hYV hy⟩
  rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
  exact ⟨by simpa only [Real.dist_eq] using hq.2.1,
    by simpa only [Real.dist_eq] using htd⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothConvexSelection
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
variable {P : Type*} [TopologicalSpace P]

theorem roundedMargins_open {n : ℕ} (C : P → Fin n → ℝ) (hC : Continuous C)
    (L w : Fin n → ℝ) (V : P → Fin n → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i}) :
    IsOpen {p : Plane × P | RoundedMargins C L w V p.1.1 p.1.2 p.2} := by
  have hlo (i : Fin n) : IsOpen {p : Plane × P | C p.2 i-p.1.2*L i/2 ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk
      (((continuous_apply i).comp (hC.comp continuous_snd)).sub
        ((continuous_fst.snd.mul continuous_const).div_const 2)))
  have hhi (i : Fin n) : IsOpen {p : Plane × P | C p.2 i+p.1.2*L i/2 ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk
      (((continuous_apply i).comp (hC.comp continuous_snd)).add
        ((continuous_fst.snd.mul continuous_const).div_const 2)))
  have hpair (i j : Fin n) : IsOpen {p : Plane × P | i < j →
      C p.2 j-p.1.1*p.1.2*L j/2 < C p.2 i-p.1.2*L i/2 ∧
      C p.2 i+p.1.2*L i/2 < C p.2 j+p.1.1*p.1.2*L j/2 ∧ w i < p.1.1*w j} := by
    by_cases hij : i < j
    · simp only [hij,true_implies,ofPred_and]
      exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
        ((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop)))
    · simp only [hij,false_implies,ofPred_true,isOpen_univ]
  change IsOpen {p : Plane × P | 0 < p.1.2 ∧
    (∀ i, C p.2 i-p.1.2*L i/2 ∈ V p.2 i ∧ C p.2 i+p.1.2*L i/2 ∈ V p.2 i) ∧
    ∀ i j, i < j → _}
  simp only [ofPred_and,ofPred_forall]
  exact (isOpen_lt continuous_const continuous_fst.snd).inter
    ((isOpen_iInter_of_finite (fun i => (hlo i).inter (hhi i))).inter
      (isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => by
        simpa only [ofPred_forall,ofPred_and] using hpair i j))))

theorem exists_exact_area_rounded_margins {n : ℕ} {Y : Set P} (hY : IsCompact Y)
    (c : P → Fin n → ℝ) (hc : Continuous c) (L w : Fin n → ℝ)
    (hw : StrictMono w) (V : P → Fin n → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hplace : ∀ y ∈ Y, (∀ i, c y i ∈ V y i ∧ c y i+L i ∈ V y i) ∧
      StrictNestedStarts L (c y)) :
    ∃ q k : ℝ, 0 < q ∧ q < 1 ∧ 0 < k ∧
      Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k ∧ 0 < squeezedArea k ∧
      ∀ y ∈ Y, RoundedMargins (fun y i => c y i+L i/2) L w V q (4/squeezedArea k) y := by
  let C : P → Fin n → ℝ := fun y i => c y i+L i/2
  have hC : Continuous C := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hc).add continuous_const
  apply exists_rounded_square_with_control hY continuous_id
    (roundedMargins_open C hC L w V hV)
  intro y hy
  change RoundedMargins C L w V 1 1 y
  refine ⟨by norm_num,?_,?_⟩
  · intro i
    simpa only [C,one_mul,add_sub_cancel_right,add_assoc,add_halves] using (hplace y hy).1 i
  · intro i j hij
    dsimp [C]
    simp only [one_mul,add_sub_cancel_right,add_assoc,add_halves]
    exact ⟨((hplace y hy).2 hij).1,((hplace y hy).2 hij).2,hw hij⟩


end

section
open scoped ContDiff Topology BigOperators
open Set Function

theorem exists_thin_rectangle_placement {m : ℕ} (h : Fin m → ℝ)
    (hh : ∀ i, 0 < h i) (hmono : StrictMono h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (L w c : Fin m → ℝ), (∀ i, 0 < L i) ∧ (∀ i, 0 < w i ∧ w i < 1) ∧
      StrictMono w ∧ (∀ i, L i*w i = h i) ∧ StrictNestedStarts L c ∧
      ∀ i, c i ∈ Ioo 0 (h i+δ/2) ∧ c i+L i ∈ Ioo 0 (h i+δ/2) := by
  let B : ℝ := 1+∑ i, h i
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ i, h i := Finset.sum_nonneg (fun i _ => (hh i).le)
    dsimp [B] <;> linarith
  have hiB (i : Fin m) : h i < B := by
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hh j).le) (Finset.mem_univ i)
    dsimp [B] <;> linarith
  let ε := min (δ/8) (1/4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε ≤ δ/8 := min_le_left _ _
  have hε1 : ε ≤ 1/4 := min_le_right _ _
  let β := ε/(2*B)
  have hd : 0 < 2*B := by linarith
  have hβ : 0 < β := div_pos hε hd
  have hβ1 : β < 1 := by apply (div_lt_one hd).mpr; linarith
  have hB0 : B ≠ 0 := ne_of_gt (by linarith)
  have hβB : β*B = ε/2 := by dsimp [β]; field_simp [hB0]
  have hsmall (i : Fin m) : β*h i < ε := by
    have he := mul_lt_mul_of_pos_left (hiB i) hβ
    rw [hβB] at he
    linarith
  let L i := h i+ε
  let w i := h i/(h i+ε)
  let c i := ε-β*h i
  have hL i : 0 < L i := add_pos (hh i) hε
  have hw i : 0 < w i ∧ w i < 1 :=
    ⟨div_pos (hh i) (hL i),(div_lt_one (hL i)).mpr (by dsimp [L] <;> linarith)⟩
  refine ⟨L,w,c,hL,hw,?_,?_,?_,?_⟩
  · intro i j hij
    apply (div_lt_div_iff₀ (hL i) (hL j)).mpr
    dsimp [L]
    have he := mul_lt_mul_of_pos_right (hmono hij) hε
    nlinarith
  · intro i
    dsimp [L,w]
    field_simp [show h i+ε ≠ 0 from (hL i).ne']
  · intro i j hij
    dsimp [c,L]
    have he := hmono hij
    have he1 := mul_lt_mul_of_pos_left he hβ
    have he2 := mul_lt_mul_of_pos_left he (sub_pos.mpr hβ1)
    constructor <;> nlinarith
  · intro i
    have hc : 0 < c i := sub_pos.mpr (hsmall i)
    have hcε : c i < ε := by dsimp [c] <;> nlinarith [mul_pos hβ (hh i)]
    have hlower : 0 < c i+L i := add_pos hc (hL i)
    have hupper : c i+L i < h i+δ/2 := by dsimp [L] <;> linarith
    exact ⟨⟨hc,(lt_add_of_pos_right (c i) (hL i)).trans hupper⟩,hlower,hupper⟩


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem affineRectangle_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (c : Plane) :
    Injective (affineRectangle c a b) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  exact Prod.ext (mul_left_cancel₀ ha (add_left_cancel h1))
    (mul_left_cancel₀ hb (add_left_cancel h2))

theorem affineRectangle_smooth (c : Plane) (a b : ℝ) :
    ContDiff ℝ ∞ (affineRectangle c a b) :=
  contDiff_const.add (diagonalScale a b).contDiff

theorem roundedMap_smooth (k : ℝ) (c : Plane) (a b : ℝ) :
    ContDiff ℝ ∞ (roundedMap k c a b) :=
  (affineRectangle_smooth c a b).comp (squareSqueeze_smooth k)

theorem roundedMap_injective {k a b : ℝ} (hk : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (c : Plane) : Injective (roundedMap k c a b) :=
  (affineRectangle_injective ha hb c).comp (squareSqueeze_injective hk)

theorem affineRectangle_fderiv (c : Plane) (a b : ℝ) (x : Plane) :
    fderiv ℝ (affineRectangle c a b) x = diagonalScale a b := by
  exact ((diagonalScale a b).hasFDerivAt.const_add c).fderiv

theorem roundedMap_det {k a b : ℝ} (c : Plane) (x : Plane) :
    (fderiv ℝ (roundedMap k c a b) x).det = a*b*(fderiv ℝ (squareSqueeze k) x).det := by
  change (fderiv ℝ (affineRectangle c a b ∘ squareSqueeze k) x).det = _
  rw [fderiv_comp x ((affineRectangle_smooth c a b).differentiable (by simp) _)
    ((squareSqueeze_smooth k).differentiable (by simp) _),affineRectangle_fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change (diagonalScale a b).det * _ = _
  rw [diagonalScale_det]

theorem roundedMap_det_pos {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (c : Plane) (x : Plane) : 0 < (fderiv ℝ (roundedMap k c a b) x).det := by
  rw [roundedMap_det]
  exact mul_pos (mul_pos ha hb) (squareSqueeze_det_pos hk x)

theorem roundedMap_mem_openBox {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k : ℝ) (c : Plane) (x : Plane) : roundedMap k c a b x ∈ openBox c a b := by
  have hx1 := Real.neg_one_lt_tanh (k*x.1)
  have hx2 := Real.tanh_lt_one (k*x.1)
  have hy1 := Real.neg_one_lt_tanh (k*x.2)
  have hy2 := Real.tanh_lt_one (k*x.2)
  change (c.1-a < c.1+a*Real.tanh (k*x.1) ∧ c.1+a*Real.tanh (k*x.1) < c.1+a) ∧
    (c.2-b < c.2+b*Real.tanh (k*x.2) ∧ c.2+b*Real.tanh (k*x.2) < c.2+b)
  constructor <;> constructor <;> nlinarith

theorem box_subset_roundedBox {q k a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) (c : Plane) :
    box c (q*a) (q*b) ⊆ roundedBox k c a b := by
  intro x hx
  let z : Plane := ((x.1-c.1)/a,(x.2-c.2)/b)
  have hz : z ∈ Icc (-q) q ×ˢ Icc (-q) q := by
    change (-q ≤ (x.1-c.1)/a ∧ (x.1-c.1)/a ≤ q) ∧
      (-q ≤ (x.2-c.2)/b ∧ (x.2-c.2)/b ≤ q)
    constructor <;> constructor
    · apply (le_div_iff₀ ha).mpr; linarith [hx.1.1]
    · apply (div_le_iff₀ ha).mpr; linarith [hx.1.2]
    · apply (le_div_iff₀ hb).mpr; linarith [hx.2.1]
    · apply (div_le_iff₀ hb).mpr; linarith [hx.2.2]
  obtain ⟨u,hu,he⟩ := hs hz
  refine ⟨u,hu,?_⟩
  change affineRectangle c a b (squareSqueeze k u) = x
  rw [he]
  ext <;> simp [affineRectangle,z,mul_div_cancel₀ _ ha.ne',mul_div_cancel₀ _ hb.ne']

theorem openBox_subset_interior_roundedBox {q k a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k) (c : Plane) :
    openBox c (q*a) (q*b) ⊆ interior (roundedBox k c a b) := by
  apply (isOpen_Ioo.prod isOpen_Ioo).subset_interior_iff.mpr
  exact (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans
    (box_subset_roundedBox ha hb hs c)

theorem roundedBox_compact (k : ℝ) (c : Plane) (a b : ℝ) :
    IsCompact (roundedBox k c a b) :=
  (closedRoundDisk_isCompact 1).image (roundedMap_smooth k c a b).continuous

theorem roundedBox_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℝ) (c : Plane) :
    (volume (roundedBox k c a b)).toReal = a*b*squeezedArea k := by
  change (volume ((affineRectangle c a b ∘ squareSqueeze k) '' closedRoundDisk 1)).toReal = _
  rw [image_comp]
  exact affineRectangle_squeezedArea ha hb c k


end

section
open scoped ContDiff Topology
open Set Function Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

theorem isInvertible_of_det_ne_zero {A : E →L[ℝ] E} (hA : A.det ≠ 0) : A.IsInvertible :=
  ⟨(A.toLinearMap.equivOfDetNeZero hA).toContinuousLinearEquiv,rfl⟩

variable [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem det_fderiv_conjugate (e : E ≃L[ℝ] F) {f : F → F} {x : E}
    (hf : DifferentiableAt ℝ f (e x)) :
    (fderiv ℝ (fun x => e.symm (f (e x))) x).det = (fderiv ℝ f (e x)).det := by
  have hd := e.symm.hasFDerivAt.comp x (hf.hasFDerivAt.comp x e.hasFDerivAt)
  change (fderiv ℝ (e.symm ∘ f ∘ e) x).det = _
  rw [hd.fderiv]
  change LinearMap.det (e.symm.toLinearEquiv.toLinearMap ∘ₗ
    (fderiv ℝ f (e x)).toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap) = _
  exact LinearMap.det_conj _ e.symm.toLinearEquiv


end

open scoped ContDiff Topology
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull_carrier _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull_radius _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem scalar_id_isInvertible {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := a⁻¹ • ContinuousLinearMap.id ℝ E)
  · ext x
    simp [smul_smul,ha]
  · ext x
    simp [smul_smul,ha]

 theorem smul_isInvertible {A : E →L[ℝ] E} (hA : A.IsInvertible)
    {a : ℝ} (ha : a ≠ 0) : (a • A).IsInvertible := by
  have he : a • A = (a • ContinuousLinearMap.id ℝ E).comp A := by ext x; rfl
  rw [he]
  exact (scalar_id_isInvertible ha).comp hA

 theorem isInvertible_injective {A : E →L[ℝ] E} (hA : A.IsInvertible) : Injective A := by
  obtain ⟨e,he⟩ := hA
  rw [← he]
  exact e.injective

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem smoothlyAmbientRelated_contraction
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (hKW : MapsTo f K W)
    (c : E) (hc : c ∈ W) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SmoothlyAmbientRelated W K f (fun x => c + ε • (f x-c)) := by
  let a : ℝ → ℝ := fun t => 1-t+t*ε
  have ha (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < a t ∧ a t ≤ 1 := by
    dsimp [a]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hε.le]
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hε1)]
  let F : ℝ × E → E := fun p => c + a p.1 • (f p.2-c)
  have hF : ContDiff ℝ ∞ F := contDiff_const.add
    (((contDiff_const.sub contDiff_fst).add (contDiff_fst.mul contDiff_const)).smul
      ((hf.comp contDiff_snd).sub contDiff_const))
  have hFi (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : InjOn (fun x => F (t,x)) U := by
    intro x hx y hy he
    apply hinj hx hy
    have hh := (smul_right_injective E (ne_of_gt (ha t ht).1)) (add_left_cancel he)
    exact sub_left_injective hh
  have hFd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ U) :
      (fderiv ℝ (fun x => F (t,x)) x).IsInvertible := by
    have hd := (((hf.differentiable (by simp) x).hasFDerivAt.sub_const c).const_smul (a t)).const_add c
    change HasFDerivAt (fun x => F (t,x)) (a t • fderiv ℝ f x) x at hd
    rw [hd.fderiv]
    exact smul_isInvertible (hi x hx) (ne_of_gt (ha t ht).1)
  have htrack (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ K) : F (t,x) ∈ W := by
    have hh := hcW hc (hKW hx) (sub_nonneg.mpr (ha t ht).2) (ha t ht).1.le
      (show (1-a t)+a t = 1 by ring)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F]
    module
  have hh := smoothlyAmbientRelated_of_path F hF U W hU hW hFi hFd K hK hKU htrack
  simpa [F,a] using hh

theorem exists_compact_planar_embedding_isotopy
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (hcU : Convex ℝ U) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set ℂ) (hK : IsCompact K) (h0K : (0:ℂ) ∈ K)
    (hKU : K ⊆ U) (hKW : K ⊆ W) (hfKW : MapsTo f K W)
    (hor : 0 < (fderiv ℝ f 0 1).re * (fderiv ℝ f 0 Complex.I).im -
      (fderiv ℝ f 0 1).im * (fderiv ℝ f 0 Complex.I).re) :
    SmoothlyAmbientRelated W K id f := by
  obtain ⟨L,hL,hLi,hL0,hL1,_⟩ := exists_positive_complex_linear_path (fderiv ℝ f 0) hor
  have h0W : (0:ℂ) ∈ W := hKW h0K
  have hf0W : f 0 ∈ W := hfKW h0K
  have h0U : (0:ℂ) ∈ U := hKU h0K
  let T : Set (ℝ × ℂ) := Icc (0:ℝ) 1 ×ˢ K
  have hT : IsCompact T := isCompact_Icc.prod hK
  let F₂ : ℝ × (ℝ × ℂ) → ℂ := fun q => q.2.1 • f 0 + q.1 • L q.2.1 q.2.2
  have hF₂ : ContDiff ℝ ∞ F₂ := (contDiff_snd.fst.smul contDiff_const).add
    (contDiff_fst.smul ((hL.comp contDiff_snd.fst).clm_apply contDiff_snd.snd))
  have hF₂0 (p : ℝ × ℂ) (hp : p ∈ T) : F₂ (0,p) ∈ W := by
    simpa [F₂] using hcW.smul_mem_of_zero_mem h0W hf0W hp.1
  obtain ⟨δ₂,hδ₂,hδ₂W⟩ := exists_small_positive_perturbation hT hF₂.continuous hW hF₂0
  let F₃ : ℝ × (ℝ × ℂ) → ℂ := fun q => f 0 + q.1 • smoothBlowup f q.2
  have hF₃ : ContDiff ℝ ∞ F₃ := contDiff_const.add
    (contDiff_fst.smul ((smoothBlowup_contDiff hf).comp contDiff_snd))
  obtain ⟨δ₃,hδ₃,hδ₃W⟩ := exists_small_positive_perturbation hT hF₃.continuous hW
    (fun _ _ => by simpa [F₃] using hf0W)
  let ε : ℝ := min (min δ₂ δ₃) 1 / 2
  have hε : 0 < ε := div_pos (lt_min (lt_min hδ₂ hδ₃) zero_lt_one) (by norm_num)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    linarith [min_le_right (min δ₂ δ₃) 1]
  have hε₂ : |ε| < δ₂ := by
    rw [abs_of_pos hε]
    have hh := (min_le_left (min δ₂ δ₃) 1).trans (min_le_left δ₂ δ₃)
    dsimp [ε] at *
    linarith
  have hε₃ : |ε| < δ₃ := by
    rw [abs_of_pos hε]
    have hh := (min_le_left (min δ₂ δ₃) 1).trans (min_le_right δ₂ δ₃)
    dsimp [ε] at *
    linarith
  have hrel₂ : SmoothlyAmbientRelated W K (fun x => ε • x)
      (fun x => f 0 + ε • fderiv ℝ f 0 x) := by
    have hh := smoothlyAmbientRelated_of_path (fun p => F₂ (ε,p))
      (hF₂.comp (contDiff_const.prodMk contDiff_id)) U W hU hW
      (fun t _ => by
        intro x _ y _ he
        apply isInvertible_injective (hLi t)
        exact (smul_right_injective ℂ (ne_of_gt hε)) (add_left_cancel he))
      (fun t _ x _ => by
        have hd := (((L t).hasFDerivAt (x := x)).const_smul ε).const_add (t • f 0)
        change HasFDerivAt (fun x => F₂ (ε,(t,x))) (ε • L t) x at hd
        rw [hd.fderiv]
        exact smul_isInvertible (hLi t) (ne_of_gt hε)) K hK hKU
      (fun t ht x hx => hδ₂W ε hε₂ (t,x) ⟨ht,hx⟩)
    simpa [F₂,hL0,hL1] using hh
  have hsmulU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : ℂ) (hx : x ∈ U) :
      t • x ∈ U := hcU.smul_mem_of_zero_mem h0U hx ht
  have hrel₃ : SmoothlyAmbientRelated W K (fun x => f 0 + ε • fderiv ℝ f 0 x)
      (fun x => f 0 + ε • (f x-f 0)) := by
    have hh := smoothlyAmbientRelated_of_path (fun p => F₃ (ε,p))
      (hF₃.comp (contDiff_const.prodMk contDiff_id)) U W hU hW
      (fun t ht => by
        intro x hx y hy he
        apply smoothBlowup_injOn hf hinj (isInvertible_injective (hi 0 h0U)) t
          (hsmulU t ht x hx) (hsmulU t ht y hy)
        exact (smul_right_injective ℂ (ne_of_gt hε)) (add_left_cancel he))
      (fun t ht x hx => by
        have hd := ((smoothBlowup_hasFDerivAt hf t x).const_smul ε).const_add (f 0)
        change HasFDerivAt (fun x => F₃ (ε,(t,x))) (ε • fderiv ℝ f (t • x)) x at hd
        rw [hd.fderiv]
        exact smul_isInvertible (hi _ (hsmulU t ht x hx)) (ne_of_gt hε)) K hK hKU
      (fun t ht x hx => hδ₃W ε hε₃ (t,x) ⟨ht,hx⟩)
    have hb (x : ℂ) : smoothBlowup f (1,x) = f x-f 0 := by
      simpa only [one_smul] using smul_smoothBlowup hf 1 x
    simpa only [F₃,smoothBlowup_zero,hb] using hh
  have hshrink : SmoothlyAmbientRelated W K id (fun x => ε • x) := by
    have hh := smoothlyAmbientRelated_contraction id contDiff_id U W hU hW hcW
      (injOn_id U) (fun x _ => by
        rw [fderiv_id]
        exact ⟨ContinuousLinearEquiv.refl ℝ ℂ,rfl⟩)
      K hK hKU hKW 0 h0W ε hε hε1
    simpa only [id_eq,sub_zero,zero_add] using hh
  have hexpand := smoothlyAmbientRelated_contraction f hf U W hU hW hcW hinj hi
    K hK hKU hfKW (f 0) hf0W ε hε hε1
  exact hshrink.trans (hrel₂.trans (hrel₃.trans hexpand.symm))

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem complex_det (A : ℂ →L[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr]
  ring

end
section

variable (P E : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {P E}

variable [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_embedding_family_transport
    (f : P × E → E) (hf : ContDiff ℝ ∞ f)
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ y ∈ O, InjOn (fun x => f (y,x)) U)
    (hi : ∀ y ∈ O, ∀ x ∈ U, (fderiv ℝ (fun x => f (y,x)) x).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ y ∈ Y, ∀ x ∈ K, f (y,x) ∈ W) :
    ∃ Φ : SupportedSmoothIsotopyFamily P E W,
      ∀ y ∈ Y, ∀ x ∈ K, Φ.map y 1 (f (y₀,x)) = f (y,x) := by
  let a : P × ℝ → P := fun p => (1-p.2) • y₀ + p.2 • p.1
  have ha : ContDiff ℝ ∞ a := ((contDiff_const.sub contDiff_snd).smul contDiff_const).add
    (contDiff_snd.smul contDiff_fst)
  have haO (y : P) (hy : y ∈ O) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : a (y,t) ∈ O :=
    hcO (hYO hy₀) hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have haY (y : P) (hy : y ∈ Y) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : a (y,t) ∈ Y :=
    hcY hy₀ hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let F : (P × ℝ) × E → E := fun p => f (a p.1,p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ := exists_parametric_flat_embedding_extension
    F hF O hO U W hU hW (fun y hy t ht => hinj _ (haO y hy t ht))
    (fun y hy t ht => hi _ (haO y hy t ht)) Y hY hYO K hK hKU
    (fun y hy t ht x hx => htrack _ (haY y hy t ht) x hx)
  refine ⟨⟨Φ,hΦ,hΦi,hΦ0,S,hS,hSW,hΦs⟩,?_⟩
  intro y hy x hx
  simpa only [F,a,sub_zero,one_smul,zero_smul,add_zero,sub_self,zero_add] using hΦf y hy x hx

end
section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SupportedSmoothIsotopyFamily

theorem conjugate_image {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (e : E ≃L[ℝ] F) (y : P) (t : ℝ) (S : Set E) :
    (Φ.conjugate e).map y t '' (e '' S) = e '' (Φ.map y t '' S) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨Φ.map y t x,⟨x,hx,rfl⟩,?_⟩
    simp [conjugate]
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨e x,⟨x,hx,rfl⟩,?_⟩
    simp [conjugate]

end SupportedSmoothIsotopyFamily

theorem complex_plane_image_closedBall {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.closedBall (0:ℂ) R = closedRoundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 ≤ R^2
    have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
  · intro hx
    change x.1^2+x.2^2 ≤ R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,← sq_le_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_image_ball {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.ball (0:ℂ) R = roundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 < R^2
    have hn : ‖z‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [(sq_lt_sq₀ (norm_nonneg _) hR).mpr hn]
  · intro hx
    change x.1^2+x.2^2 < R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_ball,dist_zero_right,← sq_lt_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_volume_image (S : Set ℂ) :
    volume (Complex.equivRealProdCLM '' S) = volume S := by
  have hh := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Complex.measurableEquivRealProd '' S)
  rw [preimage_image_eq S Complex.measurableEquivRealProd.injective] at hh
  exact hh.symm

end

theorem diagonalScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Injective (diagonalScale a b) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (mul_left_cancel₀ ha h1) (mul_left_cancel₀ hb h2)

theorem diagonalScale_inv_image_closedRoundDisk {r : ℝ} (hr : 0 < r) :
    diagonalScale r⁻¹ r⁻¹ '' closedRoundDisk r = closedRoundDisk 1 := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.1^2+z.2^2 ≤ r^2 at hz
    change (r⁻¹*z.1)^2+(r⁻¹*z.2)^2 ≤ 1^2
    have hh := mul_le_mul_of_nonneg_left hz (sq_nonneg r⁻¹)
    have he : r⁻¹^2*r^2 = 1 := by field_simp
    nlinarith only [hh,he]
  · intro hx
    change x.1^2+x.2^2 ≤ 1^2 at hx
    refine ⟨(r*x.1,r*x.2),?_,?_⟩
    · change (r*x.1)^2+(r*x.2)^2 ≤ r^2
      nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg r)]
    · ext <;> simp [diagonalScale_apply,hr.ne']

theorem volume_closedRoundDisk {r : ℝ} (hr : 0 ≤ r) :
    volume (closedRoundDisk r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [←complex_plane_image_closedBall hr,complex_plane_volume_image]
  rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) (by simp)]
  simp only [Complex.finrank_real_complex, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [←ENNReal.ofReal_pow hr,←ENNReal.ofReal_mul (sq_nonneg r),mul_comm]

theorem areaRadius_pos {a : ℝ} (ha : 0 < a) : 0 < areaRadius a :=
  Real.sqrt_pos.2 (div_pos ha Real.pi_pos)

theorem areaRadius_sq {a : ℝ} (ha : 0 ≤ a) : (areaRadius a)^2 = a/Real.pi :=
  Real.sq_sqrt (div_nonneg ha Real.pi_pos.le)

theorem areaRadius_strictMono : StrictMonoOn areaRadius (Ici 0) := by
  intro a ha b _ hab
  exact Real.sqrt_lt_sqrt (div_nonneg ha Real.pi_pos.le) ((div_lt_div_iff_of_pos_right Real.pi_pos).2 hab)

theorem mem_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ closedRoundDisk (areaRadius a) ↔ radialArea x ≤ a := by
  change radiusSq x ≤ (areaRadius a)^2 ↔ Real.pi * radiusSq x ≤ a
  rw [areaRadius_sq ha,le_div_iff₀ Real.pi_pos,mul_comm]

theorem mem_roundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) (x : Plane) :
    x ∈ roundDisk (areaRadius a) ↔ radialArea x < a := by
  change radiusSq x < (areaRadius a)^2 ↔ Real.pi * radiusSq x < a
  rw [areaRadius_sq ha,lt_div_iff₀ Real.pi_pos,mul_comm]

theorem volume_closedRoundDisk_areaRadius {a : ℝ} (ha : 0 ≤ a) :
    volume (closedRoundDisk (areaRadius a)) = ENNReal.ofReal a := by
  rw [volume_closedRoundDisk (show 0 ≤ areaRadius a from Real.sqrt_nonneg _),areaRadius_sq ha]
  congr 1
  exact mul_div_cancel₀ _ Real.pi_ne_zero

theorem roundedBox_nested_of_margins {k q a b a' b' : ℝ} {c c' : Plane}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hsquare : Icc (-q) q ×ˢ Icc (-q) q ⊆ squeezedDisk k)
    (hleft : c'.1-q*a' ≤ c.1-a) (hright : c.1+a ≤ c'.1+q*a')
    (hbottom : c'.2-q*b' ≤ c.2-b) (htop : c.2+b ≤ c'.2+q*b') :
    roundedBox k c a b ⊆ interior (roundedBox k c' a' b') := by
  apply Subset.trans _ (openBox_subset_interior_roundedBox ha' hb' hsquare c')
  rintro _ ⟨x,_,rfl⟩
  have hx := roundedMap_mem_openBox ha hb k c x
  exact ⟨⟨hleft.trans_lt hx.1.1,hx.1.2.trans_le hright⟩,
    ⟨hbottom.trans_lt hx.2.1,hx.2.2.trans_le htop⟩⟩

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
open Set Function MeasureTheory

@[fun_prop] theorem normalizedRoundedMap_smooth (k : ℝ) (c : Plane) (a b r : ℝ) :
    ContDiff ℝ ∞ (normalizedRoundedMap k c a b r) :=
  (roundedMap_smooth k c a b).comp (diagonalScale r⁻¹ r⁻¹).contDiff

theorem normalizedRoundedMap_injective {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) :
    Injective (normalizedRoundedMap k c a b r) :=
  (roundedMap_injective hk.ne' ha.ne' hb.ne' c).comp
    (diagonalScale_injective (inv_ne_zero hr.ne') (inv_ne_zero hr.ne'))

theorem normalizedRoundedMap_det_pos {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) (x : Plane) :
    0 < (fderiv ℝ (normalizedRoundedMap k c a b r) x).det := by
  rw [normalizedRoundedMap,fderiv_comp x
    ((roundedMap_smooth k c a b).differentiable (by simp) _)
    ((diagonalScale r⁻¹ r⁻¹).differentiable _), (diagonalScale r⁻¹ r⁻¹).fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change 0 < (fderiv ℝ (roundedMap k c a b) _).det * (diagonalScale r⁻¹ r⁻¹).det
  rw [diagonalScale_det]
  exact mul_pos (roundedMap_det_pos hk ha hb c _) (mul_pos (inv_pos.mpr hr) (inv_pos.mpr hr))

theorem normalizedRoundedMap_image {r : ℝ} (hr : 0 < r) (k : ℝ) (c : Plane) (a b : ℝ) :
    normalizedRoundedMap k c a b r '' closedRoundDisk r = roundedBox k c a b := by
  rw [normalizedRoundedMap,image_comp,diagonalScale_inv_image_closedRoundDisk hr]
  rfl

theorem roundedBox_volume_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℝ) (c : Plane) :
    volume (roundedBox k c a b) = ENNReal.ofReal (a*b*squeezedArea k) := by
  exact (ENNReal.toReal_eq_toReal_iff' (roundedBox_compact k c a b).measure_ne_top
    ENNReal.ofReal_ne_top).mp (by
      rw [roundedBox_volume ha hb k c,ENNReal.toReal_ofReal
        (mul_nonneg (mul_nonneg ha hb) (squeezedArea_nonneg k))])


end

open scoped ContDiff Topology NNReal
open Set Function MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_ParameterRelativeDiskMoser
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.eval_carrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Function

namespace PlanarDiskEmbedding

theorem nested_pull {W : Set ℂ} {D E : PlanarDiskEmbedding} (h : D.Nested E)
    (Φ : SupportedSmoothIsotopy W) : (D.pull Φ).Nested (E.pull Φ) := by
  refine ⟨h.1,?_⟩
  simp only [pull_carrier]
  rw [← (Φ.map 1).symm.image_interior]
  exact image_mono h.2

theorem exists_isotopy (D : PlanarDiskEmbedding) {R : ℝ}
    (hDR : D.radius < R) (hD : D.carrier ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R),
      Φ.map 1 '' Metric.closedBall 0 D.radius = D.carrier := by
  have h0 : (0:ℂ) ∈ Metric.closedBall 0 D.radius := Metric.mem_closedBall_self D.radius_pos.le
  have HH := exists_compact_planar_embedding_isotopy D.map D.smooth D.domain
    (Metric.ball 0 R) D.open_domain Metric.isOpen_ball D.convex_domain (convex_ball (0:ℂ) R)
    D.injective D.nonsingular (Metric.closedBall 0 D.radius) (isCompact_closedBall _ _) h0
    D.subset_domain (Metric.closedBall_subset_ball hDR) (fun x hx => hD ⟨x,hx,rfl⟩)
    (by rw [← complex_det]; exact D.orientation)
  obtain ⟨Φ,hΦ⟩ := HH
  refine ⟨Φ,?_⟩
  apply image_congr
  intro x hx
  exact hΦ x hx

end PlanarDiskEmbedding

namespace SupportedSmoothIsotopy

theorem image_closedBall {R : ℝ} (Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R))
    (t : ℝ) : Φ.map t '' Metric.closedBall 0 R = Metric.closedBall 0 R := by
  have hh (Ψ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R)) :
      MapsTo (Ψ.map t) (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro x hx
    by_cases hx' : x ∈ Metric.ball 0 R
    · exact Metric.ball_subset_closedBall (Ψ.mapsTo t hx')
    · rwa [Ψ.fixed t x (fun h => hx' (Ψ.support_subset h))]
  apply Subset.antisymm (image_subset_iff.mpr (hh Φ))
  intro x hx
  exact ⟨(Φ.map t).symm x,hh Φ.symm hx,(Φ.map t).apply_symm_apply x⟩

end SupportedSmoothIsotopy

theorem exists_nested_disk_isotopy (L : List PlanarDiskEmbedding)
    (hL : L.Pairwise PlanarDiskEmbedding.Nested) (R : ℝ)
    (hR : ∀ D ∈ L, D.radius < R)
    (hW : ∀ D ∈ L, D.carrier ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R),
      ∀ D ∈ L, Φ.map 1 '' Metric.closedBall 0 D.radius = D.carrier := by
  induction hn : L.length using Nat.strong_induction_on generalizing L R with
  | h n ih =>
    cases L with
    | nil => exact ⟨SupportedSmoothIsotopy.refl _,by simp⟩
    | cons D L =>
      obtain ⟨Φ,hΦ⟩ := D.exists_isotopy (hR D (by simp)) (hW D (by simp))
      let L' := L.map (fun E => E.pull Φ)
      have hLL : L.Pairwise PlanarDiskEmbedding.Nested := hL.of_cons
      have hDL : ∀ E ∈ L, D.Nested E := fun _ h => List.rel_of_pairwise_cons hL h
      have hL' : L'.Pairwise PlanarDiskEmbedding.Nested := by
        exact List.Pairwise.map (fun E => E.pull Φ)
          (fun _ _ h => PlanarDiskEmbedding.nested_pull h Φ) hLL
      have hR' : ∀ E ∈ L', E.radius < D.radius := by
        intro E hE
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        exact (hDL E0 hE0).1
      have hW' : ∀ E ∈ L', E.carrier ⊆ Metric.ball 0 D.radius := by
        intro E hE
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        rw [PlanarDiskEmbedding.pull_carrier]
        have hsub := image_mono (f := (Φ.map 1).symm) (hDL E0 hE0).2
        rw [(Φ.map 1).symm.image_interior,← hΦ] at hsub
        simpa only [Set.image_image,(Φ.map 1).symm_apply_apply,Set.image_id',
          interior_closedBall'] using hsub
      have hlen : L'.length < n := by
        simp only [L',List.length_map]
        simp only [List.length_cons] at hn
        omega
      obtain ⟨Ψ,hΨ⟩ := ih L'.length hlen L' hL' D.radius hR' hW' rfl
      let Ψ' := Ψ.mono (Metric.ball_subset_ball (hR D (by simp)).le)
      refine ⟨Ψ'.trans Φ,?_⟩
      intro E hE
      rcases List.mem_cons.mp hE with hE | hE
      · subst E
        change (fun x => Φ.map 1 (Ψ.map 1 x)) '' Metric.closedBall 0 D.radius = D.carrier
        rw [← Set.image_image,Ψ.image_closedBall 1,hΦ]
      · have he := hΨ (E.pull Φ) (List.mem_map.mpr ⟨E,hE,rfl⟩)
        simp only [PlanarDiskEmbedding.pull_radius] at he
        change (fun x => Φ.map 1 (Ψ.map 1 x)) '' Metric.closedBall 0 E.radius = E.carrier
        rw [← Set.image_image,he,PlanarDiskEmbedding.pull_carrier]
        simp only [Set.image_image,(Φ.map 1).apply_symm_apply,Set.image_id']



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ParametricNestedDisks
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
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
open Metric
section

variable (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {P}
namespace ParametricDiskEmbedding
variable {O : Set P}

theorem nested_pull {W : Set ℂ} {Y : Set P} {D E : ParametricDiskEmbedding P O}
    (h : NestedOn Y D E) (Φ : SupportedSmoothIsotopyFamily P ℂ W) :
    NestedOn Y (D.pull Φ) (E.pull Φ) := by
  intro y hy
  simp only [pull_carrier]
  rw [← (Φ.map y 1).symm.image_interior]
  exact image_mono (h y hy)

end ParametricDiskEmbedding

theorem supported_homeomorph_image {E : Type*} [TopologicalSpace E]
    (φ : E ≃ₜ E) (S : Set E) (h : ∀ x ∉ S, φ x = x) : φ '' S = S := by
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

variable [CompleteSpace P] [FiniteDimensional ℝ P]

theorem exists_nested_disk_family_transport
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    (L : List (ParametricDiskEmbedding P O))
    (hL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y))
    (W : Set ℂ) (hW : IsOpen W) (hLW : ∀ D ∈ L, ∀ y ∈ Y, D.carrier y ⊆ W) :
    ∃ Φ : SupportedSmoothIsotopyFamily P ℂ W,
      ∀ D ∈ L, ∀ y ∈ Y, Φ.map y 1 '' D.carrier y₀ = D.carrier y := by
  induction hn : L.length using Nat.strong_induction_on generalizing L W with
  | h n ih =>
    cases L with
    | nil => exact ⟨SupportedSmoothIsotopyFamily.refl _,by simp⟩
    | cons D L =>
      obtain ⟨Φ,hΦ⟩ := exists_embedding_family_transport D.map D.smooth O hO hcO
        D.domain W D.open_domain hW D.injective D.nonsingular Y hY hcY hYO y₀ hy₀
        (Metric.closedBall 0 D.radius) (isCompact_closedBall _ _) D.subset_domain
        (fun y hy x hx => hLW D (by simp) y hy ⟨x,hx,rfl⟩)
      have hΦim (y : P) (hy : y ∈ Y) : Φ.map y 1 '' D.carrier y₀ = D.carrier y := by
        rw [ParametricDiskEmbedding.carrier,ParametricDiskEmbedding.carrier,Set.image_image]
        exact image_congr (hΦ y hy)
      have hΦfix (x : ℂ) (hx : x ∈ D.carrier y₀) : Φ.map y₀ 1 x = x := by
        obtain ⟨z,hz,rfl⟩ := hx
        exact hΦ y₀ hy₀ z hz
      let L' := L.map (fun E => E.pull Φ)
      have hLL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y) := hL.of_cons
      have hDL : ∀ E ∈ L, ParametricDiskEmbedding.NestedOn Y D E :=
        fun _ h => List.rel_of_pairwise_cons hL h
      have hL' : L'.Pairwise (ParametricDiskEmbedding.NestedOn Y) := by
        exact List.Pairwise.map (fun E => E.pull Φ)
          (fun _ _ h => ParametricDiskEmbedding.nested_pull h Φ) hLL
      have hW' : ∀ E ∈ L', ∀ y ∈ Y, E.carrier y ⊆ interior (D.carrier y₀) := by
        intro E hE y hy
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        rw [ParametricDiskEmbedding.pull_carrier]
        have hsub := image_mono (f := (Φ.map y 1).symm) (hDL E0 hE0 y hy)
        rw [(Φ.map y 1).symm.image_interior,← hΦim y hy] at hsub
        simpa only [Set.image_image,(Φ.map y 1).symm_apply_apply,Set.image_id'] using hsub
      have hlen : L'.length < n := by
        simp only [L',List.length_map]
        simp only [List.length_cons] at hn
        omega
      obtain ⟨Ψ,hΨ⟩ := ih L'.length hlen L' hL' (interior (D.carrier y₀)) isOpen_interior hW' rfl
      let Ψ' := Ψ.mono (interior_subset.trans (hLW D (by simp) y₀ hy₀))
      refine ⟨Ψ'.trans Φ,?_⟩
      intro E hE y hy
      rcases List.mem_cons.mp hE with hE | hE
      · subst E
        change (fun x => Φ.map y 1 (Ψ.map y 1 x)) '' D.carrier y₀ = D.carrier y
        have hΨim : Ψ.map y 1 '' D.carrier y₀ = D.carrier y₀ :=
          supported_homeomorph_image _ _ (fun x hx => Ψ.fixed y 1 x
            (fun h => hx (interior_subset (Ψ.support_subset h))))
        rw [← Set.image_image,hΨim,hΦim y hy]
      · have he := hΨ (E.pull Φ) (List.mem_map.mpr ⟨E,hE,rfl⟩) y hy
        have hE0 : (E.pull Φ).carrier y₀ = E.carrier y₀ := by
          rw [ParametricDiskEmbedding.pull_carrier]
          calc
            (Φ.map y₀ 1).symm '' E.carrier y₀ = id '' E.carrier y₀ := by
              apply image_congr
              intro x hx
              apply (Φ.map y₀ 1).injective
              rw [(Φ.map y₀ 1).apply_symm_apply]
              exact (hΦfix x (interior_subset (hDL E hE y₀ hy₀ hx))).symm
            _ = E.carrier y₀ := image_id _
        rw [hE0] at he
        change (fun x => Φ.map y 1 (Ψ.map y 1 x)) '' E.carrier y₀ = E.carrier y
        rw [← Set.image_image,he,ParametricDiskEmbedding.pull_carrier]
        simp only [Set.image_image,(Φ.map y 1).apply_symm_apply,Set.image_id']

theorem exists_ordinary_nested_disk_family
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    (L : List (ParametricDiskEmbedding P O))
    (hL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y))
    (hr : L.Pairwise (fun D E => E.radius < D.radius))
    (R : ℝ) (hR : ∀ D ∈ L, D.radius < R)
    (hLW : ∀ D ∈ L, ∀ y ∈ Y, D.carrier y ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopyFamily P ℂ (Metric.ball 0 R),
      ∀ D ∈ L, ∀ y ∈ Y,
        Φ.map y 1 '' Metric.closedBall 0 D.radius = D.carrier y := by
  let L₀ := L.map (fun D => D.eval y₀ (hYO hy₀))
  have hL₀ : L₀.Pairwise PlanarDiskEmbedding.Nested := by
    apply List.Pairwise.map _ _ (hr.and hL)
    intro D E h
    exact ⟨h.1,h.2 y₀ hy₀⟩
  have hR₀ : ∀ D ∈ L₀, D.radius < R := by
    intro D hD
    change D ∈ L.map _ at hD
    obtain ⟨E,hE,he⟩ := List.mem_map.mp hD
    subst D
    exact hR E hE
  have hW₀ : ∀ D ∈ L₀, D.carrier ⊆ Metric.ball 0 R := by
    intro D hD
    change D ∈ L.map _ at hD
    obtain ⟨E,hE,he⟩ := List.mem_map.mp hD
    subst D
    exact hLW E hE y₀ hy₀
  obtain ⟨Φ₀,hΦ₀⟩ := exists_nested_disk_isotopy L₀ hL₀ R hR₀ hW₀
  obtain ⟨Ψ,hΨ⟩ := exists_nested_disk_family_transport O hO hcO Y hY hcY hYO y₀ hy₀
    L hL (Metric.ball 0 R) Metric.isOpen_ball hLW
  refine ⟨(SupportedSmoothIsotopyFamily.constant Φ₀).trans Ψ,?_⟩
  intro D hD y hy
  have hh := hΦ₀ (D.eval y₀ (hYO hy₀)) (List.mem_map.mpr ⟨D,hD,rfl⟩)
  change Φ₀.map 1 '' Metric.closedBall 0 D.radius = D.carrier y₀ at hh
  change (fun x => Ψ.map y 1 (Φ₀.map 1 x)) '' Metric.closedBall 0 D.radius = D.carrier y
  rw [← Set.image_image,hh,hΨ D hD y hy]

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_nested_disk_family
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    {m : ℕ} (D : Fin m → ParametricDiskEmbedding P O)
    (hfamily : ∀ ⦃i j⦄, i < j → ParametricDiskEmbedding.NestedOn Y (D i) (D j))
    (hr : StrictAnti (fun i => (D i).radius))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, (D i).radius < R)
    (hDW : ∀ i y, y ∈ Y → (D i).carrier y ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((D i).carrier y) =
      volume (Metric.closedBall (0:ℂ) (D i).radius)) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (D i).radius =
        Complex.equivRealProdCLM '' (D i).carrier y := by
  have hL : (List.ofFn D).Pairwise (ParametricDiskEmbedding.NestedOn Y) :=
    List.pairwise_ofFn.mpr hfamily
  have hLr : (List.ofFn D).Pairwise (fun D E => E.radius < D.radius) :=
    List.pairwise_ofFn.mpr hr
  obtain ⟨Φ,hΦ⟩ := exists_ordinary_nested_disk_family O hO hcO Y hY hcY hYO y₀ hy₀
    (List.ofFn D) hL hLr R
    (by intro E hE; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE; exact hrR i)
    (by intro E hE; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE; exact hDW i)
  let e := Complex.equivRealProdCLM
  let Φreal : SupportedSmoothIsotopyFamily P Plane (roundDisk R) :=
    (Φ.conjugate e).mono (by rw [complex_plane_image_ball hR.le])
  have himage (i : Fin m) (y : P) (hy : y ∈ Y) :
      Φreal.map y 1 '' closedRoundDisk (D i).radius = e '' (D i).carrier y := by
    rw [← complex_plane_image_closedBall (D i).radius_pos.le]
    change (Φ.conjugate e).map y 1 '' (e '' Metric.closedBall 0 (D i).radius) = _
    rw [Φ.conjugate_image e y 1,hΦ (D i) (List.mem_ofFn.mpr ⟨i,rfl⟩) y hy]
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_disk_isotopy_bp240 hR Φreal Y hY
    (fun i => (D i).radius) (fun i => (D i).radius_pos) hrR hr.injective (by
      intro i y hy
      rw [himage i y hy]
      change volume (Complex.equivRealProdCLM '' (D i).carrier y) = _
      rw [complex_plane_volume_image,harea i y hy,
        ← complex_plane_image_closedBall (D i).radius_pos.le,complex_plane_volume_image])
  refine ⟨Ψ,?_⟩
  intro i y hy
  rw [hΨ i y hy,himage i y hy]

end
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_disk_representative
    {Y A : Set P} (hY : IsCompact Y) (hcY : Convex ℝ Y)
    (hA : IsOpen A) (hYA : Y ⊆ A) {r : ℝ} (hr : 0 < r)
    (f : P × ℂ → ℂ) (hf : ContDiffOn ℝ ∞ f (A ×ˢ univ))
    (hi : ∀ y ∈ A, Injective (fun x => f (y,x)))
    (hd : ∀ y ∈ A, ∀ x, (fderiv ℝ (fun x => f (y,x)) x).IsInvertible)
    (ho : ∀ y ∈ A, 0 < (fderiv ℝ (fun x => f (y,x)) 0).det) :
    ∃ O : Set P, IsOpen O ∧ Convex ℝ O ∧ Y ⊆ O ∧ O ⊆ A ∧
      ∃ D : ParametricDiskEmbedding P O, D.radius = r ∧
        ∀ y ∈ O, ∀ x ∈ Metric.closedBall (0:ℂ) r, D.map (y,x) = f (y,x) := by
  let K := Y ×ˢ Metric.closedBall (0:ℂ) r
  have hK : IsCompact K := hY.prod (isCompact_closedBall _ _)
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK
    (hA.prod isOpen_univ) (by
      rintro ⟨y,x⟩ ⟨hy,_⟩
      exact ⟨hYA hy,mem_univ _⟩) hf
  let g : P × ℂ → ℂ := fun p => χ p • f p
  obtain ⟨W,hW,hKW,hWe⟩ := mem_nhdsSet_iff_exists.mp he
  obtain ⟨U,V,hU,hV,hYU,hBV,hUV⟩ :=
    generalized_tube_lemma hY (isCompact_closedBall (0:ℂ) r) hW hKW
  obtain ⟨δ,hδ,hδO⟩ := hY.exists_thickening_subset_open (hU.inter hA)
    (subset_inter hYU hYA)
  let O := thickening δ Y
  obtain ⟨ε,hε,hεV⟩ := (isCompact_closedBall (0:ℂ) r).exists_thickening_subset_open hV hBV
  have hball : ball (0:ℂ) (r+ε) ⊆ V := by
    rw [add_comm r ε,← thickening_closedBall hε hr.le (0:ℂ)]
    exact hεV
  have hEq (y : P) (hy : y ∈ O) (x : ℂ) (hx : x ∈ ball (0:ℂ) (r+ε)) :
      g (y,x) = f (y,x) := hWe (hUV ⟨(hδO hy).1,hball hx⟩)
  have hfder (y : P) (hy : y ∈ O) (x : ℂ) (hx : x ∈ ball (0:ℂ) (r+ε)) :
      fderiv ℝ (fun x => g (y,x)) x = fderiv ℝ (fun x => f (y,x)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    exact hEq y hy z hz
  let D : ParametricDiskEmbedding P O := {
      radius := r
      radius_pos := hr
      map := g
      smooth := hg
      domain := ball 0 (r+ε)
      open_domain := isOpen_ball
      convex_domain := convex_ball _ _
      subset_domain := closedBall_subset_ball (by linarith)
      injective := by
        intro y hy x hx z hz heq
        apply hi y (hδO hy).2
        change f (y,x) = f (y,z)
        rw [← hEq y hy x hx,← hEq y hy z hz]
        exact heq
      nonsingular := by
        intro y hy x hx
        rw [hfder y hy x hx]
        exact hd y (hδO hy).2 x
      orientation := by
        intro y hy
        rw [hfder y hy 0 (mem_ball_self (by linarith))]
        exact ho y (hδO hy).2 }
  refine ⟨O,isOpen_thickening,hcY.thickening δ,self_subset_thickening hδ Y,
    fun _ hy => (hδO hy).2,D,rfl,?_⟩
  intro y hy x hx
  exact hEq y hy x (closedBall_subset_ball (by linarith) hx)

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_disk_germs {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × ℂ → ℂ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, (fderiv ℝ (fun x => f i (y,x)) x).IsInvertible)
    (ho : ∀ i y, y ∈ A → 0 < (fderiv ℝ (fun x => f i (y,x)) 0).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆
        interior ((fun x => f j (y,x)) '' Metric.closedBall 0 (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) =
      volume (Metric.closedBall (0:ℂ) (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        Complex.equivRealProdCLM '' ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) := by
  classical
  have hex (i : Fin m) := exists_parametric_disk_representative hY hcY hA hYA (hr i)
    (f i) (hf i) (hi i) (hd i) (ho i)
  choose O hO hcO hYO hOA D hDr hDf using hex
  let U : Set P := ⋂ i, O i
  have hU : IsOpen U := isOpen_iInter_of_finite hO
  have hcU : Convex ℝ U := convex_iInter hcO
  have hYU : Y ⊆ U := by intro y hy; exact mem_iInter.mpr (fun i => hYO i hy)
  have hUO (i : Fin m) : U ⊆ O i := iInter_subset _ i
  let E (i : Fin m) : ParametricDiskEmbedding P U := (D i).restrictParam (hUO i)
  have hEr (i : Fin m) : (E i).radius = r i := hDr i
  have hEc (i : Fin m) (y : P) (hy : y ∈ Y) :
      (E i).carrier y = (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) := by
    change (fun x => (D i).map (y,x)) '' Metric.closedBall 0 (D i).radius = _
    rw [hDr i]
    apply image_congr
    intro x hx
    exact hDf i y (hYO i hy) x hx
  let Erev (i : Fin m) := E i.rev
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_nested_disk_family U hU hcU Y hY hcY hYU y₀ hy₀
    Erev (by
      intro i j hij y hy
      change (E j.rev).carrier y ⊆ interior ((E i.rev).carrier y)
      rw [hEc _ y hy,hEc _ y hy]
      exact hnest (Fin.rev_lt_rev.mpr hij) y hy)
    (by
      intro i j hij
      change (E j.rev).radius < (E i.rev).radius
      rw [hEr,hEr]
      exact hrmono (Fin.rev_lt_rev.mpr hij))
    R hR (by intro i; change (E i.rev).radius < R; rw [hEr]; exact hrR _)
    (by intro i y hy; change (E i.rev).carrier y ⊆ _; rw [hEc _ y hy]; exact hfit _ y hy)
    (by
      intro i y hy
      change volume ((E i.rev).carrier y) = volume (Metric.closedBall (0:ℂ) (E i.rev).radius)
      rw [hEc _ y hy,hEr]
      exact harea _ y hy)
  refine ⟨Ψ,?_⟩
  intro i y hy
  have hh := hΨ i.rev y hy
  change Ψ.isotopy.map y 1 '' closedRoundDisk (E i.rev.rev).radius =
    Complex.equivRealProdCLM '' (E i.rev.rev).carrier y at hh
  simpa only [Fin.rev_rev,hEr,hEc _ y hy] using hh

theorem exists_hamiltonian_plane_disk_germs {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × Plane → Plane)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, 0 < (fderiv ℝ (fun x => f i (y,x)) x).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆
        interior ((fun x => f j (y,x)) '' closedRoundDisk (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' closedRoundDisk (r i) ⊆ roundDisk R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' closedRoundDisk (r i)) =
      volume (closedRoundDisk (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        (fun x => f i (y,x)) '' closedRoundDisk (r i) := by
  let e := Complex.equivRealProdCLM
  let g (i : Fin m) (p : P × ℂ) := e.symm (f i (p.1,e p.2))
  have hs (i : Fin m) : ContDiffOn ℝ ∞ (g i) (A ×ˢ univ) :=
    e.symm.contDiff.comp_contDiffOn ((hf i).comp
      (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)).contDiffOn (by
        intro p hp; exact ⟨hp.1,mem_univ _⟩))
  have hder (i : Fin m) (y : P) (hy : y ∈ A) (x : ℂ) :
      (fderiv ℝ (fun x => g i (y,x)) x).det =
        (fderiv ℝ (fun x => f i (y,x)) (e x)).det := by
    change (fderiv ℝ (fun x => e.symm (f i (y,e x))) x).det = _
    apply det_fderiv_conjugate e (f := fun x => f i (y,x)) (x := x)
    have hh : ContDiffAt ℝ ∞ (f i) (y,e x) :=
      (hf i).contDiffAt ((hA.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)
    exact (hh.comp _ (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have himage (i : Fin m) (y : P) :
      e '' ((fun x => g i (y,x)) '' Metric.closedBall 0 (r i)) =
        (fun x => f i (y,x)) '' closedRoundDisk (r i) := by
    rw [←complex_plane_image_closedBall (hr i).le]
    simp only [image_image,g,e.apply_symm_apply]
    rfl
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_disk_germs hY hcY hA hYA y₀ hy₀ r hr hrmono g hs
    (fun i y hy => e.symm.injective.comp ((hi i y hy).comp e.injective))
    (fun i y hy x => isInvertible_of_det_ne_zero (by rw [hder i y hy x]; exact (hd i y hy _).ne'))
    (fun i y hy => by rw [hder i y hy 0]; exact hd i y hy _)
    (by
      intro i j hij y hy x hx
      have hh := hnest hij y hy
      rw [←himage i y,←himage j y] at hh
      have he : interior (e '' ((fun x => g j (y,x)) '' Metric.closedBall 0 (r j))) =
          e '' interior ((fun x => g j (y,x)) '' Metric.closedBall 0 (r j)) :=
        (e.toHomeomorph.image_interior _).symm
      rw [he] at hh
      have hh' := hh (mem_image_of_mem e hx)
      exact e.injective.mem_set_image.mp hh') R hR hrR
    (by
      intro i y hy x hx
      have hh := hfit i y hy
      rw [←himage i y,←complex_plane_image_ball hR.le] at hh
      exact e.injective.mem_set_image.mp (hh (mem_image_of_mem e hx)))
    (by
      intro i y hy
      rw [←complex_plane_volume_image, himage i y,harea i y hy,
        ←complex_plane_image_closedBall (hr i).le,complex_plane_volume_image])
  refine ⟨Ψ,?_⟩
  intro i y hy
  exact (hΨ i y hy).trans (himage i y)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open Set

theorem exists_positive_area_grid {A δ : ℝ} (_hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ (m : ℕ) (h : Fin m → ℝ), StrictMono h ∧ (∀ i, 0 < h i) ∧
      ∀ w ∈ Icc (0:ℝ) A, ∃ i, w ≤ h i ∧ h i-w < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (A/(δ/2))
  have hhalf : 0 < δ/2 := by positivity
  let h (i : Fin (N+1)) : ℝ := ((i:ℕ)+1 : ℝ)*(δ/2)
  refine ⟨N+1,h,?_,?_,?_⟩
  · intro i j hij
    apply mul_lt_mul_of_pos_right _ hhalf
    have he : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    linarith
  · intro i
    apply mul_pos _ hhalf
    positivity
  · intro w hw
    let k := ⌊w/(δ/2)⌋₊
    have hk : (k:ℝ) ≤ w/(δ/2) := Nat.floor_le (div_nonneg hw.1 hhalf.le)
    have hk' : w/(δ/2) < (k:ℝ)+1 := Nat.lt_floor_add_one _
    have hkn : (k:ℝ) < N := hk.trans_lt ((div_le_div_of_nonneg_right hw.2 hhalf.le).trans_lt hN)
    have hkN : k < N+1 := by
      have : k < N := by exact_mod_cast hkn
      omega
    refine ⟨⟨k,hkN⟩,?_,?_⟩
    · change w ≤ ((k:ℝ)+1)*(δ/2)
      exact ((div_lt_iff₀ hhalf).mp hk').le
    · change ((k:ℝ)+1)*(δ/2)-w < δ
      have hkw := (le_div_iff₀ hhalf).mp hk
      nlinarith

end PackingSufficiencySupport.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_PlanarRotation
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology BigOperators
open Set Function MeasureTheory

theorem exists_hamiltonian_thin_grid {m : ℕ} (h : Fin m → ℝ)
    (hh : ∀ i, 0 < h i) (hmono : StrictMono h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (R : ℝ) (Ψ : HamiltonianDiskIsotopyFamily ℝ R),
      ∀ i x, radialArea x ≤ h i →
        0 < (Ψ.isotopy.map 0 1 x).1 ∧ (Ψ.isotopy.map 0 1 x).1 < h i+δ/2 ∧
        (Ψ.isotopy.map 0 1 x).2 ∈ Ioo 0 1 := by
  obtain ⟨L,w,c,hL,hw,hwmono,hareaL,hnestL,hplace⟩ :=
    exists_thin_rectangle_placement h hh hmono hδ
  let Y : Set ℝ := {0}
  let V (_ : ℝ) (i : Fin m) : Set ℝ := Ioo 0 (h i+δ/2)
  have hV (i : Fin m) : IsOpen {p : ℝ × ℝ | p.2 ∈ V p.1 i} :=
    isOpen_Ioo.preimage continuous_snd
  obtain ⟨q,k,hq,hq1,hk,hsquare,harea,hmargin⟩ :=
    exists_exact_area_rounded_margins (isCompact_singleton (x := (0:ℝ)))
      (fun _ : ℝ => c) continuous_const L w hwmono V hV
      (fun _ _ => ⟨hplace,hnestL⟩)
  let s : ℝ := 4/squeezedArea k
  have hs : 0 < s := div_pos (by norm_num) harea
  let C (i : Fin m) : Plane := (c i+L i/2,1/2)
  let a (i : Fin m) := s*L i/2
  let b (i : Fin m) := w i/2
  have ha i : 0 < a i := div_pos (mul_pos hs (hL i)) (by norm_num)
  have hb i : 0 < b i := div_pos (hw i).1 (by norm_num)
  have hmar := hmargin 0 (mem_singleton (0:ℝ))
  have hnest ⦃i j : Fin m⦄ (hij : i < j) :
      roundedBox k (C i) (a i) (b i) ⊆ interior (roundedBox k (C j) (a j) (b j)) := by
    apply roundedBox_nested_of_margins (ha i) (hb i) (ha j) (hb j) hsquare
    all_goals
      have hn := hmar.2.2 hij
      dsimp only [C,a,b]
      nlinarith only [hn.1,hn.2.1,hn.2.2]
  have hbound (i : Fin m) {x : Plane} (hx : x ∈ roundedBox k (C i) (a i) (b i)) :
      0 < x.1 ∧ x.1 < h i+δ/2 ∧ x.2 ∈ Ioo 0 1 := by
    obtain ⟨z,_,rfl⟩ := hx
    have hz := roundedMap_mem_openBox (ha i) (hb i) k (C i) z
    have he := hmar.2.1 i
    change (0 < c i+L i/2-s*L i/2 ∧ c i+L i/2-s*L i/2 < h i+δ/2) ∧
      (0 < c i+L i/2+s*L i/2 ∧ c i+L i/2+s*L i/2 < h i+δ/2) at he
    change (c i+L i/2-s*L i/2 < _ ∧ _ < c i+L i/2+s*L i/2) ∧
      (1/2-w i/2 < _ ∧ _ < 1/2+w i/2) at hz
    exact ⟨he.1.1.trans hz.1.1,hz.1.2.trans he.2.2,
      by linarith [hz.2.1,(hw i).2],by linarith [hz.2.2,(hw i).2]⟩
  have hvol (i : Fin m) : volume (roundedBox k (C i) (a i) (b i)) = ENNReal.ofReal (h i) := by
    rw [roundedBox_volume_eq (ha i).le (hb i).le]
    congr 1
    calc
      a i*b i*squeezedArea k = L i*w i := by
        dsimp [a,b,s]
        field_simp [harea.ne']
        ring
      _ = h i := hareaL i
  let r i := areaRadius (h i)
  have hr i : 0 < r i := areaRadius_pos (hh i)
  have hrmono : StrictMono r := fun i j hij =>
    areaRadius_strictMono (hh i).le (hh j).le (hmono hij)
  let f (i : Fin m) (p : ℝ × Plane) := normalizedRoundedMap k (C i) (a i) (b i) (r i) p.2
  have himage (i : Fin m) (y : ℝ) :
      (fun x => f i (y,x)) '' closedRoundDisk (r i) = roundedBox k (C i) (a i) (b i) :=
    normalizedRoundedMap_image (hr i) k (C i) (a i) (b i)
  let K := ⋃ i, roundedBox k (C i) (a i) (b i)
  have hK : IsCompact K := isCompact_iUnion (fun i => roundedBox_compact k (C i) (a i) (b i))
  obtain ⟨M,hM⟩ := (hK.image radialArea_smooth.continuous).bddAbove
  let T := max (M+1) (1+∑ i, h i)
  have hT : 0 < T := by
    have hs : 0 ≤ ∑ i, h i := Finset.sum_nonneg (fun i _ => (hh i).le)
    have hl := le_max_right (M+1) (1+∑ i, h i)
    dsimp [T] <;> linarith
  have hiT (i : Fin m) : h i < T := by
    have hi := Finset.single_le_sum (s := Finset.univ) (fun j _ => (hh j).le) (Finset.mem_univ i)
    have hl := le_max_right (M+1) (1+∑ i, h i)
    dsimp [T] <;> linarith
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_plane_disk_germs
    (Y := Y) (A := univ) isCompact_singleton (convex_singleton 0) isOpen_univ
    (subset_univ Y) 0 (mem_singleton 0) r hr hrmono f
    (fun i => ((normalizedRoundedMap_smooth k (C i) (a i) (b i) (r i)).comp contDiff_snd).contDiffOn)
    (fun i _ _ => normalizedRoundedMap_injective hk (ha i) (hb i) (hr i) (C i))
    (fun i _ _ x => normalizedRoundedMap_det_pos hk (ha i) (hb i) (hr i) (C i) x)
    (by intro i j hij y _; rw [himage,himage]; exact hnest hij)
    (areaRadius T) (areaRadius_pos hT)
    (fun i => areaRadius_strictMono (hh i).le hT.le (hiT i))
    (by
      intro i y _ x hx
      rw [himage] at hx
      rw [mem_roundDisk_areaRadius hT.le]
      have hm : radialArea x ≤ M := hM (mem_image_of_mem radialArea (mem_iUnion.mpr ⟨i,hx⟩))
      have ht := le_max_left (M+1) (1+∑ i, h i)
      dsimp [T] <;> linarith)
    (by intro i y _; rw [himage,hvol,volume_closedRoundDisk_areaRadius (hh i).le])
  refine ⟨areaRadius T,Ψ,?_⟩
  intro i x hx
  apply hbound i
  rw [←himage i 0,←hΨ i 0 (mem_singleton 0)]
  exact mem_image_of_mem _ ((mem_closedRoundDisk_areaRadius (hh i).le x).mpr hx)

theorem exists_thin_planar_embedding_bp240_oai {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ q : Plane ≃ₜ Plane, ContDiff ℝ ∞ q ∧ ContDiff ℝ ∞ q.symm ∧
      (∀ x v w, planarArea (fderiv ℝ q x v) (fderiv ℝ q x w) = planarArea v w) ∧
      ∀ x, radialArea x ≤ A →
        0 < (q x).1 ∧ (q x).1 < radialArea x+δ ∧ (q x).2 ∈ Ioo 0 1 := by
  obtain ⟨m,h,hmono,hh,hgrid⟩ := Comparison.exists_positive_area_grid hA
    (show 0 < δ/2 by positivity)
  obtain ⟨R,Ψ,hΨ⟩ := exists_hamiltonian_thin_grid h hh hmono hδ
  refine ⟨Ψ.isotopy.map 0 1,?_,?_,Ψ.symplectic 0 1,?_⟩
  · exact Ψ.isotopy.smooth.comp ((contDiff_const (c := ((0,1) : ℝ × ℝ))).prodMk contDiff_id)
  · exact Ψ.isotopy.inverse_smooth.comp ((contDiff_const (c := ((0,1) : ℝ × ℝ))).prodMk contDiff_id)
  · intro x hx
    have hx0 : 0 ≤ radialArea x := mul_nonneg Real.pi_pos.le (by
      dsimp [radiusSq] <;> positivity)
    obtain ⟨i,hi,hiδ⟩ := hgrid (radialArea x) ⟨hx0,hx⟩
    have hb := hΨ i x hi
    exact ⟨hb.1,by linarith [hb.2.1],hb.2.2⟩


end

open scoped ContDiff Topology
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_thin_planar_embedding_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_thin_planar_embedding_bp240_oai
