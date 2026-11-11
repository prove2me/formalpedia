-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:31.448836+00:00
-- url     : https://prove2.me/submissions/90f35829-3efc-44de-aae9-dda1b901a650

import Mathlib
import Definitions.Def_OAIQ240Bp019

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

theorem phaseSq_eq_zero_iff (z : PlanePhase ι) : phaseSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : (z i).1*(z i).1+(z i).2*(z i).2 ≤ phaseSq z := by
      rw [phaseSq,phaseDot_apply]
      exact Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2) (fun j _ =>
        add_nonneg (mul_self_nonneg (z j).1) (mul_self_nonneg (z j).2)) (Finset.mem_univ i)
    rw [hz] at hi
    apply Prod.ext <;> dsimp
    · nlinarith [sq_nonneg (z i).2]
    · nlinarith [sq_nonneg (z i).1]
  · rintro rfl
    simp [phaseSq]

theorem phaseSq_pos {z : PlanePhase ι} (hz : z ≠ 0) : 0 < phaseSq z :=
  lt_of_le_of_ne (phaseSq_nonneg z) (fun h => hz ((phaseSq_eq_zero_iff z).mp h.symm))

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

 theorem projection_contDiff : ContDiff ℂ ∞ projection := by
  exact (((contDiff_apply ℂ ℂ 0).comp contDiff_snd).sub contDiff_fst).prodMk
    (((contDiff_apply ℂ ℂ 1).comp contDiff_snd).sub contDiff_fst)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem weightedProjection_contDiff (D m : ℕ) : ContDiff ℂ ∞ (weightedProjection D m) := by
  apply ContDiff.prodMk (contDiff_fst.pow (D-m))
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd.pow (D-m)
  · exact (contDiff_fst.pow (D-m)).mul (contDiff_snd.pow m)
  · exact (contDiff_fst.pow m).mul (contDiff_snd.pow (D-m))

 theorem weightedPhaseInclusion_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) ∞ (weightedPhaseInclusion D m) :=
  (affinePhase 3).contDiff.contMDiff.comp
    (((weightedProjection_contDiff D m).restrict_scalars ℝ).contMDiff.comp
      ((projection_contDiff.restrict_scalars ℝ).contMDiff.comp
        (real_inclusion_contMDiff (parameters 0))))

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
open scoped BigOperators ComplexConjugate

 theorem complexArea_apply (z v : ℂ) : complexArea z v=z.re*v.im-z.im*v.re := by
  simp only [complexArea,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

 theorem complexArea_mul (s z v : ℂ) : complexArea (s*z) (s*v)=Complex.normSq s*complexArea z v := by
  unfold complexArea
  rw [map_mul]
  have he : conj s*conj z*(s*v)=(Complex.normSq s : ℂ)*(conj z*v) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [he]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

 theorem manifoldMapDifferential_comp {g : N → M} {f : P → N} {x : P}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x) :
    manifoldMapDifferential (E := E) (F := G) (g ∘ f) x=
      (manifoldMapDifferential (E := E) (F := F) g (f x)).comp (manifoldMapDifferential (E := F) (F := G) f x) :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mfderiv

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldFormTransport
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

section

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞
    (Prod.fst : M × V → M) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_snd_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,V) ∞
    (Prod.snd : M × V → V) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_snd

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,E) (Prod.fst : M × V → M) z=
      ContinuousLinearMap.fst ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_fst

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι : Type*} [Fintype ι]

theorem complexPairing_im (z v : ι → ℂ) :
    (complexPairing z v).im=phaseArea (complexCartesian z) (complexCartesian v) := by
  simp only [complexPairing,Complex.im_sum,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,phaseArea_apply,complexCartesian_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexAffineLift_smooth : ContDiff ℝ ∞ (complexAffineLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_const
  | some i => exact contDiff_apply ℝ ℂ i

theorem complexAffineLift_sq (z : ι → ℂ) :
    phaseSq (complexCartesian (complexAffineLift z))=1+phaseSq (complexCartesian z) := by
  rw [complexCartesian_sq,complexCartesian_sq]
  simp [Fintype.sum_option]

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ExponentialMoment
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem partition_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) :
    0<partition w a x := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (ha i) (Real.exp_pos _)
  · exact Finset.univ_nonempty

 omit [Nonempty ι] in
 theorem partition_contDiff (w : ι → E) (a : ι → ℝ) : ContDiff ℝ ∞ (partition w a) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (((innerSL ℝ (w i)).contDiff).exp)

 omit [Nonempty ι] in
 theorem partition_hasFDerivAt (w : ι → E) (a : ι → ℝ) (x : E) :
    HasFDerivAt (partition w a) (innerSL ℝ (gradient w a x)) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((innerSL ℝ (w i)).hasFDerivAt (x := x)).exp).const_mul (a i))
  convert! h using 1
  · ext y
    simp [partition]
  · simp only [gradient,map_sum,map_smul,smul_smul,innerSL_apply_apply]

 theorem partition_coercive [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) :
    Tendsto (partition w a) (cocompact E) atTop := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have hb (x : E) : a j*Real.exp (δ*‖x‖)≤partition w a x := by
    obtain ⟨i,hi⟩ := hw x
    calc
      a j*Real.exp (δ*‖x‖)≤a i*Real.exp (inner ℝ (w i) x) :=
        mul_le_mul (hj i (Finset.mem_univ i)) (Real.exp_le_exp.mpr hi)
          (Real.exp_pos _).le (ha i).le
      _≤partition w a x := by
        exact Finset.single_le_sum
          (fun k _ => (mul_pos (ha k) (Real.exp_pos (inner ℝ (w k) x))).le) (Finset.mem_univ i)
  exact tendsto_atTop_mono hb ((Real.tendsto_exp_atTop.comp
    (tendsto_norm_cocompact_atTop.const_mul_atTop hδ)).const_mul_atTop (ha j))

 theorem exists_gradient_zero [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) :
    ∃ x : E,gradient w a x=0 := by
  obtain ⟨x,hx⟩ := (partition_contDiff w a).continuous.exists_forall_le
    (partition_coercive ha hδ hw)
  refine ⟨x,?_⟩
  have hm : IsLocalMin (partition w a) x := Filter.Eventually.of_forall hx
  have hz := hm.hasFDerivAt_eq_zero (partition_hasFDerivAt w a x)
  have he := congrArg (fun L : E →L[ℝ] ℝ => L (gradient w a x)) hz
  change inner ℝ (gradient w a x) (gradient w a x)=0 at he
  exact inner_self_eq_zero.mp he

 theorem exp_difference_nonneg (u v : ℝ) :
    0≤(Real.exp u-Real.exp v)*(u-v) := by
  rcases le_total v u with h|h
  · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))
      (sub_nonpos.mpr h)

 theorem exp_difference_pos {u v : ℝ} (h : v<u) :
    0<(Real.exp u-Real.exp v)*(u-v) :=
  mul_pos (sub_pos.mpr (Real.exp_lt_exp.mpr h)) (sub_pos.mpr h)

 omit [Nonempty ι] in
 theorem gradient_zero_unique {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {δ : ℝ} (hδ : 0<δ)
    (hw : ∀ x : E,∃ i,δ*‖x‖≤ inner ℝ (w i) x) {x y : E}
    (hx : gradient w a x=0) (hy : gradient w a y=0) : x=y := by
  classical
  by_contra hxy
  have hd : 0<δ*‖x-y‖ := mul_pos hδ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  obtain ⟨j,hj⟩ := hw (x-y)
  have hjp : inner ℝ (w j) y< inner ℝ (w j) x := by
    rw [inner_sub_right] at hj
    linarith
  have hs : 0< ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y)) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ha i).le (exp_difference_nonneg _ _)
    · exact ⟨j,Finset.mem_univ j,mul_pos (ha j) (exp_difference_pos hjp)⟩
  have he : ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y))=
      inner ℝ (gradient w a x-gradient w a y) (x-y) := by
    simp only [gradient,inner_sub_left,sum_inner,real_inner_smul_left,inner_sub_right,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hx,hy,sub_self,inner_zero_left] at hs
  exact (lt_irrefl (0:ℝ)) hs

 omit [Nonempty ι] in
 theorem gradient_center (w : ι → E) (a : ι → ℝ) (p x : E) :
    gradient (fun i => w i-p) a x = Real.exp (-inner ℝ p x) •
      (gradient w a x-partition w a x • p) := by
  have he (i : ι) : (a i * Real.exp (inner ℝ (w i-p) x)) • (w i-p) =
      Real.exp (-inner ℝ p x) • ((a i*Real.exp (inner ℝ (w i) x)) • w i-
        (a i*Real.exp (inner ℝ (w i) x)) • p) := by
    rw [inner_sub_left,sub_eq_add_neg (inner ℝ (w i) x),Real.exp_add]
    simp only [smul_sub,smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp only [gradient,he,←Finset.smul_sum,Finset.sum_sub_distrib,←Finset.sum_smul,partition]

 theorem moment_eq_iff_gradient_center_zero {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (p x : E) :
    moment w a x=p ↔ gradient (fun i => w i-p) a x=0 := by
  rw [gradient_center,smul_eq_zero]
  simp only [Real.exp_ne_zero,false_or,sub_eq_zero]
  dsimp [moment]
  rw [inv_smul_eq_iff₀ (partition_pos ha x).ne']

 theorem exists_unique_moment [ProperSpace E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : E} (hp : Surrounds w p) : ∃! x,moment w a x=p := by
  obtain ⟨δ,hδ,hw⟩ := hp
  obtain ⟨x,hx⟩ := exists_gradient_zero ha hδ hw
  refine ⟨x,(moment_eq_iff_gradient_center_zero ha p x).mpr hx,?_⟩
  intro y hy
  exact gradient_zero_unique ha hδ hw ((moment_eq_iff_gradient_center_zero ha p y).mp hy) hx

 omit [Fintype ι] in
 theorem surrounds_of_interior {w : ι → E} {p : E}
    (hp : p∈interior (convexHull ℝ (range w))) : Surrounds w p := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  refine ⟨ε/2,half_pos hε,?_⟩
  intro v
  by_cases hv : v=0
  · subst v
    exact ⟨Classical.ofNonempty,by simp⟩
  have hvp : 0<‖v‖ := norm_pos_iff.mpr hv
  let z := p+((ε/2)/‖v‖) • v
  have hz : z∈convexHull ℝ (range w) := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (half_pos hε) hvp),
      div_mul_cancel₀ _ hvp.ne']
    linarith
  obtain ⟨y,⟨i,rfl⟩,hi⟩ := ((innerSL ℝ v).toLinearMap.convexOn convex_univ).exists_ge_of_mem_convexHull
    (subset_univ (range w)) hz
  refine ⟨i,?_⟩
  change inner ℝ v z≤ inner ℝ v (w i) at hi
  have he : inner ℝ v z=inner ℝ v p+(ε/2)*‖v‖ := by
    dsimp [z]
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  rw [he] at hi
  rw [inner_sub_left,real_inner_comm v (w i),real_inner_comm v p]
  linarith

 omit [Fintype ι] [Nonempty ι] in
 theorem surrounds_isOpen (w : ι → E) : IsOpen {p | Surrounds w p} := by
  apply Metric.isOpen_iff.mpr
  intro p hp
  obtain ⟨δ,hδ,hw⟩ := hp
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro q hq
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro v
  obtain ⟨i,hi⟩ := hw v
  refine ⟨i,?_⟩
  have hc := real_inner_le_norm (q-p) v
  have hnorm : ‖q-p‖<δ/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  have hmul := mul_le_mul_of_nonneg_right hnorm.le (norm_nonneg v)
  rw [inner_sub_left] at hi hc ⊢
  linarith

end
section

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem hessian_apply (w : ι → E) (a : ι → ℝ) (x v : E) :
    hessian w a x v=∑ i, (a i*Real.exp (inner ℝ (w i) x)*inner ℝ (w i) v) • w i := by
  simp [hessian]

 theorem gradient_hasFDerivAt (w : ι → E) (a : ι → ℝ) (x : E) :
    HasFDerivAt (gradient w a) (hessian w a x) x := by
  have h := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((((innerSL ℝ (w i)).hasFDerivAt (x := x)).exp).const_mul (a i)).smul_const (w i))
  convert! h using 1
  · ext y
    simp [gradient]
  · simp only [hessian,smul_smul,innerSL_apply_apply]

 theorem hessian_inner (w : ι → E) (a : ι → ℝ) (x v : E) :
    inner ℝ (hessian w a x v) v=
      ∑ i,(a i*Real.exp (inner ℝ (w i) x))*(inner ℝ (w i) v)^2 := by
  rw [hessian_apply,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left]
  ring

 theorem hessian_positive {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0) (x : E) {v : E} (hv : v≠0) :
    0< inner ℝ (hessian w a x v) v := by
  classical
  rw [hessian_inner]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_pos (ha i) (Real.exp_pos _)).le (sq_nonneg _)
  · obtain ⟨i,hi⟩ := hw v hv
    exact ⟨i,Finset.mem_univ i,mul_pos (mul_pos (ha i) (Real.exp_pos _)) (sq_pos_of_ne_zero hi)⟩

 theorem hessian_isInvertible [FiniteDimensional ℝ E] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0) (x : E) :
    (hessian w a x).IsInvertible := by
  have hi : Injective (hessian w a x) := by
    intro v u h
    by_contra hn
    have hp := hessian_positive ha hw x (sub_ne_zero.mpr hn)
    rw [map_sub,h,sub_self,inner_zero_left] at hp
    exact (lt_irrefl (0:ℝ)) hp
  let L := ContinuousLinearEquiv.ofBijective (hessian w a x)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨L,rfl⟩

 omit [Fintype ι] in
 theorem surrounds_separates {w : ι → E} {p : E} (hp : Surrounds w p)
    {v : E} (hv : v≠0) : ∃ i,inner ℝ (w i-p) v≠0 := by
  obtain ⟨δ,hδ,hw⟩ := hp
  obtain ⟨i,hi⟩ := hw v
  exact ⟨i,(lt_of_lt_of_le (mul_pos hδ (norm_pos_iff.mpr hv)) hi).ne'⟩

 theorem centeredGradient_contDiff (w : ι → E) :
    ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => gradient (fun i => w i-q.1.2) q.1.1 q.2) := by
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => q.1.1 i) := by fun_prop
  have hu : ContDiff ℝ ∞ (fun q : ((ι → ℝ) × E) × E => w i-q.1.2) := by fun_prop
  exact (ha.mul ((hu.inner ℝ contDiff_snd).exp)).smul hu

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem inverse_spec {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : moment w a (inverse w a p)=p :=
  invFun_eq (exists_unique_moment ha hp).exists

 theorem inverse_unique {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) {x : E} (hx : moment w a x=p) : x=inverse w a p :=
  (exists_unique_moment ha hp).unique hx (inverse_spec ha hp)

 omit [Nonempty ι] in
 theorem positiveCoefficients_isOpen : IsOpen {a : ι → ℝ | ∀ i,0<a i} := by
  have h : IsOpen (⋂ i : ι,{a : ι → ℝ | 0<a i}) :=
    isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  simp

 theorem inverse_contDiffAt {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => inverse w q.1 q.2) (a,p) := by
  let q := (a,p)
  let x := inverse w a p
  let F : ((ι → ℝ) × E) × E → E :=
    fun t => gradient (fun i => w i-t.1.2) t.1.1 t.2
  have hF : ContDiff ℝ ∞ F := centeredGradient_contDiff w
  have hpartial : (fderiv ℝ F (q,x)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × E) E)=
      hessian (fun i => w i-p) a x := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)))
    exact hc.unique (gradient_hasFDerivAt (fun i => w i-p) a x)
  have hinv : (fderiv ℝ F (q,x) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × E) E).IsInvertible := by
    rw [hpartial]
    exact hessian_isInvertible ha (fun _ hv => surrounds_separates hp hv) x
  have hzero : F (q,x)=0 :=
    (moment_eq_iff_gradient_center_zero ha p x).mp (inverse_spec ha hp)
  have hapos : ∀ᶠ t : (ι → ℝ) × E in 𝓝 q,∀ i,0<t.1 i := by
    apply (positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds
    exact ha
  have htpos : ∀ᶠ t : (ι → ℝ) × E in 𝓝 q,Surrounds w t.2 := by
    apply ((surrounds_isOpen w).preimage continuous_snd).mem_nhds
    exact hp
  have hloc := hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,hapos,htpos]
    with t ht hta htp
  rw [hzero] at ht
  have hm := (moment_eq_iff_gradient_center_zero hta t.2 _).mpr ht
  exact (inverse_unique hta htp hm).symm

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem monomial_nonneg (k : ℕ × ℕ) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0 ≤ monomial k r := mul_nonneg (pow_nonneg hr.1 _) (pow_nonneg hr.2 _)

theorem polynomial_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<polynomial k a r := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (ha i).le (monomial_nonneg _ hr)
  · obtain ⟨i,hi⟩ := hzero
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [hi,monomial] using ha i

theorem polynomial_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => polynomial k q.1 q.2) := by
  apply ContDiff.sum
  intro i _
  dsimp [monomial]
  fun_prop

theorem centered_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : ((ι → ℝ) × Plane) × Plane => centered k q.1.1 q.1.2 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> dsimp [monomial] <;> fun_prop

theorem centered_eq (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    centered k a p r=numerator k a r-polynomial k a r • p := by
  apply Prod.ext
  · change (∑ i, (((k i).1:ℝ)-p.1)*a i*monomial (k i) r)=
      (∑ i, ((k i).1:ℝ)*a i*monomial (k i) r)-(∑ i,a i*monomial (k i) r)*p.1
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · change (∑ i, (((k i).2:ℝ)-p.2)*a i*monomial (k i) r)=
      (∑ i, ((k i).2:ℝ)*a i*monomial (k i) r)-(∑ i,a i*monomial (k i) r)*p.2
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem centered_moment {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) : centered k a (moment k a r) r=0 := by
  rw [centered_eq,moment,smul_smul,mul_inv_cancel₀ hP,one_smul,sub_self]

theorem monomial_hasFDerivAt (k : ℕ × ℕ) (r : Plane) :
    HasFDerivAt (monomial k) (monomialDerivative k r) r := by
  have h := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.1).mul
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x:=r)).pow k.2)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [monomialDerivative]
  ring

theorem centered_hasFDerivAt (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    HasFDerivAt (centered k a p) (centeredDerivative k a p r) r := by
  convert! (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (monomial_hasFDerivAt (k i) r).const_mul
    ((((k i).1:ℝ)-p.1)*a i))).prodMk
    (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (monomial_hasFDerivAt (k i) r).const_mul
    ((((k i).2:ℝ)-p.2)*a i))) using 1
  all_goals try with_reducible_and_instances rfl
  ext v <;> simp [centered]

theorem zero_power_derivative (n : ℕ) :
    (n:ℝ)*(0:ℝ)^(n-1)=if n=1 then 1 else 0 := by
  rcases n with _|n
  · simp
  · rcases n with _|n
    · simp
    · simp

theorem monomial_axis (k : ℕ × ℕ) (t : ℝ) :
    monomial k (0,t)=if k.1=0 then t^k.2 else 0 := by
  by_cases h : k.1=0
  · simp [monomial,h]
  · simp [monomial,h,zero_pow h]

theorem monomialDerivative_axis (k : ℕ × ℕ) (t : ℝ) (v : Plane) :
    monomialDerivative k (0,t) v=
      (if k.1=1 then t^k.2 else 0)*v.1+
      (if k.1=0 then (k.2:ℝ)*t^(k.2-1) else 0)*v.2 := by
  simp only [monomialDerivative,add_apply,
    smul_apply,
    smul_eq_mul,zero_power_derivative]
  by_cases h0 : k.1=0
  · simp [h0]
  · by_cases h1 : k.1=1
    · simp [h1]
    · simp [h0,h1,zero_pow h0]

theorem centered_axis_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) (t : ℝ) :
    (centered k a p (0,t)).2=∑ i,(((k i).2:ℝ)-p.2)*faceMass (k i) (a i) t := by
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_axis]
  by_cases h : (k i).1=0 <;> simp [faceMass,h,mul_assoc]

theorem centeredDerivative_axis_fst (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ) (v : Plane) :
    (centeredDerivative k a (0,p) (0,t) v).1=transverse k a t*v.1 := by
  simp only [centeredDerivative,ContinuousLinearMap.prod_apply,
    sum_apply,smul_apply,smul_eq_mul,
    monomialDerivative_axis,sub_zero,transverse,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : (k i).1=0
  · simp [h0]
  · by_cases h1 : (k i).1=1
    · simp [h1,mul_assoc]
    · simp [h0,h1]

theorem centeredDerivative_axis_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t u : ℝ) :
    (centeredDerivative k a (0,p) (0,t) (0,u)).2=active k a p t*u := by
  simp only [centeredDerivative,ContinuousLinearMap.prod_apply,
    sum_apply,smul_apply,smul_eq_mul,
    monomialDerivative_axis,mul_zero,zero_add,active,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (k i).1=0 <;> simp [h,mul_assoc]

theorem transverse_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(1,0)) {t : ℝ} (ht : 0≤t) : 0<transverse k a t := by
  classical
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact mul_nonneg (ha i).le (pow_nonneg ht _)
    · rfl
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem nat_mul_power (n : ℕ) (t : ℝ) :
    (n:ℝ)*t^(n-1)*t=(n:ℝ)*t^n := by
  rcases n with _|n
  · simp
  · simp only [Nat.succ_sub_one,pow_succ]
    ring

theorem active_variance (k : ι → ℕ × ℕ) (a : ι → ℝ) (p t : ℝ)
    (hz : (centered k a (0,p) (0,t)).2=0) :
    active k a p t*t=∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t := by
  rw [centered_axis_snd] at hz
  have he : active k a p t*t =
      (∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t)+
        p*(∑ i,(((k i).2:ℝ)-p)*faceMass (k i) (a i) t) := by
    rw [active,Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (k i).1=0
    · simp only [ite_eq_left h,faceMass]
      calc
        (((k i).2:ℝ)-p)*a i*((k i).2:ℝ)*t^((k i).2-1)*t =
            ((((k i).2:ℝ)-p)*a i)*(((k i).2:ℝ)*t^((k i).2-1)*t) := by ring
        _ = _ := by rw [nat_mul_power]; ring
    · simp [h,faceMass]
  simpa only [hz,mul_zero,add_zero] using he

theorem active_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) (he : ∃ i,k i=(0,1)) {p t : ℝ} (ht : 0<t)
    (hz : (centered k a (0,p) (0,t)).2=0) : 0<active k a p t := by
  have hV : 0<∑ i,(((k i).2:ℝ)-p)^2*faceMass (k i) (a i) t := by
    classical
    apply Finset.sum_pos'
    · intro i _
      apply mul_nonneg (sq_nonneg _)
      unfold faceMass
      split_ifs
      · exact mul_nonneg (ha i).le (pow_nonneg ht.le _)
      · rfl
    · by_cases hp : p=0
      · obtain ⟨i,hi⟩ := he
        exact ⟨i,Finset.mem_univ i,by simpa [faceMass,hi,hp] using mul_pos (ha i) ht⟩
      · obtain ⟨i,hi⟩ := hzero
        refine ⟨i,Finset.mem_univ i,?_⟩
        simpa [faceMass,hi] using mul_pos (sq_pos_of_ne_zero hp) (ha i)
  rw [← active_variance k a p t hz] at hV
  exact (mul_pos_iff_of_pos_right ht).mp hV

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSlopes
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem slopeNumerator_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => slopeNumerator k q.1 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> fun_prop

theorem slope_contDiffAt {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 q.2) (a,r) :=
  ((polynomial_contDiff k).contDiffAt.inv hP).smul (slopeNumerator_contDiff k).contDiffAt

theorem slopeNumerator_fst_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(1,0)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<(slopeNumerator k a r).1 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i).le)
      (pow_nonneg hr.1 _)) (pow_nonneg hr.2 _)
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem slopeNumerator_snd_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(0,1)) {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    0<(slopeNumerator k a r).2 := by
  classical
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i).le)
      (pow_nonneg hr.1 _)) (pow_nonneg hr.2 _)
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem slope_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (hzero : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {r : Plane} (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) : 0<(slope k a r).1 ∧ 0<(slope k a r).2 := by
  have hP := inv_pos.mpr (polynomial_pos ha hzero hr)
  exact ⟨mul_pos hP (slopeNumerator_fst_pos ha he0 hr),
    mul_pos hP (slopeNumerator_snd_pos ha he1 hr)⟩

theorem moment_eq_radius_slope (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    moment k a r=(r.1*(slope k a r).1,r.2*(slope k a r).2) := by
  have h0 : (numerator k a r).1=r.1*(slopeNumerator k a r).1 := by
    change (∑ i,((k i).1:ℝ)*a i*monomial (k i) r)=
      r.1*(∑ i,((k i).1:ℝ)*a i*r.1^((k i).1-1)*r.2^(k i).2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold monomial
    calc
      _=a i*r.2^(k i).2*(((k i).1:ℝ)*r.1^(k i).1) := by ring
      _=_ := by rw [← nat_mul_power]; ring
  have h1 : (numerator k a r).2=r.2*(slopeNumerator k a r).2 := by
    change (∑ i,((k i).2:ℝ)*a i*monomial (k i) r)=
      r.2*(∑ i,((k i).2:ℝ)*a i*r.1^(k i).1*r.2^((k i).2-1))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold monomial
    calc
      _=a i*r.1^(k i).1*(((k i).2:ℝ)*r.2^(k i).2) := by ring
      _=_ := by rw [← nat_mul_power]; ring
  apply Prod.ext
  · change (polynomial k a r)⁻¹*(numerator k a r).1=
      r.1*((polynomial k a r)⁻¹*(slopeNumerator k a r).1)
    rw [h0]
    ring
  · change (polynomial k a r)⁻¹*(numerator k a r).2=
      r.2*((polynomial k a r)⁻¹*(slopeNumerator k a r).2)
    rw [h1]
    ring

theorem moment_eq_of_centered {k : ι → ℕ × ℕ} {a : ι → ℝ} {p r : Plane}
    (hP : polynomial k a r≠0) (hz : centered k a p r=0) : moment k a r=p := by
  rw [centered_eq,sub_eq_zero] at hz
  rw [moment,hz,smul_smul,inv_mul_cancel₀ hP,one_smul]

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Function

 theorem openTrapezoid_isOpen (A B : ℝ) : IsOpen (openTrapezoid A B) := by
  have hc (j : Fin 2) : Continuous (fun p : MomentPlane => p j) := by fun_prop
  exact ((isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt (hc 0) continuous_const).inter
      ((isOpen_lt continuous_const (hc 1)).inter
        (isOpen_lt ((hc 0).add (hc 1)) continuous_const))))

 theorem trapezoid_mem_convexHull {A B : ℝ} {p : MomentPlane} (hp : p∈openTrapezoid A B) :
    p∈convexHull ℝ (range (trapezoidCorners A B)) := by
  have hA : 0<A := hp.1.trans hp.2.1
  have hB : 0<B-p 0 := by linarith [hp.2.2.1,hp.2.2.2]
  let l := p 0/A
  let t := p 1/(B-p 0)
  have hl0 : 0<l := div_pos hp.1 hA
  have hl1 : l<1 := (div_lt_one hA).mpr hp.2.1
  have ht0 : 0<t := div_pos hp.2.2.1 hB
  have ht1 : t<1 := (div_lt_one hB).mpr (by linarith [hp.2.2.2])
  let c : Fin 4 → ℝ := ![(1-l)*(1-t),l*(1-t),l*t,(1-l)*t]
  apply mem_convexHull_of_exists_fintype c (trapezoidCorners A B)
  · intro i
    fin_cases i <;> dsimp [c] <;> positivity
  · simp only [c,Fin.sum_univ_succ]
    dsimp
    ring
  · intro i
    exact mem_range_self i
  · ext j
    fin_cases j <;>
      simp [c,trapezoidCorners,planeVector,Fin.sum_univ_succ,l,t] <;>
      field_simp <;> ring

 theorem trapezoid_interior {ι : Type*} {w : ι → MomentPlane} {A B : ℝ}
    (hw : range (trapezoidCorners A B)⊆range w) {p : MomentPlane}
    (hp : p∈openTrapezoid A B) : p∈interior (convexHull ℝ (range w)) := by
  have hsub : openTrapezoid A B⊆convexHull ℝ (range w) := by
    intro q hq
    exact convexHull_mono hw (trapezoid_mem_convexHull hq)
  exact interior_maximal hsub (openTrapezoid_isOpen A B) hp

 theorem trapezoidWeight_corners {A B : ℕ} (hAB : A≤B) :
    range (trapezoidCorners A B)⊆range (trapezoidWeight A B) := by
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · refine ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]
  · refine ⟨⟨(⟨A,by omega⟩,⟨0,by omega⟩),by simp [hAB]⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]
  · refine ⟨⟨(⟨A,by omega⟩,⟨B-A,by omega⟩),by simp [Nat.add_sub_of_le hAB]⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners,Nat.cast_sub hAB]
  · refine ⟨⟨(⟨0,by omega⟩,⟨B,by omega⟩),by simp⟩,?_⟩
    simp [trapezoidWeight,trapezoidCorners]

 theorem trapezoidWeight_surrounds {A B : ℕ} (hAB : A≤B) {p : MomentPlane}
    (hp : p∈openTrapezoid A B) : Surrounds (trapezoidWeight A B) p :=
  surrounds_of_interior (trapezoid_interior (trapezoidWeight_corners hAB) hp)

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem expRadius_logRadius {r : Plane} (hr : 0 < r.1 ∧ 0 < r.2) :
    expRadius (logRadius r)=r := by
  apply Prod.ext <;> simp [expRadius,logRadius,planeVector,Real.exp_log,hr.1,hr.2]

theorem monomial_expRadius (k : ℕ × ℕ) (x : MomentPlane) :
    monomial k (expRadius x)=Real.exp (inner ℝ (planeVector k.1 k.2) x) := by
  simp [monomial,expRadius,planeVector,PiLp.inner_apply,Fin.sum_univ_succ,
    ← Real.exp_nat_mul,← Real.exp_add,mul_comm]

theorem polynomial_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) :
    polynomial k a (expRadius x)=partition (weight k) a x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_expRadius]
  rfl

theorem moment_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) :
    planeVector (moment k a (expRadius x)).1 (moment k a (expRadius x)).2=
      FiniteMoment.moment (weight k) a x := by
  rw [FiniteMoment.moment,← polynomial_expRadius]
  ext j
  fin_cases j <;>
    simp [moment,numerator,gradient,weight,planeVector,monomial_expRadius,
      mul_assoc,mul_comm,mul_left_comm]

theorem exists_positive_radial_solution [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : Plane} (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    ∃ r : Plane, (0 < r.1 ∧ 0 < r.2) ∧ moment k a r=p := by
  let x := inverse (weight k) a (planeVector p.1 p.2)
  refine ⟨expRadius x,⟨Real.exp_pos _,Real.exp_pos _⟩,?_⟩
  have he := moment_expRadius k a x
  rw [inverse_spec ha hp] at he
  exact Prod.ext (congrArg (fun z : MomentPlane => z 0) he)
    (congrArg (fun z : MomentPlane => z 1) he)

theorem moment_axis_fst (k : ι → ℕ × ℕ) (a : ι → ℝ) (t : ℝ) :
    (moment k a (0,t)).1=0 := by
  change (polynomial k a (0,t))⁻¹*(∑ i,((k i).1:ℝ)*a i*monomial (k i) (0,t))=0
  have h : (∑ i,((k i).1:ℝ)*a i*monomial (k i) (0,t))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [monomial_axis]
    by_cases h : (k i).1=0 <;> simp [h]
  rw [h,mul_zero]

theorem moment_origin (k : ι → ℕ × ℕ) (a : ι → ℝ) : moment k a (0,0)=(0,0) := by
  apply Prod.ext
  · exact moment_axis_fst k a 0
  · change (polynomial k a (0,0))⁻¹*(∑ i,((k i).2:ℝ)*a i*monomial (k i) (0,0))=0
    have h : (∑ i,((k i).2:ℝ)*a i*monomial (k i) (0,0))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : (k i).2=0
      · simp [monomial,h]
      · simp [monomial,zero_pow h]
    rw [h,mul_zero]

theorem active_origin_pos {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (he : ∃ i,k i=(0,1)) : 0<active k a 0 0 := by
  classical
  have heq : active k a 0 0=∑ i,if (k i).1=0 ∧ (k i).2=1 then a i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (k i).1=0
    · simp only [ite_eq_left h,sub_zero]
      have hmul : ((k i).2:ℝ)*a i*((k i).2:ℝ)*(0:ℝ)^((k i).2-1)=
          ((k i).2:ℝ)*a i*(((k i).2:ℝ)*(0:ℝ)^((k i).2-1)) := by ring
      rw [hmul,zero_power_derivative]
      by_cases h1 : (k i).2=1 <;> simp [h,h1]
    · simp [h]
  rw [heq]
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact (ha i).le
    · rfl
  · obtain ⟨i,hi⟩ := he
    exact ⟨i,Finset.mem_univ i,by simpa [hi] using ha i⟩

theorem centeredDerivative_axis_isInvertible {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    (centeredDerivative k a (moment k a (0,t)) (0,t)).IsInvertible := by
  let p := (moment k a (0,t)).2
  have hm : moment k a (0,t)=(0,p) := Prod.ext (moment_axis_fst k a t) rfl
  rw [hm]
  have hz : (centered k a (0,p) (0,t)).2=0 := by
    have h := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
    rw [hm] at h
    exact congrArg Prod.snd h
  have hA : 0<transverse k a t := transverse_pos ha he0 ht
  have hB : 0<active k a p t := by
    rcases eq_or_lt_of_le ht with ht0|htp
    · have hp : p=0 := by simp [p,← ht0,moment_origin]
      rw [← ht0,hp]
      exact active_origin_pos ha he1
    · exact active_pos ha hzero he1 htp hz
  have hker : ∀ v,centeredDerivative k a (0,p) (0,t) v=0 → v=0 := by
    intro v hv
    have h0 := congrArg Prod.fst hv
    rw [centeredDerivative_axis_fst] at h0
    change transverse k a t*v.1=0 at h0
    have hv0 : v.1=0 := (mul_eq_zero.mp h0).resolve_left hA.ne'
    have heq : v=(0,v.2) := Prod.ext hv0 rfl
    have h1 := congrArg Prod.snd hv
    rw [heq,centeredDerivative_axis_snd] at h1
    change active k a p t*v.2=0 at h1
    exact Prod.ext hv0 ((mul_eq_zero.mp h1).resolve_left hB.ne')
  have hi : Injective (centeredDerivative k a (0,p) (0,t)) := by
    intro v u h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,h,sub_self]
  let L := ContinuousLinearEquiv.ofBijective (centeredDerivative k a (0,p) (0,t))
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi))
  exact ⟨L,rfl⟩

theorem exists_smooth_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (0,t))=(0,t) ∧
      ContDiffAt ℝ ∞ f (a,moment k a (0,t)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (0,t)),centered k q.1 q.2 (f q)=0 := by
  let q := (a,moment k a (0,t))
  let r : Plane := (0,t)
  let F : ((ι → ℝ) × Plane) × Plane → Plane := fun s => centered k s.1.1 s.1.2 s.2
  have hF : ContDiff ℝ ∞ F := centered_contDiff k
  have hpartial : (fderiv ℝ F (q,r)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane)=
      centeredDerivative k a (moment k a (0,t)) r := by
    have hc := ((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (q,r)).hasFDerivAt.comp r
      ((hasFDerivAt_const q r).prodMk (hasFDerivAt_id r)))
    exact hc.unique (centered_hasFDerivAt k a (moment k a (0,t)) r)
  have hinv : (fderiv ℝ F (q,r) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane).IsInvertible := by
    rw [hpartial]
    exact centeredDerivative_axis_isInvertible ha hzero he0 he1 ht
  have hz : F (q,r)=0 := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
  refine ⟨hF.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_,
    hF.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv,?_⟩
  · exact hF.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv
  · simpa only [hz] using hF.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hinv

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Function

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exp_difference_strict {u v : ℝ} (h : u≠v) :
    0<(Real.exp u-Real.exp v)*(u-v) := by
  rcases lt_or_gt_of_ne h with hlt|hgt
  · have h := exp_difference_pos hlt
    nlinarith
  · exact exp_difference_pos hgt

theorem gradient_zero_unique_of_separates {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i) v≠0)
    {x y : E} (hx : gradient w a x=0) (hy : gradient w a y=0) : x=y := by
  classical
  by_contra hxy
  obtain ⟨j,hj⟩ := hw (x-y) (sub_ne_zero.mpr hxy)
  have hjn : inner ℝ (w j) x≠inner ℝ (w j) y := by
    rwa [inner_sub_right,sub_ne_zero] at hj
  have hs : 0<∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y)) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ha i).le (exp_difference_nonneg _ _)
    · exact ⟨j,Finset.mem_univ j,mul_pos (ha j) (exp_difference_strict hjn)⟩
  have he : ∑ i,a i*((Real.exp (inner ℝ (w i) x)-Real.exp (inner ℝ (w i) y))*
      (inner ℝ (w i) x-inner ℝ (w i) y))=
      inner ℝ (gradient w a x-gradient w a y) (x-y) := by
    simp only [gradient,inner_sub_left,sum_inner,real_inner_smul_left,inner_sub_right,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hx,hy,sub_self,inner_zero_left] at hs
  exact (lt_irrefl (0:ℝ)) hs

theorem moment_unique_of_separates [Nonempty ι] {w : ι → E} {a : ι → ℝ}
    (ha : ∀ i,0<a i) {p : E}
    (hw : ∀ v : E,v≠0 → ∃ i,inner ℝ (w i-p) v≠0)
    {x y : E} (hx : moment w a x=p) (hy : moment w a y=p) : x=y :=
  gradient_zero_unique_of_separates ha hw
    ((moment_eq_iff_gradient_center_zero ha p x).mp hx)
    ((moment_eq_iff_gradient_center_zero ha p y).mp hy)

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem sum_face (k : ι → ℕ × ℕ) (f : ι → ℝ) :
    (∑ i, if (k i).1=0 then f i else 0)=∑ i : Face k,f i.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

theorem polynomial_face_exp (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    polynomial k a (0,Real.exp x)=partition (faceWeight k) (fun i => a i.val) x := by
  calc
    _=∑ i,if (k i).1=0 then a i*Real.exp (((k i).2:ℝ)*x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [monomial_axis]
      by_cases h : (k i).1=0 <;> simp [h,Real.exp_nat_mul]
    _=_ := by
      rw [sum_face]
      apply Finset.sum_congr rfl
      intro i _
      simp [faceWeight,mul_comm]

theorem numerator_face_exp_snd (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    (numerator k a (0,Real.exp x)).2=
      gradient (faceWeight k) (fun i => a i.val) x := by
  calc
    _=∑ i,if (k i).1=0 then ((k i).2:ℝ)*a i*Real.exp (((k i).2:ℝ)*x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [monomial_axis]
      by_cases h : (k i).1=0 <;> simp [h,Real.exp_nat_mul]
    _=_ := by
      rw [sum_face]
      apply Finset.sum_congr rfl
      intro i _
      simp [faceWeight,mul_comm,mul_left_comm,mul_assoc]

theorem moment_face_exp (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : ℝ) :
    moment k a (0,Real.exp x)=
      (0,FiniteMoment.moment (faceWeight k) (fun i => a i.val) x) := by
  apply Prod.ext
  · exact moment_axis_fst k a _
  · change (polynomial k a (0,Real.exp x))⁻¹*(numerator k a (0,Real.exp x)).2=_
    rw [polynomial_face_exp,numerator_face_exp_snd]
    rfl

omit [Fintype ι] in
theorem interval_surrounds {w : ι → ℝ} {B p : ℝ}
    (h0 : ∃ i,w i=0) (hB : ∃ i,w i=B) (hp : 0<p ∧ p<B) : Surrounds w p := by
  refine ⟨min p (B-p),lt_min hp.1 (sub_pos.mpr hp.2),?_⟩
  intro v
  rcases le_total 0 v with hv|hv
  · obtain ⟨i,hi⟩ := hB
    refine ⟨i,?_⟩
    simp only [hi,Real.norm_eq_abs,abs_of_nonneg hv]
    change min p (B-p)*v≤v*(B-p)
    nlinarith [min_le_right p (B-p)]
  · obtain ⟨i,hi⟩ := h0
    refine ⟨i,?_⟩
    simp only [hi,Real.norm_eq_abs,abs_of_nonpos hv,zero_sub]
    change min p (B-p)*(-v)≤v*(-p)
    nlinarith [min_le_left p (B-p)]

omit [Fintype ι] in
theorem interval_separates {w : ι → ℝ} {B : ℝ} (hB : B≠0)
    (h0 : ∃ i,w i=0) (h1 : ∃ i,w i=B) (p : ℝ) {v : ℝ} (hv : v≠0) :
    ∃ i,inner ℝ (w i-p) v≠0 := by
  by_cases hp : p=0
  · obtain ⟨i,hi⟩ := h1
    refine ⟨i,?_⟩
    simpa [hi,hp] using mul_ne_zero hv hB
  · obtain ⟨i,hi⟩ := h0
    refine ⟨i,?_⟩
    simpa [hi] using mul_ne_zero hv (neg_ne_zero.mpr hp)

theorem exists_axis_solution {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) {B : ℕ} (hB : ∃ i,k i=(0,B)) {p : ℝ}
    (hp : 0<p ∧ p<B) : ∃ t : ℝ,0<t ∧ moment k a (0,t)=(0,p) := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨iB,hiB⟩ := hB
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  have hw0 : ∃ i : Face k,faceWeight k i=0 := ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
  have hwB : ∃ i : Face k,faceWeight k i=(B:ℝ) := ⟨⟨iB,by simp [hiB]⟩,by simp [faceWeight,hiB]⟩
  obtain ⟨x,hx,_⟩ := exists_unique_moment (fun i : Face k => ha i.val)
    (interval_surrounds hw0 hwB hp)
  exact ⟨Real.exp x,Real.exp_pos _,by rw [moment_face_exp,hx]⟩

theorem positive_axis_unique {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (h1 : ∃ i,k i=(0,1)) {t u p : ℝ} (ht : 0<t) (hu : 0<u)
    (htp : moment k a (0,t)=(0,p)) (hup : moment k a (0,u)=(0,p)) : t=u := by
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := h1
  let : Nonempty (Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  have hw0 : ∃ i : Face k,faceWeight k i=0 := ⟨⟨i0,by simp [hi0]⟩,by simp [faceWeight,hi0]⟩
  have hw1 : ∃ i : Face k,faceWeight k i=(1:ℝ) := ⟨⟨i1,by simp [hi1]⟩,by simp [faceWeight,hi1]⟩
  have hmt : FiniteMoment.moment (faceWeight k) (fun i => a i.val) (Real.log t)=p := by
    have h := moment_face_exp k a (Real.log t)
    rw [Real.exp_log ht,htp] at h
    exact (congrArg Prod.snd h).symm
  have hmu : FiniteMoment.moment (faceWeight k) (fun i => a i.val) (Real.log u)=p := by
    have h := moment_face_exp k a (Real.log u)
    rw [Real.exp_log hu,hup] at h
    exact (congrArg Prod.snd h).symm
  have he := moment_unique_of_separates (fun i : Face k => ha i.val)
    (fun v hv => interval_separates one_ne_zero hw0 hw1 p hv) hmt hmu
  have h := congrArg Real.exp he
  simpa only [Real.exp_log ht,Real.exp_log hu] using h

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_RadialSwap
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.FiniteMoment.Radial

section

open scoped BigOperators Topology ContDiff
open Set Filter Function
variable {ι : Type*} [Fintype ι]

theorem polynomial_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    polynomial (fun i => (k i).swap) a r.swap=polynomial k a r := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [monomial,Prod.fst_swap,Prod.snd_swap]
  ring

theorem numerator_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    numerator (fun i => (k i).swap) a r.swap=(numerator k a r).swap := by
  apply Prod.ext <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals simp only [monomial,Prod.fst_swap,Prod.snd_swap]; ring

theorem moment_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    moment (fun i => (k i).swap) a r.swap=(moment k a r).swap := by
  unfold moment
  rw [polynomial_swap,numerator_swap]
  rfl

theorem centered_swap (k : ι → ℕ × ℕ) (a : ι → ℝ) (p r : Plane) :
    centered (fun i => (k i).swap) a p.swap r.swap=(centered k a p r).swap := by
  apply Prod.ext <;> apply Finset.sum_congr rfl <;> intro i _
  all_goals simp only [monomial,Prod.fst_swap,Prod.snd_swap]; ring

theorem exists_smooth_other_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (t,0))=(t,0) ∧
      ContDiffAt ℝ ∞ f (a,moment k a (t,0)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (t,0)),centered k q.1 q.2 (f q)=0 := by
  have hzero' : ∃ i,(k i).swap=(0,0) := by
    obtain ⟨i,hi⟩ := hzero
    exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by
    obtain ⟨i,hi⟩ := he1
    exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by
    obtain ⟨i,hi⟩ := he0
    exact ⟨i,by simp [hi]⟩
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_axis_radial_solution ha hzero' he0' he1' ht
  have hm : moment (fun i => (k i).swap) a (0,t)=(moment k a (t,0)).swap :=
    moment_swap k a (t,0)
  rw [hm] at hf hfs hfe
  let F : (ι → ℝ) × Plane → Plane := fun q => (f (q.1,q.2.swap)).swap
  have hswap : ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap)) := by
    change ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,(q.2.2,q.2.1)))
    fun_prop
  refine ⟨F,?_,?_,?_⟩
  · dsimp [F]
    rw [hf]
    rfl
  · have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => f (q.1,q.2.swap))
        (a,moment k a (t,0)) := hfs.comp (a,moment k a (t,0)) hswap.contDiffAt
    exact hc.snd.prodMk hc.fst
  · have htend : Tendsto (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap))
        (𝓝 (a,moment k a (t,0))) (𝓝 (a,(moment k a (t,0)).swap)) :=
      hswap.continuous.continuousAt
    have he := htend.eventually hfe
    filter_upwards [he] with q hq
    have h := congrArg Prod.swap hq
    have hr : centered k q.1 q.2 (F q)=
        (centered (fun i => (k i).swap) q.1 q.2.swap (f (q.1,q.2.swap))).swap := by
      have hh := centered_swap k q.1 q.2 (F q)
      simp only [F,Prod.swap_swap] at hh
      exact (congrArg Prod.swap hh).symm
    rw [hr,h]
    rfl




theorem basis_weights_separate {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) (p : MomentPlane)
    {v : MomentPlane} (hv : v≠0) : ∃ i,inner ℝ (weight k i-p) v≠0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨i0,hi0⟩ := h0
  obtain ⟨i1,hi1⟩ := he0
  obtain ⟨i2,hi2⟩ := he1
  have hp : inner ℝ p v=0 := by
    have h := hn i0
    have hw : weight k i0=0 := by ext j; fin_cases j <;> simp [weight,hi0,planeVector]
    simpa only [hw,zero_sub,inner_neg_left,neg_eq_zero] using h
  have hv0 : v 0=0 := by
    have h := hn i1
    simpa [inner_sub_left,hp,weight,hi1,planeVector,PiLp.inner_apply,Fin.sum_univ_succ] using h
  have hv1 : v 1=0 := by
    have h := hn i2
    simpa [inner_sub_left,hp,weight,hi2,planeVector,PiLp.inner_apply,Fin.sum_univ_succ] using h
  apply hv
  ext j
  fin_cases j <;> assumption

theorem positive_radial_unique_basis {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {r s : Plane} (hr : 0 < r.1 ∧ 0 < r.2) (hs : 0 < s.1 ∧ 0 < s.2)
    (he : moment k a r=moment k a s) : r=s := by
  let : Nonempty ι := ⟨h0.choose⟩
  let p := planeVector (moment k a r).1 (moment k a r).2
  have hre : FiniteMoment.moment (weight k) a (logRadius r)=p := by
    rw [← moment_expRadius,expRadius_logRadius hr]
  have hse : FiniteMoment.moment (weight k) a (logRadius s)=p := by
    rw [← moment_expRadius,expRadius_logRadius hs,← he]
  have hh := moment_unique_of_separates ha (fun v hv => basis_weights_separate h0 he0 he1 p hv) hre hse
  have h := congrArg expRadius hh
  simpa only [expRadius_logRadius hr,expRadius_logRadius hs] using h

theorem moment_zero_coordinates {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) :
    ((moment k a r).1=0 ↔ r.1=0) ∧ ((moment k a r).2=0 ↔ r.2=0) := by
  have hs := slope_pos ha h0 he0 he1 hr
  rw [moment_eq_radius_slope]
  exact ⟨mul_eq_zero_iff_right hs.1.ne',mul_eq_zero_iff_right hs.2.ne'⟩

theorem moment_injective_quadrant {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) :
    InjOn (moment k a) {r : Plane | 0 ≤ r.1 ∧ 0 ≤ r.2} := by
  intro r hr s hs he
  have hzr := moment_zero_coordinates ha h0 he0 he1 hr
  have hzs := moment_zero_coordinates ha h0 he0 he1 hs
  have hz0 : r.1=0 ↔ s.1=0 := hzr.1.symm.trans ((congrArg Prod.fst he) ▸ hzs.1)
  have hz1 : r.2=0 ↔ s.2=0 := hzr.2.symm.trans ((congrArg Prod.snd he) ▸ hzs.2)
  by_cases hr0 : r.1=0
  · have hs0 := hz0.mp hr0
    by_cases hr1 : r.2=0
    · exact Prod.ext (hr0.trans hs0.symm) (hr1.trans (hz1.mp hr1).symm)
    · have hrp : 0 < r.2 := lt_of_le_of_ne hr.2 (Ne.symm hr1)
      have hsp : 0 < s.2 := lt_of_le_of_ne hs.2 (Ne.symm (fun h => hr1 (hz1.mpr h)))
      have hrr : r=(0,r.2) := Prod.ext hr0 rfl
      have hss : s=(0,s.2) := Prod.ext hs0 rfl
      have hp : moment k a (0,r.2)=(0,(moment k a (0,r.2)).2) :=
        Prod.ext (moment_axis_fst k a _) rfl
      have hps : moment k a (0,s.2)=(0,(moment k a (0,r.2)).2) := by
        rw [← hss,← he,hrr]
        exact hp
      exact Prod.ext (hr0.trans hs0.symm) (positive_axis_unique ha h0 he1 hrp hsp hp hps)
  · have hs0 : s.1≠0 := fun h => hr0 (hz0.mpr h)
    have hrp : 0 < r.1 := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hsp : 0 < s.1 := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    by_cases hr1 : r.2=0
    · have hs1 := hz1.mp hr1
      have h0' : ∃ i,(k i).swap=(0,0) := by obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
      have h1' : ∃ i,(k i).swap=(0,1) := by obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
      have hrr : r.swap=(0,r.1) := Prod.ext hr1 rfl
      have hss : s.swap=(0,s.1) := Prod.ext hs1 rfl
      have hes : moment (fun i => (k i).swap) a r.swap=moment (fun i => (k i).swap) a s.swap := by
        rw [moment_swap,moment_swap,he]
      rw [hrr,hss] at hes
      have hp : moment (fun i => (k i).swap) a (0,r.1)=
          (0,(moment (fun i => (k i).swap) a (0,r.1)).2) :=
        Prod.ext (moment_axis_fst _ a _) rfl
      exact Prod.ext (positive_axis_unique ha h0' h1' hrp hsp hp (hes.symm.trans hp))
        (hr1.trans hs1.symm)
    · exact positive_radial_unique_basis ha h0 he0 he1
        ⟨hrp,lt_of_le_of_ne hr.2 (Ne.symm hr1)⟩
        ⟨hsp,lt_of_le_of_ne hs.2 (Ne.symm (fun h => hr1 (hz1.mpr h)))⟩ he




theorem exists_smooth_boundary_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),centered k q.1 q.2 (f q)=0 := by
  rcases r with ⟨s,t⟩
  rcases hb with hs|ht
  · change s=0 at hs
    subst s
    exact exists_smooth_axis_radial_solution ha hzero he0 he1 hr.2
  · change t=0 at ht
    subst t
    exact exists_smooth_other_axis_radial_solution ha hzero he0 he1 hr.1

theorem exists_smooth_boundary_moment_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        moment k q.1 (f q)=q.2 ∧
        (0≤(f q).1 ↔ 0≤q.2.1) ∧ (0≤(f q).2 ↔ 0≤q.2.2) ∧
        (0<(f q).1 ↔ 0<q.2.1) ∧ (0<(f q).2 ↔ 0<q.2.2) := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_boundary_radial_solution ha hzero he0 he1 hr hb
  let q0 := (a,moment k a r)
  have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,f q)) q0 :=
    contDiffAt_fst.prodMk hfs
  have hP := polynomial_pos ha hzero hr
  have hPc : ContinuousAt (fun q : (ι → ℝ) × Plane => polynomial k q.1 (f q)) q0 :=
    (polynomial_contDiff k).continuous.continuousAt.comp hc.continuousAt
  have hPe : ∀ᶠ q in 𝓝 q0,0<polynomial k q.1 (f q) := by
    apply hPc.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hP)
  have hsc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 (f q)) q0 := by
    have hs := slope_contDiffAt hP.ne'
    have hh : (a,r)=(q0.1,f q0) := by simp [q0,hf]
    rw [hh] at hs
    exact hs.comp q0 hc
  have hs := slope_pos ha hzero he0 he1 hr
  have hse0 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).1 := by
    apply hsc.continuousAt.fst.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.1)
  have hse1 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).2 := by
    apply hsc.continuousAt.snd.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.2)
  refine ⟨f,hf,hfs,?_⟩
  filter_upwards [hfe,hPe,hse0,hse1] with q hq hPq hs0 hs1
  have hm := moment_eq_of_centered hPq.ne' hq
  refine ⟨hm,?_,?_,?_,?_⟩
  all_goals
    have he := moment_eq_radius_slope k q.1 (f q)
    rw [hm] at he
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_nonneg_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_nonneg_iff_of_pos_right hs1).symm
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_pos_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_pos_iff_of_pos_right hs1).symm




theorem nonnegativeInverse_nonneg (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) :
    0≤(nonnegativeInverse k a p).1 ∧ 0≤(nonnegativeInverse k a p).2 :=
  (invFun (fun r : Quadrant => moment k a r.val) p).property

theorem nonnegativeInverse_spec {k : ι → ℕ × ℕ} {a : ι → ℝ} {p : Plane}
    (hp : ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment k a r=p) :
    moment k a (nonnegativeInverse k a p)=p := by
  change (fun r : Quadrant => moment k a r.val)
    (invFun (fun r : Quadrant => moment k a r.val) p)=p
  exact invFun_eq (f := fun r : Quadrant => moment k a r.val)
    (by obtain ⟨r,hr,he⟩ := hp; exact ⟨⟨r,hr⟩,he⟩)

theorem nonnegativeInverse_of_moment {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) : nonnegativeInverse k a (moment k a r)=r := by
  apply moment_injective_quadrant ha h0 he0 he1 (nonnegativeInverse_nonneg _ _ _) hr
  exact nonnegativeInverse_spec ⟨r,hr,rfl⟩

theorem nonnegativeInverse_eq_of_moment {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r p : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (he : moment k a r=p) : nonnegativeInverse k a p=r := by
  rw [← he]
  exact nonnegativeInverse_of_moment ha h0 he0 he1 hr

theorem boundary_inverse_smooth_extension {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=nonnegativeInverse k a (moment k a r) ∧
      ContDiffAt ℝ ∞ f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        (∀ i,0<q.1 i) → 0≤q.2.1 → 0≤q.2.2 → nonnegativeInverse k q.1 q.2=f q := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_smooth_boundary_moment_inverse ha h0 he0 he1 hr hb
  refine ⟨f,hf.trans (nonnegativeInverse_of_moment ha h0 he0 he1 hr).symm,hfs,?_⟩
  filter_upwards [hfe] with q hq hqa hq0 hq1
  exact nonnegativeInverse_eq_of_moment hqa h0 he0 he1
    ⟨hq.2.1.mpr hq0,hq.2.2.1.mpr hq1⟩ hq.1

theorem boundary_inverse_contDiffWithinAt {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0 ≤ r.1 ∧ 0 ≤ r.2) (hb : r.1=0 ∨ r.2=0) :
    ContDiffWithinAt ℝ ∞ (fun q : (ι → ℝ) × Plane => nonnegativeInverse k q.1 q.2)
      {q | (∀ i,0<q.1 i) ∧ 0≤q.2.1 ∧ 0≤q.2.2} (a,moment k a r) := by
  obtain ⟨f,hf,hfs,hfe⟩ := boundary_inverse_smooth_extension ha h0 he0 he1 hr hb
  apply hfs.contDiffWithinAt.congr_of_eventuallyEq _ hf.symm
  filter_upwards [hfe.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hqS
  exact hq hqS.1 hqS.2.1 hqS.2.2


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem lattice_zero (A B : ℕ) : ∃ i : TrapezoidWeight A B,latticeIndex i=(0,0) :=
  ⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,rfl⟩

theorem lattice_unit_fst {A B : ℕ} (hA : 0<A) (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(1,0) :=
  ⟨⟨(⟨1,by omega⟩,⟨0,by omega⟩),by simp; omega⟩,rfl⟩

theorem lattice_unit_snd {A B : ℕ} (hA : 0<A) (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(0,1) :=
  ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp; omega⟩,rfl⟩

theorem lattice_end_fst {A B : ℕ} (hAB : A≤B) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(A,0) :=
  ⟨⟨(⟨A,by omega⟩,⟨0,by omega⟩),by simp [hAB]⟩,rfl⟩

theorem lattice_end_snd (A B : ℕ) :
    ∃ i : TrapezoidWeight A B,latticeIndex i=(0,B) :=
  ⟨⟨(⟨0,by omega⟩,⟨B,by omega⟩),by simp⟩,rfl⟩

theorem trapezoid_radial_surjective {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment latticeIndex a r=p := by
  by_cases hp0 : p.1=0
  · by_cases hp1 : p.2=0
    · refine ⟨(0,0),⟨le_rfl,le_rfl⟩,?_⟩
      rw [moment_origin]
      exact Prod.ext hp0.symm hp1.symm
    · obtain ⟨t,ht,he⟩ := exists_axis_solution ha (lattice_zero A B) (lattice_end_snd A B)
        (p:=p.2) ⟨lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),by simpa [hp0] using hp.2.2.2⟩
      exact ⟨(0,t),⟨le_rfl,ht.le⟩,he.trans (Prod.ext hp0.symm rfl)⟩
  · have hp0p : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    by_cases hp1 : p.2=0
    · have hzero : ∃ i : TrapezoidWeight A B,(latticeIndex i).swap=(0,0) := by
        obtain ⟨i,hi⟩ := lattice_zero A B
        exact ⟨i,by simp [hi]⟩
      have hend : ∃ i : TrapezoidWeight A B,(latticeIndex i).swap=(0,A) := by
        obtain ⟨i,hi⟩ := lattice_end_fst hAB
        exact ⟨i,by simp [hi]⟩
      obtain ⟨t,ht,he⟩ := exists_axis_solution ha hzero hend ⟨hp0p,hp.2.1⟩
      refine ⟨(t,0),⟨ht.le,le_rfl⟩,?_⟩
      have hh := moment_swap latticeIndex a (t,0)
      change moment (fun i => (latticeIndex i).swap) a (0,t)=
        (moment latticeIndex a (t,0)).swap at hh
      rw [he] at hh
      have hx := congrArg Prod.swap hh
      exact (show moment latticeIndex a (t,0)=(p.1,0) by simpa using hx.symm).trans
        (Prod.ext rfl hp1.symm)
    · obtain ⟨r,hr,he⟩ := exists_positive_radial_solution ha
        (show Surrounds (weight (latticeIndex (A:=A) (B:=B))) (planeVector p.1 p.2) from
          trapezoidWeight_surrounds hAB ⟨hp0p,hp.2.1,lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),hp.2.2.2⟩)
      exact ⟨r,⟨hr.1.le,hr.2.le⟩,he⟩

theorem trapezoid_inverse_spec {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) : moment latticeIndex a (nonnegativeInverse latticeIndex a p)=p :=
  nonnegativeInverse_spec (trapezoid_radial_surjective hAB ha hp)


end

section

open scoped BigOperators Topology ContDiff
open Set Filter Function
variable {ι : Type*} [Fintype ι]

theorem planeVector_contDiff : ContDiff ℝ ∞ (fun r : Plane => planeVector r.1 r.2) := by
  apply (contDiff_piLp 2).mpr
  intro j
  fin_cases j
  · exact contDiff_fst
  · exact contDiff_snd

theorem expRadius_contDiff : ContDiff ℝ ∞ expRadius := by
  apply ContDiff.prodMk <;> apply ContDiff.exp <;> fun_prop

theorem nonnegativeInverse_exp [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    nonnegativeInverse k a p=expRadius (inverse (weight k) a (planeVector p.1 p.2)) := by
  apply nonnegativeInverse_eq_of_moment ha h0 he0 he1
    ⟨(Real.exp_pos _).le,(Real.exp_pos _).le⟩
  have he := moment_expRadius k a (inverse (weight k) a (planeVector p.1 p.2))
  rw [inverse_spec ha hp] at he
  exact Prod.ext (congrArg (fun z : MomentPlane => z 0) he)
    (congrArg (fun z : MomentPlane => z 1) he)

theorem nonnegativeInverse_interior_contDiffAt [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => nonnegativeInverse k q.1 q.2) (a,p) := by
  have hmap : ContDiff ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,planeVector q.2.1 q.2.2)) :=
    contDiff_fst.prodMk (planeVector_contDiff.comp contDiff_snd)
  have hs := expRadius_contDiff.contDiffAt.comp (a,p)
    ((inverse_contDiffAt ha hp).comp (a,p) hmap.contDiffAt)
  apply hs.congr_of_eventuallyEq
  have hae : ∀ᶠ q : (ι → ℝ) × Plane in 𝓝 (a,p),∀ i,0<q.1 i :=
    (positiveCoefficients_isOpen.preimage continuous_fst).mem_nhds ha
  have hpe : ∀ᶠ q : (ι → ℝ) × Plane in 𝓝 (a,p),Surrounds (weight k) (planeVector q.2.1 q.2.2) :=
    ((surrounds_isOpen (weight k)).preimage (planeVector_contDiff.continuous.comp continuous_snd)).mem_nhds hp
  filter_upwards [hae,hpe] with q hqa hqp
  exact nonnegativeInverse_exp hqa h0 he0 he1 hqp


end


open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem trapezoid_inverse_contDiffWithinAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ContDiffWithinAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × Plane => nonnegativeInverse latticeIndex q.1 q.2)
      {q | (∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B} (a,p) := by
  by_cases hb : p.1=0 ∨ p.2=0
  · let r := nonnegativeInverse (latticeIndex (A:=A) (B:=B)) a p
    have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a p
    have he : moment latticeIndex a r=p := trapezoid_inverse_spec hAB ha hp
    have hz := moment_zero_coordinates ha (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hr
    have hbr : r.1=0 ∨ r.2=0 := by
      rw [he] at hz
      exact hb.elim (fun h => Or.inl (hz.1.mp h)) (fun h => Or.inr (hz.2.mp h))
    have hs := boundary_inverse_contDiffWithinAt ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr hbr
    rw [he] at hs
    exact hs.mono (fun _ hq => ⟨hq.1,hq.2.1,hq.2.2.2.1⟩)
  · have hp0 : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm (fun h => hb (Or.inl h)))
    have hp1 : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm (fun h => hb (Or.inr h)))
    exact (nonnegativeInverse_interior_contDiffAt ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      (trapezoidWeight_surrounds hAB ⟨hp0,hp.2.1,hp1,hp.2.2.2⟩)).contDiffWithinAt



end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_AnnularChartHelpers
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem flatProduct_snd_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,V) (Prod.snd : M × V → V) z=
      ContinuousLinearMap.snd ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_snd

end

section
variable {ι : Type*} [Fintype ι]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem verticalLiouville_apply (z : M × PlanePhase ι) (v : E × PlanePhase ι) :
    verticalLiouville z v=(1/2:ℝ)*phaseArea z.2 v.2 := by
  change standardLiouville z.2 (mfderiv 𝓘(ℝ,E × PlanePhase ι) 𝓘(ℝ,PlanePhase ι) Prod.snd z v)=_
  rw [flatProduct_snd_derivative]
  rfl

end

variable {ι : Type*} [Fintype ι]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem complexAffineLift_derivative (z v : ι → ℂ) :
    fderiv ℝ complexAffineLift z v=fun i => match i with
      | none => 0
      | some i => v i := by
  have h : HasFDerivAt (complexAffineLift (ι := ι))
      (ContinuousLinearMap.pi fun i => match i with
        | none => 0
        | some i => (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ)) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    cases i with
    | none => exact hasFDerivAt_const _ _
    | some i => exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt
  rw [h.fderiv]
  funext i
  cases i <;> rfl

 theorem affineFSPrimitive_hopf (c : ℝ) (z v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (complexAffineLift z))
      (complexCartesian (fderiv ℝ complexAffineLift z v))=
    affineFSPrimitive c (complexCartesian z) (complexCartesian v) := by
  rw [hopfPrimitive,complexAffineLift_sq,smul_apply,smul_eq_mul]
  change _=c/(2*(1+phaseSq (complexCartesian z)))*phaseArea (complexCartesian z) (complexCartesian v)
  congr 1
  rw [← complexPairing_im,← complexPairing_im,complexAffineLift_derivative]
  simp [complexPairing,Fintype.sum_option,complexAffineLift]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_MovingPrimitiveNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open NormalLift Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

theorem inclusion_real_contMDiff : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlaneBase) ∞ inclusion :=
  (projection_contDiff.restrict_scalars ℝ).contMDiff.comp
    (real_inclusion_contMDiff (parameters 0))

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_SixModelComparisonData
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem complexArea_add (z u v : ℂ) : complexArea z (u+v)=complexArea z u+complexArea z v := by
  simp only [complexArea,mul_add,Complex.add_im]

theorem complexArea_product (s t u v : ℂ) :
    complexArea (s*t) (u*t+s*v)=Complex.normSq t*complexArea s u+Complex.normSq s*complexArea t v := by
  rw [complexArea_add,mul_comm u t,mul_comm s t,complexArea_mul,mul_comm t s,complexArea_mul]

theorem complexBlocks_sq (s : ι → ℂ) (z : ι → κ → ℂ) :
    phaseSq (complexCartesian (complexBlocks s z))=
      ∑ i,Complex.normSq (s i)*phaseSq (complexCartesian (z i)) := by
  simp only [complexCartesian_sq,complexBlocks,Fintype.sum_prod_type,Complex.normSq_mul,Finset.mul_sum]

theorem complexBlocks_area (s d : ι → ℂ) (z v : ι → κ → ℂ) :
    phaseArea (complexCartesian (complexBlocks s z))
      (complexCartesian (fun ij => d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2))=
    ∑ i,(phaseSq (complexCartesian (z i))*complexArea (s i) (d i)+
      Complex.normSq (s i)*phaseArea (complexCartesian (z i)) (complexCartesian (v i))) := by
  have he (a b : κ → ℂ) : phaseArea (complexCartesian a) (complexCartesian b)=
      ∑ j,complexArea (a j) (b j) := by
    simp only [←complexPairing_im,complexPairing,Complex.im_sum,Complex.star_def,complexArea]
  rw [show phaseArea (complexCartesian (complexBlocks s z))
      (complexCartesian (fun ij => d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2))=
      ∑ ij : ι × κ,complexArea (s ij.1*z ij.1 ij.2) (d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2) from by
    simp only [←complexPairing_im,complexPairing,Complex.im_sum,Complex.star_def,complexArea,complexBlocks]]
  simp only [Fintype.sum_prod_type,complexArea_product,Finset.sum_add_distrib,←Finset.sum_mul,
    ←Finset.mul_sum,complexCartesian_sq,he]

theorem hopfPrimitive_complexBlocks (s d : ι → ℂ) (z v : ι → κ → ℂ)
    (hz : ∀ i,complexCartesian (z i)≠0) (c : ℝ) :
    hopfPrimitive c (complexCartesian (complexBlocks s z))
      (complexCartesian (fun ij => d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2))=
    (∑ i,(Complex.normSq (s i)*phaseSq (complexCartesian (z i)) /
      phaseSq (complexCartesian (complexBlocks s z)))*
        hopfPrimitive c (complexCartesian (z i)) (complexCartesian (v i)))+
    c/(2*phaseSq (complexCartesian (complexBlocks s z)))*
      ∑ i,phaseSq (complexCartesian (z i))*complexArea (s i) (d i) := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,complexBlocks_area,Finset.sum_add_distrib,
    mul_add,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(phaseSq_pos (hz i)).ne']

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem squaredRadii_nonneg (z : DiskPair) : 0≤(squaredRadii z).1 ∧ 0≤(squaredRadii z).2 :=
  ⟨Complex.normSq_nonneg _,Complex.normSq_nonneg _⟩

theorem squaredRadii_contDiff : ContDiff ℝ ∞ squaredRadii := by
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re+z.im*z.im)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (hn.comp contDiff_fst).prodMk (hn.comp contDiff_snd)

theorem diskDomain_isOpen (A B : ℝ) : IsOpen (diskDomain A B) :=
  (isOpen_lt squaredRadii_contDiff.continuous.fst continuous_const).inter
    (isOpen_lt (squaredRadii_contDiff.continuous.fst.add squaredRadii_contDiff.continuous.snd) continuous_const)

theorem squaredRadii_mem_lower {A B : ℝ} {z : DiskPair} (hz : z∈diskDomain A B) :
    squaredRadii z∈lowerTrapezoid A B :=
  ⟨(squaredRadii_nonneg z).1,hz.1,(squaredRadii_nonneg z).2,hz.2⟩

theorem normSq_real_smul (s : ℝ) (z : ℂ) : Complex.normSq (s • z)=s^2*Complex.normSq z := by
  change Complex.normSq ((s:ℂ)*z)=_
  rw [Complex.normSq_mul,Complex.normSq_ofReal]
  ring

theorem squaredRadii_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {z : DiskPair}
    (hz : ∃ r : Plane,(0 ≤ r.1 ∧ 0 ≤ r.2) ∧ moment k a r=squaredRadii z) :
    squaredRadii (diskInverse k a z)=nonnegativeInverse k a (squaredRadii z) := by
  have hs := slope_pos ha h0 he0 he1 (nonnegativeInverse_nonneg k a (squaredRadii z))
  have hm := nonnegativeInverse_spec hz
  rw [moment_eq_radius_slope] at hm
  apply Prod.ext
  · change Complex.normSq (_ • z.1)=_
    rw [normSq_real_smul,inv_pow,Real.sq_sqrt hs.1.le]
    change (slope k a (nonnegativeInverse k a (squaredRadii z))).1⁻¹*(squaredRadii z).1=_
    rw [←congrArg Prod.fst hm]
    field_simp [hs.1.ne']
  · change Complex.normSq (_ • z.2)=_
    rw [normSq_real_smul,inv_pow,Real.sq_sqrt hs.2.le]
    change (slope k a (nonnegativeInverse k a (squaredRadii z))).2⁻¹*(squaredRadii z).2=_
    rw [←congrArg Prod.snd hm]
    field_simp [hs.2.ne']

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment.Radial

theorem complexArea_real_smul (z v : ℂ) (r : ℝ) :
    complexArea z (r • v)=r*complexArea z v := by
  simp only [complexArea_apply,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem complexArea_power_derivative (z v : ℂ) (n : ℕ) :
    complexArea (z^n) ((n:ℂ)*z^(n-1)*v)=
      (n:ℝ)*Complex.normSq z^(n-1)*complexArea z v := by
  cases n with
  | zero => simp [complexArea]
  | succ n =>
    rw [Nat.succ_sub_one,pow_succ]
    have he : ((n+1:ℕ):ℂ)*z^n*v=((n+1:ℕ):ℝ) • (z^n*v) := by
      simp only [Complex.real_smul,Complex.ofReal_natCast]
      ring
    rw [he,complexArea_real_smul,complexArea_mul,map_pow]
    ring

theorem complexMonomial_hasFDerivAt (k : ℕ × ℕ) (z : DiskPair) :
    HasFDerivAt (complexMonomial k) (complexMonomialDerivative k z) z := by
  have h := (((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt (x := z)).pow k.1).mul
    (((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt (x := z)).pow k.2)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [complexMonomialDerivative]
  ring

theorem complexMonomial_normSq (k : ℕ × ℕ) (z : DiskPair) :
    Complex.normSq (complexMonomial k z)=monomial k (squaredRadii z) := by
  simp only [complexMonomial,Complex.normSq_mul,map_pow,monomial,squaredRadii]

theorem complexMonomial_area (k : ℕ × ℕ) (z v : DiskPair) :
    complexArea (complexMonomial k z) (complexMonomialDerivative k z v)=
      (k.1:ℝ)*(squaredRadii z).1^(k.1-1)*(squaredRadii z).2^k.2*complexArea z.1 v.1+
      (k.2:ℝ)*(squaredRadii z).1^k.1*(squaredRadii z).2^(k.2-1)*complexArea z.2 v.2 := by
  have he : complexMonomialDerivative k z v=
      ((k.1:ℂ)*z.1^(k.1-1)*v.1)*z.2^k.2+
      z.1^k.1*((k.2:ℂ)*z.2^(k.2-1)*v.2) := by
    simp only [complexMonomialDerivative,add_apply,
      smul_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    ring
  rw [he,complexMonomial,complexArea_product,complexArea_power_derivative,complexArea_power_derivative]
  simp only [map_pow,squaredRadii]
  ring

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem toricLift_sq (k : ι → ℕ × ℕ) (G : ι → κ → ℂ) (z : DiskPair) :
    phaseSq (complexCartesian (toricLift k G z))=
      polynomial k (fun i => phaseSq (complexCartesian (G i))) (squaredRadii z) := by
  rw [toricLift,complexBlocks_sq]
  simp only [complexMonomial_normSq,polynomial,mul_comm]

theorem toricLift_primitive (k : ι → ℕ × ℕ) (G V : ι → κ → ℂ)
    (hG : ∀ i,complexCartesian (G i)≠0) (z v : DiskPair) (c : ℝ) :
    hopfPrimitive c (complexCartesian (toricLift k G z))
      (complexCartesian (toricLiftDifferential k G V z v))=
    (∑ i,probability k (fun j => phaseSq (complexCartesian (G j))) (squaredRadii z) i *
      hopfPrimitive c (complexCartesian (G i)) (complexCartesian (V i)))+
    c/2*((slope k (fun j => phaseSq (complexCartesian (G j))) (squaredRadii z)).1*complexArea z.1 v.1+
      (slope k (fun j => phaseSq (complexCartesian (G j))) (squaredRadii z)).2*complexArea z.2 v.2) := by
  rw [show hopfPrimitive c (complexCartesian (toricLift k G z))
      (complexCartesian (toricLiftDifferential k G V z v))=
      hopfPrimitive c (complexCartesian (complexBlocks (fun i => complexMonomial (k i) z) G))
      (complexCartesian (fun ij => complexMonomialDerivative (k ij.1) z v*G ij.1 ij.2+
        complexMonomial (k ij.1) z*V ij.1 ij.2)) from rfl,
    hopfPrimitive_complexBlocks (fun i => complexMonomial (k i) z)
      (fun i => complexMonomialDerivative (k i) z v) G V hG c]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [complexMonomial_normSq,←toricLift,toricLift_sq]
    simp only [probability]
    congr 2
    exact mul_comm _ _
  · rw [←toricLift,toricLift_sq]
    simp only [complexMonomial_area,FiniteMoment.Radial.slope,slopeNumerator,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
      mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end

variable {ι κ X : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem toricLift_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → κ → ℂ) × DiskPair => toricLift k q.1 q.2) := by
  apply contDiff_pi.mpr
  intro ij
  dsimp only [toricLift,complexBlocks,complexMonomial]
  fun_prop

theorem toricLift_fderiv {k : ι → ℕ × ℕ} {G : X → ι → κ → ℂ} {z : X → DiskPair} {x : X}
    (hG : DifferentiableAt ℝ G x) (hz : DifferentiableAt ℝ z x) (v : X) :
    fderiv ℝ (fun q => toricLift k (G q) (z q)) x v=
      toricLiftDifferential k (G x) (fderiv ℝ G x v) (z x) (fderiv ℝ z x v) := by
  have hs := ((toricLift_contDiff k).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (G x,z x)).comp x (hG.prodMk hz)
  funext ij
  have hi := (hasFDerivAt_pi'.mp ((hasFDerivAt_pi'.mp hG.hasFDerivAt) ij.1)) ij.2
  have hm := (complexMonomial_hasFDerivAt (k ij.1) (z x)).comp x hz.hasFDerivAt
  have hh := hm.mul hi
  have he : fderiv ℝ (fun q => toricLift k (G q) (z q) ij) x=
      (ContinuousLinearMap.proj ij).comp (fderiv ℝ (fun q => toricLift k (G q) (z q)) x) :=
    ((hasFDerivAt_pi'.mp hs.hasFDerivAt) ij).fderiv
  have hh' : HasFDerivAt (fun q => toricLift k (G q) (z q) ij)
      (complexMonomial (k ij.1) (z x) • ((ContinuousLinearMap.proj ij.2).comp
         ((ContinuousLinearMap.proj ij.1).comp (fderiv ℝ G x)))+
       G x ij.1 ij.2 • ((complexMonomialDerivative (k ij.1) (z x)).comp (fderiv ℝ z x))) x := by
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  have hv := congrArg (fun L => L v) (he.symm.trans hh'.fderiv)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,add_apply,smul_apply,
    smul_eq_mul,toricLiftDifferential,mul_comm,add_comm] using hv

theorem toricLift_pullback_primitive {k : ι → ℕ × ℕ} {G : X → ι → κ → ℂ} {z : X → DiskPair} {x : X}
    (hG : DifferentiableAt ℝ G x) (hz : DifferentiableAt ℝ z x)
    (hne : ∀ i,complexCartesian (G x i)≠0) (v : X) (c : ℝ) :
    hopfPrimitive c (complexCartesian (toricLift k (G x) (z x)))
      (complexCartesian (fderiv ℝ (fun q => toricLift k (G q) (z q)) x v))=
    (∑ i,probability k (fun j => phaseSq (complexCartesian (G x j))) (squaredRadii (z x)) i *
      hopfPrimitive c (complexCartesian (G x i)) (complexCartesian (fderiv ℝ G x v i)))+
    c/2*((slope k (fun j => phaseSq (complexCartesian (G x j))) (squaredRadii (z x))).1*
      complexArea (z x).1 (fderiv ℝ z x v).1+
      (slope k (fun j => phaseSq (complexCartesian (G x j))) (squaredRadii (z x))).2*
      complexArea (z x).2 (fderiv ℝ z x v).2) := by
  rw [toricLift_fderiv hG hz]
  exact toricLift_primitive k _ _ hne _ _ c

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RadialDiskSmooth
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem diskRadius_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => nonnegativeInverse latticeIndex q.1 (squaredRadii q.2)) (a,z) := by
  let U : Set ((TrapezoidWeight A B → ℝ) × DiskPair) :=
    {q | (∀ i,0<q.1 i) ∧ q.2∈diskDomain A B}
  have hU : IsOpen U := positiveCoefficients_isOpen.prod (diskDomain_isOpen A B)
  have hs := trapezoid_inverse_contDiffWithinAt hA hAB ha (squaredRadii_mem_lower hz)
  have hm : ContDiff ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (q.1,squaredRadii q.2)) :=
    contDiff_fst.prodMk (squaredRadii_contDiff.comp contDiff_snd)
  have hmaps : MapsTo (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (q.1,squaredRadii q.2))
      U {q | (∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B} :=
    fun q hq => ⟨hq.1,squaredRadii_mem_lower hq.2⟩
  have hc := hs.comp (a,z) (hm.contDiffWithinAt (s:=U)) hmaps
  exact hc.contDiffAt (hU.mem_nhds ⟨ha,hz⟩)

theorem diskInverse_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) := by
  have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z)
  have hs := diskRadius_contDiffAt hA hAB ha hz
  have hmap := contDiffAt_fst.prodMk hs
  have hsl := slope_contDiffAt (polynomial_pos ha (lattice_zero A B) hr).ne'
  have hc := hsl.comp (a,z) hmap
  have hpos := slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr
  exact ((hc.fst.sqrt hpos.1.ne').inv (Real.sqrt_pos.mpr hpos.1).ne').smul contDiffAt_snd.fst |>.prodMk
    (((hc.snd.sqrt hpos.2.ne').inv (Real.sqrt_pos.mpr hpos.2).ne').smul contDiffAt_snd.snd)

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment.Radial

theorem complexArea_scaled_derivative (r s : ℝ) (z v : ℂ) :
    complexArea (r • z) (s • z+r • v)=r^2*complexArea z v := by
  simp only [complexArea_apply,Complex.smul_re,Complex.smul_im,Complex.add_re,Complex.add_im,smul_eq_mul]
  ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem complexArea_fderiv_real_smul {r : X → ℝ} {z : X → ℂ} {x : X}
    (hr : DifferentiableAt ℝ r x) (hz : DifferentiableAt ℝ z x) (v : X) :
    complexArea (r x • z x) (fderiv ℝ (fun q => r q • z q) x v)=
      (r x)^2*complexArea (z x) (fderiv ℝ z x v) := by
  rw [fderiv_fun_smul hr hz]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  rw [add_comm]
  exact complexArea_scaled_derivative _ _ _ _

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators ContDiff ComplexConjugate
open Hamiltonian DiagonalQuadrics

theorem inverseDiskScale_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair =>
      ((Real.sqrt (slope latticeIndex q.1 (nonnegativeInverse latticeIndex q.1 (squaredRadii q.2))).1)⁻¹,
       (Real.sqrt (slope latticeIndex q.1 (nonnegativeInverse latticeIndex q.1 (squaredRadii q.2))).2)⁻¹)) (a,z) := by
  have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z)
  have hs := diskRadius_contDiffAt hA hAB ha hz
  have hc := (slope_contDiffAt (polynomial_pos ha (lattice_zero A B) hr).ne').comp (a,z)
    (contDiffAt_fst.prodMk hs)
  have hpos := slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr
  exact ((hc.fst.sqrt hpos.1.ne').inv (Real.sqrt_pos.mpr hpos.1).ne').prodMk
    ((hc.snd.sqrt hpos.2.ne').inv (Real.sqrt_pos.mpr hpos.2).ne')

theorem diskInverse_angular_fst {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) (v : (TrapezoidWeight A B → ℝ) × DiskPair) :
    (slope latticeIndex a (squaredRadii (diskInverse latticeIndex a z))).1*
      complexArea (diskInverse latticeIndex a z).1
        ((fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).1)=
      complexArea z.1 v.2.1 := by
  have hs := (inverseDiskScale_contDiffAt hA hAB ha hz).fst.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hz' : DifferentiableAt ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.1) (a,z) :=
    differentiableAt_snd.fst
  have hd := (diskInverse_contDiffAt hA hAB ha hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := complexArea_fderiv_real_smul hs hz' v
  have hpos := (slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
    (nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z))).1
  have hrad := squaredRadii_inverse ha (lattice_zero A B) (lattice_unit_fst hA hAB)
    (lattice_unit_snd hA hAB) (trapezoid_radial_surjective hAB ha (squaredRadii_mem_lower hz))
  rw [hrad]
  rw [show (fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).1=
      fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (diskInverse latticeIndex q.1 q.2).1) (a,z) v from
      (congrArg (fun L => L v) hd.hasFDerivAt.fst.fderiv).symm]
  change _*complexArea (_ • _) (fderiv ℝ (fun q => _ • q.2.1) (a,z) v)=_
  rw [he]
  have hp : HasFDerivAt (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair)) (a,z) := by
    convert! ((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt (x := z)).comp (a,z)
      ((ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair).hasFDerivAt (x := (a,z))) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hp.fderiv]
  change _*((Real.sqrt _)⁻¹^2*complexArea z.1 v.2.1)=_
  rw [inv_pow,Real.sq_sqrt hpos.le]
  field_simp

theorem diskInverse_angular_snd {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {z : DiskPair}
    (hz : z∈diskDomain A B) (v : (TrapezoidWeight A B → ℝ) × DiskPair) :
    (slope latticeIndex a (squaredRadii (diskInverse latticeIndex a z))).2*
      complexArea (diskInverse latticeIndex a z).2
        ((fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).2)=
      complexArea z.2 v.2.2 := by
  have hs := (inverseDiskScale_contDiffAt hA hAB ha hz).snd.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hz' : DifferentiableAt ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.2) (a,z) :=
    differentiableAt_snd.snd
  have hd := (diskInverse_contDiffAt hA hAB ha hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := complexArea_fderiv_real_smul hs hz' v
  have hpos := (slope_pos ha (lattice_zero A B) (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
    (nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a (squaredRadii z))).2
  have hrad := squaredRadii_inverse ha (lattice_zero A B) (lattice_unit_fst hA hAB)
    (lattice_unit_snd hA hAB) (trapezoid_radial_surjective hAB ha (squaredRadii_mem_lower hz))
  rw [hrad]
  rw [show (fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a,z) v).2=
      fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => (diskInverse latticeIndex q.1 q.2).2) (a,z) v from
      (congrArg (fun L => L v) hd.hasFDerivAt.snd.fderiv).symm]
  change _*complexArea (_ • _) (fderiv ℝ (fun q => _ • q.2.2) (a,z) v)=_
  rw [he]
  have hp : HasFDerivAt (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair)) (a,z) := by
    convert! ((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt (x := z)).comp (a,z)
      ((ContinuousLinearMap.snd ℝ (TrapezoidWeight A B → ℝ) DiskPair).hasFDerivAt (x := (a,z))) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hp.fderiv]
  change _*((Real.sqrt _)⁻¹^2*complexArea z.2 v.2.2)=_
  rw [inv_pow,Real.sq_sqrt hpos.le]
  field_simp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem diskInverse_angular_comp {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : X → TrapezoidWeight A B → ℝ} {z : X → DiskPair} {x : X}
    (ha : DifferentiableAt ℝ a x) (hz : DifferentiableAt ℝ z x)
    (hpos : ∀ i,0<a x i) (hdom : z x∈diskDomain A B) (v : X) :
    ((slope latticeIndex (a x) (squaredRadii (diskInverse latticeIndex (a x) (z x)))).1*
      complexArea (diskInverse latticeIndex (a x) (z x)).1
        (fderiv ℝ (fun q => diskInverse latticeIndex (a q) (z q)) x v).1 =
      complexArea (z x).1 (fderiv ℝ z x v).1) ∧
    ((slope latticeIndex (a x) (squaredRadii (diskInverse latticeIndex (a x) (z x)))).2*
      complexArea (diskInverse latticeIndex (a x) (z x)).2
        (fderiv ℝ (fun q => diskInverse latticeIndex (a q) (z q)) x v).2 =
      complexArea (z x).2 (fderiv ℝ z x v).2) := by
  have hi := (diskInverse_contDiffAt hA hAB hpos hdom).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : fderiv ℝ (fun q => diskInverse latticeIndex (a q) (z q)) x=
      (fderiv ℝ (fun q : (TrapezoidWeight A B → ℝ) × DiskPair => diskInverse latticeIndex q.1 q.2) (a x,z x)).comp
        ((fderiv ℝ a x).prod (fderiv ℝ z x)) := by
    convert! (hi.hasFDerivAt.comp x (ha.hasFDerivAt.prodMk hz.hasFDerivAt)).fderiv using 1
    all_goals try with_reducible_and_instances rfl
  rw [he]
  exact ⟨diskInverse_angular_fst hA hAB hpos hdom (fderiv ℝ a x v,fderiv ℝ z x v),
    diskInverse_angular_snd hA hAB hpos hdom (fderiv ℝ a x v,fderiv ℝ z x v)⟩

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment FiniteMoment.Radial

variable {ι κ X : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem coefficientSquares_contDiff : ContDiff ℝ ∞ (coefficientSquares (ι := ι) (κ := κ)) := by
  apply contDiff_pi.mpr
  intro i
  exact phaseSq_smooth.comp ((complexCartesian (ι := κ)).contDiff.comp (contDiff_apply ℝ (κ → ℂ) i))

theorem coefficient_diskInverse_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : TrapezoidWeight A B → κ → ℂ} (hG : ∀ i,complexCartesian (G i)≠0)
    {z : DiskPair} (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
      diskInverse latticeIndex (coefficientSquares q.1) q.2) (G,z) := by
  have hf : ContDiff ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
      (coefficientSquares q.1,q.2)) :=
    (coefficientSquares_contDiff.comp contDiff_fst).prodMk contDiff_snd
  exact (diskInverse_contDiffAt hA hAB (fun i => phaseSq_pos (hG i)) hz).comp (G,z) hf.contDiffAt

theorem normalizedToricLift_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : TrapezoidWeight A B → κ → ℂ} (hG : ∀ i,complexCartesian (G i)≠0)
    {z : DiskPair} (hz : z∈diskDomain A B) :
    ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
      normalizedToricLift latticeIndex q.1 q.2) (G,z) := by
  have hi := coefficient_diskInverse_contDiffAt hA hAB hG hz
  apply contDiffAt_pi.mpr
  intro ij
  change ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair =>
    (diskInverse latticeIndex (coefficientSquares q.1) q.2).1 ^ (latticeIndex ij.1).1 *
    (diskInverse latticeIndex (coefficientSquares q.1) q.2).2 ^ (latticeIndex ij.1).2 * q.1 ij.1 ij.2) (G,z)
  have hg : ContDiffAt ℝ ∞ (fun q : (TrapezoidWeight A B → κ → ℂ) × DiskPair => q.1 ij.1 ij.2) (G,z) := by
    fun_prop
  exact ((hi.fst.pow _).mul (hi.snd.pow _)).mul hg

 theorem normalizedToricLift_pullback_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : X → TrapezoidWeight A B → κ → ℂ} {z : X → DiskPair} {x : X}
    (hG : DifferentiableAt ℝ G x) (hz : DifferentiableAt ℝ z x)
    (hne : ∀ i,complexCartesian (G x i)≠0) (hdom : z x∈diskDomain A B) (v : X) (c : ℝ) :
    hopfPrimitive c (complexCartesian (normalizedToricLift latticeIndex (G x) (z x)))
      (complexCartesian (fderiv ℝ (fun q => normalizedToricLift latticeIndex (G q) (z q)) x v))=
    (∑ i,selected latticeIndex (coefficientSquares (G x)) (squaredRadii (z x)) i *
      hopfPrimitive c (complexCartesian (G x i)) (complexCartesian (fderiv ℝ G x v i)))+
    c/2*(complexArea (z x).1 (fderiv ℝ z x v).1+complexArea (z x).2 (fderiv ℝ z x v).2) := by
  have ha : DifferentiableAt ℝ (fun q => coefficientSquares (G q)) x := by
    convert! (coefficientSquares_contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (G x)).comp x hG using 1
    all_goals try with_reducible_and_instances rfl
  have hpos : ∀ i,0 < coefficientSquares (G x) i := fun i => phaseSq_pos (hne i)
  have hi : DifferentiableAt ℝ (fun q => diskInverse latticeIndex (coefficientSquares (G q)) (z q)) x := by
    convert! ((diskInverse_contDiffAt hA hAB hpos hdom).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp x (ha.prodMk hz) using 1
    all_goals try with_reducible_and_instances rfl
  have hang := diskInverse_angular_comp hA hAB ha hz hpos hdom v
  have hrad := squaredRadii_inverse hpos (lattice_zero A B) (lattice_unit_fst hA hAB)
    (lattice_unit_snd hA hAB) (trapezoid_radial_surjective hAB hpos (squaredRadii_mem_lower hdom))
  unfold normalizedToricLift
  rw [toricLift_pullback_primitive hG hi hne v c]
  change (∑ i,probability latticeIndex (coefficientSquares (G x)) _ i*_)+c/2*(_+_)=_
  erw [hang.1,hang.2]
  rw [hrad]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open Set Function
open Hamiltonian FiniteMoment FiniteMoment.Radial DiagonalQuadrics

theorem physicalDiskCoordinates_apply (L : ℝ) (z : PlanePhase (Fin 2)) :
    physicalDiskCoordinates L z=(Real.sqrt (L*Real.pi) • (Complex.mk (z 0).1 (z 0).2),
      Real.sqrt (L*Real.pi) • (Complex.mk (z 1).1 (z 1).2)) := rfl

theorem physicalDiskCoordinates_squared {L : ℝ} (hL : 0≤L) (z : PlanePhase (Fin 2)) :
    squaredRadii (physicalDiskCoordinates L z)=physicalParameter L (planeMoments z) := by
  have hsq := Real.sq_sqrt (mul_nonneg hL Real.pi_pos.le)
  apply Prod.ext <;>
    simp only [physicalDiskCoordinates_apply,squaredRadii,Complex.normSq_apply,Complex.smul_re,
      Complex.smul_im,smul_eq_mul,physicalParameter,planeMoments,radialArea,radiusSq]
  all_goals nlinarith [sq_nonneg (z 0).1,sq_nonneg (z 0).2,sq_nonneg (z 1).1,sq_nonneg (z 1).2]

theorem physicalDiskCoordinates_mem {A B : ℕ} {L : ℝ} (hL : 0≤L) (z : PlanePhase (Fin 2)) :
    physicalDiskCoordinates L z∈diskDomain A B ↔
      physicalParameter L (planeMoments z)∈lowerTrapezoid A B := by
  rw [← physicalDiskCoordinates_squared hL z]
  exact ⟨squaredRadii_mem_lower,fun h => ⟨h.2.1,h.2.2.2⟩⟩

theorem complexArea_real_smul_both (r : ℝ) (z v : ℂ) :
    complexArea (r • z) (r • v)=r^2*complexArea z v := by
  simp only [complexArea_apply,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem physicalDiskCoordinates_area {L : ℝ} (hL : 0≤L) (z v : PlanePhase (Fin 2)) :
    complexArea (physicalDiskCoordinates L z).1 (physicalDiskCoordinates L v).1+
      complexArea (physicalDiskCoordinates L z).2 (physicalDiskCoordinates L v).2=
      (L*Real.pi)*phaseArea z v := by
  change complexArea (Real.sqrt (L*Real.pi) • (Complex.mk (z 0).1 (z 0).2))
      (Real.sqrt (L*Real.pi) • (Complex.mk (v 0).1 (v 0).2))+
    complexArea (Real.sqrt (L*Real.pi) • (Complex.mk (z 1).1 (z 1).2))
      (Real.sqrt (L*Real.pi) • (Complex.mk (v 1).1 (v 1).2))=_
  rw [complexArea_real_smul_both,complexArea_real_smul_both,Real.sq_sqrt (mul_nonneg hL Real.pi_pos.le)]
  simp only [phaseArea_apply,Fin.sum_univ_two,complexArea_apply]
  ring

theorem physicalDiskCoordinates_primitive {L : ℝ} (hL : 0<L) (z v : PlanePhase (Fin 2)) :
    (1/(L*Real.pi))/2*(complexArea (physicalDiskCoordinates L z).1 (physicalDiskCoordinates L v).1+
      complexArea (physicalDiskCoordinates L z).2 (physicalDiskCoordinates L v).2)=
      (1/2:ℝ)*phaseArea z v := by
  rw [physicalDiskCoordinates_area hL.le]
  field_simp [hL.ne',Real.pi_ne_zero]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold BigOperators
open FiniteMoment FiniteMoment.Radial DiagonalQuadrics
section

variable {κ E M : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem normalizedToricLift_manifold_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {G : M → TrapezoidWeight A B → κ → ℂ} {z : M → DiskPair} {x : M}
    (hG : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x)
    (hz : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x)
    (hne : ∀ i,complexCartesian (G x i)≠0) (hdom : z x∈diskDomain A B) (v : E) (c : ℝ) :
    hopfPrimitive c (complexCartesian (normalizedToricLift latticeIndex (G x) (z x)))
      (complexCartesian (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B × κ → ℂ)
        (fun q => normalizedToricLift latticeIndex (G q) (z q)) x v))=
    (∑ i,selected latticeIndex (coefficientSquares (G x)) (squaredRadii (z x)) i *
      hopfPrimitive c (complexCartesian (G x i))
        (complexCartesian (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x v i)))+
      c/2*(complexArea (z x).1 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x v).1+
        complexArea (z x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x v).2) := by
  let f : M → (TrapezoidWeight A B → κ → ℂ) × DiskPair := fun q => (G q,z q)
  have hf : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,(TrapezoidWeight A B → κ → ℂ) × DiskPair) f x
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x).prod
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x)) :=
    ⟨hG.hasMFDerivAt.1.prodMk hz.hasMFDerivAt.1,
      hG.hasMFDerivAt.2.prodMk hz.hasMFDerivAt.2⟩
  have ht := (normalizedToricLift_contDiffAt hA hAB hne hdom).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := ht.hasFDerivAt.hasMFDerivAt.comp x hf
  rw [show mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B × κ → ℂ)
      (fun q => normalizedToricLift latticeIndex (G q) (z q)) x=_ from hd.mfderiv]
  convert! normalizedToricLift_pullback_primitive
      (X := (TrapezoidWeight A B → κ → ℂ) × DiskPair) hA hAB
      (differentiableAt_fst (p := (G x,z x))) (differentiableAt_snd (p := (G x,z x))) hne hdom
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,TrapezoidWeight A B → κ → ℂ) G x v),
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,DiskPair) z x v)) c using 1
  all_goals try with_reducible_and_instances rfl
  simp only [fderiv_fst,fderiv_snd]
  rfl

end

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 theorem affineFSPrimitive_hopf_manifold {G : M → ι → ℂ} {x : M}
    (hG : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ι → ℂ) G x) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (complexAffineLift (G x)))
      (complexCartesian (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Option ι → ℂ)
        (fun y => complexAffineLift (G y)) x v))=
    affineFSPrimitive c (complexCartesian (G x))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,PlanePhase ι) (fun y => complexCartesian (G y)) x v) := by
  have hL := complexAffineLift_smooth.differentiable (by simp) (G x)
  have hd := hL.hasFDerivAt.hasMFDerivAt.comp x hG.hasMFDerivAt
  have hd' := (complexCartesian (ι := ι)).hasFDerivAt.hasMFDerivAt.comp x hG.hasMFDerivAt
  rw [show mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Option ι → ℂ)
      (fun y => complexAffineLift (G y)) x=_ from hd.mfderiv,
    show mfderiv 𝓘(ℝ,E) 𝓘(ℝ,PlanePhase ι) (fun y => complexCartesian (G y)) x=_ from hd'.mfderiv]
  exact affineFSPrimitive_hopf c (G x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ι → ℂ) G x v)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem weightedCoefficient_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ) ∞ (weightedCoefficient D m) :=
  complexAffineLift_smooth.contMDiff.comp
    ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.contMDiff.comp
      (weightedPhaseInclusion_smooth D m))

 theorem weightedCoefficient_nonzero (D m : ℕ) (x : BaseCurve) :
    complexCartesian (weightedCoefficient D m x)≠0 := by
  intro h
  have he := congrFun (complexCartesian.injective (h.trans (map_zero _).symm)) none
  exact one_ne_zero (by simpa only [weightedCoefficient,complexAffineLift_none,Pi.zero_apply] using he)

 theorem weightedCoefficient_norm (D m : ℕ) (x : BaseCurve) :
    phaseSq (complexCartesian (weightedCoefficient D m x))=coefficientNorm D m x := by
  rw [weightedCoefficient,complexAffineLift_sq,ContinuousLinearEquiv.apply_symm_apply]
  rfl

 theorem weightedCoefficient_hopf (D m : ℕ) (x : BaseCurve) (v : RealModel) (c : ℝ) :
    hopfPrimitive c (complexCartesian (weightedCoefficient D m x))
      (complexCartesian (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ)
        (weightedCoefficient D m) x v))=weightedFSPrimitive D m c x v := by
  have hG := ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.contMDiff.comp
      (weightedPhaseInclusion_smooth D m)).mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have he : (fun y : BaseCurve => complexCartesian
      ((complexCartesian (ι := Option (Fin 3))).symm (weightedPhaseInclusion D m y)))=
      weightedPhaseInclusion D m := by
    funext y
    exact (complexCartesian (ι := Option (Fin 3))).apply_symm_apply _
  have hh := affineFSPrimitive_hopf_manifold hG c v
  simp only [Function.comp_apply] at hh
  rw [he,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh

 theorem cubicCoefficients_smooth {A B : ℕ} (D S : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ)
      ∞ (cubicCoefficients (A := A) (B := B) D S) :=
  contMDiff_pi_space.mpr (fun _ => weightedCoefficient_smooth _ _)

 theorem cubicCoefficients_squares {A B : ℕ} (D S : ℕ) (x : BaseCurve) :
    coefficientSquares (cubicCoefficients (A := A) (B := B) D S x)=
      fun i => coefficientNorm (cubicDegree D i) (cubicMarkedOrder S i) x := by
  funext i
  exact weightedCoefficient_norm _ _ _

 theorem physicalPolynomialLift_smoothAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0≤L) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B) :
    ContMDiffAt 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
      𝓘(ℝ,TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ) ∞
        (physicalPolynomialLift (A := A) (B := B) D S L) x := by
  have hG := (cubicCoefficients_smooth (A := A) (B := B) D S).comp (flatProduct_fst_smooth (V := PlanePhase (Fin 2)))
  have hz := (physicalDiskCoordinates L).contDiff.contMDiff.comp
    (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)))
  exact (normalizedToricLift_contDiffAt hA hAB (fun _ => weightedCoefficient_nonzero _ _ _)
    ((physicalDiskCoordinates_mem hL x.2).mpr hx)).contMDiffAt.comp x (hG.prodMk_space hz).contMDiffAt

 theorem physicalPolynomialLift_primitive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0<L) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B)
    (v : RealModel × PlanePhase (Fin 2)) :
    hopfPrimitive (1/(L*Real.pi)) (complexCartesian (physicalPolynomialLift (A := A) (B := B) D S L x))
      (complexCartesian (mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
        𝓘(ℝ,TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ)
          (physicalPolynomialLift (A := A) (B := B) D S L) x v))=
    (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
      (verticalLiouville : ManifoldOneForm (RealModel × PlanePhase (Fin 2)) (BaseCurve × PlanePhase (Fin 2)))) x v := by
  let G : BaseCurve × PlanePhase (Fin 2) → TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ :=
    fun q => cubicCoefficients D S q.1
  let z : BaseCurve × PlanePhase (Fin 2) → DiskPair := fun q => physicalDiskCoordinates L q.2
  have hG := (cubicCoefficients_smooth (A := A) (B := B) D S).comp (flatProduct_fst_smooth (V := PlanePhase (Fin 2)))
  have hz := (physicalDiskCoordinates L).contDiff.contMDiff.comp
    (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)))
  have hdG (i : TrapezoidWeight A B) :
      mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
        𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) G x v i=
      mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ)
        (weightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i)) x.1 v.1 := by
    have hi := (ContinuousLinearMap.proj i :
      (TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) →L[ℝ] (WeightedHomogeneousIndex → ℂ)).hasFDerivAt.hasMFDerivAt.comp x
          (hG.mdifferentiable (by simp) x).hasMFDerivAt
    have hf := manifoldMapDifferential_comp
      ((weightedCoefficient_smooth (cubicDegree D i) (cubicMarkedOrder S i)).mdifferentiable (by simp) x.1)
      ((flatProduct_fst_smooth (V := PlanePhase (Fin 2))).mdifferentiable (by simp) x)
    have he : mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,WeightedHomogeneousIndex → ℂ)
        (fun q : BaseCurve × PlanePhase (Fin 2) => G q i) x=
      (ContinuousLinearMap.proj i).comp
        (mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2))
          𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) G x) := hi.mfderiv
    have hev := congrArg (fun T => T v) he
    have hfv := congrArg (fun T => T v) hf
    simp only [manifoldMapDifferential] at hfv
    erw [flatProduct_fst_derivative] at hfv
    exact hev.symm.trans hfv
  have hdz : mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,DiskPair) z x v=
      physicalDiskCoordinates L v.2 := by
    have he := (physicalDiskCoordinates L).hasFDerivAt.hasMFDerivAt.comp x
      ((flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))).mdifferentiable (by simp) x).hasMFDerivAt
    rw [show mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,DiskPair) z x=_ from he.mfderiv,
      flatProduct_snd_derivative]
    rfl
  have hh := normalizedToricLift_manifold_primitive hA hAB
    (hG.mdifferentiable (by simp) x) (hz.mdifferentiable (by simp) x)
    (fun _ => weightedCoefficient_nonzero _ _ _) ((physicalDiskCoordinates_mem hL.le x.2).mpr hx) v (1/(L*Real.pi))
  change hopfPrimitive _ _ (complexCartesian (mfderiv _ _ (fun q => normalizedToricLift latticeIndex (G q) (z q)) x v))=_
  erw [hh]
  change (∑ i,selected latticeIndex (coefficientSquares (cubicCoefficients D S x.1))
      (squaredRadii (physicalDiskCoordinates L x.2)) i *
      hopfPrimitive _ (complexCartesian (weightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) x.1))
        (complexCartesian (mfderiv 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,TrapezoidWeight A B → WeightedHomogeneousIndex → ℂ) G x v i)))+_= _
  simp_rw [hdG,weightedCoefficient_hopf]
  erw [hdz]
  simp only [Function.comp_apply]
  erw [physicalDiskCoordinates_primitive hL]
  rw [cubicCoefficients_squares,physicalDiskCoordinates_squared hL.le]
  simp only [Pi.add_apply,add_apply,productHorizontalLift,physicalPrimitive,radialPrimitive,radialProbability,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',sum_apply,smul_apply,smul_eq_mul,
    verticalLiouville_apply,Function.comp_apply]

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CubicToricAmbient
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem ambientWeightedCoefficient_smooth (D m : ℕ) :
    ContDiff ℝ ∞ (ambientWeightedCoefficient D m) :=
  complexAffineLift_smooth.comp ((complexCartesian (ι := Option (Fin 3))).symm.contDiff.comp
    ((affinePhase 3).contDiff.comp ((weightedProjection_contDiff D m).restrict_scalars ℝ)))

 theorem conePolynomial_smooth {A B : ℕ} (D S : ℕ) :
    ContDiff ℝ ∞ (conePolynomial (A := A) (B := B) D S) := by
  apply contDiff_pi.mpr
  intro ij
  change ContDiff ℝ ∞ (fun p : CubicConeTarget => p.2.1^(latticeIndex ij.1).1 *
    p.2.2^(latticeIndex ij.1).2 * ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2)
  have hc : ContDiff ℝ ∞ (fun p : CubicConeTarget =>
      ambientWeightedCoefficient (cubicDegree D ij.1) (cubicMarkedOrder S ij.1) p.1 ij.2) :=
    (contDiff_apply ℝ ℂ ij.2).comp
    ((ambientWeightedCoefficient_smooth (cubicDegree D ij.1) (cubicMarkedOrder S ij.1)).comp contDiff_fst)
  exact (((contDiff_snd.fst).pow _).mul ((contDiff_snd.snd).pow _)).mul hc

 theorem centralCubicCoordinates_smooth :
    ContMDiff 𝓘(ℝ,CubicConeModel) 𝓘(ℝ,CubicConeTarget) ∞ centralCubicCoordinates :=
  (inclusion_real_contMDiff.comp (flatProduct_fst_smooth (V := DiskPair))).prodMk_space
    (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve))

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

 theorem manifoldPullbackOneForm_comp_at {g : N → G} {f : M → N} {x : M}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,G) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x) (α : G → G →L[ℝ] ℝ) :
    manifoldPullbackOneForm (E := F) (F := E)
        (fun _ => manifoldPullbackOneForm (E := G) (F := F) (fun _ => α) g 0) f 0 x=
      manifoldPullbackOneForm (E := G) (F := E) (fun _ => α) (g ∘ f) 0 x := by
  unfold manifoldPullbackOneForm
  rw [manifoldMapDifferential_comp hg hf]
  rfl

 theorem manifoldPullbackOneForm_primitive_at {g : F → G} {f : M → F} {x : M}
    (hg : DifferentiableAt ℝ g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x) (α : G → G →L[ℝ] ℝ) :
    manifoldPullbackOneForm (E := F) (F := E) (fun _ => primitivePullback α g) f 0 x=
      manifoldPullbackOneForm (E := G) (F := E) (fun _ => α) (g ∘ f) 0 x := by
  unfold manifoldPullbackOneForm primitivePullback manifoldMapDifferential
  rw [mfderiv_comp x hg.hasFDerivAt.hasMFDerivAt.mdifferentiableAt hf,mfderiv_eq_fderiv]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubic_radial_primitive_bp240_oai {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
    {L : ℝ} (hL : 0<L)
    {Ξ : BaseCurve × PlanePhase (Fin 2) → CubicConeSpace}
    (hΞ : ContMDiff 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,CubicConeModel) ∞ Ξ)
    (hΞfst : ∀ p,(Ξ p).1=p.1) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B)
    (he : ∀ᶠ q in 𝓝 x,(Ξ q).2=diskInverse latticeIndex
      (coefficientSquares (cubicCoefficients (A := A) (B := B) D S q.1)) (physicalDiskCoordinates L q.2)) :
    manifoldPullbackOneForm (fun _ => centralCubicPrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Ξ 0 x=
      (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))
          (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
        (verticalLiouville : ManifoldOneForm (RealModel × PlanePhase (Fin 2)) (BaseCurve × PlanePhase (Fin 2)))) x := by
  let P := complexCartesian ∘ conePolynomial (A := A) (B := B) D S
  have hP : ContDiff ℝ ∞ P := (complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).contDiff.comp (conePolynomial_smooth D S)
  let Y := centralCubicCoordinates ∘ Ξ
  have hY : ContMDiff 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,CubicConeTarget) ∞ Y := centralCubicCoordinates_smooth.comp hΞ
  have hh := manifoldPullbackOneForm_comp_at (centralCubicCoordinates_smooth.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Ξ x))
    (hΞ.mdifferentiable (by simp) x) (cubicConePrimitive (A := A) (B := B) D S (1/(L*Real.pi)))
  change manifoldPullbackOneForm (fun _ => centralCubicPrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Ξ 0 x=
    manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Y 0 x at hh
  rw [hh]
  have hpull := manifoldPullbackOneForm_primitive_at (hP.differentiable (by simp) (Y x))
    (hY.mdifferentiable (by simp) x) (hopfPrimitive (1/(L*Real.pi)))
  change manifoldPullbackOneForm (fun _ => cubicConePrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Y 0 x=_ at hpull
  rw [hpull]
  have heP : P ∘ Y=ᶠ[𝓝 x] complexCartesian ∘ physicalPolynomialLift (A := A) (B := B) D S L := by
    filter_upwards [he] with q hq
    change complexCartesian (toricLift latticeIndex
      (fun i => ambientWeightedCoefficient (cubicDegree D i) (cubicMarkedOrder S i) (inclusion (Ξ q).1)) (Ξ q).2)=_
    rw [hΞfst,hq]
    rfl
  have hQ := (physicalPolynomialLift_smoothAt hA hAB D S hL.le hx).mdifferentiableAt (by simp)
  apply ContinuousLinearMap.ext
  intro v
  unfold manifoldPullbackOneForm manifoldMapDifferential
  rw [heP.eq_of_nhds,heP.mfderiv_eq,mfderiv_comp x
    ((complexCartesian (ι := TrapezoidWeight A B × WeightedHomogeneousIndex)).hasFDerivAt.hasMFDerivAt.mdifferentiableAt) hQ,
    mfderiv_eq_fderiv,ContinuousLinearEquiv.fderiv]
  exact physicalPolynomialLift_primitive hA hAB D S hL hx v

end PackingSufficiencySupport.CubicModel

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240_oai
