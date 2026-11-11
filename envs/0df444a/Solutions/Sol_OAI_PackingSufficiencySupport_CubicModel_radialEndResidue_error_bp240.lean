-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:41.205989+00:00
-- url     : https://prove2.me/submissions/c06c68cd-d4ac-4da0-9d7b-164836f665f4

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

theorem complexAffineLift_sq (z : ι → ℂ) :
    phaseSq (complexCartesian (complexAffineLift z))=1+phaseSq (complexCartesian z) := by
  rw [complexCartesian_sq,complexCartesian_sq]
  simp [Fintype.sum_option]

theorem complexCartesian_complex_smul_sq (ζ : ℂ) (y : ι → ℂ) :
    phaseSq (complexCartesian (ζ•y))=Complex.normSq ζ*phaseSq (complexCartesian y) := by
  simp only [complexCartesian_sq,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]

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
-- module Solutions.OAIQ240_BP.BallPacking_Moments_AnalyticBoundary
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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

 theorem gibbs_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) (i : ι) :
    0<gibbs w a x i := div_pos (mul_pos (ha i) (Real.exp_pos _)) (partition_pos ha x)

 theorem sum_gibbs {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) :
    ∑ i,gibbs w a x i=1 := by
  simp only [gibbs,←Finset.sum_div]
  change partition w a x / partition w a x = 1
  exact div_self (partition_pos ha x).ne'

 omit [Nonempty ι] in
 theorem gibbs_mean {w : ι → E} {a : ι → ℝ} (x : E) :
    ∑ i,gibbs w a x i • w i=moment w a x := by
  simp only [gibbs,moment,gradient,Finset.smul_sum,smul_smul,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

 theorem gibbs_log {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) (i : ι) :
    Real.log (gibbs w a x i)=Real.log (a i)+inner ℝ (w i) x-Real.log (partition w a x) := by
  rw [gibbs,Real.log_div (mul_pos (ha i) (Real.exp_pos _)).ne' (partition_pos ha x).ne',
    Real.log_mul (ha i).ne' (Real.exp_ne_zero _),Real.log_exp]

 theorem scalar_relative_log {h q : ℝ} (hh : 0≤h) (hq : 0<q) :
    h*(Real.log q-Real.log h)≤q-h := by
  by_cases hz : h=0
  · simp [hz,hq.le]
  have hp : 0<h := lt_of_le_of_ne hh (Ne.symm hz)
  have he := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at he
  have hm := mul_le_mul_of_nonneg_left he hh
  have hcalc : h*(q/h-1)=q-h := by field_simp
  rwa [hcalc] at hm

 omit [Nonempty ι] in
 theorem relative_log_sum_le {h q : ι → ℝ} (hh : ∀ i,0≤h i) (hq : ∀ i,0<q i)
    (hhs : ∑ i,h i=1) (hqs : ∑ i,q i=1) :
    ∑ i,h i*(Real.log (q i)-Real.log (h i))≤0 := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar_relative_log (hh i) (hq i))
  simpa only [Finset.sum_sub_distrib,hhs,hqs,sub_self] using hb

 omit [Nonempty ι] in
 theorem probability_log_sum_nonpos {h : ι → ℝ} (hh : ∀ i,0≤h i) (hs : ∑ i,h i=1) :
    ∑ i,h i*Real.log (h i)≤0 := by
  classical
  apply Finset.sum_nonpos
  intro i _
  have hi : h i≤1 := by
    rw [←hs]
    exact Finset.single_le_sum (fun j _ => hh j) (Finset.mem_univ i)
  by_cases hz : h i=0
  · simp [hz]
  · exact mul_nonpos_of_nonneg_of_nonpos (hh i)
      (Real.log_nonpos (lt_of_le_of_ne (hh i) (Ne.symm hz)).le hi)

 omit [Nonempty ι] in
 theorem probability_log_sum_lower {q : ι → ℝ} (hq : ∀ i,0<q i) (hs : ∑ i,q i=1) :
    -(Fintype.card ι : ℝ)≤∑ i,q i*Real.log (q i) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar_relative_log (hq i).le (q := 1) zero_lt_one)
  simp only [Real.log_one,zero_sub,mul_neg,Finset.sum_neg_distrib,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hs] at hb
  linarith

end
section

variable {ι : Type*} [Fintype ι]

 theorem probability_weighted_le {q f : ι → ℝ} {M : ℝ}
    (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1) (hf : ∀ i,f i≤M) :
    ∑ i,q i*f i≤M := by
  calc
    _≤∑ i,q i*M := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq i))
    _=M := by rw [←Finset.sum_mul,hs,one_mul]

 theorem probability_weighted_ge {q f : ι → ℝ} {M : ℝ}
    (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1) (hf : ∀ i,M≤f i) :
    M≤∑ i,q i*f i := by
  calc
    M=∑ i,q i*M := by rw [←Finset.sum_mul,hs,one_mul]
    _≤_ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq i))

 theorem finite_log_height_bound {q h a b m : ι → ℝ} {l C M : ℝ}
    (hq : ∀ i,0<q i) (hqs : ∑ i,q i=1)
    (hh : ∀ i,0≤h i) (hhs : ∑ i,h i=1)
    (hlog : ∀ i,Real.log (q i)=Real.log (a i)+b i+l*m i-C)
    (hmean : ∑ i,q i*b i=∑ i,h i*b i)
    (ha : ∀ i,|Real.log (a i)|≤M) :
    (-l)*((∑ i,q i*m i)-(∑ i,h i*m i))≤2*M+Fintype.card ι := by
  have hrelative := relative_log_sum_le hh hq hhs hqs
  simp only [mul_sub,Finset.sum_sub_distrib] at hrelative
  have hentq := probability_log_sum_lower hq hqs
  have henth := probability_log_sum_nonpos hh hhs
  have hqlog : ∑ i,q i*Real.log (a i)≤M :=
    probability_weighted_le (fun i => (hq i).le) hqs (fun i => (abs_le.mp (ha i)).2)
  have hhlog : -M≤∑ i,h i*Real.log (a i) :=
    probability_weighted_ge hh hhs (fun i => (abs_le.mp (ha i)).1)
  have expand (t : ι → ℝ) (ht : ∑ i,t i=1) :
      ∑ i,t i*Real.log (q i)=(∑ i,t i*Real.log (a i))+(∑ i,t i*b i)+
        l*(∑ i,t i*m i)-C := by
    simp only [hlog,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [←Finset.sum_mul,ht,one_mul,Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expand h hhs] at hrelative
  rw [expand q hqs,hmean] at hentq
  nlinarith

 variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nonempty ι]

 theorem gibbs_tilt_log {w : ι → E} {a m : ι → ℝ} (ha : ∀ i,0<a i)
    (l : ℝ) (x : E) (i : ι) :
    Real.log (gibbs w (fun j => a j*Real.exp (l*m j)) x i)=
      Real.log (a i)+inner ℝ (w i) x+l*m i-
        Real.log (partition w (fun j => a j*Real.exp (l*m j)) x) := by
  rw [gibbs_log (fun j => mul_pos (ha j) (Real.exp_pos _)),
    Real.log_mul (ha i).ne' (Real.exp_ne_zero _),Real.log_exp]
  ring

 theorem gibbs_tilt_height_bound {w : ι → E} {a m h : ι → ℝ} {M : ℝ}
    (ha : ∀ i,0<a i) (hloga : ∀ i,|Real.log (a i)|≤M)
    (hh : ∀ i,0≤h i) (hhs : ∑ i,h i=1) (l : ℝ) (x : E)
    (hmean : ∑ i,h i • w i=moment w (fun j => a j*Real.exp (l*m j)) x) :
    (-l)*((∑ i,gibbs w (fun j => a j*Real.exp (l*m j)) x i*m i)-(∑ i,h i*m i))
      ≤2*M+Fintype.card ι := by
  have hpos (i : ι) : 0<a i*Real.exp (l*m i) := mul_pos (ha i) (Real.exp_pos _)
  apply finite_log_height_bound (gibbs_pos hpos x) (sum_gibbs hpos x) hh hhs
    (gibbs_tilt_log ha l x) _ hloga
  have he := congrArg (fun p : E => inner ℝ p x) ((gibbs_mean (w := w)
    (a := fun j => a j*Real.exp (l*m j)) x).trans hmean.symm)
  simpa only [sum_inner,real_inner_smul_left] using he

end
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 omit [Nonempty ι] in
 theorem partition_scale_translate (w : ι → E) (a : ι → ℝ) (C : ℝ) (x z : E) :
    partition w (fun i => C*a i*Real.exp (inner ℝ (w i) z)) x=
      C*partition w a (x+z) := by
  simp only [partition,inner_add_right,Real.exp_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

 omit [Nonempty ι] in
 theorem gibbs_scale_translate (w : ι → E) (a : ι → ℝ) {C : ℝ} (hC : C≠0)
    (x z : E) (i : ι) :
    gibbs w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) x i=gibbs w a (x+z) i := by
  unfold gibbs
  rw [partition_scale_translate]
  simp only [inner_add_right,Real.exp_add]
  have hn : C*a i*Real.exp (inner ℝ (w i) z)*Real.exp (inner ℝ (w i) x)=
      C*(a i*(Real.exp (inner ℝ (w i) x)*Real.exp (inner ℝ (w i) z))) := by ring
  rw [hn,mul_div_mul_left _ _ hC]

 omit [Nonempty ι] in
 theorem moment_scale_translate (w : ι → E) (a : ι → ℝ) {C : ℝ} (hC : C≠0)
    (x z : E) : moment w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) x=
      moment w a (x+z) := by
  rw [←gibbs_mean,←gibbs_mean]
  simp only [gibbs_scale_translate w a hC]

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 omit [FiniteDimensional ℝ E] in
 theorem selected_sum {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (p : E) :
    ∑ i,selected w a p i=1 := sum_gibbs ha _

 theorem selected_mean {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : ∑ i,selected w a p i • w i=p :=
  (gibbs_mean _).trans (inverse_spec ha hp)

 theorem selected_gauge {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i)
    {C : ℝ} (hC : 0<C) {p : E} (hp : Surrounds w p) (z : E) (i : ι) :
    selected w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) p i=selected w a p i := by
  have hb (j : ι) : 0<C*a j*Real.exp (inner ℝ (w j) z) :=
    mul_pos (mul_pos hC (ha j)) (Real.exp_pos _)
  have hm : moment w a (inverse w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) p+z)=p := by
    rw [←moment_scale_translate w a hC.ne']
    exact inverse_spec hb hp
  unfold selected
  rw [gibbs_scale_translate w a hC.ne',inverse_unique ha hp hm]

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

theorem probability_sum {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) : ∑ i,probability k a r i=1 := by
  simp only [probability,← Finset.sum_div]
  exact div_self hP

theorem probability_mean (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    (∑ i,probability k a r i*((k i).1:ℝ),∑ i,probability k a r i*((k i).2:ℝ))=moment k a r := by
  apply Prod.ext
  · change (∑ i,probability k a r i*((k i).1:ℝ))=
      (polynomial k a r)⁻¹*(∑ i,((k i).1:ℝ)*a i*monomial (k i) r)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [probability]
    ring
  · change (∑ i,probability k a r i*((k i).2:ℝ))=
      (polynomial k a r)⁻¹*(∑ i,((k i).2:ℝ)*a i*monomial (k i) r)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [probability]
    ring

theorem probability_contDiffAt (k : ι → ℕ × ℕ) {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) (i : ι) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => probability k q.1 q.2 i) (a,r) := by
  apply ContDiffAt.div _ (polynomial_contDiff k).contDiffAt hP
  dsimp [monomial]
  fun_prop

theorem probability_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) (i : ι) :
    probability k a (expRadius x) i=gibbs (weight k) a x i := by
  simp only [probability,monomial_expRadius,polynomial_expRadius,gibbs,weight]

theorem selected_sum {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (p : Plane) : ∑ i,selected k a p i=1 :=
  probability_sum (polynomial_pos ha h0 (nonnegativeInverse_nonneg _ _ _)).ne'

theorem selected_eq_exponential [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) (i : ι) :
    selected k a p i=FiniteMoment.selected (weight k) a (planeVector p.1 p.2) i := by
  unfold selected
  rw [nonnegativeInverse_exp ha h0 he0 he1 hp,probability_expRadius]
  rfl

end

theorem trapezoid_selected_contDiffWithinAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContDiffWithinAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × Plane => selected latticeIndex q.1 q.2 i)
      {q | (∀ j,0<q.1 j) ∧ q.2∈lowerTrapezoid A B} (a,p) := by
  have hi := trapezoid_inverse_contDiffWithinAt hA hAB ha hp
  have hs := probability_contDiffAt latticeIndex
    (polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg latticeIndex a p)).ne' i
  have hmap := contDiffWithinAt_fst.prodMk hi
  have hc := hs.comp_contDiffWithinAt (a,p) hmap
  exact hc

theorem trapezoid_selected_mean {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∑ i,selected latticeIndex a p i • trapezoidWeight A B i=planeVector p.1 p.2 := by
  have he := (probability_mean latticeIndex a (nonnegativeInverse latticeIndex a p)).trans
    (trapezoid_inverse_spec hAB ha hp)
  ext j
  fin_cases j
  · simpa [trapezoidWeight,planeVector,latticeIndex,selected] using congrArg Prod.fst he
  · simpa [trapezoidWeight,planeVector,latticeIndex,selected] using congrArg Prod.snd he

end PackingSufficiencySupport.FiniteMoment.Radial

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexWeights
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Set
section
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

 theorem convexHull_range_weights {w : ι → E} {p : E}
    (hp : p∈convexHull ℝ (range w)) :
    ∃ h : ι → ℝ,(∀ i,0≤h i) ∧ (∑ i,h i)=1 ∧ ∑ i,h i • w i=p := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hp
  obtain ⟨s,c,hc,hs,hp⟩ := hp
  refine ⟨fun i => if i∈s then c i else 0,?_,?_,?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact hc i hi
    · exact le_rfl
  · simpa only [Finset.sum_ite_mem,Finset.univ_inter] using hs
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hp
    simpa only [ite_smul,zero_smul,Finset.sum_ite_mem,Finset.univ_inter] using hp

end

 theorem closedTrapezoid_mem_convexHull {A B : ℝ} (hA : 0<A) (hAB : A≤B)
    {p : MomentPlane} (hp : p∈closedTrapezoid A B) :
    p∈convexHull ℝ (range (trapezoidCorners A B)) := by
  by_cases hz : B-p 0=0
  · have hp0 : p 0=A := by linarith [hp.2.1]
    have hp1 : p 1=0 := by linarith [hp.2.2.1,hp.2.2.2]
    have he : p=trapezoidCorners A B 1 := by
      ext j
      fin_cases j <;> simp [trapezoidCorners,planeVector,hp0,hp1]
    exact he ▸ subset_convexHull ℝ _ (mem_range_self 1)
  have hB : 0<B-p 0 := lt_of_le_of_ne (by linarith [hp.2.2.1,hp.2.2.2]) (Ne.symm hz)
  let l := p 0/A
  let t := p 1/(B-p 0)
  have hl0 : 0≤l := div_nonneg hp.1 hA.le
  have hl1 : l≤1 := (div_le_one hA).mpr hp.2.1
  have ht0 : 0≤t := div_nonneg hp.2.2.1 hB.le
  have ht1 : t≤1 := (div_le_one hB).mpr (by linarith [hp.2.2.2])
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

 theorem convex_affine_height_preimage {H : Set (MomentPlane × ℝ)}
    (hH : Convex ℝ H) (S : ℝ) : Convex ℝ {p : MomentPlane | (p,S-p 0-p 1)∈H} := by
  intro p hp q hq a b ha hb hab
  have he := hH hp hq ha hb hab
  change (a • p + b • q,S-(a • p+b • q) 0-(a • p+b • q) 1)∈H
  convert he using 2
  all_goals try with_reducible_and_instances rfl
  change S-(a*p 0+b*q 0)-(a*p 1+b*q 1)=a*(S-p 0-p 1)+b*(S-q 0-q 1)
  linear_combination -S * hab

 theorem convex_zero_height_preimage {H : Set (MomentPlane × ℝ)}
    (hH : Convex ℝ H) : Convex ℝ {p : MomentPlane | (p,0)∈H} := by
  intro p hp q hq a b ha hb hab
  change (a • p+b • q,0)∈H
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero] using hH hp hq ha hb hab

 theorem lattice_height_mem {A B S i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) :
    (planeVector i j,markedHeight S (planeVector i j))∈heightHull A B S :=
  subset_convexHull ℝ _ ⟨latticeIndex hi hij,rfl⟩

 theorem lattice_lower_mem {A B S i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) (hs : i+j ≤ S) :
    (planeVector i j,(S:ℝ)-i-j)∈heightHull A B S := by
  have hs' : (i:ℝ)+j ≤ S := by exact_mod_cast hs
  have he := lattice_height_mem (S := S) hi hij
  change (planeVector i j,max ((S:ℝ)-i-j) 0)∈heightHull A B S at he
  simpa only [max_eq_left (by linarith : 0 ≤ (S:ℝ)-i-j)] using he

 theorem lattice_upper_mem {A B S i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) (hs : S ≤ i+j) :
    (planeVector i j,0)∈heightHull A B S := by
  have hs' : (S : ℝ)  ≤  (i : ℝ) + j := by exact_mod_cast hs
  have he := lattice_height_mem (S := S) hi hij
  change (planeVector i j,max ((S:ℝ)-i-j) 0)∈heightHull A B S at he
  simpa only [max_eq_right (by linarith : (S:ℝ)-i-j ≤ 0)] using he

 theorem lower_height_mem {A B S : ℕ} (hA : 0<A) (hS : 0<S) (hSB : S ≤ B)
    {p : MomentPlane} (hp : p∈closedTrapezoid A B) (hps : p 0+p 1 ≤ S) :
    (p,markedHeight S p)∈heightHull A B S := by
  have hm : 0 < min A S := lt_min hA hS
  have hms : min A S ≤ S := min_le_right _ _
  have hmc : ((min A S : ℕ) : ℝ) ≤ S := by exact_mod_cast hms
  have hp' : p∈closedTrapezoid (min A S : ℕ) S := by
    refine ⟨hp.1,?_,hp.2.2.1,hps⟩
    rw [Nat.cast_min]
    exact le_min hp.2.1 (by linarith [hp.2.2.1])
  have he := closedTrapezoid_mem_convexHull (by exact_mod_cast hm) hmc hp'
  have hc : Convex ℝ {q : MomentPlane | (q,(S:ℝ)-q 0-q 1)∈heightHull A B S} :=
    convex_affine_height_preimage (convex_convexHull ℝ _) S
  have hs : range (trapezoidCorners (min A S : ℕ) S)⊆
      {q : MomentPlane | (q,(S:ℝ)-q 0-q 1)∈heightHull A B S} := by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · simpa [trapezoidCorners,planeVector] using lattice_lower_mem (A := A) (B := B) (S := S)
        (i := 0) (j := 0) (by omega) (by omega) (by omega)
    · simpa [trapezoidCorners,planeVector] using lattice_lower_mem (A := A) (B := B) (S := S)
        (i := min A S) (j := 0) (by omega) (by omega) (by omega)
    · simpa [trapezoidCorners,planeVector,Nat.cast_sub hms] using
        lattice_lower_mem (A := A) (B := B) (S := S)
          (i := min A S) (j := S-min A S) (by omega) (by omega) (by omega)
    · simpa [trapezoidCorners,planeVector] using lattice_lower_mem (A := A) (B := B) (S := S)
        (i := 0) (j := S) (by omega) (by omega) (by omega)
  have h := convexHull_min hs hc he
  simpa only [mem_ofPred_eq,markedHeight,max_eq_left (by linarith : 0 ≤ (S:ℝ)-p 0-p 1)] using h

 theorem convex_diagonal_segment {T : Set MomentPlane} (hT : Convex ℝ T)
    {C D x : ℝ} (hC : 0<C) (hx0 : 0 ≤ x) (hxC : x ≤ C)
    (h0 : planeVector 0 D∈T) (h1 : planeVector C (D-C)∈T) :
    planeVector x (D-x)∈T := by
  have hl0 : 0 ≤ x/C := div_nonneg hx0 hC.le
  have hl1 : x/C ≤ 1 := (div_le_one hC).mpr hxC
  convert hT h0 h1 (sub_nonneg.mpr hl1) hl0 (by ring : (1-x/C)+x/C=1) using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  fin_cases j
  all_goals simp [planeVector]
  all_goals field_simp
  all_goals ring

 theorem convex_horizontal_segment {T : Set MomentPlane} (hT : Convex ℝ T)
    {C D x y : ℝ} (hCD : C<D) (hxC : C ≤ x) (hxD : x ≤ D)
    (h0 : planeVector C y∈T) (h1 : planeVector D y∈T) :
    planeVector x y∈T := by
  have hl0 : 0 ≤ (x-C)/(D-C) := div_nonneg (sub_nonneg.mpr hxC) (sub_pos.mpr hCD).le
  have hl1 : (x-C)/(D-C) ≤ 1 := (div_le_one (sub_pos.mpr hCD)).mpr (by linarith)
  convert hT h0 h1 (sub_nonneg.mpr hl1) hl0
    (by ring : (1-(x-C)/(D-C))+(x-C)/(D-C)=1) using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  fin_cases j
  all_goals simp [planeVector]
  all_goals field_simp [(sub_pos.mpr hCD).ne', (by linarith : -C+D≠0)]
  all_goals ring

 theorem convex_vertical_segment {T : Set MomentPlane} (hT : Convex ℝ T)
    {C D x y : ℝ} (hyC : C ≤ y) (hyD : y ≤ D)
    (h0 : planeVector x C∈T) (h1 : planeVector x D∈T) :
    planeVector x y∈T := by
  by_cases he : C=D
  · have hCy : C=y := by linarith
    rwa [←hCy]
  have hCD : C<D := lt_of_le_of_ne (hyC.trans hyD) he
  have hl0 : 0 ≤ (y-C)/(D-C) := div_nonneg (sub_nonneg.mpr hyC) (sub_pos.mpr hCD).le
  have hl1 : (y-C)/(D-C) ≤ 1 := (div_le_one (sub_pos.mpr hCD)).mpr (by linarith)
  convert hT h0 h1 (sub_nonneg.mpr hl1) hl0
    (by ring : (1-(y-C)/(D-C))+(y-C)/(D-C)=1) using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  fin_cases j
  all_goals simp [planeVector]
  all_goals field_simp [(sub_pos.mpr hCD).ne', (by linarith : -C+D≠0)]
  all_goals ring

 theorem upper_height_mem {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A ≤ B) (hSB : S ≤ B) {p : MomentPlane}
    (hp : p∈closedTrapezoid A B) (hps : (S:ℝ) ≤ p 0+p 1) :
    (p,markedHeight S p)∈heightHull A B S := by
  let T : Set MomentPlane := {q | (q,0)∈heightHull A B S}
  have hT : Convex ℝ T := convex_zero_height_preimage (convex_convexHull ℝ _)
  have hA' : (0:ℝ)<A := by exact_mod_cast hA
  have htop : planeVector (p 0) ((B:ℝ)-p 0)∈T := by
    apply convex_diagonal_segment hT hA' hp.1 hp.2.1
    · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := 0) (j := B) (by omega) (by omega) (by omega)
    · simpa only [T,mem_ofPred_eq,Nat.cast_sub hAB] using
        lattice_upper_mem (A := A) (B := B) (S := S) (i := A) (j := B-A) (by omega) (by omega) (by omega)
  have hbottom : planeVector (p 0) (max ((S:ℝ)-p 0) 0)∈T := by
    by_cases hx : p 0 ≤ (min A S : ℕ)
    · have hms : min A S ≤ S := min_le_right _ _
      have hmc : ((min A S : ℕ) : ℝ) ≤ S := by exact_mod_cast hms
      rw [max_eq_left (by linarith : 0 ≤ (S:ℝ)-p 0)]
      apply convex_diagonal_segment hT (by exact_mod_cast (lt_min hA hS)) hp.1 hx
      · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := 0) (j := S) (by omega) (by omega) (by omega)
      · simpa only [T,mem_ofPred_eq,Nat.cast_sub hms] using
          lattice_upper_mem (A := A) (B := B) (S := S) (i := min A S) (j := S-min A S)
            (by omega) (by omega) (by omega)
    · have hSA : S<A := by
        by_contra he
        have he' : min A S=A := min_eq_left (by omega)
        rw [he'] at hx
        exact hx hp.2.1
      have hxS : (S:ℝ)<p 0 := by simpa only [min_eq_right hSA.le] using lt_of_not_ge hx
      rw [max_eq_right (by linarith : (S:ℝ)-p 0 ≤ 0)]
      apply convex_horizontal_segment hT (by exact_mod_cast hSA) hxS.le hp.2.1
      · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := S) (j := 0) (by omega) (by omega) (by omega)
      · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := A) (j := 0) (by omega) (by omega) (by omega)
  have he := convex_vertical_segment hT (max_le (by linarith) hp.2.2.1)
    (by linarith [hp.2.2.2] : p 1 ≤ (B:ℝ)-p 0) hbottom htop
  have hpv : planeVector (p 0) (p 1)=p := by ext j; fin_cases j <;> rfl
  rw [hpv] at he
  simpa only [T,mem_ofPred_eq,markedHeight,max_eq_right (by linarith : (S:ℝ)-p 0-p 1 ≤ 0)] using he

 theorem markedHeight_feasible {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A ≤ B) (hSB : S ≤ B) {p : MomentPlane} (hp : p∈closedTrapezoid A B) :
    ∃ h : TrapezoidWeight A B → ℝ,(∀ k,0 ≤ h k) ∧ (∑ k,h k)=1 ∧
      (∑ k,h k • trapezoidWeight A B k)=p ∧
      (∑ k,h k*markedHeight S (trapezoidWeight A B k))=markedHeight S p := by
  have hh : (p,markedHeight S p)∈heightHull A B S := by
    rcases le_total (p 0+p 1) (S:ℝ) with hs|hs
    · exact lower_height_mem hA hS hSB hp hs
    · exact upper_height_mem hA hS hAB hSB hp hs
  obtain ⟨h,hn,hs,he⟩ := convexHull_range_weights hh
  refine ⟨h,hn,hs,?_,?_⟩
  · simpa only [heightGraph,Prod.fst_sum,Prod.smul_fst] using congrArg Prod.fst he
  · simpa only [heightGraph,Prod.snd_sum,Prod.smul_snd,smul_eq_mul] using congrArg Prod.snd he

 theorem markedHeight_jensen {ι : Type*} [Fintype ι] {w : ι → MomentPlane}
    {q : ι → ℝ} {p : MomentPlane} (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1)
    (he : ∑ i,q i • w i=p) (S : ℝ) :
    markedHeight S p≤∑ i,q i*markedHeight S (w i) := by
  have hcoord (j : Fin 2) : ∑ i,q i*(w i) j=p j := by
    have h := congrArg (fun z : MomentPlane => z j) he
    simpa using h
  have hsum : ∑ i,q i*(S-(w i) 0-(w i) 1)=S-p 0-p 1 := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [←Finset.sum_mul,hs,one_mul,hcoord 0,hcoord 1]
  apply max_le
  · rw [←hsum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hq i))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (le_max_right _ _))

 theorem marked_gibbs_error {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A≤B) (hSB : S≤B) {a : TrapezoidWeight A B → ℝ} {M l : ℝ}
    (ha : ∀ k,0<a k) (hloga : ∀ k,|Real.log (a k)|≤M) (hl : l<0)
    (x : MomentPlane) {p : MomentPlane} (hp : p∈closedTrapezoid A B)
    (hm : moment (trapezoidWeight A B)
      (fun k => a k*Real.exp (l*markedHeight S (trapezoidWeight A B k))) x=p) :
    0≤(∑ k,gibbs (trapezoidWeight A B)
      (fun j => a j*Real.exp (l*markedHeight S (trapezoidWeight A B j))) x k*
        markedHeight S (trapezoidWeight A B k))-markedHeight S p ∧
    (∑ k,gibbs (trapezoidWeight A B)
      (fun j => a j*Real.exp (l*markedHeight S (trapezoidWeight A B j))) x k*
        markedHeight S (trapezoidWeight A B k))-markedHeight S p
      ≤(2*M+Fintype.card (TrapezoidWeight A B))/(-l) := by
  have ha' (k : TrapezoidWeight A B) :
      0<a k*Real.exp (l*markedHeight S (trapezoidWeight A B k)) :=
    mul_pos (ha k) (Real.exp_pos _)
  constructor
  · exact sub_nonneg.mpr (markedHeight_jensen (fun k => (gibbs_pos ha' x k).le)
      (sum_gibbs ha' x) ((gibbs_mean x).trans hm) S)
  · obtain ⟨h,hn,hs,hmean,hheight⟩ := markedHeight_feasible hA hS hAB hSB hp
    have hbound := gibbs_tilt_height_bound ha hloga hn hs l x (hmean.trans hm.symm)
    rw [hheight] at hbound
    exact (le_div_iff₀ (neg_pos.mpr hl)).mpr (by simpa only [mul_comm] using hbound)

 theorem probability_affine_height {ι : Type*} [Fintype ι] {w : ι → MomentPlane}
    {q : ι → ℝ} {p : MomentPlane} (hs : ∑ i,q i=1)
    (he : ∑ i,q i • w i=p) (D c S : ℝ) :
    (∑ i,q i*(D-c*((w i) 0+(w i) 1)-markedHeight S (w i)))=
      D-c*(p 0+p 1)-(∑ i,q i*markedHeight S (w i)) := by
  have hcoord (j : Fin 2) : ∑ i,q i*(w i) j=p j := by
    have h := congrArg (fun z : MomentPlane => z j) he
    simpa using h
  calc
    _=(∑ i,q i*D)-c*(∑ i,q i*(w i) 0)-c*(∑ i,q i*(w i) 1)-
        (∑ i,q i*markedHeight S (w i)) := by
      simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=_ := by rw [←Finset.sum_mul,hs,one_mul,hcoord 0,hcoord 1]; ring

end PackingSufficiencySupport.FiniteMoment

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem removableCoordinate_eq {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) (j : Fin 2) :
    (infinityRoot (parameters 0) zeroEnd s j-1)/s=removableCoordinate s j := by
  have hq := infinityRoot_sq (parameters 0) zeroEnd s j
  dsimp [removableCoordinate]
  apply (div_eq_div_iff hs (hR.2 j)).mpr
  linear_combination hq

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

theorem complexCartesian_affineComplex (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  ext i <;> cases i <;> rfl

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 theorem endCoordinate_false {ε : EndIndex} {j : Fin 2} (hj : ε j=false)
    {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    (infinityRoot (parameters 0) ε s j-1)/s=s*endCoefficient s j := by
  have he : infinityRoot (parameters 0) ε s j=infinityRoot (parameters 0) zeroEnd s j := by
    simp only [infinityRoot,endSign,hj,zeroEnd]
    rfl
  rw [he,removableCoordinate_eq hs hR]
  dsimp [removableCoordinate,endCoefficient]
  ring

 theorem weightedEndRegular_none (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    weightedEndRegular D m ε s none=s^(weightedEndOrder D m ε) := by
  cases h0 : ε 0 <;> cases h1 : ε 1 <;>
    simp [weightedEndRegular,weightedEndOrder,h0,h1,five]

 theorem weightedEndRegular_ne_zero (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    weightedEndRegular D m ε s≠0 := by
  intro he
  by_cases hs : s=0
  · subst s
    cases h0 : ε 0 <;> cases h1 : ε 1
    · exact (one_ne_zero : (1:ℂ)≠0) (by simpa [weightedEndRegular,h0,h1,complexAffineLift] using congrFun he none)
    · have hz := congrFun he (some (some 0))
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
    · have hz := congrFun he (some none)
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
    · have hz := congrFun he (some (some 1))
      norm_num [weightedEndRegular,h0,h1,five,endNumerator,infinityRoot,endSign] at hz
  · exact (pow_ne_zero _ hs) (by simpa only [weightedEndRegular_none,Pi.zero_apply] using congrFun he none)

 theorem weightedEndRegular_cartesian_ne_zero (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    complexCartesian (weightedEndRegular D m ε s)≠0 := by
  intro h
  exact weightedEndRegular_ne_zero D m ε s (complexCartesian.injective (by simpa only [map_zero] using h))

 theorem scale_div_pow {s : ℂ} (hs : s≠0) (a : ℂ) (L : ℕ) :
    s^L*(a/s)^L=a^L := by
  rw [←mul_pow,mul_div_cancel₀ a hs]

 theorem scale_complement_pow {s : ℂ} (hs : s≠0) (a : ℂ) {D m : ℕ} (hm : m≤D) :
    s^D*(a/s)^(D-m)=s^m*a^(D-m) := by
  have hD : m+(D-m)=D := Nat.add_sub_of_le hm
  have hp : s^D=s^m*s^(D-m) := by rw [←pow_add,hD]
  calc
    _=s^m*(s^(D-m)*(a/s)^(D-m)) := by rw [hp]; ring
    _=_ := by rw [scale_div_pow hs]

 theorem scale_div_mixed {s : ℂ} (hs : s≠0) (a b : ℂ) (L m : ℕ) :
    s^(L+m)*((a/s)^L*(b/s)^m)=a^L*b^m := by
  calc
    _=(s^L*(a/s)^L)*(s^m*(b/s)^m) := by rw [pow_add]; ring
    _=_ := by rw [scale_div_pow hs,scale_div_pow hs]

 theorem scale_regular_pow (s b : ℂ) (L : ℕ) :
    s^L*(s*b)^L=s^(2*L)*b^L := by
  rw [mul_pow,two_mul,pow_add]
  ring

 theorem scale_onepole_mixed {s : ℂ} (hs : s≠0) (a b : ℂ) (L m : ℕ) :
    s^L*((a/s)^L*(s*b)^m)=s^m*a^L*b^m := by
  calc
    _=(s^L*(a/s)^L)*(s^m*b^m) := by rw [mul_pow]; ring
    _=_ := by rw [scale_div_pow hs]; ring

 theorem scale_onepole_cross {s : ℂ} (hs : s≠0) (a b : ℂ) {L m : ℕ} (hm : m≤2*L) :
    s^L*((a/s)^m*(s*b)^L)=s^(2*L-m)*a^m*b^L := by
  rw [pow_sub₀ s hs hm,two_mul,pow_add,div_pow,mul_pow]
  simp only [div_eq_mul_inv]
  ring

 theorem weightedLift_scale_poles {D m : ℕ} (hm : m≤D) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^D • weightedLift D m (a/s) (b/s)=
      five (s^D) (s^m*a^(D-m)) (s^m*b^(D-m)) (a^(D-m)*b^m) (a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^D*1=s^D; exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_complement_pow hs a hm
    | some j =>
      fin_cases j
      · exact scale_complement_pow hs b hm
      · change s^D*((a/s)^(D-m)*(b/s)^m)=a^(D-m)*b^m
        simpa only [Nat.sub_add_cancel hm] using scale_div_mixed hs a b (D-m) m
      · change s^D*((a/s)^m*(b/s)^(D-m))=a^m*b^(D-m)
        simpa only [Nat.add_sub_of_le hm] using scale_div_mixed hs a b m (D-m)

 theorem weightedLift_scale_left {D m : ℕ} (hm : m≤2*(D-m)) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^(D-m) • weightedLift D m (a/s) (s*b)=
      five (s^(D-m)) (a^(D-m)) (s^(2*(D-m))*b^(D-m))
        (s^m*a^(D-m)*b^m) (s^(2*(D-m)-m)*a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^(D-m)*1=s^(D-m); exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_div_pow hs a (D-m)
    | some j =>
      fin_cases j
      · exact scale_regular_pow s b (D-m)
      · exact scale_onepole_mixed hs a b (D-m) m
      · exact scale_onepole_cross hs a b hm

 theorem weightedLift_scale_right {D m : ℕ} (hm : m≤2*(D-m)) {s : ℂ} (hs : s≠0) (a b : ℂ) :
    s^(D-m) • weightedLift D m (s*a) (b/s)=
      five (s^(D-m)) (s^(2*(D-m))*a^(D-m)) (b^(D-m))
        (s^(2*(D-m)-m)*a^(D-m)*b^m) (s^m*a^m*b^(D-m)) := by
  funext j
  cases j with
  | none => change s^(D-m)*1=s^(D-m); exact mul_one _
  | some j =>
    cases j with
    | none => exact scale_regular_pow s a (D-m)
    | some j =>
      fin_cases j
      · exact scale_div_pow hs b (D-m)
      · change s^(D-m)*((s*a)^(D-m)*(b/s)^m)=s^(2*(D-m)-m)*a^(D-m)*b^m
        calc
          _=s^(D-m)*((b/s)^m*(s*a)^(D-m)) := by ring
          _=s^(2*(D-m)-m)*b^m*a^(D-m) := scale_onepole_cross hs b a hm
          _=_ := by ring
      · change s^(D-m)*((s*a)^m*(b/s)^(D-m))=s^m*a^m*b^(D-m)
        calc
          _=s^(D-m)*((b/s)^(D-m)*(s*a)^m) := by ring
          _=s^m*b^(D-m)*a^m := scale_onepole_mixed hs b a (D-m) m
          _=_ := by ring

 theorem weightedEndRegular_scale {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {s : ℂ} (hs : s≠0) (hR : s∈endRegularRegion) :
    weightedEndRegular D m ε s=s^(weightedEndOrder D m ε)•complexAffineLift (weightedEndQuotient D m ε s) := by
  cases h0 : ε 0 <;> cases h1 : ε 1
  · have h00 := endCoordinate_false h0 hs hR
    have h11 := endCoordinate_false h1 hs hR
    simp only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h00,h11,pow_zero,one_smul]
  · have h00 := endCoordinate_false h0 hs hR
    simpa only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h00,weightedLift,endNumerator] using
      (weightedLift_scale_right h2 hs (endCoefficient s 0) (endNumerator ε s 1)).symm
  · have h11 := endCoordinate_false h1 hs hR
    simpa only [weightedEndRegular,weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,
      weightedEndQuotient,endQuotient,h11,weightedLift,endNumerator] using
      (weightedLift_scale_left h2 hs (endNumerator ε s 0) (endCoefficient s 1)).symm
  · simpa only [weightedEndRegular,weightedEndOrder,h0,h1,↓reduceIte,
      weightedEndQuotient,endQuotient,weightedLift,endNumerator] using
      (weightedLift_scale_poles hm hs (endNumerator ε s 0) (endNumerator ε s 1)).symm

 theorem weightedEndQuotient_phase (D m : ℕ) (ε : EndIndex) (s : ℂ) :
    complexCartesian (weightedEndQuotient D m ε s)=
      affinePhase 3 (weightedProjection D m (projection (infinityPoint (parameters 0) ε s))) := by
  rw [weightedEndQuotient,complexCartesian_affineComplex]
  congr 2
  apply Prod.ext
  · change (infinityRoot (parameters 0) ε s 0-1)/s=s⁻¹*infinityRoot (parameters 0) ε s 0-s⁻¹
    simp only [div_eq_mul_inv]
    ring
  · change (infinityRoot (parameters 0) ε s 1-1)/s=s⁻¹*infinityRoot (parameters 0) ε s 1-s⁻¹
    simp only [div_eq_mul_inv]
    ring

 theorem weighted_infinityPhase_germ (D m : ℕ) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    (weightedPhaseInclusion D m ∘ infinityDiffeomorph (parameters 0) ε)=ᶠ[𝓝 y]
      fun z => complexCartesian (weightedEndQuotient D m ε (Complex.equivRealProdCLM.symm z)) := by
  filter_upwards [(infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy] with z hz
  have hzD : Complex.equivRealProdCLM.symm z∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hz
  rw [weightedEndQuotient_phase]
  change affinePhase 3 (weightedProjection D m (projection ((infinityInverse (parameters 0) ε
    (Complex.equivRealProdCLM.symm z)).val)))=_
  rw [infinityInverse_val _ ε hzD.1]

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem coefficientNorm_pos (D m : ℕ) (x : BaseCurve) : 0 < coefficientNorm D m x := by
  dsimp [coefficientNorm]
  linarith [phaseSq_nonneg (weightedPhaseInclusion D m x)]

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_other _root_.OAI.PackingSufficiencySupport.Hamiltonian.outerMoments_self _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricAngularSpeed_flow _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricFlow_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply _root_.OAI.PackingSufficiencySupport.MomentPolytope.assemble_outerMoments _root_.OAI.PackingSufficiencySupport.MomentPolytope.baseProjection_outerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold Filter

theorem radiusSq_complex (z : Plane) : Complex.normSq (Complex.equivRealProdCLM.symm z)=radiusSq z := by
  change z.1*z.1+z.2*z.2=z.1^2+z.2^2
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

 theorem regularCoefficientNorm_pos (D m : ℕ) (ε : EndIndex) (y : Plane) :
    0 < regularCoefficientNorm D m ε y := phaseSq_pos (weightedEndRegular_cartesian_ne_zero D m ε _)

 theorem coefficientNorm_regularization {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    regularCoefficientNorm D m ε y=(radiusSq y)^(weightedEndOrder D m ε)*
      coefficientNorm D m (infinityDiffeomorph (parameters 0) ε y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  dsimp [regularCoefficientNorm,weightedRegularEndPhase]
  rw [weightedEndRegular_scale hm h2 ε hD.1 hR,complexCartesian_complex_smul_sq,map_pow,
    complexAffineLift_sq,radiusSq_complex]
  congr 2
  exact congrArg phaseSq (weighted_infinityPhase_germ D m ε hy).eq_of_nhds.symm

 theorem coefficientNorm_eq_regular_div {D m : ℕ} (hm : m≤D) (h2 : m≤2*(D-m))
    (ε : EndIndex) {y : Plane} (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    coefficientNorm D m (infinityDiffeomorph (parameters 0) ε y)=
      regularCoefficientNorm D m ε y/(radiusSq y)^(weightedEndOrder D m ε) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hz : radiusSq y≠0 := by
    rw [←radiusSq_complex]
    exact (Complex.normSq_pos.mpr hD.1).ne'
  rw [coefficientNorm_regularization hm h2 ε hy hR,mul_div_cancel_left₀ _ (pow_ne_zero _ hz)]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Set

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem selected_div_power {w : ι → E} {a m : ι → ℝ} {n : ι → ℕ}
    (ha : ∀ i,0<a i) {t : ℝ} (ht : 0<t) {D : ℝ} {h : E}
    (hn : ∀ i,(n i:ℝ)=D-inner ℝ (w i) h-m i) {p : E} (hp : Surrounds w p) (i : ι) :
    selected w (fun j => a j/t^(n j)) p i=
      selected w (fun j => a j*Real.exp (Real.log t*m j)) p i := by
  have he : (fun j => a j/t^(n j))=(fun j => Real.exp (-D*Real.log t)*
      (a j*Real.exp (Real.log t*m j))*Real.exp (inner ℝ (w j) (Real.log t • h))) := by
    funext j
    rw [inner_smul_right]
    have hpow : t^(n j)=Real.exp ((n j:ℝ)*Real.log t) := by
      rw [Real.exp_nat_mul,Real.exp_log ht]
    rw [hpow,div_eq_mul_inv,←Real.exp_neg]
    have he : a j*Real.exp (-((n j:ℝ)*Real.log t))=
        a j*Real.exp ((-D*Real.log t)+(Real.log t*m j)+Real.log t*inner ℝ (w j) h) := by
      rw [hn j]
      congr 2
      ring
    rw [he,Real.exp_add,Real.exp_add]
    ring
  rw [he]
  exact selected_gauge (fun j => mul_pos (ha j) (Real.exp_pos _)) (Real.exp_pos _) hp _ i

 theorem selected_marked_error {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A≤B) (hSB : S≤B) {a : TrapezoidWeight A B → ℝ} {n : TrapezoidWeight A B → ℕ}
    {M t D C : ℝ} (ha : ∀ k,0<a k) (hloga : ∀ k,|Real.log (a k)|≤M)
    (ht : 0<t) (ht1 : t<1)
    (hn : ∀ k,(n k:ℝ)=D-C*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
      markedHeight S (trapezoidWeight A B k)) {p : MomentPlane} (hp : p∈openTrapezoid A B) :
    |(∑ k,selected (trapezoidWeight A B) (fun j => a j/t^(n j)) p k*(n k:ℝ))-
      (D-C*(p 0+p 1)-markedHeight S p)|≤
      (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log t) := by
  have hs := trapezoidWeight_surrounds hAB hp
  have hg (k : TrapezoidWeight A B) :
      selected (trapezoidWeight A B) (fun j => a j/t^(n j)) p k=
      selected (trapezoidWeight A B)
        (fun j => a j*Real.exp (Real.log t*markedHeight S (trapezoidWeight A B j))) p k := by
    apply selected_div_power ha ht (D := D) (h := planeVector C C) _ hs
    intro j
    rw [hn j]
    congr 1
    simp [PiLp.inner_apply,Fin.sum_univ_succ,planeVector]
    ring
  let b := fun j => a j*Real.exp (Real.log t*markedHeight S (trapezoidWeight A B j))
  have hb (j : TrapezoidWeight A B) : 0<b j := mul_pos (ha j) (Real.exp_pos _)
  have hbound := marked_gibbs_error hA hS hAB hSB ha hloga (Real.log_neg ht ht1)
    (inverse (trapezoidWeight A B) b p)
    (show p∈closedTrapezoid A B from ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩)
    (inverse_spec hb hs)
  simp_rw [hg,hn]
  rw [probability_affine_height (selected_sum hb p) (selected_mean hb hs)]
  have he : D-C*(p 0+p 1)-(∑ i,selected (trapezoidWeight A B) b p i*
      markedHeight S (trapezoidWeight A B i))-(D-C*(p 0+p 1)-markedHeight S p)=
      -((∑ i,selected (trapezoidWeight A B) b p i*markedHeight S (trapezoidWeight A B i))-
      markedHeight S p) := by ring
  change |D-C*(p 0+p 1)-(∑ i,selected (trapezoidWeight A B) b p i*
      markedHeight S (trapezoidWeight A B i))-(D-C*(p 0+p 1)-markedHeight S p)|≤_
  rw [he,abs_neg]
  change |(∑ i,gibbs (trapezoidWeight A B) b (inverse (trapezoidWeight A B) b p) i*
      markedHeight S (trapezoidWeight A B i))-markedHeight S p|≤_
  rw [abs_of_nonneg hbound.1]
  exact hbound.2

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

 theorem totalWeight_le {A B : ℕ} (k : TrapezoidWeight A B) : totalWeight k≤B := k.property.2

 theorem cubicMarked_lt_degree {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k < cubicDegree D k := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

 theorem cubicMarked_twice_complement {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (k : TrapezoidWeight A B) : cubicMarkedOrder S k≤2*(cubicDegree D k-cubicMarkedOrder S k) := by
  have hk := totalWeight_le k
  dsimp [cubicMarkedOrder,cubicDegree]
  omega

 theorem totalWeight_cast {A B : ℕ} (k : TrapezoidWeight A B) :
    (totalWeight k:ℝ)=(trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1 := by
  simp [totalWeight,trapezoidWeight,planeVector]

 theorem cubicDegree_cast {A B D : ℕ} (hB : 3*B≤D) (k : TrapezoidWeight A B) :
    (cubicDegree D k:ℝ)=(D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1) := by
  rw [cubicDegree,Nat.cast_sub (by have hk := totalWeight_le k; omega),Nat.cast_mul,Nat.cast_ofNat,totalWeight_cast]

 theorem cubicMarkedOrder_cast {A B : ℕ} (S : ℕ) (k : TrapezoidWeight A B) :
    (cubicMarkedOrder S k:ℝ)=markedHeight S (trapezoidWeight A B k) := by
  unfold cubicMarkedOrder markedHeight
  by_cases hk : totalWeight k≤S
  · rw [Nat.cast_sub hk,totalWeight_cast]
    have hh : (totalWeight k:ℝ)≤S := by exact_mod_cast hk
    rw [totalWeight_cast] at hh
    rw [max_eq_left (by linarith)]
    ring
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hk),Nat.cast_zero,max_eq_right]
    have hh : (S:ℝ)≤totalWeight k := by exact_mod_cast (le_of_not_ge hk)
    rw [totalWeight_cast] at hh
    linarith

 theorem cubicEndOrder_cast {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (ε : EndIndex) (k : TrapezoidWeight A B) :
    (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)=
      if ε 0 then (if ε 1 then (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)
        else (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
          markedHeight S (trapezoidWeight A B k))
      else (if ε 1 then (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
          markedHeight S (trapezoidWeight A B k) else 0) := by
  cases h0 : ε 0 <;> cases h1 : ε 1 <;>
    simp only [weightedEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,Nat.cast_zero,
      Nat.cast_sub (cubicMarked_lt_degree hB hS k).le,cubicDegree_cast hB.le,cubicMarkedOrder_cast]

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialProbability
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realAnnulusChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.realTransverseChart_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseAnnulusInverse_val _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCoordinate_point _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseDiffeomorph_target _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalChart.realSliceChart_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_toCLM _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affinePhaseEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_empty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.fiberMix_univ _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.signFlip_projection _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.areaHamiltonianForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.complexSplitPhase_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinderAngular_cover _root_.OAI.PackingSufficiencySupport.Hamiltonian.diagonalScale_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.headComplexAmbient_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.horizontalOneForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.layerOrder_symm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.oneCovectorForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_neg_area _root_.OAI.PackingSufficiencySupport.Hamiltonian.planarHamiltonianField_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_comp _root_.OAI.PackingSufficiencySupport.Hamiltonian.planeRotate_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.productForm_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.radialArea_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.radiusSq_planeRotate _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_left _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspensionInverse_right _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricSuspension_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.twoCovectorForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
section
variable {ι : Type*} [Fintype ι]

theorem radialProbability_sum {k : ι → ℕ × ℕ} (h0 : ∃ i,k i=(0,0))
    (D m : ι → ℕ) (p : Radial.Plane) (x : BaseCurve) :
    ∑ i,radialProbability k D m p x i=1 :=
  Radial.selected_sum (fun j => coefficientNorm_pos (D j) (m j) x) h0 p

theorem radialProbability_mean {A B : ℕ} (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (x : BaseCurve) :
    ∑ i,radialProbability Radial.latticeIndex D m p x i • trapezoidWeight A B i=
      planeVector p.1 p.2 :=
  Radial.trapezoid_selected_mean hAB (fun j => coefficientNorm_pos (D j) (m j) x) hp

end

 theorem probability_affine_degree {ι : Type*} [Fintype ι] {w : ι → MomentPlane}
    {q : ι → ℝ} {p : MomentPlane} (hs : ∑ i,q i=1) (he : ∑ i,q i • w i=p) (D C : ℝ) :
    (∑ i,q i*(D-C*((w i) 0+(w i) 1)))=D-C*(p 0+p 1) := by
  have hcoord (j : Fin 2) : ∑ i,q i*(w i) j=p j := by
    simpa using congrArg (fun z : MomentPlane => z j) he
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp_rw [mul_left_comm (q _) C]
  rw [←Finset.mul_sum,←Finset.mul_sum,←Finset.sum_mul,hs,one_mul,hcoord 0,hcoord 1]

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped Topology
open Set Filter
open scoped BigOperators ContDiff
open Function

theorem lowerTrapezoid_interior_sequence {A B : ℝ} {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ q : ℕ → Plane,(∀ n,planeVector (q n).1 (q n).2∈openTrapezoid A B) ∧
      Tendsto q atTop (𝓝 p) := by
  let e : ℝ := min (A-p.1) (B-(p.1+p.2))/4
  have he : 0<e := div_pos (lt_min (sub_pos.mpr hp.2.1) (sub_pos.mpr hp.2.2.2)) (by norm_num)
  have he0 : e≤(A-p.1)/4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he1 : e≤(B-(p.1+p.2))/4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let d : ℕ → ℝ := fun n => e*(1/((n:ℝ)+1))
  have hd (n : ℕ) : 0<d n ∧ d n≤e := by
    have hn : (1:ℝ)≤(n:ℝ)+1 := by have hh : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
    refine ⟨mul_pos he (one_div_pos.mpr (by positivity)),?_⟩
    simpa [d] using mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hn) he.le
  refine ⟨fun n => (p.1+d n,p.2+d n),?_,?_⟩
  · intro n
    change 0<p.1+d n ∧ p.1+d n<A ∧ 0<p.2+d n ∧ (p.1+d n)+(p.2+d n)<B
    have hh := hd n
    exact ⟨by linarith [hp.1],by linarith,by linarith [hp.2.2.1],by linarith⟩
  · have ht : Tendsto d atTop (𝓝 0) := by
      simpa [d] using tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [add_zero,Prod.eta] using
      (tendsto_const_nhds.add ht).prodMk_nhds (tendsto_const_nhds.add ht)

theorem trapezoid_selected_tendsto {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) {q : ℕ → Plane}
    (hq : ∀ n,q n∈lowerTrapezoid A B) (ht : Tendsto q atTop (𝓝 p))
    (i : TrapezoidWeight A B) :
    Tendsto (fun n => selected latticeIndex a (q n) i) atTop (𝓝 (selected latticeIndex a p i)) := by
  have hf := (trapezoid_selected_contDiffWithinAt hA hAB ha hp i).continuousWithinAt
  have hm : Tendsto (fun n => (a,q n)) atTop
      (𝓝[{z : (TrapezoidWeight A B → ℝ) × Plane | (∀ j,0<z.1 j) ∧ z.2∈lowerTrapezoid A B}] (a,p)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds ht,Eventually.of_forall (fun n => ⟨ha,hq n⟩)⟩
  exact hf.tendsto.comp hm

theorem selected_marked_error_lower {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A≤B) (hSB : S≤B) {a : TrapezoidWeight A B → ℝ} {n : TrapezoidWeight A B → ℕ}
    {M t D C : ℝ} (ha : ∀ k,0<a k) (hloga : ∀ k,|Real.log (a k)|≤M)
    (ht : 0<t) (ht1 : t<1)
    (hn : ∀ k,(n k:ℝ)=D-C*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-
      markedHeight S (trapezoidWeight A B k)) {p : Plane} (hp : p∈lowerTrapezoid A B) :
    |(∑ k,selected latticeIndex (fun j => a j/t^(n j)) p k*(n k:ℝ))-
      (D-C*(p.1+p.2)-markedHeight S (planeVector p.1 p.2))|≤
      (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log t) := by
  let b : TrapezoidWeight A B → ℝ := fun j => a j/t^(n j)
  have hb (j : TrapezoidWeight A B) : 0<b j := div_pos (ha j) (pow_pos ht _)
  obtain ⟨q,hq,hqlim⟩ := lowerTrapezoid_interior_sequence hp
  have hqlo (j : ℕ) : q j∈lowerTrapezoid A B :=
    ⟨(hq j).1.le,(hq j).2.1,(hq j).2.2.1.le,(hq j).2.2.2⟩
  have hs (j : ℕ) :
      |(∑ k,selected latticeIndex b (q j) k*(n k:ℝ))-
        (D-C*((q j).1+(q j).2)-markedHeight S (planeVector (q j).1 (q j).2))|≤
        (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log t) := by
    have hw : Surrounds (weight latticeIndex) (planeVector (q j).1 (q j).2) :=
      trapezoidWeight_surrounds hAB (hq j)
    simp_rw [selected_eq_exponential hb (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hw]
    exact selected_marked_error hA hS hAB hSB ha hloga ht ht1 hn (hq j)
  have hsum : Tendsto (fun j => ∑ k,selected latticeIndex b (q j) k*(n k:ℝ)) atTop
      (𝓝 (∑ k,selected latticeIndex b p k*(n k:ℝ))) :=
    tendsto_finsetSum _ (fun i _ => (trapezoid_selected_tendsto hA hAB hb hp hqlo hqlim i).mul_const _)
  have hh : Continuous (fun z : Plane => D-C*(z.1+z.2)-markedHeight S (planeVector z.1 z.2)) := by
    simp only [markedHeight,planeVector]
    fun_prop
  exact le_of_tendsto ((hsum.sub (hh.continuousAt.tendsto.comp hqlim)).abs) (Eventually.of_forall hs)

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 theorem radialEndProbability_regularized {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    (p : Radial.Plane) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    radialEndProbability (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) p ε y=
      Radial.selected (Radial.latticeIndex (A := A) (B := B)) (fun k =>
        regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y/
          (radiusSq y)^(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε)) p := by
  unfold radialEndProbability radialProbability
  have he : (fun k : TrapezoidWeight A B => coefficientNorm (cubicDegree D k) (cubicMarkedOrder S k)
      (infinityDiffeomorph (parameters 0) ε y))=(fun k => regularCoefficientNorm (cubicDegree D k)
      (cubicMarkedOrder S k) ε y/(radiusSq y)^(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε)) := by
    funext k
    exact coefficientNorm_eq_regular_div (cubicMarked_lt_degree hB hS k).le
      (cubicMarked_twice_complement hB hS k) ε hy hR
  rw [he]

 theorem radialEndResidue_error_bp240_oai {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (ht : 0 < radiusSq y) (ht1 : radiusSq y<1) {M : ℝ} (hM : 0≤M)
    (hlog : ∀ k : TrapezoidWeight A B,|Real.log (regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y)|≤M)
    (c : ℝ) :
    |radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p ε y-
      c*limitingEndOrder D S (planeVector p.1 p.2) ε|≤
      |c| * ((2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y))) := by
  have hb : 0≤(2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)) :=
    div_nonneg (by positivity) (neg_pos.mpr (Real.log_neg ht ht1)).le
  have he : radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p ε y=
      c*(∑ k,radialEndProbability (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) p ε y k*
        (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)) := by
    simp only [radialEndResidue,weightedEndResidue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have hsum := radialProbability_sum (Radial.lattice_zero A B) (cubicDegree D) (cubicMarkedOrder S) p
    (infinityDiffeomorph (parameters 0) ε y)
  have hmean := radialProbability_mean hAB (cubicDegree D) (cubicMarkedOrder S) hp
    (infinityDiffeomorph (parameters 0) ε y)
  have hmarked (hn : ∀ k,(weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ)=
      (D:ℝ)-3*((trapezoidWeight A B k) 0+(trapezoidWeight A B k) 1)-markedHeight S (trapezoidWeight A B k)) :
      |(∑ k,radialEndProbability (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) p ε y k*
        (weightedEndOrder (cubicDegree D k) (cubicMarkedOrder S k) ε:ℝ))-
        ((D:ℝ)-3*(p.1+p.2)-markedHeight S (planeVector p.1 p.2))|≤
        (2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)) := by
    rw [radialEndProbability_regularized hB hS p ε hy hR]
    exact Radial.selected_marked_error_lower hA hS0 hAB hSB
      (fun k => regularCoefficientNorm_pos _ _ _ _) hlog ht ht1 hn hp
  cases h0 : ε 0 <;> cases h1 : ε 1
  · simp only [limitingEndOrder,h0,h1,Bool.false_eq_true,↓reduceIte,weightedEndOrder,Nat.cast_zero,mul_zero,Finset.sum_const_zero,sub_self,abs_zero]
    exact hb
  · simpa [limitingEndOrder,h0,h1,planeVector] using
      hmarked (fun k => by simpa only [h0,h1,Bool.false_eq_true,↓reduceIte] using cubicEndOrder_cast hB hS ε k)
  · simpa [limitingEndOrder,h0,h1,planeVector] using
      hmarked (fun k => by simpa only [h0,h1,Bool.false_eq_true,↓reduceIte] using cubicEndOrder_cast hB hS ε k)
  · have hdeg (k : TrapezoidWeight A B) := cubicEndOrder_cast hB hS ε k
    simp only [h0,h1,↓reduceIte] at hdeg
    simp only [hdeg,limitingEndOrder,h0,h1,↓reduceIte]
    rw [probability_affine_degree (by exact hsum) (by exact hmean),sub_self,abs_zero]
    exact hb

end PackingSufficiencySupport.CubicModel
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240_oai := @OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240_oai
