-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:19:46.187484+00:00
-- url     : https://prove2.me/submissions/cd35102a-6d5a-4479-b8f3-2430a1dc04e9

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
import Definitions.Def_OAIQ10Bp008

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} {E F : Type v} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem superposeBCF_uniformContinuous (f : E →ᵇ F)
    (hf : UniformContinuous (f : E → F)) (base : C(K,E)) :
    UniformContinuous (superposeBCF f base) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by positivity)
  refine ⟨δ,hδ,fun v w hvw => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (by positivity : 0≤ε/2)).mpr
  intro z
  change ‖f (base z+v z)-f (base z+w z)‖≤ε/2
  have hh : dist (base z+v z) (base z+w z)<δ := by
    rw [dist_add_left, dist_eq_norm]
    exact ((v-w).norm_coe_le_norm z).trans_lt (by simpa only [dist_eq_norm] using hvw)
  simpa only [dist_eq_norm] using (hfδ hh).le

 

theorem superposeBCF_hasFDerivAt (f : E →ᵇ F) (g : E →ᵇ (E →L[ℝ] F))
    (hfg : ∀ x, HasFDerivAt (f : E → F) (g x) x)
    (hg : UniformContinuous (g : E → E →L[ℝ] F)) (base : C(K,E)) (v : K →ᵇ E) :
    HasFDerivAt (superposeBCF f base) (sectionCLM (superposeBCF g base v)) v := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hgδ⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : K →ᵇ E) hδ] with h hh
  have hhn : ‖h‖<δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro z
  change ‖f (base z+(v z+h z))-f (base z+v z)-g (base z+v z) (h z)‖≤ε*‖h‖
  have hbound : ∀ x ∈ Metric.ball (base z+v z) δ, ‖g x-g (base z+v z)‖≤ε := by
    intro x hx
    simpa only [dist_eq_norm] using (hgδ hx).le
  have hy : base z+(v z+h z)∈Metric.ball (base z+v z) δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,
      show base z+(v z+h z)-(base z+v z)=h z by abel] using
      (h.norm_coe_le_norm z).trans_lt hhn
  have hb := (convex_ball (base z+v z) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x _ => (hfg x).hasFDerivWithinAt) hbound
    (Metric.mem_ball_self hδ) hy
  have hc : ‖f (base z+(v z+h z))-f (base z+v z)-g (base z+v z) (h z)‖≤ε*‖h z‖ := by
    simpa only [show base z+(v z+h z)-(base z+v z)=h z by abel] using hb
  exact hc.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm z) hε.le)


theorem compactSuperpose_contDiff_nat (m : ℕ) {f : E → F}
    (hf : ContDiff ℝ m f) (hc : HasCompactSupport f) (base : C(K,E)) :
    ContDiff ℝ m (superposeBCF (compactCoefficient f hf.continuous hc) base) := by
  induction m generalizing F with
  | zero =>
    exact contDiff_zero.mpr
      (superposeBCF_uniformContinuous _
        (hf.continuous.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty) base).continuous
  | succ m ih =>
    have hdf : ContDiff ℝ m (fderiv ℝ f) := hf.fderiv_right (by simp)
    let g : E →ᵇ (E →L[ℝ] F) :=
      compactCoefficient (fderiv ℝ f) hdf.continuous (hc.fderiv ℝ)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun v => sectionOperatorCLM (superposeBCF g base v),?_,?_⟩
    · have hi : ContDiff ℝ m (superposeBCF g base) := ih hdf (hc.fderiv ℝ)
      exact sectionOperatorCLM.contDiff.comp hi
    · intro v
      apply superposeBCF_hasFDerivAt
      · intro x
        exact (hf.differentiable (by simp) x).hasFDerivAt
      · exact hdf.continuous.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty

theorem compactSuperpose_contDiff {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (base : C(K,E)) :
    ContDiff ℝ ∞ (superposeBCF (compactCoefficient f hf.continuous hc) base) := by
  apply contDiff_infty.mpr
  intro m
  exact compactSuperpose_contDiff_nat m (contDiff_infty.mp hf m) hc base



end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal

open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.holderCalculusNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.holderCalculusNormedSpace
theorem holderSegment_contDiff (α : ℝ) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => segmentSection (holderValue α u)) :=
  (segmentSection (K := K) (E := E)).contDiff.comp (holderValue (K := K) (E := E) α).contDiff

omit [CompleteSpace F] in
theorem holderCoefficient_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (fun u : HolderSpace K E α => superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u))) := by
  exact (compactSuperpose_contDiff (hf.fderiv_right (by simp)) (hc.fderiv ℝ)
    (0 : C(OffDiagonal K × UnitTime,E))).comp (holderSegment_contDiff α)

omit [CompleteSpace F] in
theorem holderCoefficientOperator_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u)))) :=
  (sectionOperatorCLM (K := OffDiagonal K × UnitTime) (E := E) (F := F)).contDiff.comp
    (holderCoefficient_contDiff α f hf hc)

omit [CompleteSpace F] in
theorem holderPostIntegrand_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      0 (segmentSection (holderValue α u))) (differencePull (holderDifference α u))) :=
  (holderCoefficientOperator_contDiff α f hf hc).clm_apply
    ((differencePull (K := K) (E := E)).contDiff.comp (holderDifference (K := K) (E := E) α).contDiff)

omit [CompleteSpace F] in
theorem holderPostDifference_contDiff (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (holderPostDifference α f hf hc (K := K)) :=
  (sectionMeanCLM (P := OffDiagonal K) (F := F)).contDiff.comp
    (holderPostIntegrand_contDiff α f hf hc)

omit [CompleteSpace F] in
theorem holderPostDifference_integral (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) (p : OffDiagonal K) :
    holderPostDifference α f hf hc u p = ∫ t in (0:ℝ)..1,
      fderiv ℝ f (holderValue α u p.val.2 + t •
        (holderValue α u p.val.1 - holderValue α u p.val.2)) (holderDifference α u p) := by
  change (∫ t in (0:ℝ)..1, fderiv ℝ f (0+segmentSection (holderValue α u)
    (p,Set.projIcc 0 1 (by norm_num) t)) (holderDifference α u p)) = _
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
  simp only [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht',segmentSection_apply,zero_add]

 

theorem holderPostDifference_relation (α : ℝ) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) (p : OffDiagonal K) :
    (dist p.val.1 p.val.2)^α • holderPostDifference α f hf hc u p =
      f (holderValue α u p.val.1)-f (holderValue α u p.val.2) := by
  let a := holderValue α u p.val.2
  let d := holderValue α u p.val.1-holderValue α u p.val.2
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (a+t • d)) (fderiv ℝ f (a+t • d) d) t := by
    intro t
    exact ((hf.differentiable (by simp)) (a+t • d)).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [one_smul, id_eq] using (((hasDerivAt_id t).smul_const d).const_add a))
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (a+t • d) d) MeasureTheory.volume 0 1 :=
    (((hf.continuous_fderiv (by simp)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hint
  simp only [one_smul,zero_smul,add_zero] at hi
  rw [holderPostDifference_integral,← intervalIntegral.integral_smul]
  calc
    _ = ∫ t in (0:ℝ)..1, fderiv ℝ f (a+t • d) d := by
      apply intervalIntegral.integral_congr
      intro t _
      change (dist p.val.1 p.val.2)^α • (fderiv ℝ f (a+t • d)) (holderDifference α u p) = _
      rw [← map_smul]
      congr 1
      exact (u.property p).symm
    _ = f (holderValue α u p.val.1)-f (holderValue α u p.val.2) := by
      simpa only [a,d,add_sub_cancel] using hi

theorem holderPost_coe (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) :
    (holderPost α hα f hf hc u).val =
      (superposeBCF (compactCoefficient f hf.continuous hc) 0 (holderValue α u),
       holderPostDifference α f hf hc u) := by
  apply Prod.ext
  · rfl
  · ext p
    have hw : (dist p.val.1 p.val.2)^α ≠ 0 :=
      (Real.rpow_pos_of_pos (dist_pos.mpr p.property) α).ne'
    apply smul_right_injective F hw
    change (dist p.val.1 p.val.2)^α • (holderPost α hα f hf hc u).val.2 p =
      (dist p.val.1 p.val.2)^α • holderPostDifference α f hf hc u p
    rw [← (holderPost α hα f hf hc u).property p,holderPostDifference_relation]
    simp only [← holderValue_apply,holderPost_apply]

theorem holderPost_ambient_contDiff (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => (holderPost α hα f hf hc u).val) := by
  have he : (fun u : HolderSpace K E α => (holderPost α hα f hf hc u).val) =
      (fun u : HolderSpace K E α => (superposeBCF (compactCoefficient f hf.continuous hc) 0
        (holderValue α u),holderPostDifference α f hf hc u)) := funext (holderPost_coe α hα f hf hc)
  rw [he]
  apply ContDiff.prodMk
  · exact (compactSuperpose_contDiff hf hc (0 : C(K,E))).comp (holderValue (K := K) (E := E) α).contDiff
  · exact holderPostDifference_contDiff α f hf hc

 

omit [CompleteSpace F] in
theorem holder_hasFDerivAt_of_ambient
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (α : ℝ) (g : P → HolderSpace K F α) (g' : P →L[ℝ] HolderSpace K F α) (x : P)
    (hg : DifferentiableAt ℝ (fun y => (g y).val) x)
    (hv : HasFDerivAt (fun y => holderValue α (g y)) ((holderValue α).comp g') x) :
    HasFDerivAt g g' x := by
  let L := fderiv ℝ (fun y => (g y).val) x
  have hL : HasFDerivAt (fun y => (g y).val) L x := hg.hasFDerivAt
  have hmem : ∀ v, L v ∈ holderGraph K F α := by
    intro v p
    let C : ((K →ᵇ F) × (OffDiagonal K →ᵇ F)) →L[ℝ] F :=
      (BoundedContinuousFunction.evalCLM ℝ p.val.1).comp (ContinuousLinearMap.fst ℝ _ _) -
      (BoundedContinuousFunction.evalCLM ℝ p.val.2).comp (ContinuousLinearMap.fst ℝ _ _) -
      (dist p.val.1 p.val.2)^α •
        (BoundedContinuousFunction.evalCLM ℝ p).comp (ContinuousLinearMap.snd ℝ _ _)
    have hc : (fun y => C (g y).val) = fun _ : P => (0 : F) := by
      funext y
      change (g y).val.1 p.val.1-(g y).val.1 p.val.2 -
        (dist p.val.1 p.val.2)^α • (g y).val.2 p = 0
      exact sub_eq_zero.mpr ((g y).property p)
    have hd : HasFDerivAt (fun y => C (g y).val) (C.comp L) x :=
      C.hasFDerivAt.comp x hL
    rw [hc] at hd
    have he := congrArg (fun A : P →L[ℝ] F => A v) (hd.unique (hasFDerivAt_const (0:F) x))
    change (L v).1 p.val.1 - (L v).1 p.val.2 - (dist p.val.1 p.val.2)^α • (L v).2 p = 0 at he
    exact sub_eq_zero.mp he
  have hfst : (ContinuousLinearMap.fst ℝ (K →ᵇ F) (OffDiagonal K →ᵇ F)).comp L =
      (holderValue α).comp g' :=
    (((ContinuousLinearMap.fst ℝ (K →ᵇ F) (OffDiagonal K →ᵇ F)).hasFDerivAt).comp x hL).unique hv
  have heq : L = (holderGraph K F α).subtypeL.comp g' := by
    apply ContinuousLinearMap.ext
    intro v
    have he : holderValue α (⟨L v,hmem v⟩ : HolderSpace K F α) = holderValue α (g' v) :=
      congrArg (fun A : P →L[ℝ] (K →ᵇ F) => A v) hfst
    exact congrArg Subtype.val (holderValue_injective α he)
  rw [heq] at hL
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hL ⊢
  rw [← Asymptotics.isLittleO_norm_left]
  rw [← Asymptotics.isLittleO_norm_left] at hL
  exact hL

theorem holderPost_hasFDerivAt (α : ℝ) (hα : 0<α) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : HolderSpace K E α) :
    HasFDerivAt (holderPost α hα f hf hc)
      (holderCLM α (holderPost α hα (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u)) u := by
  apply holder_hasFDerivAt_of_ambient
  · exact ((holderPost_ambient_contDiff α hα f hf hc).differentiable (by simp)) u
  · have hdf := hf.fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
    have hd := (superposeBCF_hasFDerivAt
      (compactCoefficient f hf.continuous hc)
      (compactCoefficient (fderiv ℝ f) hdf.continuous (hc.fderiv ℝ))
      (fun x => (hf.differentiable (by simp) x).hasFDerivAt)
      (hdf.continuous.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty)
      (0 : C(K,E)) (holderValue α u)).comp u (holderValue α).hasFDerivAt
    convert hd using 1 <;> try rfl

 

theorem holderPost_contDiff_nat (m : ℕ) (α : ℝ) (hα : 0<α) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ m (holderPost α hα f hf hc (K := K)) := by
  induction m generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_induced_rng.mpr (holderPost_ambient_contDiff α hα f hf hc).continuous
  | succ m ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => holderCLM α (holderPost α hα (fderiv ℝ f)
      (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u),?_,holderPost_hasFDerivAt α hα f hf hc⟩
    exact (holderOperatorCLM (K := K) (E := E) (F := F) α).contDiff.comp
      (ih (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ))

theorem holderPost_contDiff (α : ℝ) (hα : 0<α) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (holderPost α hα f hf hc (K := K)) :=
  contDiff_infty.mpr (fun m => holderPost_contDiff_nat m α hα f hf hc)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.cutoffHolderNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.cutoffHolderNormedSpace
theorem holderCutoffAffine_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (b : ContDiffBump (0:ℂ)) : ContDiff ℝ ∞ (holderCutoffAffine (E := E) α hα₀ hα₁ b) := by
  have hconst : ContDiff ℝ ∞ (fun p : E × (ℂ →L[ℝ] E) => holderConst (K := ℂ) α p.1) :=
    (holderConstCLM (K := ℂ) (E := E) α).contDiff.comp contDiff_fst
  have hlin : ContDiff ℝ ∞ (fun p : E × (ℂ →L[ℝ] E) =>
      holderLinearPost α p.2 (holderSourceCutoffLinear α hα₀ hα₁ b)) := by
    exact ((holderOperatorCLM (K := ℂ) (E := ℂ) (F := E) α).contDiff.comp
      ((holderConstCLM (K := ℂ) (E := ℂ →L[ℝ] E) α).contDiff.comp contDiff_snd)).clm_apply contDiff_const
  let M : HolderSpace ℂ (E →L[ℝ] E) α := holderLinearPost α
    (ContinuousLinearMap.lsmul ℝ ℝ) (holderSourceCutoff α hα₀ hα₁ b)
  have hmul := (holderCLM (K := ℂ) (E := E) (F := E) α M).contDiff.comp hconst
  exact hmul.add hlin

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseHolderGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseHolderSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseCompactSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenResponseLocal4
theorem cutoffFrozen_contDiff (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (cutoffFrozen (E := E) b) := by
  let D : CompactHolderSpace E b.rOut →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
    (holderJetEval ((1:ℝ)/3) 1).comp ((c1HolderDeriv ((1:ℝ)/3)).comp (compactCRInverse b.rOut))
  have hL : ContDiff ℝ ∞ (holderOperatorCLM (K := ℂ) (E := E) (F := E) ((1:ℝ)/3)) :=
    ContinuousLinearMap.contDiff _
  have hh : ContDiff ℝ ∞ (fun H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) => (holderCLM ((1:ℝ)/3) H).comp D) :=
    hL.clm_comp contDiff_const
  exact contDiff_const.sub ((contDiff_const (c := cutoffCompact (E := E) b)).clm_comp hh)

 theorem frozenResponse_contDiffAt (b : ContDiffBump (0:ℂ))
    (p : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) × E) (hi : (cutoffFrozen b p.1).IsInvertible) :
    ContDiffAt ℝ ∞ (frozenResponse b) p := by
  have hL : ContDiff ℝ ∞ (holderOperatorCLM (K := ℂ) (E := E) (F := E) ((1:ℝ)/3)) :=
    ContinuousLinearMap.contDiff _
  have hC : ContDiff ℝ ∞ (holderConstantCLM (E := E) ((1:ℝ)/3)) :=
    ContinuousLinearMap.contDiff _
  have hr : ContDiff ℝ ∞ (fun p : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) × E =>
      cutoffCompact b (holderCLM ((1:ℝ)/3) p.1 (holderConstantCLM ((1:ℝ)/3) p.2))) :=
    (cutoffCompact (E := E) b).contDiff.comp
      ((hL.comp contDiff_fst).clm_apply
        (hC.comp contDiff_snd))
  exact (hi.contDiffAt_map_inverse.comp p ((cutoffFrozen_contDiff (E := E) b).comp contDiff_fst).contDiffAt).clm_apply hr.contDiffAt

end HigherDimensionalBallPacking.Rigidity





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapHSpace
theorem responseProfile_contDiff {n : ℕ} (B : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (responseProfile (n := n) B) := by
  have hc := (holderConstantCLM (E := ℝ × Phase n) ((1:ℝ)/3)).contDiff.comp
    ((contDiff_fst.fst : ContDiff ℝ ∞ (fun x : ResponseCoords n => x.1.1)).prodMk (contDiff_const (c := (0:Phase n))))
  have ha : ContDiff ℝ ∞ (fun x : ResponseCoords n => affineSlope x.1.2.2) :=
    ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] Phase n →L[ℝ] Phase n).flip).contDiff.comp contDiff_fst.snd.snd
  have ht := (holderCutoffAffine_contDiff ((1:ℝ)/3) (by norm_num) (by norm_num) B).comp
    ((contDiff_fst.snd.fst : ContDiff ℝ ∞ (fun x : ResponseCoords n => x.1.2.1)).prodMk ha)
  let L : HolderSpace ℂ (Phase n) ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ (ℝ × Phase n) ((1:ℝ)/3) :=
    holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.inr ℝ ℝ (Phase n))
  exact hc.add (L.contDiff.comp (ht.add contDiff_snd))

 theorem responseCoefficient_contDiff {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) :
    ContDiff ℝ ∞ (responseCoefficient b B A hA hc) := by
  exact ((compactHolderSubmodule (E := End n) b.rOut).subtypeL.comp (cutoffCompact b)).contDiff.comp
    ((holderPost_contDiff ((1:ℝ)/3) (by norm_num) A hA hc).comp (responseProfile_contDiff B))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactSpace
theorem responseFactor_contDiffAt_oai {n : ℕ} (b B : ContDiffBump (0:ℂ))
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (x : ResponseCoords n) (hi : (cutoffFrozen b (responseCoefficient b B A hA hc x)).IsInvertible) :
    ContDiffAt ℝ ∞ (responseFactor b B A hA hc) x := by
  have hp : ContDiffAt ℝ ∞ (fun y : ResponseCoords n => (responseCoefficient b B A hA hc y,y.1.2.2)) x :=
    (responseCoefficient_contDiff b B A hA hc).contDiffAt.prodMk contDiffAt_fst.snd.snd
  exact (frozenResponse_contDiffAt (E := Phase n) b (responseCoefficient b B A hA hc x,x.1.2.2) hi).comp x hp

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt_oai := @OAI.HigherDimensionalBallPacking.Rigidity.responseFactor_contDiffAt_oai
