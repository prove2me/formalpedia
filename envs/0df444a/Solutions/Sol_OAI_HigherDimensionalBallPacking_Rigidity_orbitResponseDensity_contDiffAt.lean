-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:17:32.960328+00:00
-- url     : https://prove2.me/submissions/144dabcd-2f1f-4c16-9e38-bed8eb3621f0

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

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
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
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpace_3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpace_3
theorem profileWeightedDifference_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base) :
    ContDiff ℝ ∞ (profileWeightedDifference α hα₀ hα₁ base hb) :=
  contDiff_const.add ((scalarSectionCLM (E := E) (holderNearWeight (K := K))).contDiff.comp
    (holderDifference (K := K) (E := E) α).contDiff)

omit [CompleteSpace F] in
theorem profileCoefficient_contDiff (α : ℝ) (base : C(K,E)) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      (baseSegment base) (segmentSection (holderValue α u))) :=
  (compactSuperpose_contDiff (hf.fderiv_right (by simp)) (hc.fderiv ℝ)
    (baseSegment base)).comp (holderSegment_contDiff α)

omit [CompleteSpace F] in
theorem profileCoefficientOperator_contDiff (α : ℝ) (base : C(K,E)) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      (baseSegment base) (segmentSection (holderValue α u)))) := by
  simpa only [Function.comp_def, sectionOperatorCLM_apply] using
    (sectionOperatorCLM (K := OffDiagonal K × UnitTime) (E := E) (F := F)).contDiff.comp
      (profileCoefficient_contDiff α base f hf hc)

omit [CompleteSpace F] in
theorem profilePostNear_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α => sectionMeanCLM (sectionCLM (superposeBCF
      (compactCoefficient (fderiv ℝ f) (hf.continuous_fderiv (by simp)) (hc.fderiv ℝ))
      (baseSegment base) (segmentSection (holderValue α u)))
      (differencePull (profileWeightedDifference α hα₀ hα₁ base hb u)))) :=
  (sectionMeanCLM (P := OffDiagonal K) (F := F)).contDiff.comp
    ((profileCoefficientOperator_contDiff α base f hf hc).clm_apply
      ((differencePull (K := K) (E := E)).contDiff.comp
        (profileWeightedDifference_contDiff α hα₀ hα₁ base hb)))

omit [CompleteSpace F] in
theorem profileValue_contDiff (α : ℝ) (base : C(K,E)) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α =>
      superposeBCF (compactCoefficient f hf.continuous hc) base (holderValue α u)) :=
  (compactSuperpose_contDiff hf hc base).comp (holderValue (K := K) (E := E) α).contDiff

omit [CompleteSpace F] in
theorem profilePostDifference_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (profilePostDifference α hα₀ hα₁ base hb f hf hc) :=
  (profilePostNear_contDiff α hα₀ hα₁ base hb f hf hc).add
    ((scalarSectionCLM (E := F) (holderFarWeight α hα₀ hα₁ (K := K))).contDiff.comp
      (((pairLeft (K := K) F).contDiff.comp (profileValue_contDiff α base f hf hc)).sub
        ((pairRight (K := K) F).contDiff.comp (profileValue_contDiff α base f hf hc))))

theorem holderProfilePost_ambient_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun u : HolderSpace K E α =>
      (holderProfilePost α hα₀ hα₁ base hb f hf hc u).val) :=
  (profileValue_contDiff α base f hf hc).prodMk
    (profilePostDifference_contDiff α hα₀ hα₁ base hb f hf hc)

theorem holderProfilePost_hasFDerivAt (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (u : HolderSpace K E α) :
    HasFDerivAt (holderProfilePost α hα₀ hα₁ base hb f hf hc)
      (holderCLM α (holderProfilePost α hα₀ hα₁ base hb (fderiv ℝ f)
        (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u)) u := by
  apply holder_hasFDerivAt_of_ambient
  · exact ((holderProfilePost_ambient_contDiff α hα₀ hα₁ base hb f hf hc).differentiable (by simp)) u
  · have hdf := hf.fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
    have hd := (superposeBCF_hasFDerivAt
      (compactCoefficient f hf.continuous hc)
      (compactCoefficient (fderiv ℝ f) hdf.continuous (hc.fderiv ℝ))
      (fun x => (hf.differentiable (by simp) x).hasFDerivAt)
      (hdf.continuous.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty)
      base (holderValue α u)).comp u (holderValue α).hasFDerivAt
    convert hd using 1 <;> try rfl

theorem holderProfilePost_contDiff_nat (m : ℕ) (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ m (holderProfilePost α hα₀ hα₁ base hb f hf hc) := by
  induction m generalizing F with
  | zero =>
    apply contDiff_zero.mpr
    exact continuous_induced_rng.mpr
      (holderProfilePost_ambient_contDiff α hα₀ hα₁ base hb f hf hc).continuous
  | succ m ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun u => holderCLM α (holderProfilePost α hα₀ hα₁ base hb (fderiv ℝ f)
      (hf.fderiv_right (by simp)) (hc.fderiv ℝ) u),?_,
        holderProfilePost_hasFDerivAt α hα₀ hα₁ base hb f hf hc⟩
    exact (holderOperatorCLM (K := K) (E := E) (F := F) α).contDiff.comp
      (ih (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ))

 

theorem holderProfilePost_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (base : C(K,E)) {L : NNReal} (hb : LipschitzWith L base)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (holderProfilePost α hα₀ hα₁ base hb f hf hc) :=
  contDiff_infty.mpr (fun m => holderProfilePost_contDiff_nat m α hα₀ hα₁ base hb f hf hc)

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

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem affineProfile_lower_bound (c d v : E) (A B : ℂ →L[ℝ] E) (m U R t : ℝ)
    (_hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖A z‖) (hd : ‖d‖≤1) (hB : ‖B‖≤ m/2)
    (hv : ‖v‖≤U) (ht : t∈Icc (0:ℝ) 1) (z : ℂ)
    (hz : R+‖c‖+1+U ≤ m/2*‖z‖) :
    R ≤ ‖c+A z+t • (d+B z)+v‖ := by
  have hb : ‖t • (d+B z)‖ ≤ 1+(m/2)*‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    calc
      t*‖d+B z‖ ≤ ‖d+B z‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
      _ ≤ ‖d‖+‖B z‖ := norm_add_le _ _
      _ ≤ 1+‖B‖*‖z‖ := add_le_add hd (B.le_opNorm z)
      _ ≤ 1+(m/2)*‖z‖ := add_le_add (le_refl 1) (mul_le_mul_of_nonneg_right hB (norm_nonneg z))
  have hrev : ‖A z‖ ≤ ‖c+A z+t • (d+B z)+v‖+‖c‖+1+(m/2)*‖z‖+U := by
    calc
      ‖A z‖ = ‖(c+A z+t • (d+B z)+v)-(c+t • (d+B z)+v)‖ := by congr 1; abel
      _ ≤ ‖c+A z+t • (d+B z)+v‖+‖c+t • (d+B z)+v‖ := norm_sub_le _ _
      _ ≤ ‖c+A z+t • (d+B z)+v‖+((‖c‖+‖t • (d+B z)‖)+‖v‖) :=
        add_le_add (le_refl _) ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)))
      _ ≤ ‖c+A z+t • (d+B z)+v‖+‖c‖+1+(m/2)*‖z‖+U := by linarith
  have ha := hA z
  linarith

 

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem compactCoefficient_zero_outside {f : E → F} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0<R ∧ ∀ x, R≤‖x‖ → f x=0 := by
  obtain ⟨R,hR,hs⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0:E)
  refine ⟨R,hR,fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  simp only [Metric.mem_ball,dist_zero_right] at hh
  exact (not_lt_of_ge hx) hh

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyDomainNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyDomainNormedSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyCodomainNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.affineFamilyCodomainNormedSpace
omit [CompleteSpace E] in
theorem localizedAffineFamily_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (localizedAffineFamily α hα₀ hα₁ f hf hc c A b) := by
  apply (holderProfilePost_contDiff α hα₀ hα₁ (realAffineProfile c A)
    (realAffineProfile_lipschitz c A) f hf hc).comp
  exact ((holderCutoffAffine_contDiff α hα₀ hα₁ b).comp
    (((contDiff_fst.fst).sub contDiff_const).prodMk ((contDiff_fst.snd).sub contDiff_const))).add contDiff_snd

omit [CompleteSpace E] in
theorem localizedAffineFamily_eq (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ)) (m U R : ℝ)
    (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖A z‖) (hfR : ∀ x, R≤‖x‖ → f x=0)
    (hT : R+‖c‖+1+U ≤ m/2*b.rIn)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α)
    (hd : ‖p.1.1-c‖≤1) (hB : ‖p.1.2-A‖≤ m/2) (hu : ‖p.2‖≤U) :
    localizedAffineFamily α hα₀ hα₁ f hf hc c A b p = holderAffineFamily α hα₀ hα₁ f hf hc p := by
  apply holderValue_injective α
  ext z
  rw [localizedAffineFamily_apply,holderAffineFamily_apply]
  by_cases hz : ‖z‖≤b.rIn
  · have hb : b z=1 := b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    rw [hb,one_smul]
    congr 1
    simp only [sub_apply]
    abel
  · have hz' : R+‖c‖+1+U ≤ m/2*‖z‖ := hT.trans
      (mul_le_mul_of_nonneg_left (le_of_not_ge hz) (half_pos hm).le)
    have hv : ‖holderValue α p.2 z‖≤U :=
      ((holderValue α p.2).norm_coe_le_norm z).trans ((holderValue_norm α p.2).trans hu)
    have ht : b z∈Icc (0:ℝ) 1 := ⟨b.nonneg,b.le_one⟩
    rw [hfR _ (affineProfile_lower_bound c (p.1.1-c) (holderValue α p.2 z)
      A (p.1.2-A) m U R (b z) hm hA hd hB hv ht z hz')]
    symm
    apply hfR
    convert affineProfile_lower_bound c (p.1.1-c) (holderValue α p.2 z)
      A (p.1.2-A) m U R 1 hm hA hd hB hv (by constructor <;> norm_num) z hz' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    simp only [one_smul,sub_apply]
    abel

 

omit [CompleteSpace E] in
theorem holderAffineFamily_contDiffAt (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α)
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖p.1.2 z‖) :
    ContDiffAt ℝ ∞ (holderAffineFamily α hα₀ hα₁ f hf hc) p := by
  obtain ⟨R,hR,hfR⟩ := compactCoefficient_zero_outside hc
  let U : ℝ := ‖p.2‖+1
  let T : ℝ := (R+‖p.1.1‖+1+U)/(m/2)
  have hTpos : 0<T := div_pos (by dsimp [U]; positivity) (half_pos hm)
  let b : ContDiffBump (0:ℂ) := ⟨T,T+1,hTpos,lt_add_one T⟩
  have hT : R+‖p.1.1‖+1+U ≤ m/2*b.rIn := by
    dsimp [b,T]
    rw [mul_comm,div_mul_cancel₀ _ (half_pos hm).ne']
  let P := (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α
  have hdc : ∀ᶠ q : P in 𝓝 p, ‖q.1.1-p.1.1‖<1 := by
    have h := (show Continuous (fun q : P => q.1.1) from continuous_fst.fst).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds p.1.1 (by norm_num : (0:ℝ)<1))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hdA : ∀ᶠ q : P in 𝓝 p, ‖q.1.2-p.1.2‖< m/2 := by
    have h := (show Continuous (fun q : P => q.1.2) from continuous_fst.snd).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds p.1.2 (half_pos hm))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hdu : ∀ᶠ q : P in 𝓝 p, ‖q.2-p.2‖<1 := by
    have h := (show Continuous (fun q : P => q.2) from continuous_snd).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds p.2 (by norm_num : (0:ℝ)<1))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  apply (localizedAffineFamily_contDiff α hα₀ hα₁ f hf hc p.1.1 p.1.2 b).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hdc,hdA,hdu] with q hqc hqA hqu
  have hqu' : ‖q.2‖≤U := by
    calc
      ‖q.2‖ ≤ ‖q.2-p.2‖+‖p.2‖ := norm_le_norm_sub_add q.2 p.2
      _ ≤ 1+‖p.2‖ := add_le_add (le_of_lt hqu) (le_refl _)
      _ = U := add_comm _ _
  exact (localizedAffineFamily_eq α hα₀ hα₁ f hf hc p.1.1 p.1.2 b m U R hm hA hfR hT q
    hqc.le hqA.le hqu').symm

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

 theorem frozenResponse_comp_contDiffAt
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (b : ContDiffBump (0:ℂ))
    (H : D → HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (a : E) (p : D)
    (hH : ContDiffAt ℝ ∞ H p) (hi : (cutoffFrozen b (H p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => frozenResponse b (H x,a)) p := by
  have hp : ContDiffAt ℝ ∞ (fun x => (H x,a)) p := hH.prodMk contDiffAt_const
  exact (frozenResponse_contDiffAt b (H p,a) hi).comp p hp

end HigherDimensionalBallPacking.Rigidity





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHSpace
theorem orbitCoefficient_contDiff {n : ℕ} (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c a : Phase n) (ha : a≠0) : ContDiff ℝ ∞ (orbitCoefficient f hf hc c a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hA (z : ℂ) : ‖a‖*‖z‖≤‖affineSlope a z‖ := by
    rw [affineSlope_apply,norm_smul,mul_comm]
  have hh := holderAffineFamily_contDiffAt ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc
    ((c+p.1 • a,affineSlope a),p.2) ‖a‖ (norm_pos_iff.mpr ha) hA
  have hp : ContDiff ℝ ∞ (fun p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3) =>
      ((c+p.1 • a,affineSlope a),p.2)) :=
    ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_const).prodMk contDiff_snd
  exact hh.comp p hp.contDiffAt

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal2
local instance AffineC1RegularityLocal3_rc7b22d_1 (n : ℕ) : NormedAddCommGroup (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal4_rc7b22d_1 (n : ℕ) : NormedSpace ℝ (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal8
theorem orbitResponseDensity_contDiffAt_oai {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n) (ha : a≠0)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3))
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3) =>
      frozenResponse b (orbitCoefficient f hf hc c a p,a)) p := by
  exact frozenResponse_comp_contDiffAt b _ a p
    (orbitCoefficient_contDiff f hf hc c a ha).contDiffAt hi

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt_oai := @OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt_oai
