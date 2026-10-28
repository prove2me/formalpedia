-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.framed_unmarked_surjective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:55:21.563411+00:00
-- url     : https://prove2.me/submissions/08005740-577c-4faa-bca6-08de02adb5f1

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_decaying_CR_zero

section
-- module Solutions.OAIQ10_BP.BallPacking_Fredholm_FiniteExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem compactPerturbation_filtration_stops (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (V : ℕ → Submodule ℝ E) (hmono : Monotone V)
    (hclosed : ∀ n, IsClosed (V n : Set E))
    (hstep : ∀ n x, x∈V (n+1) → x+T x∈V n) :
    ∃ n, V n=V (n+1) := by
  by_contra! hne
  have hx (n : ℕ) : ∃ x∈V (n+1), ‖x‖≤3 ∧ ∀ y∈V n, 1≤‖x-y‖ := by
    have hn : ¬ V (n+1) ≤ V n := fun h => hne n (le_antisymm (hmono (Nat.le_succ n)) h)
    obtain ⟨x,hxs,hxn⟩ := Set.not_subset.mp hn
    have hc : IsClosed ((V n).comap (V (n+1)).subtype : Set (V (n+1))) :=
      (hclosed n).preimage continuous_subtype_val
    have hh : ∃ x : V (n+1), x∉(V n).comap (V (n+1)).subtype := ⟨⟨x,hxs⟩,hxn⟩
    obtain ⟨⟨x,hx⟩,hxn,hxy⟩ := riesz_lemma_of_norm_lt
      (c := (2:ℝ)) (by norm_num) (R := 3) (by norm_num) hc hh
    refine ⟨x,hx,hxn,fun y hy => ?_⟩
    exact hxy ⟨y,hmono (Nat.le_succ n) hy⟩ hy
  choose x hxv hxn hxy using hx
  have hTx {n m : ℕ} (hnm : n+1 ≤ m) : T (x n)∈V m := by
    have hs : x n+T (x n) ∈ V m := hmono (by omega) (hstep n (x n) (hxv n))
    have hz : x n∈V m := hmono hnm (hxv n)
    simpa only [add_sub_cancel_left] using (V m).sub_mem hs hz
  have hp : Pairwise (fun m n : ℕ => 1≤‖T (x m)-T (x n)‖) := by
    have : Std.Symm (fun m n : ℕ => 1≤‖T (x m)-T (x n)‖) :=
      ⟨fun _ _ h => by rwa [norm_sub_rev]⟩
    apply Pairwise.of_lt
    intro m n hmn
    let y := x n+T (x n)-T (x m)
    have hy : y∈V n := (V n).sub_mem (hstep n (x n) (hxv n)) (hTx (by omega))
    have he : x n-y=T (x m)-T (x n) := by dsimp [y]; abel
    simpa only [he] using hxy n y hy
  obtain ⟨K,hK,hTK⟩ := hT.image_closedBall_subset_compact 3
  obtain ⟨y,_,φ,hφ,hφy⟩ := hK.tendsto_subseq (fun n => hTK ⟨x n,by simpa using hxn n,rfl⟩)
  have hh := hφy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hh
  obtain ⟨N,hN⟩ := hh 1 (by norm_num)
  have hlt : ‖T (x (φ (N+1)))-T (x (φ N))‖<1 := by
    simpa only [Function.comp_apply,dist_eq_norm_sub,ContinuousLinearMap.coe_coe] using hN (N+1) (by omega)
  exact hlt.not_ge (hp (hφ.injective.ne (by omega)))

 theorem compactPerturbation_kernel_stabilizes (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    ∃ n, ((ContinuousLinearMap.id ℝ E+T : E →L[ℝ] E).toLinearMap^n).ker=
      ((ContinuousLinearMap.id ℝ E+T : E →L[ℝ] E).toLinearMap^(n+1)).ker := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+T
  apply compactPerturbation_filtration_stops T hT (fun n => (P.toLinearMap^n).ker)
    P.toLinearMap.iterateKer.monotone
  · intro n
    rw [←ContinuousLinearMap.toLinearMap_pow]
    exact (P^n).isClosed_ker
  · intro n x hx
    change (P.toLinearMap^n) (P.toLinearMap x)=0
    change (P.toLinearMap^(n+1)) x=0 at hx
    simpa only [pow_succ,Module.End.mul_apply] using hx

 theorem compactPerturbation_injective_of_surjective (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hs : Surjective (ContinuousLinearMap.id ℝ E+T)) :
    Injective (ContinuousLinearMap.id ℝ E+T) := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+T
  obtain ⟨n,hn⟩ := compactPerturbation_kernel_stabilizes T hT
  change (P.toLinearMap^n).ker=(P.toLinearMap^(n+1)).ker at hn
  apply (LinearMap.ker_eq_bot (f := P.toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hp : ∀ n : ℕ, Surjective (P.toLinearMap^n) := by
    intro m
    induction m with
    | zero => exact fun y => ⟨y,rfl⟩
    | succ m hm =>
      intro y
      obtain ⟨z,hz⟩ := hm y
      obtain ⟨x,hx⟩ := hs z
      refine ⟨x,?_⟩
      rw [pow_succ,Module.End.mul_apply]
      exact (congrArg (P.toLinearMap^m) hx).trans hz
  obtain ⟨y,rfl⟩ := hp n x
  have hy : y∈(P.toLinearMap^(n+1)).ker := by
    change (P.toLinearMap^(n+1)) y=0
    simpa only [pow_succ',Module.End.mul_apply] using hx
  rw [←hn] at hy
  exact hy


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Fredholm_CompactFredholmAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_surjective_of_injective (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hi : Injective (ContinuousLinearMap.id ℝ E+T)) :
    Surjective (ContinuousLinearMap.id ℝ E+T) := by
  obtain he | hr := hT.hasEigenvalue_or_mem_resolventSet (μ := (-1:ℝ)) (by norm_num)
  · exfalso
    apply he
    rw [Module.End.genEigenspace_one]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hi
    change x+T x=0+T 0
    have hx' : T x-(-1:ℝ) • x=0 := hx
    simpa only [neg_smul,one_smul,sub_neg_eq_add,add_comm,map_zero,add_zero] using hx'
  · rw [spectrum.mem_resolventSet_iff,←IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at hr
    convert hr.2 using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [add_comm]

 theorem compactPerturbation_injective_iff_surjective (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    Injective (ContinuousLinearMap.id ℝ E+T) ↔ Surjective (ContinuousLinearMap.id ℝ E+T) :=
  ⟨compactPerturbation_surjective_of_injective T hT,
    compactPerturbation_injective_of_surjective T hT⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph_isClosed _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule_isClosed
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

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {K E : Type*} [MetricSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holder_norm_le_of_estimate (α : ℝ) (u : HolderSpace K E α) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (h0 : ∀ x, ‖holderValue α u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue α u x-holderValue α u y‖ ≤ H*(dist x y)^α) :
    ‖u‖ ≤ max A H := by
  change max ‖u.val.1‖ ‖u.val.2‖ ≤ _
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hA).mpr h0
  · apply (BoundedContinuousFunction.norm_le hH).mpr
    intro z
    have hh := h1 z.val.1 z.val.2
    rw [holderSpace_relation α u _ _ z.property,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (mul_comm _ _))
      (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α)

 

lemma holder_third_interpolation (u : HolderSpace K E ((1:ℝ)/3)) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (h0 : ∀ x, ‖holderValue ((1:ℝ)/3) u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ L*dist x y) :
    ‖u‖ ≤ max A ((2*A)^((2:ℝ)/3)*L^((1:ℝ)/3)) := by
  apply holder_norm_le_of_estimate _ _ hA (by positivity) h0
  intro x y
  have hb : ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ 2*A :=
    (norm_sub_le _ _).trans (by linarith [h0 x,h0 y])
  calc
    ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ =
      ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖^((2:ℝ)/3)*
        ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖^((1:ℝ)/3) := by
          rw [←Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
          norm_num
    _ ≤ (2*A)^((2:ℝ)/3)*(L*dist x y)^((1:ℝ)/3) := by
      gcongr
      exact h1 x y
    _ = ((2*A)^((2:ℝ)/3)*L^((1:ℝ)/3))*(dist x y)^((1:ℝ)/3) := by
      rw [Real.mul_rpow hL dist_nonneg,mul_assoc]

lemma holder_third_small_sup (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : HolderSpace K E ((1:ℝ)/3),
      (∀ x, ‖holderValue ((1:ℝ)/3) u x‖ ≤ δ) →
      (∀ x y, ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ L*dist x y) →
      ‖u‖ < ε := by
  let φ : ℝ → ℝ := fun t => max t ((2*t)^((2:ℝ)/3)*L^((1:ℝ)/3))
  have hc : Continuous φ := continuous_id.max
    (((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)).comp
      (continuous_const.mul continuous_id)).mul continuous_const)
  have hφ : φ 0=0 := by simp [φ,Real.zero_rpow (by norm_num : (2:ℝ)/3≠0)]
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro u h0 h1
  have hh : φ (δ/2) < ε := by
    have ht := hd (show dist (δ/2) 0 < δ by simpa [Real.dist_eq,abs_of_pos (half_pos hδ),abs_of_pos hδ] using half_lt_self hδ)
    rw [hφ,dist_zero_right] at ht
    exact (le_abs_self _).trans_lt ht
  exact (holder_third_interpolation u (half_pos hδ).le hL h0 h1).trans_lt hh

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holderDiskRestrict_uniformInducing (R M : ℝ) (L : NNReal) :
    IsUniformInducing (fun u : holderLipschitzSet (E := E) R M L => holderDiskRestrict R u.val) := by
  rw [Metric.isUniformInducing_iff]
  refine ⟨(holderDiskRestrict (E := E) R).uniformContinuous.comp uniformContinuous_subtype_val,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_third_small_sup (K := ℂ) (E := E) (2*L) ε (by positivity) hε
  refine ⟨δ,hδ,?_⟩
  intro u v huv
  rw [Subtype.dist_eq,dist_eq_norm]
  apply hd (u.val-v.val)
  · intro x
    simp only [map_sub,BoundedContinuousFunction.sub_apply]
    by_cases hx : ‖x‖≤R
    · let z : Metric.closedBall (0:ℂ) R := ⟨x,by simpa using hx⟩
      have hh := BoundedContinuousFunction.dist_coe_le_dist
        (f := holderDiskRestrict R u.val) (g := holderDiskRestrict R v.val) z
      have hh' : ‖holderValue ((1:ℝ)/3) u.val x - holderValue ((1:ℝ)/3) v.val x‖ ≤
          dist (holderDiskRestrict R u.val) (holderDiskRestrict R v.val) := by
        simpa only [dist_eq_norm,holderDiskRestrict_apply] using hh
      exact hh'.trans huv.le
    · rw [u.property.1 x (lt_of_not_ge hx),v.property.1 x (lt_of_not_ge hx),sub_self,norm_zero]
      exact hδ.le
  · intro x y
    have hh := (u.property.2.2.sub v.property.2.2).dist_le_mul x y
    simpa only [map_sub,BoundedContinuousFunction.sub_apply,Pi.sub_apply,dist_eq_norm,
      NNReal.coe_add,two_mul] using hh

 

lemma holderLipschitzSet_totallyBounded [ProperSpace E] (R M : ℝ) (L : NNReal) :
    TotallyBounded (holderLipschitzSet (E := E) R M L) := by
  let A := holderLipschitzSet (E := E) R M L
  let K := Metric.closedBall (0:ℂ) R
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) R)
  let f : A → K →ᵇ E := fun u => holderDiskRestrict R u.val
  have he : Equicontinuous ((↑) : Set.range f → K → E) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    intro g
    obtain ⟨u,hu⟩ := g.property
    rw [←hu]
    change LipschitzWith L (fun x : K => holderValue ((1:ℝ)/3) u.val x.val)
    simpa only [mul_one,Function.comp_def] using u.property.2.2.comp (LipschitzWith.subtype_val K)
  have hc : IsCompact (closure (Set.range f)) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0:E) M) (isCompact_closedBall _ _) (Set.range f)
    (by
      intro g x hg
      obtain ⟨u,rfl⟩ := hg
      rw [Metric.mem_closedBall,dist_zero_right]
      exact ((holderValue ((1:ℝ)/3) u.val).norm_coe_le_norm x.val).trans u.property.2.1) he
  have ht : TotallyBounded (univ : Set A) :=
    (totallyBounded_image_iff (holderDiskRestrict_uniformInducing R M L)).mp
      (by simpa only [image_univ] using hc.totallyBounded.subset subset_closure)
  have hti := ht.image uniformContinuous_subtype_val
  simpa only [image_univ,Subtype.range_coe] using hti

lemma holderLipschitzSet_isCompact_closure [ProperSpace E] [CompleteSpace E]
    (R M : ℝ) (L : NNReal) : IsCompact (closure (holderLipschitzSet (E := E) R M L)) :=
  (holderLipschitzSet_totallyBounded R M L).closure.isCompact_of_isClosed isClosed_closure

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
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

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem c1Holder_contDiff (α : ℝ) (u : C1HolderSpace E α) :
    ContDiff ℝ 1 (holderValue α (c1HolderValue α u)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨holderValue α (c1HolderDeriv α u),
    (holderValue α (c1HolderDeriv α u)).continuous,c1Holder_hasFDerivAt α u⟩

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma compactCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (compactCRInverseValue R u) x Complex.I -
      Complex.I • fderiv ℝ (compactCRInverseValue R u) x 1 = compactHolderValue R u x := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have hh := cauchyTransform_holder_complexCurl (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v) (compactHolderValue_bound R v) (norm_nonneg v)
    (compactHolderValue_holder R v) x
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  have hs : (2*Complex.I) • compactHolderValue R v x = -compactHolderValue R u x := by
    change (2*Complex.I) • ((Complex.I/2) • compactHolderValue R u x) = _
    rw [smul_smul,show (2*Complex.I)*(Complex.I/2)=(-1:ℂ) by ring_nf;simp,neg_one_smul]
  rw [hs] at hh
  change Complex.I • _ - _ = _ at hh
  apply neg_injective
  simpa only [neg_sub] using hh

lemma compactCRInverse_contDiff (R : ℝ) (u : CompactHolderSpace E R) :
    ContDiff ℝ 1 (compactCRInverseValue R u) := c1Holder_contDiff _ _

lemma compactCRInverse_tendsto_zero (R : ℝ) (u : CompactHolderSpace E R) :
    Tendsto (compactCRInverseValue R u) (cocompact ℂ) (𝓝 0) := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  exact cauchyTransform_tendsto_zero (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v)



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrameFredholm
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
section
universe v
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma c1HolderValue_bound (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    ‖holderValue α (c1HolderValue α u) x‖ ≤ ‖u‖ :=
  ((holderValue α (c1HolderValue α u)).norm_coe_le_norm x).trans
    ((le_max_left _ _).trans (le_max_left _ _))

lemma c1HolderDeriv_bound (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    ‖holderValue α (c1HolderDeriv α u) x‖ ≤ ‖u‖ :=
  ((holderValue α (c1HolderDeriv α u)).norm_coe_le_norm x).trans
    ((le_max_left _ _).trans (le_max_right _ _))

lemma c1HolderValue_lipschitz (α : ℝ) (u : C1HolderSpace E α) :
    LipschitzWith ‖u‖₊ (holderValue α (c1HolderValue α u)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (c1Holder_hasFDerivAt α u x).differentiableAt)
  intro x
  rw [c1Holder_fderiv]
  exact_mod_cast c1HolderDeriv_bound α u x

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplexHDivRealOfNat_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplexContinuousLinearMapRealIdHDivOfNat
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupC1HolderSpaceHDivRealOfNat_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupHolderSpaceComplexHDivRealOfNat_2
lemma c1LowerOrder_image_lipschitz (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3))
    (L : NNReal) (hL : LipschitzWith L (holderValue ((1:ℝ)/3) M))
    (u : C1HolderSpace E ((1:ℝ)/3)) (hu : ‖u‖ ≤ 1) :
    LipschitzWith (‖M‖₊+L) (holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let f := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)
  let A := holderValue ((1:ℝ)/3) M
  have hMx : ‖A x‖≤‖M‖ := (A.norm_coe_le_norm x).trans (holderValue_norm _ M)
  have huy : ‖f y‖≤1 := (c1HolderValue_bound _ u y).trans hu
  have hfv : ‖f x-f y‖≤dist x y := by
    have hf : ‖f x-f y‖≤‖u‖*dist x y := by
      simpa only [f,dist_eq_norm,coe_nnnorm] using (c1HolderValue_lipschitz _ u).norm_sub_le x y
    calc
      ‖f x-f y‖ ≤ ‖u‖*dist x y := hf
      _ ≤ 1*dist x y := mul_le_mul_of_nonneg_right hu dist_nonneg
      _ = dist x y := one_mul _
  have hAv : ‖A x-A y‖≤(L:ℝ)*dist x y := by
    simpa only [A,dist_eq_norm] using hL.norm_sub_le x y
  rw [dist_eq_norm]
  change ‖A x (f x)-A y (f y)‖≤(↑(‖M‖₊+L):ℝ)*dist x y
  have he : A x (f x)-A y (f y) = A x (f x-f y)+(A x-A y) (f y) := by
    simp only [map_sub,sub_apply]
    abel
  rw [he,NNReal.coe_add]
  exact (norm_add_le _ _).trans ((add_le_add
    ((A x).le_opNorm _ |>.trans (mul_le_mul hMx hfv (norm_nonneg _) (norm_nonneg _)))
    ((A x-A y).le_opNorm _ |>.trans (mul_le_mul hAv huy (norm_nonneg _) (by positivity)))).trans_eq
    (by simp only [mul_one,coe_nnnorm];ring))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpaceComplexHDivOfNat_1
local instance instNormedSpaceRealHolderSpaceComplexContinuousLinearMapIdHDivOfNat_rb09950_1 : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealC1HolderSpaceHDivOfNat_1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealHolderSpaceComplexHDivOfNat_2
lemma c1LowerOrderCLM_compact [ProperSpace F] [CompleteSpace F]
    (R : ℝ) (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3))
    (hs : ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) M x=0)
    (L : NNReal) (hL : LipschitzWith L (holderValue ((1:ℝ)/3) M)) :
    IsCompactOperator (c1LowerOrderCLM M) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall (c1LowerOrderCLM M).toLinearMap
    (by norm_num : (0:ℝ)<1)).mpr
  apply (holderLipschitzSet_isCompact_closure R ‖M‖ (‖M‖₊+L)).of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro v ⟨u,hu,rfl⟩
  have hu' : ‖u‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
  refine ⟨?_,?_,c1LowerOrder_image_lipschitz M L hL u hu'⟩
  · intro x hx
    change holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u) x=0
    rw [c1LowerOrderCLM_value,hs x hx,zero_apply]
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg M)).mpr
    intro x
    change ‖holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u) x‖≤‖M‖
    rw [c1LowerOrderCLM_value]
    exact ((holderValue ((1:ℝ)/3) M x).le_opNorm _).trans
      ((mul_le_mul ((holderValue ((1:ℝ)/3) M).norm_coe_le_norm x |>.trans
        (holderValue_norm _ M)) ((c1HolderValue_bound _ u x).trans hu')
          (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))

end

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter





open Set Function Filter Topology

 

 

open Set Function Filter Topology
open scoped NNReal

 

 

open scoped NNReal
open Set Function Filter Topology

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped ContDiff Topology
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenOperators
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
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

 theorem c1LowerOrderCLM_compact_holder (R : ℝ)
    (M : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0) :
    IsCompactOperator (c1LowerOrderCLM M) := by
  let b : ContDiffBump (0:ℂ) := ⟨max R 0+1,max R 0+2,by positivity,by linarith⟩
  let P : ℂ → E →L[ℝ] E := fun z => b z • ContinuousLinearMap.id ℝ E
  have hP : ContDiff ℝ ∞ P := b.contDiff.smul contDiff_const
  have hc : HasCompactSupport P := b.hasCompactSupport.smul_right
  let Q := compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) P hP hc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hP (by simp)
  have hQ := c1LowerOrderCLM_compact (E := E) b.rOut Q (by
    intro z hz
    change b z • ContinuousLinearMap.id ℝ E=0
    rw [b.zero_of_le_dist (by simpa using hz.le),zero_smul]) L hL
  have he : c1LowerOrderCLM M=(holderCLM ((1:ℝ)/3) M).comp (c1LowerOrderCLM Q) := by
    apply ContinuousLinearMap.ext
    intro u
    apply holderValue_injective ((1:ℝ)/3)
    apply BoundedContinuousFunction.ext
    intro z
    change holderValue ((1:ℝ)/3) M z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u) z)=
      holderValue ((1:ℝ)/3) M z (P z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u) z))
    by_cases hz : ‖z‖≤R
    · have hb : b z=1 := b.one_of_mem_closedBall (by
        simp only [Metric.mem_closedBall,dist_zero_right]
        exact hz.trans ((le_max_left R 0).trans (by dsimp [b]; linarith)))
      simp only [P,hb,one_smul,ContinuousLinearMap.id_apply]
    · rw [hs z (lt_of_not_ge hz)]
      rfl
  rw [he]
  exact hQ.clm_comp (holderCLM ((1:ℝ)/3) M)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem unmarkedLower_compact {n : ℕ} (R : ℝ) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0) :
    IsCompactOperator (unmarkedLower R M hs) :=
  ((c1LowerOrderCLM_compact_holder R M hs).comp_clm _).codRestrict _
    (compactHolderSubmodule_isClosed R)

 theorem frame_product_CR {n : ℕ} {a : ℂ → End n} {v : ℂ → Phase n} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hv : DifferentiableAt ℝ v z) (K M : End n)
    (hint : ∀ x, a z (Complex.I • x)=K (a z x))
    (hM : ∀ x, fderiv ℝ a z Complex.I x-K (fderiv ℝ a z 1 x)=a z (M x)) :
    fderiv ℝ (fun w => a w (v w)) z Complex.I-
      K (fderiv ℝ (fun w => a w (v w)) z 1)=
    a z (fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1+M (v z)) := by
  have hd (w : ℂ) : fderiv ℝ (fun w => a w (v w)) z w=
      a z (fderiv ℝ v z w)+fderiv ℝ a z w (v z) := by
    rw [fderiv_clm_apply ha hv]
    rfl
  rw [hd Complex.I,hd 1,map_add,←hint (fderiv ℝ v z 1),map_add,map_sub]
  calc
    _ = (a z (fderiv ℝ v z Complex.I)-a z (Complex.I • fderiv ℝ v z 1))+
      (fderiv ℝ a z Complex.I (v z)-K (fderiv ℝ a z 1 (v z))) := by abel
    _ = _ := by rw [hM]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem c1_framed_decaying_kernel {n : ℕ} (R : ℝ) (K a M : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (ha : ContDiff ℝ 1 a) (v : ℂ → Phase n) (hv : ContDiff ℝ 1 v)
    (hAout : ∀ z : ℂ, R<‖z‖ → a z=ContinuousLinearMap.id ℝ _)
    (hAinj : ∀ z, Injective (a z))
    (hint : ∀ z x, a z (Complex.I • x)=K z (a z x))
    (hM : ∀ z x, fderiv ℝ a z Complex.I x-K z (fderiv ℝ a z 1 x)=a z (M z x))
    (hzero : ∀ z, fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1+M z (v z)=0)
    (hvlim : Tendsto v (cocompact ℂ) (𝓝 0)) : v=0 := by
  let u : ℂ → Phase n := fun z => a z (v z)
  have hu : ContDiff ℝ 1 u := ha.clm_apply hv
  have hCR (z : ℂ) : fderiv ℝ u z Complex.I=K z (fderiv ℝ u z 1) := by
    apply sub_eq_zero.mp
    have hh := frame_product_CR (ha.differentiable one_ne_zero z)
      (hv.differentiable one_ne_zero z) (K z) (M z) (hint z) (hM z)
    change fderiv ℝ u z Complex.I-K z (fderiv ℝ u z 1)=_ at hh
    rw [hh,hzero z,map_zero]
  have hlim : Tendsto u (cocompact ℂ) (𝓝 0) := by
    apply hvlim.congr'
    filter_upwards [(isCompact_closedBall (0:ℂ) R).compl_mem_cocompact] with z hz
    have hzR : R<‖z‖ := by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hz
    change v z=a z (v z)
    rw [hAout z hzR,ContinuousLinearMap.id_apply]
  have hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z := by
    filter_upwards [(isCompact_closedBall (0:ℂ) R).compl_mem_cocompact] with z hz
    have hzR : R<‖z‖ := by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hz
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hu.differentiable one_ne_zero z,?_⟩
    have hh := hCR z
    rw [hKout z hzR] at hh
    exact hh
  have hu0 := c1_decaying_CR_zero K hK hu hCR hholo hlim
  funext z
  apply hAinj z
  change u z=a z 0
  rw [congrFun hu0 z,map_zero]
  rfl

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.FrozenSurjectiveLocal6
theorem framed_unmarked_surjective_oai {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (A : C1HolderSpace (End n) ((1:ℝ)/3)) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hAout : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ _)
    (hAinj : ∀ z, Injective (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z))
    (hint : ∀ z x, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (Complex.I • x)=
      K z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z x))
    (hM : ∀ z x, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (holderValue ((1:ℝ)/3) M z x)) :
    Surjective (fun g : CompactHolderSpace (Phase n) R => g+unmarkedLower R M hs g) := by
  apply (compactPerturbation_injective_iff_surjective _ (unmarkedLower_compact R M hs)).mp
  apply (LinearMap.ker_eq_bot (f := (ContinuousLinearMap.id ℝ (CompactHolderSpace (Phase n) R)+unmarkedLower R M hs).toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro g hg
  change g+unmarkedLower R M hs g=0 at hg
  have hzero (z : ℂ) : compactHolderValue R g z+holderValue ((1:ℝ)/3) M z (compactCRInverseValue R g z)=0 :=
    congrArg (fun g => compactHolderValue R g z) hg
  have hg0 := c1_framed_decaying_kernel R K
    (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) (holderValue ((1:ℝ)/3) M)
    hK hKout (c1Holder_contDiff _ A) (compactCRInverseValue R g)
    (compactCRInverse_contDiff R g) hAout hAinj hint hM
    (fun z => by rw [compactCRInverse_rightInverse R g z]; exact hzero z)
    (compactCRInverse_tendsto_zero R g)
  apply Subtype.ext
  apply holderValue_injective ((1:ℝ)/3)
  apply BoundedContinuousFunction.ext
  intro z
  have hh := compactCRInverse_rightInverse R g z
  rw [hg0] at hh
  simpa using hh.symm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.framed_unmarked_surjective_oai := @OAI.HigherDimensionalBallPacking.Rigidity.framed_unmarked_surjective_oai
