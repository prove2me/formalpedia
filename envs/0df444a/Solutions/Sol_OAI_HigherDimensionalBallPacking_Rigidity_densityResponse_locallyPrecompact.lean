-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_locallyPrecompact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:11:56.839655+00:00
-- url     : https://prove2.me/submissions/2405a9a3-3070-4e69-97c4-71d1a8c96810

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp009
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_responseFactor_contDiffAt

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_CompactContinuation
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
namespace TwoPointContinuation






open scoped ContDiff Topology
open Set Filter Function






open scoped ContDiff Topology
open Set Filter Function






open scoped ContDiff Topology
open Set Filter Function






open scoped Topology
open Set Filter Function

 theorem locallyPrecompact_finite {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y] [ProperSpace Y] (f : X → Y) (x : X) (hf : ContinuousAt f x) :
    LocallyPrecompact f x := by
  refine ⟨f ⁻¹' Metric.closedBall (f x) 1,hf.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by norm_num)),
    Metric.closedBall (f x) 1,isCompact_closedBall _ _,image_preimage_subset _ _⟩

 theorem locallyPrecompact_compactLinear {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (hL : IsCompactOperator L) (x : X) : LocallyPrecompact L x := by
  obtain ⟨K,hK,hLK⟩ := hL.image_closedBall_subset_compact (‖x‖+1)
  refine ⟨Metric.closedBall 0 (‖x‖+1),?_,K,hK,hLK⟩
  apply mem_of_superset (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1))
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh := norm_le_norm_sub_add y x
  have hy' : ‖y-x‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  linarith

 theorem LocallyPrecompact.prod {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : X → Z} {x : X}
    (hf : LocallyPrecompact f x) (hg : LocallyPrecompact g x) :
    LocallyPrecompact (fun x => (f x,g x)) x := by
  obtain ⟨V,hV,K,hK,hfK⟩ := hf
  obtain ⟨W,hW,L,hL,hgL⟩ := hg
  exact ⟨V∩W,inter_mem hV hW,K×ˢL,hK.prod hL,by rintro _ ⟨y,hy,rfl⟩; exact ⟨hfK ⟨y,hy.1,rfl⟩,hgL ⟨y,hy.2,rfl⟩⟩⟩

 theorem LocallyPrecompact.comp {X Y Z : Type*} [TopologicalSpace X] [MetricSpace Y]
    [TopologicalSpace Z] {f : X → Y} {x : X} (hf : LocallyPrecompact f x)
    (hfc : ContinuousAt f x) (g : Y → Z) (U : Set Y) (ho : IsOpen U)
    (hgu : ContinuousOn g U) (hx : f x∈U) : LocallyPrecompact (g∘f) x := by
  obtain ⟨V,hV,K,hK,hfK⟩ := hf
  obtain ⟨r,hr,hru⟩ := Metric.isOpen_iff.mp ho (f x) hx
  let C := K∩Metric.closedBall (f x) (r/2)
  have hC : IsCompact C := hK.inter_right Metric.isClosed_closedBall
  have hCU : C⊆U := by
    intro y hy
    apply hru
    exact lt_of_le_of_lt hy.2 (half_lt_self hr)
  refine ⟨V∩f ⁻¹' Metric.closedBall (f x) (r/2),inter_mem hV
    (hfc.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (half_pos hr))),g '' C,hC.image_of_continuousOn (hgu.mono hCU),?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact ⟨f y,⟨hfK ⟨y,hy.1,rfl⟩,hy.2⟩,rfl⟩

end TwoPointContinuation

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
local instance instNormedSpaceRealHolderSpaceComplexContinuousLinearMapIdHDivOfNat_r28bb1f_1 : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) := inferInstance
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
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityResidual
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








open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupCompactHolderSpace_2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealCompactHolderSpace_2
theorem densitySlope_contDiff {n : ℕ} (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (densitySlope p q R) := by
  let C := compactCRInverse (E := Phase n) R
  have h0 : ContDiff ℝ ∞ (fun g : CompactHolderSpace (Phase n) R => compactCRInverseValue R g 0) := ((c1HolderEval ((1:ℝ)/3) (0:ℂ)).comp C).contDiff
  have h1 : ContDiff ℝ ∞ (fun g : CompactHolderSpace (Phase n) R => compactCRInverseValue R g 1) := ((c1HolderEval ((1:ℝ)/3) (1:ℂ)).comp C).contDiff
  exact contDiff_const.sub (h1.sub h0)

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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian

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

 theorem cutoffValues_compact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (b : ContDiffBump (0:ℂ)) : IsCompactOperator (cutoffValues (E := E) b) := by
  apply c1LowerOrderCLM_compact_holder b.rOut
  intro z hz
  change b z • (ContinuousLinearMap.id ℝ E)=0
  rw [b.zero_of_le_dist (by simpa using hz.le),zero_smul]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapHSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.compactMapCompactSpace
theorem responseCoords_contDiff {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ) :
    ContDiff ℝ ∞ (responseCoords B p q R) := by
  have h0 : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => compactCRInverseValue R y.2 0) :=
    (((c1HolderEval ((1:ℝ)/3) 0).comp (compactCRInverse (E := Phase n) R)).contDiff).comp contDiff_snd
  have ha : ContDiff ℝ ∞ (fun y : ℝ × CompactHolderSpace (Phase n) R => densitySlope p q R y.2) :=
    (densitySlope_contDiff p q R).comp contDiff_snd
  exact (contDiff_fst.prodMk ((contDiff_const.sub h0).prodMk ha)).prodMk
    (((cutoffValues B).comp (compactCRInverse (E := Phase n) R)).contDiff.comp contDiff_snd)

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
namespace TwoPointContinuation
 theorem LocallyPrecompact.comp_contDiffAt {X Y Z : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {x : X} (hf : LocallyPrecompact f x) (hfc : ContinuousAt f x)
    (g : Y → Z) (hg : ContDiffAt ℝ ∞ g (f x)) : LocallyPrecompact (g∘f) x := by
  obtain ⟨U,hU,hgU⟩ := contDiffAt_zero.mp (hg.of_le (by simp : (0:ℕ∞ω)≤∞))
  obtain ⟨V,hVU,hVo,hxV⟩ := mem_nhds_iff.mp hU
  exact hf.comp hfc g V hVo (hgU.mono hVU) hxV
end TwoPointContinuation
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.responseLocalCompactSpace
theorem responseCoords_locallyPrecompact {n : ℕ} (B : ContDiffBump (0:ℂ)) (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) : LocallyPrecompact (responseCoords B p q R) y := by
  let L := (cutoffValues (E := Phase n) B).comp ((compactCRInverse R).comp (ContinuousLinearMap.snd ℝ ℝ _))
  have hL : IsCompactOperator L := (cutoffValues_compact B).comp_clm _
  have hf := locallyPrecompact_finite (fun y : ℝ × CompactHolderSpace (Phase n) R => (responseCoords B p q R y).1) y
    (responseCoords_contDiff B p q R).continuous.continuousAt.fst
  exact hf.prod (locallyPrecompact_compactLinear L hL y)

 theorem densityResponse_locallyPrecompact_oai {n : ℕ} (b B : ContDiffBump (0:ℂ)) (p q : Phase n)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hi : (cutoffFrozen b (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y))).IsInvertible) :
    LocallyPrecompact (densityResponse b B p q A hA hc) y :=
  (responseCoords_locallyPrecompact B p q b.rOut y).comp_contDiffAt
    (responseCoords_contDiff B p q b.rOut).continuous.continuousAt _
    (responseFactor_contDiffAt b B A hA hc _ hi)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_locallyPrecompact_oai := @OAI.HigherDimensionalBallPacking.Rigidity.densityResponse_locallyPrecompact_oai
