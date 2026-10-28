-- Prove2me | solution 1 for OAI.CannonEmbeddedArc.Arc.face_incidence_card_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:15.270328+00:00
-- url     : https://prove2.me/submissions/12bdaeec-fa96-4214-b409-6437d75a46bd

import Mathlib
import Definitions.Def_OAIQ046C000
import Definitions.Def_OAIQ046C001

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_GraphPreconnected
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonClosedCover
open Set

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

theorem graph_preconnected (G : SimpleGraph ι) (C : ι → Set X)
    (hclosed : ∀ i,IsClosed (C i))
    (hconn : IsPreconnected (⋃ i,C i)) (hne : ∀ i,(C i).Nonempty)
    (hadj : ∀ i j,i≠j → (C i∩C j).Nonempty → G.Adj i j) : G.Preconnected := by
  classical
  intro a b
  by_contra hb
  let U : Set X := ⋃ i : {i : ι | G.Reachable a i},C i.val
  let V : Set X := ⋃ i : {i : ι | ¬G.Reachable a i},C i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite fun i=>hclosed i.val
  have hV : IsClosed V := isClosed_iUnion_of_finite fun i=>hclosed i.val
  have hsub : (⋃ i,C i)⊆U∪V := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases h : G.Reachable a i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
  obtain ⟨x,hx⟩ := hne a
  obtain ⟨y,hy⟩ := hne b
  obtain ⟨z,hz,hzU,hzV⟩ := isPreconnected_closed_iff.mp hconn U V hU hV hsub
    ⟨x,mem_iUnion.mpr ⟨a,hx⟩,mem_iUnion.mpr ⟨⟨a,.rfl⟩,hx⟩⟩
    ⟨y,mem_iUnion.mpr ⟨b,hy⟩,mem_iUnion.mpr ⟨⟨b,hb⟩,hy⟩⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzU
  obtain ⟨j,hj⟩ := mem_iUnion.mp hzV
  have hneij : i.val≠j.val := fun h=>j.property (h ▸ i.property)
  exact j.property (i.property.trans (hadj _ _ hneij ⟨z,hi,hj⟩).reachable)
end CannonClosedCover

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_UnitCircle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonCircleBoundary
open Set Topology Metric
open scoped OnePoint

lemma real_interval_bounded {S : Set ℝ} (hS : IsPreconnected S)
    {b c : ℝ} (hbc : b < c) (hb : b∈closure S\S) (hc : c∈closure S\S) :
    S⊆Icc b c := by
  intro z hz
  constructor
  · by_contra h
    have hzb : z<b := lt_of_not_ge h
    obtain ⟨w,hw,hwS⟩ := (mem_closure_iff_nhds.mp hc.1) (Ioi b) (isOpen_Ioi.mem_nhds hbc)
    exact hb.2 (hS.ordConnected.out hz hwS ⟨hzb.le,hw.le⟩)
  · by_contra h
    have hcz : c<z := lt_of_not_ge h
    obtain ⟨w,hw,hwS⟩ := (mem_closure_iff_nhds.mp hb.1) (Iio c) (isOpen_Iio.mem_nhds hbc)
    exact hc.2 (hS.ordConnected.out hwS hz ⟨hw.le,hcz.le⟩)

lemma onePoint_boundary_unique {S : Set (OnePoint ℝ)} (hS : IsPreconnected S)
    (hinf : (∞ : OnePoint ℝ)∈closure S\S) {b c : ℝ}
    (hb : (b : OnePoint ℝ)∈closure S\S) (hc : (c : OnePoint ℝ)∈closure S\S) : b=c := by
  let T : Set ℝ := ((↑) : ℝ → OnePoint ℝ) ⁻¹' S
  have he : ((↑) : ℝ → OnePoint ℝ) '' T=S := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    obtain ⟨w,rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinf.2 (h ▸ hz))
    exact ⟨w,hz,rfl⟩
  have hT : IsPreconnected T := OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.mp (he ▸ hS)
  have hcl : closure T=((↑) : ℝ → OnePoint ℝ) ⁻¹' closure S := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image,he]
  have hbT : b∈closure T\T := ⟨by rw [hcl]; exact hb.1,hb.2⟩
  have hcT : c∈closure T\T := ⟨by rw [hcl]; exact hc.1,hc.2⟩
  by_contra hbc
  have hbounded : ∃ l u : ℝ,T⊆Icc l u := by
    rcases lt_or_gt_of_ne hbc with h|h
    · exact ⟨b,c,real_interval_bounded hT h hbT hcT⟩
    · exact ⟨c,b,real_interval_bounded hT h hcT hbT⟩
  obtain ⟨l,u,hlu⟩ := hbounded
  have hcompact := (isCompact_Icc (a:=l) (b:=u)).image OnePoint.continuous_coe
  have hsub : S⊆((↑) : ℝ → OnePoint ℝ) '' Icc l u := by
    rw [←he]
    exact image_mono hlu
  have hinfmem := (closure_minimal hsub hcompact.isClosed) hinf.1
  exact OnePoint.infty_notMem_image_coe hinfmem

theorem circle_boundary_no_three {S : Set UnitCircle} (hS : IsPreconnected S)
    {a b c : UnitCircle} (ha : a∈closure S\S) (hb : b∈closure S\S)
    (hc : c∈closure S\S) (hab : a≠b) (hac : a≠c) : b=c := by
  let H := circleChart a
  let T : Set (OnePoint ℝ) := H.symm '' S
  have hT : IsPreconnected T := hS.image H.symm H.symm.continuous.continuousOn
  have hcl : closure T=H.symm '' closure S := H.symm.isClosedEmbedding.closure_image_eq S
  have hboundary {z : UnitCircle} (hz : z∈closure S\S) : H.symm z∈closure T\T := by
    refine ⟨?_,?_⟩
    · rw [hcl]; exact mem_image_of_mem _ hz.1
    · rintro ⟨w,hw,he⟩
      exact hz.2 (H.symm.injective he ▸ hw)
  have hH : H ∞=a := circleChart_infty a
  have hainf : H.symm a=∞ := H.symm_apply_eq.mpr hH.symm
  have hinf : (∞ : OnePoint ℝ)∈closure T\T := hainf ▸ hboundary ha
  have hbinf : H.symm b≠∞ := fun h => hab (H.symm.injective (hainf.trans h.symm))
  have hcinf : H.symm c≠∞ := fun h => hac (H.symm.injective (hainf.trans h.symm))
  obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp hbinf
  obtain ⟨y,hy⟩ := OnePoint.ne_infty_iff_exists.mp hcinf
  have he := onePoint_boundary_unique hT hinf (hx.symm ▸ hboundary hb) (hy.symm ▸ hboundary hc)
  apply H.symm.injective
  rw [←hx,←hy,he]

end CannonCircleBoundary

namespace CannonCircleBoundary
open Set Topology Metric

lemma radialDirection_continuous (q : ℂ) : Continuous (radialDirection q) := by
  apply Continuous.subtype_mk
  have h : Continuous (fun z : Punctured q => (z:ℂ)-q) :=
    continuous_subtype_val.sub continuous_const
  exact (h.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property))).smul h

lemma radialDirection_reconstruct (q : ℂ) (z : Punctured q) :
    (z:ℂ)=q+‖(z:ℂ)-q‖ • (radialDirection q z:ℂ) := by
  have hn : ‖(z:ℂ)-q‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)
  simp only [radialDirection,smul_smul,mul_inv_cancel₀ hn,one_smul]
  abel

lemma radialDirection_radial (q : ℂ) (u : UnitCircle) {s : ℝ} (hs : 0 < s) :
    radialDirection q ⟨q+s•(u:ℂ),radial_ne q u hs⟩=u := by
  apply Subtype.ext
  have hu : ‖(u:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp u.property
  simp only [radialDirection,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs,
    hu,mul_one,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]

theorem radial_face_degree_two {q : ℂ} {r : ℝ} {U : Set ℂ}
    (hU : IsPreconnected U) (hUball : U⊆ball q r\{q})
    (u : Fin 3 → UnitCircle)
    (hnot : ∀ i,∀ s : ℝ,0 < s → s < r → q+s•(u i:ℂ)∉U)
    (hcl : ∀ i,∃ s : ℝ,0 < s ∧ q+s•(u i:ℂ)∈closure U) :
    ¬Function.Injective u := by
  let V : Set (Punctured q) := Subtype.val ⁻¹' U
  have he : Subtype.val '' V=U := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    exact ⟨⟨z,(hUball hz).2⟩,hz,rfl⟩
  have hV : IsPreconnected V := IsInducing.subtypeVal.isPreconnected_image.mp (he ▸ hU)
  let S := radialDirection q '' V
  have hS : IsPreconnected S := hV.image _ (radialDirection_continuous q).continuousOn
  have hb (i : Fin 3) : u i∈closure S\S := by
    constructor
    · obtain ⟨s,hs,hsi⟩ := hcl i
      let z : Punctured q := ⟨q+s•(u i:ℂ),radial_ne q (u i) hs⟩
      have hz : z∈closure V := by
        rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,he]
        exact hsi
      have hh := mem_closure_image (radialDirection_continuous q).continuousAt hz
      rwa [radialDirection_radial q (u i) hs] at hh
    · rintro ⟨z,hz,heq⟩
      have hs : 0<‖(z:ℂ)-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr z.property)
      have hsr : ‖(z:ℂ)-q‖ < r := by simpa only [mem_ball,dist_eq_norm] using (hUball hz).1
      have hz' : q+‖(z:ℂ)-q‖•(u i:ℂ)∈U := by
        rw [←heq,←radialDirection_reconstruct q z]
        exact hz
      exact hnot i _ hs hsr hz'
  intro hu
  have hh := circle_boundary_no_three hS (hb 0) (hb 1) (hb 2)
    (hu.ne (by decide)) (hu.ne (by decide))
  exact (by decide : (1:Fin 3)≠2) (hu hh)
end CannonCircleBoundary

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Energy_PuncturedBallConnected
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPlanarNeighborhood

theorem punctured_ball_connected (x : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConnected (ball x r\{x}) := by
  let e := OpenPartialHomeomorph.univBall x r
  have hc : IsConnected ({(0:ℂ)}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  have he : e '' ({(0:ℂ)}ᶜ : Set ℂ)=ball x r\{x} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzS : z∈e.source := by simp [e]
      refine ⟨?_,?_⟩
      · simpa [e,OpenPartialHomeomorph.univBall_target x hr] using e.map_source hzS
      · intro hy
        have hz0 : z=0 := by
          calc
            z=e.symm (e z) := (e.left_inv hzS).symm
            _=0 := by simpa [e] using congrArg e.symm (mem_singleton_iff.mp hy)
        exact hz (mem_singleton_iff.mpr hz0)
    · rintro ⟨hy,hyx⟩
      have hyT : y∈e.target := by simpa [e,OpenPartialHomeomorph.univBall_target x hr] using hy
      refine ⟨e.symm y,?_,e.right_inv hyT⟩
      intro hz
      have hz0 : e.symm y=0 := mem_singleton_iff.mp hz
      apply hyx
      apply mem_singleton_iff.mpr
      calc
        y=e (e.symm y) := (e.right_inv hyT).symm
        _=x := by rw [hz0]; simp [e]
  rw [←he]
  exact hc.image e (OpenPartialHomeomorph.continuous_univBall x r).continuousOn

theorem isolated_frontier_forces_punctured_ball {R : Set ℂ} (hR : IsOpen R)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : x∈closure R) (hxR : x∉R)
    (hbound : closure R∩(ball x r\{x})⊆R) : ball x r\{x}⊆R := by
  let U := ball x r\{x}
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (punctured_ball_connected x hr).isPreconnected
  let S : Set U := Subtype.val ⁻¹' R
  have hS : IsClopen S := by
    constructor
    · have he : S=Subtype.val ⁻¹' closure R := by
        ext z
        exact ⟨fun hz => subset_closure hz,fun hz => hbound ⟨hz,z.property⟩⟩
      rw [he]
      exact isClosed_closure.preimage continuous_subtype_val
    · exact hR.preimage continuous_subtype_val
  obtain ⟨y,hyB,hyR⟩ := (mem_closure_iff_nhds.mp hx) _ (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hyx : y≠x := fun h => hxR (h ▸ hyR)
  have hn : S.Nonempty := ⟨⟨y,hyB,hyx⟩,hyR⟩
  have he := hS.eq_univ hn
  intro z hz
  exact (show (⟨z,hz⟩ : U)∈S from he.symm ▸ mem_univ _)
end CannonPlanarNeighborhood

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_ComponentRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonFaceIncidence
open Set Topology

variable {X : Type*} [TopologicalSpace X]

lemma component_region_eq (V : Set X) (x : V) :
    region V ConnectedComponents.mk (ConnectedComponents.mk x)=connectedComponentIn V x.val := by
  rw [connectedComponentIn_eq_image x.property]
  ext y
  constructor
  · rintro ⟨hy,hye⟩
    exact ⟨⟨y,hy⟩,ConnectedComponents.coe_eq_coe'.mp hye,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,ConnectedComponents.coe_eq_coe'.mpr hy⟩

lemma component_region_connected (V : Set X) (d : ConnectedComponents V) :
    IsConnected (region V ConnectedComponents.mk d) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe d
  rw [component_region_eq]
  exact isConnected_connectedComponentIn_iff.mpr x.property

lemma component_regions_disjoint (V : Set X) {d e : ConnectedComponents V} (hne : d≠e) :
    Disjoint (region V ConnectedComponents.mk d) (region V ConnectedComponents.mk e) := by
  apply disjoint_left.mpr
  rintro x ⟨hx,hd⟩ ⟨hx',he⟩
  exact hne (hd.symm.trans he)
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_FiniteClosedLocal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonVertexLinks
open Set Metric Topology

lemma finite_closed_local {J X : Type*} [Finite J] [MetricSpace X]
    (C : J → Set X) (hC : ∀ j,IsClosed (C j)) (q : X) :
    ∃ r>0,∀ z∈ball q r,∀ j,z∈C j → q∈C j := by
  classical
  let U := ⋃ j : {j : J | q∉C j},C j.val
  have hU : IsClosed U := isClosed_iUnion_of_finite fun j=>hC j.val
  have hq : q∈Uᶜ := by
    rintro ⟨S,⟨j,rfl⟩,hq⟩
    exact j.property hq
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU.isOpen_compl q hq
  refine ⟨r,hr,?_⟩
  intro z hz j hj
  by_contra hn
  exact hsub hz (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩)
lemma finite_pos_lower {J : Type*} [Finite J] (f : J → ℝ) (hf : ∀ j,0<f j) :
    ∃ r>0,∀ j,r<f j := by
  have ho : IsOpen (⋂j,Iio (f j)) := isOpen_iInter_of_finite fun _=>isOpen_Iio
  have hzero : (0:ℝ)∈⋂j,Iio (f j) := mem_iInter.mpr hf
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp ho 0 hzero
  refine ⟨ε/2,half_pos hε,mem_iInter.mp (hsub ?_)⟩
  rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
  linarith
end CannonVertexLinks

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_FlatChartBoundaryPatch
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonFaceIncidence
open Set Topology Metric

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]
theorem flat_chart_boundary_patch {V W : Set X} {π : V → D} (hπ : Continuous π)
    (H : (ℝ × ℝ) ≃ₜ X) (hW : IsOpen W) (h₀ : H (0,0)∈W)
    (hflat : ∀ z∈W, z∈V ↔ (H.symm z).2≠0)
    {d : D} (hd : d∈incident V π (H (0,0))) :
    ∃ U B : Set X, IsOpen U ∧ H (0,0)∈U ∧ U⊆W ∧
      IsConnected B ∧ B⊆W∩region V π d ∧ U∩Vᶜ⊆closure B := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage H.continuous).mem_nhds h₀)
  let C := openBox r
  let U := H '' C
  have hCU : C⊆H ⁻¹' W := by rw [show C=openBox r from rfl,openBox_eq_ball]; exact hball
  have hUW : U⊆W := by rintro _ ⟨p,hp,rfl⟩; exact hCU hp
  have hU : IsOpen U := H.isOpenMap C (by rw [show C=openBox r from rfl,openBox_eq_ball]; exact isOpen_ball)
  have h₀U : H (0,0)∈U := ⟨(0,0),by rw [show C=openBox r from rfl,openBox_eq_ball]; exact mem_ball_self hr,rfl⟩
  let S : Bool → Set X := fun b => H '' halfBox r b
  have hSc (b : Bool) : IsConnected (S b) :=
    (halfBox_connected hr b).image H H.continuous.continuousOn
  have hcover : U∩V=⋃ b, S b := by
    ext x
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpV⟩
      have hp₂ : p.2≠0 := by simpa using (hflat (H p) (hCU hp)).mp hpV
      rcases lt_or_gt_of_ne hp₂ with hl|hr'
      · exact mem_iUnion.mpr ⟨false,⟨p,⟨hp.1,hp.2.1,hl⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨true,⟨p,⟨hp.1,hr',hp.2.2⟩,rfl⟩⟩
    · intro hx
      obtain ⟨b,p,hp,rfl⟩ := mem_iUnion.mp hx
      have hpC : p∈C := by
        cases b
        · exact ⟨hp.1,hp.2.1,hp.2.2.trans hr⟩
        · exact ⟨hp.1,(neg_neg_of_pos hr).trans hp.2.1,hp.2.2⟩
      refine ⟨⟨p,hpC,rfl⟩,(hflat (H p) (hCU hpC)).mpr ?_⟩
      simp only [H.symm_apply_apply]
      cases b
      · exact hp.2.2.ne
      · exact hp.2.1.ne'
  have hclose (b : Bool) : U∩Vᶜ⊆closure (S b) := by
    rintro x ⟨⟨p,hp,hpx⟩,hxV⟩
    subst x
    have hp₂ : p.2=0 := by
      by_contra h
      apply hxV
      apply (hflat (H p) (hCU hp)).mpr
      simpa using h
    rw [show S b=H '' halfBox r b from rfl,←H.image_closure]
    exact ⟨p,halfBox_closure hr hp hp₂ b,rfl⟩
  obtain ⟨labels,hsub,hlabels⟩ := sector_incidence hU inter_subset_left hπ S hSc hcover hclose
  have hnv : H (0,0)∉V := by
    intro h
    have hh := (hflat _ h₀).mp h
    simp at hh
  have hh := hlabels (H (0,0)) ⟨h₀U,hnv⟩
  obtain ⟨b,hb⟩ := hh ▸ hd
  refine ⟨U,S b,hU,h₀U,hUW,hSc b,?_,hclose b⟩
  intro z hz
  refine ⟨hUW ?_,hb ▸ hsub b hz⟩
  exact (hcover.symm ▸ mem_iUnion_of_mem b hz).1
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Next
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonCycleOrder
open Set SimpleGraph

lemma walk_tag {E A:Type*} {R:E→A→Prop} {e:E} {z:E⊕A}
    (p:(bipartite R).Walk (.inl e) z) : ∀ k≤p.length,tag (p.getVert k)=k%2 := by
  intro k
  induction k with
  | zero => intro _; simp [tag]
  | succ k ih =>
    intro hk
    have hr := ih (by omega)
    have ha := p.adj_getVert_succ (i:=k) (by omega)
    have hstep : tag (p.getVert (k+1))+tag (p.getVert k)=1 := by
      cases h0:p.getVert k <;> cases h1:p.getVert (k+1) <;>
        simp_all [bipartite,tag]
    rw [hr] at hstep
    omega

theorem exists_order {E A:Type*} [Finite E] [Finite A] (R:E→A→Prop)
    (hc:(bipartite R).IsCycles) (hp:(bipartite R).Preconnected)
    (hne:∃ e a,R e a) :
    ∃ n:ℕ,∃ hn:0<n,∃ e:Fin n≃E,∃ a:Fin n≃A,
      2≤n ∧ (∀ i,R (e i) (a i)) ∧ (∀ i,R (e (next hn i)) (a i)) := by
  classical
  obtain ⟨e₀,a₀,he₀⟩ := hne
  let G := bipartite R
  obtain ⟨p,hpc,hcover⟩ := hc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c:=G.connectedComponentMk (.inl e₀)) (by rfl)
    (show (G.neighborSet (.inl e₀)).Nonempty from ⟨.inr a₀,he₀⟩)
  have hsupp (z:E⊕A) : z∈p.support := by
    rw [←p.mem_verts_toSubgraph,hcover]
    change G.connectedComponentMk z=G.connectedComponentMk (.inl e₀)
    exact ConnectedComponent.sound (hp z (.inl e₀))
  have hpar := walk_tag p
  have heven : p.length%2=0 := by
    have hh := hpar p.length le_rfl
    simpa only [p.getVert_length,tag] using hh.symm
  let n := p.length/2
  have hlen : p.length=2*n := by omega
  have hn : 0<n := by have hh:=hpc.three_le_length; omega
  have hs (z:E⊕A) : ∃ k<p.length,p.getVert k=z := by
    obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.mp (hsupp z)
    by_cases h:k<p.length
    · exact ⟨k,h,hk⟩
    · have he:k=p.length := by omega
      exact ⟨0,by omega,by simpa [he] using hk⟩
  have exE (i:Fin n) : ∃ e:E,p.getVert (2*i.val)=.inl e := by
    have hh := hpar (2*i.val) (by omega)
    cases hv:p.getVert (2*i.val) with
    | inl e => exact ⟨e,rfl⟩
    | inr a => simp [hv,tag] at hh
  have exA (i:Fin n) : ∃ a:A,p.getVert (2*i.val+1)=.inr a := by
    have hh := hpar (2*i.val+1) (by omega)
    cases hv:p.getVert (2*i.val+1) with
    | inl e => simp [hv,tag] at hh
    | inr a => exact ⟨a,rfl⟩
  choose e he using exE
  choose a ha using exA
  have hein : Function.Injective e := by
    intro i j hij
    have hh := hpc.getVert_injOn' (by change 2*i.val≤p.length-1; omega)
      (by change 2*j.val≤p.length-1; omega) ((he i).trans ((congrArg Sum.inl hij).trans (he j).symm))
    apply Fin.ext; omega
  have hain : Function.Injective a := by
    intro i j hij
    have hh := hpc.getVert_injOn' (by change 2*i.val+1≤p.length-1; omega)
      (by change 2*j.val+1≤p.length-1; omega) ((ha i).trans ((congrArg Sum.inr hij).trans (ha j).symm))
    apply Fin.ext; omega
  have hesur : Function.Surjective e := by
    intro v
    obtain ⟨k,hk,hv⟩ := hs (.inl v)
    have hm := hpar k (by omega)
    simp only [hv,tag] at hm
    let i:Fin n := ⟨k/2,by omega⟩
    have heq:2*i.val=k := by dsimp [i]; omega
    exact ⟨i,Sum.inl.inj ((he i).symm.trans (by simpa only [heq] using hv))⟩
  have hasur : Function.Surjective a := by
    intro v
    obtain ⟨k,hk,hv⟩ := hs (.inr v)
    have hm := hpar k (by omega)
    simp only [hv,tag] at hm
    let i:Fin n := ⟨k/2,by omega⟩
    have heq:2*i.val+1=k := by dsimp [i]; omega
    exact ⟨i,Sum.inr.inj ((ha i).symm.trans (by simpa only [heq] using hv))⟩
  have hnext (i:Fin n) : p.getVert (2*i.val+2)=.inl (e (next hn i)) := by
    unfold next
    split_ifs with h
    · rw [show 2*i.val+2 = 2*(i.val+1) by omega]
      exact he ⟨i.val+1,h⟩
    · have hi:2*i.val+2=p.length := by omega
      rw [hi,p.getVert_length]
      simpa using (he ⟨0,hn⟩)
  refine ⟨n,hn,Equiv.ofBijective e ⟨hein,hesur⟩,Equiv.ofBijective a ⟨hain,hasur⟩,by have hh:=hpc.three_le_length; omega,?_,?_⟩
  · intro i
    have hh := p.adj_getVert_succ (i:=2*i.val) (by omega)
    rw [he i,ha i] at hh
    exact hh
  · intro i
    have hh := p.adj_getVert_succ (i:=2*i.val+1) (by omega)
    have heq:2*i.val+1+1=2*i.val+2 := by omega
    rw [heq,ha i,hnext i] at hh
    exact hh
end CannonCycleOrder

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_PositiveHalfAxis
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPlanarCorner
open Set Topology Metric

lemma slit_box_connected {r : ℝ} (hr : 0 < r) :
    IsConnected (CannonFaceIncidence.openBox r\positiveHalfAxis) := by
  let L : Set (ℝ × ℝ) := Ioo (-r) 0 ×ˢ Ioo (-r) r
  have hL : IsConnected L := (isConnected_Ioo (neg_neg_of_pos hr)).prod
    (isConnected_Ioo (by linarith : -r < r))
  have hm (b : Bool) : (L∩CannonFaceIncidence.halfBox r b).Nonempty := by
    cases b
    · refine ⟨(-r/2,-r/2),?_,?_⟩
      · change (-r< -r/2 ∧ -r/2<0) ∧ (-r< -r/2 ∧ -r/2 < r)
        constructor <;> constructor <;> linarith
      · change (-r< -r/2 ∧ -r/2 < r) ∧ (-r< -r/2 ∧ -r/2<0)
        constructor <;> constructor <;> linarith
    · refine ⟨(-r/2,r/2),?_,?_⟩
      · change (-r< -r/2 ∧ -r/2<0) ∧ (-r < r/2 ∧ r/2 < r)
        constructor <;> constructor <;> linarith
      · change (-r< -r/2 ∧ -r/2 < r) ∧ (0 < r/2 ∧ r/2 < r)
        constructor <;> constructor <;> linarith
  have he : CannonFaceIncidence.openBox r\positiveHalfAxis=
      (L∪CannonFaceIncidence.halfBox r false)∪CannonFaceIncidence.halfBox r true := by
    ext p
    simp only [CannonFaceIncidence.openBox,CannonFaceIncidence.halfBox,L,positiveHalfAxis,
      Bool.false_eq_true,↓reduceIte,mem_sdiff,mem_ofPred_eq,mem_prod,mem_Ioo,mem_union]
    constructor
    · rintro ⟨⟨hx,hy⟩,hn⟩
      by_cases hpx : p.1<0
      · exact Or.inl (Or.inl ⟨⟨hx.1,hpx⟩,hy⟩)
      · have hpy : p.2≠0 := fun h => hn ⟨le_of_not_gt hpx,h⟩
        rcases lt_or_gt_of_ne hpy with hp|hp
        · exact Or.inl (Or.inr ⟨hx,hy.1,hp⟩)
        · exact Or.inr ⟨hx,hp,hy.2⟩
    · rintro ((⟨hx,hy⟩|⟨hx,hy⟩)|⟨hx,hy⟩)
      · exact ⟨⟨⟨hx.1,hx.2.trans hr⟩,hy⟩,fun h => hx.2.not_ge h.1⟩
      · exact ⟨⟨hx,hy.1,hy.2.trans hr⟩,fun h => hy.2.ne h.2⟩
      · exact ⟨⟨hx,(neg_neg_of_pos hr).trans hy.1,hy.2⟩,fun h => hy.1.ne' h.2⟩
  rw [he]
  apply IsConnected.union _ (IsConnected.union (hm false) hL (CannonFaceIncidence.halfBox_connected hr false))
    (CannonFaceIncidence.halfBox_connected hr true)
  obtain ⟨p,hpL,hpT⟩ := hm true
  exact ⟨p,Or.inl hpL,hpT⟩

lemma straight_ray_chart (x u : ℂ) (hu : u≠0) :
    ∃ H : (ℝ × ℝ) ≃ₜ ℂ, H (0,0)=x ∧
      H '' positiveHalfAxis={z | ∃ s : ℝ, 0 ≤ s ∧ z=x+s•u} := by
  let H := (Complex.equivRealProdCLM.toHomeomorph.symm.trans (Homeomorph.mulLeft₀ u hu)).trans
    (Homeomorph.addLeft x)
  have ht (t : ℝ) : H (t,0)=x+t•u := by
    change x+u*Complex.equivRealProdCLM.symm (t,0)=x+t•u
    congr 1
    rw [Complex.real_smul]
    have he : Complex.equivRealProdCLM.symm (t,0)=(t:ℂ) := by apply Complex.ext <;> rfl
    rw [he,mul_comm]
  refine ⟨H,by simpa using ht 0,?_⟩
  ext z
  constructor
  · rintro ⟨⟨s,t⟩,⟨hs,ht₀⟩,rfl⟩
    change t=0 at ht₀
    subst t
    exact ⟨s,hs,ht s⟩
  · rintro ⟨s,hs,hz⟩
    exact ⟨(s,0),⟨hs,rfl⟩,(ht s).trans hz.symm⟩
end CannonPlanarCorner

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_RegionBoundaryHitsOpen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonFaceIncidence
open Set Topology

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

lemma region_boundary_hits_in_open {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V⊆U) (hconn : IsPreconnected U) (hne : (U\V).Nonempty)
    {π : V → D} (hπ : Continuous π) (d : D) (hd : (region V π d).Nonempty) :
    ∃ x∈U\V, d∈incident V π x := by
  by_contra hn
  have hbound : closure (region V π d)⊆region V π d∪Uᶜ := by
    intro x hx
    by_cases hxU : x∈U
    · left
      have hxV : x∈V := by by_contra hxV; exact hn ⟨x,⟨hxU,hxV⟩,hx⟩
      exact closure_region_inside hV hπ hx hxV
    · exact Or.inr hxU
  have hclosed : IsClosed (region V π d∪Uᶜ) := by
    apply isClosed_of_closure_subset
    rw [closure_union,hU.isClosed_compl.closure_eq]
    exact union_subset hbound subset_union_right
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set U := Subtype.val ⁻¹' region V π d
  have hC : IsClopen C := by
    constructor
    · have he : C=Subtype.val ⁻¹' (region V π d∪Uᶜ) := by
        ext x
        simp only [C,mem_preimage,mem_union,mem_compl_iff]
        exact or_iff_left (not_not.mpr x.property) |>.symm
      rw [he]
      exact hclosed.preimage continuous_subtype_val
    · exact (region_isOpen hV hπ d).preimage continuous_subtype_val
  obtain ⟨x,hx⟩ := hd
  have hxU : x∈U := hVU (region_subset _ _ _ hx)
  have hCe : C=univ := hC.eq_univ ⟨⟨x,hxU⟩,hx⟩
  obtain ⟨y,hyU,hyV⟩ := hne
  have hyC : (⟨y,hyU⟩ : U)∈C := hCe.symm ▸ mem_univ _
  exact hyV (region_subset _ _ _ hyC)
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FiniteSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonEmbeddedArc.Arc.instFintypeRefinementIndex _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonEmbeddedArc
namespace Arc
variable {X : Type*} [TopologicalSpace X]
lemma trans_injective {x y z : X} (a : Path x y) (b : Path y z)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hmeet : ∀ s t, a s=b t → s=1 ∧ t=0) : Function.Injective (a.trans b) := by
  intro s t he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · have h := congrArg Subtype.val (ha he)
    apply Subtype.ext
    dsimp at h
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he.symm
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · have h := congrArg Subtype.val (hb he)
    apply Subtype.ext
    dsimp at h
    linarith

theorem extend_arc [T2Space X] (a b : Arc X) (hab : a 1=b 0)
    (hy : b 1∉range a) :
    ∃ c : Arc X, c 0=a 0 ∧ c 1=b 1 ∧ range c⊆range a∪range b := by
  have hc : IsCompact (b ⁻¹' range a) :=
    (a.compact_range.isClosed.preimage b.continuous).isCompact
  have hn : (b ⁻¹' range a).Nonempty := ⟨0,⟨1,hab⟩⟩
  obtain ⟨v,hv⟩ := hc.exists_isGreatest hn
  obtain ⟨u,hu⟩ := hv.1
  have hv₁ : v≠1 := fun h => hy (h ▸ hv.1)
  let d := b.subarc v 1 hv₁
  have hd₀ : d 0=a u := (subarc_zero ..).trans hu.symm
  have hd₁ : d 1=b 1 := subarc_one ..
  have hds : range d⊆range b := subarc_range_subset ..
  have hmeet : ∀ s t, a s=d t → s=u ∧ t=0 := by
    intro s t he
    have hin : Icc.convexComb v 1 t∈b ⁻¹' range a := ⟨s,he⟩
    have hle := hv.2 hin
    have hvlt : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 (fun h => hv₁ (Subtype.ext h))
    have hle' : (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v := by
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v at hle
      exact hle
    have ht : t=0 := by
      apply Subtype.ext
      dsimp
      nlinarith [t.property.1]
    refine ⟨?_,ht⟩
    apply a.injective
    simpa only [ht,hd₀] using he
  by_cases hu₀ : u=0
  · refine ⟨d,by simpa only [hu₀] using hd₀,hd₁,hds.trans subset_union_right⟩
  · let c := a.subarc 0 u (Ne.symm hu₀)
    let p : Path (a 0) (a u) := ⟨c.map,subarc_zero ..,subarc_one ..⟩
    let q : Path (a u) (b 1) := ⟨d.map,hd₀,hd₁⟩
    have hpq : ∀ s t, p s=q t → s=1 ∧ t=0 := by
      intro s t he
      obtain ⟨hs,ht⟩ := hmeet (Icc.convexComb 0 u s) t he
      refine ⟨?_,ht⟩
      have huc : (u:ℝ)≠0 := fun h => hu₀ (Subtype.ext h)
      have hh := congrArg Subtype.val hs
      simp only [Icc.coe_convexComb] at hh
      apply Subtype.ext
      dsimp at hh ⊢
      have heq : ((s:ℝ)-1)*(u:ℝ)=0 := by nlinarith [hh]
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right huc)
    refine ⟨⟨(p.trans q).toContinuousMap,trans_injective p q c.injective d.injective hpq⟩,
      (p.trans q).source,(p.trans q).target,?_⟩
    change range (p.trans q)⊆range a∪range b
    rw [Path.trans_range]
    exact union_subset_union (subarc_range_subset a 0 u (Ne.symm hu₀)) hds
end Arc
end CannonEmbeddedArc

namespace CannonPolygonal
open CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma FiniteSupport.mono {S T : Set E} (hT : FiniteSupport T) (hST : S⊆T) :
    FiniteSupport S := by
  obtain ⟨P,hP⟩ := hT
  exact ⟨P,hST.trans hP⟩
lemma FiniteSupport.segment (x y : E) : FiniteSupport (segment ℝ x y) := by
  classical
  exact ⟨{(x,y)},by simp⟩
lemma FiniteSupport.union {S T : Set E} (hS : FiniteSupport S) (hT : FiniteSupport T) :
    FiniteSupport (S∪T) := by
  classical
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q,hQ⟩ := hT
  refine ⟨P∪Q,?_⟩
  intro x hx
  rcases hx with hx|hx
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hP hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_left Q hp,hx⟩
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hQ hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_right P hp,hx⟩

lemma polyJoined_of_open_preconnected {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y : E} (hx : x∈U) (hy : y∈U) : PolyJoined U x y := by
  let V := {z | z∈U ∧ PolyJoined U x z}
  let W := {z | z∈U ∧ ¬PolyJoined U x z}
  have hstep (z : E) (hz : z∈U) :
      ∃ ε : ℝ, 0<ε ∧ ∀ w∈ball z ε, segment ℝ z w⊆U := by
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨ε,hε,fun w hw => ((convex_ball z ε).segment_subset (mem_ball_self hε) hw).trans hεU⟩
  have hV : IsOpen V := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε,hε,hs⟩ := hstep z hz.1
    refine ⟨ε,hε,fun w hw => ⟨(hs w hw) (right_mem_segment ..),hz.2.tail (hs w hw)⟩⟩
  have hW : IsOpen W := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε,hε,hs⟩ := hstep z hz.1
    refine ⟨ε,hε,fun w hw => ⟨(hs w hw) (right_mem_segment ..),?_⟩⟩
    intro hj
    apply hz.2 (hj.tail ?_)
    simpa only [segment_symm] using hs w hw
  have hs : U⊆V∪W := by intro z hz; by_cases hj : PolyJoined U x z <;> simp_all [V,W]
  have hd : Disjoint V W := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hz'.2 hz.2
  have hv : x∈U∩V := ⟨hx,hx,.refl⟩
  exact (hc.subset_left_of_subset_union hV hW hd hs ⟨x,hv⟩ hy).2

theorem polyJoined_arc {U : Set E} {x y : E} (h : PolyJoined U x y) (hne : x≠y) :
    ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
  have hh : x=y ∨ ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
    clear hne
    induction h with
    | refl => exact Or.inl rfl
    | @tail y z _ hyz ih =>
      by_cases hxz : x=z
      · exact Or.inl hxz
      · apply Or.inr
        rcases ih with rfl|⟨a,ha₀,ha₁,haU,haS⟩
        · let b : Arc E := ⟨(Path.segment x z).toContinuousMap,Path.segment_injective_of_ne hxz⟩
          refine ⟨b,(Path.segment x z).source,(Path.segment x z).target,?_,?_⟩
          · change range (Path.segment x z)⊆U
            rwa [Path.range_segment]
          · change FiniteSupport (range (Path.segment x z))
            rw [Path.range_segment]
            exact FiniteSupport.segment x z
        · by_cases hz : z∈range a
          · obtain ⟨t,ht⟩ := hz
            have ht₀ : (0:I)≠t := fun h => hxz (ha₀.symm.trans ((congrArg a h).trans ht))
            refine ⟨a.subarc 0 t ht₀,(subarc_zero ..).trans ha₀,(subarc_one ..).trans ht,
              (subarc_range_subset ..).trans haU,haS.mono (subarc_range_subset ..)⟩
          · have hyz' : y≠z := fun h => hz ⟨1,ha₁.trans h⟩
            let b : Arc E := ⟨(Path.segment y z).toContinuousMap,Path.segment_injective_of_ne hyz'⟩
            have hb₀ : b 0=y := (Path.segment y z).source
            have hb₁ : b 1=z := (Path.segment y z).target
            have hbR : range b=segment ℝ y z := Path.range_segment y z
            obtain ⟨c,hc₀,hc₁,hcs⟩ := extend_arc a b (ha₁.trans hb₀.symm) (by simpa only [hb₁] using hz)
            refine ⟨c,hc₀.trans ha₀,hc₁.trans hb₁,hcs.trans (union_subset haU ?_),
              (haS.union ?_).mono hcs⟩
            · rwa [hbR]
            · rw [hbR]
              exact FiniteSupport.segment y z
  exact hh.resolve_left hne

end CannonPolygonal

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Lift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

namespace CannonWinding

lemma lift_exp (f : C(I,Circle)) (t : I) : Circle.exp (lift f t)=f t :=
  congr_fun (Circle.isCoveringMap_exp.liftPath_lifts f _ _) t

lemma turn_eq_of_lift (f : C(I,Circle)) (g : C(I,ℝ))
    (hg : ∀ t, Circle.exp (g t)=f t) : turn f=g 1-g 0 := by
  have hconst : ∀ t t', g t-lift f t=g t'-lift f t' := by
    apply Circle.isCoveringMap_exp.const_of_comp (g.continuous.sub (lift f).continuous)
    intro t t'
    change Circle.exp (g t-lift f t)=Circle.exp (g t'-lift f t')
    simp only [Circle.exp_sub,hg,lift_exp,div_self']
  have h := hconst 1 0
  dsimp only [turn]
  linarith

lemma turn_homotopy (H : C(I×I,Circle)) (hH : ∀ s, H (s,0)=H (s,1)) :
    turn (H.comp ⟨fun t => (0,t),by fun_prop⟩)=
      turn (H.comp ⟨fun t => (1,t),by fun_prop⟩) := by
  let f := H.comp (⟨fun t => (0,t),by fun_prop⟩ : C(I,I×I))
  let g := lift f
  have h₀ (t : I) : H (0,t)=Circle.exp (g t) := (lift_exp f t).symm
  let L := Circle.isCoveringMap_exp.liftHomotopy H g h₀
  have hL (s t : I) : Circle.exp (L (s,t))=H (s,t) :=
    congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H g h₀) (s,t)
  have heq : ∀ s s', L (s,1)-L (s,0)=L (s',1)-L (s',0) := by
    apply Circle.isCoveringMap_exp.const_of_comp (by fun_prop)
    intro s s'
    simp only [Circle.exp_sub,hL,←hH,div_self']
  rw [turn_eq_of_lift (H.comp ⟨fun t => (0,t),by fun_prop⟩) (L.comp ⟨fun t => (0,t),by fun_prop⟩) (fun t => hL 0 t),
    turn_eq_of_lift (H.comp ⟨fun t => (1,t),by fun_prop⟩) (L.comp ⟨fun t => (1,t),by fun_prop⟩) (fun t => hL 1 t)]
  exact heq 0 1

end CannonWinding

namespace CannonWinding
variable {A : Type*} [TopologicalSpace A]

lemma winding_homotopy (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (z : ℂ) (hz : z∉range H) :
    winding (H.comp ⟨fun t => (0,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(0,t),ht⟩)=
    winding (H.comp ⟨fun t => (1,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(1,t),ht⟩) := by
  let K := direction (H-.const (I×I) z) (fun p hp => hz ⟨p,sub_eq_zero.mp hp⟩)
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,ContinuousMap.sub_apply,ContinuousMap.const_apply,hclosed]
  exact turn_homotopy K hc

lemma winding_moving_point (f : C(I,ℂ)) (hf : f 0=f 1) (p : C(I,ℂ))
    (hp : ∀ s, p s∉range f) : winding f (p 0) (hp 0)=winding f (p 1) (hp 1) := by
  let H : C(I×I,ℂ) := ⟨fun z => f z.2-p z.1,by fun_prop⟩
  have hH (z : I×I) : H z≠0 := fun h => hp z.1 ⟨z.2,sub_eq_zero.mp h⟩
  let K := direction H hH
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,H,ContinuousMap.coe_mk,hf]
  exact turn_homotopy K hc

end CannonWinding

namespace CannonWinding
open Metric

lemma winding_eq_of_homotopy (f g : C(I,ℂ)) (z : ℂ) (hf : z∉range f) (hg : z∉range g)
    (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (h₀ : ∀ t, H (0,t)=f t) (h₁ : ∀ t, H (1,t)=g t) (hz : z∉range H) :
    winding f z hf=winding g z hg := by
  have h₀' : H.comp ⟨fun t => (0,t),by fun_prop⟩=f := ContinuousMap.ext h₀
  have h₁' : H.comp ⟨fun t => (1,t),by fun_prop⟩=g := ContinuousMap.ext h₁
  simpa only [h₀',h₁'] using winding_homotopy H hclosed z hz

theorem winding_locally_constant (f : C(I,ℂ)) (hf : f 0=f 1) :
    IsLocallyConstant (fun z : ↥((range f)ᶜ) => winding f z.val z.property) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  have ho : IsOpen ((range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds z.property)
  refine ⟨Subtype.val ⁻¹' ball z.val ε,isOpen_ball.preimage continuous_subtype_val,
    mem_ball_self hε,?_⟩
  intro w hw
  have hp (s : I) : Path.segment z.val w.val s∉range f := by
    apply hball
    apply (convex_ball z.val ε).segment_subset (mem_ball_self hε) hw
    rw [←Path.range_segment]
    exact mem_range_self s
  have heq := winding_moving_point f hf (Path.segment z.val w.val).toContinuousMap hp
  change winding f (Path.segment z.val w.val 0) _ =
    winding f (Path.segment z.val w.val 1) _ at heq
  simpa only [Path.source,Path.target] using heq.symm

end CannonWinding

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Reverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

lemma local_arc_flat {K : Set ℂ} {x : ℂ} (a : Arc ℂ)
    (Q : Finset (ℂ × ℂ)) (hQ : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) (ht : a t=x)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x∈U)
    (hUK : ∀ z∈U, z∈K ↔ z∈range a) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
  obtain ⟨H,W,hW,htW,h₀,hW'⟩ := tame_graph_flat_chart (fun _ : Unit => a)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) Q (fun _ => hQ) () ht₀ ht₁
  refine ⟨H,W∩U,hW.inter hU,⟨ht ▸ htW,hxU⟩,h₀.trans ht,?_⟩
  intro z hz
  exact (hUK z hz.2).trans (by simpa only [iUnion_const] using hW' z hz.1)

lemma pair_start_local_arc (a b : Arc ℂ) (hab : a 0=b 0)
    (hc : ∀ s t, a s=b t → (s=0∨s=1) ∧ (t=0∨t=1)) :
    ∃ (c : Arc ℂ) (t : I) (U : Set ℂ), 0<t ∧ t<1 ∧ c t=a 0 ∧
      IsOpen U ∧ a 0∈U ∧ range c⊆range a∪range b ∧
      ∀ z∈U, (z∈range a∪range b ↔ z∈range c) := by
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm₀ : 0 < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < 1 := by change (1/2:ℝ)<1; norm_num
  let A := a.subarc 0 m hm₀.ne
  let B := b.subarc 0 m hm₀.ne
  let p : Path (a m) (a 0) := A.path.symm.cast (by simp [A]) (by simp [A])
  let q : Path (a 0) (b m) := B.path.cast (by simpa [B] using hab) (by simp [B])
  have hp (s : I) : p s=a (Icc.convexComb 0 m (unitInterval.symm s)) := rfl
  have hq (s : I) : q s=b (Icc.convexComb 0 m s) := rfl
  have hpq (s t : I) (he : p s=q t) : s=1 ∧ t=0 := by
    obtain ⟨hs,ht⟩ := hc _ _ he
    have hsₘ : Icc.convexComb 0 m (unitInterval.symm s) ≤ m := Icc.convexComb_le hm₀.le _
    have htₘ : Icc.convexComb 0 m t ≤ m := Icc.convexComb_le hm₀.le _
    have hs₀ : Icc.convexComb 0 m (unitInterval.symm s)=0 := hs.resolve_right (fun h => hm₁.not_ge (h ▸ hsₘ))
    have ht₀ : Icc.convexComb 0 m t=0 := ht.resolve_right (fun h => hm₁.not_ge (h ▸ htₘ))
    have hsval := congrArg Subtype.val hs₀
    have htval := congrArg Subtype.val ht₀
    constructor <;> apply Subtype.ext
    · simp only [Icc.coe_convexComb,unitInterval.coe_symm_eq] at hsval
      change (s:ℝ)=1
      dsimp [m] at hsval
      linarith
    · simp only [Icc.coe_convexComb] at htval
      change (t:ℝ)=0
      dsimp [m] at htval
      linarith
  have hpi : Function.Injective p := fun s t he =>
    unitInterval.symm_bijective.injective (A.injective he)
  have hqi : Function.Injective q := B.injective
  let c : Arc ℂ := ⟨(p.trans q).toContinuousMap,trans_injective p q hpi hqi hpq⟩
  have hcrange : range c=a '' Icc 0 m ∪ b '' Icc 0 m := by
    change range (p.trans q)=_
    rw [Path.trans_range]
    have hpR : range p=range A := by exact Path.symm_range A.path
    rw [hpR]
    change range A∪range B=_
    rw [subarc_range_eq a hm₀,subarc_range_eq b hm₀]
  let T : Set ℂ := a '' Ici m ∪ b '' Ici m
  have hT : IsClosed T :=
    (isClosed_Ici.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image b.continuous).isClosed
  have hxT : a 0∉T := by
    rintro (⟨s,hs,he⟩|⟨s,hs,he⟩)
    · have he₀ := a.injective he
      subst s
      exact hm₀.not_ge hs
    · have he₀ := b.injective (he.trans hab)
      subst s
      exact hm₀.not_ge hs
  refine ⟨c,m,Tᶜ,hm₀,hm₁,?_,hT.isOpen_compl,hxT,?_,?_⟩
  · change (p.trans q) m=a 0
    rw [Path.trans_apply]
    split_ifs with h
    · have hr : (⟨2*(m:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨m.2.1,h⟩⟩:I)=1 := by apply Subtype.ext; dsimp [m]; norm_num
      rw [hr,Path.target]
    · exact (h (by change (1/2:ℝ)≤1/2; rfl)).elim
  · rw [hcrange]
    exact union_subset_union (image_subset_range _ _) (image_subset_range _ _)
  · intro z hz
    rw [hcrange]
    constructor
    · rintro (⟨s,rfl⟩|⟨s,rfl⟩)
      · exact Or.inl ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inl ⟨s,hm,rfl⟩))⟩,rfl⟩
      · exact Or.inr ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inr ⟨s,hm,rfl⟩))⟩,rfl⟩
    · intro hh
      exact union_subset_union (image_subset_range _ _) (image_subset_range _ _) hh
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner CannonFaceIncidence

lemma pair_start_flat (a b : Arc ℂ) (hab : a 0 = b 0)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0 ∈ W ∧
      H (0,0)=a 0 ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  obtain ⟨c,t,U,ht₀,ht₁,ht,hU,hxU,hsub,hUK⟩ := pair_start_local_arc a b hab hc
  exact local_arc_flat c Q (fun z hz => (hsub hz).elim (fun h => ha h) (fun h => hb h)) ht₀ ht₁ ht hU hxU hUK

theorem pair_flat_at_left (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) (t : I) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a t ∈ W ∧
      H (0,0)=a t ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  by_cases ht₀ : t=0
  · subst t
    exact pair_start_flat a b hab₀ hc Q ha hb
  by_cases ht₁ : t=1
  · subst t
    have hc' : ∀ s t, a.reverse s = b.reverse t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
      intro s t he
      obtain ⟨hs,ht⟩ := hc _ _ he
      simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using And.intro hs ht
    have hh := pair_start_flat a.reverse b.reverse (by simpa) hc' Q
      (by simpa using ha) (by simpa using hb)
    simpa using hh
  have ht₀' : 0<t := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht₀)
  have ht₁' : t<1 := lt_of_le_of_ne (unitInterval.le_one t) ht₁
  have htB : a t ∉ range b := by
    rintro ⟨s,hs⟩
    exact ((hc t s hs.symm).1).elim ht₀ ht₁
  exact local_arc_flat a Q ha ht₀' ht₁' rfl
    b.compact_range.isClosed.isOpen_compl htB (fun z hz => or_iff_left hz)

theorem pair_incident_labels (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π) :
    ∃ labels : Bool → D, ∀ x∈range a ∪ range b,
      incident _ π x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsPreconnected K :=
    IsPreconnected.union' ⟨a 0,mem_range_self 0,⟨0,hab₀.symm⟩⟩
      (isPreconnected_range a.continuous) (isPreconnected_range b.continuous)
  have hflat : ∀ x∈K, ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
    rintro x (⟨t,rfl⟩|⟨t,rfl⟩)
    · exact pair_flat_at_left a b hab₀ hab₁ hc Q ha hb t
    · have hh := pair_flat_at_left b a hab₀.symm hab₁.symm
        (fun s t he => (hc t s he.symm).symm) Q hb ha t
      simpa only [K,union_comm] using hh
  have hloc₀ : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∃ labels : Bool → D, ∀ y∈U∩K, incident _ π y=range labels := by
    intro x hx
    obtain ⟨H,W,hW,hxW,h₀,hW'⟩ := hflat x hx
    have he (z : ℂ) : z∈H '' horizontal ↔ (H.symm z).2=0 := by
      rw [H.image_eq_preimage_symm]
      rfl
    obtain ⟨U,hU,h₀U,_,labels,hlabels⟩ := flat_chart_incidence hπ H hW (h₀.symm ▸ hxW)
      (fun z hz => not_congr ((hW' z hz).trans (he z)))
    exact ⟨U,hU,h₀ ▸ h₀U,labels,by simpa only [compl_compl] using hlabels⟩
  have hloc : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∀ y∈K∩U, incident _ π y=incident _ π x := by
    intro x hx
    obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ x hx
    exact ⟨U,hU,hxU,fun y hy => (hl y hy.symm).trans (hl x ⟨hxU,hx⟩).symm⟩
  have hxK : a 0∈K := Or.inl (mem_range_self 0)
  obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ (a 0) hxK
  refine ⟨l,fun x hx => ?_⟩
  exact (incident_constant_on_preconnected hK hloc x hx (a 0) hxK).trans (hl (a 0) ⟨hxU,hxK⟩)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem pair_labels_surjective (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hπs : Function.Surjective π) :
    ∃ labels : Bool → D, Function.Surjective labels ∧
      ∀ x∈range a ∪ range b, incident _ π x=range labels := by
  obtain ⟨l,hl⟩ := pair_incident_labels a b hab₀ hab₁ hc Q ha hb hπ
  refine ⟨l,?_,hl⟩
  intro d
  obtain ⟨z,hz⟩ := hπs d
  have hd : (region _ π d).Nonempty := ⟨z.val,z.property,hz⟩
  have hK : IsClosed (range a ∪ range b) := a.compact_range.isClosed.union b.compact_range.isClosed
  obtain ⟨x,hx,_,hxd⟩ := region_boundary_hits hK (T:=∅) isClosed_empty (empty_subset _)
    (by simpa using (isPreconnected_univ : IsPreconnected (univ : Set ℂ)))
    ⟨a 0,Or.inl (mem_range_self 0),notMem_empty _⟩ hπ d hd
  change d∈range l
  rw [←hl x hx]
  exact hxd
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma centered_chord_endpoints (A B : ℂ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1/2) :
    let x := A+(1/2:ℝ)•(B-A)
    let c := ε•(B-A)
    x-c∈segment ℝ A B ∧ x+c∈segment ℝ A B := by
  dsimp
  rw [segment_eq_image']
  constructor
  · refine ⟨1/2-ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [sub_smul]
    abel
  · refine ⟨1/2+ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [add_smul]
    abel

lemma centered_chord_ball (A B : ℂ) (hAB : A≠B) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z∈segment ℝ A B)
    (hb : z∈ball (A+(1/2:ℝ)•(B-A)) ‖ε•(B-A)‖) :
    z∈segment ℝ (A+(1/2:ℝ)•(B-A)-ε•(B-A))
      (A+(1/2:ℝ)•(B-A)+ε•(B-A)) := by
  rw [segment_eq_image'] at hz ⊢
  obtain ⟨s,hs,rfl⟩ := hz
  have hD : 0 < ‖B-A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have he : A+s•(B-A)-(A+(1/2:ℝ)•(B-A))=(s-1/2)•(B-A) := by rw [sub_smul]; abel
  have habs : |s-1/2| < ε := by
    rw [mem_ball,dist_eq_norm,he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hε] at hb
    exact (mul_lt_mul_iff_left₀ hD).mp hb
  have hlo := (abs_lt.mp habs).1
  have hhi := (abs_lt.mp habs).2
  refine ⟨(s-1/2+ε)/(2*ε),⟨div_nonneg (by linarith) (by positivity),
    (div_le_one (by positivity : 0 < 2*ε)).mpr (by linarith)⟩,?_⟩
  have hd : (A+(1/2:ℝ)•(B-A)+ε•(B-A))-
      (A+(1/2:ℝ)•(B-A)-ε•(B-A))=(2*ε)•(B-A) := by
    rw [mul_smul,two_smul]; abel
  dsimp only
  rw [hd,smul_smul,div_mul_cancel₀ _ (by positivity : 2*ε≠0)]
  simp only [add_smul,sub_smul]
  abel

theorem pair_isolated_chord (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ (u v : I) (x c : ℂ), u < v ∧ c≠0 ∧ a u=x-c ∧ a v=x+c ∧
      a '' Icc u v=segment ℝ (a u) (a v) ∧
      (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v := by
  let m : I := ⟨1/2,by constructor  <;> norm_num⟩
  obtain ⟨p,q,hpm,hmq,hleft,_,_⟩ := tame_interior_corner Q a ha
    (t:=m) (by change (0:ℝ) < 1/2; norm_num) (by change (1/2:ℝ) < 1; norm_num)
  let D := a m-a p
  have hD : D≠0 := sub_ne_zero.mpr (a.injective.ne hpm.ne.symm)
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  let x := a p+(1/2:ℝ)•D
  have hxseg : x∈segment ℝ (a p) (a m) := by
    rw [segment_eq_image']
    exact ⟨1/2,by constructor  <;> norm_num,rfl⟩
  obtain ⟨w,hw,hwx⟩ := hleft.symm ▸ hxseg
  have hxp : x≠a p := by
    intro he
    have hh : (1/2:ℝ)•D=0 := by
      change a p+(1/2:ℝ)•D=a p at he
      exact add_left_cancel (he.trans (add_zero (a p)).symm)
    exact hD ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hxm : x≠a m := by
    intro he
    have hh : (1/2:ℝ)•D=D := by
      change a p+(1/2:ℝ)•D=a m at he
      exact eq_sub_of_add_eq (by rwa [add_comm])
    have hh' : ((1/2:ℝ)-1)•D=0 := by rw [sub_smul,one_smul,hh,sub_self]
    exact hD ((smul_eq_zero.mp hh').resolve_left (by norm_num))
  have hpw : p < w := lt_of_le_of_ne hw.1 (fun he => hxp (he ▸ hwx).symm)
  have hwm : w  <  m := lt_of_le_of_ne hw.2 (fun he => hxm (he ▸ hwx).symm)
  let T : Set ℂ := a '' Iic p ∪ a '' Ici m ∪ range b
  have hT : IsClosed T :=
    ((isClosed_Iic.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image a.continuous).isClosed).union b.compact_range.isClosed
  have hxT : x∉T := by
    rintro ((⟨s,hs,he⟩|⟨s,hs,he⟩)|⟨s,hs⟩)
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hpw.not_ge hs
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hwm.not_ge hs
    · rcases (hc w s (hwx.trans hs.symm)).2 with rfl | rfl
      · have hwzero := a.injective ((hwx.trans hs.symm).trans hab₀.symm)
        exact (not_lt_of_ge (show (0:I) ≤ p from p.2.1)) (hwzero ▸ hpw)
      · have hwone := a.injective ((hwx.trans hs.symm).trans hab₁.symm)
        exact (not_lt_of_ge (show m ≤ (1:I) from m.2.2)) (hwone ▸ hwm)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hxT)
  let ε := min (1/4) (δ/(2*‖D‖))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε₁ : ε < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  let c : ℂ := ε•D
  have hcn : ‖c‖=ε*‖D‖ := by simp [c,Real.norm_eq_abs,abs_of_pos hε]
  have hc₀ : c≠0 := smul_ne_zero hε.ne' hD
  have hcδ : ‖c‖ < δ := by
    rw [hcn]
    have hh : ε*(2*‖D‖) ≤ δ := (le_div_iff₀ (by positivity)).mp (min_le_right (1/4) (δ/(2*‖D‖)))
    nlinarith
  have hend := centered_chord_endpoints (a p) (a m) hε hε₁
  change x-c∈segment ℝ (a p) (a m) ∧ x+c∈segment ℝ (a p) (a m) at hend
  obtain ⟨u,hu,hu'⟩ := hleft.symm ▸ hend.1
  obtain ⟨v,hv,hv'⟩ := hleft.symm ▸ hend.2
  have huv : u≠v := by
    intro he
    have hh : x-c=x+c := hu'.symm.trans (he ▸ hv')
    have hh' : c+c=0 := by linear_combination -hh
    exact hc₀ (by linear_combination (1/2:ℂ)*hh')
  have hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ segment ℝ (x-c) (x+c) := by
    rintro z ⟨hz,hzb⟩
    have hzT : z∉T := hball (ball_subset_ball hcδ.le hzb)
    rcases hz with ⟨s,rfl⟩|hz
    · have hsp : p ≤ s := le_of_not_ge (fun hh => hzT (Or.inl (Or.inl ⟨s,hh,rfl⟩)))
      have hsm : s  ≤  m := le_of_not_ge (fun hh => hzT (Or.inl (Or.inr ⟨s,hh,rfl⟩)))
      exact centered_chord_ball (a p) (a m) (a.injective.ne hpm.ne) hε
        (hleft ▸ ⟨s,⟨hsp,hsm⟩,rfl⟩) hzb
    · exact (hzT (Or.inr hz)).elim
  rcases lt_or_gt_of_ne huv with huv|hvu
  · have he := segment_subarc_image a hpm huv hleft
      (fun s hs => ⟨hu.1.trans hs.1,hs.2.trans hv.2⟩)
    refine ⟨u,v,x,c,huv,hc₀,hu',hv',he,?_⟩
    rw [he,hu',hv']
    exact hsmall
  · have he := segment_subarc_image a hpm hvu hleft
      (fun s hs => ⟨hv.1.trans hs.1,hs.2.trans hu.2⟩)
    refine ⟨v,u,x,-c,hvu,neg_ne_zero.mpr hc₀,?_,?_,he,?_⟩
    · simpa using hv'
    · simpa only [sub_eq_add_neg] using hu'
    · rw [norm_neg,he,hv',hu',segment_symm]
      exact hsmall
end CannonEmbeddedArc.Arc

noncomputable section
open Set Topology unitInterval

namespace CannonWinding
open Set Topology unitInterval

lemma turn_path_trans {a b c : Circle} (p : Path a b) (q : Path b c) :
    turn (p.trans q).toContinuousMap=turn p.toContinuousMap+turn q.toContinuousMap := by
  let f := lift p.toContinuousMap
  let g := lift q.toContinuousMap
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1+f 1-g 0) :=
    ⟨⟨fun t => g t+f 1-g 0,by fun_prop⟩,by ring,rfl⟩
  have hP (t : I) : Circle.exp (P t)=p t := lift_exp _ t
  have hQ (t : I) : Circle.exp (Q t)=q t := by
    change Circle.exp (g t+f 1-g 0)=q t
    simp only [Circle.exp_sub,Circle.exp_add,f,g,lift_exp]
    simp
  have hL (t : I) : Circle.exp ((P.trans Q) t)=(p.trans q) t := by
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> simp only [hP,hQ]
  rw [turn_eq_of_lift _ (P.trans Q).toContinuousMap hL]
  change (P.trans Q) 1-(P.trans Q) 0=_
  rw [Path.target,Path.source]
  dsimp only [turn,f,g]
  ring

lemma winding_path_trans {a b c : ℂ} (p : Path a b) (q : Path b c)
    (z : ℂ) (hp : z∉range p) (hq : z∉range q) :
    winding (p.trans q).toContinuousMap z (by change z∉range (p.trans q); rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)=
      winding p.toContinuousMap z hp+winding q.toContinuousMap z hq := by
  let f := direction (p.toContinuousMap-.const I z) (fun t ht => hp ⟨t,sub_eq_zero.mp ht⟩)
  let g := direction (q.toContinuousMap-.const I z) (fun t ht => hq ⟨t,sub_eq_zero.mp ht⟩)
  have hfg : f 1=g 0 := by
    apply Circle.ext
    simp [f,g,direction_coe]
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1) := ⟨g,hfg.symm,rfl⟩
  have he : direction ((p.trans q).toContinuousMap-.const I z)
      (fun t ht => (show z∉range (p.trans q) by rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)
        ⟨t,sub_eq_zero.mp ht⟩)=(P.trans Q).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change ((p.trans q) t-z)/(‖(p.trans q) t-z‖:ℂ)=((P.trans Q) t:ℂ)
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> rfl
  change turn (direction _ _)=turn f+turn g
  rw [he]
  exact turn_path_trans P Q

lemma winding_path_homotopy {a : ℂ} {p q : Path a a} (H : p.Homotopy q)
    (z : ℂ) (hz : z∉range H) :
    winding p.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(0,t),by simpa using ht⟩)=
      winding q.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(1,t),by simpa using ht⟩) := by
  exact winding_eq_of_homotopy _ _ _ _ _ H.toHomotopy.toContinuousMap
    (fun s => (H.source s).trans (H.target s).symm)
    (fun t => H.map_zero_left t) (fun t => H.map_one_left t) hz

lemma upperSemi_im (t : I) : 0≤(upperSemi t).im := by
  change 0≤(Circle.exp (Real.pi*(1-(t:ℝ))):ℂ).im
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg Real.pi_pos.le (sub_nonneg.mpr t.property.2),
    by nlinarith [t.property.1,Real.pi_pos]⟩
lemma lowerSemi_im (t : I) : (lowerSemi t).im≤0 := by
  change (Circle.exp (Real.pi*(1+(t:ℝ))):ℂ).im≤0
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im,
    show Real.pi*(1+(t:ℝ))=(Real.pi*(t:ℝ))+Real.pi by ring,Real.sin_add_pi]
  exact neg_nonpos.mpr (Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le t.property.1,mul_le_of_le_one_right Real.pi_pos.le t.property.2⟩)

lemma winding_upperSemi :
    winding upperSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change upperSemi t=0 at ht; have := upperSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = -Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1-(t:ℝ)),by fun_prop⟩
  have he : direction (upperSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := upperSemi_norm t
      change upperSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (upperSemi t-0)/(‖upperSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,upperSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]

lemma winding_lowerSemi :
    winding lowerSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change lowerSemi t=0 at ht; have := lowerSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1+(t:ℝ)),by fun_prop⟩
  have he : direction (lowerSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := lowerSemi_norm t
      change lowerSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (lowerSemi t-0)/(‖lowerSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,lowerSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval Metric

lemma winding_outside_move {a : ℂ} (p : Path a a) (hp : ∀ t, 1≤‖p t‖)
    {z : ℂ} (hz : ‖z‖<1) :
    winding p.toContinuousMap z (path_outside_avoids p hp hz)=
      winding p.toContinuousMap 0 (path_outside_avoids p hp (by simp)) := by
  have hw (s : I) : ‖Path.segment z 0 s‖<1 := by
    have hs : Path.segment z 0 s∈ball (0:ℂ) 1 := by
      apply (convex_ball (0:ℂ) 1).segment_subset
        (by simpa [mem_ball,dist_zero_right] using hz) (show (0:ℂ)∈ball (0:ℂ) 1 by simp)
      rw [←Path.range_segment]
      exact mem_range_self s
    simpa [mem_ball,dist_zero_right] using hs
  have he := winding_moving_point p.toContinuousMap (by change p 0=p 1; simp)
    (Path.segment z 0).toContinuousMap (fun s => path_outside_avoids p hp (hw s))
  change winding _ (Path.segment z 0 0) _=winding _ (Path.segment z 0 1) _ at he
  simpa only [Path.source,Path.target] using he

lemma segment_diameter_im (t : I) : (Path.segment (-1:ℂ) 1 t).im=0 := by
  simp [Path.segment,AffineMap.lineMap_apply]

theorem winding_chord_replace (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (q : Path (-1:ℂ) 1) (hq : ∀ t, ‖q t‖=1)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn= -1) (hside : ∀ t, sgn*(q t).im≤0)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ hz : ((sgn*η:ℝ):ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ),
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap
        (((sgn*η:ℝ):ℂ)*Complex.I) hz =
      winding (q.trans γ).toContinuousMap 0 (by
        apply path_outside_avoids (q.trans γ) _ (by simp)
        intro t
        rw [Path.trans_apply]
        split_ifs
        · exact (hq _).ge
        · exact hγ _) := by
  let z : ℂ := ((sgn*η:ℝ):ℂ)*Complex.I
  have hnz : ‖z‖<1 := by
    rcases hsgn with rfl|rfl <;> simpa [z,norm_mul,Complex.norm_I,abs_of_pos hη] using hη₁
  have himz : sgn*z.im=η := by
    rcases hsgn with rfl|rfl <;> simp [z]
  have him (s t : I) : sgn*(blendPaths (Path.segment (-1:ℂ) 1) q (s,t)).im≤0 := by
    change sgn*(((1-(s:ℝ)) • Path.segment (-1:ℂ) 1 t+(s:ℝ) • q t).im)≤0
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,segment_diameter_im,mul_zero,zero_add]
    nlinarith [hside t,s.property.1]
  let H := (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ)
  have hzH : z∉range H := by
    rintro ⟨⟨s,t⟩,he⟩
    change (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ) (s,t)=z at he
    rw [Path.Homotopy.hcomp_apply] at he
    split_ifs at he with h
    · change blendPaths (Path.segment (-1:ℂ) 1) q (s,_) = z at he
      have hh := him s ⟨2*(t:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,h⟩⟩
      rw [he,himz] at hh
      exact hη.not_ge hh
    · exact path_outside_avoids γ hγ hnz ⟨_,he⟩
  have hp : z∉range ((Path.segment (-1:ℂ) 1).trans γ) := by
    rintro ⟨t,ht⟩
    exact hzH ⟨(0,t),by simpa [H] using ht⟩
  refine ⟨hp,?_⟩
  have he := winding_path_homotopy H z hzH
  change winding _ z hp=_
  rw [he]
  apply winding_outside_move (q.trans γ) _ hnz
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact (hq _).ge
  · exact hγ _

theorem chord_winding_jump (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ (hplus : (η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ))
      (hminus : -(η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ)),
    winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap ((η:ℂ)*Complex.I) hplus -
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap (-(η:ℂ)*Complex.I) hminus
      =2*Real.pi := by
  obtain ⟨hp,hp'⟩ := winding_chord_replace γ hγ lowerSemi lowerSemi_norm 1 (Or.inl rfl)
    (fun t => by simpa using lowerSemi_im t) η hη hη₁
  obtain ⟨hm,hm'⟩ := winding_chord_replace γ hγ upperSemi upperSemi_norm (-1) (Or.inr rfl)
    (fun t => by simpa using upperSemi_im t) η hη hη₁
  simp only [one_mul,neg_one_mul,Complex.ofReal_neg] at hp hm hp' hm'
  refine ⟨hp,hm,?_⟩
  have hγ₀ := path_outside_avoids γ hγ (z:=0) (by simp)
  have hl₀ := path_outside_avoids lowerSemi (fun t => (lowerSemi_norm t).ge) (z:=0) (by simp)
  have hu₀ := path_outside_avoids upperSemi (fun t => (upperSemi_norm t).ge) (z:=0) (by simp)
  rw [hp',hm',winding_path_trans lowerSemi γ 0 hl₀ hγ₀,
    winding_path_trans upperSemi γ 0 hu₀ hγ₀,winding_lowerSemi,winding_upperSemi]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval

lemma winding_on_component (f : C(I,ℂ)) (hf : f 0=f 1) {z w : ℂ}
    (hz : z∉range f) (hw : w∈connectedComponentIn (range f)ᶜ z) :
    winding f z hz=winding f w (connectedComponentIn_subset _ _ hw) := by
  let V : Set ℂ := (range f)ᶜ
  let z' : V := ⟨z,hz⟩
  let w' : V := ⟨w,connectedComponentIn_subset _ _ hw⟩
  have hwc : w'∈connectedComponent z' := by
    have hwi : w∈Subtype.val '' connectedComponent z' :=
      (connectedComponentIn_eq_image (F:=V) (x:=z) hz) ▸ hw
    obtain ⟨v,hv,hve⟩ := hwi
    have he : v=w' := Subtype.ext hve
    exact he ▸ hv
  exact (winding_locally_constant f hf).apply_eq_of_isPreconnected
    (s:=connectedComponent z') isPreconnected_connectedComponent
    (x:=z') (y:=w') (mem_connectedComponent (x:=z')) hwc

theorem chord_separates (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    -(η:ℂ)*Complex.I∉connectedComponentIn
      (range ((Path.segment (-1:ℂ) 1).trans γ))ᶜ ((η:ℂ)*Complex.I) := by
  obtain ⟨hp,hm,he⟩ := chord_winding_jump γ hγ η hη hη₁
  intro hh
  have hc : ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 0=
      ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 1 := by
    change ((Path.segment (-1:ℂ) 1).trans γ) 0=((Path.segment (-1:ℂ) 1).trans γ) 1
    simp
  have heq := winding_on_component _ hc hp hh
  rw [heq,sub_self] at he
  linarith [Real.pi_pos]
end CannonWinding

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Portion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma portion_range (a : Arc ℂ) {u v : I} (huv : u ≤ v) :
    range (a.portion u v)=a '' Icc u v := by
  rcases huv.eq_or_lt with he|hl
  · subst v
    simp [portion,Icc.convexComb_eq]
  · exact subarc_range_eq a hl

lemma pair_closing_path (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (u v : I) :
    ∃ γ : Path (a v) (a u), range γ=
      a '' Icc v 1 ∪ range b ∪ a '' Icc 0 u := by
  let p : Path (a 1) (a 0) := b.path.symm.cast hab₁ hab₀
  refine ⟨((a.portion v 1).trans p).trans (a.portion 0 u),?_⟩
  rw [Path.trans_range,Path.trans_range,portion_range a (unitInterval.le_one v),
    portion_range a (unitInterval.nonneg u)]
  have hp : range p=range b := Path.symm_range b.path
  rw [hp]

lemma isolated_chord_closer (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ∃ γ : Path (a v) (a u),
      range (Path.segment (a u) (a v))∪range γ=range a∪range b ∧
      ∀ t, ‖c‖ ≤ dist (γ t) x := by
  obtain ⟨γ,hγ⟩ := pair_closing_path a b hab₀ hab₁ u v
  have hball : ∀ z∈(range a∪range b)∩ball x ‖c‖,
      ∃ s∈Ioo u v, a s=z := by
    intro z hz
    obtain ⟨s,hs,hsz⟩ := hsmall hz
    have hsu : s≠u := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hu,mem_ball,dist_eq_norm] at hh
      have hd : x-c-x=-c := by abel
      rw [hd,norm_neg] at hh
      exact lt_irrefl _ hh
    have hsv : s≠v := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hv,mem_ball,dist_eq_norm,add_sub_cancel_left] at hh
      exact lt_irrefl _ hh
    exact ⟨s,⟨lt_of_le_of_ne hs.1 hsu.symm,lt_of_le_of_ne hs.2 hsv⟩,hsz⟩
  refine ⟨γ,?_,?_⟩
  · rw [Path.range_segment,hγ,←he]
    apply Subset.antisymm
    · exact union_subset (fun _ h => Or.inl (image_subset_range _ _ h))
        (union_subset (union_subset (fun _ h => Or.inl (image_subset_range _ _ h)) subset_union_right)
          (fun _ h => Or.inl (image_subset_range _ _ h)))
    · rintro z (⟨s,rfl⟩|hz)
      · rcases lt_trichotomy s u with hsu | rfl | hus
        · exact Or.inr (Or.inr ⟨s,⟨unitInterval.nonneg s,hsu.le⟩,rfl⟩)
        · exact Or.inl ⟨s,⟨le_rfl,huv.le⟩,rfl⟩
        · by_cases hvs : v < s
          · exact Or.inr (Or.inl (Or.inl ⟨s,⟨hvs.le,unitInterval.le_one s⟩,rfl⟩))
          · exact Or.inl ⟨s,⟨hus.le,le_of_not_gt hvs⟩,rfl⟩
      · exact Or.inr (Or.inl (Or.inr hz))
  · intro t
    apply le_of_not_gt
    intro ht
    have htγ := mem_range_self (f:=γ) t
    rw [hγ] at htγ
    have htK : γ t∈range a∪range b := by
      rcases htγ with ((⟨s,_,he'⟩|hh)|⟨s,_,he'⟩)
      · exact Or.inl ⟨s,he'⟩
      · exact Or.inr hh
      · exact Or.inl ⟨s,he'⟩
    obtain ⟨s,hs,hse⟩ := hball (γ t) ⟨htK,ht⟩
    rcases htγ with ((⟨r,hr,he'⟩|⟨r,he'⟩)|⟨r,hr,he'⟩)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.2.not_ge hr.1
    · have hh := (hc s r (hse.trans he'.symm)).1
      rcases hh with hh|hh
      · exact (not_lt_of_ge (show (0:I) ≤ u from u.2.1)) (hh ▸ hs.1)
      · exact (not_lt_of_ge (show v ≤ (1:I) from v.2.2)) (hh ▸ hs.2)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.1.not_ge hr.2
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma isolated_chord_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hc₀ : c≠0) (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨γ,hγK,hγ⟩ := isolated_chord_closer a b hab₀ hab₁ hc huv hu hv he hsmall
  let L : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-x)).trans
    (Homeomorph.mulRight₀ c⁻¹ (inv_ne_zero hc₀))
  have hL (z : ℂ) : L z=(z-x)/c := by rfl
  have hLu : L (a u)=-1 := by rw [hL,hu]; simp [sub_sub_cancel_left,hc₀]
  have hLv : L (a v)=1 := by rw [hL,hv]; simp [hc₀]
  let Γ : Path (1:ℂ) (-1) := (γ.map L.continuous).cast hLv.symm hLu.symm
  have hΓ (t : I) : 1 ≤ ‖Γ t‖ := by
    change 1 ≤ ‖L (γ t)‖
    rw [hL,norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr hc₀)).mpr
    simpa only [one_mul,dist_eq_norm] using hγ t
  let N : ℂ →ᵃ[ℝ] ℂ := {
    toFun := fun z => (z-x)/c
    linear := {
      toFun := fun z => z/c
      map_add' := fun z w => add_div z w c
      map_smul' := fun r z => by simp only [Complex.real_smul, RingHom.id_apply]; ring }
    map_vadd' := fun z w => by change (w+z-x)/c=w/c+(z-x)/c; ring }
  have hseg : L '' segment ℝ (a u) (a v)=segment ℝ (-1:ℂ) 1 := by
    change N '' segment ℝ (a u) (a v)=_
    rw [image_segment ℝ N]
    change segment ℝ (L (a u)) (L (a v))=_
    rw [hLu,hLv]
  have hΓR : range Γ=L '' range γ := by
    change range (L ∘ γ)=_
    exact range_comp L γ
  let f := (Path.segment (-1:ℂ) 1).trans Γ
  have hfR : range f=L '' (range a∪range b) := by
    rw [show f=(Path.segment (-1:ℂ) 1).trans Γ from rfl,Path.trans_range,
      Path.range_segment,←hseg,hΓR,←image_union,←Path.range_segment,hγK]
  intro hconn
  have hconn' : IsPreconnected (range f)ᶜ := by
    rw [hfR,←L.image_compl]
    exact hconn.image L L.continuous.continuousOn
  obtain ⟨hp,hm,_⟩ := CannonWinding.chord_winding_jump Γ hΓ (1/2)
    (by norm_num) (by norm_num)
  exact CannonWinding.chord_separates Γ hΓ (1/2) (by norm_num) (by norm_num)
    (hconn'.subset_connectedComponentIn hp subset_rfl hm)

theorem pair_complement_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨u,v,x,c,huv,hc₀,hu,hv,he,hs⟩ := pair_isolated_chord a b hab₀ hab₁ hc Q ha
  exact isolated_chord_not_preconnected a b hab₀ hab₁ hc huv hc₀ hu hv he hs
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ labels : Bool ≃ ConnectedComponents ((range a ∪ range b)ᶜ : Set ℂ),
      ∀ x∈range a ∪ range b,
        incident _ ConnectedComponents.mk x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hls,hl⟩ := pair_labels_surjective a b hab₀ hab₁ hc Q ha hb
    (π:=ConnectedComponents.mk) ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  have hne : l false ≠ l true := by
    intro he
    have hconst (s t : Bool) : l s=l t := by
      cases s <;> cases t
      · rfl
      · exact he
      · exact he.symm
      · rfl
    have hsub (d e : ConnectedComponents (Kᶜ : Set ℂ)) : d=e := by
      obtain ⟨s,rfl⟩ := hls d
      obtain ⟨t,rfl⟩ := hls e
      exact hconst s t
    have hconn : PreconnectedSpace (Kᶜ : Set ℂ) := by
      rw [preconnectedSpace_iff_connectedComponent]
      intro x
      apply eq_univ_of_forall
      intro y
      exact ConnectedComponents.coe_eq_coe'.mp (hsub _ _)
    exact pair_complement_not_preconnected a b hab₀ hab₁ hc Q ha
      (isPreconnected_iff_preconnectedSpace.mpr hconn)
  have hli : Function.Injective l := by
    intro s t h
    cases s <;> cases t
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  exact ⟨Equiv.ofBijective l ⟨hli,hls⟩,hl⟩
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameInitialInterval
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

lemma tame_initial_interval (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) :
    ∃ q : I, 0<q ∧ a '' Icc 0 q=segment ℝ (a 0) (a q) := by
  classical
  obtain ⟨P,h₀,h₁,hP⟩ := finite_segment_arc_subdivision Q a ha
  let R := P.filter (0<·)
  have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,zero_lt_one⟩⟩
  let q := R.min' hR
  have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have hcon : Consecutive P 0 q := by
    refine ⟨h₀,hq.1,hq.2,?_⟩
    intro z hz hz₀ hzq
    exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,hz₀⟩))
  have hh := hP ⟨(0,q),(mem_segments P 0 q).mpr hcon⟩
  rw [subdivArc_range_eq] at hh
  exact ⟨q,hq.2,hh⟩

theorem tame_tip_chart (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0∈W ∧ H (0,0)=a 0 ∧
      ∀ z∈W, (z∈range a ↔ z∈H '' positiveHalfAxis) := by
  obtain ⟨q,hq,hseg⟩ := tame_initial_interval a Q ha
  let u := a q-a 0
  have hu : u≠0 := sub_ne_zero.mpr (a.injective.ne hq.ne')
  obtain ⟨H,hH₀,hH⟩ := straight_ray_chart (a 0) u hu
  let T := a '' Ici q
  have hT : IsClosed T := (isClosed_Ici.isCompact.image a.continuous).isClosed
  have hxT : a 0∉T := by
    rintro ⟨s,hs,he⟩
    have he' := a.injective he
    subst s
    exact hq.not_ge hs
  refine ⟨H,Tᶜ∩ball (a 0) ‖u‖,hT.isOpen_compl.inter isOpen_ball,
    ⟨hxT,mem_ball_self (norm_pos_iff.mpr hu)⟩,hH₀,?_⟩
  intro z hz
  rw [hH]
  change (z∈range a ↔ ∃ s : ℝ, 0 ≤ s ∧ z=a 0+s•u)
  rw [local_ray_segment le_rfl hz.2]
  have he : a 0+u=a q := by dsimp [u]; abel
  rw [he,←hseg]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hs => hz.1 ⟨s,hs,rfl⟩)⟩,rfl⟩
  · intro hz
    exact image_subset_range _ _ hz

theorem tame_tip_connected_neighborhood (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) {U : Set ℂ} (hU : IsOpen U) (hxU : a 0∈U) :
    ∃ W : Set ℂ, IsOpen W ∧ a 0∈W ∧ W⊆U ∧ IsConnected (W\range a) := by
  obtain ⟨H,W,hW,hxW,h₀,hflat⟩ := tame_tip_chart a Q ha
  have h₀WU : H (0,0)∈W∩U := h₀.symm ▸ ⟨hxW,hxU⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (((hW.inter hU).preimage H.continuous).mem_nhds h₀WU)
  let C := CannonFaceIncidence.openBox r
  let W' := H '' C
  have hsub : C⊆H ⁻¹' (W∩U) := by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact hball
  have hW'U : W'⊆W∩U := by rintro _ ⟨p,hp,rfl⟩; exact hsub hp
  refine ⟨W',H.isOpenMap C (by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact isOpen_ball),
    ⟨(0,0),by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact mem_ball_self hr,h₀⟩,
    fun z hz => (hW'U hz).2,?_⟩
  have he : W'\range a=H '' (C\positiveHalfAxis) := by
    ext z
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpA⟩
      refine ⟨p,⟨hp,?_⟩,rfl⟩
      intro hpR
      exact hpA ((hflat (H p) (hsub hp).1).mpr ⟨p,hpR,rfl⟩)
    · rintro ⟨p,⟨hp,hpR⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      intro hpA
      obtain ⟨q,hq,heq⟩ := (hflat (H p) (hsub hp).1).mp hpA
      exact hpR (H.injective heq ▸ hq)
  rw [he]
  exact (slit_box_connected hr).image H H.continuous.continuousOn
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RadialStable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polyJoined_of_preconnected_finite_segments (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) :
    PolyJoined (⋃ q∈Q,segment ℝ q.1 q.2) x y := by
  classical
  let K := ⋃ q∈Q,segment ℝ q.1 q.2
  let V := ⋃ q∈Q.filter (fun q => PolyJoined K x q.1),segment ℝ q.1 q.2
  let W := ⋃ q∈Q.filter (fun q => ¬PolyJoined K x q.1),segment ℝ q.1 q.2
  have hseg (q : E×E) (hq : q∈Q) : segment ℝ q.1 q.2⊆K :=
    subset_iUnion₂_of_subset q hq Subset.rfl
  have hreach (q : E×E) (hq : q∈Q) {z : E} (hz : z∈segment ℝ q.1 q.2) :
      PolyJoined K x z ↔ PolyJoined K x q.1 := by
    constructor
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset hz (left_mem_segment ..)).trans (hseg q hq))
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset (left_mem_segment ..) hz).trans (hseg q hq))
  have hV (z : E) : z∈V ↔ z∈K ∧ PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,(hreach q hq hzq).mpr hqr⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,(hreach q hq hzq).mp hr⟩,hzq⟩
  have hW (z : E) : z∈W ↔ z∈K ∧ ¬PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,fun h => hqr ((hreach q hq hzq).mp h)⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,fun h => hr ((hreach q hq hzq).mpr h)⟩,hzq⟩
  have hcV : IsClosed V := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  have hcW : IsClosed W := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  by_contra hn
  have hcover : K⊆V∪W := by
    intro z hz
    by_cases hr : PolyJoined K x z
    · exact Or.inl ((hV z).mpr ⟨hz,hr⟩)
    · exact Or.inr ((hW z).mpr ⟨hz,hr⟩)
  obtain ⟨z,hzK,hzV,hzW⟩ := isPreconnected_closed_iff.mp hK V W hcV hcW hcover
    ⟨x,hx,(hV x).mpr ⟨hx,.refl⟩⟩ ⟨y,hy,(hW y).mpr ⟨hy,hn⟩⟩
  exact ((hW z).mp hzW).2 ((hV z).mp hzV).2

theorem preconnected_finite_segments_arc (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) (hne : x≠y) :
    ∃ a : CannonEmbeddedArc.Arc E, a 0=x ∧ a 1=y ∧
      range a⊆⋃ q∈Q,segment ℝ q.1 q.2 ∧ FiniteSupport (range a) :=
  polyJoined_arc (polyJoined_of_preconnected_finite_segments Q hK hx hy) hne
end CannonPolygonal

namespace CannonSegmentCones
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma radial_dist (x y : E) {t : ℝ} (ht : 0 ≤ t) :
    dist (x+t • (y-x)) x=t*dist y x := by
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]

lemma radial_mem_ball {x y : E} {ε t : ℝ} (hy : dist y x < ε)
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) : dist (x+t • (y-x)) x < ε := by
  rw [radial_dist x y ht]
  exact (mul_le_of_le_one_left dist_nonneg ht₁).trans_lt hy

lemma segment_split {a b x : E} (hx : x ∈ segment ℝ a b) :
    segment ℝ a b=segment ℝ x a ∪ segment ℝ x b := by
  apply Subset.antisymm
  · intro z hz
    by_cases hza : z=a
    · exact Or.inl (hza ▸ right_mem_segment ℝ x a)
    by_cases hzb : z=b
    · exact Or.inr (hzb ▸ right_mem_segment ℝ x b)
    have hzo := mem_openSegment_of_ne_left_right (Ne.symm hza) (Ne.symm hzb) hz
    have hxr : x ∈ range (AffineMap.lineMap a b : ℝ → E) := by
      rw [segment_eq_image_lineMap] at hx
      exact image_subset_range _ _ hx
    rcases openSegment_subset_union a b hxr hzo with he|ha|hb
    · exact Or.inl (he ▸ left_mem_segment ℝ x a)
    · exact Or.inl (segment_symm ℝ a x ▸ openSegment_subset_segment ℝ _ _ ha)
    · exact Or.inr (openSegment_subset_segment ℝ _ _ hb)
  · exact union_subset
      ((convex_segment (𝕜:=ℝ) a b).segment_subset hx (left_mem_segment ℝ a b))
      ((convex_segment (𝕜:=ℝ) a b).segment_subset hx (right_mem_segment ℝ a b))

lemma anchored_radial_stable (x a : E) :
    ∃ ε>0, RadialStable (segment ℝ x a) x ε := by
  by_cases ha : a=x
  · subst a
    refine ⟨1,zero_lt_one,?_⟩
    intro y hy t ht ht₁
    simp only [segment_same,mem_singleton_iff,add_eq_left]
    rw [smul_eq_zero]
    simp [ht.ne',sub_eq_zero]
  · refine ⟨‖a-x‖,norm_pos_iff.mpr (sub_ne_zero.mpr ha),?_⟩
    intro y hy t ht ht₁
    constructor
    · intro hz
      rw [segment_eq_image'] at hz ⊢
      obtain ⟨s,hs,he⟩ := hz
      have he' : s • (a-x)=t • (y-x) := by
        simpa only [add_right_inj] using he
      have hv : y-x=(s/t) • (a-x) := by
        calc
          y-x=t⁻¹ • (t • (y-x)) := by simp [smul_smul,ht.ne']
          _=t⁻¹ • (s • (a-x)) := by rw [he']
          _=(s/t) • (a-x) := by rw [smul_smul,div_eq_inv_mul]
      have hst₀ : 0 ≤ s/t := div_nonneg hs.1 ht.le
      have hst₁ : s/t ≤ 1 := by
        have hn := congrArg norm hv
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hst₀] at hn
        rw [dist_eq_norm] at hy
        have han : 0 < ‖a-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
        nlinarith
      refine ⟨s/t,⟨hst₀,hst₁⟩,?_⟩
      change x+(s/t) • (a-x)=y
      rw [←hv,add_sub_cancel]
    · intro hyseg
      have hz := (convex_segment (𝕜:=ℝ) x a) (left_mem_segment ℝ x a) hyseg
        (sub_nonneg.mpr ht₁) ht.le (sub_add_cancel 1 t)
      convert hz using 1; module

lemma RadialStable.mono_radius {K : Set E} {x : E} {ε δ : ℝ}
    (h : RadialStable K x ε) (hδε : δ ≤ ε) : RadialStable K x δ :=
  fun y hy t ht ht₁ => h y (hy.trans_le hδε) t ht ht₁

lemma RadialStable.union {K L : Set E} {x : E} {ε δ : ℝ}
    (hK : RadialStable K x ε) (hL : RadialStable L x δ) :
    RadialStable (K∪L) x (min ε δ) := by
  intro y hy t ht ht₁
  simp only [mem_union]
  rw [hK y (hy.trans_le (min_le_left _ _)) t ht ht₁,
    hL y (hy.trans_le (min_le_right _ _)) t ht ht₁]

lemma segment_closed (a b : E) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))).isClosed

lemma segment_radial_stable (a b x : E) :
    ∃ ε>0, RadialStable (segment ℝ a b) x ε := by
  by_cases hx : x∈segment ℝ a b
  · obtain ⟨ε,hε,hεK⟩ := anchored_radial_stable x a
    obtain ⟨δ,hδ,hδK⟩ := anchored_radial_stable x b
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    rw [segment_split hx]
    exact hεK.union hδK
  · obtain ⟨ε,hε,hεK⟩ := Metric.isOpen_iff.mp (segment_closed a b).isOpen_compl x hx
    refine ⟨ε,hε,?_⟩
    intro y hy t ht ht₁
    have hyK := hεK hy
    have hzK := hεK (radial_mem_ball hy ht.le ht₁)
    exact iff_of_false hzK hyK

theorem finite_segments_radial_stable (Q : Finset (E×E)) (x : E) :
    ∃ ε>0, RadialStable (⋃ q∈Q,segment ℝ q.1 q.2) x ε := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp [RadialStable]⟩
  | @insert q Q hq ih =>
    obtain ⟨ε,hε,hεK⟩ := segment_radial_stable q.1 q.2 x
    obtain ⟨δ,hδ,hδK⟩ := ih
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hεK.union hδK

theorem component_radial_access (Q : Finset (E×E)) {x a : E}
    (hxK : x ∈ ⋃ q∈Q,segment ℝ q.1 q.2)
    (hx : x∈closure (connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ a)) :
    ∃ y : E, y≠x ∧ ∀ t : ℝ, 0<t → t≤1 →
      x+t • (y-x)∈connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ a := by
  let K : Set E := ⋃ q∈Q,segment ℝ q.1 q.2
  obtain ⟨ε,hε,hstable⟩ := finite_segments_radial_stable Q x
  obtain ⟨y,hyball,hy⟩ := (mem_closure_iff_nhds.mp hx)
    (Metric.ball x ε) (Metric.ball_mem_nhds x hε)
  have hyK : y∉K := connectedComponentIn_subset _ _ hy
  have hyx : y≠x := fun h => hyK (h ▸ hxK)
  let S : Set E := (fun t : ℝ => x+t • (y-x)) '' Ioc 0 1
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hyS : y∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSK : S⊆Kᶜ := by
    rintro z ⟨t,ht,rfl⟩ hz
    exact hyK ((hstable y hyball t ht.1 ht.2).mp hz)
  have hsub := hS.subset_connectedComponentIn hyS hSK
  rw [←connectedComponentIn_eq hy] at hsub
  refine ⟨y,hyx,fun t ht ht₁ => hsub ⟨t,⟨ht,ht₁⟩,rfl⟩⟩

end CannonSegmentCones
namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Finite ι]

theorem finite_graph_exact_segments (F : ι → Arc E)
    (Q : Finset (E×E)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2) :
    ∃ P : Finset (E×E), (⋃ i,range (F i))=⋃ p∈P,segment ℝ p.1 p.2 := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP₀ hP₁ hPs using fun i => finite_segment_arc_subdivision Q (F i) (hQ i)
  let R : Finset (E×E) := Finset.univ.biUnion fun i =>
    (segments (P i)).image (fun z => (F i z.1,F i z.2))
  refine ⟨R,?_⟩
  have he (i : ι) : range (F i)=⋃ z : segments (P i),
      segment ℝ (F i z.val.1) (F i z.val.2) := by
    rw [subdivision_cover (F i) (P i) (hP₀ i) (hP₁ i)]
    exact iUnion_congr fun z => hPs i z
  simp only [he]
  ext x
  constructor
  · intro hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hxi
    apply mem_iUnion₂.mpr
    refine ⟨(F i z.val.1,F i z.val.2),?_,hz⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
      Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩⟩
  · intro hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨z,hz⟩,hxp⟩⟩

lemma halfopen_radial_segment {U : Set E} {x y : E}
    (h : ∀ t : ℝ, 0<t → t≤1 → x+t • (y-x)∈U) :
    segment ℝ x y⊆insert x U := by
  rw [segment_eq_image']
  rintro z ⟨t,ht,rfl⟩
  rcases eq_or_lt_of_le ht.1 with he|he
  · simp [←he]
  · exact Or.inr (h t he ht.2)

end CannonEmbeddedArc.Arc
namespace CannonSegmentCones
open Set Metric Topology

lemma complex_segment_supporting_line (a b : ℂ) :
    ∃ f : ℂ →L[ℝ] ℝ, f≠0 ∧ segment ℝ a b⊆{x | f x=f a} := by
  let x₀ := Complex.reCLM
  let x₁ := Complex.imCLM
  by_cases hd : b.re=a.re
  · refine ⟨x₀,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f 1) h
      norm_num [x₀] at hh
    · exact ((convex_singleton (x₀ a)).linear_preimage x₀.toLinearMap).segment_subset rfl hd
  · let f := x₁-((b.im-a.im)/(b.re-a.re)) • x₀
    refine ⟨f,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f Complex.I) h
      norm_num [f,x₀,x₁] at hh
    · have hab : f b=f a := by
        change b.im-((b.im-a.im)/(b.re-a.re))*b.re=a.im-((b.im-a.im)/(b.re-a.re))*a.re
        have hn := sub_ne_zero.mpr hd
        field_simp [hn]
        ring
      exact ((convex_singleton (f a)).linear_preimage f.toLinearMap).segment_subset rfl hab

lemma complex_finite_segments_compl_dense (Q : Finset (ℂ × ℂ)) :
    Dense ((⋃ q∈Q,segment ℝ q.1 q.2)ᶜ : Set ℂ) := by
  classical
  choose f hf hfs using fun q : Q => complex_segment_supporting_line q.val.1 q.val.2
  have hsurj (q : Q) : Function.Surjective (f q) := by
    obtain ⟨v,hv⟩ : ∃ v, f q v≠0 := by
      by_contra hn
      push Not at hn
      apply hf q
      ext v
      exact hn v
    intro y
    refine ⟨(y/f q v) • v,?_⟩
    simp only [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ y hv
  have hopen (q : Q) : IsOpen {x | f q x≠f q q.val.1} :=
    isOpen_compl_singleton.preimage (f q).continuous
  have hdense (q : Q) : Dense {x | f q x≠f q q.val.1} :=
    (dense_compl_singleton _).preimage ((f q).isOpenMap (hsurj q))
  have hd := dense_iInter_of_isOpen hopen hdense
  apply hd.mono
  intro z hz hzQ
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzQ
  exact (mem_iInter.mp hz ⟨q,hq⟩) (hfs ⟨q,hq⟩ hzq)

end CannonSegmentCones

namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_between_accessible_points {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y a b : E} (hxy : x≠y)
    (hax : ∀ t : ℝ, 0<t → t≤1 → x+t • (a-x)∈U)
    (hby : ∀ t : ℝ, 0<t → t≤1 → y+t • (b-y)∈U) :
    ∃ c : Arc E, c 0=x ∧ c 1=y ∧ (∀ t : I, t≠0 → t≠1 → c t∈U) ∧
      FiniteSupport (range c) := by
  let V := insert x (insert y U)
  have ha : a∈U := by simpa using hax 1 zero_lt_one le_rfl
  have hb : b∈U := by simpa using hby 1 zero_lt_one le_rfl
  have hUV : U⊆V := (subset_insert y U).trans (subset_insert x _)
  have hxa : PolyJoined V x a := Relation.ReflTransGen.single
    ((halfopen_radial_segment hax).trans (insert_subset (mem_insert _ _) hUV))
  have hab : PolyJoined V a b := Relation.ReflTransGen.mono
    (r:=fun a b => segment ℝ a b⊆U) (p:=fun a b => segment ℝ a b⊆V)
    (fun _ _ h => h.trans hUV) a b (polyJoined_of_open_preconnected hU hc ha hb)
  have hby' : PolyJoined V b y := Relation.ReflTransGen.single (by
    rw [segment_symm]
    exact (halfopen_radial_segment hby).trans (insert_subset (by simp [V]) hUV))
  obtain ⟨c,hc₀,hc₁,hcV,hcS⟩ := polyJoined_arc (hxa.trans (hab.trans hby')) hxy
  refine ⟨c,hc₀,hc₁,?_,hcS⟩
  intro t ht₀ ht₁
  rcases hcV (mem_range_self t) with h|h|h
  · exact (ht₀ (c.injective (h.trans hc₀.symm))).elim
  · exact (ht₁ (c.injective (h.trans hc₁.symm))).elim
  · exact h

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RegionEdges
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarNeighborhood

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma interior_dense_interval : closure (Ioo (0:I) 1)=univ := by
  rw [closure_Ioo zero_ne_one]
  ext t
  simp only [mem_Icc,mem_univ,iff_true]
  exact ⟨t.property.1,t.property.2⟩

lemma range_in_closed_of_interior {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} (hS : IsClosed S) (hI : ∀ t : I, 0<t → t<1 → a t∈S) : range a⊆S := by
  have hs : closure (Ioo (0:I) 1)⊆a ⁻¹' S :=
    closure_minimal (fun t ht => hI t ht.1 ht.2) (hS.preimage a.continuous)
  rw [interior_dense_interval] at hs
  rintro x ⟨t,rfl⟩
  exact hs (mem_univ t)

omit [Finite ι] in
lemma graph_no_isolated (F : ι → Arc ℂ) {x : ℂ} (hx : x∈⋃ i, range (F i))
    {U : Set ℂ} (hU : IsOpen U) (hxU : x∈U) :
    ∃ y∈⋃ i, range (F i), y∈U ∧ y≠x := by
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hx
  obtain ⟨s,hst,hsU⟩ := (dense_compl_singleton t).exists_mem_open
    ((F i).continuous.isOpen_preimage U hU) ⟨t,hxU⟩
  exact ⟨F i s,mem_iUnion.mpr ⟨i,mem_range_self s⟩,hsU,
    fun h => hst (mem_singleton_iff.mpr ((F i).injective h))⟩

lemma region_edge_in_closure (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    {d : D} {i : ι} (hi : i∈regionEdges F π d) :
    range (F i)⊆closure (region _ π d) := by
  obtain ⟨s,hs₀,hs₁,hds⟩ := hi
  obtain ⟨labels,hlabels⟩ := tame_edge_incident_labels F hF Q hQ hπ i
  apply range_in_closed_of_interior (F i) isClosed_closure
  intro t ht₀ ht₁
  show d∈incident _ π (F i t)
  rwa [hlabels t ht₀ ht₁,←hlabels s hs₀ hs₁]

theorem tame_region_closure (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π) (d : D) :
    closure (region _ π d)=region _ π d∪⋃ i∈regionEdges F π d,range (F i) := by
  let K : Set ℂ := ⋃ i,range (F i)
  let R := region Kᶜ π d
  let S : Set ℂ := ⋃ i∈regionEdges F π d,range (F i)
  let T : Set ℂ := {x | Vertex F x}
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed)
  have hR : IsOpen R := region_isOpen hK.isOpen_compl hπ d
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun i =>
    isClosed_iUnion_of_finite (fun _ => (F i).compact_range.isClosed))
  have hT : T.Finite := finite_vertex_set F
  have hnonvert : ∀ x∈closure R, x∉R → x∉T → x∈S := by
    intro x hx hxR hxT
    have hxK : x∈K := by
      by_contra hn
      exact hxR (closure_region_inside hK.isOpen_compl hπ hx hn)
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
    have ht₀ : t≠0 := fun he => hxT ⟨i,Or.inl (congrArg (F i) he.symm)⟩
    have ht₁ : t≠1 := fun he => hxT ⟨i,Or.inr (congrArg (F i) he.symm)⟩
    exact mem_iUnion₂.mpr ⟨i,⟨t,lt_of_le_of_ne t.property.1 ht₀.symm,
      lt_of_le_of_ne t.property.2 ht₁,hx⟩,mem_range_self t⟩
  apply Subset.antisymm
  · intro x hx
    by_cases hxR : x∈R
    · exact Or.inl hxR
    right
    by_contra hxS
    have hxK : x∈K := by
      by_contra hn
      exact hxR (closure_region_inside hK.isOpen_compl hπ hx hn)
    let W := (S∪(T\{x}))ᶜ
    have hW : IsOpen W := (hS.union hT.sdiff.isClosed).isOpen_compl
    have hxW : x∈W := by
      rintro (h|h)
      · exact hxS h
      · exact h.2 rfl
    obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW x hxW
    have hall : ball x r\{x}⊆R := by
      apply isolated_frontier_forces_punctured_ball hR hr hx hxR
      rintro y ⟨hy,hyB,hyx⟩
      by_contra hyR
      have hyW := hrW hyB
      by_cases hyT : y∈T
      · exact hyW (Or.inr ⟨hyT,hyx⟩)
      · exact hyW (Or.inl (hnonvert y hy hyR hyT))
    obtain ⟨y,hyK,hyB,hyx⟩ := graph_no_isolated F hxK isOpen_ball (mem_ball_self hr)
    exact (region_subset Kᶜ π d (hall ⟨hyB,hyx⟩)) hyK
  · rintro x (hx|hx)
    · exact subset_closure hx
    · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
      exact region_edge_in_closure F hF Q hQ hπ hi hxi
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameEdgeIncidenceOpen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma FiniteSupport.iUnion {ι : Type*} [Finite ι] {S : ι → Set E}
    (hS : ∀ i, FiniteSupport (S i)) : FiniteSupport (⋃ i,S i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP using hS
  refine ⟨Finset.univ.biUnion P,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hP i hi)
  exact mem_iUnion₂.mpr ⟨p,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩,hxp⟩
end CannonPolygonal

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

lemma finite_segment_union (P Q : Finset (ℂ × ℂ)) :
    (⋃ p∈P∪Q,segment ℝ p.1 p.2)=(⋃ p∈P,segment ℝ p.1 p.2)∪(⋃ p∈Q,segment ℝ p.1 p.2) := by
  ext x
  simp only [mem_iUnion,Finset.mem_union,mem_union]
  constructor
  · rintro ⟨p,hp,hx⟩
    exact hp.elim (fun h => Or.inl ⟨p,h,hx⟩) (fun h => Or.inr ⟨p,h,hx⟩)
  · rintro (⟨p,hp,hx⟩|⟨p,hp,hx⟩)
    · exact ⟨p,Or.inl hp,hx⟩
    · exact ⟨p,Or.inr hp,hx⟩

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {X : Type*} [TopologicalSpace X] [T2Space X]
theorem isolate_edge_interior_weak {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (i : ι) {p t q : I} (hpt : p<t) (htq : t<q) :
    ∃ W : Set X, IsOpen W ∧ F i t∈W ∧
      ∀ z∈W, (z∈⋃ j, range (F j) ↔ z∈F i '' Icc p q) := by
  classical
  let A : Set X := ⋃ j : {j // j≠i}, range (F j.val)
  let B : Set X := F i '' (Iic p∪Ici q)
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun j => (F j.val).compact_range.isClosed)
  have hB : IsClosed B :=
    ((isClosed_Iic.union isClosed_Ici).isCompact.image (F i).continuous).isClosed
  let W := (A∪B)ᶜ
  have ht₀ : t≠0 := ne_of_gt ((unitInterval.nonneg p).trans_lt hpt)
  have ht₁ : t≠1 := ne_of_lt (htq.trans_le (unitInterval.le_one q))
  have htA : F i t∉A := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    obtain ⟨s,hs⟩ := hj
    have hh := (hF j.property.symm) t s hs.symm
    exact hh.1.elim ht₀ ht₁
  have htB : F i t∉B := by
    rintro ⟨s,hs,hst⟩
    have he := (F i).injective hst
    subst s
    exact hs.elim hpt.not_ge htq.not_ge
  refine ⟨W,(hA.union hB).isOpen_compl,fun h => h.elim htA htB,?_⟩
  intro z hz
  constructor
  · intro hzF
    obtain ⟨j,s,hs⟩ := mem_iUnion.mp hzF
    by_cases hji : j=i
    · subst j
      refine ⟨s,?_,hs⟩
      have hsB : s∉Iic p∪Ici q := fun hsB => hz (Or.inr ⟨s,hsB,hs⟩)
      constructor
      · exact (lt_of_not_ge (fun h => hsB (Or.inl h))).le
      · exact (lt_of_not_ge (fun h => hsB (Or.inr h))).le
    · exact (hz (Or.inl (mem_iUnion.mpr ⟨⟨j,hji⟩,⟨s,hs⟩⟩))).elim
  · rintro ⟨s,_,rfl⟩
    exact mem_iUnion.mpr ⟨i,mem_range_self s⟩
end CannonEmbeddedArc.Arc
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

theorem tame_graph_flat_chart_weak {ι : Type*} [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ F i t∈W ∧
      H (0,0)=F i t ∧ ∀ z∈W,
        (z∈⋃ j, range (F j) ↔ z∈H '' horizontal) := by
  obtain ⟨p,q,hpt,htq,hleft,hright,hcorner⟩ := tame_interior_corner Q (F i) (hQ i) ht₀ ht₁
  obtain ⟨W,hW,htW,hiso⟩ := isolate_edge_interior_weak F hF i hpt htq
  let x := F i t
  let u := F i p-x
  let v := F i q-x
  have hu : u≠0 := sub_ne_zero.mpr ((F i).injective.ne hpt.ne)
  have hv : v≠0 := sub_ne_zero.mpr ((F i).injective.ne htq.ne.symm)
  let r := min ‖u‖ ‖v‖
  have hr : 0 < r := lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  obtain ⟨H₀,hH₀,hHr⟩ := straighten_corner hcorner
  let H := H₀.trans (Homeomorph.addLeft x)
  refine ⟨H,W∩ball x r,hW.inter isOpen_ball,⟨htW,mem_ball_self hr⟩,?_,?_⟩
  · simp [H,hH₀,x]
  · intro z hz
    rw [hiso z hz.1]
    have he : Icc p q=Icc p t∪Icc t q := by
      ext s
      constructor
      · intro hs
        rcases le_total s t with hst|hts
        · exact Or.inl ⟨hs.1,hst⟩
        · exact Or.inr ⟨hts,hs.2⟩
      · rintro (hs|hs)
        · exact ⟨hs.1,hs.2.trans htq.le⟩
        · exact ⟨hpt.le.trans hs.1,hs.2⟩
    rw [he,image_union,hleft,hright]
    have hHimage : H '' horizontal=(fun w : ℂ => x+w) '' (ray u∪ray v) := by
      change ((fun w : ℂ => x+w) ∘ H₀) '' horizontal=_
      rw [image_comp,hHr]
    rw [hHimage,image_union,mem_union,mem_union]
    have hxU : x+u=F i p := by dsimp [u,x]; abel
    have hxV : x+v=F i q := by dsimp [v,x]; abel
    have hmem (w : ℂ) : z∈(fun b : ℂ => x+b) '' ray w ↔
        ∃ s : ℝ, 0 ≤ s ∧ z = x+s•w := by
      constructor
      · rintro ⟨b,⟨s,hs,hb⟩,hbe⟩
        exact ⟨s,hs,by rw [hb] at hbe; exact hbe.symm⟩
      · rintro ⟨s,hs,rfl⟩
        exact ⟨s•w,⟨s,hs,rfl⟩,rfl⟩
    rw [hmem u,hmem v,local_ray_segment (min_le_left _ _) hz.2,
      local_ray_segment (min_le_right _ _) hz.2,hxU,hxV]
    rw [segment_symm (𝕜:=ℝ) (x:=F i p) (y:=x)]
end CannonEmbeddedArc.Arc
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_in_open_weak (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ W : Set ℂ, IsOpen W ∧ F i t∈W ∧ ∃ l : Bool → D,
      ∀ x∈W∩(⋃ j,range (F j)), incident (U\(⋃ j,range (F j))) π x=range l := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart_weak F hF Q hQ i ht₀ ht₁
  have htU : F i t∈U := hiU ⟨t,⟨ht₀,ht₁⟩,rfl⟩
  have hf : ∀ z∈W∩U, z∈U\(⋃ j,range (F j)) ↔ (H.symm z).2≠0 := by
    intro z hz
    have he : z∈(⋃ j,range (F j)) ↔ (H.symm z).2=0 := by
      rw [hflat z hz.1,H.image_eq_preimage_symm]
      rfl
    simp only [mem_sdiff,hz.2,true_and,he]
  obtain ⟨W',hW',h₀W',_,l,hl⟩ := flat_chart_incidence hπ H (hW.inter hU)
    (h₀.symm ▸ ⟨htW,htU⟩) hf
  exact ⟨W',hW',h₀ ▸ h₀W',l,fun x hx => hl x ⟨hx.1,fun h => h.2 hx.2⟩⟩

theorem tame_edge_labels_in_open_weak (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) :
    ∃ l : Bool → D, ∀ t : I, 0<t → t<1 →
      incident (U\(⋃ j,range (F j))) π (F i t)=range l := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A := isPreconnected_Ioo.image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ W : Set ℂ, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨W,hW,htW,l,hl⟩ := tame_edge_incidence_in_open_weak F hF Q hQ hU hπ i hiU ht.1 ht.2
    refine ⟨W,hW,htW,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyW⟩
    exact (hl y ⟨hyW,mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩⟩).trans
      (hl (F i t) ⟨htW,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; norm_num
  obtain ⟨W,hW,hmW,l,hl⟩ := tame_edge_incidence_in_open_weak F hF Q hQ hU hπ i hiU hm.1 hm.2
  refine ⟨l,fun t ht₀ ht₁ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₀,ht₁⟩,rfl⟩
    (F i m) ⟨m,hm,rfl⟩).trans (hl (F i m) ⟨hmW,mem_iUnion.mpr ⟨i,mem_range_self m⟩⟩)

theorem tame_star_center_incident_weak [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (x : ℂ) (hx : x∈U) (h₀ : ∀ i, F i 0=x) (h₁ : ∀ i, F i 1∉U)
    (hFU : ∀ i, F i '' Ioo (0:I) 1⊆U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region (U\(⋃ j,range (F j))) π d).Nonempty) :
    d∈incident (U\(⋃ j,range (F j))) π x := by
  let K := ⋃ j,range (F j)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  have hxK : x∈K := by obtain ⟨i⟩ := ‹Nonempty ι›; exact mem_iUnion.mpr ⟨i,⟨0,h₀ i⟩⟩
  have hne : (U\(U\K)).Nonempty := ⟨x,hx,fun hxV => hxV.2 hxK⟩
  obtain ⟨y,⟨hyU,hyV⟩,hyd⟩ := region_boundary_hits_in_open
    hU (hU.sdiff hK) sdiff_subset hconn hne hπ d hd
  by_cases hyx : y=x
  · subst y
    exact hyd
  have hyK : y∈K := by by_contra hn; exact hyV ⟨hyU,hn⟩
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hyK
  have ht₀ : t≠0 := fun ht => hyx (ht ▸ h₀ i)
  have ht₁ : t≠1 := fun h => h₁ i (h ▸ hyU)
  obtain ⟨l,hl⟩ := tame_edge_labels_in_open_weak F hF Q hQ hU hπ i (hFU i)
  have hdR : d∈range l := by
    rw [←hl t (lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) ht₀.symm)
      (lt_of_le_of_ne (le_one t) ht₁)]
    exact hyd
  have hclosed : IsClosed ((F i) ⁻¹' closure (region (U\K) π d)) :=
    isClosed_closure.preimage (F i).continuous
  have hs : Ioo (0:I) 1⊆(F i) ⁻¹' closure (region (U\K) π d) := by
    intro t ht
    show d∈incident (U\K) π (F i t)
    rw [hl t ht.1 ht.2]
    exact hdR
  have hz : (0:I)∈closure (Ioo (0:I) 1) := by
    rw [closure_Ioo (by exact zero_ne_one)]
    exact ⟨le_rfl,zero_le_one⟩
  have he := closure_minimal hs hclosed hz
  change x∈closure (region (U\K) π d)
  simpa only [mem_preimage,h₀ i] using he
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem arc_with_terminal_germ {U C : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y w z : ℂ} (hxy : x≠y) (hy : y∉U)
    (hax : ∀ t : ℝ, 0<t → t≤1 → x+t • (w-x)∈U)
    (hby : ∀ t : ℝ, 0<t → t≤1 → y+t • (z-y)∈U∩C) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (∀ t : I,t≠0 → t≠1 → c t∈U) ∧
      ∃ ε : ℝ,0<ε ∧ range c∩ball y ε⊆insert y C := by
  have hz : z∈U := by simpa using (hby 1 zero_lt_one le_rfl).1
  have hzy : z≠y := fun h => hy (h ▸ hz)
  have hseg : segment ℝ y z⊆insert y (U∩C) := halfopen_radial_segment hby
  by_cases hxz : x=z
  · subst x
    let c := lineArc z y hzy
    refine ⟨c,by simp [c],by simp [c],?_,?_,1,zero_lt_one,?_⟩
    · rw [show range c=segment ℝ z y by exact lineArc_range ..]
      exact FiniteSupport.segment z y
    · intro t ht₀ ht₁
      have hm : c t∈segment ℝ y z := by rw [segment_symm,←lineArc_range z y hzy]; exact mem_range_self t
      rcases hseg hm with hm|hm
      · exact (ht₁ (c.injective (hm.trans (show c 1=y by simp [c]).symm))).elim
      · exact hm.1
    · intro q hq
      have hm : q∈segment ℝ y z := by
        have hh := hq.1
        rwa [show range c=segment ℝ z y by exact lineArc_range ..,segment_symm] at hh
      exact (hseg hm).imp id And.right
  obtain ⟨b,hb₀,hb₁,hbU,hbS⟩ := arc_between_accessible_points hU hc hxz hax
    (a:=w) (b:=z) (fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using hz)
  have hyb : y∉range b := by
    rintro ⟨t,ht⟩
    by_cases ht₀ : t=0
    · exact hxy (hb₀.symm.trans (ht₀ ▸ ht))
    by_cases ht₁ : t=1
    · exact hy ((ht₁ ▸ ht) ▸ hb₁.symm ▸ hz)
    exact hy (ht ▸ hbU t ht₀ ht₁)
  let d := lineArc z y hzy
  obtain ⟨c,hc₀,hc₁,hcr⟩ := extend_arc b d (by simpa [d] using hb₁) (by simpa [d] using hyb)
  have hc₀' : c 0=x := hc₀.trans hb₀
  have hc₁' : c 1=y := by simpa [d] using hc₁
  have hdr : range d=segment ℝ y z := by rw [lineArc_range,segment_symm]
  have hr : range b⊆insert x U := by
    rintro q ⟨t,rfl⟩
    by_cases ht₀ : t=0
    · exact Or.inl (ht₀ ▸ hb₀)
    by_cases ht₁ : t=1
    · exact Or.inr (ht₁ ▸ hb₁.symm ▸ hz)
    exact Or.inr (hbU t ht₀ ht₁)
  obtain ⟨ε,hε,havoid⟩ := Metric.isOpen_iff.mp b.compact_range.isClosed.isOpen_compl y hyb
  refine ⟨c,hc₀',hc₁',?_,?_,ε,hε,?_⟩
  · apply (hbS.union (FiniteSupport.segment y z)).mono
    simpa only [hdr] using hcr
  · intro t ht₀ ht₁
    rcases hcr (mem_range_self t) with hh|hh
    · rcases hr hh with hh|hh
      · exact (ht₀ (c.injective (hh.trans hc₀'.symm))).elim
      · exact hh
    · rw [hdr] at hh
      rcases hseg hh with hh|hh
      · exact (ht₁ (c.injective (hh.trans hc₁'.symm))).elim
      · exact hh.1
  · rintro q ⟨hq,hqball⟩
    rcases hcr hq with hh|hh
    · exact (havoid hqball hh).elim
    · rw [hdr] at hh
      exact (hseg hh).imp id And.right
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_HalfParam
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem extend_star_in_sector {ι : Type*} [Finite ι]
    (P : Finset (ℂ × ℂ)) {a x y : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2)
    (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (hS : ∀ i,FiniteSupport (range (F i))) (h₀ : ∀ i,F i 0=x)
    (h₁ : ∀ i,F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hFU : ∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (C : Set ℂ) (hC : IsOpen C) (hyC : y∈closure C)
    (hCU : C⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ z∈C,∀ t : ℝ,0<t → t≤1 → y+t • (z-y)∈C) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (c '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      (∀ i,∀ s t : I,c s=F i t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      ∃ ε : ℝ,0<ε ∧ range c∩ball y ε⊆insert y C := by
  classical
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  let G := ⋃ i,range (F i)
  have hK : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUK : U⊆Kᶜ := connectedComponentIn_subset _ _
  have hyU : y∉U := fun hh => hUK hh hy
  have hxy : x≠y := fun he => hyU (he ▸ hx)
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hS
  have hQi (i : ι) : range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2 :=
    fun z hz => hQ (mem_iUnion.mpr ⟨i,hz⟩)
  obtain ⟨R,hR⟩ := finite_graph_exact_segments F Q hQi
  let L := K∪G
  have hL : L=⋃ p∈P∪R,segment ℝ p.1 p.2 := by rw [finite_segment_union,←hR]
  have hLc : IsClosed L := by rw [hL]; exact isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  obtain ⟨r,hr,hstable⟩ := finite_segments_radial_stable (P∪R) y
  have hne : (ball y r∩C).Nonempty := mem_closure_iff_nhds.mp hyC _ (ball_mem_nhds y hr)
  obtain ⟨z,⟨hzball,hzC⟩,hzL⟩ := (complex_finite_segments_compl_dense (P∪R)).inter_open_nonempty
    _ (isOpen_ball.inter hC) hne
  rw [←hL] at hzL
  have hzU : z∈U := hCU hzC
  let Z := connectedComponentIn Lᶜ z
  have hZU : Z⊆U := by
    have hs := connectedComponentIn_mono z (show Lᶜ⊆Kᶜ from compl_subset_compl.mpr subset_union_left)
    rwa [←connectedComponentIn_eq hzU] at hs
  have hzrad (t : ℝ) (ht : 0<t) (ht₁ : t≤1) : y+t • (z-y)∈Z∩C := by
    let T : Set ℂ := (fun t : ℝ => y+t • (z-y)) '' Ioc 0 1
    have hT : IsPreconnected T := isPreconnected_Ioc.image _ (by fun_prop)
    have hzT : z∈T := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
    have hTL : T⊆Lᶜ := by
      rintro b ⟨s,hs,rfl⟩ hb
      rw [hL] at hb
      exact hzL (hL ▸ (hstable z hzball s hs.1 hs.2).mp hb)
    exact ⟨hT.subset_connectedComponentIn hzT hTL ⟨t,⟨ht,ht₁⟩,rfl⟩,hrad z hzC t ht ht₁⟩
  let V := U\G
  have hV : IsOpen V := hU.sdiff (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed)
  have hzV : z∈V := ⟨hzU,fun h => hzL (Or.inr h)⟩
  have hVL : V⊆Lᶜ := by
    rintro b ⟨hbU,hbG⟩ (hbK|hbG')
    · exact hUK hbU hbK
    · exact hbG hbG'
  have hcomp : connectedComponentIn V z=Z := by
    apply subset_antisymm (connectedComponentIn_mono z hVL)
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzL)
    intro b hb
    exact ⟨hZU hb,fun hbG => connectedComponentIn_subset _ _ hb (Or.inr hbG)⟩
  have haccess : ∃ w : ℂ, ∀ t : ℝ,0<t → t≤1 → x+t • (w-x)∈Z := by
    by_cases hn : Nonempty ι
    · let _ : Nonempty ι := hn
      let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
      let _ : DiscreteTopology (ConnectedComponents V) := inferInstance
      have hxcl := tame_star_center_incident_weak F hF Q hQi hU isPreconnected_connectedComponentIn
        x hx h₀ h₁ hFU ConnectedComponents.continuous_coe
        (ConnectedComponents.mk (⟨z,hzV⟩ : V)) ⟨z,hzV,rfl⟩
      change x∈closure (region V ConnectedComponents.mk (ConnectedComponents.mk (⟨z,hzV⟩ : V))) at hxcl
      rw [component_region_eq,hcomp] at hxcl
      have hxG : x∈G := by
        obtain ⟨i⟩ := hn
        exact mem_iUnion.mpr ⟨i,0,h₀ i⟩
      have hxL : x∈⋃ p∈P∪R,segment ℝ p.1 p.2 := hL ▸ Or.inr hxG
      change x∈closure (connectedComponentIn Lᶜ z) at hxcl
      rw [hL] at hxcl
      obtain ⟨w,_,hw⟩ := component_radial_access (P∪R) hxL hxcl
      exact ⟨w,fun t ht ht₁ => by simpa only [←hL] using hw t ht ht₁⟩
    · have hGe : G=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨i,_⟩ := mem_iUnion.mp hb
        exact hn ⟨i⟩
      have hUL : U⊆Lᶜ := by simpa only [L,hGe,union_empty] using hUK
      have hxZ : x∈Z := isPreconnected_connectedComponentIn.subset_connectedComponentIn hzU hUL hx
      exact ⟨x,fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using hxZ⟩
  obtain ⟨w,hw⟩ := haccess
  obtain ⟨c,hc₀,hc₁,hcS,hcZ,hce⟩ := arc_with_terminal_germ hLc.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hxy (fun h => hyU (hZU h)) hw hzrad
  have hcV (t : I) (ht₀ : t≠0) (ht₁ : t≠1) : c t∈V := by
    have hh : c t∈Z := hcZ t ht₀ ht₁
    rw [←hcomp] at hh
    exact connectedComponentIn_subset _ _ hh
  refine ⟨c,hc₀,hc₁,hcS,?_,?_,hce⟩
  · rintro b ⟨t,ht,rfl⟩
    exact (hcV t ht.1.ne' ht.2.ne).1
  · intro i s t he
    have hs : s=0 ∨ s=1 := by
      by_contra hn
      exact (hcV s (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))).2
        (mem_iUnion.mpr ⟨i,t,he.symm⟩)
    refine ⟨hs,?_⟩
    rcases hs with rfl|rfl
    · exact Or.inl ((F i).injective (he.symm.trans (hc₀.trans (h₀ i).symm)))
    · by_contra hn
      have htU := hFU i ⟨t,⟨lt_of_le_of_ne (show (0:I) ≤ t from t.property.1)
        (fun h => hn (Or.inl h.symm)),lt_of_le_of_ne (le_one t) (fun h => hn (Or.inr h))⟩,rfl⟩
      exact hyU ((he.symm.trans hc₁) ▸ htU)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal

theorem finite_prescribed_star (P : Finset (ℂ × ℂ)) {a x : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (n : ℕ) (y : Fin n → ℂ) (C : Fin n → Set ℂ)
    (hy : ∀ i,y i∈⋃ p∈P,segment ℝ p.1 p.2)
    (hC : ∀ i,IsOpen (C i)) (hyC : ∀ i,y i∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → y i+t • (z-y i)∈C i) :
    ∃ F : Fin n → Arc ℂ,
      Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      (∀ i,F i 0=x) ∧ (∀ i,F i 1=y i) ∧ (∀ i,FiniteSupport (range (F i))) ∧
      (∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      ∀ i,∃ ε : ℝ,0<ε ∧ range (F i)∩ball (y i) ε⊆insert (y i) (C i) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_,?_,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨F,hF,h₀,h₁,hS,hFU,hgerm⟩ := ih (fun i => y i.succ) (fun i => C i.succ)
      (fun i => hy i.succ) (fun i => hC i.succ) (fun i => hyC i.succ)
      (fun i => hCU i.succ) (fun i => hrad i.succ)
    have h₁' (i : Fin n) : F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a := by
      intro h
      exact connectedComponentIn_subset _ _ h (h₁ i ▸ hy i.succ)
    obtain ⟨c,hc₀,hc₁,hcS,hcU,hcF,hce⟩ := extend_star_in_sector P hx (hy 0) F hF hS h₀ h₁'
      hFU (C 0) (hC 0) (hyC 0) (hCU 0) (hrad 0)
    let F' : Fin (n+1) → Arc ℂ := Fin.cases c F
    refine ⟨F',?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact fun h => (h rfl).elim
        · intro _ s t he
          exact hcF j s t he
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ s t he
          exact (hcF i t s he.symm).symm
        · intro h s t he
          exact hF (fun h' => h (congrArg Fin.succ h')) s t he
    · exact Fin.cases hc₀ h₀
    · exact Fin.cases hc₁ h₁
    · exact Fin.cases hcS hS
    · exact Fin.cases hcU hFU
    · exact Fin.cases hce hgerm
end CannonEmbeddedArc.Arc

namespace CannonSectors
open Set Metric Topology CannonPolygonal CannonSegmentCones

variable {ι : Type*}

lemma radial_vertex_closure {C : Set ℂ} {x : ℂ} (hne : C.Nonempty)
    (hrad : ∀ z∈C,∀ t : ℝ,0<t → t≤1 → x+t • (z-x)∈C) : x∈closure C := by
  obtain ⟨z,hz⟩ := hne
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min (1/2:ℝ) (ε/(2*(dist z x+1)))
  have hd : 0<2*(dist z x+1) := by positivity
  have ht : 0<t := lt_min (by norm_num) (div_pos hε hd)
  have ht₁ : t≤1 := (min_le_left ..).trans (by norm_num)
  have htd : t*(2*(dist z x+1))≤ε := (le_div_iff₀ hd).mp (min_le_right ..)
  refine ⟨x+t • (z-x),hrad z hz t ht ht₁,?_⟩
  rw [dist_comm,radial_dist x z ht.le]
  nlinarith [dist_nonneg (x:=z) (y:=x)]

end CannonSectors

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_VertexLines
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Finite ι]

omit [Finite ι] in
lemma vertex_mem_support (F : ι → Arc ℂ) {v : ℂ} (hv : Vertex F v) :
    v∈⋃ i,range (F i) := by
  obtain ⟨i,hi⟩ := hv
  exact mem_iUnion.mpr ⟨i,hi.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)⟩

omit [Finite ι] in
lemma vertex_parameter (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι) {t : I}
    (ht : Vertex F (F i t)) : t=0 ∨ t=1 := by
  by_contra hn
  push Not at hn
  exact interior_not_vertex F hF i (lt_of_le_of_ne (nonneg t) hn.1.symm)
    (lt_of_le_of_ne (le_one t) hn.2) ht

lemma mem_faceVertices (F : ι → Arc ℂ) (d : Faces F) (v : ℂ) :
    v∈faceVertices F d ↔ Vertex F v ∧ v∈closure (face F d) := by
  simp [faceVertices]

omit [Finite ι] in
lemma face_nonempty (F : ι → Arc ℂ) (d : Faces F) : (face F d).Nonempty :=
  (component_region_connected _ d).nonempty
lemma face_open (F : ι → Arc ℂ) (d : Faces F) : IsOpen (face F d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  exact region_isOpen (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl
    ConnectedComponents.continuous_coe d

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_Support
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι] in
lemma mem_vertices (F : ι → Arc ℂ) (S : Finset ι) (x : ℂ) :
    x∈vertices F S ↔ ∃ i∈S,F i 0=x ∨ F i 1=x := by
  classical
  simp [vertices,eq_comm]
end CannonPlanarEuler

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_LabelsConstant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonClosedCover
open Set

variable {X D J : Type*} [TopologicalSpace X] [Finite J]

theorem labels_constant {S : Set X} (hS : IsPreconnected S) (C : J → Set X)
    (hC : ∀ j,IsClosed (C j)) (hcover : S⊆⋃ j,C j) (hne : ∀ j,(S∩C j).Nonempty)
    (l : J → D) (hcompat : ∀ x∈S,∀ i,x∈C i → ∀ j,x∈C j → l i=l j) :
    ∀ i j,l i=l j := by
  classical
  intro i j
  by_contra hij
  let A := ⋃ k∈{k | l k=l i},C k
  let B := ⋃ k∈{k | l k≠l i},C k
  have hA : IsClosed A := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hC k
  have hB : IsClosed B := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hC k
  have hAB : S⊆A∪B := by
    intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases h : l k=l i
    · exact Or.inl (mem_iUnion₂.mpr ⟨k,h,hk⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨k,h,hk⟩)
  obtain ⟨u,hu,huC⟩ := hne i
  obtain ⟨v,hv,hvC⟩ := hne j
  obtain ⟨x,hx,hxa,hxb⟩ := isPreconnected_closed_iff.mp hS A B hA hB hAB
    ⟨u,hu,mem_iUnion₂.mpr ⟨i,rfl,huC⟩⟩
    ⟨v,hv,mem_iUnion₂.mpr ⟨j,Ne.symm hij,hvC⟩⟩
  obtain ⟨k,hk,hkx⟩ := mem_iUnion₂.mp hxa
  obtain ⟨m,hm,hmx⟩ := mem_iUnion₂.mp hxb
  exact hm ((hcompat x hx m hmx k hkx).trans hk)
end CannonClosedCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceClosuresCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_interior_complement_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (e : ι)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    IsPreconnected ((⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  let m : I := ⟨1/2,by norm_num,by norm_num⟩
  have hm₀ : (0:I) < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < (1:I) := by change (1/2:ℝ)<1; norm_num
  let q := F e m
  let S : Set ℂ := (⋃ i,range (F i))\{q}
  have hR₀ : F e 0∈R := Or.inr (by simp)
  have hR₁ : F e 1∈R := Or.inr (by simp)
  have hRi (i : {i : ι // i≠e}) : range (F i.val)⊆R := fun z hz => Or.inl (mem_iUnion.mpr ⟨i,hz⟩)
  have hnot (i : {i : ι // i≠e}) : q∉range (F i.val) := by
    rintro ⟨t,ht⟩
    rcases ((hF i.property).1 t m ht).2 with h|h
    · exact hm₀.ne' h
    · exact hm₁.ne h
  have hRS : R⊆S := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion.mpr ⟨i.val,hzi⟩,fun he => hnot i (he ▸ hzi)⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 0⟩,fun he => hm₀.ne ((F e).injective he)⟩
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 1⟩,fun he => hm₁.ne ((F e).injective he).symm⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  let C : ({i : ι // i≠e}⊕Bool) → Set ℂ := Sum.elim (fun i => range (F i.val))
    (fun b => if b then F e '' Icc m (1:I) else F e '' Icc (0:I) m)
  let l : ({i : ι // i≠e}⊕Bool) → Bool := Sum.elim (fun i => f (F i.val 0))
    (fun b => if b then f (F e 1) else f (F e 0))
  have hclosed : ∀ j,IsClosed (C j) := by
    rintro (i|b)
    · exact (F i.val).compact_range.isClosed
    · cases b <;> exact (isCompact_Icc.image (F e).continuous).isClosed
  have hcover : S⊆⋃ j,C j := by
    rintro z ⟨hz,hzq⟩
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hz
    by_cases hi : i=e
    · subst i
      rcases le_total t m with ht|ht
      · exact mem_iUnion.mpr ⟨Sum.inr false,⟨t,⟨nonneg t,ht⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨Sum.inr true,⟨t,⟨ht,le_one t⟩,rfl⟩⟩
    · exact mem_iUnion.mpr ⟨Sum.inl ⟨i,hi⟩,mem_range_self t⟩
  have hne : ∀ j,(S∩C j).Nonempty := by
    rintro (i|b)
    · exact ⟨F i.val 0,hRS (hRi i (mem_range_self 0)),mem_range_self 0⟩
    · cases b
      · exact ⟨F e 0,hRS hR₀,⟨0,⟨le_rfl,hm₀.le⟩,rfl⟩⟩
      · exact ⟨F e 1,hRS hR₁,⟨1,⟨hm₁.le,le_rfl⟩,rfl⟩⟩
  have hlabel (i : {i : ι // i≠e}) {z : ℂ} (hz : z∈C (Sum.inl i)) :
      f z=l (Sum.inl i) :=
    (isPreconnected_range (F i.val).continuous).constant (hf.mono (hRi i)) hz (mem_range_self 0)
  have holdnew (i : {i : ι // i≠e}) (b : Bool) {z : ℂ}
      (hzi : z∈C (Sum.inl i)) (hzb : z∈C (Sum.inr b)) :
      l (Sum.inl i)=l (Sum.inr b) := by
    obtain ⟨s,rfl⟩ := hzi
    cases b
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₀ : t=0 := ((hF i.property).1 s t he.symm).2.resolve_right
        (fun h => hm₁.not_ge (h ▸ ht.2))
      have hz : F i.val s=F e 0 := ht₀ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₁ : t=1 := ((hF i.property).1 s t he.symm).2.resolve_left
        (fun h => hm₀.not_ge (h ▸ ht.1))
      have hz : F i.val s=F e 1 := ht₁ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
  have hall : ∀ i j,l i=l j := by
    apply CannonClosedCover.labels_constant (hK q) C hclosed hcover hne l
    intro z hz i hzi j hzj
    rcases i with i|b <;> rcases j with j|c
    · exact (hlabel i hzi).symm.trans (hlabel j hzj)
    · exact holdnew i c hzi hzj
    · exact (holdnew j b hzj hzi).symm
    · cases b <;> cases c
      · rfl
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm hs.2 (hts ▸ ht.1)
        exact (hz.2 (congrArg (F e) hsm)).elim
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm (hts ▸ ht.2) hs.1
        exact (hz.2 (congrArg (F e) hsm)).elim
      · rfl
  have hvalue {z : ℂ} (hz : z∈R) : f z=l (Sum.inr false) := by
    rcases hz with hz|hz
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact (hlabel i hzi).trans (hall _ _)
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · rfl
      · exact hall (Sum.inr true) _
  exact (hvalue hx).trans (hvalue hy).symm
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_on_tame_cycle (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ b : Arc ℂ,b 0=F e 0 ∧ b 1=F e 1 ∧
      range b⊆⋃ i,range (F i) ∧ FiniteSupport (range b) ∧
      ∀ s t,F e s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  have hR : IsPreconnected R := edge_interior_complement_preconnected F hF e hK
  obtain ⟨P,hP⟩ := finite_graph_exact_segments (fun i : {i : ι // i≠e} => F i.val) Q (fun i => hQ i.val)
  let T := P∪{(F e 0,F e 0),(F e 1,F e 1)}
  have hT : R=⋃ p∈T,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hP]
    apply congrArg (fun S : Set ℂ => (⋃ i : {i : ι // i≠e},range (F i.val))∪S)
    ext z
    constructor
    · intro hz
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion₂.mpr ⟨(F e 0,F e 0),Finset.mem_insert_self ..,left_mem_segment ..⟩
      · exact mem_iUnion₂.mpr ⟨(F e 1,F e 1),Finset.mem_insert_of_mem (Finset.mem_singleton_self _),left_mem_segment ..⟩
    · intro hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      rcases Finset.mem_insert.mp hp with rfl|hp
      · exact Or.inl (by simpa only [segment_same,mem_singleton_iff] using hz)
      · have hp' := Finset.mem_singleton.mp hp
        subst p
        exact Or.inr (by simpa only [segment_same,mem_singleton_iff] using hz)
  obtain ⟨b,hb₀,hb₁,hbT,hbS⟩ := preconnected_finite_segments_arc T (hT ▸ hR)
    (hT ▸ (show F e 0∈R from Or.inr (by simp)))
    (hT ▸ (show F e 1∈R from Or.inr (by simp))) (F e).endpoints_ne
  have hbR : range b⊆R := by rwa [←hT] at hbT
  have hRK : R⊆⋃ i,range (F i) := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i.val,hzi⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion.mpr ⟨e,mem_range_self 0⟩
      · exact mem_iUnion.mpr ⟨e,mem_range_self 1⟩
  refine ⟨b,hb₀,hb₁,hbR.trans hRK,hbS,?_⟩
  intro s t he
  have hs : s=0 ∨ s=1 := by
    have hbs : F e s∈R := he.symm ▸ hbR (mem_range_self t)
    rcases hbs with hbs|hbs
    · obtain ⟨i,u,hu⟩ := mem_iUnion.mp hbs
      exact ((hF i.property).1 u s hu).2
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hbs : F e s=F e 0 ∨ F e s=F e 1) with h|h
      · exact Or.inl ((F e).injective h)
      · exact Or.inr ((F e).injective h)
  refine ⟨hs,?_⟩
  rcases hs with rfl|rfl
  · exact Or.inl (b.injective (he.symm.trans hb₀.symm))
  · exact Or.inr (b.injective (he.symm.trans hb₁.symm))
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NoncutCycleFreeRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem noncut_cycle_free_region {K : Set ℂ}
    (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hb : range b⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : IsConnected (K\{a 1}))
    (hCK : (range a∪range b)\{a 1}⊆Kᶜ) :
    ∃ d : ConnectedComponents ((range a∪range b)ᶜ : Set ℂ),
      (∀ z∈range a∪range b,d∈incident _ ConnectedComponents.mk z) ∧
      closure (region _ ConnectedComponents.mk d)\{a 1}⊆connectedComponentIn Kᶜ (a 0) := by
  let C : Set ℂ := range a∪range b
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Cᶜ : Set ℂ) := hC.isOpen_compl.locallyConnectedSpace
  have hqC : a 1∈C := Or.inl (mem_range_self 1)
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  have hKC : K\{a 1}⊆Cᶜ := by
    intro z hz hzC
    exact hCK ⟨hzC,hz.2⟩ hz.1
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe hK hKC
  let i := l.symm d
  let e := l (!i)
  let R := region Cᶜ ConnectedComponents.mk e
  have hRconn : IsConnected R := component_region_connected _ _
  have hRi : R⊆Kᶜ := by
    intro z hz hzK
    have hzq : z≠a 1 := fun h => (region_subset _ _ _ hz) (h.symm ▸ hqC)
    obtain ⟨_,he⟩ := hd ⟨hzK,hzq⟩
    obtain ⟨_,he'⟩ := hz
    have hh : (!i)=i := l.injective (he'.symm.trans (he.trans (l.apply_symm_apply d).symm))
    cases i <;> simp at hh
  have hRcl : closure R=R∪C := by
    apply Subset.antisymm
    · intro z hz
      by_cases hzC : z∈C
      · exact Or.inr hzC
      · exact Or.inl (closure_region_inside hC.isOpen_compl ConnectedComponents.continuous_coe hz hzC)
    · apply union_subset subset_closure
      intro z hz
      change e∈incident _ ConnectedComponents.mk z
      rw [hl z hz]
      exact mem_range_self (!i)
  have hRnoq : R⊆closure R\{a 1} := by
    intro z hz
    exact ⟨subset_closure hz,fun he => (region_subset _ _ _ hz) (he.symm ▸ hqC)⟩
  have hpre : IsPreconnected (closure R\{a 1}) :=
    hRconn.isPreconnected.subset_closure hRnoq sdiff_subset
  have hsub : closure R\{a 1}⊆Kᶜ := by
    rintro z ⟨hz,hzq⟩
    rw [hRcl] at hz
    exact hz.elim (fun h => hRi h) (fun h => hCK ⟨h,hzq⟩)
  have hxcl : a 0∈closure R\{a 1} := by
    rw [hRcl]
    exact ⟨Or.inr (Or.inl (mem_range_self 0)),a.endpoints_ne⟩
  refine ⟨e,?_,hpre.subset_connectedComponentIn hxcl hsub⟩
  intro z hz
  rw [hl z hz]
  exact mem_range_self (!i)
end CannonEmbeddedArc.Arc

namespace CannonSegmentCones
open Set Metric Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma local_component_radial {K : Set E} {q : E} {r : ℝ}
    (hstable : RadialStable K q r) {a z : E}
    (hz : z∈connectedComponentIn (ball q r\K) a) {t : ℝ} (ht : 0<t) (ht₁ : t≤1) :
    q+t • (z-q)∈connectedComponentIn (ball q r\K) a := by
  let S : Set E := (fun u : ℝ => q+u • (z-q)) '' Ioc 0 1
  have hzV := connectedComponentIn_subset (ball q r\K) a hz
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hSV : S⊆ball q r\K := by
    rintro w ⟨u,hu,rfl⟩
    exact ⟨radial_mem_ball hzV.1 hu.1.le hu.2,fun h => hzV.2 ((hstable z hzV.1 u hu.1 hu.2).mp h)⟩
  have hzS : z∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSC := hS.subset_connectedComponentIn hzS hSV
  have he := connectedComponentIn_eq hz
  rw [←he] at hSC
  exact hSC ⟨t,⟨ht,ht₁⟩,rfl⟩
end CannonSegmentCones

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal CannonFaceIncidence CannonSegmentCones

theorem noncut_radial_germs_join (P : Finset (ℂ × ℂ)) {q a x : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q}))
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (C : Fin 2 → Set ℂ) (hC : ∀ i,IsOpen (C i)) (hqC : ∀ i,q∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → q+t • (z-q)∈C i)
    {r : ℝ} (hr : 0 < r) :
    ∃ B : Set ℂ,IsConnected B ∧
      B⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q r ∧
      ∀ i,(B∩C i).Nonempty := by
  classical
  let K : Set ℂ := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  obtain ⟨F,hF,h₀,h₁,hS,hFU,hgerm⟩ := finite_prescribed_star P hx 2 (fun _ => q) C
    (fun _ => hqK) hC hqC hCU hrad
  let b := F 0
  let c := F 1
  have hbc₀ : b 0=c 0 := (h₀ 0).trans (h₀ 1).symm
  have hbc₁ : b 1=c 1 := (h₁ 0).trans (h₁ 1).symm
  have hbc : ∀ s t,b s=c t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := hF (by decide : (0:Fin 2)≠1)
  obtain ⟨Q,hQ⟩ := (hS 0).union (hS 1)
  have hbQ : range b⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun z hz => hQ (Or.inl hz)
  have hcQ : range c⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun z hz => hQ (Or.inr hz)
  have hFnot (i : Fin 2) {t : I} (ht : t≠1) : F i t∈U := by
    by_cases ht₀ : t=0
    · simpa only [ht₀,h₀] using hx
    · exact hFU i ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),
        lt_of_le_of_ne (le_one t) ht⟩,rfl⟩
  have hCK : (range b∪range c)\{b 1}⊆Kᶜ := by
    rintro z ⟨hz,hzq⟩
    rcases hz with ⟨t,rfl⟩|⟨t,rfl⟩
    · exact connectedComponentIn_subset Kᶜ a (hFnot 0 (fun he => hzq (congrArg b he)))
    · exact connectedComponentIn_subset Kᶜ a (hFnot 1 (fun he => hzq ((congrArg c he).trans hbc₁.symm)))
  have hconn : IsConnected (K\{b 1}) := by simpa only [b,h₁] using hK
  obtain ⟨d,hd,hfree⟩ := noncut_cycle_free_region b c hbc₀ hbc₁ hbc Q hbQ hcQ hconn hCK
  have hBU : closure (region _ ConnectedComponents.mk d)\{q}⊆U := by
    have he : connectedComponentIn Kᶜ (b 0)=U := by
      rw [show b 0=x from h₀ 0]
      exact (connectedComponentIn_eq hx).symm
    simpa only [show b 1=q from h₁ 0,he] using hfree
  let L : Set ℂ := range b∪range c
  have hL : IsClosed L := b.compact_range.isClosed.union c.compact_range.isClosed
  let _ : LocallyConnectedSpace (Lᶜ : Set ℂ) := hL.isOpen_compl.locallyConnectedSpace
  obtain ⟨H,W,hW,hqW,hH,hflat⟩ := pair_flat_at_left b c hbc₀ hbc₁ hbc Q hbQ hcQ 1
  have hHq : H (0,0)=q := hH.trans (h₁ 0)
  have hqW' : q∈W∩ball q r := ⟨(h₁ 0) ▸ hqW,mem_ball_self hr⟩
  have hflat' : ∀ z∈W∩ball q r,z∈Lᶜ ↔ (H.symm z).2≠0 := by
    intro z hz
    rw [mem_compl_iff,hflat z hz.1]
    have hh : z∈H '' CannonPlanarCorner.horizontal ↔ (H.symm z).2=0 := by
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [H.symm_apply_apply,CannonPlanarCorner.horizontal,mem_ofPred_eq] using hy
      · intro hy
        exact ⟨H.symm z,hy,H.apply_symm_apply z⟩
    rw [hh]
  obtain ⟨V,B,hV,hqV,hVW,hB,hBW,hBcl⟩ := flat_chart_boundary_patch
    ConnectedComponents.continuous_coe H (hW.inter isOpen_ball) (hHq.symm ▸ hqW') hflat'
    (d:=d) (by rw [hHq]; exact hd q (Or.inl ⟨1,h₁ 0⟩))
  have hqV' : q∈V := hHq ▸ hqV
  have hBV : B⊆U∩ball q r := by
    intro z hz
    have hh := hBW hz
    refine ⟨hBU ⟨subset_closure hh.2,?_⟩,hh.1.2⟩
    intro he
    exact (region_subset _ _ _ hh.2) (he.symm ▸ Or.inl ⟨1,h₁ 0⟩)
  refine ⟨B,hB,hBV,?_⟩
  intro i
  obtain ⟨ε,hε,hεg⟩ := hgerm i
  let N := V∩ball q ε
  have hN : IsOpen N := hV.inter isOpen_ball
  have hqN : q∈N := ⟨hqV',mem_ball_self hε⟩
  obtain ⟨t,ht,htN⟩ := (dense_compl_singleton (1:I)).exists_mem_open
    ((F i).continuous.isOpen_preimage N hN) ⟨1,by change F i 1∈N; rw [h₁]; exact hqN⟩
  have htq : F i t≠q := fun he => ht ((F i).injective (he.trans (h₁ i).symm))
  have htC : F i t∈C i := (hεg ⟨mem_range_self t,htN.2⟩).resolve_left htq
  have htL : F i t∈L := by
    fin_cases i
    · exact Or.inl (mem_range_self t)
    · exact Or.inr (mem_range_self t)
  have htcl : F i t∈closure B := hBcl ⟨htN.1,by simpa only [compl_compl] using htL⟩
  obtain ⟨z,hzC,hzB⟩ := (mem_closure_iff_nhds.mp htcl) (C i) ((hC i).mem_nhds htC)
  exact ⟨z,hzB,hzC⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal CannonFaceIncidence CannonSegmentCones

theorem noncut_face_ball_preconnected (P : Finset (ℂ × ℂ)) {q : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q}))
    {r : ℝ} (hr : 0 < r) (hstable : RadialStable (⋃ p∈P,segment ℝ p.1 p.2) q r) :
    ∀ a : ℂ,IsPreconnected
      (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q r) := by
  classical
  let K : Set ℂ := ⋃ p∈P,segment ℝ p.1 p.2
  have hKclosed : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  let V := ball q r\K
  have hV : IsOpen V := isOpen_ball.sdiff hKclosed
  intro a
  let U := connectedComponentIn Kᶜ a
  by_cases hne : (U∩ball q r).Nonempty
  · obtain ⟨x,hxU,hxr⟩ := hne
    have hxV : x∈V := ⟨hxr,connectedComponentIn_subset Kᶜ a hxU⟩
    have hsub {z : ℂ} (hz : z∈U∩ball q r) : connectedComponentIn V z⊆U∩ball q r := by
      have hzV : z∈V := ⟨hz.2,connectedComponentIn_subset Kᶜ a hz.1⟩
      have h := (isPreconnected_connectedComponentIn (F:=V) (x:=z)).subset_connectedComponentIn
        (mem_connectedComponentIn hzV) (fun w hw => (connectedComponentIn_subset V z hw).2)
      have he : U=connectedComponentIn Kᶜ z := connectedComponentIn_eq hz.1
      change connectedComponentIn V z⊆connectedComponentIn Kᶜ z at h
      rw [←he] at h
      exact fun w hw => ⟨h hw,(connectedComponentIn_subset V z hw).1⟩
    have heq : U∩ball q r=connectedComponentIn V x := by
      apply Subset.antisymm ?_ (hsub ⟨hxU,hxr⟩)
      intro y hy
      let Z : Fin 2 → ℂ := ![x,y]
      have hZ : ∀ i,Z i∈U∩ball q r := by
        intro i
        fin_cases i
        · exact ⟨hxU,hxr⟩
        · exact hy
      let C : Fin 2 → Set ℂ := fun i => connectedComponentIn V (Z i)
      have hZV (i : Fin 2) : Z i∈V := ⟨(hZ i).2,connectedComponentIn_subset Kᶜ a (hZ i).1⟩
      have hCopen (i : Fin 2) : IsOpen (C i) := hV.connectedComponentIn
      have hCrad (i : Fin 2) : ∀ z∈C i,∀ t : ℝ,0<t → t≤1 → q+t • (z-q)∈C i :=
        fun _ hz _ ht ht₁ => local_component_radial hstable hz ht ht₁
      have hCcl (i : Fin 2) : q∈closure (C i) := CannonSectors.radial_vertex_closure
        ⟨Z i,mem_connectedComponentIn (hZV i)⟩ (hCrad i)
      have hCU (i : Fin 2) : C i⊆U := (hsub (hZ i)).trans inter_subset_left
      obtain ⟨B,hB,hBV,hBC⟩ := noncut_radial_germs_join P hqK hK hxU C hCopen hCcl hCU hCrad hr
      obtain ⟨z,hzB,hzC⟩ := hBC 0
      have hBV' : B⊆V := fun w hw => ⟨(hBV hw).2,connectedComponentIn_subset Kᶜ a (hBV hw).1⟩
      have hBC₀ := hB.isPreconnected.subset_connectedComponentIn hzB hBV'
      have he₀ : C 0=connectedComponentIn V z := connectedComponentIn_eq hzC
      rw [←he₀] at hBC₀
      obtain ⟨w,hwB,hwC⟩ := hBC 1
      have he₁ : C 1=connectedComponentIn V w := connectedComponentIn_eq hwC
      have he₂ : C 0=connectedComponentIn V w := connectedComponentIn_eq (hBC₀ hwB)
      have hyC : y∈C 1 := mem_connectedComponentIn (hZV 1)
      rw [he₁,←he₂] at hyC
      exact hyC
    rw [heq]
    exact isPreconnected_connectedComponentIn
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty
theorem noncut_locally_connected_faces (P : Finset (ℂ × ℂ)) {q : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q})) :
    ∃ r>0,∀ s : ℝ,0 < s → s ≤ r → ∀ a : ℂ,IsPreconnected
      (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q s) := by
  obtain ⟨r,hr,hstable⟩ := finite_segments_radial_stable P q
  exact ⟨r,hr,fun _ hs hsr => noncut_face_ball_preconnected P hqK hK hs (hstable.mono_radius hsr)⟩
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Spans
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonCircleBoundary

variable {ι : Type*} [Finite ι]

lemma tame_incident_segment (a : Arc ℂ) (P : Finset (ℂ × ℂ))
    (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2) {q : ℂ} (hq : q=a 0 ∨ q=a 1) :
    ∃ p : ℂ,p≠q ∧ segment ℝ q p⊆range a := by
  have first (a : Arc ℂ) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2) :
      ∃ p : ℂ,p≠a 0 ∧ segment ℝ (a 0) p⊆range a := by
    obtain ⟨t,ht,he⟩ := tame_initial_interval a P ha
    exact ⟨a t,a.injective.ne ht.ne',he ▸ image_subset_range _ _⟩
  rcases hq with rfl|rfl
  · exact first a ha
  · simpa only [reverse_zero,reverse_range] using first a.reverse (by simpa only [reverse_range] using ha)

lemma radial_mem_segment {q p : ℂ} (hp : p≠q) {s : ℝ}
    (hs : 0 ≤ s) (hsp : s ≤ ‖p-q‖) :
    q+s • (radialDirection q ⟨p,hp⟩:ℂ)∈segment ℝ q p := by
  have hn : 0<‖p-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  rw [segment_eq_image']
  refine ⟨s/‖p-q‖,⟨div_nonneg hs hn.le,(div_le_one hn).mpr hsp⟩,?_⟩
  simp only [radialDirection,smul_smul,div_eq_mul_inv]

theorem noncut_face_degree_two (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q)
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    (e : Fin 3 → ι) (he : Function.Injective e)
    (heq : ∀ k,q∈range (F (e k)))
    (heface : ∀ k,e k∈regionEdges F ConnectedComponents.mk d) : False := by
  classical
  let K : Set ℂ := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hqK : q∈K := vertex_mem_support F hq
  have hep (k : Fin 3) : q=F (e k) 0 ∨ q=F (e k) 1 := by
    obtain ⟨t,ht⟩ := heq k
    have hh := vertex_parameter F hF (e k) (ht.symm ▸ hq)
    exact hh.elim (fun h => Or.inl (h ▸ ht.symm)) (fun h => Or.inr (h ▸ ht.symm))
  choose p hp hps using fun k => tame_incident_segment (F (e k)) P (hP (e k)) (hep k)
  let u : Fin 3 → UnitCircle := fun k => radialDirection q ⟨p k,hp k⟩
  have hn (k : Fin 3) : 0<‖p k-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hp k))
  have hui : Function.Injective u := by
    intro i j hij
    by_contra hne
    let s := min ‖p i-q‖ ‖p j-q‖/2
    have hs : 0 < s := half_pos (lt_min (hn i) (hn j))
    have hsi : s≤‖p i-q‖ := (half_le_self (le_of_lt (lt_min (hn i) (hn j)))).trans (min_le_left _ _)
    have hsj : s≤‖p j-q‖ := (half_le_self (le_of_lt (lt_min (hn i) (hn j)))).trans (min_le_right _ _)
    have hz₁ : q+s • (u i:ℂ)∈range (F (e i)) := hps i (radial_mem_segment (hp i) hs.le hsi)
    have hz₂ : q+s • (u i:ℂ)∈range (F (e j)) := by
      rw [hij]
      exact hps j (radial_mem_segment (hp j) hs.le hsj)
    exact radial_ne q (u i) hs ((hF (he.ne hne)).2 ⟨hz₁,hz₂⟩ ⟨heq i,heq j⟩)
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  have hKc : IsConnected (K\{q}) := by
    obtain ⟨z,hz,-,hzq⟩ := graph_no_isolated F hqK isOpen_univ (mem_univ _)
    exact ⟨⟨z,hz,hzq⟩,hK⟩
  have hqQ : q∈⋃ p∈Q,segment ℝ p.1 p.2 := by rw [←hQ]; exact hqK
  have hKQ : IsConnected ((⋃ p∈Q,segment ℝ p.1 p.2)\{q}) := by rw [←hQ]; exact hKc
  obtain ⟨R,hR,hlocal⟩ := noncut_locally_connected_faces Q hqQ hKQ
  let r := min R (min ‖p 0-q‖ (min ‖p 1-q‖ ‖p 2-q‖))
  have hr : 0 < r := lt_min hR (lt_min (hn 0) (lt_min (hn 1) (hn 2)))
  have hrR : r≤R := min_le_left _ _
  have hrp (k : Fin 3) : r≤‖p k-q‖ := by
    have hh := min_le_right R (min ‖p 0-q‖ (min ‖p 1-q‖ ‖p 2-q‖))
    fin_cases k
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  let U := face F d∩ball q r
  have hU : IsPreconnected U := by
    obtain ⟨a,ha⟩ := ConnectedComponents.surjective_coe d
    have hh := hlocal r hr hrR a.val
    rw [←hQ] at hh
    simpa only [U,face,←ha,component_region_eq] using hh
  have hUball : U⊆ball q r\{q} := by
    intro z hz
    exact ⟨hz.2,fun heq => hz.1.1 (heq ▸ hqK)⟩
  apply radial_face_degree_two hU hUball u ?_ ?_ hui
  · intro k s hs hsr hz
    exact hz.1.1 (mem_iUnion.mpr ⟨e k,hps k (radial_mem_segment (hp k) hs.le (hsr.le.trans (hrp k)))⟩)
  · intro k
    have hs : 0 < r/2 := half_pos hr
    have hsr : r/2 < r := half_lt_self hr
    let z := q+(r/2) • (u k:ℂ)
    have hzr : z∈ball q r := by
      have hu : ‖(u k:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp (u k).property
      simpa only [z,mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_pos hs,hu,mul_one] using hsr
    have hzcl : z∈closure (face F d) :=
      region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe (heface k)
        (hps k (radial_mem_segment (hp k) hs.le (hsr.le.trans (hrp k))))
    refine ⟨r/2,hs,?_⟩
    change z∈closure (face F d∩ball q r)
    rw [inter_comm]
    exact isOpen_ball.inter_closure ⟨hzr,hzcl⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma cycle_edge_otherpoint (a b : Arc ℂ) (h₀ : b 0=a 0) (h₁ : b 1=a 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {q : ℂ} (hq : q=a 0 ∨ q=a 1) {W : Set ℂ} (hW : IsOpen W) (hqW : q∈W) :
    ∃ z∈range b,z∈W ∧ z∉range a := by
  have first (t : I) (ht : q=b t) (hqt : t∈closure (Ioo (0:I) 1)) :
      ∃ z∈range b,z∈W ∧ z∉range a := by
    obtain ⟨s,hsW,hs⟩ := (mem_closure_iff_nhds.mp hqt) (b ⁻¹' W)
      ((hW.preimage b.continuous).mem_nhds (show b t∈W from ht ▸ hqW))
    refine ⟨b s,mem_range_self s,hsW,?_⟩
    rintro ⟨u,hu⟩
    exact ((hc u s hu).2).elim hs.1.ne' hs.2.ne
  rcases hq with h|h
  · apply first 0 (h.trans h₀.symm)
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl,zero_le_one⟩
  · apply first 1 (h.trans h₁.symm)
    rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one,le_rfl⟩

theorem noncut_face_second_edge (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (d : Faces F) {q : ℂ} (hq : Vertex F q) {e : ι}
    (he : e∈regionEdges F ConnectedComponents.mk d) (heq : q∈range (F e)) :
    ∃ j : ι,j≠e ∧ j∈regionEdges F ConnectedComponents.mk d ∧ q∈range (F j) := by
  classical
  let K : Set ℂ := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let B : Set ℂ := ⋃ i∈E,range (F i)
  let T : Set ℂ := ⋃ i∈E\{e},range (F i)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  by_contra hn
  push Not at hn
  have hqT : q∉T := by
    intro hh
    obtain ⟨j,hj,hqj⟩ := mem_iUnion₂.mp hh
    exact hn j hj.2 hj.1 hqj
  have hep : q=F e 0 ∨ q=F e 1 := by
    obtain ⟨t,ht⟩ := heq
    have hh := vertex_parameter F hF e (ht.symm ▸ hq)
    exact hh.elim (fun h => Or.inl (h ▸ ht.symm)) (fun h => Or.inr (h ▸ ht.symm))
  have hw : ∃ W : Set ℂ,IsOpen W ∧ q∈W ∧ W⊆Tᶜ ∧ IsConnected (W\range (F e)) := by
    rcases hep with h|h
    · exact h.symm ▸ tame_tip_connected_neighborhood (F e) P (hP e) hT.isOpen_compl (h ▸ hqT)
    · have hh := tame_tip_connected_neighborhood (F e).reverse P
        (by simpa only [reverse_range] using hP e) hT.isOpen_compl
        (by simpa only [reverse_zero] using h ▸ hqT)
      simpa only [reverse_range,reverse_zero,←h] using hh
  obtain ⟨W,hW,hqW,hWT,hconn⟩ := hw
  have hB (z : ℂ) (hz : z∈W\range (F e)) : z∉B := by
    intro hh
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hh
    by_cases hie : i=e
    · exact hz.2 (hie ▸ hzi)
    · exact hWT hz.1 (mem_iUnion₂.mpr ⟨i,⟨hi,hie⟩,hzi⟩)
  have hcl : closure (face F d)=face F d∪B :=
    tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  have hcover : W\range (F e)⊆face F d∪(closure (face F d))ᶜ := by
    intro z hz
    by_cases hzu : z∈face F d
    · exact Or.inl hzu
    · refine Or.inr ?_
      rw [hcl]
      exact fun h => h.elim hzu (hB z hz)
  have hdis : Disjoint (face F d) (closure (face F d))ᶜ :=
    disjoint_left.mpr (fun _ hu hcl => hcl (subset_closure hu))
  have hh := hconn.isPreconnected.subset_or_subset (face_open F d) isClosed_closure.isOpen_compl hdis hcover
  have hqcl : q∈closure (face F d) := region_edge_in_closure F hF P hP
    ConnectedComponents.continuous_coe he heq
  obtain ⟨x,hxW,hxU⟩ := (mem_closure_iff_nhds.mp hqcl) W (hW.mem_nhds hqW)
  have hx : x∈W\range (F e) := ⟨hxW,fun h => hxU.1 (mem_iUnion.mpr ⟨e,h⟩)⟩
  obtain ⟨b,hb₀,hb₁,hbK,-,hbc⟩ := edge_on_tame_cycle F hF P hP hK e
  obtain ⟨z,hzb,hzW,hza⟩ := cycle_edge_otherpoint (F e) b hb₀ hb₁ hbc hep hW hqW
  rcases hh with hh|hh
  · exact (hh ⟨hzW,hza⟩).1 (hbK hzb)
  · exact hh hx (subset_closure hxU)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma face_edge_eq [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q)
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    {i j k : ι} (hij : i≠j)
    (hi : i∈regionEdges F ConnectedComponents.mk d) (hj : j∈regionEdges F ConnectedComponents.mk d)
    (hk : k∈regionEdges F ConnectedComponents.mk d)
    (hqi : q∈range (F i)) (hqj : q∈range (F j)) (hqk : q∈range (F k)) : k=i ∨ k=j := by
  by_contra hn
  push Not at hn
  let es : Fin 3 → ι := ![i,j,k]
  have hes : Function.Injective es := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [es]
  exact noncut_face_degree_two F hF P hP hq hK d es hes
    (by intro a; fin_cases a <;> assumption)
    (by intro a; fin_cases a <;> assumption)

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TamePairJordanRegions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan_regions (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ R : Bool → Set ℂ,
      (∀ i, IsOpen (R i) ∧ IsConnected (R i) ∧
        closure (R i)=R i ∪ (range a∪range b) ∧ frontier (R i)=range a∪range b) ∧
      Disjoint (R false) (R true) ∧ R false∪R true=(range a∪range b)ᶜ := by
  let K : Set ℂ := range a∪range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  let R := fun i => region Kᶜ ConnectedComponents.mk (l i)
  have hRsub (i) : R i⊆Kᶜ := region_subset _ _ _
  have hRclose (i) : closure (R i)=R i∪K := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxK : x∈K
      · exact Or.inr hxK
      · exact Or.inl (closure_region_inside hK.isOpen_compl ConnectedComponents.continuous_coe hx hxK)
    · apply union_subset subset_closure
      intro x hx
      show l i∈incident _ ConnectedComponents.mk x
      rw [hl x hx]
      exact mem_range_self i
  refine ⟨R,fun i => ⟨region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe _,
    component_region_connected _ _,hRclose i,?_⟩,
    component_regions_disjoint _ (l.injective.ne (by decide)),?_⟩
  · rw [frontier, (region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe (l i)).interior_eq,
      hRclose i]
    ext x
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hx,hn⟩
      exact hx.resolve_left hn
    · intro hx
      exact ⟨Or.inr hx,fun h => hRsub i h hx⟩
  · apply Subset.antisymm (union_subset (hRsub false) (hRsub true))
    intro x hx
    obtain ⟨i,hi⟩ := l.surjective (ConnectedComponents.mk ⟨x,hx⟩)
    cases i
    · exact Or.inl ⟨hx,hi.symm⟩
    · exact Or.inr ⟨hx,hi.symm⟩

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NoncutEdgeTwoFaces
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem noncut_edge_two_faces (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ d₀ d₁ : Faces F,d₀≠d₁ ∧ e∈regionEdges F ConnectedComponents.mk d₀ ∧
      e∈regionEdges F ConnectedComponents.mk d₁ := by
  classical
  let K := ⋃ i,range (F i)
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨b,hb₀,hb₁,hbK,⟨P,hP⟩,hab⟩ := edge_on_tame_cycle F hF Q hQ hK e
  have ha' : range (F e)⊆⋃q∈Q∪P,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hQ e hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_left P hq,hzq⟩
  have hb' : range b⊆⋃q∈Q∪P,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hP hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_right Q hq,hzq⟩
  obtain ⟨R,hR,hdis,hcov⟩ := tame_pair_jordan_regions (F e) b hb₀.symm hb₁.symm hab (Q∪P) ha' hb'
  have hsub (d : Faces F) : face F d⊆R false ∨ face F d⊆R true := by
    apply (component_region_connected Kᶜ d).isPreconnected.subset_or_subset (hR false).1 (hR true).1 hdis
    rw [hcov]
    intro z hz hh
    exact hz.1 (hh.elim (fun h=>mem_iUnion.mpr ⟨e,h⟩) (fun h=>hbK h))
  have hkey (i : Bool) {z : ℂ} (hz : z∈R i) (hzK : z∉K) :
      face F (ConnectedComponents.mk ⟨z,hzK⟩)⊆R i := by
    have hzF : z∈face F (ConnectedComponents.mk ⟨z,hzK⟩) := ⟨hzK,rfl⟩
    rcases hsub (ConnectedComponents.mk ⟨z,hzK⟩) with hh|hh
    · cases i
      · exact hh
      · exact False.elim (disjoint_left.mp hdis (hh hzF) hz)
    · cases i
      · exact False.elim (disjoint_left.mp hdis hz (hh hzF))
      · exact hh
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : (0:I)<t := by change (0:ℝ)<1/2; norm_num
  have ht₁ : t<(1:I) := by change (1/2:ℝ)<1; norm_num
  have hfind (i : Bool) : ∃ d : Faces F,face F d⊆R i ∧ F e t∈closure (face F d) := by
    let B : Set (Faces F) := {d | face F d⊆R i}
    let T := ⋃ d∈B,closure (face F d)
    have hT : IsClosed T := isClosed_iUnion_of_finite fun d=>isClosed_iUnion_of_finite fun _=>isClosed_closure
    have hd : Dense (Kᶜ : Set ℂ) :=
      (complex_finite_segments_compl_dense Q).mono (compl_subset_compl.mpr (iUnion_subset hQ))
    have hinc : R i∩Kᶜ⊆T := by
      intro z hz
      exact mem_iUnion₂.mpr ⟨ConnectedComponents.mk ⟨z,hz.2⟩,hkey i hz.1 hz.2,subset_closure ⟨hz.2,rfl⟩⟩
    have hRT : R i⊆T := by
      intro z hz
      exact closure_minimal hinc hT ((hR i).1.inter_closure ⟨hz,hd z⟩)
    have hx : F e t∈closure (R i) := by
      rw [(hR i).2.2.1]
      exact Or.inr (Or.inl (mem_range_self t))
    obtain ⟨d,hd,hx⟩ := mem_iUnion₂.mp (closure_minimal hRT hT hx)
    exact ⟨d,hd,hx⟩
  obtain ⟨d₀,hd₀,hx₀⟩ := hfind false
  obtain ⟨d₁,hd₁,hx₁⟩ := hfind true
  refine ⟨d₀,d₁,?_,⟨t,ht₀,ht₁,hx₀⟩,⟨t,ht₀,ht₁,hx₁⟩⟩
  intro he
  obtain ⟨z,hz⟩ := face_nonempty F d₀
  exact disjoint_left.mp hdis (hd₀ hz) (hd₁ (he ▸ hz))

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FacialStar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma facial_closures_cover (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) :
    ∀ x : ℂ,∃ d : Faces F,x∈closure (face F d) := by
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  have hd : Dense ((⋃ i,range (F i))ᶜ : Set ℂ) := (complex_finite_segments_compl_dense Q).mono (by
    intro x hx hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hx (hQ i hi))
  have hC : IsClosed (⋃ d : Faces F,closure (face F d)) :=
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hsub : (⋃ i,range (F i))ᶜ⊆⋃ d : Faces F,closure (face F d) := by
    intro x hx
    refine mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨x,hx⟩,subset_closure ?_⟩
    exact ⟨hx,rfl⟩
  intro x
  exact mem_iUnion.mp ((closure_minimal hsub hC) (hd x))

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_IncidentFaces
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler CannonVertexLinks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem vertexFaceGraph_preconnected [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q) : (vertexFaceGraph F q).Preconnected := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨rF,hrF,hnearF⟩ := finite_closed_local (fun d : Faces F=>closure (face F d))
    (fun _=>isClosed_closure) q
  obtain ⟨rE,hrE,hnearE⟩ := finite_closed_local (fun i=>range (F i))
    (fun i=>(F i).compact_range.isClosed) q
  obtain ⟨rV,hrV,hnearV⟩ := finite_closed_local
    (fun v : (vertices F Finset.univ : Set ℂ)=>({v.val}:Set ℂ)) (fun _=>isClosed_singleton) q
  choose w hw using face_nonempty F
  have hqw (d : Faces F) : 0<dist (w d) q := by
    apply dist_pos.mpr
    intro h
    exact (hw d).1 (h.symm ▸ vertex_mem_support F hq)
  obtain ⟨rW,hrW,hfar⟩ := finite_pos_lower (fun d=>dist (w d) q) hqw
  let r := min (min rF rE) (min rV rW)/2
  have hr : 0 < r := half_pos (lt_min (lt_min hrF hrE) (lt_min hrV hrW))
  have hsmall : r < rF ∧ r < rE ∧ r < rV ∧ r < rW := by
    have ht : r < min (min rF rE) (min rV rW) := half_lt_self (lt_min (lt_min hrF hrE) (lt_min hrV hrW))
    exact ⟨ht.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
      ht.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
      ht.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  let C (d : IncidentFaces F q) : Set ℂ := sphere q r∩closure (face F d.val)
  have hcover : (⋃d,C d)=sphere q r := by
    apply Subset.antisymm
    · exact iUnion_subset fun _=>inter_subset_left
    · intro z hz
      obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ z
      have hqd := hnearF z (show z∈ball q rF from by rw [mem_ball,(mem_sphere.mp hz)]; exact hsmall.1) d hd
      exact mem_iUnion.mpr ⟨⟨d,hqd⟩,hz,hd⟩
  have hne (d : IncidentFaces F q) : (C d).Nonempty := by
    obtain ⟨z,hz,hzdist⟩ := Metric.mem_closure_iff.mp d.property r hr
    have hc : IsPreconnected (face F d.val) := (component_region_connected _ d.val).isPreconnected
    obtain ⟨y,hy,hyd⟩ := hc.intermediate_value hz (hw d.val)
      (continuous_id.dist continuous_const).continuousOn
      (show r∈Icc (dist z q) (dist (w d.val) q) from
        ⟨by rw [dist_comm]; exact hzdist.le,(hsmall.2.2.2.trans (hfar d.val)).le⟩)
    exact ⟨y,mem_sphere.mpr hyd,subset_closure hy⟩
  refine CannonClosedCover.graph_preconnected (vertexFaceGraph F q) C
    (fun _=>isClosed_sphere.inter isClosed_closure) ?_ hne ?_
  · rw [hcover]
    exact (isConnected_sphere (E:=ℂ) (by rw [Complex.rank_real_complex]; norm_num) q hr.le).isPreconnected
  intro d c hdc ⟨z,hzd,hzc⟩
  have hzq : z≠q := by intro h; have he := mem_sphere.mp hzd.1; rw [h,dist_self] at he; linarith
  have hzV : ¬Vertex F z := by
    intro hz
    obtain ⟨i,hi⟩ := hz
    have hv : z∈vertices F Finset.univ := (mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hi⟩
    have hqz := hnearV z (by rw [mem_ball,mem_sphere.mp hzd.1]; exact hsmall.2.2.1) ⟨z,hv⟩ rfl
    exact hzq hqz.symm
  have hzK : z∈⋃i,range (F i) := by
    by_contra hn
    have get (a : Faces F) (ha : z∈closure (face F a)) : z∈face F a := by
      change z∈closure (region ((⋃ i,range (F i))ᶜ) ConnectedComponents.mk a) at ha
      rw [tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe a] at ha
      rcases ha with h|h
      · exact h
      · obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp h
        exact (hn (mem_iUnion.mpr ⟨i,hi⟩)).elim
    have hd := get d.val hzd.2
    have hc := get c.val hzc.2
    exact hdc (Subtype.ext (hd.2.symm.trans hc.2))
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzK
  have ht₀ : 0<t := by
    apply lt_of_le_of_ne (nonneg t)
    intro he
    exact hzV ⟨i,Or.inl (congrArg (F i) (show (0:I)=t from Subtype.ext he))⟩
  have ht₁ : t<1 := by
    apply lt_of_le_of_ne (le_one t)
    intro he
    exact hzV ⟨i,Or.inr (congrArg (F i) (show (1:I)=t from Subtype.ext he.symm))⟩
  refine ⟨hdc,i,?_,⟨t,ht₀,ht₁,hzd.2⟩,⟨t,ht₀,ht₁,hzc.2⟩⟩
  exact hnearE (F i t) (by rw [mem_ball,mem_sphere.mp hzd.1]; exact hsmall.2.1) i (mem_range_self t)
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma edge_face_unique_two [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (i : ι) {a b c : Faces F} (hab : a≠b)
    (ha : i∈regionEdges F ConnectedComponents.mk a)
    (hb : i∈regionEdges F ConnectedComponents.mk b)
    (hc : i∈regionEdges F ConnectedComponents.mk c) : c=a ∨ c=b := by
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨labels,hlabels⟩ := tame_edge_incident_labels F hF Q hQ ConnectedComponents.continuous_coe i
  have get (d : Faces F) (hd : i∈regionEdges F ConnectedComponents.mk d) : ∃ b,labels b=d := by
    obtain ⟨t,ht₀,ht₁,ht⟩ := hd
    have : d∈incident _ ConnectedComponents.mk (F i t) := ht
    rwa [hlabels t ht₀ ht₁] at this
  obtain ⟨u,hu⟩ := get a ha
  obtain ⟨v,hv⟩ := get b hb
  obtain ⟨w,hw⟩ := get c hc
  cases u <;> cases v <;> cases w <;> simp_all

theorem vertexLink_isCycles (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    {q : ℂ} (hq : Vertex F q) : (vertexLink F q).IsCycles := by
  classical
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  intro x hx
  cases x with
  | inl i =>
    obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i.val
    let a' : IncidentFaces F q := ⟨a,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha i.property⟩
    let b' : IncidentFaces F q := ⟨b,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hb i.property⟩
    apply Set.ncard_eq_two.mpr
    refine ⟨Sum.inr a',Sum.inr b',?_,?_⟩
    · intro h; exact hab (congrArg Subtype.val (Sum.inr.inj h))
    · ext z
      cases z with
      | inl j => simp [vertexLink]
      | inr d =>
        change (i.val∈regionEdges F ConnectedComponents.mk d.val) ↔ _
        constructor
        · intro hd
          rcases edge_face_unique_two F hF Q hQ i.val hab ha hb hd with h|h
          · exact Or.inl (congrArg Sum.inr (Subtype.ext h))
          · exact Or.inr (congrArg Sum.inr (Subtype.ext h))
        · rintro (h|h)
          · have hd : d=a' := Sum.inr.inj h
            exact hd.symm ▸ ha
          · have hd : d=b' := Sum.inr.inj h
            exact hd.symm ▸ hb
  | inr d =>
    obtain ⟨z,hz⟩ := hx
    cases z with
    | inr c => exact hz.elim
    | inl i =>
      obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF Q hQ hK d.val hq hz i.property
      let j' : IncidentEdges F q := ⟨j,hqj⟩
      apply Set.ncard_eq_two.mpr
      refine ⟨Sum.inl i,Sum.inl j',?_,?_⟩
      · intro h; exact hji (congrArg Subtype.val (Sum.inl.inj h)).symm
      · ext z
        cases z with
        | inr c => simp [vertexLink]
        | inl k =>
          change (k.val∈regionEdges F ConnectedComponents.mk d.val) ↔ _
          constructor
          · intro hk
            rcases face_edge_eq F hF Q hQ hq (hK q) d.val hji.symm hz hj hk i.property hqj k.property with h|h
            · exact Or.inl (congrArg Sum.inl (Subtype.ext h))
            · exact Or.inr (congrArg Sum.inl (Subtype.ext h))
          · rintro (h|h)
            · have hk : k=i := Sum.inl.inj h
              exact hk.symm ▸ hz
            · have hk : k=j' := Sum.inl.inj h
              exact hk.symm ▸ hj

theorem vertexLink_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    {q : ℂ} (hq : Vertex F q) : (vertexLink F q).Preconnected := by
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hins (a b : IncidentFaces F q) : (vertexLink F q).Reachable (.inr a) (.inr b) := by
    obtain ⟨p⟩ := vertexFaceGraph_preconnected F hF Q hQ hq a b
    induction p with
    | nil => exact .rfl
    | @cons a b c h p ih =>
      obtain ⟨-,i,hi,ha,hb⟩ := h
      exact ((show (vertexLink F q).Adj (.inr a) (.inl ⟨i,hi⟩) from ha).reachable.trans
        (show (vertexLink F q).Adj (.inl ⟨i,hi⟩) (.inr b) from hb).reachable).trans ih
  have hface (x : IncidentEdges F q ⊕ IncidentFaces F q) :
      ∃ a : IncidentFaces F q,(vertexLink F q).Reachable x (.inr a) := by
    cases x with
    | inr a => exact ⟨a,.rfl⟩
    | inl i =>
      obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i.val
      let a' : IncidentFaces F q := ⟨a,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha i.property⟩
      exact ⟨a',(show (vertexLink F q).Adj (.inl i) (.inr a') from ha).reachable⟩
  intro x y
  obtain ⟨a,ha⟩ := hface x
  obtain ⟨b,hb⟩ := hface y
  exact (ha.trans (hins a b)).trans hb.symm
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_VertexLinkOrder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem vertexLink_order (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    {q : ℂ} (hq : Vertex F q) :
    ∃ n:ℕ,∃ hn:0<n,∃ e:Fin n≃IncidentEdges F q,∃ a:Fin n≃IncidentFaces F q,
      2≤n ∧ (∀ i,(e i).val∈regionEdges F ConnectedComponents.mk (a i).val) ∧
      (∀ i,(e (CannonCycleOrder.next hn i)).val∈regionEdges F ConnectedComponents.mk (a i).val) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hgraph : CannonCycleOrder.bipartite
      (fun (e : IncidentEdges F q) (a : IncidentFaces F q)=>e.val∈regionEdges F ConnectedComponents.mk a.val)=vertexLink F q := by
    ext x y; cases x <;> cases y <;> rfl
  apply CannonCycleOrder.exists_order
    (fun (e : IncidentEdges F q) (a : IncidentFaces F q)=>e.val∈regionEdges F ConnectedComponents.mk a.val)
    (by rw [hgraph]; exact vertexLink_isCycles F hF Q hQ hK hq)
    (by rw [hgraph]; exact vertexLink_preconnected F hF Q hQ hK hq)
  obtain ⟨i,hi⟩ := hq
  have hqi : q∈range (F i) := hi.elim (fun h=>h ▸ ⟨0,rfl⟩) (fun h=>h ▸ ⟨1,rfl⟩)
  obtain ⟨face,_,_,hface,_⟩ := noncut_edge_two_faces F hF Q hQ hK i
  have hqa := region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hface hqi
  exact ⟨⟨i,hqi⟩,⟨face,hqa⟩,hface⟩
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceHullCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

lemma face_incidence_card_le_oai
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (N : ℕ)
    (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (F i)}≤N) (v : ℂ) :
    (Finset.univ.filter (fun d : Faces F=>v∈faceVertices F d)).card≤N := by
  classical
  by_cases hv : Vertex F v
  · obtain ⟨n,hn,e,a,-⟩:=vertexLink_order F hF Q hQ hK hv
    have he : Nat.card (IncidentFaces F v)=Nat.card (IncidentEdges F v):=
      Nat.card_congr (a.symm.trans e)
    let eqv : {d : Faces F // v∈faceVertices F d}≃IncidentFaces F v :=
      { toFun:=fun d=>⟨d.val,((mem_faceVertices F d.val v).mp d.property).2⟩
        invFun:=fun d=>⟨d.val,(mem_faceVertices F d.val v).mpr ⟨hv,d.property⟩⟩
        left_inv:=fun _=>rfl
        right_inv:=fun _=>rfl }
    have hc : Nat.card {d : Faces F // v∈faceVertices F d}≤N:=
      (Nat.card_congr eqv).trans he ▸ hdeg v
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
  · have he : ∀ d : Faces F,v∉faceVertices F d:=fun d hh=>hv ((mem_faceVertices F d v).mp hh).1
    simp [he]

end CannonEmbeddedArc.Arc

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonEmbeddedArc.Arc.face_incidence_card_le_oai.{u_1} := @OAI.CannonEmbeddedArc.Arc.face_incidence_card_le_oai.{u_1}
