-- Prove2me | solution 1 for OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:01:09.729707+00:00
-- url     : https://prove2.me/submissions/9f569444-d31f-4282-847b-63dcbb0a8b87

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
-- module Solutions.OAIQ046_CN.Cannon_Boundary_GraphReachableCover
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

theorem graph_reachable_cover (G : SimpleGraph ι) (C : ι → Set X)
    (hclosed : ∀ i,IsClosed (C i))
    (hconn : IsPreconnected (⋃ i,C i)) (hne : ∀ i,(C i).Nonempty)
    (hadj : ∀ i j,(C i∩C j).Nonempty → G.Reachable i j) : G.Preconnected := by
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
  obtain ⟨z,-,hzU,hzV⟩ := isPreconnected_closed_iff.mp hconn U V hU hV hsub
    ⟨x,mem_iUnion.mpr ⟨a,hx⟩,mem_iUnion.mpr ⟨⟨a,.rfl⟩,hx⟩⟩
    ⟨y,mem_iUnion.mpr ⟨b,hy⟩,mem_iUnion.mpr ⟨⟨b,hb⟩,hy⟩⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzU
  obtain ⟨j,hj⟩ := mem_iUnion.mp hzV
  exact j.property (i.property.trans (hadj _ _ ⟨z,hi,hj⟩))

omit [Finite ι] in
theorem union_preconnected (G : SimpleGraph ι) (hG : G.Preconnected)
    (C : ι → Set X) (hc : ∀ i,IsPreconnected (C i)) (hne : ∀ i,(C i).Nonempty)
    (hadj : ∀ i j,G.Adj i j → (C i∩C j).Nonempty) : IsPreconnected (⋃ i,C i) := by
  classical
  choose z hz using hne
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hconst (i : ι) {x y : X} (hx:x∈C i) (hy:y∈C i) : f x=f y :=
    (hc i).constant (hf.mono (subset_iUnion C i)) hx hy
  have hstep (i j:ι) (hij:G.Adj i j) : f (z i)=f (z j) := by
    obtain ⟨w,hwi,hwj⟩ := hadj i j hij
    exact (hconst i (hz i) hwi).trans (hconst j hwj (hz j))
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp hy
  have hwalk {a b:ι} (p:G.Walk a b) : f (z a)=f (z b) := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (hstep _ _ h).trans ih
  obtain ⟨p⟩ := hG i j
  exact (hconst i hi (hz i)).trans ((hwalk p).trans (hconst j (hz j) hj))
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
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_EdgeGraph
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
namespace CannonForest
open Set

theorem empty_of_no_leaves {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (hother : ∀ x y,G.Adj x y → ∃ z,G.Adj x z ∧ z≠y) : G=⊥ := by
  classical
  ext x y
  constructor
  · intro hxy
    let c := G.connectedComponentMk x
    let a : c.supp := ⟨x,rfl⟩
    let b : c.supp := ⟨y,SimpleGraph.ConnectedComponent.sound hxy.reachable.symm⟩
    have hab : a≠b := fun h=>hxy.ne (congrArg Subtype.val h)
    let _ : Nontrivial c.supp := ⟨⟨a,b,hab⟩⟩
    let _ : Fintype c.supp := Fintype.ofFinite c.supp
    obtain ⟨v,hv⟩ := (hG.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
    obtain ⟨w,hw,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    have hval : G.Adj v.val w.val := hw
    obtain ⟨z,hz,hzw⟩ := hother v.val w.val hval
    have hzc : z∈c.supp := c.mem_supp_of_adj_mem_supp v.property hz
    let z' : c.supp := ⟨z,hzc⟩
    have hvz : c.toSimpleGraph.Adj v z' := hz
    exact (hzw (congrArg Subtype.val (hunique _ hvz))).elim
  · exact False.elim
end CannonForest

end
end
section
noncomputable section
namespace CannonGraphGauge
open Set

variable {V E D : Type*} [Fintype E] [Group D]

theorem exists_connected_good (a b:E→V) (hneq:∀i,a i≠b i) (K:E→D)
    (hconn:(edgeGraph a b hneq univ).Preconnected) :
    ∃ v:V→D,(edgeGraph a b hneq (goodEdges a b K v : Set E)).Preconnected := by
  classical
  let S : Finset (Finset E) := Finset.univ.filter fun A=>∃ v:V→D,goodEdges a b K v=A
  have hS : S.Nonempty := ⟨goodEdges a b K (fun _=>1),by simp [S]⟩
  obtain ⟨A,hAS,hmax⟩ := Finset.exists_max_image S Finset.card hS
  obtain ⟨v,rfl⟩ := (Finset.mem_filter.mp hAS).2
  have hmaxv (w:V→D) : (goodEdges a b K w).card≤(goodEdges a b K v).card :=
    hmax _ (by simp [S])
  let H := edgeGraph a b hneq (goodEdges a b K v : Set E)
  have hreach (i:E) : H.Reachable (a i) (b i) := by
    by_contra hn
    let C (x:V) : Prop := H.Reachable (a i) x
    let γ := (K i*v (a i))⁻¹*v (b i)
    let w (x:V) : D := if C x then v x*γ else v x
    have hpres : goodEdges a b K v⊆goodEdges a b K w := by
      intro j hj
      have hadj : H.Adj (a j) (b j) := ⟨j,hj,Or.inl ⟨rfl,rfl⟩⟩
      have hc : C (a j)↔C (b j) :=
        ⟨fun h=>h.trans hadj.reachable,fun h=>h.trans hadj.reachable.symm⟩
      apply (mem_goodEdges ..).mpr
      have he := (mem_goodEdges a b K v j).mp hj
      by_cases ha : C (a j)
      · simp only [w,ite_eq_left ha,ite_eq_left (hc.mp ha),←mul_assoc,he]
      · simp only [w,ite_eq_right ha,ite_eq_right (mt hc.mpr ha),he]
    have hiw : i∈goodEdges a b K w := by
      apply (mem_goodEdges ..).mpr
      have hai : C (a i) := .rfl
      have hbi : ¬C (b i) := hn
      simp [w,hai,hbi,γ,←mul_assoc]
    have hiv : i∉goodEdges a b K v := by
      intro hi
      exact hn (show H.Adj (a i) (b i) from ⟨i,hi,Or.inl ⟨rfl,rfl⟩⟩).reachable
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hpres,fun he=>hiv (he ▸ hiw)⟩)
    exact (not_lt_of_ge (hmaxv w)) hlt
  refine ⟨v,?_⟩
  intro x y
  obtain ⟨p⟩ := hconn x y
  induction p with
  | nil => exact .rfl
  | @cons x y z h p ih =>
    obtain ⟨i,-,h|h⟩ := h
    · exact (h.1 ▸ h.2 ▸ hreach i).trans ih
    · exact (h.2 ▸ h.1 ▸ (hreach i).symm).trans ih

theorem exists_connected_good_restrict (a b:E→V) (hneq:∀i,a i≠b i) (K:E→D)
    (R:Set E) (hconn:(edgeGraph a b hneq R).Preconnected) :
    ∃ v:V→D,(edgeGraph a b hneq (R∩(goodEdges a b K v : Set E))).Preconnected := by
  classical
  let I := {i // i∈R}
  let _ : Fintype I := Fintype.ofFinite I
  let a' : I→V := fun i=>a i.val
  let b' : I→V := fun i=>b i.val
  have hab' : ∀ i:I,a' i≠b' i := fun i=>hneq i.val
  have heq0 : edgeGraph a' b' hab' univ=edgeGraph a b hneq R := by
    ext x y
    constructor
    · rintro ⟨i,-,h⟩; exact ⟨i.val,i.property,h⟩
    · rintro ⟨i,hi,h⟩; exact ⟨⟨i,hi⟩,mem_univ _,h⟩
  obtain ⟨v,hv⟩ := exists_connected_good a' b' hab' (fun i=>K i.val) (heq0 ▸ hconn)
  refine ⟨v,?_⟩
  have heq : edgeGraph a' b' hab' (goodEdges a' b' (fun i=>K i.val) v : Set I)=
      edgeGraph a b hneq (R∩(goodEdges a b K v : Set E)) := by
    ext x y
    constructor
    · rintro ⟨i,hi,h⟩
      exact ⟨i.val,⟨i.property,by simpa [a',b'] using hi⟩,h⟩
    · rintro ⟨i,⟨hi,hg⟩,h⟩
      exact ⟨⟨i,hi⟩,by simpa [a',b'] using hg,h⟩
  rwa [heq] at hv

theorem label_equal_of_other_edges {W Z : Type*} [Finite W] (G:SimpleGraph W)
    (hG:G.IsCycles) {a b:W} (hab:G.Adj a b) (f:W→Z)
    (hother:∀x y,G.Adj x y → s(x,y)≠s(a,b) → f x=f y) : f a=f b := by
  obtain ⟨p⟩ := hG.reachable_deleteEdges hab
  have hw {x y:W} (p:(G.deleteEdges {s(a,b)}).Walk x y) : f x=f y := by
    induction p with
    | nil => rfl
    | @cons x y z h p ih =>
      have hx : G.Adj x y ∧ s(x,y)∉({s(a,b)}:Set (Sym2 W)) := SimpleGraph.deleteEdges_adj.mp h
      exact (hother x y hx.1 (by simpa using hx.2)).trans ih
  exact hw p
end CannonGraphGauge

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_EdgesConfinedCore
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
namespace CannonForest
open Set

theorem edges_confined_to_core {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Set V) (hS : (G.induce S).Preconnected)
    (hother : ∀ x∉S,∀ y,G.Adj x y → ∃ z,G.Adj x z ∧ z≠y) :
    ∀ x y,G.Adj x y → x∈S ∧ y∈S := by
  classical
  let R : SimpleGraph V := {
    Adj := fun x y=>G.Adj x y ∧ ¬(x∈S ∧ y∈S)
    symm := ⟨fun x y h=>⟨h.1.symm,fun hh=>h.2 hh.symm⟩⟩
    loopless := ⟨fun x h=>h.1.ne rfl⟩ }
  have hRG : R≤G := fun _ _ h=>h.1
  have acR := hG.anti hRG
  have unique_core {x y:V} (hx:x∈S) (hy:y∈S) (hxy:R.Reachable x y) : x=y := by
    by_contra hn
    obtain ⟨p,hp⟩ := hxy.exists_isPath
    obtain ⟨q,hq⟩ := (hS ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
    let f : G.induce S →g G := ⟨Subtype.val,fun h=>h⟩
    have he : p.mapLe hRG=q.map f := Subtype.mk.inj
      (hG.subsingleton_path x y |>.elim ⟨_,hp.mapLe hRG⟩ ⟨_,hq.map Subtype.val_injective⟩)
    have hs : ∀ z∈p.support,z∈S := by
      intro z hz
      have hz' : z∈(p.mapLe hRG).support := by simpa using hz
      rw [he,SimpleGraph.Walk.support_map] at hz'
      obtain ⟨w,-,rfl⟩ := List.mem_map.mp hz'
      exact w.property
    have hpne : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hn
    exact (p.adj_snd hpne).2 ⟨hx,hs _ (List.mem_of_mem_tail (p.snd_mem_tail_support hpne))⟩
  have hempty : R=⊥ := by
    ext x y
    constructor
    · intro hxy
      let c := R.connectedComponentMk x
      let a : c.supp := ⟨x,rfl⟩
      let b : c.supp := ⟨y,SimpleGraph.ConnectedComponent.sound hxy.reachable.symm⟩
      have hab : a≠b := fun h=>hxy.ne (congrArg Subtype.val h)
      let _ : Nontrivial c.supp := ⟨⟨a,b,hab⟩⟩
      let _ : Fintype c.supp := Fintype.ofFinite c.supp
      obtain ⟨u,v,huv,hu,hv⟩ := (acR.isTree_connectedComponent c).exists_ne_and_degree_eq_one
      have leaves (z : c.supp) (hz : c.toSimpleGraph.degree z=1) : z.val∈S := by
        by_contra hn
        obtain ⟨w,hw,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
        have hwG : G.Adj z.val w.val := hRG hw
        obtain ⟨t,ht,htw⟩ := hother z.val hn w.val hwG
        have htR : R.Adj z.val t := ⟨ht,fun h=>hn h.1⟩
        let t' : c.supp := ⟨t,c.mem_supp_of_adj_mem_supp z.property htR⟩
        have hadj : c.toSimpleGraph.Adj z t' := htR
        exact htw (congrArg Subtype.val (hunique _ hadj))
      have huvR : R.Reachable u.val v.val :=
        SimpleGraph.ConnectedComponent.exact (u.property.trans v.property.symm)
      exact huv (Subtype.ext (unique_core (leaves u hu) (leaves v hv) huvR))
    · exact False.elim
  intro x y hxy
  by_contra hn
  have h : R.Adj x y := ⟨hxy,hn⟩
  rw [hempty] at h
  exact h
end CannonForest

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

lemma Spans.mem_left {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : x∈range a := by
  rcases h with h|h
  · exact ⟨0,h.1⟩
  · exact ⟨1,h.1⟩
lemma Spans.mem_right {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : y∈range a := h.symm.mem_left
lemma Spans.vertex_left [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F x :=
  ⟨i,h.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)⟩
lemma Spans.vertex_right [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F y :=
  h.symm.vertex_left
lemma Spans.other_unique {a : Arc ℂ} {x y z : ℂ} (h : Spans a x y) (h' : Spans a x z) : y=z := by
  rcases h with h|h <;> rcases h' with h'|h'
  · exact h.2.symm.trans h'.2
  · exact (a.endpoints_ne (h.1.trans h'.1.symm)).elim
  · exact (a.endpoints_ne (h'.1.trans h.1.symm)).elim
  · exact h.2.symm.trans h'.2
lemma spans_edge_unique [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {i j : ι} {x y : ℂ}
    (hi : Spans (F i) x y) (hj : Spans (F j) x y) : i=j := by
  by_contra hn
  exact hi.ne ((hF hn).2 ⟨hi.mem_left,hj.mem_left⟩ ⟨hi.mem_right,hj.mem_right⟩)
lemma vertex_spans [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {q : ℂ}
    (hq : Vertex F q) {i : ι} (hi : q∈range (F i)) : ∃ z,Spans (F i) q z := by
  obtain ⟨t,ht⟩ := hi
  rcases vertex_parameter F hF i (ht.symm ▸ hq) with h|h
  · exact ⟨F i 1,Or.inl ⟨h ▸ ht,rfl⟩⟩
  · exact ⟨F i 0,Or.inr ⟨h ▸ ht,rfl⟩⟩

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

theorem facial_graph_isCycles [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    (edgeGraph F (regionEdges F ConnectedComponents.mk d)).IsCycles := by
  intro x ⟨y,i,hi,hiy⟩
  obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF P hP hK d x.property hi hiy.mem_left
  obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hqj
  let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
  have hyz : y≠z' := by
    intro h
    exact hji (spans_edge_unique F hF (show Spans (F j) x.val y.val from (congrArg Subtype.val h).symm ▸ hjz) hiy)
  apply Set.ncard_eq_two.mpr
  refine ⟨y,z',hyz,?_⟩
  ext w
  constructor
  · rintro ⟨k,hk,hkw⟩
    rcases face_edge_eq F hF P hP x.property (hK x.val) d hji.symm hi hj hk
      hiy.mem_left hqj hkw.mem_left with h|h
    · subst k
      exact Or.inl (Subtype.ext (hkw.other_unique hiy))
    · subst k
      exact Or.inr (Subtype.ext (hkw.other_unique hjz))
  · rintro (rfl|rfl)
    · exact ⟨i,hi,hiy⟩
    · exact ⟨j,hj,hjz⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma edgeKey_eq [Finite ι] (F : ι → Arc ℂ) (i : ι) (x y : GraphVertices F) :
    edgeKey F i=s(x,y) ↔ Spans (F i) x.val y.val := by
  simp only [edgeKey,Sym2.eq_iff,Subtype.ext_iff,edgeStart,edgeEnd,Spans]
  tauto

lemma edgeKey_injective [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) : Function.Injective (edgeKey F) := by
  intro i j hij
  exact spans_edge_unique F hF (show Spans (F i) (F i 0) (F i 1) from Or.inl ⟨rfl,rfl⟩)
    ((edgeKey_eq F j (edgeStart F i) (edgeEnd F i)).mp hij.symm)

lemma walkCarrier_cons [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y z : GraphVertices F} (h : (edgeGraph F E).Adj x y) (w : (edgeGraph F E).Walk y z)
    {i : ι} (hi : Spans (F i) x.val y.val) : walkCarrier F (w.cons h)=range (F i)∪walkCarrier F w := by
  have hk := (edgeKey_eq F i x y).mpr hi
  ext p
  simp only [walkCarrier,mem_ofPred_eq,SimpleGraph.Walk.edges_cons,List.mem_cons,mem_union]
  constructor
  · rintro ⟨j,(hj|hj),hp⟩
    · have he := edgeKey_injective F hF (hj.trans hk.symm)
      exact Or.inl (he ▸ hp)
    · exact Or.inr ⟨j,hj,hp⟩
  · rintro (hp|⟨j,hj,hp⟩)
    · exact ⟨i,Or.inl hk,hp⟩
    · exact ⟨j,Or.inr hj,hp⟩

lemma walkCarrier_vertex [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y q : GraphVertices F} {w : (edgeGraph F E).Walk x y} (hq : q.val∈walkCarrier F w) : q∈w.support := by
  obtain ⟨i,hi,t,ht⟩ := hq
  rcases vertex_parameter F hF i (ht.symm ▸ q.property) with h|h
  · have he : edgeStart F i=q := Subtype.ext ((congrArg (F i) h).symm.trans ht)
    exact he ▸ w.fst_mem_support_of_mem_edges hi
  · have he : edgeEnd F i=q := Subtype.ext ((congrArg (F i) h).symm.trans ht)
    exact he ▸ w.snd_mem_support_of_mem_edges hi

lemma oriented_arc {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) :
    ∃ b : Arc ℂ,b 0=x ∧ b 1=y ∧ range b=range a := by
  rcases h with h|h
  · exact ⟨a,h.1,h.2,rfl⟩
  · exact ⟨a.reverse,by simpa using h.1,by simpa using h.2,a.reverse_range⟩

theorem simple_walk_arc [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) (hw : w.IsPath) (hne : x≠y) :
    ∃ a : Arc ℂ,a 0=x.val ∧ a 1=y.val ∧ range a=walkCarrier F w := by
  induction w with
  | nil => exact (hne rfl).elim
  | @cons x v y h w ih =>
    have hed : ∃ i∈E,Spans (F i) x.val v.val := h
    obtain ⟨i,_hi,hix⟩ := hed
    obtain ⟨a,ha₀,ha₁,ha⟩ := oriented_arc hix
    have hw' := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hw
    by_cases hvy : v=y
    · subst y
      have hn : w.Nil := SimpleGraph.Walk.isPath_iff_nil.mp hw'.1
      cases hn
      refine ⟨a,ha₀,ha₁,?_⟩
      rw [walkCarrier_cons F hF _ _ hix,ha]
      simp [walkCarrier]
    · obtain ⟨b,hb₀,hb₁,hb⟩ := ih hw'.1 hvy
      have hmeet : ∀ s t,a s=b t → s=1 ∧ t=0 := by
        intro s t he
        have hbs : b t∈walkCarrier F w := hb ▸ mem_range_self t
        obtain ⟨j,hj,u,hju⟩ := hbs
        have hji : j≠i := by
          intro hji
          subst j
          have hk := (edgeKey_eq F i x v).mpr hix
          exact hw'.2 (w.fst_mem_support_of_mem_edges (hk ▸ hj))
        obtain ⟨r,hr⟩ := ha ▸ (mem_range_self s : a s∈range a)
        have hrj : F i r=F j u := hr.trans (he.trans hju.symm)
        have hre := ((hF hji.symm).1 r u hrj).1
        have hax : a s=x.val ∨ a s=v.val := by
          rcases hre with rfl|rfl <;> rcases hix with hix|hix
          · exact Or.inl (hr.symm.trans hix.1)
          · exact Or.inr (hr.symm.trans hix.2)
          · exact Or.inr (hr.symm.trans hix.2)
          · exact Or.inl (hr.symm.trans hix.1)
        have hav : a s=v.val := hax.resolve_left (by
          intro hx
          apply hw'.2
          apply walkCarrier_vertex F hF (q:=x)
          exact (he.symm.trans hx) ▸ (hb ▸ mem_range_self t))
        exact ⟨a.injective (hav.trans ha₁.symm),b.injective (he.symm.trans (hav.trans hb₀.symm))⟩
      let pa : Path x.val v.val := a.path.cast ha₀.symm ha₁.symm
      let pb : Path v.val y.val := b.path.cast hb₀.symm hb₁.symm
      let c : Arc ℂ := ⟨(pa.trans pb).toContinuousMap,
        trans_injective pa pb a.injective b.injective hmeet⟩
      refine ⟨c,(pa.trans pb).source,(pa.trans pb).target,?_⟩
      change range (pa.trans pb)=_
      rw [Path.trans_range,walkCarrier_cons F hF _ _ hix]
      exact congrArg₂ (·∪·) ha hb
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

theorem simple_cycle_arcs [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x : GraphVertices F} (p : (edgeGraph F E).Walk x x) (hp : p.IsCycle) :
    ∃ a b : Arc ℂ,a 0=b 0 ∧ a 1=b 1 ∧
      (∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      range a∪range b=walkCarrier F p := by
  cases p with
  | nil => exact (hp.not_nil (by simp)).elim
  | @cons x v x h p =>
    have hed : ∃ i∈E,Spans (F i) x.val v.val := h
    obtain ⟨i,_hi,hix⟩ := hed
    obtain ⟨a,ha₀,ha₁,ha⟩ := oriented_arc hix
    have hp' := (p.cons_isCycle_iff h).mp hp
    obtain ⟨c,hc₀,hc₁,hc⟩ := simple_walk_arc F hF p hp'.1 h.ne.symm
    let b := c.reverse
    have hb₀ : b 0=x.val := by simpa only [b,reverse_zero] using hc₁
    have hb₁ : b 1=v.val := by simpa only [b,reverse_one] using hc₀
    have hb : range b=walkCarrier F p := c.reverse_range.trans hc
    refine ⟨a,b,ha₀.trans hb₀.symm,ha₁.trans hb₁.symm,?_,?_⟩
    · intro s t he
      obtain ⟨j,hj,u,hju⟩ := (show b t∈walkCarrier F p from hb ▸ mem_range_self t)
      have hji : j≠i := by
        intro hji
        subst j
        exact hp'.2 ((edgeKey_eq F i x v).mpr hix ▸ hj)
      obtain ⟨r,hr⟩ := ha ▸ (mem_range_self s : a s∈range a)
      have hre := ((hF hji.symm).1 r u (hr.trans (he.trans hju.symm))).1
      have hav : a s=x.val ∨ a s=v.val := by
        rcases hre with rfl|rfl <;> rcases hix with hix|hix
        · exact Or.inl (hr.symm.trans hix.1)
        · exact Or.inr (hr.symm.trans hix.2)
        · exact Or.inr (hr.symm.trans hix.2)
        · exact Or.inl (hr.symm.trans hix.1)
      rcases hav with hx|hv
      · exact ⟨Or.inl (a.injective (hx.trans ha₀.symm)),Or.inl (b.injective (he.symm.trans (hx.trans hb₀.symm)))⟩
      · exact ⟨Or.inr (a.injective (hv.trans ha₁.symm)),Or.inr (b.injective (he.symm.trans (hv.trans hb₁.symm)))⟩
    · rw [ha,hb,walkCarrier_cons F hF h p hix]

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

omit [Nonempty ι] in
theorem noncut_facial_vertices_edges (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    (faceVertices F d).card=Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let V := faceVertices F d
  let C (q : V) : Set E := {e | q.val∈range (F e.val)}
  let B (e : E) : Set V := {q | q.val∈range (F e.val)}
  have hC (q : V) : Nat.card (C q)=2 := by
    have hq := (mem_faceVertices F d q.val).mp q.property
    have hq' := hq.2
    have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
    change closure (face F d)=face F d∪⋃ e∈E,range (F e) at hcl
    rw [hcl] at hq'
    have hs : q.val∈⋃ e∈E,range (F e) := hq'.resolve_left (fun hh=>hh.1 (vertex_mem_support F hq.1))
    obtain ⟨i,hi,hqi⟩ := mem_iUnion₂.mp hs
    obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF Q hQ hK d hq.1 hi hqi
    let i' : E := ⟨i,hi⟩
    let j' : E := ⟨j,hj⟩
    change (C q).ncard=2
    apply Set.ncard_eq_two.mpr
    refine ⟨i',j',fun he=>hji (congrArg Subtype.val he).symm,?_⟩
    ext k
    constructor
    · intro hk
      rcases face_edge_eq F hF Q hQ hq.1 (hK q.val) d hji.symm hi hj k.property hqi hqj hk with h|h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl|rfl)
      · exact hqi
      · exact hqj
  have hB (e : E) : Nat.card (B e)=2 := by
    have hend (t : I) (ht : t=0 ∨ t=1) : F e.val t∈V := by
      apply (mem_faceVertices F d _).mpr
      refine ⟨⟨e.val,?_⟩,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe e.property (mem_range_self t)⟩
      rcases ht with rfl|rfl <;> simp
    let a : V := ⟨F e.val 0,hend 0 (Or.inl rfl)⟩
    let b : V := ⟨F e.val 1,hend 1 (Or.inr rfl)⟩
    change (B e).ncard=2
    apply Set.ncard_eq_two.mpr
    refine ⟨a,b,fun he=>(F e.val).endpoints_ne (congrArg Subtype.val he),?_⟩
    ext q
    constructor
    · rintro ⟨t,ht⟩
      have hv := (mem_faceVertices F d q.val).mp q.property |>.1
      rcases vertex_parameter F hF e.val (ht.symm ▸ hv) with h|h
      · subst t
        exact Or.inl (Subtype.ext ht.symm)
      · subst t
        exact Or.inr (Subtype.ext ht.symm)
    · rintro (rfl|rfl)
      · exact mem_range_self 0
      · exact mem_range_self 1
  let e : (Σ q : V,C q) ≃ Σ i : E,B i :=
    { toFun := fun ⟨q,i⟩=>⟨i.val,⟨q,i.property⟩⟩
      invFun := fun ⟨i,q⟩=>⟨q.val,⟨i,q.property⟩⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  have hh := Nat.card_congr e
  rw [Nat.card_sigma,Nat.card_sigma] at hh
  simp only [hC,hB,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  simp only [Fintype.card_coe] at hh
  have heq : V.card=Fintype.card E := by omega
  simpa only [V,E,Nat.card_eq_fintype_card] using heq

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

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_PairComponentClosure
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
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma walk_edge_mem (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) {i : ι} (hi : edgeKey F i∈w.edges) : i∈E := by
  have h := w.edges_subset_edgeSet hi
  change (edgeGraph F E).Adj (edgeStart F i) (edgeEnd F i) at h
  obtain ⟨j,hj,hji⟩ := h
  have he : j=i := spans_edge_unique F hF hji (Or.inl ⟨rfl,rfl⟩)
  exact he ▸ hj

lemma walkCarrier_edgeUnion (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) :
    walkCarrier F w⊆⋃ i∈E,range (F i) := by
  rintro z ⟨i,hi,hzi⟩
  exact mem_iUnion₂.mpr ⟨i,walk_edge_mem F hF w hi,hzi⟩

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_DualGraph
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
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem dualGraph_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2) :
    (dualGraph F univ).Preconnected := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hcov : (⋃ d:Faces F,closure (face F d))=univ :=
    eq_univ_of_forall fun x=>mem_iUnion.mpr (facial_closures_cover F hF Q hQ x)
  apply CannonClosedCover.graph_reachable_cover (dualGraph F univ) (fun d=>closure (face F d))
    (fun _=>isClosed_closure) (by rw [hcov]; exact isPreconnected_univ)
    (fun d=>(face_nonempty F d).mono subset_closure)
  rintro a b ⟨z,hza,hzb⟩
  by_cases heq : a=b
  · subst b; exact .rfl
  by_cases hzV : Vertex F z
  · obtain ⟨p⟩ := vertexFaceGraph_preconnected F hF Q hQ hzV
      (⟨a,hza⟩ : IncidentFaces F z) ⟨b,hzb⟩
    have hmap {u v : IncidentFaces F z} (p : (vertexFaceGraph F z).Walk u v) :
        (dualGraph F univ).Reachable u.val v.val := by
      induction p with
      | nil => exact .rfl
      | @cons u v w h p ih =>
        obtain ⟨huv,i,hi,hu,hv⟩ := h
        have hh : (dualGraph F univ).Adj u.val v.val :=
          ⟨fun h=>huv (Subtype.ext h),i,mem_univ _,hu,hv⟩
        exact hh.reachable.trans ih
    exact hmap p
  have hzK : z∈⋃i,range (F i) := by
    by_contra hn
    have get (d:Faces F) (hd:z∈closure (face F d)) : z∈face F d := by
      change z∈closure (region ((⋃i,range (F i))ᶜ) ConnectedComponents.mk d) at hd
      rw [tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d] at hd
      rcases hd with h|h
      · exact h
      · obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp h
        exact (hn (mem_iUnion.mpr ⟨i,hi⟩)).elim
    exact heq ((get a hza).2.symm.trans (get b hzb).2)
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzK
  have ht₀ : 0<t := by
    apply lt_of_le_of_ne (nonneg t)
    intro he
    exact hzV ⟨i,Or.inl (congrArg (F i) (show (0:I)=t from Subtype.ext he))⟩
  have ht₁ : t<1 := by
    apply lt_of_le_of_ne (le_one t)
    intro he
    exact hzV ⟨i,Or.inr (congrArg (F i) (show (1:I)=t from Subtype.ext he.symm))⟩
  exact (show (dualGraph F univ).Adj a b from
    ⟨heq,i,mem_univ _,⟨t,ht₀,ht₁,hza⟩,⟨t,ht₀,ht₁,hzb⟩⟩).reachable

omit [DecidableEq ι] [Nonempty ι] in
theorem complement_preconnected_of_dual [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (E : Set ι) (hdual : (dualGraph F E).Preconnected) :
    IsPreconnected ((⋃ i∈Eᶜ,range (F i))ᶜ : Set ℂ) := by
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let X : Set ℂ := (⋃ i∈Eᶜ,range (F i))ᶜ
  let C (d:Faces F) := closure (face F d)∩X
  have hface (d:Faces F) : face F d⊆C d := by
    intro z hz
    refine ⟨subset_closure hz,?_⟩
    intro hh
    obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp hh
    exact hz.1 (mem_iUnion.mpr ⟨i,hi⟩)
  have hcover : (⋃d,C d)=X := by
    apply Subset.antisymm (iUnion_subset fun _=>inter_subset_right)
    intro z hz
    obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ z
    exact mem_iUnion.mpr ⟨d,hd,hz⟩
  change IsPreconnected X
  rw [←hcover]
  apply CannonClosedCover.union_preconnected (dualGraph F E) hdual C
    (fun d=>(component_region_connected _ d).isPreconnected.subset_closure (hface d) inter_subset_left)
    (fun d=>(face_nonempty F d).mono (hface d))
  rintro a b ⟨hab,i,hi,ha,hb⟩
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : 0<t := by change (0:ℝ)<1/2; norm_num
  have ht₁ : t<1 := by change (1/2:ℝ)<1; norm_num
  have hzX : F i t∈X := by
    intro hh
    obtain ⟨j,hj,s,hs⟩ := mem_iUnion₂.mp hh
    have hij : i≠j := fun h=>hj (h ▸ hi)
    rcases ((hF hij).1 t s hs.symm).1 with h|h
    · exact (ne_of_gt ht₀) h
    · exact (ne_of_lt ht₁) h
  exact ⟨F i t,⟨region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha (mem_range_self t),hzX⟩,
    region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hb (mem_range_self t),hzX⟩
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem nonseparating_isAcyclic (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (E : Set ι) (hC : IsPreconnected ((⋃ i∈E,range (F i))ᶜ : Set ℂ)) :
    (edgeGraph F E).IsAcyclic := by
  intro x p hp
  obtain ⟨a,b,h₀,h₁,hint,he⟩ := simple_cycle_arcs F hF p hp
  have hs : range a∪range b⊆⋃ i∈E,range (F i) := by
    rw [he]; exact walkCarrier_edgeUnion F hF p
  have hK : (⋃ i∈E,range (F i))⊆⋃ q∈Q,segment ℝ q.1 q.2 :=
    iUnion₂_subset fun i _=>hQ i
  have hd : Dense ((⋃ i∈E,range (F i))ᶜ : Set ℂ) :=
    (complex_finite_segments_compl_dense Q).mono (compl_subset_compl.mpr hK)
  have hc : IsPreconnected ((range a∪range b)ᶜ : Set ℂ) :=
    hC.subset_closure (compl_subset_compl.mpr hs) (fun z _=>hd z)
  obtain ⟨l,hl⟩ := tame_pair_jordan a b h₀ h₁ hint Q
    (subset_union_left.trans (hs.trans hK)) (subset_union_right.trans (hs.trans hK))
  let _ : PreconnectedSpace ((range a∪range b)ᶜ : Set ℂ) :=
    isPreconnected_iff_preconnectedSpace.mp hc
  have hh : l true=l false := Subsingleton.elim _ _
  exact Bool.noConfusion (l.injective hh)
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_DualGraphGaugeGraph
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
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

lemma dualGraph_eq_gaugeGraph (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i)) (E : Set ι) :
    dualGraph F E=CannonGraphGauge.edgeGraph a b hab E := by
  ext x y
  constructor
  · rintro ⟨hxy,i,hi,hx,hy⟩
    refine ⟨i,hi,?_⟩
    rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hx with hx|hx <;>
      rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hy with hy|hy
    · exact (hxy (hx.trans hy.symm)).elim
    · exact Or.inl ⟨hx.symm,hy.symm⟩
    · exact Or.inr ⟨hy.symm,hx.symm⟩
    · exact (hxy (hx.trans hy.symm)).elim
  · rintro ⟨i,hi,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact ⟨hab i,i,hi,ha i,hb i⟩
    · exact ⟨(hab i).symm,i,hi,hb i,ha i⟩

lemma no_single_bad_transition (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (K : ι→D) (v t : Faces F→D) {q : ℂ} (hq : Vertex F q)
    (hlocal : ∀ j,q∈range (F j) → K j*t (a j)=t (b j))
    (i : ι) (hi : q∈range (F i))
    (hother : ∀ j,q∈range (F j) → j≠i → K j*v (a j)=v (b j)) :
    K i*v (a i)=v (b i) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let f (d : Faces F) := (t d)⁻¹*v d
  let w : IncidentEdges F q ⊕ IncidentFaces F q → D :=
    Sum.elim (fun j=>f (a j.val)) (fun d=>f d.val)
  let i' : IncidentEdges F q := ⟨i,hi⟩
  let b' : IncidentFaces F q := ⟨b i,region_edge_in_closure F hF Q hQ
    ConnectedComponents.continuous_coe (hb i) hi⟩
  have good (j : ι) (hj : q∈range (F j)) (hji : j≠i) : f (a j)=f (b j) := by
    simp only [f,←hlocal j hj,←hother j hj hji,mul_inv_rev]
    group
  have step (j : IncidentEdges F q) (d : IncidentFaces F q)
      (hd : j.val∈regionEdges F ConnectedComponents.mk d.val)
      (hne : s(Sum.inl j,Sum.inr d)≠s(Sum.inl i',Sum.inr b')) :
      w (.inl j)=w (.inr d) := by
    change f (a j.val)=f d.val
    rcases edge_face_unique_two F hF Q hQ j.val (hab j.val) (ha j.val) (hb j.val) hd with h|h
    · rw [h]
    · rw [h]
      apply good _ j.property
      intro he
      apply hne
      have hj : j=i' := Subtype.ext he
      have hd : d=b' := Subtype.ext (h.trans (congrArg b he))
      rw [hj,hd]
  have he := CannonGraphGauge.label_equal_of_other_edges (vertexLink F q)
    (vertexLink_isCycles F hF Q hQ hK hq)
    (show (vertexLink F q).Adj (.inl i') (.inr b') from hb i) w (by
      intro x y h hne
      cases x with
      | inl j =>
        cases y with
        | inl k => exact h.elim
        | inr d => exact step j d h hne
      | inr d =>
        cases y with
        | inr c => exact h.elim
        | inl j =>
          apply (step j d h ?_).symm
          intro he
          exact hne (Sym2.eq_swap.trans he))
  change (t (a i))⁻¹*v (a i)=(t (b i))⁻¹*v (b i) at he
  have he' := congrArg (fun z=>t (b i)*z) he
  rw [←hlocal i hi] at he'
  group at he'
  exact he'

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NoSingleFaceDiscordance
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
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D Z : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

lemma no_single_face_discordance (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (f : Faces F→Z) {q : ℂ} (hq : Vertex F q)
    (i : ι) (hi : q∈range (F i))
    (hother : ∀ j,q∈range (F j) → j≠i → f (a j)=f (b j)) : f (a i)=f (b i) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let w : IncidentEdges F q ⊕ IncidentFaces F q → Z :=
    Sum.elim (fun j=>f (a j.val)) (fun d=>f d.val)
  let i' : IncidentEdges F q := ⟨i,hi⟩
  let b' : IncidentFaces F q := ⟨b i,region_edge_in_closure F hF Q hQ
    ConnectedComponents.continuous_coe (hb i) hi⟩
  have step (j : IncidentEdges F q) (d : IncidentFaces F q)
      (hd : j.val∈regionEdges F ConnectedComponents.mk d.val)
      (hne : s(Sum.inl j,Sum.inr d)≠s(Sum.inl i',Sum.inr b')) :
      w (.inl j)=w (.inr d) := by
    change f (a j.val)=f d.val
    rcases edge_face_unique_two F hF Q hQ j.val (hab j.val) (ha j.val) (hb j.val) hd with h|h
    · rw [h]
    · rw [h]
      apply hother _ j.property
      intro he
      apply hne
      have hj : j=i' := Subtype.ext he
      have hd : d=b' := Subtype.ext (h.trans (congrArg b he))
      rw [hj,hd]
  exact CannonGraphGauge.label_equal_of_other_edges (vertexLink F q)
    (vertexLink_isCycles F hF Q hQ hK hq)
    (show (vertexLink F q).Adj (.inl i') (.inr b') from hb i) w (by
      intro x y h hne
      cases x with
      | inl j =>
        cases y with
        | inl k => exact h.elim
        | inr d => exact step j d h hne
      | inr d =>
        cases y with
        | inr c => exact h.elim
        | inl j =>
          apply (step j d h ?_).symm
          intro he
          exact hne (Sym2.eq_swap.trans he))

theorem dual_preconnected_delete_forest (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (T : Set ι) (hT : (edgeGraph F T).IsAcyclic) :
    (dualGraph F Tᶜ).Preconnected := by
  classical
  let H := dualGraph F Tᶜ
  let f := H.connectedComponentMk
  let B : Set ι := {i | f (a i)≠f (b i)}
  have hBT : B⊆T := by
    intro i hi
    by_contra hn
    exact hi (SimpleGraph.ConnectedComponent.sound
      (show H.Adj (a i) (b i) from ⟨hab i,i,hn,ha i,hb i⟩).reachable)
  have hBG : edgeGraph F B≤edgeGraph F T := by
    rintro x y ⟨i,hi,h⟩; exact ⟨i,hBT hi,h⟩
  have hempty : edgeGraph F B=⊥ := by
    apply CannonForest.empty_of_no_leaves _ (hT.anti hBG)
    rintro x y ⟨i,hi,hiy⟩
    by_contra hn
    push Not at hn
    apply hi
    exact no_single_face_discordance F hF Q hQ hK a b hab ha hb f x.property i
      hiy.mem_left (by
        intro j hj hji
        by_contra hbad
        obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hj
        let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
        have hAdj : (edgeGraph F B).Adj x z' := ⟨j,hbad,hjz⟩
        have hzy := congrArg Subtype.val (hn z' hAdj)
        exact hji (spans_edge_unique F hF (hzy ▸ hjz) hiy))
  have he (i:ι) : f (a i)=f (b i) := by
    by_contra hn
    let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
    let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
    have h : (edgeGraph F B).Adj x y := ⟨i,hn,Or.inl ⟨rfl,rfl⟩⟩
    rw [hempty] at h
    exact h
  intro x y
  have hc : (CannonGraphGauge.edgeGraph a b hab univ).Preconnected := by
    rw [←dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact dualGraph_preconnected F hF Q hQ
  obtain ⟨p⟩ := hc x y
  apply SimpleGraph.ConnectedComponent.exact
  induction p with
  | nil => rfl
  | @cons x y z h p ih =>
    obtain ⟨i,-,h|h⟩ := h
    · exact (h.1 ▸ h.2 ▸ he i).trans ih
    · exact (h.2 ▸ h.1 ▸ (he i).symm).trans ih

theorem planar_disk_gauge_integrates (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (T : Set ι) (hT : (edgeGraph F T).IsAcyclic)
    (S : Set (GraphVertices F)) (hS : ((edgeGraph F T).induce S).Preconnected)
    (hTS : ∀ x y,(edgeGraph F T).Adj x y → x∈S ∧ y∈S)
    (K : ι→D)
    (hflat : ∀ q:GraphVertices F,q∉S → ∃ t : Faces F→D,
      ∀ j,q.val∈range (F j) → K j*t (a j)=t (b j)) :
    ∃ v : Faces F→D,∀ i,
      ((⟨F i 0,⟨i,Or.inl rfl⟩⟩:GraphVertices F)∉S ∨
       (⟨F i 1,⟨i,Or.inr rfl⟩⟩:GraphVertices F)∉S) → K i*v (a i)=v (b i) := by
  classical
  have hconn : (CannonGraphGauge.edgeGraph a b hab Tᶜ).Preconnected := by
    rw [←dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact dual_preconnected_delete_forest F hF Q hQ hK a b hab ha hb T hT
  obtain ⟨v,hv⟩ := CannonGraphGauge.exists_connected_good_restrict a b hab K Tᶜ hconn
  let E : Set ι := Tᶜ∩(CannonGraphGauge.goodEdges a b K v : Set ι)
  have hd : (dualGraph F E).Preconnected := by
    rw [dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact hv
  have hac := nonseparating_isAcyclic F hF Q hQ Eᶜ
    (complement_preconnected_of_dual F hF Q hQ E hd)
  have hTB : edgeGraph F T≤edgeGraph F Eᶜ := by
    rintro x y ⟨i,hi,h⟩
    exact ⟨i,fun he=>he.1 hi,h⟩
  have hconnS : ((edgeGraph F Eᶜ).induce S).Preconnected := by
    apply hS.mono
    exact fun _ _ h=>hTB h
  have hconfine := CannonForest.edges_confined_to_core (edgeGraph F Eᶜ) hac S hconnS (by
    rintro x hx y ⟨i,hi,hiy⟩
    by_contra hn
    push Not at hn
    obtain ⟨t,ht⟩ := hflat x hx
    have he : K i*v (a i)=v (b i) := no_single_bad_transition F hF Q hQ hK a b hab ha hb
      K v t x.property ht i hiy.mem_left (by
        intro j hj hji
        by_contra hbad
        obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hj
        let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
        have hjB : j∈Eᶜ := fun h=>hbad ((CannonGraphGauge.mem_goodEdges ..).mp h.2)
        have hAdj : (edgeGraph F Eᶜ).Adj x z' := ⟨j,hjB,hjz⟩
        have hzy := congrArg Subtype.val (hn z' hAdj)
        exact hji (spans_edge_unique F hF (hzy ▸ hjz) hiy))
    have hinT : i∉T := by
      intro hiT
      have hAdj : (edgeGraph F T).Adj x y := ⟨i,hiT,hiy⟩
      exact hx (hTS x y hAdj).1
    exact hi ⟨hinT,(CannonGraphGauge.mem_goodEdges ..).mpr he⟩)
  refine ⟨v,fun i hi=>?_⟩
  by_contra hn
  let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
  let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
  have hB : i∈Eᶜ := fun h=>hn ((CannonGraphGauge.mem_goodEdges ..).mp h.2)
  have h := hconfine x y ⟨i,hB,Or.inl ⟨rfl,rfl⟩⟩
  exact hi.elim (fun hn=>hn h.1) (fun hn=>hn h.2)
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

lemma Spans.endpoints_eq {a:Arc ℂ} {x y u v:ℂ} (h:Spans a x y) (h':Spans a u v) :
    (u=x ∧ v=y) ∨ (u=y ∧ v=x) := by
  rcases h with ⟨hx,hy⟩|⟨hx,hy⟩ <;> rcases h' with ⟨hu,hv⟩|⟨hu,hv⟩
  · exact Or.inl ⟨hu.symm.trans hx,hv.symm.trans hy⟩
  · exact Or.inr ⟨hu.symm.trans hy,hv.symm.trans hx⟩
  · exact Or.inr ⟨hu.symm.trans hy,hv.symm.trans hx⟩
  · exact Or.inl ⟨hu.symm.trans hx,hv.symm.trans hy⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem triangular_face_scaffold [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (out:Faces F) (hthree:(faceVertices F out).card=3) :
    let S : Set (GraphVertices F) := {x | x.val∈faceVertices F out}
    ∃ T:Set ι,(edgeGraph F T).IsAcyclic ∧ ((edgeGraph F T).induce S).Preconnected ∧
      (∀ x y,(edgeGraph F T).Adj x y → x∈S ∧ y∈S) ∧
      ∀ i,F i 0∈faceVertices F out → F i 1∈faceVertices F out →
        i∈regionEdges F ConnectedComponents.mk out := by
  classical
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let S : Set (GraphVertices F) := {x | x.val∈faceVertices F out}
  dsimp only
  have hE : (regionEdges F ConnectedComponents.mk out).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have hn := noncut_facial_vertices_edges F hF Q hQ hK out
    rw [hthree] at hn
    change Nat.card (regionEdges F ConnectedComponents.mk out)≠0
    omega
  obtain ⟨i,hi⟩ := hE
  let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
  let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
  have hixy : Spans (F i) x.val y.val := Or.inl ⟨rfl,rfl⟩
  obtain ⟨j,hji,hj,hxj⟩ := noncut_face_second_edge F hF Q hQ hK out x.property hi hixy.mem_left
  obtain ⟨z₀,hjxz⟩ := vertex_spans F hF x.property hxj
  let z : GraphVertices F := ⟨z₀,hjxz.vertex_right⟩
  have hxy : x≠y := fun h=>hixy.ne (congrArg Subtype.val h)
  have hxz : x≠z := fun h=>hjxz.ne (congrArg Subtype.val h)
  have hyz : y≠z := by
    intro h
    exact hji (spans_edge_unique F hF (show Spans (F j) x.val y.val from
      (congrArg Subtype.val h).symm ▸ hjxz) hixy)
  have memS {a:ι} (ha:a∈regionEdges F ConnectedComponents.mk out) {v:GraphVertices F}
      (hv:v.val∈range (F a)) : v∈S :=
    (mem_faceVertices F out v.val).mpr ⟨v.property,region_edge_in_closure F hF Q hQ
      ConnectedComponents.continuous_coe ha hv⟩
  have hxS : x∈S := memS hi hixy.mem_left
  have hyS : y∈S := memS hi hixy.mem_right
  have hzS : z∈S := memS hj hjxz.mem_right
  have hfin : faceVertices F out={x.val,y.val,z.val} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption
    · rw [hthree]
      have hxy' : x.val≠y.val := fun h=>hxy (Subtype.ext h)
      have hxz' : x.val≠z.val := fun h=>hxz (Subtype.ext h)
      have hyz' : y.val≠z.val := fun h=>hyz (Subtype.ext h)
      simp [hxy',hxz',hyz']
  have hS : S={x,y,z} := by
    ext v
    simp only [S,mem_ofPred_eq,hfin,Finset.mem_insert,Finset.mem_singleton,
      mem_insert_iff,mem_singleton_iff,Subtype.val_inj]
  let T : Set ι := {i,j}
  have hTend {u v:GraphVertices F} (h:(edgeGraph F T).Adj u v) :
      (u=x ∧ (v=y ∨ v=z)) ∨ (v=x ∧ (u=y ∨ u=z)) := by
    obtain ⟨k,hk,hksp⟩ := h
    rcases hk with rfl|rfl
    · rcases hixy.endpoints_eq hksp with h|h
      · exact Or.inl ⟨Subtype.ext h.1,Or.inl (Subtype.ext h.2)⟩
      · exact Or.inr ⟨Subtype.ext h.2,Or.inl (Subtype.ext h.1)⟩
    · rcases hjxz.endpoints_eq hksp with h|h
      · exact Or.inl ⟨Subtype.ext h.1,Or.inr (Subtype.ext h.2)⟩
      · exact Or.inr ⟨Subtype.ext h.2,Or.inr (Subtype.ext h.1)⟩
  have hTstar : edgeGraph F T≤SimpleGraph.starGraph x := by
    intro u v h
    apply SimpleGraph.starGraph_adj.mpr
    exact ⟨h.ne,(hTend h).elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)⟩
  refine ⟨T,(SimpleGraph.isAcyclic_starGraph x).anti hTstar,?_,?_,?_⟩
  · have reach (v:S) : ((edgeGraph F T).induce S).Reachable ⟨x,hxS⟩ v := by
      have hv : v.val∈({x,y,z}:Set (GraphVertices F)) := by simpa only [hS] using v.property
      rcases hv with hv|hv|hv
      · have he : v=⟨x,hxS⟩ := Subtype.ext hv
        rw [he]
      · have he : v=⟨y,hyS⟩ := Subtype.ext hv
        rw [he]
        exact (show ((edgeGraph F T).induce S).Adj ⟨x,hxS⟩ ⟨y,hyS⟩ from
          ⟨i,Or.inl rfl,hixy⟩).reachable
      · have he : v=⟨z,hzS⟩ := Subtype.ext hv
        rw [he]
        exact (show ((edgeGraph F T).induce S).Adj ⟨x,hxS⟩ ⟨z,hzS⟩ from
          ⟨j,Or.inr rfl,hjxz⟩).reachable
    exact fun u v=>(reach u).symm.trans (reach v)
  · intro u v h
    rcases hTend h with ⟨rfl,hv⟩|⟨rfl,hu⟩
    · exact ⟨hxS,hv.elim (fun h=>h ▸ hyS) (fun h=>h ▸ hzS)⟩
    · exact ⟨hu.elim (fun h=>h ▸ hyS) (fun h=>h ▸ hzS),hxS⟩
  · intro k hk₀ hk₁
    let u : GraphVertices F := ⟨F k 0,⟨k,Or.inl rfl⟩⟩
    let v : GraphVertices F := ⟨F k 1,⟨k,Or.inr rfl⟩⟩
    have huv : u≠v := fun he=>(F k).endpoints_ne (congrArg Subtype.val he)
    have huS : u∈S := hk₀
    have hvS : v∈S := hk₁
    let G := edgeGraph F (regionEdges F ConnectedComponents.mk out)
    have every_neighbor {p:GraphVertices F} (hp:p∈S) :
        ∃ w,G.Adj p w := by
      rw [hS] at hp
      rcases hp with rfl|rfl|rfl
      · exact ⟨y,i,hi,hixy⟩
      · exact ⟨x,i,hi,hixy.symm⟩
      · exact ⟨x,j,hj,hjxz.symm⟩
    obtain ⟨w,hw⟩ := every_neighbor huS
    obtain ⟨a,b,hab,heq⟩ := Set.ncard_eq_two.mp
      (facial_graph_isCycles F hF Q hQ hK out (show (G.neighborSet u).Nonempty from ⟨w,hw⟩))
    have ha : G.Adj u a := by
      change a∈G.neighborSet u
      rw [heq]
      exact Or.inl rfl
    have hb : G.Adj u b := by
      change b∈G.neighborSet u
      rw [heq]
      exact Or.inr rfl
    have haS : a∈S := by obtain ⟨e,he,hsp⟩ := ha; exact memS he hsp.mem_right
    have hbS : b∈S := by obtain ⟨e,he,hsp⟩ := hb; exact memS he hsp.mem_right
    have hvab : v=a ∨ v=b := by
      by_contra hn
      push Not at hn
      have hsCard : S.ncard=3 := by rw [hS]; simp [hxy,hxz,hyz]
      have hsu : ({u,v,a,b}:Set (GraphVertices F))⊆S := by
        intro p hp; rcases hp with rfl|rfl|rfl|rfl <;> assumption
      have hc := Set.ncard_le_ncard hsu (Set.toFinite S)
      have hua : u≠a := ha.ne
      have hub : u≠b := hb.ne
      have hc4 : ({u,v,a,b}:Set (GraphVertices F)).ncard=4 := by
        simp [huv,hua,hub,hn.1,hn.2,hab]
      rw [hc4,hsCard] at hc
      omega
    have hvG : G.Adj u v := hvab.elim (fun h=>h ▸ ha) (fun h=>h ▸ hb)
    obtain ⟨e,he,hsp⟩ := hvG
    have hek := spans_edge_unique F hF hsp (show Spans (F k) u.val v.val from Or.inl ⟨rfl,rfl⟩)
    exact hek ▸ he

theorem triangular_disk_gauge_integrates_oai (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (out:Faces F) (hthree:(faceVertices F out).card=3)
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (K : ι→D)
    (hflat : ∀ q,Vertex F q → q∉faceVertices F out → ∃ t : Faces F→D,
      ∀ j,q∈range (F j) → K j*t (a j)=t (b j)) :
    ∃ v : Faces F→D,∀ i,a i≠out → b i≠out → K i*v (a i)=v (b i) := by
  classical
  obtain ⟨T,hTa,hTc,hTS,hchord⟩ := triangular_face_scaffold F hF Q hQ hK out hthree
  obtain ⟨v,hv⟩ := planar_disk_gauge_integrates F hF Q hQ hK a b hab ha hb T hTa
    {x | x.val∈faceVertices F out} hTc hTS K (fun q hq=>hflat q q.property hq)
  refine ⟨v,fun i hai hbi=>hv i ?_⟩
  by_contra hn
  push Not at hn
  have hi := hchord i hn.1 hn.2
  rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hi with h|h
  · exact hai h.symm
  · exact hbi h.symm
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates_oai.{u_1, u_2} := @OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates_oai.{u_1, u_2}
