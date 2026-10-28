-- Prove2me | solution 1 for OAI.Paper170.polygonal_no_adjacent_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:42:47.363233+00:00
-- url     : https://prove2.me/submissions/673d91df-c380-4ba1-9943-1e22d153eede

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc002

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Drawing
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous graph drawings, proper spatial crossings, incidence, and endpoint properties. -/

section

/-! A weaker INPUT for normalization: actual simple routes with finite contacts and no triples.
The endpoint's Paper170.AdmissibleDrawing and MainTarget definitions are unchanged. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem finiteCrossingCount_eq_ncard  (D : FiniteIntersectionDrawing graph) :
    finiteCrossingCount D=(Paper170.crossingPoints D.toContinuousDrawing).ncard :=
  (Set.ncard_eq_toFinset_card _ D.crossings_finite).symm

end Paper170Geometry

end
end

section

/-! Finite point incidence for actual drawings, retaining repeated pair crossings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
open scoped BigOperators Classical
/-- A minimum exists once an actual admissible drawing has been constructed.
This is the well-ordering step; construction of a drawing remains a separate obligation. -/
theorem crossingCount_attainment (D₀ : Paper170.AdmissibleDrawing graph) :
    ∃ D : Paper170.AdmissibleDrawing graph, Paper170.crossingCount D = Paper170.ordinaryCrossingNumber graph := by
  exact csInf_mem (show (Set.range (@Paper170.crossingCount Vertex Edge graph)).Nonempty from
    ⟨Paper170.crossingCount D₀, D₀, rfl⟩)

theorem ordinaryCrossingNumber_le_count (D : Paper170.AdmissibleDrawing graph) :
    Paper170.ordinaryCrossingNumber graph ≤ Paper170.crossingCount D :=
  csInf_le' ⟨D, rfl⟩

theorem crossing_incident_iff (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (e f : Edge) (hef : e ≠ f)
    (he : x ∈ Paper170.edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ Paper170.edgeInterior D.toContinuousDrawing f) (g : Edge) :
    x ∈ Paper170.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f ∩
        Paper170.edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PlanarSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem det2_neg_left (u v : Plane) : det2 (-u) v = -det2 u v := by
  simp [det2]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem segmentReach_mem {O : Set Plane} {a b : Plane} (ha : a ∈ O) (h : SegmentReach O a b) : b ∈ O := by
  induction h with
  | refl => exact ha
  | @tail b c hab hbc ih => exact hbc (right_mem_segment ℝ b c)

theorem isOpen_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) (ha : a ∈ O) :
    IsOpen {b | SegmentReach O a b} := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds (segmentReach_mem ha hb))
  refine ⟨ε,hε,?_⟩
  intro c hc
  apply Relation.ReflTransGen.tail hb
  exact ((convex_ball b ε).segment_subset (Metric.mem_ball_self hε) hc).trans hball

theorem isOpen_non_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) :
    IsOpen (O \ {b | SegmentReach O a b}) := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hb.1)
  refine ⟨ε,hε,?_⟩
  intro c hc
  refine ⟨hball hc,?_⟩
  intro hreach
  apply hb.2
  apply Relation.ReflTransGen.tail hreach
  exact ((convex_ball b ε).segment_subset hc (Metric.mem_ball_self hε)).trans hball

theorem segmentReach_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : SegmentReach O a b := by
  have ha : a ∈ O := by simpa using hγ 0
  let A : Set unitInterval := {t | SegmentReach O a (γ t)}
  have hopen : IsOpen A := (isOpen_segmentReach O hO a ha).preimage γ.continuous
  have hcomp : IsOpen Aᶜ := by
    have heq : Aᶜ = γ ⁻¹' (O \ {x | SegmentReach O a x}) := by
      ext t
      simp only [A,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_sdiff,hγ t,true_and]
    rw [heq]
    exact (isOpen_non_segmentReach O hO a).preimage γ.continuous
  have hall : A=Set.univ := (show IsClopen A from ⟨by simpa using hcomp.isClosed_compl,hopen⟩).eq_univ ⟨0,by
    change SegmentReach O a (γ 0)
    rw [γ.source]
    exact Relation.ReflTransGen.refl⟩
  have hb : (1 : unitInterval) ∈ A := by rw [hall]; trivial
  change SegmentReach O a (γ 1) at hb
  rwa [γ.target] at hb

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem nonempty_polygonalChain_of_reach {O : Set Plane} {a b : Plane}
    (ha : a ∈ O) (h : SegmentReach O a b) : Nonempty (PolygonalChain O a b) := by
  induction h with
  | refl => exact ⟨PolygonalChain.point O a ha⟩
  | @tail b c hab hbc ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.append c hbc⟩

theorem nonempty_polygonalChain_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : Nonempty (PolygonalChain O a b) := by
  exact nonempty_polygonalChain_of_reach (by simpa using hγ 0) (segmentReach_of_path γ O hO hγ)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteAffineCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem hasFiniteAffineCover_refl (a : Plane) : HasFiniteAffineCover (Path.refl a) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    change a=segmentPoint a a t.val
    simp [segmentPoint,← add_smul]

theorem hasFiniteAffineCover_segment (a b : Plane) : HasFiniteAffineCover (Path.segment a b) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    simp only [intervalSegment_zero_one,Path.source,Path.target]
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]

theorem HasFiniteAffineCover.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (hγ : HasFiniteAffineCover γ) (hη : HasFiniteAffineCover η) : HasFiniteAffineCover (γ.trans η) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  obtain ⟨T,hTlt,hTcov,hTaff⟩ := hη
  let L : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalLeft ab.1,intervalLeft ab.2)
  let R : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalRight ab.1,intervalRight ab.2)
  refine ⟨S.image L ∪ T.image R,?_,?_,?_⟩
  · intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (hSlt cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (hTlt cd hcd)
  · intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hScov u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨L ab,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [← hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [← hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hTcov u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨R ab,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalRight ab.1 ≤ t
        rw [← hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [← hu]
        exact intervalRight_strictMono.monotone hb
  · intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalLeft cd.1) (intervalLeft cd.2) t)=_
      rw [intervalSegment_left,path_trans_intervalLeft]
      exact (hSaff cd hcd t).trans (by simp only [L,path_trans_intervalLeft])
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalRight cd.1) (intervalRight cd.2) t)=_
      rw [intervalSegment_right,path_trans_intervalRight]
      exact (hTaff cd hcd t).trans (by simp only [R,path_trans_intervalRight])

theorem HasFiniteAffineCover.cast {a b c d : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (ha : c=a) (hb : d=b) : HasFiniteAffineCover (γ.cast ha hb) := hγ

theorem polygonalArcPath_hasFiniteAffineCover (v : ℕ → Plane) :
    (k : ℕ) → HasFiniteAffineCover (polygonalArcPath v k)
  | 0 => hasFiniteAffineCover_refl _
  | 1 => hasFiniteAffineCover_segment _ _
  | k+2 => (polygonalArcPath_hasFiniteAffineCover v (k+1)).trans (hasFiniteAffineCover_segment _ _)

theorem PolygonalChain.hasFiniteAffineCover {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) : HasFiniteAffineCover P.path :=
  (polygonalArcPath_hasFiniteAffineCover P.vertices P.pieces).cast P.first.symm P.last.symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_AffineIntervalRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem intervalSegment_interpolate (a b u v t : unitInterval) :
    intervalSegment (intervalSegment a b u) (intervalSegment a b v) t=
      intervalSegment a b (intervalSegment u v t) := by
  apply Subtype.ext
  dsimp [intervalSegment]
  ring

theorem segmentPoint_interpolate (a b : Plane) (u v t : ℝ) :
    segmentPoint (segmentPoint a b u) (segmentPoint a b v) t=
      segmentPoint a b ((1-t)*u+t*v) := by
  ext <;> dsimp [segmentPoint] <;> ring

theorem path_affine_restrict {a b : Plane} (γ : Path a b) (l r : unitInterval) (hlr : l < r)
    (haff : ∀ t : unitInterval, γ (intervalSegment l r t)=segmentPoint (γ l) (γ r) t.val)
    (u v : unitInterval) (hu : l ≤ u ∧ u ≤ r) (hv : l ≤ v ∧ v ≤ r) (t : unitInterval) :
    γ (intervalSegment u v t)=segmentPoint (γ u) (γ v) t.val := by
  obtain ⟨u',rfl⟩ := intervalSegment_surjective_interval l r hlr u hu
  obtain ⟨v',rfl⟩ := intervalSegment_surjective_interval l r hlr v hv
  rw [intervalSegment_interpolate,haff,haff,haff,segmentPoint_interpolate]
  rfl

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_IntervalSegmentStrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem intervalSegment_strict_between (a b t : unitInterval) (hab : a < b)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    a < intervalSegment a b t ∧ intervalSegment a b t < b := by
  have hab' : a.val < b.val := hab
  have ht0 : 0 < t.val := ht.1
  have ht1 : t.val < 1 := ht.2
  have h₀ := mul_pos ht0 (sub_pos.mpr hab')
  have h₁ := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab')
  change a.val < (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val < b.val
  constructor <;> nlinarith

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨ε,hε,hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self i S)
    refine ⟨min (ε/2) (f i/2),lt_min (by linarith) (by linarith),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (by have hh := hbound j hj; linarith)

theorem finite_node_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε < |node i-node j| := by
  obtain ⟨ε,hε,hb⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2))
    (fun ij => |node ij.1-node ij.2|) (by
      intro ij hij
      exact abs_pos.mpr (sub_ne_zero.mpr (hn.ne (Finset.mem_filter.mp hij).2)))
  exact ⟨ε,hε,fun i j hij => hb (i,j) (by simpa using hij)⟩

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PlanarDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem det2_smul_left (r : ℝ) (u v : Plane) : det2 (r • u) v = r*det2 u v := by
  dsimp [det2]
  ring

theorem det2_smul_right (r : ℝ) (u v : Plane) : det2 u (r • v) = r*det2 u v := by
  dsimp [det2]
  ring

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SortedMarkedParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_sorted_unitInterval_finset (S : Finset unitInterval)
    (h0 : (0 : unitInterval) ∈ S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧ Set.range t=(S : Set unitInterval) := by
  have hc : 1 < S.card := Finset.one_lt_card.mpr ⟨0,h0,1,h1,zero_ne_one⟩
  let k := S.card-1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : S.card=k+1 := by dsimp [k]; omega
  let e := S.orderEmbOfFin hcard
  have hrange : Set.range e=(S : Set unitInterval) := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, e i=0 := by
    have hm : (0 : unitInterval) ∈ Set.range e := hrange.symm ▸ h0
    exact hm
  obtain ⟨j,hj⟩ : ∃ j, e j=1 := by
    have hm : (1 : unitInterval) ∈ Set.range e := hrange.symm ▸ h1
    exact hm
  have he0 : e 0=0 := by
    apply le_antisymm
    · exact (e.monotone (Fin.zero_le i)).trans_eq hi
    · exact (e 0).property.1
  have he1 : e (Fin.last k)=1 := by
    apply le_antisymm
    · exact (e (Fin.last k)).property.2
    · exact hj.symm.trans_le (e.monotone (Fin.le_last j))
  exact ⟨k,hk,e,e.strictMono,he0,he1,hrange⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OrderedAffineSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem strictMono_no_between_successors {k : ℕ} (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (i : Fin k) (j : Fin (k+1)) :
    ¬ (t i.castSucc < t j ∧ t j < t i.succ) := by
  intro h
  have hlo : i.castSucc < j := by
    by_contra hn
    exact h.1.not_ge (ht.monotone (le_of_not_gt hn))
  have hhi : j < i.succ := by
    by_contra hn
    exact h.2.not_ge (ht.monotone (le_of_not_gt hn))
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

theorem HasFiniteAffineCover.nonempty_polygonalParametrization {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) : Nonempty (PolygonalParametrization γ) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 (S.image Prod.fst ∪ S.image Prod.snd))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=?_}⟩
  intro i u
  let mid : unitInterval := ⟨1/2,by norm_num⟩
  let z := intervalSegment (t i.castSucc) (t i.succ) mid
  have hz : t i.castSucc < z ∧ z < t i.succ :=
    intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
      constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
  obtain ⟨ab,hab,ha,hb⟩ := hScov z
  have hlo : ab.1 ≤ t i.castSucc := by
    by_contra hn
    obtain ⟨j,hj⟩ := hleft ab hab
    exact strictMono_no_between_successors t ht i j
      ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
  have hhi : t i.succ ≤ ab.2 := by
    by_contra hn
    obtain ⟨j,hj⟩ := hright ab hab
    exact strictMono_no_between_successors t ht i j
      ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
  have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
  exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
    (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_AffineSubdivisionRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem HasFiniteAffineCover.refine {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (R : Finset unitInterval) :
    ∃ P : PolygonalParametrization γ, (R : Set unitInterval) ⊆ Set.range P.knot := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 ((S.image Prod.fst ∪ S.image Prod.snd) ∪ R))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have haff : ∀ i : Fin k, ∀ u : unitInterval,
      γ (intervalSegment (t i.castSucc) (t i.succ) u)=segmentPoint (γ (t i.castSucc)) (γ (t i.succ)) u.val := by
    intro i u
    let mid : unitInterval := ⟨1/2,by norm_num⟩
    let z := intervalSegment (t i.castSucc) (t i.succ) mid
    have hz : t i.castSucc < z ∧ z < t i.succ :=
      intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
        constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
    obtain ⟨ab,hab,ha,hb⟩ := hScov z
    have hlo : ab.1 ≤ t i.castSucc := by
      by_contra hn
      obtain ⟨j,hj⟩ := hleft ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
    have hhi : t i.succ ≤ ab.2 := by
      by_contra hn
      obtain ⟨j,hj⟩ := hright ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
    have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
    exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
      (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=haff},?_⟩
  intro u hu
  change u ∈ Set.range t
  rw [hR]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CollinearSegmentUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem collinear_segment_subset_union (a b c : Plane) (hac : a ≠ c)
    (h : det2 (b-a) (c-b)=0) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  have hd : det2 (c-a) (b-a)=0 := by
    have he : det2 (c-a) (b-a) = -det2 (b-a) (c-b) := by dsimp [det2]; ring
    rw [he,h,neg_zero]
  have hp := vector_parallel_of_det_zero (c-a) (b-a) (sub_ne_zero.mpr (Ne.symm hac)) hd
  have hb : b ∈ Set.range (AffineMap.lineMap a c : ℝ → Plane) := by
    refine ⟨dot2 (c-a) (b-a)/squaredLength (c-a),?_⟩
    rw [AffineMap.lineMap_apply]
    change (dot2 (c-a) (b-a)/squaredLength (c-a)) • (c-a)+a=b
    rw [← hp,sub_add_cancel]
  intro x hx
  rw [← insert_endpoints_openSegment] at hx
  rcases hx with hxa | hxc | hxo
  · subst x
    exact Or.inl (left_mem_segment ℝ a b)
  · subst x
    exact Or.inr (right_mem_segment ℝ b c)
  · rcases openSegment_subset_union a c hb hxo with hxb | hx'
    · subst x
      exact Or.inl (right_mem_segment ℝ a b)
    · exact hx'.elim (fun hh => Or.inl (openSegment_subset_segment ℝ a b hh))
        (fun hh => Or.inr (openSegment_subset_segment ℝ b c hh))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_minimum_polygonalChain {O : Set Plane} {a b : Plane}
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces := by
  classical
  obtain ⟨P⟩ := h
  have hex : ∃ n : ℕ, ∃ Q : PolygonalChain O a b, Q.pieces=n := ⟨P.pieces,P,rfl⟩
  obtain ⟨Q,hQ⟩ := Nat.find_spec hex
  refine ⟨Q,?_⟩
  intro R
  rw [hQ]
  exact Nat.find_min' hex ⟨R,rfl⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainShortcuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_shortcut_bound (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.pieces)
    (Q : PolygonalChain O (P.vertices i) (P.vertices j)) : j-i ≤ Q.pieces := by
  have hh := hmin (((P.take i (by omega)).join Q).join (P.drop j hj))
  simp only [pieces_join,pieces_take,pieces_drop] at hh
  omega

theorem minimum_vertices_ne (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i < j) (hj : j ≤ P.pieces) : P.vertices i ≠ P.vertices j := by
  intro he
  let Q := (point O (P.vertices i) (P.vertex_mem i (by omega))).withEndpoints rfl he.symm
  have hh := P.minimum_shortcut_bound hmin i j (by omega) hj Q
  change j-i ≤ 0 at hh
  omega

theorem minimum_nonadjacent_disjoint (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i+1 < j) (hj : j < P.pieces) :
    Disjoint (segment ℝ (P.vertices i) (P.vertices (i+1)))
      (segment ℝ (P.vertices j) (P.vertices (j+1))) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hleft : segment ℝ (P.vertices i) x ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hxi).trans
      (P.inside i (by omega))
  have hright : segment ℝ x (P.vertices (j+1)) ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset hxj (right_mem_segment ℝ _ _)).trans
      (P.inside j hj)
  let Q := (single O (P.vertices i) x (P.vertex_mem i (by omega)) hleft).join
    (single O x (P.vertices (j+1)) (P.inside i (by omega) hxi) hright)
  have hh := P.minimum_shortcut_bound hmin i (j+1) (by omega) (by omega) Q
  change j+1-i ≤ 1+1 at hh
  omega

theorem minimum_two_step_not_subset (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    ¬ segment ℝ (P.vertices i) (P.vertices (i+2)) ⊆ O := by
  intro h
  have hh := P.minimum_shortcut_bound hmin i (i+2) (by omega) hi
    (single O (P.vertices i) (P.vertices (i+2)) (P.vertex_mem i (by omega)) h)
  change i+2-i ≤ 1 at hh
  omega

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_MinimumChainGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem adjacent_segments_meet_only_at_bend (a b c : Plane)
    (h : det2 (b-a) (c-b) ≠ 0) {x : Plane}
    (hx : x ∈ segment ℝ a b) (hy : x ∈ segment ℝ b c) : x=b := by
  rw [← Path.range_segment] at hx hy
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  have hs' : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint b c t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have he := segment_intersection_parameters_unique a b b c h s.val t.val 1 0
    (hs'.trans ht'.symm) (by simp)
  rw [he.1,segmentPoint_one] at hs'
  exact hs'.symm

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_piece_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) : P.vertices (i+1)-P.vertices i ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)))

theorem minimum_bend_det_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0 := by
  intro he
  apply P.minimum_two_step_not_subset hmin i hi
  exact (collinear_segment_subset_union _ _ _ (P.minimum_vertices_ne hmin i (i+2) (by omega) hi) he).trans
    (Set.union_subset (P.inside i (by omega)) (P.inside (i+1) (by omega)))

theorem minimum_adjacent_intersection (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) {x : Plane}
    (hx : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hy : x ∈ segment ℝ (P.vertices (i+1)) (P.vertices (i+2))) : x=P.vertices (i+1) := by
  exact adjacent_segments_meet_only_at_bend _ _ _ (P.minimum_bend_det_ne_zero hmin i hi) hx hy

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalArcInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem minimum_path_injective (P : PolygonalChain O a b) (hab : a ≠ b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) : Function.Injective P.path := by
  have hp : 0 < P.pieces := by
    by_contra h
    have hz : P.pieces=0 := by omega
    exact hab (P.first.symm.trans (hz ▸ P.last))
  change Function.Injective (polygonalArcPath P.vertices P.pieces)
  apply polygonalArcPath_injective P.vertices P.pieces hp
  · intro i hi
    exact P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)
  · intro i j hij hj x hx hy
    by_cases he : j=i+1
    · subst j
      exact ⟨rfl,P.minimum_adjacent_intersection hmin i (by omega) hx hy⟩
    · exact False.elim ((Set.disjoint_left.mp (P.minimum_nonadjacent_disjoint hmin i j (by omega) hj)) hx hy)

end PolygonalChain

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SubdivisionSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

theorem pieceTrace_knot_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : Fin P.pieces) (j : Fin (P.pieces+1))
    (hx : γ (P.knot j) ∈ P.pieceTrace i) :
    γ (P.knot j)=γ (P.knot i.castSucc) ∨ γ (P.knot j)=γ (P.knot i.succ) := by
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i _ hx
  by_cases ht0 : t=0
  · subst t
    simpa [intervalSegment] using Or.inl ht.symm
  by_cases ht1 : t=1
  · subst t
    simpa [intervalSegment] using Or.inr ht.symm
  have hmid := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) t
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have he := hγ ht
  rw [he] at hmid
  exact False.elim (strictMono_no_between_successors P.knot P.increasing i j hmid)

theorem pieceTrace_other_piece_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i j : Fin P.pieces) (hij : i ≠ j) (x : Plane)
    (hx : x ∈ P.pieceTrace i) (hy : x ∈ P.pieceTrace j) :
    x=γ (P.knot i.castSucc) ∨ x=γ (P.knot i.succ) := by
  obtain ⟨s,hs⟩ := P.pieceTrace_parameter i x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter j x hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl (by simpa [intervalSegment] using hs.symm)
  by_cases hs1 : s=1
  · subst s
    exact Or.inr (by simpa [intervalSegment] using hs.symm)
  have hsbetween := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) s
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩
  have htbetween := intervalSegment_between (P.knot j.castSucc) (P.knot j.succ) t
    (P.increasing.monotone (by change j.val ≤ j.val+1; omega))
  have he := hγ (hs.trans ht.symm)
  rw [he] at hsbetween
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := P.increasing.monotone (show i.succ ≤ j.castSucc by change i.val+1 ≤ j.val; exact hij)
    exact False.elim (hsbetween.2.not_ge (hgap.trans htbetween.1))
  · have hgap := P.increasing.monotone (show j.succ ≤ i.castSucc by change j.val+1 ≤ i.val; exact hji)
    exact False.elim (hsbetween.1.not_ge (htbetween.2.trans hgap))

end Zarankiewicz.PolygonalParametrization

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_DrawingSubdivisionGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RoundDiskClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical Topology

theorem dist_le_of_mem_closedRoundDisk (z x : Plane) (r : ℝ) (hr : 0 ≤ r)
    (hx : x ∈ closedRoundDisk z r) : dist x z ≤ r := by
  change (x.1-z.1)^2+(x.2-z.2)^2 ≤ r^2 at hx
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff,abs_le,abs_le]
  have h₁ := sq_nonneg (x.1-z.1)
  have h₂ := sq_nonneg (x.2-z.2)
  constructor <;> constructor <;> nlinarith

theorem exists_round_disk_clearance {ι : Type*} [Fintype ι]
    (z : ι → Plane) (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hz : ∀ i, z i ∉ K i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, Disjoint (closedRoundDisk (z i) r) (K i) := by
  have hex (i : ι) : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z i) ε ⊆ (K i)ᶜ :=
    Metric.mem_nhds_iff.mp ((hK i).isClosed.isOpen_compl.mem_nhds (hz i))
  choose radius hpos hclear using hex
  obtain ⟨r,hr,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  refine ⟨r,hr,?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro x hx hmem
  have hd := dist_le_of_mem_closedRoundDisk (z i) x r hr.le hx
  exact hclear i (hd.trans_lt (hbound i (Finset.mem_univ _))) hmem

theorem exists_disjoint_round_disks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r) := by
  obtain ⟨δ,hδ,hgap⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2)) (fun ij => dist (z ij.1) (z ij.2)) (by
      intro ij hij
      exact dist_pos.mpr (hz.ne (Finset.mem_filter.mp hij).2))
  refine ⟨δ/3,by positivity,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h₁ := dist_le_of_mem_closedRoundDisk (z i) x (δ/3) (by positivity) hx
  have h₂ := dist_le_of_mem_closedRoundDisk (z j) x (δ/3) (by positivity) hy
  have htri := dist_triangle (z i) x (z j)
  rw [dist_comm (z i) x] at htri
  have hg := hgap (i,j) (by simpa using hij)
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_MarkedCurveDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedRoundDisk_mono (z : Plane) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    closedRoundDisk z r ⊆ closedRoundDisk z s := by
  intro x hx
  change squaredLength (x-z) ≤ r^2 at hx
  change squaredLength (x-z) ≤ s^2
  nlinarith

theorem finite_curve_mark_isolation {E M : Type*} [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hγ : ∀ e, Continuous (γ e))
    (mark : M → Plane) (hm : Function.Injective mark)
    (O : E → M → Set unitInterval) (hO : ∀ e k, IsOpen (O e k))
    (hvisit : ∀ e k t, γ e t=mark k → t ∈ O e k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r → t ∈ O e k) := by
  let K : E × M → Set Plane := fun ek => γ ek.1 '' (O ek.1 ek.2)ᶜ
  have hK (ek : E × M) : IsCompact (K ek) :=
    (hO ek.1 ek.2).isClosed_compl.isCompact.image (hγ ek.1)
  have hnot (ek : E × M) : mark ek.2 ∉ K ek := by
    rintro ⟨t,ht,he⟩
    exact ht (hvisit ek.1 ek.2 t he)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun ek : E × M => mark ek.2) K hK hnot
  obtain ⟨σ,hσ,hdisjoint⟩ := exists_disjoint_round_disks mark hm
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro k l hkl
    exact (hdisjoint k l hkl).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro e k t ht
    by_contra hn
    have hd : γ e t ∈ closedRoundDisk (mark k) ρ :=
      closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _) ht
    exact Set.disjoint_left.mp (hclear (e,k)) hd ⟨t,hn,rfl⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ParameterNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem parameterNeighborhood_open (t : unitInterval) (δ : ℝ) :
    IsOpen (parameterNeighborhood t δ) := by
  apply isOpen_lt _ continuous_const
  fun_prop

theorem parameterNeighborhood_between (t : unitInterval) (δ : ℝ)
    (u v w : unitInterval) (hu : u ∈ parameterNeighborhood t δ)
    (hv : v ∈ parameterNeighborhood t δ) (huw : u ≤ w) (hwv : w ≤ v) :
    w ∈ parameterNeighborhood t δ := by
  change |w.val-t.val| < δ
  change |u.val-t.val| < δ at hu
  change |v.val-t.val| < δ at hv
  rw [abs_lt] at hu hv ⊢
  have h₁ : u.val ≤ w.val := huw
  have h₂ : w.val ≤ v.val := hwv
  constructor <;> linarith

theorem parameterNeighborhood_ordered (a b : unitInterval) (δ : ℝ) (hδ : 0 < δ)
    (hab : a < b) (hd : Disjoint (parameterNeighborhood a δ) (parameterNeighborhood b δ))
    (u v : unitInterval) (hu : u ∈ parameterNeighborhood a δ)
    (hv : v ∈ parameterNeighborhood b δ) : u < v := by
  by_contra hn
  have hvu : v ≤ u := le_of_not_gt hn
  have ha : a ∈ parameterNeighborhood a δ := by simpa [parameterNeighborhood] using hδ
  have hb : b ∈ parameterNeighborhood b δ := by simpa [parameterNeighborhood] using hδ
  by_cases hva : v ≤ a
  · exact Set.disjoint_left.mp hd ha (parameterNeighborhood_between b δ v b a hv hb hva hab.le)
  · have hav : a ≤ v := (lt_of_not_ge hva).le
    exact Set.disjoint_left.mp hd (parameterNeighborhood_between a δ a u v ha hu hav hvu) hv

theorem finite_parameter_neighborhoods {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → unitInterval) (ht : Function.Injective t) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, t i ∈ parameterNeighborhood (t i) δ) ∧
      (∀ i j, i ≠ j → Disjoint (closure (parameterNeighborhood (t i) δ))
        (closure (parameterNeighborhood (t j) δ))) := by
  obtain ⟨ε,hε,hsep⟩ := finite_node_separation (fun i => (t i).val)
    (Subtype.val_injective.comp ht)
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hclosed (i : ι) : IsClosed {s : unitInterval | |s.val-(t i).val| ≤ δ} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hcl (i : ι) : closure (parameterNeighborhood (t i) δ) ⊆
      {s : unitInterval | |s.val-(t i).val| ≤ δ} :=
    closure_minimal (fun s hh => le_of_lt (show |s.val-(t i).val| < δ from hh)) (hclosed i)
  refine ⟨δ,hδ,fun i => by simpa [parameterNeighborhood] using hδ,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hcl i hx
  have hy' := hcl j hy
  have hg := hsep i j hij
  have htri := abs_sub_le (t i).val x.val (t j).val
  rw [abs_sub_comm (t i).val x.val] at htri
  change |x.val-(t i).val| ≤ δ at hx'
  change |x.val-(t j).val| ≤ δ at hy'
  dsimp [δ] at hx' hy'
  linarith

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CurveDiskIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_injective_curve_disk_isolation {E M : Type*}
    [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hc : ∀ e, Continuous (γ e))
    (hi : ∀ e, Function.Injective (γ e)) (mark : M → Plane) (hm : Function.Injective mark) :
    ∃ δ : E → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r →
        ∃ u : unitInterval, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  have hfinite (e : E) : ((γ e) ⁻¹' Set.range mark).Finite :=
    Set.Finite.preimage (hi e).injOn (Set.finite_range mark)
  have hex (e : E) : ∃ δ : ℝ, 0 < δ ∧
      ∀ u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u δ)) (closure (parameterNeighborhood v δ)) := by
    let S := (γ e) ⁻¹' Set.range mark
    let : Fintype S := (hfinite e).fintype
    let : DecidableEq S := Classical.decEq _
    obtain ⟨δ,hδ,_,hd⟩ := finite_parameter_neighborhoods (fun t : S => t.val) Subtype.val_injective
    refine ⟨δ,hδ,?_⟩
    intro u v hu hv huv
    exact hd ⟨u,hu⟩ ⟨v,hv⟩ (fun he => huv (congrArg Subtype.val he))
  choose δ hδ hseparate using hex
  let O : E → M → Set unitInterval := fun e k =>
    {t | ∃ u, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)}
  have hO (e : E) (k : M) : IsOpen (O e k) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro t ⟨u,hu,ht⟩
    exact Filter.mem_of_superset ((parameterNeighborhood_open u (δ e)).mem_nhds ht)
      (fun s hs => ⟨u,hu,hs⟩)
  obtain ⟨r,hr,hdisks,hvisits⟩ := finite_curve_mark_isolation γ hc mark hm O hO (by
    intro e k t ht
    exact ⟨t,ht,by simpa [parameterNeighborhood] using hδ e⟩)
  exact ⟨δ,r,hδ,hr,hdisks,hvisits,hseparate⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RoundDiskVisits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem continuous_path_squared_distance {a b : Plane} (γ : Path a b) (z : Plane) :
    Continuous (fun t : ℝ => squaredLength (γ.extend t-z)) := by
  unfold squaredLength
  fun_prop

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SublevelExtrema
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem sublevel_passage_extrema (f : ℝ → ℝ) (hf : Continuous f) (r τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hvisit : f τ < r) :
    ∃ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧
      a ≤ τ ∧ τ ≤ b ∧ f a ≤ r ∧ f b ≤ r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → a ≤ t ∧ t ≤ b) ∧
      (0 < a → f a=r) ∧ (b < 1 → f b=r) ∧
      (0 < τ → a < τ) ∧ (τ < 1 → τ < b) := by
  let S : Set ℝ := Set.Icc 0 1 ∩ {t | f t ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hτS : τ ∈ S := ⟨hτ,hvisit.le⟩
  obtain ⟨a,ha⟩ := hS.exists_isLeast ⟨τ,hτS⟩
  obtain ⟨b,hb⟩ := hS.exists_isGreatest ⟨τ,hτS⟩
  have hfa (ha0 : 0 < a) : f a=r := by
    have hf0 : r < f 0 := by
      apply lt_of_not_ge
      intro h
      have hh := ha.2 (show (0 : ℝ) ∈ S from ⟨⟨le_rfl,zero_le_one⟩,h⟩)
      linarith
    apply le_antisymm ha.1.2
    by_contra hn
    have hlt : f a < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha.1.1.1 hf.continuousOn ⟨hlt.le,hf0.le⟩
    have hmem : t ∈ S := ⟨⟨ht.1,ht.2.trans ha.1.1.2⟩,he.le⟩
    have hta : t=a := le_antisymm ht.2 (ha.2 hmem)
    rw [hta] at he
    exact hlt.ne he
  have hfb (hb1 : b < 1) : f b=r := by
    have hf1 : r < f 1 := by
      apply lt_of_not_ge
      intro h
      have hh := hb.2 (show (1 : ℝ) ∈ S from ⟨⟨zero_le_one,le_rfl⟩,h⟩)
      linarith
    apply le_antisymm hb.1.2
    by_contra hn
    have hlt : f b < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb.1.1.2 hf.continuousOn ⟨hlt.le,hf1.le⟩
    have hmem : t ∈ S := ⟨⟨hb.1.1.1.trans ht.1,ht.2⟩,he.le⟩
    have htb : t=b := le_antisymm (hb.2 hmem) ht.1
    rw [htb] at he
    exact hlt.ne he
  refine ⟨a,b,ha.1.1,hb.1.1,ha.2 hτS,hb.2 hτS,ha.1.2,hb.1.2,
    fun t ht hh => ⟨ha.2 ⟨ht,hh⟩,hb.2 ⟨ht,hh⟩⟩,hfa,hfb,?_,?_⟩
  · intro ht0
    apply lt_of_le_of_ne (ha.2 hτS)
    intro he
    have h := hfa (he.symm ▸ ht0)
    rw [he] at h
    exact hvisit.ne h
  · intro ht1
    apply lt_of_le_of_ne (hb.2 hτS)
    intro he
    have h := hfb (he ▸ ht1)
    rw [← he] at h
    exact hvisit.ne h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_DiskPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem nonempty_diskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ)
    (τ : unitInterval) (hτ : squaredLength (γ τ-z) < r^2) :
    Nonempty (DiskPassage γ z r τ) := by
  obtain ⟨u,v,hu,hv,huτ,hτv,hfu,hfv,hall,hbu,hbv,hsu,hsv⟩ := sublevel_passage_extrema
    (fun t => squaredLength (γ.extend t-z)) (continuous_path_squared_distance γ z) (r^2) τ.val τ.property
    (by simpa using hτ)
  let u' : unitInterval := ⟨u,hu⟩
  let v' : unitInterval := ⟨v,hv⟩
  have heu : γ.extend u=γ u' := γ.extend_extends' u'
  have hev : γ.extend v=γ v' := γ.extend_extends' v'
  rw [heu] at hfu hbu
  rw [hev] at hfv hbv
  exact ⟨{
    enter := u'
    leave := v'
    enter_le_mark := huτ
    mark_le_leave := hτv
    enter_mem := hfu
    leave_mem := hfv
    all_visits := fun t ht => hall t.val t.property (by simpa [closedRoundDisk] using ht)
    enter_boundary := hbu
    leave_boundary := hbv
    strict_enter := hsu
    strict_leave := hsv }⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OrderedPassages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem diskPassage_separated {a b z w : Plane} {γ : Path a b} {r δ : ℝ}
    {s t : unitInterval} (P : DiskPassage γ z r s) (Q : DiskPassage γ w r t)
    (hst : s < t) (hδ : 0 < δ)
    (hd : Disjoint (closure (parameterNeighborhood s δ)) (closure (parameterNeighborhood t δ)))
    (hP : P.leave ∈ parameterNeighborhood s δ) (hQ : Q.enter ∈ parameterNeighborhood t δ) :
    P.leave < Q.enter :=
  parameterNeighborhood_ordered s t δ hδ hst (hd.mono subset_closure subset_closure) P.leave Q.enter hP hQ

theorem ordered_passage_leave_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).leave) := by
  intro i j hij
  exact (hsep i j hij).trans (P j).enter_lt_leave

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RadialExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_segment_translated (a b z : Plane) (t : ℝ) :
    squaredLength (segmentPoint a b t-z)=
      squaredLength (a-z)+2*t*dot2 (a-z) (b-a)+t^2*squaredLength (b-a) := by
  dsimp [squaredLength,dot2,segmentPoint]
  ring

theorem exterior_segment_of_dot (z a b : Plane) (r : ℝ)
    (ha : r^2 < squaredLength (a-z)) (hd : 0 ≤ dot2 (a-z) (b-a)) :
    segment ℝ a b ⊆ {x | r^2 < squaredLength (x-z)} := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  change r^2 < squaredLength (segmentPoint a b t.val-z)
  rw [squaredLength_segment_translated]
  have h₁ : 0 ≤ 2*t.val*dot2 (a-z) (b-a) := mul_nonneg (mul_nonneg (by norm_num) t.property.1) hd
  have h₂ : 0 ≤ t.val^2*squaredLength (b-a) := by dsimp [squaredLength]; positivity
  linarith

theorem radial_spur_exterior (z x : Plane) (r α : ℝ)
    (hx : squaredLength (x-z)=r^2) (hr : 0 < r) (hα : 0 < α) :
    segment ℝ x (x+α • (x-z)) ⊆ insert x {y | r^2 < squaredLength (y-z)} := by
  intro y hy
  rw [← Path.range_segment] at hy
  obtain ⟨t,rfl⟩ := hy
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  by_cases ht : t.val=0
  · left
    change segmentPoint x (x+α • (x-z)) t.val=x
    rw [ht,segmentPoint_zero]
  · right
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    change r^2 < squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)
    have he : squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)=
        (1+t.val*α)^2*squaredLength (x-z) := by
      dsimp [squaredLength,segmentPoint]
      ring
    rw [he,hx]
    have hp := mul_pos htpos hα
    nlinarith [sq_pos_of_pos hr,mul_pos hp (sq_pos_of_pos hr)]

theorem radial_tip_dot (z x : Plane) (α : ℝ) :
    dot2 (x-z) ((x+α • (x-z))-x)=α*squaredLength (x-z) := by
  dsimp [dot2,squaredLength]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_BoundaryCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem exists_radial_tip_collar (z x : Plane) (r : ℝ) (hr : 0 < r)
    (hx : squaredLength (x-z)=r^2) (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z)) ⊆ U ∩ insert x {y | r^2 < squaredLength (y-z)} ∧
      (∀ y, dist y x < ρ → r^2 < squaredLength (y-z) →
        segment ℝ (x+α • (x-z)) y ⊆ U ∩ {p | r^2 < squaredLength (p-z)}) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hxu
  have hmove : Continuous (fun α : ℝ => x+α • (x-z)) := by fun_prop
  have hevent : ∀ᶠ α : ℝ in 𝓝 0, x+α • (x-z) ∈ Metric.ball x ε :=
    hmove.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds x hε)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  let α := δ/2
  have hα : 0 < α := by dsimp [α]; positivity
  have htip : x+α • (x-z) ∈ Metric.ball x ε := hd (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hα]
    dsimp [α]
    linarith)
  have hdpos : 0 < dot2 (x-z) ((x+α • (x-z))-x) := by
    rw [radial_tip_dot,hx]
    exact mul_pos hα (sq_pos_of_pos hr)
  have hdot : Continuous (fun y : Plane => dot2 (y-z) ((x+α • (x-z))-y)) := by
    unfold dot2
    fun_prop
  have hev : ∀ᶠ y : Plane in 𝓝 x, 0 < dot2 (y-z) ((x+α • (x-z))-y) :=
    continuousAt_const.eventually_lt hdot.continuousAt hdpos
  obtain ⟨σ,hσ,hσdot⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨α,min ε σ,hα,lt_min hε hσ,?_,?_⟩
  · apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) htip).trans hball
    · exact radial_spur_exterior z x r α hx hr hα
  · intro y hy hout
    apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset htip (hy.trans_le (min_le_left _ _))).trans hball
    · rw [segment_symm]
      exact exterior_segment_of_dot z y (x+α • (x-z)) r hout
        (hσdot (hy.trans_le (min_le_right _ _))).le

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteDiskCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem isOpen_disk_exterior (z : Plane) (r : ℝ) :
    IsOpen {x | r^2 < squaredLength (x-z)} := by
  apply isOpen_lt continuous_const
  unfold squaredLength
  fun_prop

theorem isOpen_outsideDisks {ι : Type*} [Finite ι] (z : ι → Plane) (r : ℝ) :
    IsOpen (outsideDisks z r) := by
  have he : outsideDisks z r=⋂ i, {x | r^2 < squaredLength (x-z i)} := by
    ext x
    simp [outsideDisks]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_disk_exterior (z i) r)

theorem exists_finite_disk_collar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k : ι) (x : Plane) (hx : squaredLength (x-z k)=r^2)
    (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z k)) ⊆ U ∩ insert x (outsideDisks z r) ∧
      (∀ y, dist y x < ρ → y ∈ outsideDisks z r →
        segment ℝ (x+α • (x-z k)) y ⊆ U ∩ outsideDisks z r) := by
  let V : Set Plane := U ∩ ⋂ j : {j : ι // j ≠ k}, {y | r^2 < squaredLength (y-z j.val)}
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite (fun j => isOpen_disk_exterior (z j.val) r))
  have hxV : x ∈ V := by
    refine ⟨hxu,Set.mem_iInter.mpr (fun j => ?_)⟩
    change r^2 < squaredLength (x-z j.val)
    apply lt_of_not_ge
    intro hh
    exact Set.disjoint_left.mp (hd k j.val (Ne.symm j.property)) (show x ∈ closedRoundDisk (z k) r from hx.le) hh
  obtain ⟨α,ρ,hα,hρ,hspur,hnear⟩ := exists_radial_tip_collar (z k) x r hr hx V hV hxV
  have hout : V ∩ {p | r^2 < squaredLength (p-z k)} ⊆ U ∩ outsideDisks z r := by
    intro p hp
    refine ⟨hp.1.1,fun j => ?_⟩
    by_cases he : j=k
    · simpa [he] using hp.2
    · exact Set.mem_iInter.mp hp.1.2 ⟨j,he⟩
  refine ⟨α,ρ,hα,hρ,?_,?_⟩
  · intro p hp
    obtain ⟨hpV,hpx | hpout⟩ := hspur hp
    · exact ⟨hpV.1,Or.inl hpx⟩
    · exact ⟨hpV.1,Or.inr (hout ⟨hpV,hpout⟩).2⟩
  · intro y hy hyout
    exact (hnear y hy (hyout k)).trans hout

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteLineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical

theorem lineAvoidancePolynomial_eval (z a v : Plane) (t : ℝ) :
    (lineAvoidancePolynomial z a v).eval t = det2 (z+(t,t^2)-a) v := by
  simp [lineAvoidancePolynomial,det2]
  ring

theorem lineAvoidancePolynomial_ne_zero (z a v : Plane) (hv : v ≠ 0) :
    lineAvoidancePolynomial z a v ≠ 0 := by
  intro h
  have h₁ := congrArg (fun p : ℝ[X] => p.coeff 1) h
  have h₂ := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [lineAvoidancePolynomial,coeff_C_mul] at h₁ h₂
  apply hv
  exact Prod.ext h₂ h₁

theorem exists_near_avoiding_lines {ι : Type*} [Fintype ι] (a v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ o : Plane, dist o z < ε ∧ ∀ i, det2 (o-a i) (v i) ≠ 0 := by
  let bad : Finset ℝ := Finset.univ.biUnion (fun i => (lineAvoidancePolynomial z (a i) (v i)).roots.toFinset)
  have hδ : 0 < min ε 1 := lt_min hε (by norm_num)
  obtain ⟨t,ht⟩ := ((Set.Ioo_infinite hδ).sdiff bad.finite_toSet).nonempty
  have ht0 : 0 < t := ht.1.1
  have htε : t < ε := lt_of_lt_of_le ht.1.2 (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le ht.1.2 (min_le_right _ _)
  refine ⟨z+(t,t^2),?_,?_⟩
  · have ht2 : t^2 < ε := by nlinarith
    simp only [Prod.dist_eq,Prod.fst_add,Prod.snd_add,Real.dist_eq,add_sub_cancel_left]
    exact max_lt (by simpa [abs_of_pos ht0] using htε) (by simpa [abs_of_nonneg (sq_nonneg t)] using ht2)
  · intro i hi
    have hp : (lineAvoidancePolynomial z (a i) (v i)).eval t = 0 := by
      rwa [lineAvoidancePolynomial_eval]
    apply ht.2
    change t ∈ bad
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [mem_roots (lineAvoidancePolynomial_ne_zero z (a i) (v i) (hv i))] using hp

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_VertexDiskSpokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_vertex_disk_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Plane) (r : ℝ) (hr : 0 < r) (p : ι → Plane) (hp : Function.Injective p)
    (hcircle : ∀ i, squaredLength (p i-z)=r^2) :
    ∃ v : Plane, squaredLength (v-z) < r^2 ∧
      (∀ i, v ≠ p i) ∧ (∀ i j, i ≠ j → det2 (p i-v) (p j-v) ≠ 0) := by
  classical
  let S := {ij : ι × ι // ij.1 ≠ ij.2}
  obtain ⟨v,hv,havoid⟩ := exists_near_avoiding_lines
    (fun ij : S => p ij.val.1) (fun ij : S => p ij.val.2-p ij.val.1)
    (fun ij => sub_ne_zero.mpr (hp.ne (Ne.symm ij.property))) z (r/3) (by positivity)
  have hinside : squaredLength (v-z) < r^2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff,abs_lt,abs_lt] at hv
    have h₁ := mul_pos (sub_pos.mpr hv.1.2) (show 0 < r/3+(v.1-z.1) by linarith [hv.1.1])
    have h₂ := mul_pos (sub_pos.mpr hv.2.2) (show 0 < r/3+(v.2-z.2) by linarith [hv.2.1])
    change (v.1-z.1)^2+(v.2-z.2)^2 < r^2
    nlinarith [sq_pos_of_pos hr]
  refine ⟨v,hinside,?_,?_⟩
  · intro i he
    rw [he,hcircle i] at hinside
    exact lt_irrefl _ hinside
  · intro i j hij
    have he : det2 (p i-v) (p j-v) = -det2 (v-p i) (p j-p i) := by dsimp [det2]; ring
    rw [he]
    exact neg_ne_zero.mpr (havoid ⟨(i,j),hij⟩)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PathEndpointNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem path_near_endpoints {a b : Plane} (γ : Path a b) (ρ σ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ) :
    ∃ u v : unitInterval, 0 < u ∧ u < v ∧ v < 1 ∧
      dist (γ u) a < ρ ∧ dist (γ v) b < σ := by
  have he0 : ∀ᶠ t : ℝ in 𝓝 0, γ.extend t ∈ Metric.ball a ρ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds a hρ)
  have he1 : ∀ᶠ t : ℝ in 𝓝 1, γ.extend t ∈ Metric.ball b σ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds b hσ)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he0
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he1
  let p := min (δ/2) (1/4)
  let q := min (ε/2) (1/4)
  have hp : 0 < p := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  have hp4 : p ≤ 1/4 := min_le_right _ _
  have hq4 : q ≤ 1/4 := min_le_right _ _
  have hpd : p < δ := (min_le_left _ _).trans_lt (by linarith)
  have hqe : q < ε := (min_le_left _ _).trans_lt (by linarith)
  let u : unitInterval := ⟨p,hp.le,by linarith⟩
  let v : unitInterval := ⟨1-q,by linarith,by linarith⟩
  have hu : γ.extend p ∈ Metric.ball a ρ := hd (by simpa [Real.dist_eq,abs_of_pos hp] using hpd)
  have hv : γ.extend (1-q) ∈ Metric.ball b σ := he (by
    simpa [Real.dist_eq,abs_of_pos hq] using hqe)
  rw [show γ.extend p=γ u from γ.extend_extends' u] at hu
  rw [show γ.extend (1-q)=γ v from γ.extend_extends' v] at hv
  exact ⟨u,v,hp,(by change p < 1-q; linarith),(by change 1-q < 1; linarith),hu,hv⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CompactCorridors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_compact_corridors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K O : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, K i ⊆ O i) :
    ∃ U : ι → Set Plane, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      (∀ i, U i ⊆ O i) ∧ (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by
  have hex (i j : ι) : ∃ A B : Set Plane, IsOpen A ∧ IsOpen B ∧ K i ⊆ A ∧ K j ⊆ B ∧
      (i ≠ j → Disjoint A B) := by
    by_cases he : i=j
    · exact ⟨Set.univ,Set.univ,isOpen_univ,isOpen_univ,Set.subset_univ _,Set.subset_univ _,fun hn => False.elim (hn he)⟩
    · obtain ⟨A,B,hA,hB,hi,hj,hab⟩ := normal_separation (hK i).isClosed (hK j).isClosed (hd i j he)
      exact ⟨A,B,hA,hB,hi,hj,fun _ => hab⟩
  choose A B hA hB hKA hKB hAB using hex
  let U : ι → Set Plane := fun i => O i ∩ ⋂ j, A i j ∩ B j i
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    exact (hO i).inter (isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i)))
  · intro i x hx
    exact ⟨hKO i hx,Set.mem_iInter.mpr (fun j => ⟨hKA i j hx,hKB j i hx⟩)⟩
  · intro i x hx
    exact hx.1
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hAB i j hij)
      (Set.mem_iInter.mp hx.2 j).1 (Set.mem_iInter.mp hy.2 i).2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SimultaneousPolygonalReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_simple_polygonalChain {O : Set Plane} {a b : Plane} (hab : a ≠ b)
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, Function.Injective P.path ∧ Set.range P.path ⊆ O := by
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain h
  exact ⟨P,P.minimum_path_injective hab hmin,P.path_range_subset⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalBoundaryReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem simple_path_interior_of_range_insert {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (O : Set Plane)
    (hrange : Set.range γ ⊆ insert a (insert b O))
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) : γ t ∈ O := by
  rcases hrange ⟨t,rfl⟩ with ha | hb | ho
  · have he := hinj (ha.trans γ.source.symm)
    exact False.elim (ht.1.ne he.symm)
  · have he := hinj (hb.trans γ.target.symm)
    exact False.elim (ht.2.ne he)
  · exact ho

theorem polygonal_replacement_with_spurs (O : Set Plane) (hO : IsOpen O)
    (a a' b' b : Plane) (hab : a ≠ b) (γ : Path a' b')
    (hγ : ∀ t, γ t ∈ O)
    (ha : segment ℝ a a' ⊆ insert a (insert b O))
    (hb : segment ℝ b' b ⊆ insert a (insert b O)) :
    ∃ P : PolygonalChain (insert a (insert b O)) a b,
      Function.Injective P.path ∧
      (∀ t : unitInterval, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ O) := by
  obtain ⟨Q⟩ := nonempty_polygonalChain_of_path γ O hO hγ
  let S := insert a (insert b O)
  let Q' : PolygonalChain S a' b' := Q.widen (fun _ hx => Or.inr (Or.inr hx))
  let L : PolygonalChain S a a' := PolygonalChain.single S a a' (Or.inl rfl) ha
  let R : PolygonalChain S b' b := PolygonalChain.single S b' b
    (Or.inr (Or.inr (by simpa using hγ 1))) hb
  obtain ⟨P,hP,hR⟩ := exists_simple_polygonalChain hab ⟨(L.join Q').join R⟩
  exact ⟨P,hP,fun t ht => simple_path_interior_of_range_insert P.path hP O hR t ht⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ExteriorArcReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exterior_arc_polygonal_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : ι) (a b : Plane) (hab : a ≠ b)
    (ha : squaredLength (a-z k)=r^2) (hb : squaredLength (b-z l)=r^2)
    (γ : Path a b) (U : Set Plane) (hU : IsOpen U) (hγU : ∀ t, γ t ∈ U)
    (hγout : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ t ∈ outsideDisks z r) :
    ∃ P : PolygonalChain U a b, Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) := by
  obtain ⟨α,ρ,hα,hρ,hspurA,hnearA⟩ := exists_finite_disk_collar z r hr hd k a ha U hU
    (by simpa using hγU 0)
  obtain ⟨β,σ,hβ,hσ,hspurB,hnearB⟩ := exists_finite_disk_collar z r hr hd l b hb U hU
    (by simpa using hγU 1)
  obtain ⟨u,v,hu0,huv,hv1,hu,hv⟩ := path_near_endpoints γ ρ σ hρ hσ
  let a' := a+α • (a-z k)
  let b' := b+β • (b-z l)
  let O := U ∩ outsideDisks z r
  have hO : IsOpen O := hU.inter (isOpen_outsideDisks z r)
  have hleft : segment ℝ a' (γ u) ⊆ O := hnearA (γ u) hu (hγout u ⟨hu0,huv.trans hv1⟩)
  have hright : segment ℝ (γ v) b' ⊆ O := by
    rw [segment_symm]
    exact hnearB (γ v) hv (hγout v ⟨hu0.trans huv,hv1⟩)
  have hmiddle : Set.range (pathSubarc γ u v) ⊆ O := by
    rw [pathSubarc_range γ u v huv]
    rintro x ⟨t,ht,rfl⟩
    exact ⟨hγU t,hγout t ⟨hu0.trans_le ht.1,ht.2.trans_lt hv1⟩⟩
  let η : Path a' b' := (Path.segment a' (γ u)).trans
    ((pathSubarc γ u v).trans (Path.segment (γ v) b'))
  have hη : Set.range η ⊆ O := by
    dsimp [η]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset hleft (Set.union_subset hmiddle hright)
  have hA : segment ℝ a a' ⊆ insert a (insert b O) := by
    intro x hx
    obtain ⟨hxU,hxa | hxout⟩ := hspurA hx
    · exact Or.inl hxa
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  have hB : segment ℝ b' b ⊆ insert a (insert b O) := by
    rw [segment_symm]
    intro x hx
    obtain ⟨hxU,hxb | hxout⟩ := hspurB hx
    · exact Or.inr (Or.inl hxb)
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  obtain ⟨Q,hQ,hQout⟩ := polygonal_replacement_with_spurs O hO a a' b' b hab η
    (fun t => hη ⟨t,rfl⟩) hA hB
  have hSU : insert a (insert b O) ⊆ U := by
    intro x hx
    rcases hx with rfl | rfl | hx
    · simpa using hγU 0
    · simpa using hγU 1
    · exact hx.1
  exact ⟨Q.widen hSU,hQ,fun t ht => (hQout t ht).2⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SimultaneousExteriorArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_exterior_arc_replacements {E M : Type*}
    [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]
    (z : M → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : E → M) (a b : E → Plane) (hab : ∀ e, a e ≠ b e)
    (ha : ∀ e, squaredLength (a e-z (k e))=r^2)
    (hb : ∀ e, squaredLength (b e-z (l e))=r^2)
    (γ : ∀ e, Path (a e) (b e))
    (hdisjoint : ∀ e f, e ≠ f → Disjoint (Set.range (γ e)) (Set.range (γ f)))
    (hγ : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ e t ∈ outsideDisks z r) :
    ∃ U : E → Set Plane, ∃ P : ∀ e, PolygonalChain (U e) (a e) (b e),
      (∀ e, IsOpen (U e)) ∧ (∀ e, Function.Injective (P e).path) ∧
      (∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → (P e).path t ∈ outsideDisks z r) ∧
      (∀ e f, e ≠ f → Disjoint (Set.range (P e).path) (Set.range (P f).path)) := by
  obtain ⟨U,hU,hKU,_,hUU⟩ := finite_compact_corridors (fun e => Set.range (γ e))
    (fun _ => Set.univ) (fun e => isCompact_range (γ e).continuous) hdisjoint
    (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  have hex (e : E) : ∃ P : PolygonalChain (U e) (a e) (b e), Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) :=
    exterior_arc_polygonal_replacement z r hr hd (k e) (l e) (a e) (b e) (hab e)
      (ha e) (hb e) (γ e) (U e) (hU e) (fun t => hKU e ⟨t,rfl⟩) (hγ e)
  choose P hP hR using hex
  exact ⟨U,P,hU,hP,hR,fun e f hef =>
    (hUU e f hef).mono (P e).path_range_subset (P f).path_range_subset⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem alternatingPath_hasFiniteAffineCover (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) (hp : ∀ i, HasFiniteAffineCover (p i))
    (hq : ∀ i, HasFiniteAffineCover (q i)) :
    (k : ℕ) → HasFiniteAffineCover (alternatingPath a b p q k)
  | 0 => hp 0
  | k+1 => ((alternatingPath_hasFiniteAffineCover a b p q hp hq k).trans (hq k)).trans (hp (k+1))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DrawingMarks
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked subdivision parameters, incidence graphs, and edge walks. -/

section

/-! The actual finite marks and marked parameters of a continuous drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem drawingMarks_finite [Fintype Vertex] (D : FiniteIntersectionDrawing graph) : (drawingMarks D).Finite :=
  (Set.finite_range D.vertex).union D.crossings_finite

theorem marked_parameters_finite [Fintype Vertex] (D : FiniteIntersectionDrawing graph) (e : Edge) :
    ((D.edge e) ⁻¹' drawingMarks D).Finite :=
  Set.Finite.preimage (D.edge_injective e).injOn (drawingMarks_finite D)

end Paper170Geometry

end
end

section

/-! Increasing enumeration of the actual marked parameters, with both endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem exists_sorted_drawing_parameters [Fintype Vertex] (D : FiniteIntersectionDrawing graph)
    (e : Edge) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧
      Set.range t=(D.edge e) ⁻¹' drawingMarks D := by
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset (marked_parameters_finite D e).toFinset
    (by simpa using marked_parameter_zero D e) (by simpa using marked_parameter_one D e)
  exact ⟨k,hk,t,ht,h0,h1,by simpa using hR⟩

end Paper170Geometry

end
end

section

/-! Actual subdivision segments, parameter witnesses, and marked-point endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem subdivision_mark_endpoint (D : Paper170.AdmissibleDrawing graph)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (e : Edge) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ (P e).pieceTrace i) (hm : x ∈ drawingMarks D.toFiniteIntersectionDrawing) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hmark e t (ht.symm ▸ hm)
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

end Paper170Geometry

end
end

section

/-! Refined segments of the actual drawing meet only at common subdivision endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_curve_meeting_mark (D : Paper170.AdmissibleDrawing graph) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hy : x ∈ Set.range (D.edge f)) :
    x ∈ drawingMarks D.toFiniteIntersectionDrawing := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl ⟨(graph.src e),by simpa using hs⟩
  by_cases hs1 : s=1
  · subst s
    exact Or.inl ⟨(graph.dst e),by simpa using hs⟩
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨(graph.src f),by simpa using ht⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inl ⟨(graph.dst f),by simpa using ht⟩
  exact Or.inr ⟨e,f,hef,
    ⟨s,⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩,hs⟩,
    ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,ht⟩⟩

theorem drawing_pieces_meeting_endpoints (D : Paper170.AdmissibleDrawing graph)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (p q : DrawingPiece P) (hpq : p ≠ q) (x : Plane)
    (hx : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p))
    (hy : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q)) :
    (x=drawingPieceStart P p ∨ x=drawingPieceEnd P p) ∧
      (x=drawingPieceStart P q ∨ x=drawingPieceEnd P q) := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  by_cases hef : e=f
  · subst f
    have hij : i ≠ j := fun he => hpq (by subst j; rfl)
    exact ⟨(P e).pieceTrace_other_piece_endpoint (D.edge_injective e) i j hij x hx hy,
      (P e).pieceTrace_other_piece_endpoint (D.edge_injective e) j i (Ne.symm hij) x hy hx⟩
  · have hm := drawing_curve_meeting_mark D e f hef x
      ((P e).pieceTrace_subset_range i hx) ((P f).pieceTrace_subset_range j hy)
    exact ⟨subdivision_mark_endpoint D P hmark e i x hx hm,
      subdivision_mark_endpoint D P hmark f j x hy hm⟩

end Paper170Geometry

end
end

section

/-! The actual straight embedded graph formed by refined drawing segments. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))

theorem drawingSubdivisionGraph_embedding (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) :
    StraightEdgeEmbedding (drawingSubdivisionGraph P) id := by
  refine ⟨Function.injective_id,?_⟩
  rintro a b c d ⟨hab,p,hp⟩ ⟨hcd,q,hq⟩ x hx hy
  by_cases hpq : p=q
  · subst q
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inl ⟨rfl,rfl⟩
  · have hxp : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx
      · simpa only [id_eq,segment_symm] using hx
    have hxq : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q) := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hy
      · simpa only [id_eq,segment_symm] using hy
    obtain ⟨hpe,hqe⟩ := drawing_pieces_meeting_endpoints D P hmark p q hpq x hxp hxq
    have heab : x=a ∨ x=b := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hpe
      · exact hpe.symm
    have hecd : x=c ∨ x=d := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hqe
      · exact hqe.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives a b c d x heab hecd))

end Paper170Geometry

end
end

section

/-! Prescribed subdivision points cannot lie in the interior of a graph segment. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}

theorem subdivision_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (e : Edge) (i : Fin (P e).pieces) (hx : x ∈ (P e).pieceTrace i) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hpoint e t ht
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh

theorem drawingSubdivisionGraph_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (a b : Plane) (hab : (drawingSubdivisionGraph P).Adj a b) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b := by
  obtain ⟨hab,p,hp⟩ := hab
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact subdivision_point_endpoint P x hpoint p.1 p.2 hx
  · have hx' : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      simpa only [segment_symm] using hx
    exact (subdivision_point_endpoint P x hpoint p.1 p.2 hx').symm

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Ports
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isolated drawing disks, retained arcs, and boundary ports. -/

section

/-! The actual finite vertex/crossing marks supply the normalization disk family. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem drawing_disk_isolation [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ δ : Edge → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ x y : DrawingMark D, x ≠ y →
        Disjoint (closedRoundDisk x.val r) (closedRoundDisk y.val r)) ∧
      (∀ e (x : DrawingMark D) t, D.edge e t ∈ closedRoundDisk x.val r →
        ∃ u : unitInterval, D.edge e u=x.val ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, D.edge e u ∈ drawingMarks D → D.edge e v ∈ drawingMarks D → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  let : DecidableEq (DrawingMark D) := Classical.decEq _
  obtain ⟨δ,r,hδ,hr,hd,hv,hs⟩ := finite_injective_curve_disk_isolation
    (fun e => D.edge e) (fun e => (D.edge e).continuous) D.edge_injective
    (fun x : DrawingMark D => x.val) Subtype.val_injective
  refine ⟨δ,r,hδ,hr,hd,hv,?_⟩
  intro e u v hu hv huv
  exact hs e u v ⟨⟨D.edge e u,hu⟩,rfl⟩ ⟨⟨D.edge e v,hv⟩,rfl⟩ huv

end Paper170Geometry

end
end

section

/-! Constructed finite marked-passage decomposition of the given actual drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem nonempty_drawingPassages [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) : Nonempty (DrawingPassages D) := by
  classical
  obtain ⟨δ,r,hδ,hr,hdisks,hvisits,hparam⟩ := drawing_disk_isolation D
  choose k hk τ hτ h0 h1 hR using (fun e => exists_sorted_drawing_parameters D e)
  have hnode (e : Edge) (i : Fin (k e+1)) : D.edge e (τ e i) ∈ drawingMarks D := by
    change τ e i ∈ (D.edge e) ⁻¹' drawingMarks D
    rw [← hR e]
    exact ⟨i,rfl⟩
  have hex (e : Edge) (i : Fin (k e+1)) :
      Nonempty (DiskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)) :=
    nonempty_diskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)
      (by simpa [squaredLength] using sq_pos_of_pos hr)
  let P (e : Edge) (i : Fin (k e+1)) := Classical.choice (hex e i)
  have hlocal (e : Edge) (i : Fin (k e+1)) (t : unitInterval)
      (ht : D.edge e t ∈ closedRoundDisk (D.edge e (τ e i)) r) :
      t ∈ parameterNeighborhood (τ e i) (δ e) := by
    obtain ⟨u,hu,hh⟩ := hvisits e ⟨D.edge e (τ e i),hnode e i⟩ t ht
    have he : u=τ e i := D.edge_injective e hu
    simpa [he] using hh
  have hsep (e : Edge) (i j : Fin (k e+1)) (hij : i < j) :
      (P e i).leave < (P e j).enter := by
    apply diskPassage_separated (P e i) (P e j) (hτ e hij) (hδ e)
    · exact hparam e (τ e i) (τ e j) (hnode e i) (hnode e j) ((hτ e).injective.ne (ne_of_lt hij))
    · exact hlocal e i _ (P e i).leave_mem
    · exact hlocal e j _ (P e j).enter_mem
  exact ⟨{
    radius := r
    radius_pos := hr
    disks_disjoint := hdisks
    count := k
    count_pos := hk
    node := τ
    increasing := hτ
    first := h0
    last := h1
    node_range := hR
    passage := P
    separated := hsep
    visited_mark_on_edge := fun e x t ht => by
      obtain ⟨u,hu,_⟩ := hvisits e x t ht
      exact ⟨u,hu⟩ }⟩

end Paper170Geometry

end
end

section

/-! Actual retained middle arcs: endpoint circles and avoidance of every disk and mark. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem retained_parameter_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter) :
    D.edge i.1 t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  intro x
  apply lt_of_not_ge
  intro hh
  obtain ⟨u,hu⟩ := C.visited_mark_on_edge i.1 x t hh
  have hmu : u ∈ Set.range (C.node i.1) := by
    rw [C.node_range]
    change D.edge i.1 u ∈ drawingMarks D
    rw [hu]
    exact x.property
  obtain ⟨j,hj⟩ := hmu
  have hc : D.edge i.1 (C.node i.1 j)=x.val := (congrArg (D.edge i.1) hj).trans hu
  have hv := (C.passage i.1 j).all_visits t (by rw [hc]; exact hh)
  by_cases hji : j ≤ i.2.castSucc
  · have hm := (ordered_passage_leave_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hji
    exact ht.1.not_ge (hv.2.trans hm)
  · have hij : i.2.succ ≤ j := by
      change i.2.val+1 ≤ j.val
      have hn : ¬ j.val ≤ i.2.val := hji
      omega
    have hm := (ordered_passage_enter_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hij
    exact ht.2.not_ge (hm.trans hv.1)

theorem arc_interior_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    C.arc i t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  exact C.retained_parameter_outside i _ (intervalSegment_strict_between _ _ t (C.arc_gap i) ht)

end Paper170Geometry.DrawingPassages

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DiskFilling
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior disk passages, vertex ports, filling containment, and crossing uniqueness. -/

section

/-! Actual replacement vertices and all incident straight-spoke directions. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem exists_drawing_vertex_placement [Fintype Edge] (C : DrawingPassages D) :
    ∃ v : Vertex → Plane, Function.Injective v ∧
      (∀ i, squaredLength (v i-D.vertex i) < C.radius^2) ∧
      (∀ i (p : C.PortsAt (C.vertexMark i)), v i ≠ C.portPoint p.val) ∧
      (∀ i (p q : C.PortsAt (C.vertexMark i)), p ≠ q →
        det2 (C.portPoint p.val-v i) (C.portPoint q.val-v i) ≠ 0) := by
  classical
  have hex (i : Vertex) : ∃ v : Plane,
      squaredLength (v-D.vertex i) < C.radius^2 ∧
      (∀ p : C.PortsAt (C.vertexMark i), v ≠ C.portPoint p.val) ∧
      (∀ p q : C.PortsAt (C.vertexMark i), p ≠ q → det2 (C.portPoint p.val-v) (C.portPoint q.val-v) ≠ 0) :=
    exists_vertex_disk_point (D.vertex i) C.radius C.radius_pos
      (fun p : C.PortsAt (C.vertexMark i) => C.portPoint p.val)
      (C.portPoint_injective.comp Subtype.val_injective) (C.portsAt_on_circle (C.vertexMark i))
  choose v hv hne hdet using hex
  refine ⟨v,?_,hv,hne,hdet⟩
  intro i j he
  by_contra hij
  have hd := C.disks_disjoint (C.vertexMark i) (C.vertexMark j) (C.vertexMark_injective.ne hij)
  have hi : v i ∈ closedRoundDisk (C.vertexMark i).val C.radius := (hv i).le
  have hj : v j ∈ closedRoundDisk (C.vertexMark j).val C.radius := (hv j).le
  exact Set.disjoint_left.mp hd hi (he.symm ▸ hj)

end Paper170Geometry.DrawingPassages

end
end

section

/-! Count actual spatial chord crossings by their original crossing disks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
open scoped Classical
variable  {D : FiniteIntersectionDrawing graph}

/-- Different original crossing disks remain separately counted, even when
their two chords come from the same pair of graph edges. -/
theorem chordCrossings_ncard_le (C : DrawingPassages D) :
    C.chordCrossings.ncard ≤ finiteCrossingCount D := by
  calc
    C.chordCrossings.ncard ≤ (Paper170.crossingPoints D.toContinuousDrawing).ncard :=
      Set.ncard_le_ncard_of_injOn C.chordCrossingOrigin C.chordCrossingOrigin_mapsTo
        C.chordCrossingOrigin_injOn D.crossings_finite
    _ = finiteCrossingCount D := Set.ncard_eq_toFinset_card _ D.crossings_finite

end Paper170Geometry.DrawingPassages

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DiskChords
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior polygonal replacement, ordered passages, and injective middle paths. -/

section

/-! Constructed polygonal exterior paths, packaged with their actual geometric properties. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : FiniteIntersectionDrawing graph}

theorem nonempty_polygonalExterior [Fintype Vertex] [Fintype Edge] (C : DrawingPassages D) : Nonempty (PolygonalExterior C) := by
  classical
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨{
    chain := fun i => (P i).widen (Set.subset_univ _)
    injective := hP
    outside := hout
    disjoint := hdisjoint }⟩

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Polygonalization
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Admissible polygonal replacement and retention of crossing counts. -/

section

/-! All admissibility conditions and spatial crossing-count nonincrease for the assembled drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_crossingCount_le (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ finiteCrossingCount D := by
  have h := Set.ncard_le_ncard (E.assembled_crossings_subset v hvinj hv hdet) C.chordCrossings_finite
  have hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet)=
      (Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    rfl
  rw [hcount]
  exact h.trans C.chordCrossings_ncard_le

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Appendix A's actual polygonal normalization, with full admissibility and point-count control. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middlePath_hasFiniteAffineCover (E : PolygonalExterior C) (e : Edge) :
    HasFiniteAffineCover (E.middlePath e) :=
  alternatingPath_hasFiniteAffineCover _ _ _ _ (fun i => (E.chain (C.orderedArc e i)).hasFiniteAffineCover)
    (fun _ => hasFiniteAffineCover_segment _ _) _

theorem assembledEdge_hasFiniteAffineCover (E : PolygonalExterior C)
    (v : Vertex → Plane) (e : Edge) :
    HasFiniteAffineCover (E.assembledEdge v e) := by
  apply HasFiniteAffineCover.trans
  · apply HasFiniteAffineCover.trans (hasFiniteAffineCover_segment _ _)
    exact E.middlePath_hasFiniteAffineCover e
  · simp only [endSpoke,Path.segment_symm]
    exact hasFiniteAffineCover_segment _ _

end PolygonalExterior

/-- Finite contacts and no triples suffice to construct genuinely proper crossings. -/
theorem finite_intersection_normalization [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ D' : Paper170.AdmissibleDrawing graph,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ Paper170.crossingCount D' ≤ finiteCrossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩

end Paper170Geometry

end
end

section

/-! At equal total count, reassembly retains every original crossing and its incident pair. -/
noncomputable section
open Set
namespace Paper170Geometry
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace DrawingPassages
variable {D : FiniteIntersectionDrawing graph}

theorem chordCrossingOrigin_eq_innerMark (C : DrawingPassages D) {y : Plane}
    (hy : y ∈ C.chordCrossings) (p : C.InnerIndex) (hp : y ∈ Set.range (C.crossingChord p)) :
    C.chordCrossingOrigin y = (C.innerMark p).val := by
  unfold chordCrossingOrigin
  rw [dite_eq_left hy]
  obtain ⟨r,s,hrs,hr,hs,hyr,hys⟩ := (C.chord_crossing_original_mark hy).choose_spec.2
  exact congrArg Subtype.val ((C.chord_meeting_marks_eq p r hp hyr).trans hr).symm

end DrawingPassages
namespace PolygonalExterior
variable {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_origin_mem_pair (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (y : Plane)
    (he : y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hf : y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) :
    C.chordCrossingOrigin y ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
      C.chordCrossingOrigin y ∈ Paper170.edgeInterior D.toContinuousDrawing f := by
  have hy := E.assembled_crossings_subset v hvinj hv hdet ⟨e,f,hef,he,hf⟩
  obtain ⟨s,hs,hys⟩ := he
  obtain ⟨t,ht,hyt⟩ := hf
  obtain ⟨p,q,hp,hq,hyp,hyq⟩ := E.assembled_meeting_chords v hv hdet e f hef y
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (hys.trans heq))
    ⟨s,hys⟩ ⟨t,hyt⟩
  constructor
  · rw [C.chordCrossingOrigin_eq_innerMark hy p hyp, ← hp]
    exact ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  · rw [C.chordCrossingOrigin_eq_innerMark hy q hyq, ← hq]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩

theorem assembled_origin_surj_of_count_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) = finiteCrossingCount D) :
    Set.SurjOn C.chordCrossingOrigin (Paper170.crossingPoints (E.assembledDrawing v hvinj hv))
      (Paper170.crossingPoints D.toContinuousDrawing) := by
  have hsub := E.assembled_crossings_subset v hvinj hv hdet
  have hmap := C.chordCrossingOrigin_mapsTo.mono_left hsub
  have hinj := C.chordCrossingOrigin_injOn.mono hsub
  have hsize : (Paper170.crossingPoints D.toContinuousDrawing).ncard ≤
      (C.chordCrossingOrigin '' Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [hinj.ncard_image, ← finiteCrossingCount_eq_ncard]
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    exact hcount.ge
  have heq := Set.eq_of_subset_of_ncard_le hmap.image_subset hsize D.crossings_finite
  intro x hx
  rw [← heq] at hx
  exact hx

theorem assembled_pair_retained_of_count_eq
    {D₀ : Paper170.AdmissibleDrawing graph} {C₀ : DrawingPassages D₀.toFiniteIntersectionDrawing}
    (E : PolygonalExterior C₀) (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D₀.vertex j) < C₀.radius^2)
    (hdet : ∀ j (p q : C₀.PortsAt (C₀.vertexMark j)), p ≠ q →
      det2 (C₀.portPoint p.val-v j) (C₀.portPoint q.val-v j) ≠ 0)
    (hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
      Paper170.crossingCount D₀)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (hxe : x ∈ Paper170.edgeInterior D₀.toContinuousDrawing e)
    (hxf : x ∈ Paper170.edgeInterior D₀.toContinuousDrawing f) :
    ∃ y, y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e ∧
      y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f := by
  obtain ⟨y,hy,hxy⟩ := E.assembled_origin_surj_of_count_eq v hvinj hv hdet hcount
    (show x ∈ Paper170.crossingPoints D₀.toContinuousDrawing from ⟨e,f,hef,hxe,hxf⟩)
  obtain ⟨a,b,hab,hya,hyb⟩ := hy
  have hold := E.assembled_origin_mem_pair v hvinj hv hdet a b hab y hya hyb
  rw [hxy] at hold
  have ha := (crossing_incident_iff D₀ x e f hef hxe hxf a).mp hold.1
  have hb := (crossing_incident_iff D₀ x e f hef hxe hxf b).mp hold.2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · exact ⟨y,hya,hyb⟩
  · exact ⟨y,hyb,hya⟩
  · exact False.elim (hab rfl)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Subdivide actual polygonal drawings at all marks and any extra finite set of spatial points. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_drawing_subdivision_at [Fintype Vertex] (D : Paper170.AdmissibleDrawing graph)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) (S : Set Plane) (hS : S.Finite) :
    ∃ P : ∀ e, PolygonalParametrization (D.edge e),
      (∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) ∧
      (∀ e t, D.edge e t ∈ S → t ∈ Set.range (P e).knot) := by
  classical
  have hfinite (e : Edge) : ((D.edge e) ⁻¹' (drawingMarks D.toFiniteIntersectionDrawing ∪ S)).Finite :=
    ((drawingMarks_finite D.toFiniteIntersectionDrawing).union hS).preimage (D.edge_injective e).injOn
  have hex (e : Edge) := (hpoly e).refine (hfinite e).toFinset
  choose P hP using hex
  refine ⟨P,?_,?_⟩
  · intro e t ht
    exact hP e (by simpa using Or.inl ht)
  · intro e t ht
    exact hP e (by simpa using Or.inr ht)

namespace PolygonalExterior
variable {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_assembled_port_subdivision [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    ∃ P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e),
      (∀ e t, E.assembledEdge v e t ∈ drawingMarks (E.assembledAdmissible v hvinj hv hdet).toFiniteIntersectionDrawing →
        t ∈ Set.range (P e).knot) ∧
      (∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot) :=
  exists_drawing_subdivision_at (E.assembledAdmissible v hvinj hv hdet)
    (E.assembledEdge_hasFiniteAffineCover v) (Set.range C.portPoint) (Set.finite_range _)

end PolygonalExterior
end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OrderedPathParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem OrderedPathPart.refl {a b : Plane} (γ : Path a b) : OrderedPathPart γ γ :=
  ⟨id,strictMono_id,fun _ => rfl⟩

theorem OrderedPathPart.trans {a b c d e f : Plane} {γ : Path a b} {δ : Path c d} {η : Path e f}
    (hγ : OrderedPathPart γ δ) (hδ : OrderedPathPart δ η) : OrderedPathPart γ η := by
  obtain ⟨u,hu,he⟩ := hγ
  obtain ⟨v,hv,hf⟩ := hδ
  exact ⟨u ∘ v,hu.comp hv,fun t => (he (v t)).trans (hf t)⟩

theorem OrderedPathPart.left {a b c d e : Plane} {γ : Path a b} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path b c) : OrderedPathPart (γ.trans η) δ :=
  (show OrderedPathPart (γ.trans η) γ from
    ⟨intervalLeft,intervalLeft_strictMono,path_trans_intervalLeft γ η⟩).trans h

theorem OrderedPathPart.right {a b c d e : Plane} {γ : Path b c} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path a b) : OrderedPathPart (η.trans γ) δ :=
  (show OrderedPathPart (η.trans γ) γ from
    ⟨intervalRight,intervalRight_strictMono,path_trans_intervalRight η γ⟩).trans h

theorem OrderedPathPart.congr_right {a b c d e f : Plane} {γ : Path a b}
    {δ : Path c d} {η : Path e f} (h : OrderedPathPart γ δ) (he : ∀ t, δ t=η t) :
    OrderedPathPart γ η := by
  obtain ⟨u,hu,hh⟩ := h
  exact ⟨u,hu,fun t => (hh t).trans (he t)⟩

theorem OrderedPathPart.endpoints_ordered {a b c d : Plane} {γ : Path a b} {δ : Path c d}
    (h : OrderedPathPart γ δ) :
    ∃ u v : unitInterval, u < v ∧ γ u=c ∧ γ v=d := by
  obtain ⟨f,hf,he⟩ := h
  exact ⟨f 0,f 1,hf zero_lt_one,(he 0).trans δ.source,(he 1).trans δ.target⟩

theorem alternatingPath_contains_bridge (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) :
    (n : ℕ) → ∀ i, i < n → OrderedPathPart (alternatingPath a b p q n) (q i)
  | 0, i, hi => by omega
  | n+1, i, hi => by
    by_cases he : i=n
    · subst i
      exact ((OrderedPathPart.refl (q n)).right _).left _
    · exact ((alternatingPath_contains_bridge a b p q n i (by omega)).left (q n)).left (p (n+1))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exterior_segment_chord_meeting (G : SimpleGraph Plane) (U : Set Plane) (a b x y z : Plane)
    (hxy : G.Adj x y) (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : openSegmentTrace a b ⊆ U)
    (ha : a ∈ segment ℝ x y → a=x ∨ a=y) (hb : b ∈ segment ℝ x y → b=x ∨ b=y)
    (hz : z ∈ segment ℝ x y) (hchord : z ∈ segment ℝ a b) :
    (z=x ∨ z=y) ∧ (z=a ∨ z=b) := by
  rcases segment_endpoint_or_open a b z hchord with rfl | rfl | hz'
  · exact ⟨ha hz,Or.inl rfl⟩
  · exact ⟨hb hz,Or.inr rfl⟩
  · exact False.elim (Set.disjoint_left.mp (hout x y hxy) hz (hin hz'))

theorem segmentAugmentedGraph_embedding {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (hemb : StraightEdgeEmbedding G id) (U : Set Plane)
    (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : ∀ i, openSegmentTrace (a i) (b i) ⊆ U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (segment ℝ (a i) (b i)) (segment ℝ (a j) (b j)))
    (hend : ∀ i x y, G.Adj x y →
      (a i ∈ segment ℝ x y → a i=x ∨ a i=y) ∧
      (b i ∈ segment ℝ x y → b i=x ∨ b i=y)) :
    StraightEdgeEmbedding (segmentAugmentedGraph G a b hne) id := by
  refine ⟨Function.injective_id,?_⟩
  intro x y z w hxy hzw r hrx hrz
  rcases hxy with hxy | ⟨i,hi⟩ <;> rcases hzw with hzw | ⟨j,hj⟩
  · exact hemb.2 x y z w hxy hzw r hrx hrz
  · have hchord : r ∈ segment ℝ (a j) (b j) := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrz
      · simpa only [id_eq,segment_symm] using hrz
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a j) (b j) x y r hxy hout
      (hin j) (hend j x y hxy).1 (hend j x y hxy).2 hrx hchord
    have hrzw : r=z ∨ r=w := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hold hrzw))
  · have hchord : r ∈ segment ℝ (a i) (b i) := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrx
      · simpa only [id_eq,segment_symm] using hrx
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a i) (b i) z w r hzw hout
      (hin i) (hend i z w hzw).1 (hend i z w hzw).2 hrz hchord
    have hrxy : r=x ∨ r=y := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hrxy hold))
  · by_cases hij : i=j
    · subst j
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inl ⟨rfl,rfl⟩
    · apply False.elim
      apply Set.disjoint_left.mp (hdisj i j hij)
      · rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrx
        · simpa only [id_eq,segment_symm] using hrx
      · rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrz
        · simpa only [id_eq,segment_symm] using hrz

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CrossingCuts
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered crossing ports, surgery cut walks, path witnesses, and cut separation. -/

section

/-! The actual embedded surgery graph: exterior drawing tracks and two disjoint reconnection chords. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

theorem crossingSurgeryGraph_embedding (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e))
    (hmark : ∀ e t, D'.edge e t ∈ drawingMarks D'.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (hport : ∀ e t, D'.edge e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p q : C.InnerIndex) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id := by
  have hemb := drawingSubdivisionGraph_embedding P hmark
  have houtEmb : StraightEdgeEmbedding
      (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p)) id := by
    refine ⟨hemb.1,?_⟩
    intro a b c d hab hcd x hx hy
    exact hemb.2 a b c d hab.1 hcd.1 x hx hy
  apply segmentAugmentedGraph_embedding _ _ _ _ houtEmb (C.crossingDisk p)
  · intro x y hxy
    exact hxy.2
  · exact C.reconnection_open_in_disk p q hm
  · exact C.reconnection_chords_disjoint p q hcross
  · intro i x y hxy
    constructor
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.incomingPort q,ht.symm⟩
      · exact ⟨C.incomingPort p,ht.symm⟩
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.outgoingPort p,ht.symm⟩
      · exact ⟨C.outgoingPort q,ht.symm⟩

end Paper170Geometry

end
end

section

/-! The actual incoming and outgoing ports occur in the correct order on each edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem middlePath_contains_chord (E : PolygonalExterior C) (p : C.InnerIndex) :
    OrderedPathPart (E.middlePath p.1) (C.crossingChord p) := by
  rcases p with ⟨e,⟨i,hi⟩⟩
  have hj : i.val-1+1 < C.count e := by omega
  have hinner : C.orderedInner e (i.val-1) hj=⟨e,⟨i,hi⟩⟩ := by
    unfold DrawingPassages.orderedInner
    congr 1
    apply Subtype.ext
    apply Fin.ext
    change i.val-1+1=i.val
    omega
  have hpart : OrderedPathPart (E.middlePath e) (orderedBridge C e (i.val-1)) :=
    alternatingPath_contains_bridge _ _ _ _ (C.count e-1) (i.val-1) (by omega)
  apply hpart.congr_right
  intro t
  rw [orderedBridge_apply (C:=C) e (i.val-1) hj t,hinner]

theorem assembledEdge_contains_chord (E : PolygonalExterior C)
    (v : Vertex → Plane) (p : C.InnerIndex) :
    OrderedPathPart (E.assembledEdge v p.1) (C.crossingChord p) := by
  have h : OrderedPathPart (E.anchoredMiddle p.1) (C.crossingChord p) := E.middlePath_contains_chord p
  exact (h.right (startSpoke C v p.1)).left (endSpoke C v p.1)

theorem assembled_crossing_ports_ordered (E : PolygonalExterior C)
    (v : Vertex → Plane) (p : C.InnerIndex) :
    ∃ u w : unitInterval, u < w ∧
      E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p) ∧
      E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p) :=
  (E.assembledEdge_contains_chord v p).endpoints_ordered

theorem crossing_port_walk_indices (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) := by
  obtain ⟨u,w,huw,hu,hw⟩ := E.assembled_crossing_ports_ordered v p
  obtain ⟨i,hi⟩ := hport p.1 u ⟨C.incomingPort p,hu.symm⟩
  obtain ⟨j,hj⟩ := hport p.1 w ⟨C.outgoingPort p,hw.symm⟩
  have hij : i < j := by
    by_contra hn
    have hh := (P p.1).increasing.monotone (le_of_not_gt hn)
    rw [hi,hj] at hh
    exact huw.not_ge hh
  refine ⟨i,j,hij,?_,?_⟩
  · rw [drawingEdgeWalk_getVert P p.1 i.val (by omega)]
    have he := (P p.1).vertices_at i
    change (P p.1).vertices i.val=E.assembledEdge v p.1 ((P p.1).knot i) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hi).trans hu)
  · rw [drawingEdgeWalk_getVert P p.1 j.val (by omega)]
    have he := (P p.1).vertices_at j
    change (P p.1).vertices j.val=E.assembledEdge v p.1 ((P p.1).knot j) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hj).trans hw)

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Before the incoming port and after the outgoing port, the actual edge avoids the open crossing disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
namespace DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}

theorem crossingChord_parameter_interior (C : DrawingPassages D.toFiniteIntersectionDrawing) (p : C.InnerIndex)
    (t : unitInterval) (ht : C.crossingChord p t ∈ C.crossingDisk p) :
    t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 0-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.source,C.incomingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 1-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.target,C.outgoingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

end DrawingPassages
namespace PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_crossing_disk_parameter_between (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : E.assembledEdge v p.1 t ∈ C.crossingDisk p) : u < t ∧ t < w := by
  obtain ⟨f,hf,he⟩ := E.assembledEdge_contains_chord v p
  have h0 : f 0=u := E.assembledEdge_injective v hv p.1
    (((he 0).trans (C.crossingChord p).source).trans hu.symm)
  have h1 : f 1=w := E.assembledEdge_injective v hv p.1
    (((he 1).trans (C.crossingChord p).target).trans hw.symm)
  have hmem : E.assembledEdge v p.1 t ∈ Set.range (C.crossingChord p) :=
    (E.assembled_range_in_crossingDisk v hv p _ ht).mp ⟨t,rfl⟩
  obtain ⟨s,hs⟩ := hmem
  have hsint := C.crossingChord_parameter_interior p s (hs.symm ▸ ht)
  have hst : f s=t := E.assembledEdge_injective v hv p.1 ((he s).trans hs)
  exact ⟨by simpa only [h0,hst] using hf hsint.1,by simpa only [h1,hst] using hf hsint.2⟩

theorem assembled_crossing_port_clearance (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : t ≤ u ∨ w ≤ t) : E.assembledEdge v p.1 t ∉ C.crossingDisk p := by
  intro hmem
  have hbetween := E.assembled_crossing_disk_parameter_between v hv p u w hu hw t hmem
  rcases ht with ht | ht
  · exact hbetween.1.not_ge ht
  · exact hbetween.2.not_ge ht

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Actual ordered prefix and suffix cuts lie in the exterior segment graph. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem crossing_cut_traces_disjoint (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (p : C.InnerIndex) (i j : Fin ((P p.1).pieces+1))
    (hi : (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p))
    (hj : (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p)) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  have hki : (drawingEdgeWalk P p.1).getVert i.val=E.assembledEdge v p.1 ((P p.1).knot i) :=
    (drawingEdgeWalk_getVert P p.1 i.val (by omega)).trans ((P p.1).vertices_at i)
  have hkj : (drawingEdgeWalk P p.1).getVert j.val=E.assembledEdge v p.1 ((P p.1).knot j) :=
    (drawingEdgeWalk_getVert P p.1 j.val (by omega)).trans ((P p.1).vertices_at j)
  have hu := hki.symm.trans hi
  have hw := hkj.symm.trans hj
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P p.1 i hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inl ht.2) (he.symm ▸ hxin)
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P p.1 j hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inr ht.1) (he.symm ▸ hxin)

theorem exists_exterior_crossing_cuts (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  obtain ⟨i,j,hij,hi,hj⟩ := E.crossing_port_walk_indices v hvinj hv hdet P hport p
  exact ⟨i,j,hij,hi,hj,E.crossing_cut_traces_disjoint v hvinj hv hdet P p i j hi hj⟩

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Ordered actual cut data, whose existence is proved for the constructed normalization. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

theorem PolygonalExterior.nonempty_exteriorCrossingCut {C : DrawingPassages D.toFiniteIntersectionDrawing} (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (r : C.InnerIndex) : Nonempty (ExteriorCrossingCut C P r) := by
  obtain ⟨i,j,hij,hi,hj,hout,hout'⟩ := E.exists_exterior_crossing_cuts v hvinj hv hdet P hport r
  exact ⟨⟨i,j,hij,hi,hj,hout,hout'⟩⟩

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ArcRangeMinimality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem path_range_eq_of_subset {a b : Plane} (γ δ : Path a b)
    (hγ : Function.Injective γ) (hsub : Set.range δ ⊆ Set.range γ) :
    Set.range δ=Set.range γ := by
  apply Set.Subset.antisymm hsub
  rintro x ⟨t,rfl⟩
  have hc : IsPreconnected (γ ⁻¹' Set.range δ) :=
    (isPreconnected_range δ.continuous).preimage_of_isClosedMap hγ γ.continuous.isClosedMap hsub
  have h0 : (0 : unitInterval) ∈ γ ⁻¹' Set.range δ := ⟨0,δ.source.trans γ.source.symm⟩
  have h1 : (1 : unitInterval) ∈ γ ⁻¹' Set.range δ := ⟨1,δ.target.trans γ.target.symm⟩
  exact hc.Icc_subset h0 h1 t.property

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ReducedPolygonalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_reduced_polygonalChain {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (hpoly : HasFiniteAffineCover γ) :
    ∃ P : PolygonalChain (Set.range γ) a b,
      Set.range P.path=Set.range γ ∧ Function.Injective P.path ∧ 0 < P.pieces ∧
      (∀ i, i < P.pieces → P.vertices (i+1)-P.vertices i ≠ 0) ∧
      (∀ i, i+2 ≤ P.pieces →
        det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0) ∧
      (∀ Q : PolygonalChain (Set.range γ) a b, P.pieces ≤ Q.pieces) := by
  have hab : a ≠ b := by
    intro h
    exact zero_ne_one (hinj (γ.source.trans (h.trans γ.target.symm)))
  obtain ⟨Q⟩ := hpoly.nonempty_polygonalParametrization
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain ⟨Q.containedChain⟩
  exact ⟨P,path_range_eq_of_subset γ P.path hinj P.path_range_subset,
    P.minimum_path_injective hab hmin,P.pieces_pos_of_ne hab,
    P.minimum_piece_ne_zero hmin,P.minimum_bend_det_ne_zero hmin,hmin⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine polygonal subdivisions and chain parametrizations. -/

section

noncomputable section
open Set
open Zarankiewicz
open scoped Classical
namespace Paper170

lemma AffineCoverData.trans_endpoints {a b c : Plane} {γ : Path a b} {η : Path b c}
    (S : AffineCoverData γ) (T : AffineCoverData η) (B : Set Plane)
    (hS : ∀ ab ∈ S.intervals, γ ab.1 ∈ B ∧ γ ab.2 ∈ B)
    (hT : ∀ ab ∈ T.intervals, η ab.1 ∈ B ∧ η ab.2 ∈ B) :
    ∀ ab ∈ (S.trans T).intervals, (γ.trans η) ab.1 ∈ B ∧ (γ.trans η) ab.2 ∈ B := by
  intro ab hab
  rcases Finset.mem_union.mp hab with hab | hab
  · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
    simpa only [path_trans_intervalLeft] using hS cd hcd
  · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
    simpa only [path_trans_intervalRight] using hT cd hcd

lemma AffineCoverData.subdivision {a b : Plane} {γ : Path a b}
    (S : AffineCoverData γ) (B : Set Plane) (ha : a ∈ B) (hb : b ∈ B)
    (hS : ∀ ab ∈ S.intervals, γ ab.1 ∈ B ∧ γ ab.2 ∈ B) :
    ∃ P : PolygonalParametrization γ, ∀ i, γ (P.knot i) ∈ B := by
  let T : Finset unitInterval := insert 0 (insert 1 (S.intervals.image Prod.fst ∪ S.intervals.image Prod.snd))
  obtain ⟨k, _, t, ht, h0, h1, hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S.intervals) : ab.1 ∈ range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S.intervals) : ab.2 ∈ range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  let P : Zarankiewicz.PolygonalParametrization γ := {
    pieces := k
    knot := t
    increasing := ht
    first := h0
    last := h1
    affine := by
      intro i u
      let mid : unitInterval := ⟨1/2, by norm_num⟩
      let z := intervalSegment (t i.castSucc) (t i.succ) mid
      have hz : t i.castSucc < z ∧ z < t i.succ :=
        intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
          constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
      obtain ⟨ab,hab,ha,hb⟩ := S.cover z
      have hlo : ab.1 ≤ t i.castSucc := by
        by_contra hn
        obtain ⟨j,hj⟩ := hleft ab hab
        exact strictMono_no_between_successors t ht i j
          ⟨by rw [hj]; exact lt_of_not_ge hn, by rw [hj]; exact ha.trans_lt hz.2⟩
      have hhi : t i.succ ≤ ab.2 := by
        by_contra hn
        obtain ⟨j,hj⟩ := hright ab hab
        exact strictMono_no_between_successors t ht i j
          ⟨by rw [hj]; exact hz.1.trans_le hb, by rw [hj]; exact lt_of_not_ge hn⟩
      have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
      exact path_affine_restrict γ ab.1 ab.2 (S.ordered ab hab) (S.affine ab hab)
        (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u }
  refine ⟨ofZarankiewiczParametrization P, ?_⟩
  intro i
  have hi : t i ∈ T := by
    change t i ∈ (T : Set unitInterval)
    rw [←hR]
    exact ⟨i,rfl⟩
  simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with hi | hi | ⟨ab,hab,hi⟩ | ⟨ab,hab,hi⟩
  · change γ (t i) ∈ B
    simpa [hi] using ha
  · change γ (t i) ∈ B
    simpa [hi] using hb
  · change γ (t i) ∈ B
    simpa only [←hi] using (hS ab hab).1
  · change γ (t i) ∈ B
    simpa only [←hi] using (hS ab hab).2

end Paper170

end
end

section

noncomputable section
open Set
open Zarankiewicz
open scoped Classical
namespace Paper170

lemma polygonalArcPath_safe_cover (v : ℕ → Plane) (B : Set Plane) (n : ℕ)
    (hn : 0 < n) (hv : ∀ i, i ≤ n → v i ∈ B) :
    ∃ S : AffineCoverData (polygonalArcPath v n),
      ∀ ab ∈ S.intervals, polygonalArcPath v n ab.1 ∈ B ∧ polygonalArcPath v n ab.2 ∈ B := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        refine ⟨AffineCoverData.segment (v 0) (v 1), ?_⟩
        intro ab hab
        have he : ab = (0,1) := Finset.mem_singleton.mp hab
        subst ab
        exact ⟨by simpa only [polygonalArcPath, Path.source] using hv 0 (by omega),
          by simpa only [polygonalArcPath, Path.target] using hv 1 le_rfl⟩
      | succ n =>
        obtain ⟨S,hS⟩ := ih (n+1) (by omega) (by omega) (fun i hi => hv i (by omega))
        let T := AffineCoverData.segment (v (n+1)) (v (n+2))
        refine ⟨S.trans T, S.trans_endpoints T B hS ?_⟩
        intro ab hab
        have he : ab = (0,1) := Finset.mem_singleton.mp hab
        subst ab
        exact ⟨by simpa only [Path.source] using hv (n+1) (by omega),
          by simpa only [Path.target] using hv (n+2) le_rfl⟩

lemma chain_subdivision_avoiding {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hP : 0 < P.pieces) (B : Set Plane)
    (hv : ∀ i, i ≤ P.pieces → P.vertices i ∈ B) :
    ∃ Q : PolygonalParametrization P.path, ∀ i, P.path (Q.knot i) ∈ B := by
  obtain ⟨S,hS⟩ := polygonalArcPath_safe_cover P.vertices B P.pieces hP hv
  obtain ⟨Q,hQ⟩ := S.subdivision B (hv 0 (Nat.zero_le _)) (hv _ le_rfl) hS
  exact ⟨Q.cast P.first.symm P.last.symm, hQ⟩

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_SurgeryIntersections
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Surgery intersection containment, strict crossing reduction, and admissibility. -/

section

/-! The constructed surgery drawing satisfies exactly the proved weaker normalization input. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryFiniteDrawing_count_lt
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    finiteCrossingCount (E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq) <
      Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  rw [finiteCrossingCount_eq_ncard]
  have h := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).2
  exact h.trans_eq (Set.ncard_eq_toFinset_card _ (E.assembledAdmissible v hvinj hv hdet).crossings_finite)

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Strict adjacent-crossing improvement with actual admissibility restored by proved normalization. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_admissible_adjacent_surgery [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : Paper170.AdmissibleDrawing graph, (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      Paper170.crossingCount A < Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let B := E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq
  obtain ⟨A,hpoly,hcount⟩ := finite_intersection_normalization B
  exact ⟨A,hpoly,hcount.trans_lt
    (E.adjacentSurgeryFiniteDrawing_count_lt v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq)⟩

end Paper170Geometry.PolygonalExterior

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_LocalLineBends
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem segment_direction_of_local_line (a b d : Plane) (U : Set Plane)
    (hU : IsOpen U) (hb : b ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ b a → det2 d (z-b)=0) :
    det2 d (a-b)=0 := by
  have hc : Continuous (fun t : ℝ => segmentPoint b a t) := by dsimp [segmentPoint]; fun_prop
  have hh : ∀ᶠ t : ℝ in 𝓝 0, segmentPoint b a t ∈ U := by
    exact hc.continuousAt.eventually (by simpa using hU.mem_nhds hb)
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp hh
  let t : ℝ := min (r/2) (1/2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hm : segmentPoint b a t ∈ U := hs (by simpa [Real.dist_eq,abs_of_pos ht] using htr)
  have hseg : segmentPoint b a t ∈ segment ℝ b a := by
    rw [← Path.range_segment]
    exact ⟨⟨t,⟨ht.le,ht1⟩⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
  have he := hline _ hm hseg
  have heq : segmentPoint b a t-b=t • (a-b) := by
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  rw [heq,det2_smul_right] at he
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt ht)

theorem bend_det_zero_of_local_line (a b c d : Plane) (hd : d ≠ 0)
    (U : Set Plane) (hU : IsOpen U) (hb : b ∈ U)
    (hline : ∀ z ∈ U, z ∈ segment ℝ a b ∪ segment ℝ b c → det2 d (z-b)=0) :
    det2 (b-a) (c-b)=0 := by
  have ha := segment_direction_of_local_line a b d U hU hb (by
    intro z hz hs
    exact hline z hz (Or.inl (by simpa only [segment_symm ℝ b a] using hs)))
  have hc := segment_direction_of_local_line c b d U hU hb (fun z hz hs => hline z hz (Or.inr hs))
  have hba : b-a=-(a-b) := by abel
  rw [hba,vector_parallel_of_det_zero d (a-b) hd ha,
    vector_parallel_of_det_zero d (c-b) hd hc,det2_neg_left,
    det2_smul_left,det2_smul_right,det2_self]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ReducedCrossingCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem det2_of_common_openSegment (a b x z : Plane)
    (hx : x ∈ openSegmentTrace a b) (hz : z ∈ openSegmentTrace a b) :
    det2 (b-a) (z-x)=0 := by
  obtain ⟨t,ht,rfl⟩ := hx
  obtain ⟨u,hu,rfl⟩ := hz
  dsimp [det2,segmentPoint]
  ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Truncation
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex-disk truncation, retained crossings, reduced corners, and transverse segments. -/

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem LocallyStraightAt.exists_trace_line (D : Paper170.ContinuousDrawing graph)
    (e : Edge) (x : Plane) (hx : x ∈ Paper170.edgeInterior D e)
    (h : LocallyStraightAt D e x) :
    ∃ d : Plane, d ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0 := by
  obtain ⟨a,b,hab,hxab,U,hU,hxU,htrace⟩ := h.exists_line
  let V : Set Plane := Set.range D.vertex
  have hV : IsClosed V := (Set.finite_range D.vertex).isClosed
  have hxV : x ∉ V := by
    rintro ⟨j,hj⟩
    exact edgeInterior_not_vertex D e x hx j hj.symm
  refine ⟨b-a,sub_ne_zero.mpr (Ne.symm hab),U ∩ Vᶜ,hU.inter hV.isOpen_compl,⟨hxU,hxV⟩,?_⟩
  intro z hz hze
  have hzi : z ∈ Paper170.edgeInterior D e := edgeInterior_of_range_not_vertices D e z hze (by
    intro j hj
    exact hz.2 ⟨j,hj.symm⟩)
  exact det2_of_common_openSegment a b x z hxab ((htrace z hz.1).mp hzi)

theorem minimum_bend_not_locallyStraight (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) (hx : P.vertices (i+1) ∈ Paper170.edgeInterior D e) :
    ¬ LocallyStraightAt D e (P.vertices (i+1)) := by
  intro h
  obtain ⟨d,hd,U,hU,hxU,hh⟩ := LocallyStraightAt.exists_trace_line D e _ hx h
  apply P.minimum_bend_det_ne_zero hmin i hi
  apply bend_det_zero_of_local_line _ _ _ d hd U hU hxU
  intro z hz hseg
  apply hh z hz
  rcases hseg with hseg | hseg
  · exact P.inside i (by omega) hseg
  · exact P.inside (i+1) (by omega) hseg

theorem minimum_bend_not_crossing (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) : P.vertices (i+1) ∉ Paper170.crossingPoints D.toContinuousDrawing := by
  rintro ⟨f,g,hfg,hf,hg⟩
  have hx : P.vertices (i+1) ∈ Paper170.edgeInterior D.toContinuousDrawing e :=
    edgeInterior_of_range_not_vertices D.toContinuousDrawing e _ (P.vertex_mem (i+1) (by omega))
      (edgeInterior_not_vertex D.toContinuousDrawing f _ hf)
  apply minimum_bend_not_locallyStraight D.toContinuousDrawing e P hmin i hi hx
  by_cases hef : e=f
  · subst f
    exact (hstraight.at_crossing e g hfg _ hx hg).1
  · exact (hstraight.at_crossing e f hef _ hx hf).1

theorem minimum_vertices_not_crossing (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∉ Paper170.crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf ((graph.src e)) rfl
  by_cases hn : i=P.pieces
  · subst i
    rw [P.last]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf ((graph.dst e)) rfl
  have h := minimum_bend_not_crossing D hstraight e P hmin (i-1) (by omega)
  simpa only [show i-1+1=i by omega] using h

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Normalization
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reorientation invariance and normalization without adjacent crossings or crossing knots. -/

section

/-! Reversing chosen oriented representatives changes no spatial drawing or crossing count. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170
variable {V E : Type}

namespace AdmissibleDrawing
variable {G : Graph V E}

theorem reorient_crossingCount (D : AdmissibleDrawing G) (reverse : E → Bool) :
    crossingCount (D.reorient reverse) = crossingCount D := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, reorient, ContinuousDrawing.reorient_crossingPoints]

end AdmissibleDrawing
end Paper170

end
end

section

/-! Reorientation preserves the minimum property among ordinary drawings. -/
noncomputable section
namespace Paper170
variable {V E : Type}

theorem Graph.eq_of_endpoints {G H : Graph V E} (hs : G.src = H.src)
    (ht : G.dst = H.dst) : G = H := by
  cases G
  cases H
  cases hs
  cases ht
  rfl

theorem Graph.reorient_reorient (G : Graph V E) (reverse : E → Bool) :
    (G.reorient reverse).reorient reverse = G := by
  apply Graph.eq_of_endpoints
  · funext e
    by_cases h : reverse e = true <;> simp [Graph.reorient,h]
  · funext e
    by_cases h : reverse e = true <;> simp [Graph.reorient,h]

namespace AdmissibleDrawing
variable {G H : Graph V E}

theorem castGraph_crossingCount (h : G = H) (D : AdmissibleDrawing G) :
    crossingCount (D.castGraph h) = crossingCount D := by
  cases h
  rfl

theorem reorient_minimal (D : AdmissibleDrawing G) (reverse : E → Bool)
    (hmin : ∀ A : AdmissibleDrawing G, crossingCount D ≤ crossingCount A) :
    ∀ A : AdmissibleDrawing (G.reorient reverse),
      crossingCount (D.reorient reverse) ≤ crossingCount A := by
  intro A
  have h := hmin ((A.reorient reverse).castGraph (G.reorient_reorient reverse))
  simpa only [castGraph_crossingCount,reorient_crossingCount] using h

end AdmissibleDrawing
end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {G : Graph V E}

lemma reparametrized_count (D : AdmissibleDrawing G)
    (P : ∀ e, Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)))
    (hP : ∀ e, Function.Injective (P e).path)
    (htrace : ∀ e, range (P e).path = range (D.edge e)) :
    crossingCount (reparametrizedDrawing D P hP htrace) = crossingCount D := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset]
  change x ∈ crossingPoints (reparametrizedContinuous D.toContinuousDrawing P hP) ↔ _
  rw [reparametrized_crossings D.toContinuousDrawing P hP htrace]

lemma normalized_of_locally_straight [Fintype V] (D : AdmissibleDrawing G)
    (hpoly : ∀ e, Zarankiewicz.HasFiniteAffineCover (D.edge e))
    (hnoadj : Paper170Geometry.NoAdjacentCrossings D)
    (hstraight : Paper170Geometry.LocallyStraightCrossings D) :
    ∃ N : NormalizedDrawing G, crossingCount N.toAdmissibleDrawing = crossingCount D := by
  have hp (e : E) : ∃ P : Zarankiewicz.PolygonalChain (range (D.edge e))
      (D.vertex (G.src e)) (D.vertex (G.dst e)),
      range P.path = range (D.edge e) ∧ Function.Injective P.path ∧ 0 < P.pieces ∧
      ∀ Q : Zarankiewicz.PolygonalChain (range (D.edge e))
        (D.vertex (G.src e)) (D.vertex (G.dst e)), P.pieces ≤ Q.pieces := by
    obtain ⟨P, ht, hi, hn, _, _, hm⟩ :=
      Zarankiewicz.exists_reduced_polygonalChain (D.edge e) (D.edge_injective e) (hpoly e)
    exact ⟨P, ht, hi, hn, hm⟩
  choose P htrace hinj hpos hmin using hp
  have hq (e : E) : ∃ Q : PolygonalParametrization (P e).path,
      ∀ i, (P e).path (Q.knot i) ∉ crossingPoints D.toContinuousDrawing :=
    chain_subdivision_avoiding (P e) (hpos e) {x | x ∉ crossingPoints D.toContinuousDrawing}
      (Paper170Geometry.minimum_vertices_not_crossing D hstraight e (P e) (hmin e))
  choose Q hQ using hq
  let N : NormalizedDrawing G := {
    toAdmissibleDrawing := reparametrizedDrawing D P hinj htrace
    polygonal := Q
    no_adjacent := by
      intro e f hef hinc
      change Disjoint (edgeInterior (reparametrizedContinuous D.toContinuousDrawing P hinj) e)
        (edgeInterior (reparametrizedContinuous D.toContinuousDrawing P hinj) f)
      simp only [reparametrized_interior D.toContinuousDrawing P hinj htrace]
      exact Set.disjoint_iff_inter_eq_empty.mpr (hnoadj.eq_empty e f hef hinc)
    crossings_not_knots := by
      intro e i
      change (P e).path ((Q e).knot i) ∉
        crossingPoints (reparametrizedContinuous D.toContinuousDrawing P hinj)
      rw [reparametrized_crossings D.toContinuousDrawing P hinj htrace]
      exact hQ e i }
  exact ⟨N, reparametrized_count D P hinj htrace⟩

end Paper170

end
end

section

/-! The assembled ordinary drawing is genuinely straight near every crossing. -/
noncomputable section
namespace Paper170Geometry
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace PolygonalExterior
variable {D : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_locallyStraightCrossings (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    LocallyStraightCrossings (E.assembledAdmissible v hvinj hv hdet) := by
  constructor
  intro e f hef x hx hy
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hpx := (C.crossingChord_meeting_proper p q hpq x hxp hxq).1
  have hqx := (C.crossingChord_meeting_proper q p (Ne.symm hpq) x hxq hxp).1
  have hlocal (r : C.InnerIndex) (hr : x ∈ C.crossingDisk r)
      (hxr : x ∈ Set.range (C.crossingChord r)) :
      LocallyStraightAt (E.assembledDrawing v hvinj hv) r.1 x := by
    constructor
    refine ⟨C.portPoint (C.incomingPort r),C.portPoint (C.outgoingPort r),
      C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort r r),
      (C.crossingChord_openTrace_iff r x hr).mp hxr,C.crossingDisk r,C.crossingDisk_isOpen r,hr,?_⟩
    exact E.assembled_trace_in_crossingDisk v hvinj hv r
  change LocallyStraightAt (E.assembledDrawing v hvinj hv) e x ∧
    LocallyStraightAt (E.assembledDrawing v hvinj hv) f x
  exact ⟨by simpa only [hp] using hlocal p hpx hxp,by simpa only [hq] using hlocal q hqx hxq⟩

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Minimum ordinary drawings have no crossing between any pair sharing a vertex. -/
noncomputable section
namespace Paper170Geometry
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Paper170.Graph Vertex Edge}

theorem minimum_no_common_source_or_target (D : Paper170.AdmissibleDrawing graph)
    (hmin : ∀ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount D ≤ Paper170.crossingCount A)
    (e f : Edge) (hef : e ≠ f)
    (hadj : graph.src e = graph.src f ∨ graph.dst e = graph.dst f) :
    Paper170.edgeInterior D.toContinuousDrawing e ∩
      Paper170.edgeInterior D.toContinuousDrawing f = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxe,hxf⟩
  obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  have hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
      Paper170.crossingCount D :=
    le_antisymm (E.assembled_crossingCount_le v hvinj hv hdet) (hmin _)
  obtain ⟨y,hye,hyf⟩ := E.assembled_pair_retained_of_count_eq v hvinj hv hdet hcount e f hef x hxe hxf
  obtain ⟨p,q,hp,hq,hyp,hyq⟩ := E.assembled_meeting_chords v hv hdet e f hef y
    (edgeInterior_not_vertex (E.assembledDrawing v hvinj hv) e y hye)
    (edgeInterior_subset_range (E.assembledDrawing v hvinj hv) e hye)
    (edgeInterior_subset_range (E.assembledDrawing v hvinj hv) f hyf)
  have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
  have hadj' : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1 := by
    simpa only [hp,hq] using hadj
  obtain ⟨R,hRpoly,hRcount⟩ := E.exists_admissible_adjacent_surgery
    v hvinj hv hdet p q hpq hadj' y hyp hyq
  rw [hcount] at hRcount
  exact (not_lt_of_ge (hmin R)) hRcount

theorem minimum_no_adjacent (D : Paper170.AdmissibleDrawing graph)
    (hmin : ∀ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount D ≤ Paper170.crossingCount A) : NoAdjacentCrossings D := by
  constructor
  intro e f hef hadj
  obtain ⟨i,he,hf⟩ : ∃ i, (graph.src e = i ∨ graph.dst e = i) ∧
      (graph.src f = i ∨ graph.dst f = i) := by
    rcases hadj with h | h | h | h
    · exact ⟨graph.src e,Or.inl rfl,Or.inl h.symm⟩
    · exact ⟨graph.src e,Or.inl rfl,Or.inr h.symm⟩
    · exact ⟨graph.dst e,Or.inr rfl,Or.inl h.symm⟩
    · exact ⟨graph.dst e,Or.inr rfl,Or.inr h.symm⟩
  let reverse : Edge → Bool := fun a => decide (graph.dst a = i)
  have hsource (a : Edge) (ha : graph.src a = i ∨ graph.dst a = i) :
      (graph.reorient reverse).src a = i := by
    simp only [Paper170.Graph.reorient,reverse,decide_eq_true_eq]
    split
    · assumption
    · exact ha.resolve_right (by assumption)
  have h := minimum_no_common_source_or_target (D.reorient reverse)
    (D.reorient_minimal reverse hmin) e f hef
    (Or.inl ((hsource e he).trans (hsource f hf).symm))
  simpa only [Paper170.AdmissibleDrawing.reorient,
    Paper170.ContinuousDrawing.reorient_edgeInterior] using h

theorem exists_minimum_assembled (D : Paper170.AdmissibleDrawing graph) :
    ∃ (B : Paper170.AdmissibleDrawing graph) (C : DrawingPassages B.toFiniteIntersectionDrawing)
      (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
      (hv : ∀ j, squaredLength (v j-B.vertex j) < C.radius^2)
      (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
        det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0),
      NoAdjacentCrossings (E.assembledAdmissible v hvinj hv hdet) ∧
        Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
          Paper170.ordinaryCrossingNumber graph := by
  obtain ⟨B,hB⟩ := crossingCount_attainment D
  obtain ⟨C⟩ := nonempty_drawingPassages B.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  let A := E.assembledAdmissible v hvinj hv hdet
  have hcount : Paper170.crossingCount A = Paper170.ordinaryCrossingNumber graph := by
    apply le_antisymm
    · exact (E.assembled_crossingCount_le v hvinj hv hdet).trans_eq hB
    · exact ordinaryCrossingNumber_le_count A
  refine ⟨B,C,E,v,hvinj,hv,hdet,minimum_no_adjacent A ?_,hcount⟩
  intro R
  rw [hcount]
  exact ordinaryCrossingNumber_le_count R

theorem polygonal_no_adjacent_locally_straight (D : Paper170.AdmissibleDrawing graph) :
    ∃ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount A = Paper170.ordinaryCrossingNumber graph ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧ LocallyStraightCrossings A := by
  obtain ⟨B,C,E,v,hvinj,hv,hdet,hnorm,hcount⟩ := exists_minimum_assembled D
  exact ⟨E.assembledAdmissible v hvinj hv hdet,hcount,E.assembledEdge_hasFiniteAffineCover v,
    hnorm,E.assembled_locallyStraightCrossings v hvinj hv hdet⟩

end Paper170Geometry

end
end

section

noncomputable section
namespace Paper170
variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

theorem polygonal_no_adjacent_normalization_oai (D : AdmissibleDrawing G) :
    ∃ N : NormalizedDrawing G, crossingCount N.toAdmissibleDrawing ≤ crossingCount D := by
  obtain ⟨A, hcount, hpoly, hnoadj, hstraight⟩ :=
    Paper170Geometry.polygonal_no_adjacent_locally_straight D
  obtain ⟨N, hN⟩ := normalized_of_locally_straight A hpoly hnoadj hstraight
  exact ⟨N, (hN.trans hcount).le.trans (Paper170Geometry.ordinaryCrossingNumber_le_count D)⟩

end Paper170

end
end

end OAI
end

theorem solution : type_of% @OAI.Paper170.polygonal_no_adjacent_normalization_oai := @OAI.Paper170.polygonal_no_adjacent_normalization_oai
