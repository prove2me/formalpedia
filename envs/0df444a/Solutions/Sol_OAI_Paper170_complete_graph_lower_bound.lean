-- Prove2me | solution 1 for OAI.Paper170.complete_graph_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:42:48.890451+00:00
-- url     : https://prove2.me/submissions/e9b7abf2-1052-4e99-8eac-787c60886e6f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc002
import Theorems.Thm_OAI_Paper170_cycle_pairing_of_coordinates
import Theorems.Thm_OAI_Paper170_polygonal_no_adjacent_normalization

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

/-! Finite point incidence for actual drawings, retaining repeated pair crossings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
open scoped BigOperators Classical

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

/-- Every spatial crossing has exactly two incident edges; no bound is imposed
on the number of points common to that edge pair. -/
theorem crossing_two_edges (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) :
    ∃ e f : Edge, e ≠ f ∧
      ∀ g, x ∈ Paper170.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  obtain ⟨e,f,hef,he,hf⟩ := hx
  exact ⟨e,f,hef,crossing_incident_iff D x e f hef he hf⟩

variable [Fintype Edge]

/-- Each crossing point contributes two ordered edge pairs. -/
theorem crossing_ordered_incidence (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) :
    (∑ e : Edge, ∑ f : Edge,
      if e ≠ f ∧ x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
        x ∈ Paper170.edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
  classical
  obtain ⟨e,f,hef,hinc⟩ := crossing_two_edges D x hx
  simp_rw [hinc]
  have hp : ∀ a b : Edge,
      (a ≠ b ∧ (a = e ∨ a = f) ∧ (b = e ∨ b = f)) ↔
        ((a = e ∧ b = f) ∨ (a = f ∧ b = e)) := by
    intro a b
    constructor
    · rintro ⟨hab, rfl | rfl, rfl | rfl⟩ <;> tauto
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> tauto
  simp_rw [hp]
  have hi : ∀ a b : Edge,
      (if (a = e ∧ b = f) ∨ (a = f ∧ b = e) then (1 : ℕ) else 0) =
        (if a = e ∧ b = f then 1 else 0) + (if a = f ∧ b = e then 1 else 0) := by
    intro a b
    split_ifs <;> simp_all
  simp_rw [hi, Finset.sum_add_distrib]
  simp [ite_and]

/-- Sum over ordered edge pairs equals twice the number of spatial crossing points. -/
theorem sum_pairCrossings_card (D : Paper170.AdmissibleDrawing graph) :
    (∑ e : Edge, ∑ f : Edge, (pairCrossings D e f).card) =
      2 * Paper170.crossingCount D := by
  classical
  simp only [pairCrossings, Finset.card_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext f; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have he : ∀ x ∈ D.crossings_finite.toFinset,
      (∑ f : Edge, ∑ e : Edge,
        if e ≠ f ∧ x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
          x ∈ Paper170.edgeInterior D.toContinuousDrawing f then (1 : ℕ) else 0) = 2 := by
    intro x hx
    rw [Finset.sum_comm]
    exact crossing_ordered_incidence D x (by simpa using hx)
  simp_rw [Finset.sum_congr rfl he]
  simp [Paper170.crossingCount, Nat.mul_comm]

end Paper170Geometry

end
end

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

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentSymmetries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem nonzero_orientation_sign_neg (r : ℝ) (hr : r ≠ 0) :
    (if 0 < -r then (1 : ℝ) else -1) = -(if 0 < r then 1 else -1) := by
  by_cases hpos : 0 < r
  · have hn : ¬ 0 < -r := by linarith
    simp [hpos,hn]
  · have hn : 0 < -r := by rcases lt_or_gt_of_ne hr with hh | hh <;> linarith
    simp [hpos,hn]

theorem segmentCrossingSign_swap (a b c d : Plane) :
    segmentCrossingSign c d a b = -segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_swap]
  by_cases h : SegmentsCrossProperly a b c d
  · rw [ite_eq_left h, ite_eq_left h, det2_swap]
    exact nonzero_orientation_sign_neg _ h.1
  · simp [h]

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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalParametrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

namespace PolygonalParametrization
variable {a b : Plane} {γ : Path a b}

theorem segment_formula (P : PolygonalParametrization γ) (i : Fin P.pieces) (t : unitInterval) :
    γ (intervalSegment (P.knot i.castSucc) (P.knot i.succ) t)=
      segmentPoint (P.vertices i.val) (P.vertices (i.val+1)) t.val := by
  have he := P.affine i t
  rw [← P.vertices_at i.castSucc,← P.vertices_at i.succ] at he
  simpa using he

theorem direction_ne_zero (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : ℕ) (hi : i < P.pieces) : trackDirection P.vertices i ≠ 0 := by
  let j : Fin P.pieces := ⟨i,hi⟩
  intro hzero
  have he : P.vertices (i+1)=P.vertices i := sub_eq_zero.mp hzero
  have h₀ : P.vertices i=γ (P.knot j.castSucc) := by simpa [j] using P.vertices_at j.castSucc
  have h₁ : P.vertices (i+1)=γ (P.knot j.succ) := by simpa [j] using P.vertices_at j.succ
  rw [h₁,h₀] at he
  have hlt := P.increasing (show j.castSucc < j.succ by change i < i+1; omega)
  exact hlt.ne (hγ he).symm

end PolygonalParametrization
end Zarankiewicz

end

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
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Plane
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Planar segment geometry, affine parametrizations, and oriented arc directions. -/

section

/-! Generic planar ingredients reused through exact definitions of actual paths. -/
noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170

theorem det2_eq (a b : Plane) : det2 a b = Zarankiewicz.det2 a b := rfl

theorem segmentIntersection_eq_segmentCrossingSign (a b c d : Plane) :
    segmentIntersection a b c d = Zarankiewicz.segmentCrossingSign a b c d := by
  simp only [segmentIntersection, segmentPoint_eq, det2_eq,
    Zarankiewicz.segmentCrossingSign, Zarankiewicz.SegmentsCrossProperly]
  by_cases h : ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      Zarankiewicz.segmentPoint a b s = Zarankiewicz.segmentPoint c d t
  · simp only [h, ite_true, and_true]
    rcases lt_trichotomy (Zarankiewicz.det2 (b-a) (d-c)) 0 with hd | hd | hd
    · simp [hd, ne_of_lt hd, not_lt.mpr hd.le]
    · simp [hd]
    · simp [hd, ne_of_gt hd]
  · simp only [h, ite_false, and_false]

theorem segmentIntersection_swap (a b c d : Plane) :
    segmentIntersection c d a b = -segmentIntersection a b c d := by
  simpa only [segmentIntersection_eq_segmentCrossingSign] using
    Zarankiewicz.segmentCrossingSign_swap a b c d

end Paper170

end
end

section

/-! The frozen subdivision and the reused geometric subdivision describe the same path. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170

theorem PolygonalParametrization.segment_mem_interior {V E : Type} {G : Graph V E}
    (D : ContinuousDrawing G) (e : E) (P : PolygonalParametrization (D.edge e))
    (i : Fin P.pieces) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    segmentPoint (P.vertices i.val) (P.vertices (i.val+1)) s ∈ edgeInterior D e := by
  let t : unitInterval := ⟨s,hs.1.le,hs.2.le⟩
  let u := Zarankiewicz.intervalSegment (P.knot i.castSucc) (P.knot i.succ) t
  have hlt : P.knot i.castSucc < P.knot i.succ := P.increasing Fin.castSucc_lt_succ
  have hu := Zarankiewicz.intervalSegment_strict_between
    (P.knot i.castSucc) (P.knot i.succ) t hlt (show t ∈ Ioo (0 : unitInterval) 1 from hs)
  refine ⟨u,⟨lt_of_le_of_lt (P.knot i.castSucc).property.1 hu.1,
    lt_of_lt_of_le hu.2 (P.knot i.succ).property.2⟩,?_⟩
  exact (toZarankiewiczParametrization P).segment_formula i t

theorem PolygonalParametrization.vertices_first {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : P.vertices 0 = a :=
  (toZarankiewiczParametrization P).vertices_first

theorem PolygonalParametrization.vertices_last {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : P.vertices P.pieces = b :=
  (toZarankiewiczParametrization P).vertices_last

theorem PolygonalParametrization.direction_ne_zero {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : ℕ) (hi : i < P.pieces) : P.vertices (i+1) - P.vertices i ≠ 0 :=
  (toZarankiewiczParametrization P).direction_ne_zero hγ i hi

end Paper170

end
end

section

noncomputable section
open Set
namespace Paper170

/-- Two injective paths with the same endpoints and trace have the same orientation. -/
theorem path_reparametrization {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η) :
    ∃ f : unitInterval → unitInterval, Continuous f ∧ StrictMono f ∧
      f 0 = 0 ∧ f 1 = 1 ∧ ∀ t, γ (f t) = η t := by
  let e := (γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph
  let lift : unitInterval → Set.range γ := fun t =>
    ⟨η t, hrange.symm ▸ Set.mem_range_self t⟩
  let f : unitInterval → unitInterval := fun t => e.symm (lift t)
  have heval (t) : γ (f t) = η t := by
    have h := congrArg Subtype.val (e.apply_symm_apply (lift t))
    exact h
  have hzero : f 0 = 0 := hγ (by simpa using heval 0)
  have hone : f 1 = 1 := hγ (by simpa using heval 1)
  have hc : Continuous f := e.symm.continuous.comp
    (η.continuous.subtype_mk (fun t => hrange.symm ▸ Set.mem_range_self t))
  have hi : Function.Injective f := by
    intro s t hst
    apply hη
    rw [← heval s, ← heval t, hst]
  refine ⟨f, hc, ?_, hzero, hone, heval⟩
  apply hc.strictMono_of_inj_boundedOrder _ hi
  simpa only [show (⊥ : unitInterval) = 0 from rfl,
    show (⊤ : unitInterval) = 1 from rfl, hzero, hone] using
    (show (0 : unitInterval) ≤ 1 from zero_le_one)

end Paper170

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170

lemma intervalSegment_lt_iff {a b p q : unitInterval} (hab : a < b) :
    intervalSegment a b p < intervalSegment a b q ↔ p < q := by
  have hd : 0 < b.val - a.val := sub_pos.mpr hab
  change (1 - p.val) * a.val + p.val * b.val <
    (1 - q.val) * a.val + q.val * b.val ↔ p.val < q.val
  have he : ((1 - q.val) * a.val + q.val * b.val) -
      ((1 - p.val) * a.val + p.val * b.val) =
      (q.val - p.val) * (b.val - a.val) := by ring
  rw [← sub_pos, he, mul_pos_iff_of_pos_right hd, sub_pos]

lemma segmentPoint_sub_segmentPoint (A B : Plane) (p q : ℝ) :
    Paper170.segmentPoint A B q - Paper170.segmentPoint A B p = (q-p) • (B-A) := by
  ext <;> simp [Paper170.segmentPoint] <;> ring

/-- Oriented affine pieces of two parametrizations of the same simple arc have
positively proportional directions whenever they overlap to the right. -/
theorem path_segments_direction {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η)
    (a₀ a₁ b₀ b₁ : unitInterval) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (A B C D : Plane)
    (hγseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val)
    (hηseg : ∀t, η (intervalSegment b₀ b₁ t) = Paper170.segmentPoint C D t.val)
    (p q : unitInterval) (hp : p < 1) (hq : q < 1)
    (hpoint : Paper170.segmentPoint A B p.val = Paper170.segmentPoint C D q.val) :
    ∃ r : ℝ, 0 < r ∧ D-C = r • (B-A) := by
  obtain ⟨f, hc, hf, _, _, heval⟩ := path_reparametrization γ η hγ hη hrange
  let u := intervalSegment a₀ a₁ p
  let v := intervalSegment b₀ b₁ q
  have hmatch : f v = u := hγ (by rw [heval, hηseg, hγseg, hpoint])
  have hu : u < a₁ := by
    simpa [u, intervalSegment] using (intervalSegment_lt_iff ha).mpr hp
  have hv : v < b₁ := by
    simpa [v, intervalSegment] using (intervalSegment_lt_iff hb).mpr hq
  obtain ⟨c, huc, hcmin⟩ := exists_between (lt_min hu (hmatch ▸ hf hv))
  have hfc : f v < c := by rwa [hmatch]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo hv.le hc.continuousOn
    ⟨hfc, (lt_min_iff.mp hcmin).2⟩
  have hctop : c < a₁ := (lt_min_iff.mp hcmin).1
  obtain ⟨p', hp'⟩ := intervalSegment_surjective_interval a₀ a₁ ha c
    ⟨(intervalSegment_between a₀ a₁ p ha.le).1.trans huc.le, hctop.le⟩
  obtain ⟨q', hq'⟩ := intervalSegment_surjective_interval b₀ b₁ hb t
    ⟨(intervalSegment_between b₀ b₁ q hb.le).1.trans ht.1.le, ht.2.le⟩
  have hpp : p < p' := (intervalSegment_lt_iff ha).mp (by simpa [hp'] using huc)
  have hqq : q < q' := (intervalSegment_lt_iff hb).mp (by simpa [hq'] using ht.1)
  have hpoint' : Paper170.segmentPoint A B p'.val =
      Paper170.segmentPoint C D q'.val := by
    rw [← hγseg, ← hηseg, hp', hq', ← hft, heval]
  have heq : (p'.val-p.val) • (B-A) = (q'.val-q.val) • (D-C) := by
    rw [← segmentPoint_sub_segmentPoint, ← segmentPoint_sub_segmentPoint,
      hpoint, hpoint']
  have hα : 0 < p'.val-p.val := sub_pos.mpr hpp
  have hβ : 0 < q'.val-q.val := sub_pos.mpr hqq
  refine ⟨(q'.val-q.val)⁻¹ * (p'.val-p.val), mul_pos (inv_pos.mpr hβ) hα, ?_⟩
  calc
    D-C = (q'.val-q.val)⁻¹ • ((q'.val-q.val) • (D-C)) := by
      rw [smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
    _ = (q'.val-q.val)⁻¹ • ((p'.val-p.val) • (B-A)) := by rw [heq]
    _ = _ := by rw [smul_smul]

end Paper170

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170

lemma reverse_affine_piece {a b : Plane} (γ : Path a b)
    (a₀ a₁ : unitInterval) (A B : Plane)
    (hseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val) :
    ∀t, γ.symm (intervalSegment (unitInterval.symm a₁) (unitInterval.symm a₀) t) =
      Paper170.segmentPoint B A t.val := by
  intro t
  have hi : unitInterval.symm
      (intervalSegment (unitInterval.symm a₁) (unitInterval.symm a₀) t) =
      intervalSegment a₀ a₁ (unitInterval.symm t) := by
    apply Subtype.ext
    simp only [unitInterval.symm, intervalSegment]
    ring
  rw [Path.symm_apply, Function.comp_apply, hi, hseg]
  ext <;> simp [Paper170.segmentPoint, unitInterval.symm] <;> ring

theorem path_final_segments_direction {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η)
    (a₀ a₁ b₀ b₁ : unitInterval) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (A B C D : Plane)
    (hγseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val)
    (hηseg : ∀t, η (intervalSegment b₀ b₁ t) = Paper170.segmentPoint C D t.val)
    (hpoint : B = D) :
    ∃ r : ℝ, 0 < r ∧ C-D = r • (A-B) := by
  apply path_segments_direction γ.symm η.symm
    (hγ.comp unitInterval.symmHomeomorph.injective)
    (hη.comp unitInterval.symmHomeomorph.injective)
    (by simpa only [Path.symm_range] using hrange)
    (unitInterval.symm a₁) (unitInterval.symm a₀)
    (unitInterval.symm b₁) (unitInterval.symm b₀)
    (unitInterval.symm_lt_symm.mpr ha) (unitInterval.symm_lt_symm.mpr hb)
    B A D C (reverse_affine_piece γ a₀ a₁ A B hγseg)
    (reverse_affine_piece η b₀ b₁ C D hηseg) 0 0
    (by norm_num) (by norm_num)
  simpa [Paper170.segmentPoint] using hpoint

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem circle_denominator_pos (t : ℝ) : 0 < 1+t^2 := by nlinarith [sq_nonneg t]

end Zarankiewicz

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

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_NormalizedPolygonalDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalParametrization.pieces_pos {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : 0 < P.pieces := by
  by_contra hn
  have hp : P.pieces=0 := by omega
  have hi : (0 : Fin (P.pieces+1))=Fin.last P.pieces := by
    apply Fin.ext
    exact hp.symm
  have he := P.first.symm.trans ((congrArg P.knot hi).trans P.last)
  exact zero_ne_one he

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OrderedKnotCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem ordered_knots_cover {k : ℕ} (hk : 0 < k) (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (h0 : t 0=0) (h1 : t (Fin.last k)=1) (u : unitInterval) :
    ∃ i : Fin k, t i.castSucc ≤ u ∧ u ≤ t i.succ := by
  classical
  let S := Finset.univ.filter (fun i : Fin (k+1) => t i ≤ u)
  have hS : S.Nonempty := ⟨0,by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,h0]; exact u.property.1⟩
  let j := S.max' hS
  have hj : t j ≤ u := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  by_cases hjlast : j.val=k
  · let i : Fin k := ⟨k-1,by omega⟩
    have hjl : j=Fin.last k := Fin.ext hjlast
    have hi : i.succ=Fin.last k := by apply Fin.ext; change k-1+1=k; omega
    have hu : u=1 := le_antisymm u.property.2 (by simpa only [hjl,h1] using hj)
    refine ⟨i,?_,?_⟩
    · rw [hu, ← h1]
      exact (ht (Fin.castSucc_lt_last i)).le
    · rw [hi,h1,hu]
  · have hjk : j.val < k := by have hh := j.isLt; omega
    let i : Fin k := ⟨j.val,hjk⟩
    have hij : i.castSucc=j := Fin.ext rfl
    refine ⟨i,by rw [hij]; exact hj,?_⟩
    by_contra hu
    have hmem : i.succ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(lt_of_not_ge hu).le⟩
    have hh : i.succ ≤ j := Finset.le_max' S i.succ hmem
    change j.val+1 ≤ j.val at hh
    omega

theorem PolygonalParametrization.knot_cover {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (u : unitInterval) :
    ∃ i : Fin P.pieces, P.knot i.castSucc ≤ u ∧ u ≤ P.knot i.succ :=
  ordered_knots_cover P.pieces_pos P.knot P.increasing P.first P.last u

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_MinimumChainVertexPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalChain.minimum_vertex_piece_index {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i k : ℕ) (hi : i < P.pieces) (hk : k ≤ P.pieces)
    (hx : P.vertices k ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) : k=i ∨ k=i+1 := by
  have hlow : i ≤ k := by
    by_contra h
    have hki : k < i := by omega
    have hseg : segment ℝ (P.vertices k) (P.vertices (i+1)) ⊆ O :=
      ((convex_segment (𝕜 := ℝ) _ _).segment_subset hx (right_mem_segment ℝ _ _)).trans (P.inside i hi)
    have hh := P.minimum_shortcut_bound hmin k (i+1) (by omega) (by omega)
      (PolygonalChain.single O _ _ (P.vertex_mem k hk) hseg)
    change i+1-k ≤ 1 at hh
    omega
  have hhigh : k ≤ i+1 := by
    by_contra h
    have hik : i+1 < k := by omega
    have hseg : segment ℝ (P.vertices i) (P.vertices k) ⊆ O :=
      ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hx).trans (P.inside i hi)
    have hh := P.minimum_shortcut_bound hmin i k (by omega) hk
      (PolygonalChain.single O _ _ (P.vertex_mem i (by omega)) hseg)
    change k-i ≤ 1 at hh
    omega
  omega

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_VertexSpokeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_small_squared_radius {ι : Type*} [Fintype ι] (ρ : ℝ) (hρ : 0 < ρ)
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ i, r^2 < L i := by
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ (fun i => min 1 (L i))
    (fun i _ => lt_min (by norm_num) (hL i))
  refine ⟨min ρ δ,lt_min hρ hδ,min_le_left _ _,?_⟩
  intro i
  have hh := (min_le_right ρ δ).trans_lt (hbound i (Finset.mem_univ _))
  have h1 := hh.trans_le (min_le_left 1 (L i))
  have hlen := hh.trans_le (min_le_right 1 (L i))
  have hpos := lt_min hρ hδ
  have hm := mul_pos hpos (sub_pos.mpr h1)
  nlinarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RadialBoundaryPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_smul (v : Plane) (t : ℝ) : squaredLength (t • v)=t^2*squaredLength v := by
  dsimp [squaredLength]
  ring

theorem radialPort_sub (a b : Plane) (r : ℝ) :
    radialPort a b r-a=(r/Real.sqrt (squaredLength (b-a))) • (b-a) := by
  simp only [radialPort,add_sub_cancel_left]

theorem radialPort_on_circle (a b : Plane) (hab : a ≠ b) (r : ℝ) :
    squaredLength (radialPort a b r-a)=r^2 := by
  have hL := squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm)
  have hs : Real.sqrt (squaredLength (b-a)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  rw [radialPort_sub,squaredLength_smul,div_pow,Real.sq_sqrt hL.le]
  exact div_mul_cancel₀ _ (ne_of_gt hL)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleParameterChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem circlePoint_surjective_away_cut (z : Plane) (hz : z.1^2+z.2^2 = 1) (hcut : z.1 ≠ -1) :
    circlePoint (z.2/(1+z.1)) = z := by
  have hx : 0 < 1+z.1 := by
    have hy := sq_nonneg z.2
    have hnonneg : 0 ≤ 1+z.1 := by nlinarith
    rcases hnonneg.eq_or_lt with he | he
    · exfalso
      apply hcut
      linarith
    · exact he
  have hxn := ne_of_gt hx
  have hden : 1+(z.2/(1+z.1))^2 = 2/(1+z.1) := by
    field_simp
    nlinarith
  apply Prod.ext
  · change (1-(z.2/(1+z.1))^2)/(1+(z.2/(1+z.1))^2) = z.1
    rw [hden]
    field_simp
    nlinarith [congrArg (fun t : ℝ => (1+z.1)*t) hz]
  · change (2*(z.2/(1+z.1)))/(1+(z.2/(1+z.1))^2) = z.2
    rw [hden]
    field_simp

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Angles
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spoke angles, circle angles, scaling, and coordinate frames. -/

section

noncomputable section
open scoped Classical
namespace Paper170

lemma complexPoint_injective : Function.Injective complexPoint := by
  intro a b h
  exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)

lemma complexPoint_ne_zero {a : Plane} (ha : a ≠ 0) : complexPoint a ≠ 0 := by
  exact fun h => ha (complexPoint_injective h)

lemma spokeAngle_coe (cut : ℝ) (a : Plane) (ha : a ≠ 0) :
    (spokeAngle cut a : Real.Angle) = (Complex.arg (complexPoint a) : Real.Angle) - cut := by
  change (Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint a) : Real.Angle) = _
  rw [Complex.arg_mul_coe_angle (Complex.exp_ne_zero _) (complexPoint_ne_zero ha)]
  simp [Complex.arg_exp, sub_eq_add_neg, add_comm]

lemma finite_spoke_cut {ι : Type*} [Fintype ι] (a : ι → Plane) (ha : ∀ i, a i ≠ 0) :
    ∃ cut : ℝ, ∀ i, spokeAngle cut (a i) ≠ Real.pi := by
  have hreal (t : ℝ) : (Real.arctan t : Real.Angle).toReal = Real.arctan t := by
    apply Real.Angle.toReal_coe_eq_self_iff.mpr
    rcases Real.arctan_mem_Ioo t with ⟨hl, hu⟩
    constructor <;> linarith [Real.pi_pos]
  have hinj : Function.Injective (fun t : ℝ => (Real.arctan t : Real.Angle)) := by
    intro t u h
    apply Real.arctan_injective
    simpa only [hreal] using congrArg Real.Angle.toReal h
  let := Infinite.of_injective _ hinj
  let bad : ι → Real.Angle := fun i => (Complex.arg (complexPoint (a i)) : Real.Angle) - Real.pi
  obtain ⟨θ, hθ⟩ := (Set.finite_range bad).exists_notMem
  refine ⟨θ.toReal, ?_⟩
  intro i hi
  have h := spokeAngle_coe θ.toReal (a i) (ha i)
  rw [hi, Real.Angle.coe_toReal] at h
  apply hθ
  refine ⟨i, ?_⟩
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using (eq_sub_iff_add_eq.mp h).symm

lemma spokeAngle_eq_smul (cut : ℝ) (a b : Plane) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : spokeAngle cut a = spokeAngle cut b) : ∃ r : ℝ, 0 < r ∧ r • a = b := by
  let q := Complex.exp (-(cut : ℂ) * Complex.I)
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have ha' : q * complexPoint a ≠ 0 := mul_ne_zero hq (complexPoint_ne_zero ha)
  have hb' : q * complexPoint b ≠ 0 := mul_ne_zero hq (complexPoint_ne_zero hb)
  let r : ℝ := ‖q * complexPoint b‖ / ‖q * complexPoint a‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hb') (norm_pos_iff.mpr ha')
  refine ⟨r, hr, complexPoint_injective ?_⟩
  rw [complexPoint_smul]
  apply mul_left_cancel₀ hq
  have heq := (Complex.arg_eq_arg_iff ha' hb').mp h
  rw [← Complex.ofReal_div] at heq
  change ((r : ℂ) * (q * complexPoint a)) = q * complexPoint b at heq
  calc
    q * ((r : ℂ) * complexPoint a) = (r : ℂ) * (q * complexPoint a) := by ring
    _ = q * complexPoint b := heq

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma spokeAngle_smul (cut r : ℝ) (hr : 0 < r) (a : Plane) :
    spokeAngle cut (r • a) = spokeAngle cut a := by
  change Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint (r • a)) = _
  rw [complexPoint_smul, mul_left_comm, Complex.arg_real_mul _ hr]
  rfl

end Paper170

end
end

section

noncomputable section
open scoped Classical
namespace Paper170

lemma circlePoint_complex (t : ℝ) :
    complexPoint (Zarankiewicz.circlePoint t) =
      (Real.cos (2 * Real.arctan t) : ℂ) + (Real.sin (2 * Real.arctan t) : ℂ) * Complex.I := by
  have hden := Zarankiewicz.circle_denominator_pos t
  have hsqrt := Real.sq_sqrt hden.le
  have hsqrt0 : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hden)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    dsimp [complexPoint, Zarankiewicz.circlePoint]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    dsimp [complexPoint, Zarankiewicz.circlePoint]
    field_simp
    rw [hsqrt]

lemma circlePoint_arg (t : ℝ) :
    Complex.arg (complexPoint (Zarankiewicz.circlePoint t)) = 2 * Real.arctan t := by
  rw [circlePoint_complex]
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  apply Complex.arg_cos_add_sin_mul_I
  rcases Real.arctan_mem_Ioo t with ⟨hl, hu⟩
  constructor <;> linarith

lemma circlePoint_arg_lt (a b : ℝ) :
    Complex.arg (complexPoint (Zarankiewicz.circlePoint a)) <
      Complex.arg (complexPoint (Zarankiewicz.circlePoint b)) ↔ a < b := by
  rw [circlePoint_arg, circlePoint_arg, mul_lt_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)]
  exact Real.arctan_strictMono.lt_iff_lt

lemma angleRotation_complex (cut : ℝ) (a : Plane) :
    complexPoint (angleRotation cut a) =
      Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint a := by
  apply Complex.ext <;> simp [complexPoint, angleRotation, Zarankiewicz.similarityPoint, add_comm]

lemma angleRotation_unit (cut : ℝ) (a : Plane) (ha : squaredLength a = 1) :
    squaredLength (angleRotation cut a) = 1 := by
  have he : Complex.normSq (Complex.exp (-(cut : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.sq_norm]
    simp [Complex.norm_exp]
  have hform (p : Plane) : Complex.normSq (complexPoint p) = squaredLength p := by
    simp [Complex.normSq_apply, complexPoint, squaredLength, pow_two]
  have h : Complex.normSq (complexPoint a) = 1 := by rw [hform, ha]
  rw [← hform]
  rw [angleRotation_complex, map_mul, he, h, mul_one]

lemma angleRotation_parameter (cut : ℝ) (a : Plane) (ha : squaredLength a = 1)
    (hc : spokeAngle cut a ≠ Real.pi) :
    ∃ t, Zarankiewicz.circlePoint t = angleRotation cut a := by
  have hu := angleRotation_unit cut a ha
  have hx : (angleRotation cut a).1 ≠ -1 := by
    intro h
    have hy : (angleRotation cut a).2 = 0 := by
      dsimp [squaredLength] at hu
      rw [h] at hu
      nlinarith [sq_nonneg (angleRotation cut a).2]
    apply hc
    change Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint a) = _
    rw [← angleRotation_complex]
    exact Complex.arg_eq_pi_iff.mpr ⟨by simpa only [complexPoint, h] using (by norm_num : (-1:ℝ)<0), hy⟩
  exact ⟨(angleRotation cut a).2 / (1 + (angleRotation cut a).1),
    Zarankiewicz.circlePoint_surjective_away_cut _ hu hx⟩

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {G : Graph V E}

lemma outwardSpoke_ne_zero (N : NormalizedDrawing G) (v : V) (e : E) :
    outwardSpoke N v e ≠ 0 := by
  unfold outwardSpoke
  split_ifs
  · exact (N.polygonal e).direction_ne_zero (N.edge_injective e) 0 (N.polygonal e).positive
  · have h := (N.polygonal e).direction_ne_zero (N.edge_injective e)
      ((N.polygonal e).pieces - 1) (by have := (N.polygonal e).positive; omega)
    have hi : (N.polygonal e).pieces - 1 + 1 = (N.polygonal e).pieces := by
      have := (N.polygonal e).positive
      omega
    rw [hi] at h
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h))

lemma outwardSpoke_interior (N : NormalizedDrawing G) (v : V) (e : G.IncidentEdge v)
    (t : ℝ) (ht : 0 < t ∧ t < 1) :
    N.vertex v + t • outwardSpoke N v e.val ∈ edgeInterior N.toContinuousDrawing e.val := by
  by_cases hs : G.src e.val = v
  · have h := (N.polygonal e.val).segment_mem_interior N.toContinuousDrawing e.val
      ⟨0, (N.polygonal e.val).positive⟩ t ht
    have hp : (N.polygonal e.val).vertices 0 = N.vertex v := by
      simpa [hs] using (N.polygonal e.val).vertices_first
    convert h using 1
    rw [outwardSpoke, ite_eq_left hs, hp]
    simp only [segmentPoint]
    module
  · have hd : G.dst e.val = v := e.property.resolve_left hs
    have hi : (N.polygonal e.val).pieces - 1 + 1 = (N.polygonal e.val).pieces := by
      have := (N.polygonal e.val).positive
      omega
    have h := (N.polygonal e.val).segment_mem_interior N.toContinuousDrawing e.val
      ⟨(N.polygonal e.val).pieces - 1, by have := (N.polygonal e.val).positive; omega⟩
      (1-t) ⟨by linarith, by linarith⟩
    have hp : (N.polygonal e.val).vertices (N.polygonal e.val).pieces = N.vertex v := by
      simpa [hd] using (N.polygonal e.val).vertices_last
    simp only [hi, hp] at h
    convert h using 1
    rw [outwardSpoke, ite_eq_right hs, hp]
    simp only [segmentPoint]
    module

lemma spokeAngle_injective (N : NormalizedDrawing G) (v : V) (cut : ℝ) :
    Function.Injective (fun e : G.IncidentEdge v => spokeAngle cut (outwardSpoke N v e.val)) := by
  intro e f h
  by_contra hne
  have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hadj : G.src e.val = G.src f.val ∨ G.src e.val = G.dst f.val ∨
      G.dst e.val = G.src f.val ∨ G.dst e.val = G.dst f.val := by
    rcases e.property with he | he <;> rcases f.property with hf | hf <;> grind
  obtain ⟨r, hr, heq⟩ := spokeAngle_eq_smul cut (outwardSpoke N v e.val)
    (outwardSpoke N v f.val) (outwardSpoke_ne_zero N v e.val) (outwardSpoke_ne_zero N v f.val) h
  have hden : 0 < 1+r := by linarith
  have ht : 0 < 1/(1+r) ∧ 1/(1+r) < 1 := by
    constructor
    · exact div_pos zero_lt_one hden
    · exact (div_lt_one hden).mpr (by linarith)
  have hu : 0 < r/(1+r) ∧ r/(1+r) < 1 := by
    constructor
    · exact div_pos hr hden
    · exact (div_lt_one hden).mpr (by linarith)
  have hx := outwardSpoke_interior N v e (r/(1+r)) hu
  have hy := outwardSpoke_interior N v f (1/(1+r)) ht
  have hxy : N.vertex v + (1/(1+r)) • outwardSpoke N v f.val =
      N.vertex v + (r/(1+r)) • outwardSpoke N v e.val := by
    rw [← heq, smul_smul]
    congr 2
    ring
  rw [hxy] at hy
  exact Set.disjoint_left.mp (N.no_adjacent e.val f.val hef hadj) hx hy

theorem spoke_orders_exist [Fintype V] [Fintype E] (G : Graph V E)
    (N : NormalizedDrawing G) : Nonempty (SpokeOrders N) := by
  have hc (v : V) : ∃ cut : ℝ, ∀ e : G.IncidentEdge v,
      spokeAngle cut (outwardSpoke N v e.val) ≠ Real.pi :=
    finite_spoke_cut _ (fun e => outwardSpoke_ne_zero N v e.val)
  choose cut hcut using hc
  exact ⟨{
    cut := cut
    order := fun v => LinearOrder.lift' _ (spokeAngle_injective N v (cut v))
    cut_avoids := hcut
    compatible := fun _ _ _ => Iff.rfl
  }⟩

end Paper170

end
end

section

noncomputable section
open Zarankiewicz
namespace Paper170

theorem complexPoint_similarity (o u x : Plane) :
    complexPoint (similarityPoint o u x)=complexPoint o+complexPoint u*complexPoint x := by
  apply Complex.ext <;> simp [complexPoint,similarityPoint,add_comm]

theorem complexPoint_angleCoordinateFrame (cut radius : ℝ) :
    complexPoint (angleCoordinateFrame cut radius)=
      (radius:ℂ)*(Complex.exp (-(cut:ℂ)*Complex.I))⁻¹ := by
  rw [angleCoordinateFrame,complexPoint_smul]
  rfl

theorem angleCoordinateFrame_length (cut radius : ℝ) :
    squaredLength (angleCoordinateFrame cut radius)=radius^2 := by
  have hq : Complex.normSq (Complex.exp (-(cut:ℂ)*Complex.I))=1 := by
    rw [← Complex.sq_norm]
    simp [Complex.norm_exp]
  have hnorm (p : Plane) : squaredLength p=Complex.normSq (complexPoint p) := by
    simp [complexPoint,squaredLength,Complex.normSq_apply,pow_two]
  rw [hnorm,complexPoint_angleCoordinateFrame,map_mul,map_inv₀,hq,inv_one,mul_one]
  simp [Complex.normSq_apply,pow_two]

theorem angleCoordinateFrame_ne_zero (cut radius : ℝ) (hr : 0 < radius) :
    angleCoordinateFrame cut radius≠0 := by
  intro he
  have hl := angleCoordinateFrame_length cut radius
  rw [he] at hl
  have hz : squaredLength (0:Plane)=0 := by norm_num [squaredLength]
  rw [hz] at hl
  nlinarith

theorem angleCoordinateFrame_point (cut radius : ℝ) (hr : 0 < radius) (o x : Plane) :
    similarityPoint o (angleCoordinateFrame cut radius)
      (angleRotation cut (radius⁻¹ • (x-o)))=x := by
  apply complexPoint_injective
  rw [complexPoint_similarity,complexPoint_angleCoordinateFrame,angleRotation_complex,
    complexPoint_smul]
  have hsub : complexPoint (x-o)=complexPoint x-complexPoint o := rfl
  rw [hsub]
  have hr' : (radius:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hq : Complex.exp (-(cut:ℂ)*Complex.I)≠0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_inv]
  field_simp
  ring

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_LocalGeometry
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local straightness and transversality of normalized drawings. -/

section

/-! Actual local line and adjacency properties used in the cycle-intersection proof. -/
noncomputable section
open Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem normalized_noAdjacent (N : Paper170.NormalizedDrawing graph) :
    NoAdjacentCrossings N.toAdmissibleDrawing :=
  ⟨fun e f hef hadj => Set.disjoint_iff_inter_eq_empty.mp (N.no_adjacent e f hef hadj)⟩

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OpenSegmentEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem openSegmentTrace_ne_endpoints (a b : Plane) (hab : a ≠ b)
    (x : Plane) (hx : x ∈ openSegmentTrace a b) : x ≠ a ∧ x ≠ b := by
  obtain ⟨t,ht,he⟩ := hx
  let u : unitInterval := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
  have hu : (Path.segment a b) u=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
  constructor
  · intro h
    have hh := Path.segment_injective_of_ne hab (hu.trans (h.trans (Path.segment a b).source.symm))
    have ht0 : t=0 := congrArg Subtype.val hh
    exact ht.1.ne ht0.symm
  · intro h
    have hh := Path.segment_injective_of_ne hab (hu.trans (h.trans (Path.segment a b).target.symm))
    have ht1 : t=1 := congrArg Subtype.val hh
    exact ht.2.ne ht1

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_SpokePorts
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chain pieces near vertices, incident spoke ports, and short vertex radii. -/

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_piece_vertex (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (j : Vertex)
    (hx : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    (j=(graph.src e) ∧ i=0) ∨ (j=(graph.dst e) ∧ i+1=P.pieces) := by
  obtain ⟨t,ht⟩ := P.inside i hi hx
  rcases drawing_edge_vertex_parameter D e t j ht with ⟨_,he⟩ | ⟨_,he⟩
  · have hx0 : P.vertices 0 ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.first,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i 0 hi (by omega) hx0
    exact Or.inl ⟨he,by omega⟩
  · have hxN : P.vertices P.pieces ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := by
      simpa only [P.last,he] using hx
    have hh := P.minimum_vertex_piece_index hmin i P.pieces hi (by omega) hxN
    exact Or.inr ⟨he,by omega⟩

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_range_eq (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e)))) :
    Set.range P.path=Set.range (D.edge e) :=
  path_range_eq_of_subset (D.edge e) P.path (D.edge_injective e) P.path_range_subset

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_piece_open_subset_interior (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) :
    openSegmentTrace (P.vertices i) (P.vertices (i+1)) ⊆ Paper170.edgeInterior D e := by
  intro x hx
  have hseg := openSegmentTrace_subset_segment _ _ hx
  have hne := openSegmentTrace_ne_endpoints _ _
    (P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)) x hx
  apply edgeInterior_of_range_not_vertices D e x (P.inside i hi hseg)
  intro j hj
  have hvertex : D.vertex j ∈ segment ℝ (P.vertices i) (P.vertices (i+1)) := hj ▸ hseg
  rcases drawing_chain_piece_vertex D e P hmin i hi j hvertex with ⟨he,hii⟩ | ⟨he,hii⟩
  · apply hne.1
    calc
      x = D.vertex j := hj
      _ = D.vertex ((graph.src e)) := congrArg D.vertex he
      _ = P.vertices i := by simpa only [hii] using P.first.symm
  · apply hne.2
    calc
      x = D.vertex j := hj
      _ = D.vertex ((graph.dst e)) := congrArg D.vertex he
      _ = P.vertices (i+1) := by simpa only [hii] using P.last.symm

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_vertex_piece_clearance [Fintype Vertex] [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j k, j ≠ k → Disjoint (closedRoundDisk (D.vertex j) r) (closedRoundDisk (D.vertex k) r)) ∧
      (∀ j e (i : Fin (P e).pieces),
        ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
        Disjoint (closedRoundDisk (D.vertex j) r)
          (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1)))) := by
  classical
  let Bad := Σ j : Vertex, Σ e : Edge,
    {i : Fin (P e).pieces // ¬ ((j=(graph.src e) ∧ i.val=0) ∨
      (j=(graph.dst e) ∧ i.val+1=(P e).pieces))}
  let K : Bad → Set Plane := fun t =>
    segment ℝ ((P t.2.1).vertices t.2.2.val.val) ((P t.2.1).vertices (t.2.2.val.val+1))
  have hK (t : Bad) : IsCompact (K t) := by
    dsimp [K]
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment _ _).continuous
  have hnot (t : Bad) : D.vertex t.1 ∉ K t := by
    intro hx
    exact t.2.2.property (drawing_chain_piece_vertex D t.2.1 (P t.2.1)
      (hmin t.2.1) t.2.2.val.val t.2.2.val.isLt t.1 hx)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun t : Bad => D.vertex t.1) K hK hnot
  obtain ⟨σ,hσ,hdis⟩ := exists_disjoint_round_disks D.vertex D.vertex_injective
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro j k hjk
    exact (hdis j k hjk).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro j e i hi
    exact (hclear ⟨j,e,⟨i,hi⟩⟩).mono_left
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _))

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_chain_startPort_interior (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r) (hshort : r^2 < squaredLength (P.vertices 1-P.vertices 0)) :
    P.startPort r ∈ Paper170.edgeInterior D e := by
  exact drawing_chain_piece_open_subset_interior D e P hmin 0 (drawing_chain_pieces_pos D e P)
    (radialPort_mem_openSegment _ _ r hr hshort)

theorem drawing_chain_endPort_interior (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    P.endPort r ∈ Paper170.edgeInterior D e := by
  have hp := drawing_chain_pieces_pos D e P
  have hs : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
    rwa [squaredLength_sub_comm]
  have hx := openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hs)
  apply drawing_chain_piece_open_subset_interior D e P hmin (P.pieces-1) (by omega)
  simpa only [PolygonalChain.endPort,show P.pieces-1+1=P.pieces by omega] using hx

theorem drawing_chain_startPort_circle (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces) (r : ℝ) :
    squaredLength (P.startPort r-D.vertex ((graph.src e)))=r^2 := by
  have hp := drawing_chain_pieces_pos D e P
  have h := radialPort_on_circle (P.vertices 0) (P.vertices 1)
    (P.minimum_vertices_ne hmin 0 1 (by omega) hp) r
  simpa only [PolygonalChain.startPort,P.first] using h

theorem drawing_chain_endPort_circle (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces) (r : ℝ) :
    squaredLength (P.endPort r-D.vertex ((graph.dst e)))=r^2 := by
  have hp := drawing_chain_pieces_pos D e P
  have h := radialPort_on_circle (P.vertices P.pieces) (P.vertices (P.pieces-1))
    (Ne.symm (P.minimum_vertices_ne hmin (P.pieces-1) P.pieces (by omega) (by omega))) r
  simpa only [PolygonalChain.endPort,P.last] using h

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem incident_edges_adjacent (j : Vertex) (e f : IncidentEdges graph j) :
    graph.src e.val=graph.src f.val ∨ graph.src e.val=graph.dst f.val ∨
      graph.dst e.val=graph.src f.val ∨ graph.dst e.val=graph.dst f.val := by
  rcases e.property with he | he <;> rcases f.property with hf | hf
  · exact Or.inl (he.symm.trans hf)
  · exact Or.inr (Or.inl (he.symm.trans hf))
  · exact Or.inr (Or.inr (Or.inl (he.symm.trans hf)))
  · exact Or.inr (Or.inr (Or.inr (he.symm.trans hf)))

theorem drawingSpokePort_interior (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : Vertex) (e : IncidentEdges graph j) :
    drawingSpokePort D P r j e ∈ Paper170.edgeInterior D e.val := by
  unfold drawingSpokePort
  split_ifs
  · exact drawing_chain_startPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).1
  · exact drawing_chain_endPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).2

theorem drawingSpokePort_circle (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (j : Vertex) (e : IncidentEdges graph j) :
    squaredLength (drawingSpokePort D P r j e-D.vertex j)=r^2 := by
  unfold drawingSpokePort
  split_ifs with h
  · simpa only [h] using drawing_chain_startPort_circle D e.val (P e.val) (hmin e.val) r
  · have he := e.property.resolve_left h
    simpa only [he] using drawing_chain_endPort_circle D e.val (P e.val) (hmin e.val) r

theorem drawingSpokePort_injective (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : Vertex) : Function.Injective (drawingSpokePort D.toContinuousDrawing P r j) := by
  intro e f heq
  by_contra hne
  have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hp := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j e
  have hq := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j f
  rw [← heq] at hq
  have hh : drawingSpokePort D.toContinuousDrawing P r j e ∈
      Paper170.edgeInterior D.toContinuousDrawing e.val ∩ Paper170.edgeInterior D.toContinuousDrawing f.val := ⟨hp,hq⟩
  rw [hnorm.eq_empty e.val f.val hef (incident_edges_adjacent j e f)] at hh
  exact hh

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_vertex_spoke_bound [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  let L : Edge → ℝ := fun e =>
    min (squaredLength ((P e).vertices 1-(P e).vertices 0))
      (squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
  have hL (e : Edge) : 0 < L e := by
    have hp := drawing_chain_pieces_pos D e (P e)
    have hlast := (P e).minimum_piece_ne_zero (hmin e) ((P e).pieces-1) (by omega)
    rw [show (P e).pieces-1+1=(P e).pieces by omega] at hlast
    exact lt_min (squaredLength_pos _ ((P e).minimum_piece_ne_zero (hmin e) 0 hp))
      (squaredLength_pos _ hlast)
  obtain ⟨r,hr,hrρ,hbound⟩ := exists_small_squared_radius ρ hρ L hL
  exact ⟨r,hr,hrρ,fun e => ⟨(hbound e).trans_le (min_le_left _ _),
    (hbound e).trans_le (min_le_right _ _)⟩⟩

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_short_vertex_radius [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  obtain ⟨s,hs,hsρ,hbound⟩ := exists_vertex_spoke_bound D P hmin ρ hρ
  refine ⟨s/2,by positivity,by linarith,?_⟩
  intro e
  obtain ⟨hfirst,hlast⟩ := hbound e
  constructor <;> nlinarith

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalParametrizationCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalParametrization.hasFiniteAffineCover {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : HasFiniteAffineCover γ := by
  classical
  let f : Fin P.pieces → unitInterval × unitInterval := fun i => (P.knot i.castSucc,P.knot i.succ)
  refine ⟨Finset.univ.image f,?_,?_,?_⟩
  · intro ab hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hab
    exact P.increasing (by change i.val < i.val+1; omega)
  · intro t
    obtain ⟨i,hi,hj⟩ := P.knot_cover t
    exact ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi,hj⟩
  · intro ab hab t
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hab
    exact P.affine i t

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
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem nonempty_vertexTruncation [Fintype Vertex] [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) : Nonempty (VertexTruncation D) := by
  classical
  have hex (e : Edge) := exists_reduced_polygonalChain (D.edge e) (D.edge_injective e) (hpoly e)
  choose P htrace hinj hpos hdir hbend hmin using hex
  obtain ⟨ρ,hρ,hdis,hclear⟩ := exists_vertex_piece_clearance D P hmin
  obtain ⟨r,hr,hrρ,hshort⟩ := exists_short_vertex_radius D P hmin ρ hρ
  refine ⟨⟨P,hmin,r,hr,hshort,?_,?_⟩⟩
  · intro j k hjk
    exact (hdis j k hjk).mono (closedRoundDisk_mono _ hr.le hrρ) (closedRoundDisk_mono _ hr.le hrρ)
  · intro j e i hi
    exact (hclear j e i hi).mono_left (closedRoundDisk_mono _ hr.le hrρ)

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem normalized_vertexTruncation [Fintype Vertex] [Fintype Edge]
    (N : Paper170.NormalizedDrawing graph) : Nonempty (VertexTruncation N.toContinuousDrawing) :=
  nonempty_vertexTruncation N.toContinuousDrawing (fun e =>
    (Paper170.toZarankiewiczParametrization (N.polygonal e)).hasFiniteAffineCover)

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Tracks
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Truncated spoke coordinates, endpoint connections, and stable signed track intersections. -/

section

/-! The actual endpoint directions of truncated tracks, with their common fixed edge orientation. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokePort_circle (j : Vertex) (e : IncidentEdges graph j) :
    squaredLength (V.spokePort j e-D.vertex j)=V.radius^2 :=
  drawingSpokePort_circle D V.chain V.minimal V.radius j e

theorem spokePort_injective {A : Paper170.AdmissibleDrawing graph}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (j : Vertex) : Function.Injective (V.spokePort j) :=
  drawingSpokePort_injective A hnorm V.chain V.minimal V.radius V.radius_pos V.weak_short j

end Paper170Geometry.VertexTruncation

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Refinement
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matching refined crossing pieces and arc directions with truncated angle coordinates. -/

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

/-- Every actual polygonal-chain piece is traversed along an increasing affine parameter interval. -/
theorem polygonalArcPath_piece_interval (v : ℕ → Plane) : ∀ n i, i<n →
    ∃a b : unitInterval, a<b ∧ ∀t : unitInterval,
      polygonalArcPath v n (intervalSegment a b t)=segmentPoint (v i) (v (i+1)) t.val
  | 0, i, hi => by omega
  | 1, i, hi => by
    have he : i=0 := by omega
    subst i
    refine ⟨0,1,by norm_num,?_⟩
    intro t
    simp only [polygonalArcPath,intervalSegment_zero_one,Path.segment_apply,
      AffineMap.lineMap_apply_module,segmentPoint]
  | n+2, i, hi => by
    by_cases hprev : i<n+1
    · obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval v (n+1) i hprev
      refine ⟨intervalLeft a,intervalLeft b,intervalLeft_strictMono hab,?_⟩
      intro t
      rw [polygonalArcPath,intervalSegment_left,path_trans_intervalLeft]
      exact hseg t
    · have he : i=n+1 := by omega
      subst i
      refine ⟨intervalRight 0,intervalRight 1,intervalRight_strictMono (by norm_num),?_⟩
      intro t
      rw [polygonalArcPath,intervalSegment_right,path_trans_intervalRight,intervalSegment_zero_one]
      simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem minimum_first_direction (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) :
    ∃r : ℝ, 0 < r ∧ (V.chain e).vertices 1 - (V.chain e).vertices 0 =
      r • ((N.polygonal e).vertices 1 - (N.polygonal e).vertices 0) := by
  let k : Fin (N.polygonal e).pieces := ⟨0, (N.polygonal e).positive⟩
  obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval (V.chain e).vertices
    (V.chain e).pieces 0 (V.pieces_pos e)
  have hend : N.vertex (graph.src e) ≠ N.vertex (graph.dst e) :=
    fun he => graph.loopless e (N.vertex_injective he)
  apply Paper170.path_segments_direction (N.edge e) (V.chain e).path
    (N.edge_injective e) ((V.chain e).minimum_path_injective hend (V.minimal e))
    (drawing_chain_range_eq N.toContinuousDrawing e (V.chain e)).symm
    ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) a b
    ((N.polygonal e).increasing Fin.castSucc_lt_succ) hab
    ((N.polygonal e).vertices 0) ((N.polygonal e).vertices 1)
    ((V.chain e).vertices 0) ((V.chain e).vertices 1)
    ((Paper170.toZarankiewiczParametrization (N.polygonal e)).segment_formula k)
    hseg 0 0 (by norm_num) (by norm_num)
  simpa [Paper170.segmentPoint] using
    (N.polygonal e).vertices_first.trans (V.chain e).first.symm

theorem minimum_last_direction (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) :
    ∃r : ℝ, 0 < r ∧ (V.chain e).vertices ((V.chain e).pieces-1) -
        (V.chain e).vertices (V.chain e).pieces =
      r • ((N.polygonal e).vertices ((N.polygonal e).pieces-1) -
        (N.polygonal e).vertices (N.polygonal e).pieces) := by
  have hn : 0 < (N.polygonal e).pieces := (N.polygonal e).positive
  have hv : 0 < (V.chain e).pieces := V.pieces_pos e
  let k : Fin (N.polygonal e).pieces := ⟨(N.polygonal e).pieces-1, by omega⟩
  obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval (V.chain e).vertices
    (V.chain e).pieces ((V.chain e).pieces-1) (by omega)
  have hend : N.vertex (graph.src e) ≠ N.vertex (graph.dst e) :=
    fun he => graph.loopless e (N.vertex_injective he)
  have hnk : k.val+1 = (N.polygonal e).pieces := by dsimp [k]; omega
  have hvk : (V.chain e).pieces-1+1 = (V.chain e).pieces := by omega
  have hγseg := (Paper170.toZarankiewiczParametrization (N.polygonal e)).segment_formula k
  change ∀t, N.edge e (intervalSegment ((N.polygonal e).knot k.castSucc)
    ((N.polygonal e).knot k.succ) t) =
      Paper170.segmentPoint ((N.polygonal e).vertices k.val)
        ((N.polygonal e).vertices (k.val+1)) t.val at hγseg
  rw [hnk] at hγseg
  rw [hvk] at hseg
  exact Paper170.path_final_segments_direction (N.edge e) (V.chain e).path
    (N.edge_injective e) ((V.chain e).minimum_path_injective hend (V.minimal e))
    (drawing_chain_range_eq N.toContinuousDrawing e (V.chain e)).symm
    ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) a b
    ((N.polygonal e).increasing Fin.castSucc_lt_succ) hab
    ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (N.polygonal e).pieces)
    ((V.chain e).vertices ((V.chain e).pieces-1)) ((V.chain e).vertices (V.chain e).pieces)
    hγseg hseg ((N.polygonal e).vertices_last.trans (V.chain e).last.symm)

/-- The truncation port lies on the positive ray of the original outward spoke. -/
theorem spokePort_pos_mul_outward (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (j : Vertex) (e : IncidentEdges graph j) :
    ∃r : ℝ, 0 < r ∧ V.spokePort j e - N.vertex j = r • Paper170.outwardSpoke N j e.val := by
  by_cases hsrc : j = graph.src e.val
  · obtain ⟨r,hr,he⟩ := minimum_first_direction N V e.val
    have hp := radialPort_parameter_between ((V.chain e.val).vertices 0)
      ((V.chain e.val).vertices 1) V.radius V.radius_pos (V.weak_short e.val).1
    refine ⟨(V.radius / Real.sqrt (squaredLength
      ((V.chain e.val).vertices 1 - (V.chain e.val).vertices 0))) * r,
      mul_pos hp.1 hr, ?_⟩
    change drawingSpokePort N.toContinuousDrawing V.chain V.radius j e - N.vertex j = _
    rw [drawingSpokePort, ite_eq_left hsrc, PolygonalChain.startPort]
    have hcenter : N.vertex j = (V.chain e.val).vertices 0 := by
      exact (congrArg N.vertex hsrc).trans (V.chain e.val).first.symm
    rw [hcenter, radialPort_sub, he, smul_smul, Paper170.outwardSpoke, ite_eq_left hsrc.symm]
  · have hdst : j = graph.dst e.val := e.property.resolve_left hsrc
    obtain ⟨r,hr,he⟩ := minimum_last_direction N V e.val
    have hshort : V.radius^2 < squaredLength
        ((V.chain e.val).vertices ((V.chain e.val).pieces-1) -
          (V.chain e.val).vertices (V.chain e.val).pieces) := by
      rw [squaredLength_sub_comm]
      exact (V.weak_short e.val).2
    have hp := radialPort_parameter_between ((V.chain e.val).vertices (V.chain e.val).pieces)
      ((V.chain e.val).vertices ((V.chain e.val).pieces-1)) V.radius V.radius_pos hshort
    refine ⟨(V.radius / Real.sqrt (squaredLength
      ((V.chain e.val).vertices ((V.chain e.val).pieces-1) -
        (V.chain e.val).vertices (V.chain e.val).pieces))) * r, mul_pos hp.1 hr, ?_⟩
    change drawingSpokePort N.toContinuousDrawing V.chain V.radius j e - N.vertex j = _
    rw [drawingSpokePort, ite_eq_right hsrc, PolygonalChain.endPort]
    have hcenter : N.vertex j = (V.chain e.val).vertices (V.chain e.val).pieces := by
      exact (congrArg N.vertex hdst).trans (V.chain e.val).last.symm
    rw [hcenter, radialPort_sub, he, smul_smul, Paper170.outwardSpoke,
      ite_eq_right (Ne.symm hsrc)]

end Paper170Geometry

end
end

section

/-! Circle coordinates chosen with the very same cuts and local orders as the
original normalized drawing. -/
noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem exists_truncatedSpokeCoordinates_compatible (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (O : Paper170.SpokeOrders N) :
    ∃C : TruncatedSpokeCoordinates V, ∀j (e f : IncidentEdges graph j),
      orderSign (C.node j e) (C.node j f) = Paper170.spokeComparison O j e.val f.val := by
  classical
  let p (j : Vertex) (e : IncidentEdges graph j) : Plane :=
    V.radius⁻¹ • (V.spokePort j e-N.vertex j)
  have hinc (j : Vertex) (e : IncidentEdges graph j) :
      graph.src e.val=j ∨ graph.dst e.val=j := e.property.imp Eq.symm Eq.symm
  have hp (j : Vertex) (e : IncidentEdges graph j) : Paper170.squaredLength (p j e)=1 := by
    change squaredLength (V.radius⁻¹ • (V.spokePort j e-N.vertex j))=1
    rw [squaredLength_smul,V.spokePort_circle,inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 V.radius_pos.ne')]
  have hangle (j : Vertex) (e : IncidentEdges graph j) :
      Paper170.spokeAngle (O.cut j) (p j e)=
        Paper170.spokeAngle (O.cut j) (Paper170.outwardSpoke N j e.val) := by
    dsimp only [p]
    rw [Paper170.spokeAngle_smul _ _ (inv_pos.mpr V.radius_pos)]
    obtain ⟨r,hr,he⟩ := spokePort_pos_mul_outward N V j e
    rw [he,Paper170.spokeAngle_smul _ _ hr]
  have hex (j : Vertex) (e : IncidentEdges graph j) :
      ∃t : ℝ, circlePoint t=Paper170.angleRotation (O.cut j) (p j e) := by
    apply Paper170.angleRotation_parameter _ _ (hp j e)
    rw [hangle]
    exact O.cut_avoids j ⟨e.val,hinc j e⟩
  choose node hnode using hex
  have hpoint (j : Vertex) (e : IncidentEdges graph j) :
      similarityPoint (N.vertex j) (Paper170.angleCoordinateFrame (O.cut j) V.radius)
        (circlePoint (node j e))=V.spokePort j e := by
    rw [hnode]
    exact Paper170.angleCoordinateFrame_point _ _ V.radius_pos _ _
  let C : TruncatedSpokeCoordinates V := {
    frame := fun j => Paper170.angleCoordinateFrame (O.cut j) V.radius
    frame_ne_zero := fun j => Paper170.angleCoordinateFrame_ne_zero _ _ V.radius_pos
    frame_length := fun j => Paper170.angleCoordinateFrame_length (O.cut j) V.radius
    node := node
    node_injective := by
      intro j e f he
      apply V.spokePort_injective (normalized_noAdjacent N) j
      rw [← hpoint j e,← hpoint j f,he]
    point_eq := hpoint }
  refine ⟨C,?_⟩
  have harg (j : Vertex) (e : IncidentEdges graph j) :
      Paper170.spokeAngle (O.cut j) (Paper170.outwardSpoke N j e.val) =
        Complex.arg (Paper170.complexPoint (circlePoint (node j e))) := by
    rw [hnode,Paper170.angleRotation_complex]
    exact (hangle j e).symm
  have hlt (j : Vertex) (e f : IncidentEdges graph j) :
      @LT.lt _ (O.order j).toLT ⟨e.val,hinc j e⟩ ⟨f.val,hinc j f⟩ ↔ node j e < node j f := by
    rw [O.compatible,harg j e,harg j f,Paper170.circlePoint_arg_lt]
  intro j e f
  change orderSign (node j e) (node j f)=_
  unfold Paper170.spokeComparison
  rw [dite_eq_left (hinc j e),dite_eq_left (hinc j f)]
  simp only [orderSign,hlt]

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_NodeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivativeAtNode_eq_prod (node : ι → ℝ) (i : ι) :
    derivativeAtNode node i = ∏ j ∈ Finset.univ.erase i, (node i-node j) := by
  unfold derivativeAtNode nodePolynomial
  change (Lagrange.nodal Finset.univ node).derivative.eval (node i) = _
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

theorem derivativeAtNode_ne_zero (node : ι → ℝ) (hn : Function.Injective node) (i : ι) :
    derivativeAtNode node i ≠ 0 := by
  rw [derivativeAtNode_eq_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hij
  exact (Finset.mem_erase.mp hj).1 (hn hij).symm

theorem node_polynomial_moment (node : ι → ℝ) (hn : Function.Injective node)
    (P : ℝ[X]) (hP : P.degree < (Fintype.card ι - 1 : ℕ)) :
    (∑ i, P.eval (node i) / derivativeAtNode node i) = 0 := by
  by_cases hcard : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  have hp' : P.degree < (Finset.univ : Finset ι).card :=
    hP.trans_le (by exact_mod_cast Nat.sub_le (Fintype.card ι) 1)
  have he := Lagrange.coeff_eq_sum (s := Finset.univ) (v := node) hn.injOn hp'
  rw [Finset.card_univ, coeff_eq_zero_of_degree_lt hP] at he
  simpa only [Finset.card_univ, derivativeAtNode_eq_prod] using he.symm

theorem node_power_moment (node : ι → ℝ) (hn : Function.Injective node)
    (k : ℕ) (hk : k+1 < Fintype.card ι) :
    (∑ i, node i ^ k / derivativeAtNode node i) = 0 := by
  have hdeg : (X^k : ℝ[X]).degree < (Fintype.card ι - 1 : ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast (show k < Fintype.card ι-1 by omega)
  simpa only [eval_pow, eval_X] using node_polynomial_moment node hn (X^k) hdeg

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Tensor
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric crossing tensors, local orders, supports, and bilinear chain pairings. -/

section

/-! Algebraic consequences of the actual signed-intersection definition. -/
noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170
variable {V E : Type} {G : Graph V E}

theorem interiorIntersection_swap (N : NormalizedDrawing G) (e f : E) :
    interiorIntersection N f e = -interiorIntersection N e f := by
  by_cases h : e = f
  · subst f
    simp [interiorIntersection]
  · simp only [interiorIntersection, h, Ne.symm h, ite_false]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact segmentIntersection_swap _ _ _ _

theorem spokeComparison_swap {N : NormalizedDrawing G} (O : SpokeOrders N)
    (v : V) (e f : E) : spokeComparison O v f e = -spokeComparison O v e f := by
  by_cases he : G.src e = v ∨ G.dst e = v
  · by_cases hf : G.src f = v ∨ G.dst f = v
    · let : LinearOrder (G.IncidentEdge v) := O.order v
      rcases lt_trichotomy (⟨e,he⟩ : G.IncidentEdge v) ⟨f,hf⟩ with h | h | h
      · simp [spokeComparison, he, hf, h, not_lt.mpr h.le]
      · simp [spokeComparison, he, hf, h]
      · simp [spokeComparison, he, hf, h, not_lt.mpr h.le]
    · simp [spokeComparison, he, hf]
  · simp [spokeComparison, he]

variable [Fintype V]

theorem cycle_intersection_skew {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)
    (N : NormalizedDrawing G) (O : SpokeOrders N) (e f : E) :
    cycleIntersection O f e = -cycleIntersection O e f := by
  have hs : (∑ v, endpointSign G v f * endpointSign G v e * spokeComparison O v f e) =
      -(∑ v, endpointSign G v e * endpointSign G v f * spokeComparison O v e f) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [spokeComparison_swap]
    ring
  unfold cycleIntersection
  rw [interiorIntersection_swap, hs]
  ring

variable [Fintype E]

theorem edgePairing_neg_left (J : E → E → ℝ) (z z' : E → ℝ) :
    edgePairing J (-z) z' = -edgePairing J z z' := by
  simp [edgePairing, Finset.sum_neg_distrib]

theorem edgePairing_neg_right (J : E → E → ℝ) (z z' : E → ℝ) :
    edgePairing J z (-z') = -edgePairing J z z' := by
  simp [edgePairing, Finset.sum_neg_distrib]

theorem edgePairing_swap (J : E → E → ℝ) (hJ : ∀ e f, J f e = -J e f)
    (z z' : E → ℝ) : edgePairing J z' z = -edgePairing J z z' := by
  unfold edgePairing
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro f _
  rw [hJ]
  ring

theorem completeEdgeVector_self {n : ℕ} (i : Fin n) : completeEdgeVector i i = 0 := by
  funext e
  have h : ¬(e.val.1 = i ∧ e.val.2 = i) := by
    rintro ⟨h1,h2⟩
    exact (ne_of_lt e.property) (h1.trans h2.symm)
  simp [completeEdgeVector, h]

theorem completeEdgeVector_reverse {n : ℕ} (i p : Fin n) :
    completeEdgeVector p i = -completeEdgeVector i p := by
  funext e
  by_cases h : e.val.1 = i ∧ e.val.2 = p
  · have hn : ¬(e.val.1 = p ∧ e.val.2 = i) := by
      rintro ⟨h1,h2⟩
      exact (ne_of_lt e.property) (h.1.trans h2.symm)
    simp only [completeEdgeVector, Pi.neg_apply, ite_eq_left h, ite_eq_right hn]
  · by_cases hr : e.val.1 = p ∧ e.val.2 = i
    · simp only [completeEdgeVector, Pi.neg_apply, ite_eq_right h, ite_eq_left hr, neg_neg]
    · simp only [completeEdgeVector, Pi.neg_apply, ite_eq_right h, ite_eq_right hr, neg_zero]

theorem raw_cycle_symmetries {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (O : SpokeOrders N) :
    (∀ i k q, rawCycleIntersection O i i k q = 0) ∧
    (∀ i p k, rawCycleIntersection O i p k k = 0) ∧
    (∀ i p k q, rawCycleIntersection O p i k q = -rawCycleIntersection O i p k q) ∧
    (∀ i p k q, rawCycleIntersection O i p q k = -rawCycleIntersection O i p k q) ∧
    (∀ i p k q, rawCycleIntersection O k q i p = -rawCycleIntersection O i p k q) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i k q
    simp [rawCycleIntersection, completeEdgeVector_self, edgePairing]
  · intro i p k
    simp [rawCycleIntersection, completeEdgeVector_self, edgePairing]
  · intro i p k q
    unfold rawCycleIntersection
    rw [completeEdgeVector_reverse i p, edgePairing_neg_left]
  · intro i p k q
    unfold rawCycleIntersection
    rw [completeEdgeVector_reverse k q, edgePairing_neg_right]
  · intro i p k q
    exact edgePairing_swap _ (cycle_intersection_skew _ N O) _ _

end Paper170

end
end

section

/-! Every nonzero independent-edge coefficient is witnessed by an actual crossing point. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

theorem completeEdgeVector_endpoints {n : ℕ} (e : CompleteEdge n) :
    completeEdgeVector e.val.1 e.val.2 = Pi.single e 1 := by
  funext f
  by_cases h : f = e
  · subst f
    simp only [completeEdgeVector, and_self, ite_true, Pi.single_eq_same]
  · have hne : ¬(f.val.1 = e.val.1 ∧ f.val.2 = e.val.2) := by
      rintro ⟨h1,h2⟩
      exact h (Subtype.ext (Prod.ext h1 h2))
    have hrev : ¬(f.val.1 = e.val.2 ∧ f.val.2 = e.val.1) := by
      rintro ⟨h1,h2⟩
      have hf := f.property
      rw [h1,h2] at hf
      exact lt_asymm e.property hf
    simp only [completeEdgeVector, ite_eq_right hne, ite_eq_right hrev, Pi.single_eq_of_ne h]

theorem rawCycleIntersection_endpoints {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (e f : CompleteEdge n) :
    rawCycleIntersection O e.val.1 e.val.2 f.val.1 f.val.2 = cycleIntersection O e f := by
  rw [rawCycleIntersection, completeEdgeVector_endpoints, completeEdgeVector_endpoints]
  simp [edgePairing, Pi.single_apply, ite_mul, mul_ite]

theorem independent_cycleIntersection {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (e f : CompleteEdge n)
    (h11 : e.val.1 ≠ f.val.1) (h12 : e.val.1 ≠ f.val.2)
    (h21 : e.val.2 ≠ f.val.1) (h22 : e.val.2 ≠ f.val.2) :
    cycleIntersection O e f = interiorIntersection N e f := by
  have hs : (∑ v, endpointSign (completeGraph n) v e *
      endpointSign (completeGraph n) v f * spokeComparison O v e f) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases he1 : e.val.1 = v
    · have hf1 : f.val.1 ≠ v := fun h => h11 (he1.trans h.symm)
      have hf2 : f.val.2 ≠ v := fun h => h12 (he1.trans h.symm)
      simp [endpointSign, completeGraph, hf1, hf2]
    · by_cases he2 : e.val.2 = v
      · have hf1 : f.val.1 ≠ v := fun h => h21 (he2.trans h.symm)
        have hf2 : f.val.2 ≠ v := fun h => h22 (he2.trans h.symm)
        simp [endpointSign, completeGraph, hf1, hf2]
      · simp [endpointSign, completeGraph, he1, he2]
  simp [cycleIntersection, hs]

theorem interiorIntersection_ne_zero_crossing {V E : Type} {G : Graph V E}
    (N : NormalizedDrawing G) (e f : E) (h : interiorIntersection N e f ≠ 0) :
    (Paper170Geometry.pairCrossings N.toAdmissibleDrawing e f).Nonempty := by
  have hef : e ≠ f := by
    intro he
    subst f
    exact h (by simp [interiorIntersection])
  rw [interiorIntersection, ite_eq_right hef] at h
  obtain ⟨i,hi,hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j,hj,hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi'
  have hc : ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      segmentPoint ((N.polygonal e).vertices i) ((N.polygonal e).vertices (i+1)) s =
        segmentPoint ((N.polygonal f).vertices j) ((N.polygonal f).vertices (j+1)) t := by
    by_contra hn
    exact hij (by unfold segmentIntersection; rw [ite_eq_right hn])
  obtain ⟨s,hs,t,ht,hst⟩ := hc
  let x := segmentPoint ((N.polygonal e).vertices i) ((N.polygonal e).vertices (i+1)) s
  have he : x ∈ edgeInterior N.toContinuousDrawing e :=
    (N.polygonal e).segment_mem_interior N.toContinuousDrawing e ⟨i,Finset.mem_range.mp hi⟩ s hs
  have hf : x ∈ edgeInterior N.toContinuousDrawing f := by
    rw [show x = _ from hst]
    exact (N.polygonal f).segment_mem_interior N.toContinuousDrawing f
      ⟨j,Finset.mem_range.mp hj⟩ t ht
  refine ⟨x, Finset.mem_filter.mpr ⟨?_,hef,he,hf⟩⟩
  exact N.crossings_finite.mem_toFinset.mpr ⟨e,f,hef,he,hf⟩

theorem signed_support_bound {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (O : SpokeOrders N) :
    (supportedPairs (rawCycleIntersection O)).card ≤ 2 * crossingCount N.toAdmissibleDrawing := by
  let W := ↥(supportedPairs (rawCycleIntersection O))
  let e : W → CompleteEdge n := fun w => ⟨w.val.1,(Finset.mem_filter.mp w.property).2.1⟩
  let f : W → CompleteEdge n := fun w => ⟨w.val.2,(Finset.mem_filter.mp w.property).2.2.1⟩
  have hc (w : W) : (Paper170Geometry.pairCrossings N.toAdmissibleDrawing (e w) (f w)).Nonempty := by
    obtain ⟨_,_,_,h11,h12,h21,h22,hJ⟩ := Finset.mem_filter.mp w.property
    apply interiorIntersection_ne_zero_crossing
    have hr := rawCycleIntersection_endpoints O (e w) (f w)
    rw [independent_cycleIntersection O (e w) (f w) h11 h12 h21 h22] at hr
    exact fun hz => hJ (hr.trans hz)
  choose x hx using hc
  let φ : W → (Σ a : CompleteEdge n, Σ b : CompleteEdge n,
      ↥(Paper170Geometry.pairCrossings N.toAdmissibleDrawing a b)) :=
    fun w => ⟨e w,f w,⟨x w,hx w⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => (z.1.val,z.2.1.val)) hab
  have hcard := Fintype.card_le_of_injective φ hφ
  have hs := Paper170Geometry.sum_pairCrossings_card N.toAdmissibleDrawing
  simpa only [W, Fintype.card_coe, Fintype.card_sigma, hs] using hcard

end Paper170

end
end

section

/-! The local order in the tensor is the actual order of outward incident edges. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} {G : Graph V E}

theorem Graph.common_endpoint_unique (G : Graph V E) (e f : E) (hef : e ≠ f)
    (i v : V) (hei : G.src e = i ∨ G.dst e = i) (hfi : G.src f = i ∨ G.dst f = i)
    (hev : G.src e = v ∨ G.dst e = v) (hfv : G.src f = v ∨ G.dst f = v) : v = i := by
  by_contra hvi
  apply hef
  apply G.simple e f
  rcases hei with hei | hei <;> rcases hfi with hfi | hfi <;>
    rcases hev with hev | hev <;> rcases hfv with hfv | hfv <;> simp_all

theorem endpointSign_eq_zero (G : Graph V E) (v : V) (e : E)
    (h : ¬(G.src e = v ∨ G.dst e = v)) : endpointSign G v e = 0 := by
  simp [endpointSign, (not_or.mp h).1, (not_or.mp h).2]

theorem endpointSign_sq (G : Graph V E) (v : V) (e : E)
    (h : G.src e = v ∨ G.dst e = v) : endpointSign G v e ^ 2 = 1 := by
  rcases h with h | h
  · simp [endpointSign, h]
  · by_cases hs : G.src e = v <;> simp [endpointSign, hs, h]

theorem adjacent_interiorIntersection_eq_zero (N : NormalizedDrawing G) (e f : E)
    (hef : e ≠ f) (i : V) (he : G.src e = i ∨ G.dst e = i)
    (hf : G.src f = i ∨ G.dst f = i) : interiorIntersection N e f = 0 := by
  have hadj : G.src e = G.src f ∨ G.src e = G.dst f ∨
      G.dst e = G.src f ∨ G.dst e = G.dst f := by
    rcases he with he | he <;> rcases hf with hf | hf <;> simp_all
  by_contra hn
  obtain ⟨x,hx⟩ := interiorIntersection_ne_zero_crossing N e f hn
  obtain ⟨_,_,hxe,hxf⟩ := Finset.mem_filter.mp hx
  exact Set.disjoint_left.mp (N.no_adjacent e f hef hadj) hxe hxf

theorem cycleIntersection_incident [Fintype V] (N : NormalizedDrawing G)
    (O : SpokeOrders N) (e f : E) (hef : e ≠ f) (i : V)
    (he : G.src e = i ∨ G.dst e = i) (hf : G.src f = i ∨ G.dst f = i) :
    cycleIntersection O e f = (1 / 2 : ℝ) *
      (endpointSign G i e * endpointSign G i f * spokeComparison O i e f) := by
  have hs : (∑ v, endpointSign G v e * endpointSign G v f * spokeComparison O v e f) =
      endpointSign G i e * endpointSign G i f * spokeComparison O i e f := by
    apply Finset.sum_eq_single i
    · intro v _ hvi
      by_cases hev : G.src e = v ∨ G.dst e = v
      · by_cases hfv : G.src f = v ∨ G.dst f = v
        · exact False.elim (hvi (G.common_endpoint_unique e f hef i v he hf hev hfv))
        · rw [endpointSign_eq_zero G v f hfv]
          ring
      · rw [endpointSign_eq_zero G v e hev]
        ring
    · simp
  simp only [cycleIntersection, hs, adjacent_interiorIntersection_eq_zero N e f hef i he hf,
    zero_add]

theorem completeIncidentEdge_neighbor {n : ℕ} (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    (if (completeIncidentEdge i p).val.val.1 = i then
      (completeIncidentEdge i p).val.val.2 else (completeIncidentEdge i p).val.val.1) = p.val := by
  by_cases h : i < p.val <;> simp [completeIncidentEdge, h, p.property]

theorem completeIncidentEdge_injective {n : ℕ} (i : Fin n) :
    Function.Injective (completeIncidentEdge i) := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg (fun e : (completeGraph n).IncidentEdge i =>
    if e.val.val.1 = i then e.val.val.2 else e.val.val.1) hpq
  simpa only [completeIncidentEdge_neighbor] using h

theorem completeEdgeVector_incident {n : ℕ} (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    completeEdgeVector i p.val =
      endpointSign (completeGraph n) i (completeIncidentEdge i p).val •
        Pi.single (completeIncidentEdge i p).val 1 := by
  by_cases h : i < p.val
  · simpa [completeIncidentEdge, h, endpointSign, completeGraph] using
      completeEdgeVector_endpoints (⟨(i,p.val),h⟩ : CompleteEdge n)
  · have hp : p.val < i := lt_of_le_of_ne (le_of_not_gt h) p.property
    have he := completeEdgeVector_reverse p.val i
    rw [show completeEdgeVector p.val i = Pi.single (⟨(p.val,i),hp⟩ : CompleteEdge n) 1 from
      completeEdgeVector_endpoints ⟨(p.val,i),hp⟩] at he
    simpa [completeIncidentEdge, h, endpointSign, completeGraph, p.property] using he

theorem edgePairing_smul_smul [Fintype E] (J : E → E → ℝ) (a b : ℝ) (z z' : E → ℝ) :
    edgePairing J (a • z) (b • z') = (a*b) * edgePairing J z z' := by
  simp only [edgePairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem halfOrder_self {ι : Type} (order : LinearOrder ι) (p : ι) :
    halfOrder order p p = 0 := by
  let _ : LinearOrder ι := order
  simp [halfOrder]

theorem complete_local_orders {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (O : SpokeOrders N) :
    ∃ orders : ∀ i : Fin n, LinearOrder {j : Fin n // j ≠ i},
      ∀ i (p q : {j : Fin n // j ≠ i}),
        rawCycleIntersection O i p.val i q.val = halfOrder (orders i) p q := by
  let orders (i : Fin n) : LinearOrder {j : Fin n // j ≠ i} :=
    @LinearOrder.lift' _ _ (O.order i) (completeIncidentEdge i) (completeIncidentEdge_injective i)
  refine ⟨orders,?_⟩
  intro i p q
  by_cases hpq : p = q
  · subst q
    have hh := (raw_cycle_symmetries N O).2.2.2.2 i p.val i p.val
    have hz : rawCycleIntersection O i p.val i p.val = 0 := by linarith
    rw [hz]
    exact (halfOrder_self (orders i) p).symm
  · let e := completeIncidentEdge i p
    let f := completeIncidentEdge i q
    have hef : e.val ≠ f.val := fun h =>
      hpq (completeIncidentEdge_injective i (Subtype.ext h))
    rw [rawCycleIntersection, completeEdgeVector_incident, completeEdgeVector_incident,
      edgePairing_smul_smul]
    have hsingle : edgePairing (cycleIntersection O) (Pi.single e.val 1) (Pi.single f.val 1) =
        cycleIntersection O e.val f.val := by
      simp [edgePairing, Pi.single_apply, ite_mul, mul_ite]
    change (endpointSign (completeGraph n) i e.val * endpointSign (completeGraph n) i f.val) *
      edgePairing (cycleIntersection O) (Pi.single e.val 1) (Pi.single f.val 1) = _
    rw [hsingle, cycleIntersection_incident N O e.val f.val hef i e.property f.property]
    calc
      _ = (1/2 : ℝ) * (endpointSign (completeGraph n) i e.val ^ 2) *
          (endpointSign (completeGraph n) i f.val ^ 2) * spokeComparison O i e.val f.val := by ring
      _ = (1/2 : ℝ) * spokeComparison O i e.val f.val := by
        rw [endpointSign_sq _ _ _ e.property, endpointSign_sq _ _ _ f.property]
        ring
      _ = halfOrder (orders i) p q := by
        unfold spokeComparison
        rw [dite_eq_left e.property, dite_eq_left f.property]
        change (1/2 : ℝ) *
          (if @LT.lt _ (O.order i).toLT e f then 1
            else if @LT.lt _ (O.order i).toLT f e then -1 else 0) =
          (if @LT.lt _ (O.order i).toLT e f then 1/2
            else if @LT.lt _ (O.order i).toLT f e then -(1/2) else 0)
        split_ifs <;> ring

end Paper170

end
end

section

/-! The directed complete-graph chains and the chosen unoriented edge representatives agree. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E A : Type} [Fintype E] [Fintype A]

theorem boundary_sum (G : Graph V E) (w : A → E → ℝ) (v : V) :
    boundary G (fun e => ∑ a, w a e) v = ∑ a, boundary G (w a) v := by
  simp only [boundary,Finset.sum_mul]
  exact Finset.sum_comm

theorem boundary_mul (G : Graph V E) (c : ℝ) (w : E → ℝ) (v : V) :
    boundary G (fun e => c*w e) v = c*boundary G w v := by
  simp only [boundary,Finset.mul_sum,mul_assoc]

theorem edgePairing_sum_left (J : E → E → ℝ) (w : A → E → ℝ) (z : E → ℝ) :
    edgePairing J (fun e => ∑ a, w a e) z = ∑ a, edgePairing J (w a) z := by
  simp only [edgePairing,Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun f a => w a _ * z f * J _ f)]
  exact Finset.sum_comm

theorem edgePairing_sum_right (J : E → E → ℝ) (z : E → ℝ) (w : A → E → ℝ) :
    edgePairing J z (fun e => ∑ a, w a e) = ∑ a, edgePairing J z (w a) := by
  simp only [edgePairing,Finset.mul_sum,Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun f a => z _ * w a f * J _ f)]
  exact Finset.sum_comm

theorem edgePairing_mul_left (J : E → E → ℝ) (c : ℝ) (z w : E → ℝ) :
    edgePairing J (fun e => c*z e) w = c*edgePairing J z w := by
  simp only [edgePairing,Finset.mul_sum,mul_assoc]

theorem edgePairing_mul_right (J : E → E → ℝ) (c : ℝ) (z w : E → ℝ) :
    edgePairing J z (fun e => c*w e) = c*edgePairing J z w := by
  simp only [edgePairing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

omit [Fintype E] [Fintype A] in
theorem boundary_completeEdgeVector {n : ℕ} (i p v : Fin n) :
    boundary (completeGraph n) (completeEdgeVector i p) v =
      (if p=v then 1 else 0) - (if i=v then 1 else 0) := by
  rcases lt_trichotomy i p with hip | rfl | hpi
  · let e : CompleteEdge n := ⟨(i,p),hip⟩
    have hs := completeEdgeVector_endpoints e
    change completeEdgeVector i p = Pi.single e 1 at hs
    rw [hs]
    simp [boundary,Pi.single_apply,completeGraph,e]
    exact congrArg₂ (fun x y : ℝ => x-y)
      (ite_cond_congr rfl) (ite_cond_congr rfl)
  · rw [completeEdgeVector_self]
    simp [boundary]
  · let e : CompleteEdge n := ⟨(p,i),hpi⟩
    have hs := completeEdgeVector_endpoints e
    change completeEdgeVector p i = Pi.single e 1 at hs
    rw [completeEdgeVector_reverse,hs]
    simp [boundary,Pi.single_apply,completeGraph,e]
    exact congrArg₂ (fun x y : ℝ => x-y)
      (ite_cond_congr rfl) (ite_cond_congr rfl)

omit [Fintype E] [Fintype A] in
theorem boundary_liftedChain {n : ℕ} (z : Fin n → Fin n → ℝ) (v : Fin n) :
    boundary (completeGraph n) (liftedChain z) v = chainBoundary z v := by
  unfold liftedChain
  rw [boundary_sum]
  simp_rw [boundary_sum,boundary_mul,boundary_completeEdgeVector,mul_sub]
  simp [chainBoundary,Finset.sum_sub_distrib]

omit [Fintype E] [Fintype A] in
theorem chainPairing_rawCycleIntersection {n : ℕ} {N : NormalizedDrawing (completeGraph n)}
    (O : SpokeOrders N) (z z' : Fin n → Fin n → ℝ) :
    chainPairing (rawCycleIntersection O) z z' =
      edgePairing (cycleIntersection O) (liftedChain z) (liftedChain z') := by
  unfold liftedChain
  simp_rw [edgePairing_sum_left,edgePairing_sum_right,edgePairing_mul_left,edgePairing_mul_right]
  unfold chainPairing rawCycleIntersection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro q _
  ring

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CycleIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric cycle identity deduced from endpoint and intersection coordinates. -/

section

/-! The source cycle identity for every normalized ordinary drawing. -/
noncomputable section
namespace Paper170
open Paper170Geometry

theorem cycle_pairing {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    (G : Graph Vertex Edge) (N : NormalizedDrawing G) (O : SpokeOrders N)
    (z z' : Edge → ℝ) (hz : ∀v, boundary G z v = 0) (hz' : ∀v, boundary G z' v = 0) :
    edgePairing (cycleIntersection O) z z' = 0 := by
  obtain ⟨V⟩ := normalized_vertexTruncation N
  obtain ⟨C,hC⟩ := exists_truncatedSpokeCoordinates_compatible N V O
  exact cycle_pairing_of_coordinates N O V C hC z z' hz hz'

theorem raw_cycle_pairing {n : ℕ} (N : NormalizedDrawing (completeGraph n)) (O : SpokeOrders N)
    (z z' : Fin n → Fin n → ℝ) (hz : ∀v, chainBoundary z v = 0) (hz' : ∀v, chainBoundary z' v = 0) :
    chainPairing (rawCycleIntersection O) z z' = 0 := by
  rw [chainPairing_rawCycleIntersection]
  apply cycle_pairing (completeGraph n) N O (liftedChain z) (liftedChain z')
  · simpa only [boundary_liftedChain] using hz
  · simpa only [boundary_liftedChain] using hz'

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Deletion
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex deletion, its crossing-count identity, and small complete graphs. -/

section

noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

lemma deletionEdge_range {n : ℕ} (v : Fin (n + 1)) (e : CompleteEdge (n + 1)) :
    (∃ f, deletionEdge v f = e) ↔ e.val.1 ≠ v ∧ e.val.2 ≠ v := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Fin.succAbove_ne v _, Fin.succAbove_ne v _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h1
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq h2
    have hab : a < b := (Fin.strictMono_succAbove v).lt_iff_lt.mp (by
      rw [ha, hb]
      exact e.property)
    exact ⟨⟨(a,b), hab⟩, Subtype.ext (Prod.ext ha hb)⟩

lemma deleteDrawing_spec {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : VertexDeletion D v (deleteDrawing D v) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro e f h1 h2 t
  have h : f = deletionEdge v e := Subtype.ext (Prod.ext h1 h2)
  subst f
  rfl

lemma deletion_crossing_iff {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) (x : Plane) (e f : CompleteEdge (n + 1)) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    x ∈ crossingPoints (deleteDrawing D v).toContinuousDrawing ↔
      e.val.1 ≠ v ∧ e.val.2 ≠ v ∧ f.val.1 ≠ v ∧ f.val.2 ≠ v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' := (Paper170Geometry.crossing_incident_iff D x e f hef he hf
      (deletionEdge v a)).mp ha
    have hb' := (Paper170Geometry.crossing_incident_iff D x e f hef he hf
      (deletionEdge v b)).mp hb
    have hab' : deletionEdge v a ≠ deletionEdge v b :=
      fun h => hab (deletionEdge_injective v h)
    have hae := (deletionEdge_range v (deletionEdge v a)).mp ⟨a, rfl⟩
    have hbe := (deletionEdge_range v (deletionEdge v b)).mp ⟨b, rfl⟩
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact (hab' (ha'.trans hb'.symm)).elim
    · simpa [ha', hb', and_assoc] using And.intro hae hbe
    · simpa [ha', hb', and_assoc] using And.intro hbe hae
    · exact (hab' (ha'.trans hb'.symm)).elim
  · rintro ⟨he1, he2, hf1, hf2⟩
    obtain ⟨a, ha⟩ := (deletionEdge_range v e).mpr ⟨he1, he2⟩
    obtain ⟨b, hb⟩ := (deletionEdge_range v f).mpr ⟨hf1, hf2⟩
    refine ⟨a, b, ?_, ?_, ?_⟩
    · intro h
      exact hef (ha.symm.trans ((congrArg (deletionEdge v) h).trans hb))
    · change x ∈ edgeInterior D.toContinuousDrawing (deletionEdge v a)
      simpa [ha] using he
    · change x ∈ edgeInterior D.toContinuousDrawing (deletionEdge v b)
      simpa [hb] using hf

end Paper170

end
end

section

noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170

lemma crossing_endpoints_distinct {n : ℕ} (N : NormalizedDrawing (completeGraph n))
    (x : Plane) (e f : CompleteEdge n) (hef : e ≠ f)
    (he : x ∈ edgeInterior N.toContinuousDrawing e)
    (hf : x ∈ edgeInterior N.toContinuousDrawing f) :
    e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
  have hn : ¬ (e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨
      e.val.2 = f.val.1 ∨ e.val.2 = f.val.2) := by
    intro h
    exact Set.disjoint_left.mp (N.no_adjacent e f hef h) he hf
  tauto

lemma deletion_survivor_card {n : ℕ} (N : NormalizedDrawing (completeGraph (n + 1)))
    (x : Plane) (hx : x ∈ crossingPoints N.toContinuousDrawing) :
    (Finset.univ.filter (fun v : Fin (n + 1) =>
      x ∈ crossingPoints (deleteDrawing N.toAdmissibleDrawing v).toContinuousDrawing)).card =
      n + 1 - 4 := by
  obtain ⟨e, f, hef, he, hf⟩ := hx
  rcases crossing_endpoints_distinct N x e f hef he hf with ⟨h13, h14, h23, h24⟩
  have h12 : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have h34 : f.val.1 ≠ f.val.2 := ne_of_lt f.property
  simp_rw [deletion_crossing_iff N.toAdmissibleDrawing _ x e f hef he hf]
  have hset : Finset.univ.filter (fun v : Fin (n + 1) =>
      e.val.1 ≠ v ∧ e.val.2 ≠ v ∧ f.val.1 ≠ v ∧ f.val.2 ≠ v) =
      Finset.univ \ {e.val.1, e.val.2, f.val.1, f.val.2} := by
    ext v
    simp [eq_comm]
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [h12, h13, h14, h23, h24, h34]

lemma deleteDrawing_count_filter {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) :
    crossingCount (deleteDrawing D v) = (D.crossings_finite.toFinset.filter fun x =>
      x ∈ crossingPoints (deleteDrawing D v).toContinuousDrawing).card := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨deletion_crossings_subset D.toContinuousDrawing v h, h⟩, And.right⟩

theorem vertex_deletion_count (n : ℕ) (_hn : 4 ≤ n)
    (N : NormalizedDrawing (completeGraph (n + 1))) :
    ∃ A : Fin (n + 1) → AdmissibleDrawing (completeGraph n),
      (∀ v, VertexDeletion N.toAdmissibleDrawing v (A v)) ∧
      (∑ v, crossingCount (A v)) = (n + 1 - 4) * crossingCount N.toAdmissibleDrawing := by
  refine ⟨deleteDrawing N.toAdmissibleDrawing, deleteDrawing_spec N.toAdmissibleDrawing, ?_⟩
  simp_rw [deleteDrawing_count_filter, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ N.crossings_finite.toFinset,
      ∑ v : Fin (n + 1), if x ∈ crossingPoints
        (deleteDrawing N.toAdmissibleDrawing v).toContinuousDrawing then 1 else 0) =
        ∑ _x ∈ N.crossings_finite.toFinset, (n + 1 - 4) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [Finset.card_filter] using
        deletion_survivor_card N x (by simpa using hx)
    _ = (n + 1 - 4) * crossingCount N.toAdmissibleDrawing := by
      simp [crossingCount, Nat.mul_comm]

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Hill
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harary–Hill arithmetic, residue-page definitions, and the even-order deletion inequality. -/

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem hill_numerator_dvd (n : ℕ) :
    4 ∣ n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  have h₂ : (n - 2) / 2 = n / 2 - 1 := by omega
  have h₃ : (n - 3) / 2 = (n - 1) / 2 - 1 := by omega
  rw [h₂, h₃]
  convert Nat.mul_dvd_mul (Nat.two_dvd_mul_sub_one (n / 2))
    (Nat.two_dvd_mul_sub_one ((n - 1) / 2)) using 1
  ring

theorem hill_odd (s : ℕ) : hill (2 * s + 1) = (s.choose 2) ^ 2 := by
  have h₀ : (2 * s + 1) / 2 = s := by omega
  have h₁ : (2 * s + 1 - 1) / 2 = s := by omega
  have h₂ : (2 * s + 1 - 2) / 2 = s - 1 := by omega
  have h₃ : (2 * s + 1 - 3) / 2 = s - 1 := by omega
  have hdiv := Nat.two_dvd_mul_sub_one s
  obtain ⟨a, ha⟩ := hdiv
  rw [hill, h₀, h₁, h₂, h₃, Nat.choose_two_right]
  have hp : s * s * (s - 1) * (s - 1) = 4 * a ^ 2 := by nlinarith [ha]
  rw [hp, ha]
  simp

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma four_mul_hill (n : ℕ) :
    4 * hill n = n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  exact Nat.mul_div_cancel' (hill_numerator_dvd n)

lemma four_mul_hill_even (s : ℕ) :
    4 * hill (2 * s) = s * (s - 1) ^ 2 * (s - 2) := by
  rw [four_mul_hill]
  have h0 : 2 * s / 2 = s := by omega
  have h1 : (2 * s - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 2) / 2 = s - 1 := by omega
  have h3 : (2 * s - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma four_mul_hill_preceding (s : ℕ) :
    4 * hill (2 * s - 1) = (s - 1) ^ 2 * (s - 2) ^ 2 := by
  rw [four_mul_hill]
  have h0 : (2 * s - 1) / 2 = s - 1 := by omega
  have h1 : (2 * s - 1 - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 1 - 2) / 2 = s - 2 := by omega
  have h3 : (2 * s - 1 - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma hill_deletion_relation (s : ℕ) :
    (2 * s - 4) * hill (2 * s) = 2 * s * hill (2 * s - 1) := by
  have hs : 2 * s - 4 = 2 * (s - 2) := by omega
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4)
  calc
    4 * ((2 * s - 4) * hill (2 * s)) =
        (2 * s - 4) * (4 * hill (2 * s)) := by ring
    _ = (2 * s - 4) * (s * (s - 1) ^ 2 * (s - 2)) := by rw [four_mul_hill_even]
    _ = 2 * s * ((s - 1) ^ 2 * (s - 2) ^ 2) := by rw [hs]; ring
    _ = 4 * (2 * s * hill (2 * s - 1)) := by rw [← four_mul_hill_preceding]; ring

lemma even_lower_bound_of_deletion (s c : ℕ) (hs : 3 ≤ s)
    (h : 2 * s * hill (2 * s - 1) ≤ (2 * s - 4) * c) : hill (2 * s) ≤ c := by
  rw [← hill_deletion_relation] at h
  have hp : 0 < 2 * s - 4 := by omega
  nlinarith

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolynomialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem bounded_mono {k l : ℕ} {p : PolynomialModule ℝ W}
    (hp : Bounded k p) (hkl : k ≤ l) : Bounded l p :=
  fun n hn => hp n (hkl.trans hn)

theorem bounded_sub {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p - q) := by
  intro n hn
  change p.coeff n - q.coeff n = 0
  rw [hp n hn, hq n hn, sub_self]

theorem bounded_single {k n : ℕ} (hn : n < k) (w : W) :
    Bounded k (single ℝ n w) := by
  intro j hj
  simp [show n ≠ j by omega]

theorem bounded_zero_iff (p : PolynomialModule ℝ W) : Bounded 0 p ↔ p = 0 := by
  constructor
  · intro h
    ext n
    exact h n (Nat.zero_le n)
  · rintro rfl
    exact bounded_zero 0

theorem mulRoot_coeff_zero (t : ℝ) (p : PolynomialModule ℝ W) :
    (mulRoot t p).coeff 0 = -t • p.coeff 0 := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff 0 -
    (Polynomial.C t • p).coeff 0) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem mulRoot_coeff_succ (t : ℝ) (p : PolynomialModule ℝ W) (n : ℕ) :
    (mulRoot t p).coeff (n+1) = p.coeff n - t • p.coeff (n+1) := by
  unfold mulRoot
  rw [sub_smul]
  change (((Polynomial.X : Polynomial ℝ) • p).coeff (n+1) -
    (Polynomial.C t • p).coeff (n+1)) = _
  simp [← Polynomial.monomial_one_one_eq_X, ← Polynomial.monomial_zero_left]

theorem eval_mulRoot (t u : ℝ) (p : PolynomialModule ℝ W) :
    eval u (mulRoot t p) = (u-t) • eval u p := by
  simp [mulRoot]

theorem bounded_mulRoot {k : ℕ} {p : PolynomialModule ℝ W}
    (t : ℝ) (hp : Bounded k p) : Bounded (k+1) (mulRoot t p) := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [mulRoot_coeff_succ, hp j (by omega), hp (j+1) (by omega)]
  simp

theorem eq_constant_of_bounded_one {p : PolynomialModule ℝ W} (hp : Bounded 1 p) :
    p = single ℝ 0 (p.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [hp (n+1) (by omega)]

theorem exists_mulRoot_of_eval_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded (k+1) p) (he : eval t p = 0) :
    ∃ q, Bounded k q ∧ mulRoot t q = p := by
  induction k generalizing p with
  | zero =>
    have hc := eq_constant_of_bounded_one hp
    have hz : p.coeff 0 = 0 := by
      rw [hc] at he
      simpa only [eval_single, pow_zero, one_smul] using he
    refine ⟨0, bounded_zero 0, ?_⟩
    have hp0 : p = 0 := hc.trans (by rw [hz, single_zero])
    simp [mulRoot, hp0]
  | succ k ih =>
    let q₀ := single ℝ k (p.coeff (k+1))
    have hq₀ : Bounded (k+1) q₀ := bounded_single (by omega) _
    let r := p - mulRoot t q₀
    have hr : Bounded (k+1) r := by
      intro n hn
      rcases eq_or_lt_of_le hn with rfl | hn'
      · change p.coeff (k+1) - (mulRoot t q₀).coeff (k+1) = 0
        rw [mulRoot_coeff_succ]
        simp [q₀]
      · exact bounded_sub hp (bounded_mulRoot t hq₀) n (by omega)
    have er : eval t r = 0 := by simp [r, eval_mulRoot, he]
    obtain ⟨q, hq, eq⟩ := ih r hr er
    refine ⟨q + q₀, bounded_add (bounded_mono hq (by omega)) hq₀, ?_⟩
    change (Polynomial.X - Polynomial.C t) • (q + q₀) = p
    rw [smul_add]
    change mulRoot t q + mulRoot t q₀ = p
    rw [eq]
    exact sub_add_cancel p _

theorem eq_zero_of_mulRoot_eq_zero (t : ℝ) (k : ℕ) (p : PolynomialModule ℝ W)
    (hp : Bounded k p) (he : mulRoot t p = 0) : p = 0 := by
  induction k with
  | zero => exact (bounded_zero_iff p).mp hp
  | succ k ih =>
    have hc : p.coeff k = 0 := by
      have hh := congrArg (fun q : PolynomialModule ℝ W => q.coeff (k+1)) he
      rw [mulRoot_coeff_succ, hp (k+1) (by omega)] at hh
      simpa using hh
    apply ih
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hn'
    · exact hc
    · exact hp n (by omega)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ι : Type*}

theorem eq_zero_of_node_roots (node : ι → ℝ) (hn : Function.Injective node)
    (s : Finset ι) (p : PolynomialModule ℝ W) (hp : Bounded s.card p)
    (he : ∀ i ∈ s, eval (node i) p = 0) : p = 0 := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact (bounded_zero_iff p).mp hp
  | @insert a s ha ih =>
    have hp' : Bounded (s.card+1) p := by simpa [Finset.card_insert_of_notMem ha] using hp
    obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero (node a) s.card p hp'
      (he a (Finset.mem_insert_self a s))
    have hqe : ∀ i ∈ s, eval (node i) q = 0 := by
      intro i hi
      have h := he i (Finset.mem_insert_of_mem hi)
      rw [← eq, eval_mulRoot] at h
      have hia : node i - node a ≠ 0 := sub_ne_zero.mpr (fun e => ha (hn e ▸ hi))
      exact (smul_eq_zero.mp h).resolve_left hia
    have hq0 := ih q hq hqe
    rw [← eq, hq0]
    simp [mulRoot]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

theorem flattenBi_apply (p : BiPoly) (a b : ℕ) : flattenBi p (a,b) = biCoeff p a b := rfl

theorem biCoeff_swap (p : BiPoly) (a b : ℕ) : biCoeff (swapBi p) a b = biCoeff p b a := by
  rw [← flattenBi_apply]
  change flattenBi (flattenBi.symm _) (a,b) = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_equiv_apply (flattenBi p) (a,b)

theorem bi_ext {p q : BiPoly} (h : ∀ a b, biCoeff p a b = biCoeff q a b) : p = q := by
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro a
  apply PolynomialModule.ext
  apply Finsupp.ext
  exact h a

theorem swapBi_swapBi (p : BiPoly) : swapBi (swapBi p) = p := by
  apply bi_ext
  intro a b
  rw [biCoeff_swap, biCoeff_swap]

theorem swapBi_single (a b : ℕ) (c : ℝ) :
    swapBi (single ℝ a (single ℝ b c)) = single ℝ b (single ℝ a c) := by
  apply bi_ext
  intro i j
  rw [biCoeff_swap]
  simp [biCoeff, Finsupp.single_apply]
  split_ifs <;> simp_all

theorem biEval_swap (p : BiPoly) (u v : ℝ) : biEval u v (swapBi p) = biEval v u p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single a q =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [single_add, map_add, hp, hq]
    | single b c =>
      rw [swapBi_single]
      simp [biEval, eval_single, smul_eq_mul]
      ring

theorem biBounded_swap {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) :
    BiBounded s r (swapBi p) := by
  constructor
  · intro a ha
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro b
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    exact hp.2 b a ha
  · intro a b hb
    change biCoeff (swapBi p) a b = 0
    rw [biCoeff_swap]
    simp [biCoeff, hp.1 b hb]

theorem coefficients_of_mulRoot {W : Type*} [AddCommGroup W] [Module ℝ W]
    (Z : Submodule ℝ W) (t : ℝ) (k : ℕ) (q : PolynomialModule ℝ W)
    (hq : Bounded k q) (hc : ∀ n, (mulRoot t q).coeff n ∈ Z) :
    ∀ n, q.coeff n ∈ Z := by
  have aux : ∀ d n, k-n = d → q.coeff n ∈ Z := by
    intro d
    induction d with
    | zero =>
      intro n hn
      rw [hq n (by omega)]
      exact Z.zero_mem
    | succ d ih =>
      intro n hn
      have hh := Z.add_mem (hc (n+1)) (Z.smul_mem t (ih (n+1) (by omega)))
      simpa only [mulRoot_coeff_succ, sub_add_cancel] using hh
  intro n
  exact aux (k-n) n rfl

theorem bi_factor_row (r s : ℕ) (p : BiPoly) (hp : BiBounded (r+1) s p)
    (t : ℝ) (hz : eval t p = 0) :
    ∃ q : BiPoly, BiBounded r s q ∧ mulRoot t q = p := by
  obtain ⟨q, hq, he⟩ := exists_mulRoot_of_eval_zero t r p hp.1 hz
  refine ⟨q, ⟨hq, ?_⟩, he⟩
  apply coefficients_of_mulRoot (boundedSpace s) t r q hq
  intro n
  rw [he]
  exact hp.2 n

theorem biEval_mulRoot (t u v : ℝ) (p : BiPoly) :
    biEval u v (mulRoot t p) = (u-t) * biEval u v p := by
  change eval v (eval u (mulRoot t p)) = _
  rw [eval_mulRoot, _root_.map_smul]
  rfl

theorem bounded_eval_outer {r s : ℕ} {p : BiPoly} (hp : BiBounded r s p) (u : ℝ) :
    Bounded s (eval u p) := by
  change eval u p ∈ boundedSpace s
  change p.coeff.sum (fun a c => u^a • c) ∈ boundedSpace s
  apply Submodule.sum_mem
  intro a ha
  exact (boundedSpace s).smul_mem (u^a) (hp.2 a)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TwoTriangleIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open Finset

theorem mem_lowerTriangle (s p q : ℕ) :
    (p,q) ∈ lowerTriangle s ↔ 1 ≤ q ∧ q < p ∧ p ≤ s+1 := by
  simp only [lowerTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_upperTriangle (s p q : ℕ) :
    (p,q) ∈ upperTriangle s ↔ s+1 < p ∧ p < q ∧ q ≤ 2*s+1 := by
  simp only [upperTriangle, mem_filter, mem_product, mem_Icc]
  omega

theorem mem_twoTriangle (s p q : ℕ) :
    (p,q) ∈ twoTriangle s ↔
      (1 ≤ q ∧ q < p ∧ p ≤ s+1) ∨ (s+1 < p ∧ p < q ∧ q ≤ 2*s+1) := by
  rw [twoTriangle, mem_union, mem_lowerTriangle, mem_upperTriangle]

theorem triangleRelabel_injective_on (s : ℕ) :
    Set.InjOn (triangleRelabel s) (Set.Icc 1 (2*s-1)) := by
  intro p hp q hq he
  simp only [Set.mem_Icc] at hp hq
  unfold triangleRelabel at he
  split_ifs at he <;> omega

theorem triangleRelabel_range (s k : ℕ) (hk : k ∈ Icc 1 (2*s-1)) :
    triangleRelabel s k ∈ Icc 1 (2*s+1) ∧
      triangleRelabel s k ≠ s+1 ∧ triangleRelabel s k ≠ 1 := by
  simp only [mem_Icc] at hk ⊢
  unfold triangleRelabel
  split_ifs <;> omega

theorem relabel_twoTriangle (s : ℕ) (hs : 1 ≤ s) (p q : ℕ)
    (hpq : (p,q) ∈ twoTriangle (s-1)) :
    (triangleRelabel s q, triangleRelabel s p) ∈ twoTriangle s ∧
      triangleRelabel s q ≠ s+1 ∧ triangleRelabel s p ≠ 1 := by
  rw [mem_twoTriangle] at hpq ⊢
  unfold triangleRelabel
  split_ifs <;> omega

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TwoTriangleUnisolvence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open Finset

theorem eq_zero_of_roots_injOn {W : Type*} [AddCommGroup W] [Module ℝ W]
    (node : ℕ → ℝ) (S : Finset ℕ) (hn : Set.InjOn node (S : Set ℕ))
    (p : PolynomialModule ℝ W) (hp : Bounded S.card p)
    (he : ∀ i ∈ S, eval (node i) p = 0) : p = 0 := by
  let x : S → ℝ := fun i => node i.val
  have hx : Function.Injective x := by
    intro i j hij
    exact Subtype.ext (hn i.property j.property hij)
  apply eq_zero_of_node_roots x hx Finset.univ p
  · simpa using hp
  · intro i hi
    exact he i.val i.property

theorem twoTriangle_unisolvent (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (p : BiPoly)
    (hp : BiBounded s s p)
    (hv : ∀ a b, (a,b) ∈ twoTriangle s → biEval (node a) (node b) p = 0) : p = 0 := by
  induction s generalizing node p with
  | zero => exact (bounded_zero_iff p).mp hp.1
  | succ k ih =>
    have node_ne : ∀ a b, a ∈ Icc 1 (2*(k+1)+1) → b ∈ Icc 1 (2*(k+1)+1) →
        a ≠ b → node a ≠ node b := by
      intro a b ha hb hab he
      exact hab (hn (by simpa only [mem_Icc, Set.mem_Icc] using ha)
        (by simpa only [mem_Icc, Set.mem_Icc] using hb) he)

    have hrow : eval (node (k+2)) p = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 1 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer hp (node (k+2))
      · intro q hq
        apply hv (k+2) q
        rw [mem_twoTriangle]
        simp only [mem_Icc] at hq
        left
        omega
    obtain ⟨p₁, hp₁, he₁⟩ := bi_factor_row k (k+1) p hp (node (k+2)) hrow

    have hcol : eval (node 1) (swapBi p₁) = 0 := by
      apply eq_zero_of_roots_injOn node (Icc 2 (k+1))
      · intro a ha b hb he
        apply hn _ _ he <;> simp only [mem_coe, mem_Icc, Set.mem_Icc] at * <;> omega
      · simpa using bounded_eval_outer (biBounded_swap hp₁) (node 1)
      · intro a ha
        change biEval (node 1) (node a) (swapBi p₁) = 0
        rw [biEval_swap]
        have hpa : biEval (node a) (node 1) p = 0 := by
          apply hv
          rw [mem_twoTriangle]
          simp only [mem_Icc] at ha
          left
          omega
        rw [← he₁, biEval_mulRoot] at hpa
        apply (mul_eq_zero.mp hpa).resolve_left
        apply sub_ne_zero.mpr
        apply node_ne a (k+2) <;> simp only [mem_Icc] at * <;> omega
    obtain ⟨r, hr, her⟩ := bi_factor_row k k (swapBi p₁) (biBounded_swap hp₁) (node 1) hcol

    let y : ℕ → ℝ := fun i => node (triangleRelabel (k+1) i)
    have hyrange : ∀ a, a ∈ Icc 1 (2*k+1) →
        triangleRelabel (k+1) a ∈ Icc 1 (2*(k+1)+1) ∧
          triangleRelabel (k+1) a ≠ k+2 ∧ triangleRelabel (k+1) a ≠ 1 := by
      intro a ha
      simpa only [show k+1+1 = k+2 from rfl] using
        triangleRelabel_range (k+1) a (by simp only [mem_Icc] at *; omega)
    have hyn : Set.InjOn y (Set.Icc 1 (2*k+1)) := by
      intro a ha b hb he
      have ha' : a ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using ha
      have hb' : b ∈ Icc 1 (2*k+1) := by simpa only [mem_Icc, Set.mem_Icc] using hb
      apply triangleRelabel_injective_on (k+1)
      · simp only [Set.mem_Icc] at *
        omega
      · simp only [Set.mem_Icc] at *
        omega
      · exact hn (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange a ha').1)
          (by simpa only [Set.mem_Icc, mem_Icc] using (hyrange b hb').1) he
    have hrv : ∀ a b, (a,b) ∈ twoTriangle k → biEval (y a) (y b) r = 0 := by
      intro a b hab
      have ha : a ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hb : b ∈ Icc 1 (2*k+1) := by
        rw [mem_twoTriangle] at hab
        simp only [mem_Icc]
        omega
      have hpattern := relabel_twoTriangle (k+1) (by omega) a b (by simpa using hab)
      have hval := hv (triangleRelabel (k+1) b) (triangleRelabel (k+1) a) hpattern.1
      rw [← he₁, biEval_mulRoot] at hval
      have hfirst : node (triangleRelabel (k+1) b) - node (k+2) ≠ 0 :=
        sub_ne_zero.mpr (node_ne _ _ (hyrange b hb).1 (by simp) (hyrange b hb).2.1)
      have hp₁val := (mul_eq_zero.mp hval).resolve_left hfirst
      have hswap : p₁ = swapBi (mulRoot (node 1) r) := by rw [her, swapBi_swapBi]
      rw [hswap, biEval_swap, biEval_mulRoot] at hp₁val
      apply (mul_eq_zero.mp hp₁val).resolve_left
      exact sub_ne_zero.mpr (node_ne _ _ (hyrange a ha).1 (by simp) (hyrange a ha).2.2)
    have hr0 := ih y hyn r hr hrv
    have hp₁0 : p₁ = 0 := by
      apply swapBi.injective
      rw [← her, hr0]
      simp [mulRoot]
    rw [← he₁, hp₁0]
    simp [mulRoot]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bivariate interpolation degrees, spaces, pairings, and polynomial tests. -/

section

/-! Degree conventions and interpolation weights.
 -/

open scoped BigOperators
noncomputable section

namespace Paper170

theorem weight_nonzero {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (hn : Function.Injective node) (i : ι) : nodeWeight node i ≠ 0 := by
  classical
  exact inv_ne_zero (Zarankiewicz.derivativeAtNode_ne_zero node hn i)

theorem omitted_node_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) (i p : ι) (hip : i ≠ p) :
    (node p - node i) * nodeWeight node p =
      ((omittedNodePolynomial node i).derivative.eval (node p))⁻¹ := by
  have hF : Zarankiewicz.nodePolynomial node =
      (Polynomial.X - Polynomial.C (node i)) * omittedNodePolynomial node i :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)
  have hzero : (omittedNodePolynomial node i).eval (node p) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hip.symm, Finset.mem_univ p⟩)
  have hd : Zarankiewicz.derivativeAtNode node p = (node p - node i) *
      (omittedNodePolynomial node i).derivative.eval (node p) := by
    rw [Zarankiewicz.derivativeAtNode, hF, Polynomial.derivative_mul]
    simp [hzero]
  have hdiff : node p - node i ≠ 0 := sub_ne_zero.mpr (hn.ne hip.symm)
  rw [nodeWeight, hd, mul_inv, ← mul_assoc, mul_inv_cancel₀ hdiff, one_mul]

theorem weighted_chain_boundary {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (a b : ℕ) (ha : a + 1 < n) (hb : b + 1 < n) :
    ∀ v, chainBoundary (weightedChain node a b) v = 0 := by
  have hsum (k : ℕ) (hk : k + 1 < n) : ∑ i, nodeWeight node i * node i ^ k = 0 := by
    simpa only [nodeWeight, div_eq_mul_inv, mul_comm] using
      Zarankiewicz.node_power_moment node hn k (by simpa using hk)
  have hz (i p : Fin n) : weightedChain node a b i p =
      (nodeWeight node i * node i ^ a) * (nodeWeight node p * node p ^ b) := by
    unfold weightedChain
    ring
  intro v
  simp only [chainBoundary, hz, ← Finset.sum_mul, ← Finset.mul_sum, hsum a ha, hsum b hb,
    zero_mul, mul_zero, sub_self]

end Paper170

end
end

section

/-! Separate degree bounds for the local four-variable test polynomial. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem degreeOf_mul_bound {i : Fin 4} {P Q : Poly4} {a b : ℕ}
    (hP : P.degreeOf i ≤ a) (hQ : Q.degreeOf i ≤ b) : (P*Q).degreeOf i ≤ a+b :=
  (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add hP hQ)

theorem degreeOf_liftUnivariate (i k : Fin 4) (U : Polynomial ℝ) :
    (liftUnivariate i U).degreeOf k ≤ if k=i then U.natDegree else 0 := by
  classical
  unfold liftUnivariate
  conv_lhs => rw [← Polynomial.sum_monomial_eq U, Polynomial.sum, map_sum]
  apply (MvPolynomial.degreeOf_sum_le k _ _).trans
  apply Finset.sup_le
  intro a ha
  rw [Polynomial.aeval_monomial]
  change (MvPolynomial.C (U.coeff a) * MvPolynomial.X i ^ a).degreeOf k ≤ _
  apply (MvPolynomial.degreeOf_C_mul_le _ k _).trans
  by_cases h : k=i
  · subst k
    simpa using Polynomial.le_natDegree_of_mem_supp a ha
  · simp only [ite_eq_right h, MvPolynomial.degreeOf_X_pow_of_ne a h]
    exact Nat.le_refl 0

theorem liftBivariate_eq_rename (i j : Fin 4) (B : Poly2) :
    liftBivariate i j B = MvPolynomial.rename ![i,j] B := by
  have hf : (MvPolynomial.X ∘ (![i,j] : Fin 2 → Fin 4)) =
      (![MvPolynomial.X i, MvPolynomial.X j] : Fin 2 → Poly4) := by
    funext k
    fin_cases k <;> rfl
  simp only [liftBivariate, MvPolynomial.rename_eq_aeval, hf]

theorem degreeOf_rename_zero {σ : Type*} (f : σ → Fin 4) (B : MvPolynomial σ ℝ)
    (k : Fin 4) (hk : ∀i, f i ≠ k) : (MvPolynomial.rename f B).degreeOf k = 0 := by
  by_contra h
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename f B
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact hk i hi

theorem degreeOf_liftBivariate13 (B : Poly2) (k : Fin 4) :
    (liftBivariate 1 3 B).degreeOf k = ![0,B.degreeOf 0,0,B.degreeOf 1] k := by
  have hi : Function.Injective (![1,3] : Fin 2 → Fin 4) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
  rw [liftBivariate_eq_rename]
  fin_cases k
  · exact degreeOf_rename_zero _ B 0 (by intro i; fin_cases i <;> decide)
  · exact MvPolynomial.degreeOf_rename_of_injective hi 0
  · exact degreeOf_rename_zero _ B 2 (by intro i; fin_cases i <;> decide)
  · exact MvPolynomial.degreeOf_rename_of_injective hi 1

theorem degreeOf_difference_bound (i j k : Fin 4) :
    (MvPolynomial.X i - MvPolynomial.X j : Poly4).degreeOf k ≤
      max (if k=i then 1 else 0) (if k=j then 1 else 0) := by
  simpa only [MvPolynomial.degreeOf_X] using
    MvPolynomial.degreeOf_sub_le k (MvPolynomial.X i : Poly4) (MvPolynomial.X j)

theorem local_test_degree (s : ℕ) (hs : 2 ≤ s) (P : Poly4)
    (hP : P ∈ endpointSymmetricSpace s) (U V : Polynomial ℝ)
    (hU : U.natDegree ≤ s) (hV : V.natDegree ≤ s) (B : Poly2)
    (hB : B ∈ rectangle (s-1) (s-1)) :
    localTestPolynomial P U V B ∈ box4 (2*s-1) := by
  apply (box4_membership _ _).mpr
  intro k
  have hP := ((symmetric_space_membership s P).mp hP).1 k
  have hB := (rectangle_membership _ _ B).mp hB
  have h := degreeOf_mul_bound
    (degreeOf_mul_bound
      (degreeOf_mul_bound
        (degreeOf_mul_bound
          (degreeOf_mul_bound
            (degreeOf_mul_bound hP (degreeOf_difference_bound 1 3 k))
            (degreeOf_difference_bound 1 2 k))
          (degreeOf_difference_bound 3 0 k))
        (degreeOf_liftUnivariate 0 k U))
      (degreeOf_liftUnivariate 2 k V))
    (Nat.le_of_eq (degreeOf_liftBivariate13 B k))
  change (localTestPolynomial P U V B).degreeOf k ≤ _ at h
  fin_cases k <;> norm_num [Fin.ext_iff] at h ⊢ <;> omega

end Paper170

end
end

section

/-! Interpolation moments remove row and column perturbations from the order pairing. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalTwo_monomial (u v : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    evalTwo u v (MvPolynomial.monomial m c) = c*(u^m 0*v^m 1) := by
  simp only [evalTwo, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]
  · intro i
    simp

theorem weighted_evalTwo_second_zero {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (u : ℝ) (P : Poly2)
    (hP : P.degreeOf 1 + 1 < Fintype.card ι) :
    (∑q, evalTwo u (node q) P / Zarankiewicz.derivativeAtNode node q) = 0 := by
  classical
  rw [P.as_sum]
  simp only [map_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdeg := MvPolynomial.le_degreeOf_of_mem_support 1 hm
  have hz := Zarankiewicz.node_power_moment node hn (m 1) (by omega)
  calc
    (∑q, evalTwo u (node q) (MvPolynomial.monomial m (P.coeff m)) /
        Zarankiewicz.derivativeAtNode node q) =
      (P.coeff m*u^m 0) * ∑q, node q^m 1 / Zarankiewicz.derivativeAtNode node q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [evalTwo_monomial]
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem weighted_evalTwo_first_zero {ι : Type*} [Fintype ι]
    (node : ι → ℝ) (hn : Function.Injective node) (v : ℝ) (P : Poly2)
    (hP : P.degreeOf 0 + 1 < Fintype.card ι) :
    (∑p, evalTwo (node p) v P / Zarankiewicz.derivativeAtNode node p) = 0 := by
  classical
  rw [P.as_sum]
  simp only [map_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hmdeg := MvPolynomial.le_degreeOf_of_mem_support 0 hm
  have hz := Zarankiewicz.node_power_moment node hn (m 0) (by omega)
  calc
    (∑p, evalTwo (node p) v (MvPolynomial.monomial m (P.coeff m)) /
        Zarankiewicz.derivativeAtNode node p) =
      (P.coeff m*v^m 1) * ∑p, node p^m 0 / Zarankiewicz.derivativeAtNode node p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [evalTwo_monomial]
      ring
    _ = 0 := by rw [hz,mul_zero]

theorem weightedPairing_add {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (K L : ι → ι → ℝ) (A B : Poly2) :
    weightedPairing node (fun p q => K p q+L p q) A B =
      weightedPairing node K A B + weightedPairing node L A B := by
  simp [weightedPairing, add_mul, add_div, Finset.sum_add_distrib]

theorem evalTwo_difference_mul (u v : ℝ) (A B : Poly2) :
    evalTwo u v ((MvPolynomial.X 0-MvPolynomial.X 1)*A*B) =
      (u-v)*evalTwo u v A*evalTwo u v B := by
  simp [evalTwo]

theorem pairing_row_column_invariant {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (K : ι → ι → ℝ)
    (r c : ι → ℝ) (A B : Poly2)
    (hA : A ∈ rectangle (s-1) (s-2))
    (hB : B ∈ rectangle (s-2) (s-1)) :
    weightedPairing node (fun p q => K p q+r p+c q) A B =
      weightedPairing node K A B := by
  classical
  let C : Poly2 := (MvPolynomial.X 0-MvPolynomial.X 1)*A*B
  have hC (i : Fin 2) : C.degreeOf i + 1 < Fintype.card ι := by
    have hA := (rectangle_membership _ _ A).mp hA
    have hB := (rectangle_membership _ _ B).mp hB
    have h1 := MvPolynomial.degreeOf_mul_le i ((MvPolynomial.X 0-MvPolynomial.X 1)*A) B
    have h2 := MvPolynomial.degreeOf_mul_le i (MvPolynomial.X 0-MvPolynomial.X 1) A
    have h3 := MvPolynomial.degreeOf_sub_le i (MvPolynomial.X 0 : Poly2) (MvPolynomial.X 1)
    change C.degreeOf i ≤ _ at h1
    rw [hc]
    fin_cases i <;> norm_num [MvPolynomial.degreeOf_X, Fin.ext_iff] at h1 h2 h3 ⊢ <;> omega
  have hr : weightedPairing node (fun p _ => r p) A B = 0 := by
    unfold weightedPairing
    apply Finset.sum_eq_zero
    intro p _
    calc
      (∑q, r p*(node p-node q)/
        (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q)*
        evalTwo (node p) (node q) A*evalTwo (node p) (node q) B) =
        (r p/Zarankiewicz.derivativeAtNode node p) *
        ∑q, evalTwo (node p) (node q) C/Zarankiewicz.derivativeAtNode node q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          rw [show evalTwo (node p) (node q) C = _ from evalTwo_difference_mul _ _ A B]
          ring
      _ = 0 := by rw [weighted_evalTwo_second_zero node hn _ C (hC 1), mul_zero]
  have hcol : weightedPairing node (fun _ q => c q) A B = 0 := by
    unfold weightedPairing
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    calc
      (∑p, c q*(node p-node q)/
        (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q)*
        evalTwo (node p) (node q) A*evalTwo (node p) (node q) B) =
        (c q/Zarankiewicz.derivativeAtNode node q) *
        ∑p, evalTwo (node p) (node q) C/Zarankiewicz.derivativeAtNode node p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          rw [show evalTwo (node p) (node q) C = _ from evalTwo_difference_mul _ _ A B]
          ring
      _ = 0 := by rw [weighted_evalTwo_first_zero node hn _ C (hC 0), mul_zero]
  rw [weightedPairing_add, weightedPairing_add, hr, hcol, add_zero, add_zero]

end Paper170

end
end

section

/-! Coefficient spaces for the even-node interpolation argument. -/
noncomputable section
open scoped BigOperators
open Module
namespace Paper170

theorem rectangle_finite (a b : ℕ) : FiniteDimensional ℝ (rectangle a b) :=
  Module.Finite.of_basis (rectangleBasis a b)

theorem rectangle_dimension (a b : ℕ) :
    Module.finrank ℝ (rectangle a b) = (a+1)*(b+1) := by
  rw [Module.finrank_eq_card_basis (rectangleBasis a b)]
  simp

theorem toBiPolynomial_coeff (P : Poly2) (a b : ℕ) :
    Zarankiewicz.biCoeff (toBiPolynomial P) a b =
      P.coeff (exponentPair.symm (a,b)) := by
  rw [← Zarankiewicz.flattenBi_apply]
  change (Zarankiewicz.flattenBi (Zarankiewicz.flattenBi.symm _)) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem toBiPolynomial_monomial (m : Fin 2 →₀ ℕ) (c : ℝ) :
    toBiPolynomial (MvPolynomial.monomial m c) =
      PolynomialModule.single ℝ (m 0) (PolynomialModule.single ℝ (m 1) c) := by
  apply Zarankiewicz.bi_ext
  intro a b
  rw [toBiPolynomial_coeff]
  simp only [MvPolynomial.coeff_monomial, Zarankiewicz.biCoeff,
    PolynomialModule.coeff_single, Finsupp.single_apply]
  by_cases hm : m = exponentPair.symm (a,b)
  · subst m
    simp
  · have hne : m 0 ≠ a ∨ m 1 ≠ b := by
      by_contra h
      simp only [not_or, not_not] at h
      apply hm
      apply exponentPair.injective
      exact Prod.ext h.1 h.2
    rcases hne with h | h
    · simp [hm, h]
    · by_cases ha : m 0 = a <;> simp [hm, h, ha]

theorem toBiPolynomial_eval (P : Poly2) (u v : ℝ) :
    Zarankiewicz.biEval u v (toBiPolynomial P) = evalTwo u v P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial m c =>
    rw [toBiPolynomial_monomial]
    simp only [Zarankiewicz.biEval, LinearMap.comp_apply, PolynomialModule.eval_single,
      map_smul, smul_eq_mul]
    simp only [evalTwo, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_two]
      ring
    · intro i
      simp

theorem toBiPolynomial_bounded (a b : ℕ) (P : Poly2) (hP : P ∈ rectangle a b) :
    Zarankiewicz.BiBounded (a+1) (b+1) (toBiPolynomial P) := by
  obtain ⟨ha,hb⟩ := (rectangle_membership a b P).mp hP
  constructor
  · intro k hk
    apply PolynomialModule.ext
    apply Finsupp.ext
    intro j
    change Zarankiewicz.biCoeff (toBiPolynomial P) k j = 0
    rw [toBiPolynomial_coeff]
    by_contra h
    have := MvPolynomial.degreeOf_le_iff.mp ha _ (MvPolynomial.mem_support_iff.mpr h)
    simp only [exponentPair_symm_zero] at this
    omega
  · intro k j hj
    change Zarankiewicz.biCoeff (toBiPolynomial P) k j = 0
    rw [toBiPolynomial_coeff]
    by_contra h
    have := MvPolynomial.degreeOf_le_iff.mp hb _ (MvPolynomial.mem_support_iff.mpr h)
    simp only [exponentPair_symm_one] at this
    omega

end Paper170

end
end

section

/-! Polynomial cycle tests and the span of products of bounded-degree polynomials. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem polynomialTestLinear_apply {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n) (P : Poly4) :
    polynomialTestLinear node J P = polynomialTest node J P := by
  simp [polynomialTestLinear, polynomialTest]

theorem evalFour_monomial (x u y v : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    evalFour x u y v (MvPolynomial.monomial m c) = c * (x^m 0 * u^m 1 * y^m 2 * v^m 3) := by
  simp only [evalFour, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four]
  · intro i
    simp

theorem polynomialTest_monomial {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (m : Fin 4 →₀ ℕ) (c : ℝ) :
    polynomialTest node J (MvPolynomial.monomial m c) = c *
      chainPairing J (weightedChain node (m 0) (m 1)) (weightedChain node (m 2) (m 3)) := by
  simp only [polynomialTest, evalFour_monomial, chainPairing, Finset.mul_sum, weightedChain]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem polynomial_cycle_tests {n : ℕ} (hn : 2 ≤ n) (node : Fin n → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor n)
    (hcycles : ∀ z z' : Fin n → Fin n → ℝ,
      (∀ v, chainBoundary z v = 0) → (∀ v, chainBoundary z' v = 0) →
        chainPairing J z z' = 0)
    (H : Poly4) (hH : H ∈ box4 (n-2)) : polynomialTest node J H = 0 := by
  rw [← polynomialTestLinear_apply, H.as_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [polynomialTestLinear_apply, polynomialTest_monomial]
  have hb (i : Fin 4) : m i + 1 < n := by
    have := MvPolynomial.degreeOf_le_iff.mp ((box4_membership (n-2) H).mp hH i) m hm
    omega
  rw [hcycles _ _ (weighted_chain_boundary node hnode _ _ (hb 0) (hb 1))
    (weighted_chain_boundary node hnode _ _ (hb 2) (hb 3)), mul_zero]

theorem products_span_degree (s : ℕ) :
    Submodule.span ℝ {P : Polynomial ℝ | ∃ U V : Polynomial ℝ,
      U.natDegree ≤ s ∧ V.natDegree ≤ s ∧ P = U * V} = Polynomial.degreeLT ℝ (2*s+1) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro P ⟨U,V,hU,hV,rfl⟩
    change U * V ∈ Polynomial.degreeLT ℝ (2*s+1)
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have := Polynomial.natDegree_mul_le_of_le hU hV
    omega
  · rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
    intro P hP
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hP
    have hk : k ≤ 2*s := by rw [Finset.mem_range] at hk; omega
    apply Submodule.subset_span
    refine ⟨Polynomial.X ^ min k s, Polynomial.X ^ (k-min k s), ?_, ?_, ?_⟩
    · simp only [Polynomial.natDegree_X_pow]
      exact min_le_right _ _
    · simp only [Polynomial.natDegree_X_pow]
      omega
    · rw [← pow_add, Nat.add_sub_of_le (min_le_left k s)]

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_PairSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric double and quadruple sums over unordered pairs. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

theorem upperPairSum_mul {α : Type*} [Fintype α] [LinearOrder α]
    (r : ℝ) (f : α → α → ℝ) :
    upperPairSum (fun i p => r * f i p) = r * upperPairSum f := by
  simp only [upperPairSum, Finset.mul_sum, mul_ite, mul_zero]

theorem sum_symmetric_pair {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → ℝ) (hsym : ∀ i p, f p i = f i p) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ p, f i p) = 2 * upperPairSum f := by
  have hpoint (i p : α) : f i p =
      (if i < p then f i p else 0) + (if p < i then f i p else 0) := by
    rcases lt_trichotomy i p with h | rfl | h
    · simp [h, not_lt_of_ge h.le]
    · simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  have hsum : (∑ i, ∑ p, f i p) =
      upperPairSum f + ∑ i, ∑ p, if p < i then f i p else 0 := by
    calc
      _ = ∑ i, ∑ p, ((if i < p then f i p else 0) +
          (if p < i then f i p else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro p _
        exact hpoint i p
      _ = _ := by simp only [upperPairSum, Finset.sum_add_distrib]
  rw [hsum, Finset.sum_comm]
  have he : (∑ p, ∑ i, if p < i then f i p else 0) = upperPairSum f := by
    unfold upperPairSum
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym]
  rw [he]
  ring

theorem sum_symmetric_quad {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → α → α → ℝ)
    (hfirst : ∀ i p k q, f p i k q = f i p k q)
    (hsecond : ∀ i p k q, f i p q k = f i p k q)
    (hdiag₁ : ∀ i k q, f i i k q = 0) (hdiag₂ : ∀ i p k, f i p k k = 0) :
    (∑ i, ∑ p, ∑ k, ∑ q, f i p k q) =
      4 * upperPairSum (fun i p => upperPairSum (f i p)) := by
  have hs (i p : α) : (∑ k, ∑ q, f p i k q) = ∑ k, ∑ q, f i p k q := by
    simp only [hfirst]
  have hd (i : α) : (∑ k, ∑ q, f i i k q) = 0 := by simp [hdiag₁]
  rw [sum_symmetric_pair _ hs hd]
  have he : (fun i p => ∑ k, ∑ q, f i p k q) =
      (fun i p => 2 * upperPairSum (f i p)) := by
    funext i p
    exact sum_symmetric_pair _ (hsecond i p) (hdiag₂ i p)
  rw [he, upperPairSum_mul]
  ring

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Polynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate symmetry, polynomial quotients, collision divisibility, and specialization. -/

section

noncomputable section
open MvPolynomial
namespace Paper170

lemma substitution_difference_dvd {σ : Type*} (f : MvPolynomial σ ℝ)
    (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ)
    (hX : ∀ i, f ∣ X i - φ (X i)) (P : MvPolynomial σ ℝ) : f ∣ P - φ P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    have h := dvd_add hP hQ
    simpa only [map_add, sub_add_sub_comm] using h
  | mul_X P i hP =>
    have h := dvd_add (dvd_mul_of_dvd_left hP (X i))
      (dvd_mul_of_dvd_right (hX i) (φ P))
    convert h using 1
    rw [map_mul]
    ring

theorem diagonal_vanishing_iff_divisible (P : Poly4) :
    diagonalSpecialization P = 0 ↔ (X 0 - X 2 : Poly4) ∣ P := by
  let φ : Poly4 →ₐ[ℝ] Poly4 := reinsertDiagonal.comp diagonalSpecialization
  have hX : ∀ i, (X 0 - X 2 : Poly4) ∣ X i - φ (X i) := by
    intro i
    fin_cases i <;> simp [φ, reinsertDiagonal, diagonalSpecialization,
      Matrix.cons_val_two, Matrix.cons_val_three]
    exact ⟨-1, by ring⟩
  constructor
  · intro hP
    have h := substitution_difference_dvd (X 0 - X 2) φ hX P
    simpa [φ, hP] using h
  · rintro ⟨Q, rfl⟩
    simp [diagonalSpecialization, Matrix.cons_val_two]

end Paper170

end
end

section

noncomputable section
open MvPolynomial
namespace Paper170

lemma difference_coefficient (i j : Fin 4) (hij : i ≠ j) :
    (X i - X j : Poly4).coeff (Finsupp.single i 1) = 1 := by
  simp [coeff_X, Finsupp.single_left_inj, Ne.symm hij]

lemma difference_degree (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    (X i - X j : Poly4).degreeOf k = if k = i ∨ k = j then 1 else 0 := by
  have hupper := degreeOf_sub_le k (X i : Poly4) (X j)
  simp only [degreeOf_X] at hupper
  by_cases hki : k = i
  · subst k
    rw [ite_eq_left (Or.inl rfl)]
    apply Nat.le_antisymm
    · simpa [hij] using hupper
    · have hm : Finsupp.single i 1 ∈ (X i - X j : Poly4).support :=
        mem_support_iff.mpr (by rw [difference_coefficient i j hij]; norm_num)
      simpa using monomial_le_degreeOf i hm
  · by_cases hkj : k = j
    · subst k
      rw [ite_eq_left (Or.inr rfl)]
      apply Nat.le_antisymm
      · simpa [hki] using hupper
      · have hc : (X i - X j : Poly4).coeff (Finsupp.single j 1) = -1 := by
          simp [coeff_X, Finsupp.single_left_inj, hij]
        have hm : Finsupp.single j 1 ∈ (X i - X j : Poly4).support :=
          mem_support_iff.mpr (by rw [hc]; norm_num)
        simpa using monomial_le_degreeOf j hm
    · rw [ite_eq_right (not_or.mpr ⟨hki, hkj⟩)]
      exact Nat.eq_zero_of_le_zero (by simpa [hki, hkj] using hupper)

theorem difference_prime (i j : Fin 4) (hij : i ≠ j) :
    Prime (X i - X j : Poly4) := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  apply irreducible_of_totalDegree_eq_one
  · apply Nat.le_antisymm
    · simpa using totalDegree_sub (X i : Poly4) (X j)
    · have h := degreeOf_le_totalDegree (X i - X j : Poly4) i
      simpa [difference_degree i j hij] using h
  · intro r hr
    apply isUnit_of_dvd_one
    simpa only [difference_coefficient i j hij] using hr (Finsupp.single i 1)

theorem collision_factors_nonassociate :
    Pairwise (fun i j : Fin 4 => ¬ Associated (collisionFactors i) (collisionFactors j)) := by
  let w : Fin 4 → Fin 4 → ℝ := ![![0, 1, 0, 2], ![0, 1, 2, 0],
    ![1, 0, 0, 2], ![1, 0, 2, 0]]
  intro i j hij ha
  have hi : eval (w i) (collisionFactors i) = 0 := by
    fin_cases i <;> norm_num [w, collisionFactors, Matrix.cons_val_two, Matrix.cons_val_three]
  have hj : eval (w i) (collisionFactors j) ≠ 0 := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | norm_num [w, collisionFactors,
      Matrix.cons_val_two, Matrix.cons_val_three]
  obtain ⟨Q, hQ⟩ := ha.dvd
  have h := congrArg (eval (w i)) hQ
  simp only [eval_mul, hi, zero_mul] at h
  exact hj h

theorem collision_factor_properties :
    collisionFactor ≠ 0 ∧ swapFirstPair collisionFactor = collisionFactor ∧
      swapSecondPair collisionFactor = collisionFactor ∧
      ∀ i : Fin 4, collisionFactor.degreeOf i = 2 := by
  have h02 := (difference_prime 0 2 (by decide)).ne_zero
  have h03 := (difference_prime 0 3 (by decide)).ne_zero
  have h12 := (difference_prime 1 2 (by decide)).ne_zero
  have h13 := (difference_prime 1 3 (by decide)).ne_zero
  refine ⟨mul_ne_zero (mul_ne_zero (mul_ne_zero h02 h03) h12) h13, ?_, ?_, ?_⟩
  · norm_num [collisionFactor, swapFirstPair, Equiv.swap_apply_def, Fin.ext_iff]
    ring
  · norm_num [collisionFactor, swapSecondPair, Equiv.swap_apply_def, Fin.ext_iff]
    ring
  · intro i
    rw [collisionFactor, degreeOf_mul_eq (mul_ne_zero (mul_ne_zero h02 h03) h12) h13,
      degreeOf_mul_eq (mul_ne_zero h02 h03) h12, degreeOf_mul_eq h02 h03]
    fin_cases i <;> norm_num [difference_degree, Fin.ext_iff, show (0 : Fin 4) ≠ 2 by decide,
      show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
      show (1 : Fin 4) ≠ 3 by decide]

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open Module MvPolynomial
namespace Paper170

lemma box_finite (d : ℕ) : FiniteDimensional ℝ (box4 d) :=
  Module.Finite.of_basis (boxBasis d)

theorem symmetric_space_finite (s : ℕ) :
    FiniteDimensional ℝ (endpointSymmetricSpace s) := by
  let := box_finite (s - 2)
  let f : endpointSymmetricSpace s →ₗ[ℝ] box4 (s - 2) :=
    Submodule.inclusion (inf_le_left.trans inf_le_left)
  exact FiniteDimensional.of_injective f (Submodule.inclusion_injective _)

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem collision_quotient (s : ℕ) (_hs : 2 ≤ s) (P : Poly4)
    (hP : P ∈ endpointSymmetricSpace s) (hP0 : P ≠ 0) (hdiv : collisionFactor ∣ P) :
    ∃ Q : Poly4, Q ≠ 0 ∧ P = collisionFactor * Q ∧
      Q ∈ endpointSymmetricSpace s ∧
      (∀ i : Fin 4, Q.degreeOf i + 2 = P.degreeOf i) ∧
      Q.degreeOf 0 < P.degreeOf 0 := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hP0
    simp [h, hQ]
  rcases collision_factor_properties with ⟨hc, hc1, hc2, hcd⟩
  rcases (symmetric_space_membership s P).mp hP with ⟨hpdeg, hp1, hp2⟩
  have hdeg (i : Fin 4) : Q.degreeOf i + 2 = P.degreeOf i := by
    rw [hQ, MvPolynomial.degreeOf_mul_eq hc hQ0, hcd, add_comm]
  have hfirst : swapFirstPair Q = Q := by
    apply mul_left_cancel₀ hc
    calc
      collisionFactor * swapFirstPair Q = swapFirstPair (collisionFactor * Q) := by
        rw [swapFirstPair_mul, hc1]
      _ = collisionFactor * Q := by rw [← hQ, hp1, hQ]
  have hsecond : swapSecondPair Q = Q := by
    apply mul_left_cancel₀ hc
    calc
      collisionFactor * swapSecondPair Q = swapSecondPair (collisionFactor * Q) := by
        rw [swapSecondPair_mul, hc2]
      _ = collisionFactor * Q := by rw [← hQ, hp2, hQ]
  refine ⟨Q, hQ0, hQ, (symmetric_space_membership s Q).mpr ⟨?_, hfirst, hsecond⟩,
    hdeg, ?_⟩
  · intro i
    have := hdeg i
    have := hpdeg i
    omega
  · have := hdeg 0
    omega

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

lemma diagonalUnivariate_monomial (u v : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    diagonalUnivariate u v (monomial m c) =
      Polynomial.C (c * u ^ m 1 * v ^ m 3) * Polynomial.X ^ (m 0 + m 2) := by
  simp only [diagonalUnivariate, MvPolynomial.aeval_monomial,
    Polynomial.algebraMap_apply]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four, pow_add]
    ring
  · intro i
    simp

lemma diagonalUnivariate_bound (s : ℕ) (P : endpointSymmetricSpace s) (u v : ℝ) :
    (diagonalUnivariate u v P.val).natDegree ≤ 2 * (s - 2) := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).1
  rw [P.val.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [diagonalUnivariate_monomial]
  have h0 := degreeOf_le_iff.mp (hp 0) m hm
  have h2 := degreeOf_le_iff.mp (hp 2) m hm
  calc
    (Polynomial.C (P.val.coeff m * u ^ m 1 * v ^ m 3) *
      Polynomial.X ^ (m 0 + m 2)).natDegree ≤ m 0 + m 2 := by
        simpa using Polynomial.natDegree_C_mul_le (P.val.coeff m * u ^ m 1 * v ^ m 3)
          (Polynomial.X ^ (m 0 + m 2) : Polynomial ℝ)
    _ ≤ 2 * (s - 2) := by omega

lemma diagonalUnivariate_eval (u v x : ℝ) (P : Poly4) :
    (diagonalUnivariate u v P).eval x = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalUnivariate, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul, Polynomial.eval_mul]
    rw [hP]
    fin_cases i <;> simp [diagonalUnivariate, evalFour, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma diagonal_eval (P : Poly4) (x u v : ℝ) :
    MvPolynomial.eval ![x, u, v] (diagonalSpecialization P) = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [diagonalSpecialization, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [diagonalSpecialization, evalFour, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma vertex_eval (P : Poly4) (x u v : ℝ) :
    evalTwo u v (vertexSpecialization x P) = evalFour x u x v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [vertexSpecialization, evalFour, evalTwo]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    change MvPolynomial.aeval ![u, v] _ = MvPolynomial.aeval ![x, u, x, v] _
    change MvPolynomial.aeval ![u, v] _ = MvPolynomial.aeval ![x, u, x, v] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [vertexSpecialization, Matrix.cons_val_two,
      Matrix.cons_val_three]

lemma diagonal_zero_of_vertices (s : ℕ) (node : Fin (2 * s + 1) → ℝ)
    (hn : Function.Injective node) (P : endpointSymmetricSpace s)
    (hP : ∀ i, vertexSpecialization (node i) P.val = 0) :
    diagonalSpecialization P.val = 0 := by
  have hpoly (u v : ℝ) : diagonalUnivariate u v P.val = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hn
    · intro i
      rw [diagonalUnivariate_eval, ← vertex_eval, hP, map_zero]
    · have h := diagonalUnivariate_bound s P u v
      simp only [Fintype.card_fin]
      omega
  apply MvPolynomial.funext
  intro t
  have ht : t = ![t 0, t 1, t 2] := by ext i; fin_cases i <;> rfl
  rw [ht, diagonal_eval, ← diagonalUnivariate_eval, hpoly]
  simp

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem symmetric_space_dimension (s : ℕ) (hs : 2 ≤ s) :
    Module.finrank ℝ (endpointSymmetricSpace s) = (Nat.choose s 2) ^ 2 := by
  rw [(symmetricCoordinatesEquiv s).finrank_eq, Module.finrank_pi]
  simp only [SymmetricCoordinate, Fintype.card_prod, Sym2.card, Fintype.card_fin]
  have he : s - 2 + 1 + 1 = s := by omega
  rw [he]
  ring

end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

lemma collisionFactors_prime (i : Fin 4) : Prime (collisionFactors i) := by
  fin_cases i <;> exact difference_prime _ _ (by decide)

lemma collisionFactors_coprime :
    Pairwise (fun i j : Fin 4 => IsRelPrime (collisionFactors i) (collisionFactors j)) := by
  intro i j hij
  rw [(collisionFactors_prime i).irreducible.isRelPrime_iff_not_dvd,
    (collisionFactors_prime i).dvd_prime_iff_associated (collisionFactors_prime j)]
  exact collision_factors_nonassociate hij

lemma collision_divides_of_diagonal_vanishing (s : ℕ) (P : endpointSymmetricSpace s)
    (hP : diagonalSpecialization P.val = 0) : collisionFactor ∣ P.val := by
  have h02 := (diagonal_vanishing_iff_divisible P.val).mp hP
  rcases (symmetric_space_membership s P.val).mp P.property with ⟨_, hp1, hp2⟩
  have h03 : (X 0 - X 3 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h02
    refine ⟨swapSecondPair Q, ?_⟩
    have h := congrArg swapSecondPair hQ
    rw [hp2, swapSecondPair_mul] at h
    simpa [swapSecondPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have h12 : (X 1 - X 2 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h02
    refine ⟨swapFirstPair Q, ?_⟩
    have h := congrArg swapFirstPair hQ
    rw [hp1, swapFirstPair_mul] at h
    simpa [swapFirstPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have h13 : (X 1 - X 3 : Poly4) ∣ P.val := by
    obtain ⟨Q, hQ⟩ := h03
    refine ⟨swapFirstPair Q, ?_⟩
    have h := congrArg swapFirstPair hQ
    rw [hp1, swapFirstPair_mul] at h
    simpa [swapFirstPair, Equiv.swap_apply_def,
      Fin.ext_iff] using h
  have hdvd (i : Fin 4) : collisionFactors i ∣ P.val := by
    fin_cases i
    · exact h02
    · exact h03
    · exact h12
    · exact h13
  have h := Finset.prod_dvd_of_isRelPrime
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) j _ hij =>
      collisionFactors_coprime hij) (fun i _ => hdvd i)
  simpa [Fin.prod_univ_four, collisionFactors, collisionFactor,
    Matrix.cons_val_two, Matrix.cons_val_three] using h

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The support form, injectivity criterion, and support-space dimension. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem collision_nonzero_on_support {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) (a : SupportCoord J) :
    evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1) (node a.val.2.2)
      collisionFactor ≠ 0 := by
  rcases (Finset.mem_filter.mp a.property).2 with ⟨_, _, h02, h03, h12, h13, _⟩
  simpa [evalFour, collisionFactor, Matrix.cons_val_two, Matrix.cons_val_three] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hn.ne h02))
      (sub_ne_zero.mpr (hn.ne h03))) (sub_ne_zero.mpr (hn.ne h12)))
      (sub_ne_zero.mpr (hn.ne h13))

lemma support_diagonal_nonzero {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) (a : SupportCoord J) :
    supportDiagonal node J a ≠ 0 := by
  rcases (Finset.mem_filter.mp a.property).2 with ⟨h01, h23, _, _, _, _, hJ⟩
  have hc := collision_nonzero_on_support node hn J a
  have hf : evalFour (node a.val.1.1) (node a.val.1.2) (node a.val.2.1)
      (node a.val.2.2) fullDifference ≠ 0 := by
    simpa [fullDifference, evalFour, Matrix.cons_val_two, Matrix.cons_val_three] using
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hn.ne (ne_of_lt h01)))
        (sub_ne_zero.mpr (hn.ne (ne_of_lt h23)))) hc
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hJ
    (weight_nonzero node hn _)) (weight_nonzero node hn _))
      (weight_nonzero node hn _)) (weight_nonzero node hn _)) hf

theorem support_bilinear_nondegenerate {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n) :
    (supportBilinear node J).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => support_diagonal_nonzero node hn J a

theorem isotropic_dimension {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℝ (ι → ℝ)) (hB : B.Nondegenerate)
    (W : Submodule ℝ (ι → ℝ)) (hW : W ≤ B.orthogonal W) :
    2 * Module.finrank ℝ W ≤ Fintype.card ι := by
  have hle := Submodule.finrank_mono hW
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at hle
  have hdim := Submodule.finrank_le W
  have hv : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by simp
  rw [hv] at hle hdim
  omega

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma support_evaluation_injective_of_collision {n s : ℕ} (hs : 2 ≤ s)
    (node : Fin n → ℝ) (hn : Function.Injective node) (J : CrossingTensor n)
    (hdiv : ∀ P : endpointSymmetricSpace s,
      supportEvaluation s node J P = 0 → collisionFactor ∣ P.val) :
    Function.Injective (supportEvaluation s node J) := by
  have hzero : ∀ d (P : endpointSymmetricSpace s), P.val.degreeOf 0 = d →
      supportEvaluation s node J P = 0 → P.val = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hd hP
      by_contra hP0
      obtain ⟨Q, hQ0, heq, hQmem, _, hQdeg⟩ := collision_quotient s hs P.val
        P.property hP0 (hdiv P hP)
      have hQ : supportEvaluation s node J ⟨Q, hQmem⟩ = 0 := by
        funext a
        have hp := congrFun hP a
        change evalFour (node a.val.1.1) (node a.val.1.2)
          (node a.val.2.1) (node a.val.2.2) P.val = 0 at hp
        rw [heq, evalFour_mul] at hp
        exact (mul_eq_zero.mp hp).resolve_left (collision_nonzero_on_support node hn J a)
      exact hQ0 (ih (Q.degreeOf 0) (by omega) ⟨Q, hQmem⟩ rfl hQ)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  exact Subtype.ext (hzero _ P rfl hP)

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma support_cardinality_of_injective_isotropic {n s : ℕ} (hs : 2 ≤ s)
    (node : Fin n → ℝ) (hn : Function.Injective node) (J : CrossingTensor n)
    (hi : Function.Injective (supportEvaluation s node J))
    (ho : ∀ P Q : endpointSymmetricSpace s,
      supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) = 0) :
    2 * (Nat.choose s 2) ^ 2 ≤ (supportedPairs J).card := by
  let := symmetric_space_finite s
  let f := supportEvaluation s node J
  have hr : f.range ≤ (supportBilinear node J).orthogonal f.range := by
    rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
    exact ho Q P
  have hd := isotropic_dimension (supportBilinear node J)
    (support_bilinear_nondegenerate node hn J) f.range hr
  have he : Module.finrank ℝ f.range = Module.finrank ℝ (endpointSymmetricSpace s) :=
    (LinearEquiv.ofInjective f hi).finrank_eq.symm
  rw [he, symmetric_space_dimension s hs, Fintype.card_coe] at hd
  exact hd

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Isotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isotropic evaluation image and order-pairing identities. -/

section

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace Paper170

theorem evalFour_swap_first (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapFirstPair P) = evalFour u x y v P := by
  change aeval ![x, u, y, v] (rename (Equiv.swap (0 : Fin 4) 1) P) = aeval ![u, x, y, v] P
  rw [aeval_rename]
  congr 2
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

theorem evalFour_swap_second (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapSecondPair P) = evalFour x u v y P := by
  change aeval ![x, u, y, v] (rename (Equiv.swap (2 : Fin 4) 3) P) = aeval ![x, u, v, y] P
  rw [aeval_rename]
  congr 2
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

theorem evalFour_fullDifference (x u y v : ℝ) :
    evalFour x u y v fullDifference =
      (x - u) * (y - v) * (x - y) * (x - v) * (u - y) * (u - v) := by
  simp [evalFour, fullDifference, collisionFactor]
  ring

theorem isotropicTerm_first {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hJ : ∀ i p k q, J p i k q = -J i p k q) (P Q : endpointSymmetricSpace s)
    (i p k q : Fin n) :
    isotropicTerm node J P.val Q.val p i k q = isotropicTerm node J P.val Q.val i p k q := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.1
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).2.1
  have hep := evalFour_swap_first P.val (node i) (node p) (node k) (node q)
  have heq := evalFour_swap_first Q.val (node i) (node p) (node k) (node q)
  rw [hp] at hep
  rw [hq] at heq
  unfold isotropicTerm
  rw [hJ i p k q, ← hep, ← heq]
  simp only [evalFour_fullDifference]
  ring

theorem isotropicTerm_second {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hJ : ∀ i p k q, J i p q k = -J i p k q) (P Q : endpointSymmetricSpace s)
    (i p k q : Fin n) :
    isotropicTerm node J P.val Q.val i p q k = isotropicTerm node J P.val Q.val i p k q := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).2.2
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).2.2
  have hep := evalFour_swap_second P.val (node i) (node p) (node k) (node q)
  have heq := evalFour_swap_second Q.val (node i) (node p) (node k) (node q)
  rw [hp] at hep
  rw [hq] at heq
  unfold isotropicTerm
  rw [hJ i p k q, ← hep, ← heq]
  simp only [evalFour_fullDifference]
  ring

theorem isotropicTerm_vanish {n : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (P Q : Poly4) (i p k q : Fin n)
    (h : i = p ∨ k = q ∨ i = k ∨ i = q ∨ p = k ∨ p = q ∨ J i p k q = 0) :
    isotropicTerm node J P Q i p k q = 0 := by
  rcases h with h | h | h | h | h | h | h <;>
    simp [isotropicTerm, evalFour_fullDifference, h]

theorem support_sum_eq_upper {n : ℕ} (J : CrossingTensor n)
    (f : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hzero : ∀ i p k q, i = k ∨ i = q ∨ p = k ∨ p = q ∨ J i p k q = 0 → f i p k q = 0) :
    (∑ a : SupportCoord J, f a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2) =
      upperPairSum (fun i p => upperPairSum (f i p)) := by
  let F (a : (Fin n × Fin n) × (Fin n × Fin n)) := f a.1.1 a.1.2 a.2.1 a.2.2
  change (∑ a : SupportCoord J, F a.val) = _
  rw [Finset.sum_coe_sort (supportedPairs J) F]
  simp only [supportedPairs, Finset.sum_filter, Fintype.sum_prod_type, upperPairSum, F]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  by_cases hip : i < p
  · simp only [hip, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    by_cases hkq : k < q
    · simp only [hkq, true_and, ite_true]
      by_cases hgood : i ≠ k ∧ i ≠ q ∧ p ≠ k ∧ p ≠ q ∧ J i p k q ≠ 0
      · simp [hgood]
      · have hz : f i p k q = 0 := hzero i p k q (by tauto)
        simp [hz]
    · simp [hkq]
  · simp [hip]

theorem supportBilinear_eq_isotropicSum {n s : ℕ} (node : Fin n → ℝ)
    (J : CrossingTensor n) (P Q : endpointSymmetricSpace s) :
    supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) =
      upperPairSum (fun i p => upperPairSum (isotropicTerm node J P.val Q.val i p)) := by
  calc
    _ = ∑ a : SupportCoord J, isotropicTerm node J P.val Q.val
        a.val.1.1 a.val.1.2 a.val.2.1 a.val.2.2 := by
      simp only [supportBilinear, Matrix.toBilin'_apply, Matrix.diagonal_apply,
        mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      apply Finset.sum_congr rfl
      intro a _
      change evalFour _ _ _ _ P.val * supportDiagonal node J a * evalFour _ _ _ _ Q.val = _
      unfold supportDiagonal isotropicTerm
      ring
    _ = _ := support_sum_eq_upper J _ (fun i p k q h =>
      isotropicTerm_vanish node J P.val Q.val i p k q (Or.inr (Or.inr h)))

theorem isotropic_test_degree {s : ℕ} (hs : 2 ≤ s) (P Q : endpointSymmetricSpace s) :
    P.val * Q.val * fullDifference ∈ box4 (2 * s - 1) := by
  apply (box4_membership _ _).mpr
  intro i
  have hΔ : fullDifference.degreeOf i ≤ 3 := by
    have h := degreeOf_mul_bound
      (degreeOf_mul_bound (degreeOf_difference_bound 0 1 i) (degreeOf_difference_bound 2 3 i))
      (le_of_eq (collision_factor_properties.2.2.2 i))
    fin_cases i <;> norm_num [fullDifference] at h ⊢ <;> exact h
  have hp := ((symmetric_space_membership s P.val).mp P.property).1 i
  have hq := ((symmetric_space_membership s Q.val).mp Q.property).1 i
  exact (degreeOf_mul_bound (degreeOf_mul_bound hp hq) hΔ).trans (by omega)

theorem polynomialTest_isotropic {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hfirst : ∀ i p k q, J p i k q = -J i p k q)
    (hsecond : ∀ i p k q, J i p q k = -J i p k q)
    (P Q : endpointSymmetricSpace s) :
    polynomialTest node J (P.val * Q.val * fullDifference) =
      4 * supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) := by
  rw [supportBilinear_eq_isotropicSum]
  have hterm : polynomialTest node J (P.val * Q.val * fullDifference) =
      ∑ i, ∑ p, ∑ k, ∑ q, isotropicTerm node J P.val Q.val i p k q := by
    unfold polynomialTest
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    rw [evalFour_mul, evalFour_mul]
    unfold isotropicTerm
    ring
  rw [hterm]
  exact sum_symmetric_quad _ (isotropicTerm_first node J hfirst P Q)
    (isotropicTerm_second node J hsecond P Q)
    (fun i k q => isotropicTerm_vanish node J P.val Q.val i i k q (Or.inl rfl))
    (fun i p k => isotropicTerm_vanish node J P.val Q.val i p k k (Or.inr (Or.inl rfl)))

theorem evaluation_image_isotropic {s : ℕ} (hs : 2 ≤ s) (node : Fin (2 * s + 1) → ℝ)
    (_hnode : Function.Injective node) (J : CrossingTensor (2 * s + 1))
    (_orders : ∀ i : Fin (2 * s + 1), LinearOrder {j : Fin (2 * s + 1) // j ≠ i})
    (_hloopLeft : ∀ i k q, J i i k q = 0)
    (_hloopRight : ∀ i p k, J i p k k = 0)
    (hreverseLeft : ∀ i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀ i p k q, J i p q k = -J i p k q)
    (_hskew : ∀ i p k q, J k q i p = -J i p k q)
    (_hlocal : ∀ i (p q : {j : Fin (2 * s + 1) // j ≠ i}),
      J i p.val i q.val = halfOrder (_orders i) p q)
    (htests : ∀ H ∈ box4 (2 * s - 1), polynomialTest node J H = 0)
    (P Q : endpointSymmetricSpace s) :
    supportBilinear node J (supportEvaluation s node J P) (supportEvaluation s node J Q) = 0 := by
  have h := htests _ (isotropic_test_degree hs P Q)
  rw [polynomialTest_isotropic node J hreverseLeft hreverseRight P Q] at h
  linarith

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Triangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even triangular interpolation and unisolvence. -/

section

/-! The even two-triangle set, as actual ordered interpolation coordinates. -/
noncomputable section
namespace Paper170

theorem even_triangle_card (s : ℕ) : (evenTriangle s).card = s*(s-1) := by
  have hc := Fintype.card_congr (evenTriangleOffDiagEquiv s)
  simp only [EvenTriangleCoord, Fintype.card_coe] at hc
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hc
  simpa only [Nat.mul_sub_left_distrib, mul_one] using hc

end Paper170

end
end

section

/-! Even-node interpolation by adjoining one fresh node to the checked odd-node theorem. -/
noncomputable section
open PolynomialModule
open Zarankiewicz
namespace Paper170

theorem biBounded_mulRoot {r s : ℕ} {P : BiPoly} (hP : BiBounded r s P) (t : ℝ) :
    BiBounded (r+1) s (mulRoot t P) := by
  refine ⟨bounded_mulRoot t hP.1, ?_⟩
  intro a
  cases a with
  | zero =>
    rw [mulRoot_coeff_zero]
    exact (boundedSpace s).smul_mem _ (hP.2 0)
  | succ a =>
    rw [mulRoot_coeff_succ]
    exact bounded_sub (hP.2 a) ((boundedSpace s).smul_mem _ (hP.2 (a+1)))

theorem insertNode_injective {n : ℕ} (r : Fin (n+1)) (node : Fin n → ℝ)
    (hn : Function.Injective node) (t : ℝ) (ht : ∀i, node i ≠ t) :
    Function.Injective (Fin.insertNth r t node) := by
  intro a b
  refine Fin.succAboveCases r ?_ (fun a => ?_) a
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · intro
      rfl
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro h
      exact (ht b h.symm).elim
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro h
      exact (ht a h).elim
    · simp only [Fin.insertNth_apply_succAbove]
      intro h
      exact congrArg r.succAbove (hn h)

theorem oddTriangle_unisolvent_fin (s : ℕ) (node : Fin (2*s+1) → ℝ)
    (hn : Function.Injective node) (P : BiPoly) (hP : BiBounded s s P)
    (hv : ∀a b : Fin (2*s+1),
      (b < a ∧ a.val ≤ s) ∨ (s < a.val ∧ a < b) → biEval (node a) (node b) P = 0) :
    P = 0 := by
  let x : ℕ → ℝ := fun k => if h : 1 ≤ k ∧ k ≤ 2*s+1 then node ⟨k-1,by omega⟩ else 0
  have hx : Set.InjOn x (Set.Icc 1 (2*s+1)) := by
    intro a ha b hb he
    simp only [Set.mem_Icc] at ha hb
    simp only [x, dite_eq_left ha, dite_eq_left hb] at he
    have := congrArg Fin.val (hn he)
    dsimp at this
    omega
  apply twoTriangle_unisolvent s x hx P hP
  intro a b hab
  rw [mem_twoTriangle] at hab
  have ha : 1 ≤ a ∧ a ≤ 2*s+1 := by omega
  have hb : 1 ≤ b ∧ b ≤ 2*s+1 := by omega
  simp only [x, dite_eq_left ha, dite_eq_left hb]
  apply hv
  change (b-1 < a-1 ∧ a-1 ≤ s) ∨ (s < a-1 ∧ a-1 < b-1)
  omega

theorem evenTriangle_unisolvent_first (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded s (s-1) P)
    (hv : ∀a b, (a,b) ∈ evenTriangle s → biEval (node a) (node b) P = 0) : P = 0 := by
  obtain ⟨t,ht⟩ := (Set.finite_range node).exists_notMem
  have hnt : ∀i, node i ≠ t := fun i h => ht ⟨i,h⟩
  let x : Fin (2*s+1) → ℝ := Fin.insertNth (0 : Fin (2*s+1)) t node
  let Q := swapBi (mulRoot t (swapBi P))
  have hQ : BiBounded s s Q := by
    have hb := biBounded_swap (biBounded_mulRoot (biBounded_swap hP) t)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using hb
  have hev (u v : ℝ) : biEval u v Q = (v-t)*biEval u v P := by
    simp only [Q, biEval_swap, biEval_mulRoot]
  have hzero : Q = 0 := by
    apply oddTriangle_unisolvent_fin s x (insertNode_injective _ node hn t hnt) Q hQ
    intro a b
    refine Fin.succAboveCases (0 : Fin (2*s+1)) ?_ (fun a => ?_) a
    · intro h
      have : False := by simp only [Fin.lt_def, Fin.val_zero] at h; omega
      exact this.elim
    · refine Fin.succAboveCases (0 : Fin (2*s+1)) ?_ (fun b => ?_) b
      · intro _
        simp only [hev, x, Fin.insertNth_apply_same, sub_self, zero_mul]
      · intro hab
        simp only [x, Fin.insertNth_apply_succAbove, hev]
        rw [hv a b]
        · exact mul_zero _
        · rw [mem_evenTriangle]
          simp only [Fin.succAbove_zero, Fin.val_succ, Fin.lt_def] at hab
          simp only [Fin.lt_def]
          omega
  have hroot : mulRoot t (swapBi P) = 0 := by
    apply swapBi.injective
    simpa only [map_zero] using hzero
  have hpzero := eq_zero_of_mulRoot_eq_zero t (s-1) (swapBi P) (biBounded_swap hP).1 hroot
  apply swapBi.injective
  simpa only [map_zero] using hpzero

theorem evenTriangle_unisolvent_second (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded (s-1) s P)
    (hv : ∀a b, (a,b) ∈ evenTriangle s → biEval (node a) (node b) P = 0) : P = 0 := by
  obtain ⟨t,ht⟩ := (Set.finite_range node).exists_notMem
  have hnt : ∀i, node i ≠ t := fun i h => ht ⟨i,h⟩
  let r : Fin (2*s+1) := ⟨s,by omega⟩
  let x : Fin (2*s+1) → ℝ := Fin.insertNth r t node
  have hQ : BiBounded s s (mulRoot t P) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using biBounded_mulRoot hP t
  apply eq_zero_of_mulRoot_eq_zero t (s-1) P hP.1
  apply oddTriangle_unisolvent_fin s x (insertNode_injective r node hn t hnt) _ hQ
  intro a b
  refine Fin.succAboveCases r ?_ (fun a => ?_) a
  · intro _
    simp only [biEval_mulRoot, x, Fin.insertNth_apply_same, sub_self, zero_mul]
  · refine Fin.succAboveCases r ?_ (fun b => ?_) b
    · intro hab
      have : False := by
        simp only [Fin.lt_def, r] at hab
        omega
      exact this.elim
    · intro hab
      simp only [x, Fin.insertNth_apply_succAbove, biEval_mulRoot]
      rw [hv a b]
      · exact mul_zero _
      · rw [mem_evenTriangle]
        simp only [Fin.lt_def, r, Fin.succAbove, Fin.val_castSucc] at hab
        simp only [Fin.lt_def]
        split_ifs at hab <;> simp only [Fin.val_castSucc, Fin.val_succ] at hab <;> omega

end Paper170

end
end

section

/-! Bijective interpolation on both even-node degree rectangles. -/
noncomputable section
namespace Paper170

theorem evenTriangle_vanish_first (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P ∈ rectangle (s-1) (s-2))
    (hv : ∀a b, (a,b) ∈ evenTriangle s → evalTwo (node a) (node b) P = 0) : P = 0 := by
  apply toBiPolynomial.injective
  rw [map_zero]
  apply evenTriangle_unisolvent_first s hs node hn (toBiPolynomial P)
  · convert toBiPolynomial_bounded (s-1) (s-2) P hP using 1 <;> omega
  · intro a b hab
    rw [toBiPolynomial_eval]
    exact hv a b hab

theorem evenTriangle_vanish_second (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P ∈ rectangle (s-2) (s-1))
    (hv : ∀a b, (a,b) ∈ evenTriangle s → evalTwo (node a) (node b) P = 0) : P = 0 := by
  apply toBiPolynomial.injective
  rw [map_zero]
  apply evenTriangle_unisolvent_second s hs node hn (toBiPolynomial P)
  · convert toBiPolynomial_bounded (s-2) (s-1) P hP using 1 <;> omega
  · intro a b hab
    rw [toBiPolynomial_eval]
    exact hv a b hab

theorem triangleEvaluation_bijective_of_unisolvent (s a b : ℕ) (node : Fin (2*s) → ℝ)
    (hdim : (a+1)*(b+1) = s*(s-1))
    (hv : ∀P ∈ rectangle a b,
      (∀i j, (i,j) ∈ evenTriangle s → evalTwo (node i) (node j) P = 0) → P=0) :
    Function.Bijective (triangleEvaluation s a b node) := by
  let := rectangle_finite a b
  have hi : Function.Injective (triangleEvaluation s a b node) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    apply hv P.val P.property
    intro i j hij
    exact congrFun hP ⟨(i,j),hij⟩
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  rw [rectangle_dimension, Module.finrank_fintype_fun_eq_card]
  have hc : Fintype.card (EvenTriangleCoord s) = s*(s-1) := by
    rw [Fintype.card_coe, even_triangle_card]
  rw [hc,hdim]

theorem two_triangle_interpolation (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) :
    Function.Bijective (triangleEvaluation s (s-1) (s-2) node) ∧
      Function.Bijective (triangleEvaluation s (s-2) (s-1) node) := by
  constructor
  · apply triangleEvaluation_bijective_of_unisolvent
    · congr 1 <;> omega
    · exact evenTriangle_vanish_first s hs node hn
  · apply triangleEvaluation_bijective_of_unisolvent
    · rw [Nat.mul_comm]
      congr 1 <;> omega
    · exact evenTriangle_vanish_second s hs node hn

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_OrderPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Order-detecting interpolation and its kernel. -/

section

/-! The order pairing as a nonzero diagonal pairing on the even two-triangle set. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evenTriangleWeight_ne_zero (s : ℕ) (node : Fin (2*s) → ℝ)
    (hn : Function.Injective node) (a : EvenTriangleCoord s) : evenTriangleWeight s node a ≠ 0 := by
  have ha := (mem_evenTriangle s a.val.1 a.val.2).mp a.property
  have hne : a.val.1 ≠ a.val.2 := by rcases ha with ha | ha; exact ne_of_gt ha.2; exact ne_of_lt ha.2
  unfold evenTriangleWeight
  apply div_ne_zero
  · apply mul_ne_zero
    · split_ifs <;> norm_num
    · exact sub_ne_zero.mpr (hn.ne hne)
  · exact mul_ne_zero (Zarankiewicz.derivativeAtNode_ne_zero node hn _)
      (Zarankiewicz.derivativeAtNode_ne_zero node hn _)

theorem shifted_halfOrder (s : ℕ) (node : Fin (2*s) → ℝ) (p q : Fin (2*s)) :
    (halfOrder inferInstance p q + (if p.val < s then -(1/2) else 1/2)) * (node p-node q) =
      if (p,q) ∈ evenTriangle s then
        (if p.val < s then -1 else 1) * (node p-node q) else 0 := by
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have hqp := not_lt_of_ge (le_of_lt hpq)
    by_cases hp : p.val < s <;>
      simp [halfOrder, hpq, hqp, mem_evenTriangle, hp, not_lt.mp]
    ring
  · simp [halfOrder]
  · have hpq := not_lt_of_ge (le_of_lt hqp)
    by_cases hp : p.val < s <;>
      simp [halfOrder, hpq, hqp, mem_evenTriangle, hp, not_lt.mp]
    ring

theorem orderPairing_triangle (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) (A B : Poly2)
    (hA : A ∈ rectangle (s-1) (s-2)) (hB : B ∈ rectangle (s-2) (s-1)) :
    orderPairing node inferInstance A B = ∑ a : EvenTriangleCoord s,
      evenTriangleWeight s node a * evalTwo (node a.val.1) (node a.val.2) A *
        evalTwo (node a.val.1) (node a.val.2) B := by
  have hshift := pairing_row_column_invariant s hs (by simp) node hn (halfOrder inferInstance)
    (fun p => if p.val < s then -(1/2) else 1/2) (fun _ => 0) A B hA hB
  simp only [add_zero] at hshift
  rw [orderPairing, ← hshift]
  let F (a : Fin (2*s) × Fin (2*s)) : ℝ :=
    (if a.1.val < s then -1 else 1) * (node a.1-node a.2) /
      (Zarankiewicz.derivativeAtNode node a.1 * Zarankiewicz.derivativeAtNode node a.2) *
      evalTwo (node a.1) (node a.2) A * evalTwo (node a.1) (node a.2) B
  change _ = ∑ a : EvenTriangleCoord s, F a.val
  calc
    _ = ∑ a ∈ evenTriangle s, F a := by
      unfold weightedPairing
      simp_rw [shifted_halfOrder]
      rw [evenTriangle, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      by_cases ha : (p,q) ∈ evenTriangle s
      · have hh := (mem_evenTriangle s p q).mp ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hh, F]
      · have hh := (mem_evenTriangle s p q).not.mp ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_right hh, zero_div, zero_mul]
    _ = ∑ a : EvenTriangleCoord s, F a.val := (Finset.sum_coe_sort (evenTriangle s) F).symm

theorem derivativeAtNode_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (node : ι → ℝ) (e : κ ≃ ι) (p : κ) :
    Zarankiewicz.derivativeAtNode (node ∘ e) p = Zarankiewicz.derivativeAtNode node (e p) := by
  classical
  have h : Zarankiewicz.nodePolynomial (node ∘ e) = Zarankiewicz.nodePolynomial node := by
    unfold Zarankiewicz.nodePolynomial
    exact e.prod_comp (fun i => (Polynomial.X-Polynomial.C (node i) : Polynomial ℝ))
  simp only [Zarankiewicz.derivativeAtNode, h, Function.comp_apply]

theorem weightedPairing_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (node : ι → ℝ) (e : κ ≃ ι) (K : ι → ι → ℝ) (A B : Poly2) :
    weightedPairing (node ∘ e) (fun p q => K (e p) (e q)) A B = weightedPairing node K A B := by
  unfold weightedPairing
  simp_rw [derivativeAtNode_equiv, Function.comp_apply]
  let F (p q : ι) : ℝ := K p q * (node p-node q) /
    (Zarankiewicz.derivativeAtNode node p*Zarankiewicz.derivativeAtNode node q) *
    evalTwo (node p) (node q) A * evalTwo (node p) (node q) B
  change (∑p : κ, ∑q : κ, F (e p) (e q)) = ∑p : ι, ∑q : ι, F p q
  calc
    _ = ∑p : κ, ∑q : ι, F (e p) q := by
      apply Finset.sum_congr rfl
      intro p _
      exact e.sum_comp (F (e p))
    _ = _ := e.sum_comp (fun p => ∑q, F p q)

theorem orderPairing_orderIso {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] (node : ι → ℝ) (e : κ ≃o ι) (A B : Poly2) :
    orderPairing (node ∘ e) inferInstance A B = orderPairing node inferInstance A B := by
  have h : (fun p q => halfOrder inferInstance (e p) (e q)) = halfOrder (inferInstance : LinearOrder κ) := by
    funext p q
    simp only [halfOrder, e.lt_iff_lt]
  rw [orderPairing, ← h]
  exact weightedPairing_equiv node e.toEquiv _ A B

end Paper170

end
end

section

/-! Nonsingularity of the weighted half-order pairing for every node order. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem order_pairing_nonsingular_fin (s : ℕ) (hs : 2 ≤ s)
    (node : Fin (2*s) → ℝ) (hn : Function.Injective node) :
    (∀ A ∈ rectangle (s-1) (s-2),
      (∀ B ∈ rectangle (s-2) (s-1), orderPairing node inferInstance A B = 0) → A=0) ∧
    (∀ B ∈ rectangle (s-2) (s-1),
      (∀ A ∈ rectangle (s-1) (s-2), orderPairing node inferInstance A B = 0) → B=0) := by
  classical
  obtain ⟨hfirst,hsecond⟩ := two_triangle_interpolation s hs node hn
  constructor
  · intro A hA hz
    apply evenTriangle_vanish_first s hs node hn A hA
    intro i j hij
    let a : EvenTriangleCoord s := ⟨(i,j),hij⟩
    obtain ⟨B,hB⟩ := hsecond.surjective (Pi.single a (1:ℝ))
    have he (b : EvenTriangleCoord s) : evalTwo (node b.val.1) (node b.val.2) B.val =
        (Pi.single a (1:ℝ) : EvenTriangleCoord s → ℝ) b := congrFun hB b
    have hzero := hz B.val B.property
    rw [orderPairing_triangle s hs node hn A B.val hA B.property] at hzero
    simp_rw [he] at hzero
    have hv : evenTriangleWeight s node a * evalTwo (node i) (node j) A = 0 := by
      simpa [Pi.single_apply, mul_ite, a] using hzero
    exact (mul_eq_zero.mp hv).resolve_left (evenTriangleWeight_ne_zero s node hn a)
  · intro B hB hz
    apply evenTriangle_vanish_second s hs node hn B hB
    intro i j hij
    let a : EvenTriangleCoord s := ⟨(i,j),hij⟩
    obtain ⟨A,hA⟩ := hfirst.surjective (Pi.single a (1:ℝ))
    have he (b : EvenTriangleCoord s) : evalTwo (node b.val.1) (node b.val.2) A.val =
        (Pi.single a (1:ℝ) : EvenTriangleCoord s → ℝ) b := congrFun hA b
    have hzero := hz A.val A.property
    rw [orderPairing_triangle s hs node hn A.val B A.property hB] at hzero
    simp_rw [he] at hzero
    have hv : evenTriangleWeight s node a * evalTwo (node i) (node j) B = 0 := by
      simpa [Pi.single_apply, mul_ite, ite_mul, a] using hzero
    exact (mul_eq_zero.mp hv).resolve_left (evenTriangleWeight_ne_zero s node hn a)

theorem order_pairing_nonsingular {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (order : LinearOrder ι) :
    (∀ A ∈ rectangle (s-1) (s-2),
      (∀ B ∈ rectangle (s-2) (s-1), orderPairing node order A B = 0) → A=0) ∧
    (∀ B ∈ rectangle (s-2) (s-1),
      (∀ A ∈ rectangle (s-1) (s-2), orderPairing node order A B = 0) → B=0) := by
  let := order
  let e : Fin (2*s) ≃o ι := Fintype.orderIsoFinOfCardEq ι hc
  obtain ⟨hfirst,hsecond⟩ := order_pairing_nonsingular_fin s hs (node ∘ e) (hn.comp e.injective)
  constructor
  · intro A hA hz
    apply hfirst A hA
    intro B hB
    rw [orderPairing_orderIso node e]
    exact hz B hB
  · intro B hB hz
    apply hsecond B hB
    intro A hA
    rw [orderPairing_orderIso node e]
    exact hz A hA

theorem order_detector {ι : Type*} [Fintype ι]
    (s : ℕ) (hs : 2 ≤ s) (hc : Fintype.card ι = 2*s)
    (node : ι → ℝ) (hn : Function.Injective node) (order : LinearOrder ι)
    (A : Poly2) (hA : A ∈ rectangle (s-2) (s-2))
    (hzero : ∀ B ∈ rectangle (s-1) (s-1), orderPairing node order A B = 0) : A=0 := by
  apply (order_pairing_nonsingular s hs hc node hn order).1 A
  · rw [rectangle_membership] at hA ⊢
    exact ⟨hA.1.trans (by omega), hA.2⟩
  · intro B hB
    apply hzero B
    rw [rectangle_membership] at hB ⊢
    exact ⟨hB.1.trans (by omega), hB.2⟩

end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_VertexEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex specialization, local interpolation tests, and kernel vanishing. -/

section

/-! Evaluation symmetries and genuine degree bounds after fixing a vertex. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalFour_swapFirst (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapFirstPair P) = evalFour u x y v P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [swapFirstPair, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [swapFirstPair, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.rename_X] at hP ⊢
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![u,x,y,v] _
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![u,x,y,v] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

theorem evalFour_swapSecond (P : Poly4) (x u y v : ℝ) :
    evalFour x u y v (swapSecondPair P) = evalFour x u v y P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [swapSecondPair, evalFour]
  | add P Q hP hQ => simpa using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [swapSecondPair, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.rename_X] at hP ⊢
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![x,u,v,y] _
    change MvPolynomial.aeval ![x,u,y,v] _ = MvPolynomial.aeval ![x,u,v,y] _ at hP
    simp only [map_mul]
    rw [hP]
    fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

theorem vertexSpecialization_monomial (x : ℝ) (m : Fin 4 →₀ ℕ) (c : ℝ) :
    vertexSpecialization x (MvPolynomial.monomial m c) =
      MvPolynomial.C (c*x^m 0*x^m 2) * MvPolynomial.X 0^m 1 * MvPolynomial.X 1^m 3 := by
  simp only [vertexSpecialization, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_four]
    ring
  · intro i
    simp

theorem vertexSpecialization_rectangle (s : ℕ) (P : endpointSymmetricSpace s) (x : ℝ) :
    vertexSpecialization x P.val ∈ rectangle (s-2) (s-2) := by
  have hp := ((symmetric_space_membership s P.val).mp P.property).1
  have hb (k : Fin 2) : (vertexSpecialization x P.val).degreeOf k ≤ s-2 := by
    rw [P.val.as_sum, map_sum]
    apply (MvPolynomial.degreeOf_sum_le k _ _).trans
    apply Finset.sup_le
    intro m hm
    rw [vertexSpecialization_monomial]
    have h1 := MvPolynomial.degreeOf_le_iff.mp (hp 1) m hm
    have h3 := MvPolynomial.degreeOf_le_iff.mp (hp 3) m hm
    have hmul := MvPolynomial.degreeOf_mul_le k
      (MvPolynomial.C (P.val.coeff m*x^m 0*x^m 2)*MvPolynomial.X 0^m 1)
      (MvPolynomial.X 1^m 3)
    have hC := MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X 0^m 1 : Poly2) k
      (P.val.coeff m*x^m 0*x^m 2)
    have hpow0 := MvPolynomial.degreeOf_pow_le k (MvPolynomial.X 0 : Poly2) (m 1)
    have hpow1 := MvPolynomial.degreeOf_pow_le k (MvPolynomial.X 1 : Poly2) (m 3)
    fin_cases k <;> norm_num [MvPolynomial.degreeOf_X, Fin.ext_iff] at hpow0 hpow1 hmul hC ⊢ <;> omega
  exact (rectangle_membership _ _ _).mpr ⟨hb 0,hb 1⟩

theorem neighbor_nodePolynomial {n : ℕ} (node : Fin n → ℝ) (i : Fin n) :
    Zarankiewicz.nodePolynomial (fun p : {j : Fin n // j ≠ i} => node p.val) =
      omittedNodePolynomial node i := by
  classical
  unfold Zarankiewicz.nodePolynomial omittedNodePolynomial
  exact (Finset.prod_subtype (Finset.univ.erase i) (by simp)
    (fun j => Polynomial.X-Polynomial.C (node j))).symm

theorem neighbor_nodeWeight {n : ℕ} (node : Fin n → ℝ) (hn : Function.Injective node)
    (i : Fin n) (p : {j : Fin n // j ≠ i}) :
    nodeWeight (fun q : {j : Fin n // j ≠ i} => node q.val) p =
      (node p.val-node i)*nodeWeight node p.val := by
  classical
  rw [omitted_node_weight node hn i p.val p.property.symm]
  unfold nodeWeight Zarankiewicz.derivativeAtNode
  rw [neighbor_nodePolynomial]

theorem sum_away {n : ℕ} (i : Fin n) (f : Fin n → ℝ) (hi : f i=0) :
    (∑j, f j) = ∑j : {j : Fin n // j ≠ i}, f j.val := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi, add_zero]
  exact Finset.sum_subtype (Finset.univ.erase i) (by simp) f

end Paper170

end
end

section

/-! The kernel vanishes on every orientation of an independent supported edge pair. -/
noncomputable section
namespace Paper170

theorem kernel_ordered_eval_zero {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P = 0)
    {i p k q : Fin n} (hip : i<p) (hkq : k<q) (hik : i≠k) (hiq : i≠q)
    (hpk : p≠k) (hpq : p≠q) (hJ : J i p k q ≠ 0) :
    evalFour (node i) (node p) (node k) (node q) P.val = 0 := by
  classical
  let a : SupportCoord J := ⟨((i,p),(k,q)), by
    simp only [supportedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hip,hkq,hik,hiq,hpk,hpq,hJ⟩⟩
  exact congrFun hP a

theorem kernel_independent_eval_zero {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P = 0)
    {i p k q : Fin n} (hip : i≠p) (hkq : k≠q) (hik : i≠k) (hiq : i≠q)
    (hpk : p≠k) (hpq : p≠q) (hJ : J i p k q ≠ 0) :
    evalFour (node i) (node p) (node k) (node q) P.val = 0 := by
  have hsym := (symmetric_space_membership s P.val).mp P.property
  have he1 (x u y v : ℝ) : evalFour x u y v P.val = evalFour u x y v P.val := by
    rw [← evalFour_swapFirst, hsym.2.1]
  have he2 (x u y v : ℝ) : evalFour x u y v P.val = evalFour x u v y P.val := by
    rw [← evalFour_swapSecond, hsym.2.2]
  rcases lt_or_gt_of_ne hip with hip | hpi
  · rcases lt_or_gt_of_ne hkq with hkq | hqk
    · exact kernel_ordered_eval_zero node J P hP hip hkq hik hiq hpk hpq hJ
    · rw [he2]
      apply kernel_ordered_eval_zero node J P hP hip hqk hiq hik hpq hpk
      rw [hreverseRight i p k q]
      exact neg_ne_zero.mpr hJ
  · rw [he1]
    rcases lt_or_gt_of_ne hkq with hkq | hqk
    · apply kernel_ordered_eval_zero node J P hP hpi hkq hpk hpq hik hiq
      rw [hreverseLeft i p k q]
      exact neg_ne_zero.mpr hJ
    · rw [he2]
      apply kernel_ordered_eval_zero node J P hP hpi hqk hpq hpk hiq hik
      rw [hreverseLeft i p q k, hreverseRight i p k q, neg_neg]
      exact hJ

end Paper170

end
end

section

/-! The local test polynomial reduces the global tensor sum to its adjacent-edge pairings. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem evalFour_liftUnivariate (x u y v : ℝ) (i : Fin 4) (U : Polynomial ℝ) :
    evalFour x u y v (liftUnivariate i U) = U.eval (![x,u,y,v] i) := by
  change MvPolynomial.aeval ![x,u,y,v] (Polynomial.aeval (MvPolynomial.X i) U) = _
  rw [← Polynomial.aeval_algHom_apply]
  simp

theorem evalFour_liftBivariate13 (x u y v : ℝ) (B : Poly2) :
    evalFour x u y v (liftBivariate 1 3 B) = evalTwo u v B := by
  have h : (MvPolynomial.aeval ![x,u,y,v]).comp
      (MvPolynomial.aeval ![MvPolynomial.X 1,MvPolynomial.X 3] : Poly2 →ₐ[ℝ] Poly4) =
      MvPolynomial.aeval ![u,v] := by
    ext i
    fin_cases i <;> simp
  exact congrArg (fun f : Poly2 →ₐ[ℝ] ℝ => f B) h

theorem evalFour_localTestPolynomial (x u y v : ℝ) (P : Poly4)
    (U V : Polynomial ℝ) (B : Poly2) :
    evalFour x u y v (localTestPolynomial P U V B) =
      evalFour x u y v P * (u-v) * (u-y) * (v-x) *
        U.eval x * V.eval y * evalTwo u v B := by
  have hm (Q R : Poly4) : evalFour x u y v (Q*R) = evalFour x u y v Q*evalFour x u y v R :=
    map_mul (MvPolynomial.aeval ![x,u,y,v]) Q R
  simp only [localTestPolynomial, hm, evalFour_liftUnivariate, evalFour_liftBivariate13]
  simp [evalFour]

theorem vertexTestSummand_offDiagonal {n s : ℕ} (node : Fin n → ℝ) (J : CrossingTensor n)
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P=0)
    (U V : Polynomial ℝ) (B : Poly2) (i p k q : Fin n) (hik : i≠k) :
    vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q = 0 := by
  by_cases hip : i=p
  · subst p
    simp [vertexTestSummand, hloopLeft]
  by_cases hkq : k=q
  · subst q
    simp [vertexTestSummand, hloopRight]
  by_cases hpq : p=q
  · subst q
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hpk : p=k
  · subst k
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hiq : i=q
  · subst q
    simp [vertexTestSummand, evalFour_localTestPolynomial]
  by_cases hJ : J i p k q=0
  · simp [vertexTestSummand, hJ]
  have hz := kernel_independent_eval_zero node J hreverseLeft hreverseRight P hP
    hip hkq hik hiq hpk hpq hJ
  simp [vertexTestSummand, evalFour_localTestPolynomial, hz]

theorem orderPairing_weight_form {ι : Type*} [Fintype ι] (node : ι → ℝ)
    (order : LinearOrder ι) (A B : Poly2) :
    orderPairing node order A B = ∑p, ∑q,
      halfOrder order p q * (node p-node q) * nodeWeight node p * nodeWeight node q *
        evalTwo (node p) (node q) A * evalTwo (node p) (node q) B := by
  simp only [orderPairing, weightedPairing, nodeWeight, div_eq_mul_inv, mul_inv]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem vertexTestSummand_diagonal {n : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i})
    (hlocal : ∀i (p q : {j : Fin n // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (P : Poly4) (U V : Polynomial ℝ) (B : Poly2) (i : Fin n)
    (p q : {j : Fin n // j≠i}) :
    vertexTestSummand node J (localTestPolynomial P U V B) i p.val i q.val =
      (nodeWeight node i)^2 * U.eval (node i) * V.eval (node i) *
      (halfOrder (orders i) p q * (node p.val-node q.val) *
        nodeWeight (fun j : {j : Fin n // j≠i} => node j.val) p *
        nodeWeight (fun j : {j : Fin n // j≠i} => node j.val) q *
        evalTwo (node p.val) (node q.val) (vertexSpecialization (node i) P) *
        evalTwo (node p.val) (node q.val) B) := by
  rw [vertexTestSummand, evalFour_localTestPolynomial, hlocal]
  rw [neighbor_nodeWeight node hn, neighbor_nodeWeight node hn, vertex_eval]
  ring

theorem polynomialTest_local_reduction {n s : ℕ} (node : Fin n → ℝ)
    (hn : Function.Injective node) (J : CrossingTensor n)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i})
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (hlocal : ∀i (p q : {j : Fin n // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (P : endpointSymmetricSpace s) (hP : supportEvaluation s node J P=0)
    (U V : Polynomial ℝ) (B : Poly2) :
    polynomialTest node J (localTestPolynomial P.val U V B) =
      ∑i, (nodeWeight node i)^2 * U.eval (node i) * V.eval (node i) *
        orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P.val) B := by
  change (∑i, ∑p, ∑k, ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q)=_
  apply Finset.sum_congr rfl
  intro i _
  have hk (p : Fin n) :
      (∑k, ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p k q) =
      ∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p i q := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro q _
      exact vertexTestSummand_offDiagonal node J hloopLeft hloopRight hreverseLeft hreverseRight
        P hP U V B i p k q hki.symm
    · simp
  simp_rw [hk]
  rw [sum_away i _ (by simp [vertexTestSummand,hloopLeft])]
  have hq (p : {j : Fin n // j≠i}) :
      (∑q, vertexTestSummand node J (localTestPolynomial P.val U V B) i p.val i q) =
      ∑q : {j : Fin n // j≠i}, vertexTestSummand node J (localTestPolynomial P.val U V B) i p.val i q.val :=
    sum_away i _ (by simp [vertexTestSummand,hloopRight])
  simp_rw [hq, vertexTestSummand_diagonal node hn J orders hlocal]
  rw [orderPairing_weight_form]
  simp only [Finset.mul_sum]

end Paper170

end
end

section

/-! Lagrange isolation of each vertex and the full kernel vertex-vanishing theorem. -/
noncomputable section
open scoped BigOperators
namespace Paper170

theorem vertexPairingFunctional_apply {n : ℕ} (node : Fin n → ℝ)
    (orders : ∀i : Fin n, LinearOrder {j : Fin n // j≠i}) (P : Poly4) (B : Poly2)
    (W : Polynomial ℝ) :
    vertexPairingFunctional node orders P B W =
      ∑i, (nodeWeight node i)^2 * W.eval (node i) *
        orderPairing (fun j : {j : Fin n // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P) B := by
  simp only [vertexPairingFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

section CrossingTensor
variable {s : ℕ} (hs : 2 ≤ s) (node : Fin (2*s+1) → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor (2*s+1))
    (orders : ∀i : Fin (2*s+1), LinearOrder {j : Fin (2*s+1) // j≠i})
    (hloopLeft : ∀i k q, J i i k q=0) (hloopRight : ∀i p k, J i p k k=0)
    (hreverseLeft : ∀i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀i p k q, J i p q k = -J i p k q)
    (hskew : ∀i p k q, J k q i p = -J i p k q)
    (hlocal : ∀i (p q : {j : Fin (2*s+1) // j≠i}), J i p.val i q.val=halfOrder (orders i) p q)
    (htests : ∀H ∈ box4 (2*s-1), polynomialTest node J H=0)

include hs hnode hloopLeft hloopRight hreverseLeft hreverseRight hlocal htests in
theorem vertexPairingFunctional_zero (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) (B : Poly2) (hB : B∈rectangle (s-1) (s-1))
    (W : Polynomial ℝ) (hW : W∈Polynomial.degreeLT ℝ (2*s+1)) :
    vertexPairingFunctional node orders P.val B W=0 := by
  have hspan : Submodule.span ℝ {Q : Polynomial ℝ | ∃U V : Polynomial ℝ,
      U.natDegree ≤ s ∧ V.natDegree ≤ s ∧ Q=U*V} ≤
        LinearMap.ker (vertexPairingFunctional node orders P.val B) := by
    rw [Submodule.span_le]
    rintro Q ⟨U,V,hU,hV,rfl⟩
    change vertexPairingFunctional node orders P.val B (U*V)=0
    have hz := htests (localTestPolynomial P.val U V B) (local_test_degree s hs P.val P.property U V hU hV B hB)
    rw [polynomialTest_local_reduction node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hlocal P hP U V B] at hz
    rw [vertexPairingFunctional_apply]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul]
    ring
  rw [products_span_degree] at hspan
  exact hspan hW

include hs hnode hloopLeft hloopRight hreverseLeft hreverseRight hlocal htests in
theorem kernel_local_pairing_zero (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) (i : Fin (2*s+1)) (B : Poly2)
    (hB : B∈rectangle (s-1) (s-1)) :
    orderPairing (fun j : {j : Fin (2*s+1) // j≠i} => node j.val) (orders i)
      (vertexSpecialization (node i) P.val) B = 0 := by
  classical
  let W := Lagrange.basis Finset.univ node i
  have hW : W∈Polynomial.degreeLT ℝ (2*s+1) := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Lagrange.degree_basis hnode.injOn (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel_right]
    exact_mod_cast (show 2*s < 2*s+1 by omega)
  have hz := vertexPairingFunctional_zero hs node hnode J orders hloopLeft hloopRight
    hreverseLeft hreverseRight hlocal htests P hP B hB W hW
  rw [vertexPairingFunctional_apply] at hz
  have heq : (∑j, (nodeWeight node j)^2 * W.eval (node j) *
      orderPairing (fun k : {k : Fin (2*s+1) // k≠j} => node k.val) (orders j)
        (vertexSpecialization (node j) P.val) B) =
      (nodeWeight node i)^2 *
        orderPairing (fun j : {j : Fin (2*s+1) // j≠i} => node j.val) (orders i)
          (vertexSpecialization (node i) P.val) B := by
    rw [Finset.sum_eq_single i]
    · rw [show W.eval (node i)=1 from Lagrange.eval_basis_self hnode.injOn (Finset.mem_univ i), mul_one]
    · intro j _ hji
      rw [show W.eval (node j)=0 from Lagrange.eval_basis_of_ne hji.symm (Finset.mem_univ j)]
      simp
    · simp
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (weight_nonzero node hnode i))

include hs hnode orders hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests in
theorem kernel_vertex_vanishing (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P=0) : ∀i, vertexSpecialization (node i) P.val=0 := by
  have hlocal' : ∀j (p q : {j' : Fin (2*s+1) // j'≠j}),
      J j p.val j q.val=halfOrder (orders j) p q := by
    intro j p q
    by_cases hpq : p=q
    · subst q
      have hh := hskew j p.val j p.val
      have hz : J j p.val j p.val=0 := by linarith
      have hpp := @lt_irrefl _ (orders j).toPartialOrder.toPreorder p
      simp only [hz,halfOrder,ite_eq_right hpp]
    · exact hlocal j p q
  intro i
  apply order_detector s hs (by simp [Fintype.card_subtype_compl])
    (fun j : {j : Fin (2*s+1) // j≠i} => node j.val)
    (hnode.comp Subtype.val_injective) (orders i) _ (vertexSpecialization_rectangle s P (node i))
  intro B hB
  exact kernel_local_pairing_zero hs node hnode J orders hloopLeft hloopRight
    hreverseLeft hreverseRight hlocal' htests P hP i B hB

end CrossingTensor
end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial injectivity and the lower bound on crossing-tensor support. -/

section

/-! The polynomial lower-bound argument for complete graphs. -/
noncomputable section
namespace Paper170
section CrossingTensor

variable {s : ℕ} (hs : 2 ≤ s) (node : Fin (2 * s + 1) → ℝ)
    (hnode : Function.Injective node) (J : CrossingTensor (2 * s + 1))
    (orders : ∀ i : Fin (2 * s + 1), LinearOrder {j : Fin (2 * s + 1) // j ≠ i})
    (hloopLeft : ∀ i k q, J i i k q = 0)
    (hloopRight : ∀ i p k, J i p k k = 0)
    (hreverseLeft : ∀ i p k q, J p i k q = -J i p k q)
    (hreverseRight : ∀ i p k q, J i p q k = -J i p k q)
    (hskew : ∀ i p k q, J k q i p = -J i p k q)
    (hlocal : ∀ i (p q : {j : Fin (2 * s + 1) // j ≠ i}),
      J i p.val i q.val = halfOrder (orders i) p q)
    (htests : ∀ H ∈ box4 (2 * s - 1), polynomialTest node J H = 0)

include hs hnode orders hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests

theorem kernel_diagonal_vanishing (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P = 0) :
    diagonalSpecialization P.val = 0 :=
  diagonal_zero_of_vertices s node hnode P (kernel_vertex_vanishing hs node hnode J orders
    hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests P hP)

theorem kernel_collision_divisibility (P : endpointSymmetricSpace s)
    (hP : supportEvaluation s node J P = 0) : collisionFactor ∣ P.val :=
  collision_divides_of_diagonal_vanishing s P (kernel_diagonal_vanishing hs node hnode J orders
    hloopLeft hloopRight hreverseLeft hreverseRight hskew hlocal htests P hP)

theorem support_evaluation_injective : Function.Injective (supportEvaluation s node J) :=
  support_evaluation_injective_of_collision hs node hnode J
    (kernel_collision_divisibility hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)

theorem support_cardinality_lower_bound :
    2 * (Nat.choose s 2) ^ 2 ≤ (supportedPairs J).card :=
  support_cardinality_of_injective_isotropic hs node hnode J
    (support_evaluation_injective hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)
    (evaluation_image_isotropic hs node hnode J orders hloopLeft hloopRight
      hreverseLeft hreverseRight hskew hlocal htests)

end CrossingTensor
end Paper170

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd and even lower bounds, explicit attainment, and the ordinary complete-graph crossing formula. -/

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

theorem complete_graph_odd_lower_bound (s : ℕ) (hs : 2 ≤ s)
    (N : NormalizedDrawing (completeGraph (2 * s + 1))) :
    (s.choose 2) ^ 2 ≤ crossingCount N.toAdmissibleDrawing := by
  obtain ⟨O⟩ := spoke_orders_exist _ N
  obtain ⟨orders, hlocal⟩ := complete_local_orders N O
  obtain ⟨hleft, hright, hrevleft, hrevright, hskew⟩ := raw_cycle_symmetries N O
  let node : Fin (2 * s + 1) → ℝ := fun i => i.val
  have hn : Function.Injective node := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  have ht (H : Poly4) (hH : H ∈ box4 (2 * s - 1)) :
      polynomialTest node (rawCycleIntersection O) H = 0 := by
    apply polynomial_cycle_tests (by omega) node hn (rawCycleIntersection O)
      (raw_cycle_pairing N O) H
    convert hH using 1
    congr 1
  have hl := support_cardinality_lower_bound hs node hn (rawCycleIntersection O) orders
    hleft hright hrevleft hrevright hskew hlocal ht
  have hu := signed_support_bound N O
  omega

lemma complete_graph_odd_lower_arbitrary (s : ℕ) (hs : 2 ≤ s)
    (D : AdmissibleDrawing (completeGraph (2 * s + 1))) : hill (2 * s + 1) ≤ crossingCount D := by
  obtain ⟨N, hN⟩ := polygonal_no_adjacent_normalization _ D
  rw [hill_odd]
  exact (complete_graph_odd_lower_bound s hs N).trans hN

lemma complete_graph_even_lower_normalized (s : ℕ) (hs : 2 ≤ s)
    (N : NormalizedDrawing (completeGraph (2 * s + 2))) :
    hill (2 * s + 2) ≤ crossingCount N.toAdmissibleDrawing := by
  obtain ⟨A, _, hA⟩ := vertex_deletion_count (2 * s + 1) (by omega) N
  have hl : ∀ v, hill (2 * s + 1) ≤ crossingCount (A v) :=
    fun v => complete_graph_odd_lower_arbitrary s hs (A v)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hl v)
  rw [hA] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
  have he : 2 * (s + 1) = 2 * s + 2 := by omega
  have ho : 2 * s + 2 - 1 = 2 * s + 1 := by omega
  conv_lhs => rw [← he]
  apply even_lower_bound_of_deletion (s + 1) _ (by omega)
  simpa only [he, ho, Nat.add_assoc] using hh

theorem complete_graph_lower_bound_oai (n : ℕ) (hn : 3 ≤ n)
    (D : AdmissibleDrawing (completeGraph n)) : hill n ≤ crossingCount D := by
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [hill]
  by_cases hodd : n % 2 = 1
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 1 := ⟨n / 2, by omega⟩
    exact complete_graph_odd_lower_arbitrary s (by omega) D
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 2 := ⟨n / 2 - 1, by omega⟩
    obtain ⟨N, hN⟩ := polygonal_no_adjacent_normalization _ D
    exact (complete_graph_even_lower_normalized s (by omega) N).trans hN

end Paper170

end
end

end OAI
end

theorem solution : type_of% @OAI.Paper170.complete_graph_lower_bound_oai := @OAI.Paper170.complete_graph_lower_bound_oai
