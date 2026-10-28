-- Prove2me | solution 1 for OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_passage_pairing_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:46:27.976461+00:00
-- url     : https://prove2.me/submissions/19c3bf78-adeb-4334-b79e-8f301d8fc2c9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc002

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

theorem det2_neg_right (u v : Plane) : det2 u (-v) = -det2 u v := by
  simp [det2]
  ring

end Zarankiewicz

end

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

theorem segmentsCrossProperly_reverse_left (a b c d : Plane) :
    SegmentsCrossProperly b a c d ↔ SegmentsCrossProperly a b c d := by
  have forward : ∀ a b c d : Plane,
      SegmentsCrossProperly a b c d → SegmentsCrossProperly b a c d := by
    intro a b c d h
    obtain ⟨hn,t,ht,u,hu,he⟩ := h
    refine ⟨?_,1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,u,hu,?_⟩
    · rw [← neg_sub b a, det2_neg_left]
      exact neg_ne_zero.mpr hn
    · rwa [segmentPoint_reverse]
  exact ⟨forward b a c d, forward a b c d⟩

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

theorem segmentCrossingSign_reverse_left (a b c d : Plane) :
    segmentCrossingSign b a c d = -segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_reverse_left]
  by_cases h : SegmentsCrossProperly a b c d
  · rw [ite_eq_left h, ite_eq_left h, ← neg_sub b a, det2_neg_left]
    exact nonzero_orientation_sign_neg _ h.1
  · simp [h]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem closedSegmentsMeet_of_proper (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    ClosedSegmentsMeet a b c d := by
  obtain ⟨_,t,ht,u,hu,he⟩ := h
  exact ⟨t,⟨ht.1.le,ht.2.le⟩,u,⟨hu.1.le,hu.2.le⟩,he⟩

theorem isClosed_closedSegmentsMeet (c d : Plane) :
    IsClosed {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d} := by
  let P := (Plane × Plane) × (unitInterval × unitInterval)
  let S : Set P := {x | segmentPoint x.1.1 x.1.2 x.2.1.val = segmentPoint c d x.2.2.val}
  have hS : IsClosed S := by
    apply isClosed_eq
    · dsimp [segmentPoint]
      fun_prop
    · dsimp [segmentPoint]
      fun_prop
  have hproj := (isClosedMap_fst_of_compactSpace : IsClosedMap (Prod.fst : P → Plane × Plane)) S hS
  have heq : Prod.fst '' S = {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d} := by
    ext ab
    constructor
    · rintro ⟨⟨ab',t,u⟩,hx,h⟩
      change ab'=ab at h
      subst ab'
      exact ⟨t.val,t.property,u.val,u.property,hx⟩
    · rintro ⟨t,ht,u,hu,h⟩
      exact ⟨(ab,(⟨t,ht⟩,⟨u,hu⟩)),h,rfl⟩
  rwa [heq] at hproj

end Zarankiewicz

end

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

theorem det2_add_right (u v w : Plane) : det2 u (v+w) = det2 u v+det2 u w := by
  dsimp [det2]
  ring

theorem det2_sub_right (u v w : Plane) : det2 u (v-w) = det2 u v-det2 u w := by
  dsimp [det2]
  ring

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
-- module Solutions.OAIQ4_Cc.Crossing_OffsetVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem det2_normalShift (v : Plane) (hv : v ≠ 0) : det2 v (normalShift v) = 1 := by
  have hn := ne_of_gt (squaredLength_pos v hv)
  unfold normalShift
  rw [det2_smul_right]
  have he : det2 v (rotateQuarter v) = squaredLength v := by
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [he,inv_mul_cancel₀ hn]

theorem det2_cornerShift_left (u v : Plane) (hn : det2 u v ≠ 0) :
    det2 u (cornerShift u v) = 1 := by
  unfold cornerShift
  rw [det2_smul_right,det2_sub_right,det2_self,sub_zero,inv_mul_cancel₀ hn]

theorem det2_cornerShift_right (u v : Plane) (hn : det2 u v ≠ 0) :
    det2 v (cornerShift u v) = 1 := by
  unfold cornerShift
  rw [det2_smul_right,det2_sub_right,det2_self,det2_swap u v,zero_sub,neg_neg,inv_mul_cancel₀ hn]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ParallelDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem offset_direction_det_zero (a b qa qb : Plane) (ε : ℝ)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    det2 (b-a) ((b+ε • qb)-(a+ε • qa)) = 0 := by
  dsimp [det2] at *
  linear_combination ε*hb-ε*ha

theorem exists_forward_offset_radius (a b qa qb : Plane) (hab : b ≠ a)
    (ha : det2 (b-a) qa=1) (hb : det2 (b-a) qb=1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ →
      ∃ r : ℝ, 0 < r ∧ (b+ε • qb)-(a+ε • qa) = r • (b-a) := by
  have hn : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hlen := squaredLength_pos (b-a) hn
  let f : ℝ → ℝ := fun ε => dot2 (b-a) ((b+ε • qb)-(a+ε • qa)) / squaredLength (b-a)
  have hf : Continuous f := by
    dsimp [f,dot2,squaredLength]
    fun_prop
  have hf0 : 0<f 0 := by
    have he : f 0=1 := by
      dsimp [f]
      simp only [zero_smul,add_zero]
      have hd : dot2 (b-a) (b-a)=squaredLength (b-a) := by dsimp [dot2,squaredLength]; ring
      rw [hd]
      exact div_self (ne_of_gt hlen)
    rw [he]
    norm_num
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, 0<f ε := continuousAt_const.eventually_lt hf.continuousAt hf0
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  refine ⟨f ε,hd (by simpa [Real.dist_eq] using hε),?_⟩
  exact vector_parallel_of_det_zero (b-a) _ hn (offset_direction_det_zero a b qa qb ε ha hb)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_OffsetTrack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem trackOffset_incident_levels (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (i : ℕ) (hi : i < n) :
    det2 (trackDirection v i) (trackOffset v n i)=1 ∧
      det2 (trackDirection v i) (trackOffset v n (i+1))=1 := by
  constructor
  · by_cases hz : i=0
    · subst i
      simpa [trackOffset] using det2_normalShift (trackDirection v 0) (hv 0 hi)
    · have hip : 0 < i := by omega
      simpa [trackOffset,hz,hi] using
        det2_cornerShift_right (trackDirection v (i-1)) (trackDirection v i) (hb i hip hi)
  · by_cases hnext : i+1 < n
    · simpa [trackOffset,hnext] using
        det2_cornerShift_left (trackDirection v i) (trackDirection v (i+1))
          (by simpa using hb (i+1) (by omega) hnext)
    · have hn : n=i+1 := by omega
      subst n
      simpa [trackOffset] using det2_normalShift (trackDirection v i) (hv i hi)

theorem exists_forward_shiftedTrack_radius (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i : Fin n,
      ∃ r : ℝ, 0 < r ∧ shiftedTrack v n t (i.val+1)-shiftedTrack v n t i.val = r • trackDirection v i.val := by
  have hh (i : Fin n) := exists_forward_offset_radius (v i.val) (v (i.val+1))
    (trackOffset v n i.val) (trackOffset v n (i.val+1))
    (sub_ne_zero.mp (hv i.val i.isLt))
    (trackOffset_incident_levels v n hv hb i.val i.isLt).1
    (trackOffset_incident_levels v n hv hb i.val i.isLt).2
  choose radius hpos hdir using hh
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  exact ⟨δ,hδ,fun t ht i => hdir i t (ht.trans (hbound i (Finset.mem_univ _)))⟩

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

end PolygonalChain
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

end Zarankiewicz

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

theorem circlePoint_on_unit_circle (t : ℝ) : (circlePoint t).1^2+(circlePoint t).2^2 = 1 := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_parameter (t : ℝ) : (circlePoint t).2/(1+(circlePoint t).1) = t := by
  have h := ne_of_gt (circle_denominator_pos t)
  have hden : 1+(circlePoint t).1 = 2/(1+t^2) := by
    dsimp [circlePoint]
    field_simp
    ring
  rw [hden]
  dsimp [circlePoint]
  field_simp

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro a b hab
  have hh := congrArg (fun z : Plane => z.2/(1+z.1)) hab
  simpa only [circlePoint_parameter] using hh

theorem circle_orient_formula (a b c : ℝ) :
    orient2 (circlePoint a) (circlePoint b) (circlePoint c) =
      4*(b-a)*(c-a)*(c-b)/((1+a^2)*(1+b^2)*(1+c^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  have hc := ne_of_gt (circle_denominator_pos c)
  dsimp [orient2,det2,circlePoint]
  field_simp
  ring

theorem circle_orient_pos (a b c : ℝ) (hab : a<b) (hbc : b < c) :
    0 < orient2 (circlePoint a) (circlePoint b) (circlePoint c) := by
  rw [circle_orient_formula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hab))
      (sub_pos.mpr (hab.trans hbc))) (sub_pos.mpr hbc))
    (mul_pos (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)) (circle_denominator_pos c))

theorem circle_chords_alternating_positive (a c b d : ℝ) (hac : a < c) (hcb : c<b) (hbd : b<d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 1 := by
  apply segmentCrossingSign_of_positive_sides
  · rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a c b hac hcb)
  · exact circle_orient_pos a b d (hac.trans hcb) hbd
  · rw [orient2_cycle]
    exact circle_orient_pos a c d hac (hcb.trans hbd)
  · rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos c b d hcb hbd)

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
-- module Solutions.OAIQ4_Cc.Crossing_ChainTracePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalChain.piece_subset_path_range {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (i : ℕ) (hi : i < P.pieces) :
    segment ℝ (P.vertices i) (P.vertices (i+1)) ⊆ Set.range P.path := by
  exact polygonalArcPath_piece_subset_range P.vertices P.pieces i hi

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

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentClosedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedSegmentsMeet_iff_nonempty_inter (a b c d : Plane) :
    ClosedSegmentsMeet a b c d ↔ (segment ℝ a b ∩ segment ℝ c d).Nonempty := by
  constructor
  · rintro ⟨s,hs,t,ht,he⟩
    refine ⟨segmentPoint a b s,?_,?_⟩
    · rw [← Path.range_segment]
      exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
    · rw [← Path.range_segment]
      exact ⟨⟨t,ht⟩,by simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he.symm⟩
  · rintro ⟨x,hx,hy⟩
    rw [← Path.range_segment] at hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    refine ⟨s.val,s.property,t.val,t.property,?_⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm

theorem not_closedSegmentsMeet_of_disjoint (a b c d : Plane)
    (h : Disjoint (segment ℝ a b) (segment ℝ c d)) : ¬ ClosedSegmentsMeet a b c d := by
  intro hh
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter a b c d).mp hh
  exact Set.disjoint_left.mp h hx hy

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ShiftedSegmentStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem closedSegmentsMeet_symm (a b c d : Plane) : ClosedSegmentsMeet a b c d ↔ ClosedSegmentsMeet c d a b := by
  constructor <;> rintro ⟨t,ht,u,hu,he⟩ <;> exact ⟨u,hu,t,ht,he.symm⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedChainVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radialPort_parameter_half (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : 4*r^2 < squaredLength (b-a)) :
    0 < r/Real.sqrt (squaredLength (b-a)) ∧ r/Real.sqrt (squaredLength (b-a)) < 1/2 := by
  have hL : 0 < squaredLength (b-a) := by nlinarith [sq_nonneg r]
  have hs := Real.sqrt_pos.mpr hL
  have hs2 := Real.sq_sqrt hL.le
  exact ⟨div_pos hr hs,(div_lt_iff₀ hs).mpr (by nlinarith)⟩

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem startPort_eq_fraction (P : PolygonalChain O a b) (r : ℝ) :
    P.startPort r=P.vertices 0+P.startFraction r • (P.vertices 1-P.vertices 0) := rfl

theorem endPort_eq_fraction (P : PolygonalChain O a b) (r : ℝ) :
    P.endPort r=P.vertices P.pieces-P.endFraction r • (P.vertices P.pieces-P.vertices (P.pieces-1)) := by
  unfold endPort radialPort endFraction
  rw [squaredLength_sub_comm (P.vertices (P.pieces-1)) (P.vertices P.pieces)]
  apply Prod.ext <;> dsimp <;> ring

end PolygonalChain
end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedChainDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_start_formula (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (hi : i < P.pieces) :
    P.truncatedVertices r i=P.vertices i+(if i=0 then P.startFraction r else 0) • trackDirection P.vertices i := by
  by_cases h : i=0
  · subst i
    rw [truncatedVertices_first,startPort_eq_fraction]
    rfl
  · simp only [truncatedVertices,ite_eq_right h,ite_eq_right (show i ≠ P.pieces by omega),zero_smul,add_zero]

theorem truncated_end_formula (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (_hi : i < P.pieces) :
    P.truncatedVertices r (i+1)=P.vertices (i+1)-(if i+1=P.pieces then P.endFraction r else 0) •
      trackDirection P.vertices i := by
  by_cases h : i+1=P.pieces
  · have hh : i=P.pieces-1 := by omega
    rw [h,truncatedVertices_last P (by omega) r,endPort_eq_fraction,ite_eq_left rfl]
    simp only [trackDirection,hh,show P.pieces-1+1=P.pieces by omega]
  · simp only [truncatedVertices,ite_eq_right (show i+1 ≠ 0 by omega),ite_eq_right h,zero_smul,sub_zero]

theorem truncated_direction (P : PolygonalChain O a b) (r : ℝ) (i : ℕ) (hi : i < P.pieces) :
    trackDirection (P.truncatedVertices r) i=P.truncatedScale r i • trackDirection P.vertices i := by
  change P.truncatedVertices r (i+1)-P.truncatedVertices r i=_
  rw [truncated_end_formula P r i hi,truncated_start_formula P r i hi]
  apply Prod.ext <;> dsimp [trackDirection,truncatedScale] <;> ring

theorem truncatedScale_pos (P : PolygonalChain O a b) (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) (i : ℕ) :
    0 < P.truncatedScale r i := by
  have hs := radialPort_parameter_half (P.vertices 0) (P.vertices 1) r hr hfirst
  have he := radialPort_parameter_half (P.vertices (P.pieces-1)) (P.vertices P.pieces) r hr hlast
  change 0 < P.startFraction r ∧ P.startFraction r < 1/2 at hs
  change 0 < P.endFraction r ∧ P.endFraction r < 1/2 at he
  unfold truncatedScale
  split_ifs <;> linarith

theorem truncated_direction_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : i < P.pieces) : trackDirection (P.truncatedVertices r) i ≠ 0 := by
  rw [P.truncated_direction r i hi]
  exact smul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast i)) (P.minimum_piece_ne_zero hmin i hi)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedTrackAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_bend_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1)))
    (i : ℕ) (hi : 0 < i) (hi' : i < P.pieces) :
    det2 (trackDirection (P.truncatedVertices r) (i-1)) (trackDirection (P.truncatedVertices r) i) ≠ 0 := by
  rw [P.truncated_direction r (i-1) (by omega),P.truncated_direction r i hi',det2_smul_left,det2_smul_right]
  apply mul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast (i-1)))
  apply mul_ne_zero (ne_of_gt (P.truncatedScale_pos r hr hfirst hlast i))
  have h := P.minimum_bend_det_ne_zero hmin (i-1) (by omega)
  simpa only [trackDirection,show i-1+1=i by omega,show i-1+2=i+1 by omega] using h

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedRadialEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem radial_segment_of_coefficients (o p q v : Plane) (r α β : ℝ)
    (hr : 0 < r) (hα : 0 < α) (hβ : 0 < β)
    (hp : p-o=α • v) (hq : q-p=β • v) (hc : squaredLength (p-o)=r^2) :
    segment ℝ p q ⊆ insert p {x | r^2 < squaredLength (x-o)} := by
  have he : q=p+(β/α) • (p-o) := by
    rw [hp,smul_smul,div_mul_cancel₀ _ (ne_of_gt hα)]
    rw [← hq]
    abel
  rw [he]
  exact radial_spur_exterior o p r (β/α) hc hr (div_pos hβ hα)

namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}

theorem truncated_first_exterior (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    segment ℝ (P.truncatedVertices r 0) (P.truncatedVertices r 1) ⊆
      insert (P.startPort r) {x | r^2 < squaredLength (x-P.vertices 0)} := by
  have hα := (radialPort_parameter_half (P.vertices 0) (P.vertices 1) r hr hfirst).1
  have hβ := P.truncatedScale_pos r hr hfirst hlast 0
  rw [P.truncatedVertices_first]
  apply radial_segment_of_coefficients (P.vertices 0) (P.startPort r) (P.truncatedVertices r 1)
    (trackDirection P.vertices 0) r (P.startFraction r) (P.truncatedScale r 0) hr hα hβ
  · exact radialPort_sub (P.vertices 0) (P.vertices 1) r
  · simpa only [trackDirection,P.truncatedVertices_first] using P.truncated_direction r 0 hp
  · exact radialPort_on_circle (P.vertices 0) (P.vertices 1)
      (P.minimum_vertices_ne hmin 0 1 (by omega) hp) r

theorem truncated_last_exterior (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) (hp : 0 < P.pieces)
    (r : ℝ) (hr : 0 < r)
    (hfirst : 4*r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : 4*r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    segment ℝ (P.truncatedVertices r (P.pieces-1)) (P.truncatedVertices r P.pieces) ⊆
      insert (P.endPort r) {x | r^2 < squaredLength (x-P.vertices P.pieces)} := by
  have hi : P.pieces-1 < P.pieces := by omega
  have hα := (radialPort_parameter_half (P.vertices (P.pieces-1)) (P.vertices P.pieces) r hr hlast).1
  have hβ := P.truncatedScale_pos r hr hfirst hlast (P.pieces-1)
  rw [P.truncatedVertices_last hp,segment_symm]
  apply radial_segment_of_coefficients (P.vertices P.pieces) (P.endPort r)
    (P.truncatedVertices r (P.pieces-1)) (-(trackDirection P.vertices (P.pieces-1)))
    r (P.endFraction r) (P.truncatedScale r (P.pieces-1)) hr hα hβ
  · rw [P.endPort_eq_fraction]
    simp only [trackDirection,show P.pieces-1+1=P.pieces by omega,smul_neg]
    abel
  · have h := P.truncated_direction r (P.pieces-1) hi
    simp only [trackDirection,show P.pieces-1+1=P.pieces by omega,P.truncatedVertices_last hp] at h ⊢
    rw [smul_neg,← h]
    abel
  · have hn := Ne.symm (P.minimum_vertices_ne hmin (P.pieces-1) P.pieces hi (by omega))
    exact radialPort_on_circle (P.vertices P.pieces) (P.vertices (P.pieces-1)) hn r

end PolygonalChain
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
theorem truncated_piece_vertex_disk_cases (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : Vertex) (e : Edge) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))) :
    (j=(graph.src e) ∧ x=(P e).startPort r) ∨
      (j=(graph.dst e) ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  have hp := drawing_chain_pieces_pos D e (P e)
  by_cases hfirst : j=(graph.src e) ∧ i.val=0
  · have hh := (P e).truncated_first_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hfirst.2] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inl ⟨hfirst.1,he⟩
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).first,hfirst.1] using he
  by_cases hlast : j=(graph.dst e) ∧ i.val+1=(P e).pieces
  · have hi : i.val=(P e).pieces-1 := by omega
    have hh := (P e).truncated_last_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hi,show (P e).pieces-1+1=(P e).pieces by omega] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inr (Or.inl ⟨hlast.1,he⟩)
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).last,hlast.1] using he
  · right; right
    have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
    have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
      nlinarith [(hshort e).2,sq_nonneg r]
    have hxi := (P e).truncated_piece_subset r hr hs ht i.val i.isLt hx
    by_contra h
    exact Set.disjoint_left.mp (hclear j e i (fun h => h.elim hfirst hlast)) (le_of_not_gt h) hxi

theorem truncated_path_vertex_disk_cases (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : Vertex) (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces)) :
    (j=(graph.src e) ∧ x=(P e).startPort r) ∨
      (j=(graph.dst e) ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece ((P e).truncatedVertices r) (P e).pieces
    (drawing_chain_pieces_pos D e (P e)) x hx
  exact truncated_piece_vertex_disk_cases D P hmin r hr hshort hclear j e ⟨i,hi⟩ x hxi

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem vertex_disks_crossing_free (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : Vertex) :
    Disjoint (closedRoundDisk (D.vertex j) r) (Paper170.crossingPoints D.toContinuousDrawing) := by
  apply Set.disjoint_left.mpr
  rintro x hxd ⟨e,f,hef,hxe,hxf⟩
  have hincident (g : Edge) (hxg : x ∈ Paper170.edgeInterior D.toContinuousDrawing g) :
      j=(graph.src g) ∨ j=(graph.dst g) := by
    have hx := edgeInterior_subset_range D.toContinuousDrawing g hxg
    rw [← drawing_chain_range_eq D.toContinuousDrawing g (P g)] at hx
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (P g).vertices (P g).pieces
      (drawing_chain_pieces_pos D.toContinuousDrawing g (P g)) x hx
    by_contra h
    have hbad : ¬ ((j=(graph.src g) ∧ i=0) ∨ (j=(graph.dst g) ∧ i+1=(P g).pieces)) :=
      fun hh => h (hh.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1))
    exact Set.disjoint_left.mp (hclear j g ⟨i,hi⟩ hbad) hxd hxi
  have hadj := incident_edges_adjacent j ⟨e,hincident e hxe⟩ ⟨f,hincident f hxf⟩
  have hh : x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f := ⟨hxe,hxf⟩
  rw [hnorm.eq_empty e f hef hadj] at hh
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
theorem truncated_range_subset_edgeInterior (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : Edge) :
    Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) ⊆ Paper170.edgeInterior D e := by
  intro x hx
  have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
  have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
    nlinarith [(hshort e).2,sq_nonneg r]
  apply edgeInterior_of_range_not_vertices D e x
  · exact ((P e).truncated (drawing_chain_pieces_pos D e (P e)) r hr hs ht).path_range_subset hx
  · intro j he
    rcases truncated_path_vertex_disk_cases D P hmin r hr hshort hclear j e x hx with ⟨hj,hp⟩ | ⟨hj,hp⟩ | hout
    · have hpi := drawing_chain_startPort_interior D e (P e) (hmin e) r hr hs
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · have hpi := drawing_chain_endPort_interior D e (P e) (hmin e) r hr ht
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · rw [he,sub_self] at hout
      have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
      rw [hz] at hout
      exact (sq_nonneg r).not_gt hout

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem range_subset_edgeInterior (e : Edge) : Set.range (V.path e) ⊆ Paper170.edgeInterior D e :=
  truncated_range_subset_edgeInterior D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance e

theorem direction_ne_zero (e : Edge) (i : ℕ) (hi : i < V.pieces e) :
    trackDirection (V.vertices e) i ≠ 0 :=
  (V.chain e).truncated_direction_ne_zero (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2 i hi

end VertexTruncation

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.VertexTruncation

theorem crossing_free_disks {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : Vertex) :
    Disjoint (closedRoundDisk (D.vertex j) V.radius) (Paper170.crossingPoints D.toContinuousDrawing) :=
  vertex_disks_crossing_free D hnorm V.chain V.radius V.piece_clearance j

theorem vertex_disk_cases {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)
    (j : Vertex) (e : Edge) (x : Plane) (hx : x ∈ Set.range (V.path e)) :
    (j=(graph.src e) ∧ x=V.startPort e) ∨ (j=(graph.dst e) ∧ x=V.endPort e) ∨
      V.radius^2 < squaredLength (x-D.vertex j) :=
  truncated_path_vertex_disk_cases D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance j e x hx

end Paper170Geometry.VertexTruncation

end
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

theorem circlePoint_one_add_x (t : ℝ) : 1+(circlePoint t).1 = 2/(1+t^2) := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_avoids_cut (t : ℝ) : (circlePoint t).1 ≠ -1 := by
  have hh : 0 < 1+(circlePoint t).1 := by
    rw [circlePoint_one_add_x]
    exact div_pos (by norm_num) (circle_denominator_pos t)
  linarith

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
-- module Solutions.OAIQ4_Cc.Crossing_OrientedSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem similarityPoint_injective (o u : Plane) (hu : u ≠ 0) : Function.Injective (similarityPoint o u) := by
  intro x y he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  dsimp [similarityPoint] at h₁ h₂
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hx : squaredLength u*(x.1-y.1)=0 := by
    dsimp [squaredLength]
    linear_combination u.1*h₁+u.2*h₂
  have hy : squaredLength u*(x.2-y.2)=0 := by
    dsimp [squaredLength]
    linear_combination -u.2*h₁+u.1*h₂
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hs))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hs))

theorem similarityPoint_segment (o u a b : Plane) (t : ℝ) :
    similarityPoint o u (segmentPoint a b t) =
      segmentPoint (similarityPoint o u a) (similarityPoint o u b) t := by
  apply Prod.ext <;> dsimp [similarityPoint,segmentPoint] <;> ring

theorem similarityPoint_det (o u a b c d : Plane) :
    det2 (similarityPoint o u b-similarityPoint o u a)
      (similarityPoint o u d-similarityPoint o u c) = squaredLength u*det2 (b-a) (d-c) := by
  dsimp [similarityPoint,squaredLength,det2]
  ring

theorem segmentsCrossProperly_similarity (o u a b c d : Plane) (hu : u ≠ 0) :
    SegmentsCrossProperly (similarityPoint o u a) (similarityPoint o u b)
      (similarityPoint o u c) (similarityPoint o u d) ↔ SegmentsCrossProperly a b c d := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  unfold SegmentsCrossProperly
  rw [similarityPoint_det,mul_ne_zero_iff]
  simp only [← similarityPoint_segment,(similarityPoint_injective o u hu).eq_iff]
  exact ⟨fun hh => ⟨hh.1.2,hh.2⟩,fun hh => ⟨⟨hs,hh.1⟩,hh.2⟩⟩

theorem segmentCrossingSign_similarity (o u a b c d : Plane) (hu : u ≠ 0) :
    segmentCrossingSign (similarityPoint o u a) (similarityPoint o u b)
      (similarityPoint o u c) (similarityPoint o u d) = segmentCrossingSign a b c d := by
  unfold segmentCrossingSign
  rw [segmentsCrossProperly_similarity o u a b c d hu]
  simp only [similarityPoint_det,mul_pos_iff_of_pos_left (squaredLength_pos u hu)]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleDeterminantOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem circle_det_formula (a b : ℝ) :
    det2 (circlePoint a) (circlePoint b) =
      2*(b-a)*(1+a*b)/((1+a^2)*(1+b^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  dsimp [det2,circlePoint]
  field_simp
  ring

theorem circle_det_pos_iff (a b : ℝ) (h : 0<1+a*b) :
    0<det2 (circlePoint a) (circlePoint b) ↔ a<b := by
  rw [circle_det_formula,div_pos_iff_of_pos_right (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)),
    mul_pos_iff_of_pos_right h,mul_pos_iff_of_pos_left (show (0 : ℝ)<2 by norm_num),sub_pos]

theorem circle_det_neg_iff (a b : ℝ) (h : 0<1+a*b) :
    det2 (circlePoint a) (circlePoint b)<0 ↔ b<a := by
  have hh : 0<1+b*a := by nlinarith
  have he := circle_det_pos_iff b a hh
  rw [det2_swap,neg_pos] at he
  exact he

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem circleOffset_on_circle (u : Plane) (hu : squaredLength u=1) (δ : ℝ) (hδ : |δ|≤1) :
    squaredLength (circleOffset u δ)=1 := by
  have hnon : 0 ≤ 1-δ^2 := by
    have h := abs_le.mp hδ
    nlinarith
  have hs := Real.sq_sqrt hnon
  have he : squaredLength (circleOffset u δ)=
      ((Real.sqrt (1-δ^2))^2+δ^2)*squaredLength u := by
    dsimp [squaredLength,circleOffset,rotateQuarter]
    ring
  rw [he,hu,hs]
  ring

theorem circleOffset_side (u : Plane) (hu : squaredLength u=1) (δ : ℝ) :
    det2 u (circleOffset u δ)=δ := by
  dsimp [circleOffset,det2,rotateQuarter,squaredLength] at *
  linear_combination δ*hu

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffsetParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem continuous_circleOffset (u : Plane) : Continuous (circleOffset u) := by
  change Continuous (fun δ : ℝ => Real.sqrt (1-δ^2) • u+δ • rotateQuarter u)
  fun_prop

@[simp] theorem offsetParameter_zero (a : ℝ) : offsetParameter a 0=a := by
  simp only [offsetParameter,circleOffset_zero,circlePoint_parameter]

theorem continuousAt_offsetParameter_zero (a : ℝ) : ContinuousAt (offsetParameter a) 0 := by
  apply ContinuousAt.div
  · exact (continuous_circleOffset (circlePoint a)).continuousAt.snd
  · exact continuousAt_const.add (continuous_circleOffset (circlePoint a)).continuousAt.fst
  · rw [circleOffset_zero,circlePoint_one_add_x]
    exact div_ne_zero (by norm_num) (ne_of_gt (circle_denominator_pos a))

theorem exists_circle_offset_parameter_radius (a ε : ℝ) (hε : 0<ε) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ δ : ℝ, |δ|<ρ →
      circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ ∧
      |offsetParameter a δ-a|<ε ∧
      (0<δ → a<offsetParameter a δ) ∧ (δ<0 → offsetParameter a δ<a) := by
  have hp := continuousAt_offsetParameter_zero a
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0, offsetParameter a δ ∈ Set.Ioo (a-ε) (a+ε) :=
    hp.eventually (isOpen_Ioo.mem_nhds (by rw [offsetParameter_zero]; constructor <;> linarith))
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ|<1 := by
    apply Metric.eventually_nhds_iff.mpr
    exact ⟨1,by norm_num,by intro delta; simp [Real.dist_eq]⟩
  have hcut : ∀ᶠ δ : ℝ in 𝓝 0, (circleOffset (circlePoint a) δ).1 ≠ -1 :=
    (continuous_circleOffset (circlePoint a)).continuousAt.fst.eventually_ne
      (by simpa using circlePoint_avoids_cut a)
  have hprodcont : ContinuousAt (fun δ : ℝ => 1+a*offsetParameter a δ) 0 :=
    continuousAt_const.add (continuousAt_const.mul hp)
  have hprod : ∀ᶠ δ : ℝ in 𝓝 0, 0<1+a*offsetParameter a δ :=
    continuousAt_const.eventually_lt hprodcont (by rw [offsetParameter_zero]; nlinarith [sq_nonneg a])
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0,
      circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ ∧
      |offsetParameter a δ-a|<ε ∧
      (0<δ → a<offsetParameter a δ) ∧ (δ<0 → offsetParameter a δ<a) := by
    filter_upwards [hnear,hsmall,hcut,hprod] with δ hnear hsmall hcut hprod
    have hunit : squaredLength (circlePoint a)=1 := circlePoint_on_unit_circle a
    have he := circlePoint_surjective_away_cut (circleOffset (circlePoint a) δ)
      (circleOffset_on_circle _ hunit δ hsmall.le) hcut
    change circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ at he
    have hdet : det2 (circlePoint a) (circlePoint (offsetParameter a δ))=δ := by
      rw [he]
      exact circleOffset_side _ hunit δ
    refine ⟨he,?_,?_,?_⟩
    · exact abs_lt.mpr ⟨by linarith [hnear.1],by linarith [hnear.2]⟩
    · intro hδ
      apply (circle_det_pos_iff a _ hprod).mp
      rwa [hdet]
    · intro hδ
      apply (circle_det_neg_iff a _ hprod).mp
      rwa [hdet]
  obtain ⟨ρ,hρ,hh⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ρ,hρ,fun δ hδ => hh (by simpa [Real.dist_eq] using hδ)⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteScaledRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem finite_scaled_radius {ι : Type*} [Fintype ι] (a r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, |t|<δ → ∀ i, |a i*t| < r i := by
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ
    (fun i => r i/(|a i|+1)) (fun i _ => div_pos (hr i) (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro t ht i
  have hd : 0 < |a i|+1 := by positivity
  have hb : δ*(|a i|+1) < r i := (lt_div_iff₀ hd).mp (hbound i (Finset.mem_univ _))
  calc
    |a i*t| = |t| *|a i| := by rw [abs_mul,mul_comm]
    _ ≤ |t| *(|a i|+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    _ < δ*(|a i|+1) := mul_lt_mul_of_pos_right ht hd
    _ < r i := hb

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ChordPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem chordEndpointPairing_reverse_left (a b c d : ℝ) :
    chordEndpointPairing b a c d = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  ring

theorem circle_chords_separated (a b c d : ℝ) (hab : a<b) (hbc : b < c) (hcd : c<d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 0 := by
  have hh := not_segmentsCrossProperly_of_same_side (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d)
    (Or.inl ⟨circle_orient_pos a b c hab hbc,circle_orient_pos a b d hab (hbc.trans hcd)⟩)
  simp [segmentCrossingSign,hh]

theorem circle_chords_nested (a c d b : ℝ) (hac : a < c) (hcd : c<d) (hdb : d<b) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 0 := by
  have hc : orient2 (circlePoint a) (circlePoint b) (circlePoint c) < 0 := by
    rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a c b hac (hcd.trans hdb))
  have hd : orient2 (circlePoint a) (circlePoint b) (circlePoint d) < 0 := by
    rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a d b (hac.trans hcd) hdb)
  have hh := not_segmentsCrossProperly_of_same_side _ _ _ _ (Or.inr ⟨hc,hd⟩)
  simp [segmentCrossingSign,hh]

theorem circle_chord_pairing_ordered (a b c d : ℝ) (hab : a<b) (hcd : c<d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      chordEndpointPairing a b c d := by
  by_cases hac' : a < c
  · by_cases hbc' : b < c
    · rw [circle_chords_separated a b c d hab hbc' hcd]
      unfold chordEndpointPairing orderSign
      split_ifs <;> norm_num <;> linarith
    · have hcb : c<b := lt_of_le_of_ne (le_of_not_gt hbc') (Ne.symm hbc)
      by_cases hbd' : b<d
      · rw [circle_chords_alternating_positive a c b d hac' hcb hbd']
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
      · have hdb : d<b := lt_of_le_of_ne (le_of_not_gt hbd') (Ne.symm hbd)
        rw [circle_chords_nested a c d b hac' hcd hdb]
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
  · have hca : c<a := lt_of_le_of_ne (le_of_not_gt hac') (Ne.symm hac)
    by_cases hda : d<a
    · rw [segmentCrossingSign_swap, circle_chords_separated c d a b hcd hda hab]
      unfold chordEndpointPairing orderSign
      split_ifs <;> norm_num <;> linarith
    · have had' : a<d := lt_of_le_of_ne (le_of_not_gt hda) had
      by_cases hdb : d<b
      · rw [segmentCrossingSign_swap, circle_chords_alternating_positive c a d b hca had' hdb]
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
      · have hbd' : b<d := lt_of_le_of_ne (le_of_not_gt hdb) hbd
        rw [segmentCrossingSign_swap, circle_chords_nested c a b d hca hab hbd']
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ChordOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentCrossingSign_reverse_right (a b c d : Plane) :
    segmentCrossingSign a b d c = -segmentCrossingSign a b c d := by
  rw [segmentCrossingSign_swap d c a b,segmentCrossingSign_reverse_left c d a b,
    neg_neg,segmentCrossingSign_swap a b c d]

theorem chordEndpointPairing_reverse_right (a b c d : ℝ) :
    chordEndpointPairing a b d c = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  ring

theorem circle_chord_pairing_first_ordered (a b c d : ℝ) (hab : a<b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      chordEndpointPairing a b c d := by
  rcases lt_or_gt_of_ne hcd with hcd | hdc
  · exact circle_chord_pairing_ordered a b c d hab hcd hac had hbc hbd
  · have hh := circle_chord_pairing_ordered a b d c hab hdc had hac hbd hbc
    rw [segmentCrossingSign_reverse_right, chordEndpointPairing_reverse_right] at hh
    exact neg_injective hh

theorem circle_chord_pairing (a b c d : ℝ) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      (orderSign a c-orderSign a d-orderSign b c+orderSign b d)/2 := by
  change _ = chordEndpointPairing a b c d
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact circle_chord_pairing_first_ordered a b c d hab hcd hac had hbc hbd
  · have hh := circle_chord_pairing_first_ordered b a c d hba hcd hbc hbd hac had
    rw [segmentCrossingSign_reverse_left, chordEndpointPairing_reverse_left] at hh
    exact neg_injective hh

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GeneralOrderAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem orderSign_of_close (a b z ε : ℝ) (hgap : ε < |a-b|) (hz : |z-b| < ε) :
    orderSign a z = orderSign a b := by
  have ha : a ≠ b := by intro h; subst a; simp at hgap; have := abs_nonneg (z-b); linarith
  have hzb := abs_lt.mp hz
  rcases lt_or_gt_of_ne ha with hab | hba
  · have hgz : a < z := by rw [abs_of_neg (sub_neg.mpr hab)] at hgap; linarith
    simp [orderSign,hab,hgz]
  · have hgz : z < a := by rw [abs_of_pos (sub_pos.mpr hba)] at hgap; linarith
    simp [orderSign,not_lt.mpr hba.le,not_lt.mpr hgz.le,hba,hgz]

theorem orderSign_straddling_average (a b p q ε : ℝ)
    (hgap : a ≠ b → ε < |a-b|) (hp : |p-b| < ε) (hq : |q-b| < ε)
    (hstraddle : (p<b ∧ b<q) ∨ (q<b ∧ b<p)) :
    (orderSign a p+orderSign a q)/2 = orderSign a b := by
  by_cases hab : a=b
  · subst a
    rcases hstraddle with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · simp [orderSign,hp,hq,not_lt.mpr hp.le]
    · simp [orderSign,hp,hq,not_lt.mpr hq.le]
  · rw [orderSign_of_close a b p ε (hgap hab) hp,orderSign_of_close a b q ε (hgap hab) hq]
    ring

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GeneralSpokeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*}

theorem small_perturbation_injective (node f : ι → ℝ)
    (ε : ℝ) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hf : ∀ i, |f i-node i| < ε) : Function.Injective f := by
  intro i j hij
  by_contra hne
  have h₀ := hf i
  have h₁ := hf j
  have hh := abs_sub_le (node i) (f i) (node j)
  rw [abs_sub_comm (node i) (f i),hij] at hh
  have hg := hgap i j hne
  rw [hij] at h₀
  linarith

theorem fixed_node_ne_small_perturbation (node f : ι → ℝ)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hf : ∀ i, |f i-node i| < ε) (hself : ∀ i, node i ≠ f i) (i j : ι) : node i ≠ f j := by
  by_cases hij : i=j
  · subst j
    exact hself i
  · intro he
    have hg := hgap i j hij
    have hh := hf j
    rw [← he] at hh
    linarith

theorem local_spoke_straddling_average (node plus minus : ι → ℝ) (hn : Function.Injective node)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → 2*ε < |node i-node j|)
    (hp : ∀ i, |plus i-node i| < ε) (hm : ∀ i, |minus i-node i| < ε)
    (hs : ∀ i, (plus i<node i ∧ node i < minus i) ∨ (minus i<node i ∧ node i<plus i))
    (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d) :
    (segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
        (circlePoint (plus c)) (circlePoint (plus d)) +
      segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
        (circlePoint (minus c)) (circlePoint (minus d))) / 2 =
      chordEndpointPairing (node a) (node b) (node c) (node d) := by
  have hpne (i : ι) : node i ≠ plus i := by
    rcases hs i with h | h
    · exact ne_of_gt h.1
    · exact ne_of_lt h.2
  have hmne (i : ι) : node i ≠ minus i := by
    rcases hs i with h | h
    · exact ne_of_lt h.2
    · exact ne_of_gt h.1
  have hpall := fixed_node_ne_small_perturbation node plus ε hε hgap hp hpne
  have hmall := fixed_node_ne_small_perturbation node minus ε hε hgap hm hmne
  have hpinj := small_perturbation_injective node plus ε hgap hp
  have hminj := small_perturbation_injective node minus ε hgap hm
  rw [circle_chord_pairing _ _ _ _ (hn.ne hab) (hpinj.ne hcd) (hpall a c) (hpall a d) (hpall b c) (hpall b d),
    circle_chord_pairing _ _ _ _ (hn.ne hab) (hminj.ne hcd) (hmall a c) (hmall a d) (hmall b c) (hmall b d)]
  have hav (i j : ι) : (orderSign (node i) (plus j)+orderSign (node i) (minus j))/2 = orderSign (node i) (node j) := by
    apply orderSign_straddling_average _ _ _ _ ε _ (hp j) (hm j) (hs j)
    intro hne
    have hg := hgap i j (fun he => hne (congrArg node he))
    linarith
  have h₁ := hav a c
  have h₂ := hav a d
  have h₃ := hav b c
  have h₄ := hav b d
  unfold chordEndpointPairing
  linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PhysicalSpokeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_physical_spoke_average (node scale : ι → ℝ) (hn : Function.Injective node)
    (hs : ∀ i, scale i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
      (segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
          (circleOffset (circlePoint (node c)) (scale c*t))
          (circleOffset (circlePoint (node d)) (scale d*t)) +
        segmentCrossingSign (circlePoint (node a)) (circlePoint (node b))
          (circleOffset (circlePoint (node c)) (scale c*(-t)))
          (circleOffset (circlePoint (node d)) (scale d*(-t)))) / 2 =
        chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨γ,hγ,hgap⟩ := finite_node_separation node hn
  let ε := γ/3
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsep (i j : ι) (hij : i ≠ j) : 2*ε < |node i-node j| := by
    have hh := hgap i j hij
    dsimp [ε]
    linarith
  have hex (i : ι) := exists_circle_offset_parameter_radius (node i) ε hε
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_scaled_radius scale radius hpos
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ a b c d hab hcd
  have hbt : |t| < δ := by simpa [abs_of_pos ht] using htδ
  have hbmt : |-t| < δ := by simpa [abs_neg] using hbt
  let plus : ι → ℝ := fun i => offsetParameter (node i) (scale i*t)
  let minus : ι → ℝ := fun i => offsetParameter (node i) (scale i*(-t))
  have hp (i : ι) := hprop i (scale i*t) (hbound t hbt i)
  have hm (i : ι) := hprop i (scale i*(-t)) (hbound (-t) hbmt i)
  have hpnear (i : ι) : |plus i-node i| < ε := (hp i).2.1
  have hmnear (i : ι) : |minus i-node i| < ε := (hm i).2.1
  have hstraddle (i : ι) : (plus i<node i ∧ node i < minus i) ∨
      (minus i<node i ∧ node i<plus i) := by
    have hne : scale i*t ≠ 0 := mul_ne_zero (hs i) (ne_of_gt ht)
    rcases lt_or_gt_of_ne hne with hi | hi
    · exact Or.inl ⟨(hp i).2.2.2 hi,(hm i).2.2.1 (by nlinarith)⟩
    · exact Or.inr ⟨(hm i).2.2.2 (by nlinarith),(hp i).2.2.1 hi⟩
  have havg := local_spoke_straddling_average node plus minus hn ε hε hsep hpnear hmnear hstraddle a b c d hab hcd
  have hpe (i : ι) : circlePoint (plus i)=circleOffset (circlePoint (node i)) (scale i*t) := (hp i).1
  have hme (i : ι) : circlePoint (minus i)=circleOffset (circlePoint (node i)) (scale i*(-t)) := (hm i).1
  simpa only [hpe,hme] using havg

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PhysicalCircleAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem physical_spoke_average_in_similarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o u : Plane) (hu : u ≠ 0) (node scale : ι → ℝ)
    (hn : Function.Injective node) (hs : ∀ i, scale i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : ι, a ≠ b → c ≠ d →
      (segmentCrossingSign
          (similarityPoint o u (circlePoint (node a))) (similarityPoint o u (circlePoint (node b)))
          (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*t)))
          (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*t))) +
        segmentCrossingSign
          (similarityPoint o u (circlePoint (node a))) (similarityPoint o u (circlePoint (node b)))
          (similarityPoint o u (circleOffset (circlePoint (node c)) (scale c*(-t))))
          (similarityPoint o u (circleOffset (circlePoint (node d)) (scale d*(-t))))) / 2 =
        chordEndpointPairing (node a) (node b) (node c) (node d) := by
  obtain ⟨δ,hδ,hh⟩ := exists_physical_spoke_average node scale hn hs
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [segmentCrossingSign_similarity o u _ _ _ _ hu] using hh t ht hsmall a b c d hab hcd

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleOffsetLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem similarity_circleOffset (o u v : Plane) (δ : ℝ) :
    similarityPoint o u (circleOffset v δ)-o =
      Real.sqrt (1-δ^2) • (similarityPoint o u v-o) +
        δ • rotateQuarter (similarityPoint o u v-o) := by
  apply Prod.ext <;> dsimp [similarityPoint,circleOffset,rotateQuarter] <;> ring

theorem rotated_parallel_det_ne_zero (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : det2 d (rotateQuarter w) ≠ 0 := by
  have hp := vector_parallel_of_det_zero d w hd hpar
  have hc : dot2 d w/squaredLength d ≠ 0 := by
    intro h
    rw [h,zero_smul] at hp
    exact hw hp
  have he : det2 d (rotateQuarter w)=(dot2 d w/squaredLength d)*squaredLength d := by
    conv_lhs => rw [hp]
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [he]
  exact mul_ne_zero hc (ne_of_gt (squaredLength_pos d hd))

theorem circleTrackScale_ne_zero (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : circleTrackScale d w ≠ 0 :=
  inv_ne_zero (rotated_parallel_det_ne_zero d w hd hw hpar)

theorem circleOffset_track_level (o u v d : Plane) (hd : d ≠ 0)
    (hw : similarityPoint o u v-o ≠ 0)
    (hpar : det2 d (similarityPoint o u v-o)=0) (ε : ℝ) :
    det2 d (similarityPoint o u (circleOffset v (circleTrackScale d (similarityPoint o u v-o)*ε))-
      similarityPoint o u v)=ε := by
  let w := similarityPoint o u v-o
  let δ := circleTrackScale d w*ε
  have he : similarityPoint o u (circleOffset v δ)-similarityPoint o u v =
      (Real.sqrt (1-δ^2)-1) • w+δ • rotateQuarter w := by
    have hh := similarity_circleOffset o u v δ
    calc
      _ = (similarityPoint o u (circleOffset v δ)-o)-(similarityPoint o u v-o) := by abel
      _ = Real.sqrt (1-δ^2) • w+δ • rotateQuarter w-w := by rw [hh]
      _ = _ := by rw [sub_smul,one_smul]; abel
  change det2 d (similarityPoint o u (circleOffset v δ)-similarityPoint o u v)=ε
  rw [he,det2_add_right,det2_smul_right,det2_smul_right,hpar,mul_zero,zero_add]
  have hn := rotated_parallel_det_ne_zero d w hd hw hpar
  dsimp [δ,circleTrackScale]
  field_simp

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_MovingSegmentStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem moving_endpoints_tendsto (C D : ℝ → Plane) (c d : Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d) :
    Filter.Tendsto (fun t : ℝ => (C t,D t)) (𝓝 0) (𝓝 (c,d)) := by
  simpa [ContinuousAt,hC0,hD0] using hC.prodMk hD

theorem eventually_moving_disjoint_segments (a b c d : Plane) (C D : ℝ → Plane)
    (hC : ContinuousAt C 0) (hD : ContinuousAt D 0) (hC0 : C 0=c) (hD0 : D 0=d)
    (h : ¬ ClosedSegmentsMeet a b c d) :
    ∀ᶠ t : ℝ in 𝓝 0, ¬ ClosedSegmentsMeet a b (C t) (D t) := by
  have hn : (c,d) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 a b}ᶜ := by
    intro hx
    exact h ((closedSegmentsMeet_symm c d a b).mp hx)
  have he := (moving_endpoints_tendsto C D c d hC hD hC0 hD0).eventually
    ((isClosed_closedSegmentsMeet a b).isOpen_compl.mem_nhds hn)
  filter_upwards [he] with t ht
  intro hx
  exact ht ((closedSegmentsMeet_symm a b _ _).mp hx)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteMovingPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem finite_moving_points_separation {ι : Type*} [Fintype ι]
    (point : ι → ℝ → Plane) (hc : ∀ i, Continuous (point i))
    (hinj : Function.Injective (fun i => point i 0)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ i j : ι, i ≠ j →
      point i 0 ≠ point j ε ∧ point i ε ≠ point j ε := by
  classical
  let Pair := {ij : ι × ι // ij.1 ≠ ij.2}
  have hevent (p : Pair) : ∀ᶠ ε : ℝ in 𝓝 0,
      point p.val.1 0 ≠ point p.val.2 ε ∧ point p.val.1 ε ≠ point p.val.2 ε := by
    have hne := hinj.ne p.property
    have h₁ := (hc p.val.2).continuousAt.eventually_ne hne.symm
    have hd : Continuous (fun ε : ℝ => point p.val.1 ε-point p.val.2 ε) := (hc _).sub (hc _)
    have h₂ := hd.continuousAt.eventually_ne (sub_ne_zero.mpr hne)
    filter_upwards [h₁,h₂] with ε h₁ h₂
    exact ⟨h₁.symm,sub_ne_zero.mp h₂⟩
  have hex (p : Pair) := Metric.eventually_nhds_iff.mp (hevent p)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun p _ => hpos p)
  refine ⟨δ,hδ,?_⟩
  intro ε hε i j hij
  exact hprop ⟨(i,j),hij⟩ (by
    simpa [Real.dist_eq] using hε.trans (hbound ⟨(i,j),hij⟩ (Finset.mem_univ _)))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CircleConnectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_radial (u : Plane) (hu : squaredLength u=1) (a b : ℝ) :
    squaredLength (a • u+b • rotateQuarter u)=a^2+b^2 := by
  have he : squaredLength (a • u+b • rotateQuarter u)=(a^2+b^2)*squaredLength u := by
    dsimp [squaredLength,rotateQuarter]
    ring
  rw [he,hu,mul_one]

theorem circleConnector_parameterization (u : Plane) (δ t : ℝ) :
    segmentPoint (circleOffset u δ) (circleTangentOffset u δ) t =
      ((1-t)*Real.sqrt (1-δ^2)+t) • u+δ • rotateQuarter u := by
  apply Prod.ext <;> dsimp [segmentPoint,circleOffset,circleTangentOffset,rotateQuarter] <;> ring

theorem circleConnector_strictly_outside (u : Plane) (hu : squaredLength u=1)
    (δ : ℝ) (hδ : |δ|<1) (hne : δ ≠ 0) (t : ℝ) (ht : 0<t) :
    1 < squaredLength (segmentPoint (circleOffset u δ) (circleTangentOffset u δ) t) := by
  have hnon : 0 ≤ 1-δ^2 := by have hh := abs_lt.mp hδ; nlinarith
  have hs := Real.sq_sqrt hnon
  have hs0 := Real.sqrt_nonneg (1-δ^2)
  have hs1 : Real.sqrt (1-δ^2) < 1 := by nlinarith [sq_pos_of_ne_zero hne]
  have hA : Real.sqrt (1-δ^2) < (1-t)*Real.sqrt (1-δ^2)+t := by
    have hmul := mul_pos ht (sub_pos.mpr hs1)
    nlinarith
  rw [circleConnector_parameterization,squaredLength_radial u hu]
  nlinarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TangentTrackIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem det2_rotateQuarter_self (d : Plane) : det2 d (rotateQuarter d)=squaredLength d := by
  dsimp [det2,rotateQuarter,squaredLength]
  ring

theorem normalShift_eq_circleTrackScale (d w : Plane) (hd : d ≠ 0) (hw : w ≠ 0)
    (hpar : det2 d w=0) : normalShift d=circleTrackScale d w • rotateQuarter w := by
  let c := dot2 d w/squaredLength d
  have hp : w=c • d := vector_parallel_of_det_zero d w hd hpar
  have hc : c ≠ 0 := by
    intro h
    rw [h,zero_smul] at hp
    exact hw hp
  have hrot : rotateQuarter w=c • rotateQuarter d := by
    rw [hp]
    apply Prod.ext
    · dsimp [rotateQuarter]
      ring
    · rfl
  have hL := ne_of_gt (squaredLength_pos d hd)
  unfold normalShift circleTrackScale
  rw [hrot,det2_smul_right,det2_rotateQuarter_self,smul_smul]
  congr 1
  field_simp

theorem similarity_circleTangentOffset (o u v : Plane) (δ : ℝ) :
    similarityPoint o u (circleTangentOffset v δ)=
      similarityPoint o u v+δ • rotateQuarter (similarityPoint o u v-o) := by
  apply Prod.ext <;> dsimp [similarityPoint,circleTangentOffset,rotateQuarter] <;> ring

theorem tangentOffset_eq_normalShift (o u v d : Plane) (hd : d ≠ 0)
    (hw : similarityPoint o u v-o ≠ 0) (hpar : det2 d (similarityPoint o u v-o)=0)
    (ε : ℝ) :
    similarityPoint o u (circleTangentOffset v (circleTrackScale d (similarityPoint o u v-o)*ε))=
      similarityPoint o u v+ε • normalShift d := by
  rw [similarity_circleTangentOffset,normalShift_eq_circleTrackScale d _ hd hw hpar,smul_smul]
  congr 2
  ring

theorem similarityPoint_squaredLength (o u x : Plane) :
    squaredLength (similarityPoint o u x-o)=squaredLength u*squaredLength x := by
  dsimp [similarityPoint,squaredLength]
  ring

theorem physical_circleConnector_strictly_outside (o u v : Plane) (hu : u ≠ 0)
    (hv : squaredLength v=1) (δ : ℝ) (hδ : |δ|<1) (hne : δ ≠ 0)
    (t : ℝ) (ht : 0<t) :
    squaredLength u < squaredLength
      (segmentPoint (similarityPoint o u (circleOffset v δ))
        (similarityPoint o u (circleTangentOffset v δ)) t-o) := by
  rw [← similarityPoint_segment,similarityPoint_squaredLength]
  have hh := circleConnector_strictly_outside v hv δ hδ hne t ht
  nlinarith [squaredLength_pos u hu]

end Zarankiewicz

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

/-! Fixed graph-edge directions at both endpoint circles, including the incoming right-vertex direction. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem drawingSpokeDirection_port_parallel (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ) (j : Vertex) (e : IncidentEdges graph j)
    (hpos : 0 < (P e.val).pieces) :
    det2 (drawingSpokeDirection D P j e) (drawingSpokePort D P r j e-D.vertex j)=0 := by
  unfold drawingSpokeDirection drawingSpokePort
  split_ifs with h
  · have hc : D.vertex j=(P e.val).vertices 0 := (congrArg D.vertex h).trans (P e.val).first.symm
    rw [hc]
    change det2 ((P e.val).vertices 1-(P e.val).vertices 0)
      (radialPort ((P e.val).vertices 0) ((P e.val).vertices 1) r-(P e.val).vertices 0)=0
    rw [radialPort_sub,det2_smul_right,det2_self,mul_zero]
  · have he := e.property.resolve_left h
    have hc : D.vertex j=(P e.val).vertices (P e.val).pieces :=
      (congrArg D.vertex he).trans (P e.val).last.symm
    rw [hc]
    simp only [trackDirection,PolygonalChain.endPort,
      show (P e.val).pieces-1+1=(P e.val).pieces by omega,radialPort_sub,det2_smul_right]
    have hn : (P e.val).vertices ((P e.val).pieces-1)-(P e.val).vertices (P e.val).pieces =
        -((P e.val).vertices (P e.val).pieces-(P e.val).vertices ((P e.val).pieces-1)) := by abel
    rw [hn,det2_neg_right,det2_self,neg_zero,mul_zero]

end Paper170Geometry

end
end

section

/-! The actual endpoint directions of truncated tracks, with their common fixed edge orientation. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokeIndex_lt (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeIndex j e < V.pieces e.val := by
  have hp := V.pieces_pos e.val
  unfold spokeIndex
  split_ifs <;> omega

theorem spokeDirection_ne_zero (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeDirection j e ≠ 0 := V.direction_ne_zero e.val _ (V.spokeIndex_lt j e)

theorem spokeDirection_eq_scale (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeDirection j e =
      (V.chain e.val).truncatedScale V.radius (V.spokeIndex j e) •
        drawingSpokeDirection D V.chain j e := by
  change trackDirection ((V.chain e.val).truncatedVertices V.radius) (V.spokeIndex j e)=_
  rw [(V.chain e.val).truncated_direction V.radius _ (V.spokeIndex_lt j e)]
  congr 1
  unfold spokeIndex drawingSpokeDirection
  split_ifs <;> rfl

theorem spokePort_circle (j : Vertex) (e : IncidentEdges graph j) :
    squaredLength (V.spokePort j e-D.vertex j)=V.radius^2 :=
  drawingSpokePort_circle D V.chain V.minimal V.radius j e

theorem spokePort_ne_center (j : Vertex) (e : IncidentEdges graph j) :
    V.spokePort j e-D.vertex j ≠ 0 := by
  intro h
  have hc := V.spokePort_circle j e
  rw [h] at hc
  have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
  rw [hz] at hc
  nlinarith [V.radius_pos]

theorem spokeDirection_parallel (j : Vertex) (e : IncidentEdges graph j) :
    det2 (V.spokeDirection j e) (V.spokePort j e-D.vertex j)=0 := by
  rw [V.spokeDirection_eq_scale,det2_smul_left]
  have hp := drawingSpokeDirection_port_parallel D V.chain V.radius j e (V.pieces_pos e.val)
  change det2 (drawingSpokeDirection D V.chain j e) (V.spokePort j e-D.vertex j)=0 at hp
  rw [hp,mul_zero]

theorem spokeScale_ne_zero (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeScale j e ≠ 0 :=
  circleTrackScale_ne_zero _ _ (V.spokeDirection_ne_zero j e)
    (V.spokePort_ne_center j e) (V.spokeDirection_parallel j e)

end Paper170Geometry.VertexTruncation

end
end

section

/-! One actual oriented circle chart at each vertex, chosen before any cycle or pair of chords. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable {D : Paper170.ContinuousDrawing graph}

namespace TruncatedSpokeCoordinates
variable {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

theorem tangentPort_eq (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    C.tangentPort j e ε = similarityPoint (D.vertex j) (C.frame j)
      (circleTangentOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)) := by
  have hh := tangentOffset_eq_normalShift (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,tangentPort] using hh.symm

theorem shiftedPort_level (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.shiftedPort j e ε-V.spokePort j e)=ε := by
  have hh := circleOffset_track_level (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,shiftedPort] using hh

theorem shiftedPort_circle (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ)
    (hε : |V.spokeScale j e*ε| ≤ 1) :
    squaredLength (C.shiftedPort j e ε-D.vertex j)=V.radius^2 := by
  unfold shiftedPort
  rw [similarityPoint_squaredLength,circleOffset_on_circle _ (circlePoint_on_unit_circle _) _ hε,
    mul_one,C.frame_length]

theorem connector_strictly_outside (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ)
    (hε : |V.spokeScale j e*ε| < 1) (hne : ε ≠ 0) (t : ℝ) (ht : 0<t) :
    V.radius^2 < squaredLength (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-D.vertex j) := by
  rw [C.tangentPort_eq]
  have hh := physical_circleConnector_strictly_outside (D.vertex j) (C.frame j)
    (circlePoint (C.node j e)) (C.frame_ne_zero j) (circlePoint_on_unit_circle _)
    (V.spokeScale j e*ε) hε (mul_ne_zero (V.spokeScale_ne_zero j e) hne) t ht
  simpa only [C.frame_length,shiftedPort] using hh

theorem exists_vertex_average_radius [Fintype Edge] (j : Vertex) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : IncidentEdges graph j,
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := physical_spoke_average_in_similarity (D.vertex j) (C.frame j) (C.frame_ne_zero j)
    (C.node j) (V.spokeScale j) (C.node_injective j) (V.spokeScale_ne_zero j)
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [C.point_eq,shiftedPort] using hh t ht hsmall a b c d hab hcd

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! The ends of each actual shifted track are precisely the ends of its two circle connectors. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokePort_left (e : Edge) :
    V.spokePort ((graph.src e)) (V.leftIncident e)=V.startPort e := by
  simp [spokePort,drawingSpokePort,leftIncident,startPort]

theorem spokePort_right (e : Edge) :
    V.spokePort ((graph.dst e)) (V.rightIncident e)=V.endPort e := by
  simp [spokePort,drawingSpokePort,rightIncident,endPort,(graph.loopless e).symm]

end Paper170Geometry.VertexTruncation

end
end

section

/-! Every original/shifted vertex endpoint is distinct for either sufficiently small nonzero displacement. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_shiftedPort (j : Vertex) (e : IncidentEdges graph j) :
    Continuous (C.shiftedPort j e) := by
  change Continuous (fun ε : ℝ => similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)))
  dsimp [similarityPoint,circleOffset,rotateQuarter]
  fun_prop

theorem shiftedPort_zero (j : Vertex) (e : IncidentEdges graph j) :
    C.shiftedPort j e 0=V.spokePort j e := by
  simp only [shiftedPort,mul_zero,circleOffset_zero,C.point_eq]

theorem shiftedPort_ne_original (j : Vertex) (e : IncidentEdges graph j)
    (ε : ℝ) (hε : ε ≠ 0) : C.shiftedPort j e ε ≠ V.spokePort j e := by
  intro he
  have hh := C.shiftedPort_level j e ε
  rw [he,sub_self] at hh
  have hz : det2 (V.spokeDirection j e) (0 : Plane)=0 := by simp [det2]
  rw [hz] at hh
  exact hε hh.symm

theorem exists_endpoint_separation_radius [Fintype Edge] (j : Vertex) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ e f : IncidentEdges graph j, V.spokePort j e ≠ C.shiftedPort j f ε) ∧
      Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e ε) := by
  have hinj : Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e 0) := by
    intro e f he
    have hh : circlePoint (C.node j e)=circlePoint (C.node j f) := by
      apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
      simpa only [shiftedPort,mul_zero,circleOffset_zero] using he
    exact C.node_injective j (circlePoint_injective hh)
  obtain ⟨δ,hδ,hh⟩ := finite_moving_points_separation (C.shiftedPort j)
    (C.continuous_shiftedPort j) hinj
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  constructor
  · intro e f
    by_cases hef : e=f
    · subst f
      exact (C.shiftedPort_ne_original j e ε hε).symm
    · simpa only [C.shiftedPort_zero] using (hh ε hsmall e f hef).1
  · intro e f he
    by_contra hef
    exact (hh ε hsmall e f hef).2 he

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Signed intersections are actual segment-traversal sums; their support is controlled by spatial crossing points. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
open scoped BigOperators
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem piece_subset_range (e : Edge) (i : ℕ) (hi : i<V.pieces e) :
    segment ℝ (V.vertices e i) (V.vertices e (i+1)) ⊆ Set.range (V.path e) := by
  exact ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos
    (V.weak_short e).1 (V.weak_short e).2).piece_subset_path_range i hi

end Paper170Geometry.VertexTruncation

end
end

section

/-! An actual boundary port belongs to exactly its incident truncated endpoint piece. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation

theorem spokePort_interior {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)
    (j : Vertex) (f : IncidentEdges graph j) : V.spokePort j f ∈ Paper170.edgeInterior D f.val :=
  drawingSpokePort_interior D V.chain V.minimal V.radius V.radius_pos V.weak_short j f

theorem spokePort_piece_unique {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : Vertex) (f : IncidentEdges graph j)
    (e : Edge) (i : Fin (V.pieces e))
    (hx : V.spokePort j f ∈ segment ℝ (V.vertices e i.val) (V.vertices e (i.val+1))) :
    e=f.val ∧ i.val=V.spokeIndex j f := by
  have hcircle : V.spokePort j f ∈ closedRoundDisk (D.vertex j) V.radius := by
    change squaredLength (V.spokePort j f-D.vertex j) ≤ V.radius^2
    rw [V.spokePort_circle]
  have he : e=f.val := by
    by_contra hef
    have hcross : V.spokePort j f ∈ Paper170.crossingPoints D.toContinuousDrawing :=
      ⟨e,f.val,hef,V.range_subset_edgeInterior e (V.piece_subset_range e i.val i.isLt hx),V.spokePort_interior j f⟩
    exact Set.disjoint_left.mp (V.crossing_free_disks hnorm j) hcircle hcross
  have hcase : (j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=V.pieces e) := by
    by_contra hh
    have hold := (V.chain e).truncated_piece_subset V.radius V.radius_pos
      (V.weak_short e).1 (V.weak_short e).2 i.val i.isLt hx
    exact Set.disjoint_left.mp (V.piece_clearance j e i hh) hcircle hold
  refine ⟨he,?_⟩
  unfold spokeIndex
  split_ifs with hj
  · rcases hcase with hh | hh
    · exact hh.2
    · have hbad : graph.src f.val = graph.dst e := hj.symm.trans hh.1
      exact False.elim ((graph.loopless e) ((congrArg graph.src he).trans hbad))
  · rcases hcase with hh | hh
    · exact False.elim (hj (hh.1.trans (congrArg (fun g : Edge => (graph.src g)) he)))
    · have hn : V.pieces e=V.pieces f.val := congrArg V.pieces he
      omega

end Paper170Geometry.VertexTruncation

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SegmentTraversalReversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentPairTransverse_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    SegmentPairTransverse a b c d := by
  intro s hs t ht he
  exact False.elim (h ⟨s,hs,t,ht,he⟩)

theorem segmentCrossingSign_eq_zero_of_not_meet (a b c d : Plane) (h : ¬ ClosedSegmentsMeet a b c d) :
    segmentCrossingSign a b c d=0 := by
  have hn : ¬ SegmentsCrossProperly a b c d := fun hh => h (closedSegmentsMeet_of_proper _ _ _ _ hh)
  simp [segmentCrossingSign,hn]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_DartPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Drawn-edge chains, dart-path realizations, and endpoint-flag pairing. -/

section

/-! Actual closed polygonal realizations of cyclic graph darts, with a chord at every vertex passage. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem dartPassage_ne (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ)
    (hne : OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i)) :
    dartTargetIncident (d i) ≠ dartPassageNext d hd i := by
  intro he
  exact hne (congrArg Subtype.val he).symm

end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_MovingDiskClearance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem eventually_moving_segment_outside_disk (a b : ℝ → Plane) (ha : Continuous a)
    (hb : Continuous b) (z : Plane) (r : ℝ)
    (hout : segment ℝ (a 0) (b 0) ⊆ {x | r^2 < squaredLength (x-z)}) :
    ∀ᶠ ε : ℝ in 𝓝 0, segment ℝ (a ε) (b ε) ⊆ {x | r^2 < squaredLength (x-z)} := by
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      r^2 < squaredLength (segmentPoint (a ε) (b ε) t-z) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc : Continuous (fun p : ℝ × ℝ => squaredLength (segmentPoint (a p.1) (b p.1) p.2-z)) := by
      dsimp [squaredLength,segmentPoint]
      fun_prop
    apply continuousAt_const.eventually_lt hc.continuousAt
    apply hout
    rw [← Path.range_segment]
    refine ⟨⟨t,ht⟩,?_⟩
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]
  filter_upwards [hevent] with ε hε
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  simpa only [Set.mem_ofPred_eq,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hε t.val t.property

theorem exists_shifted_segment_disk_radius (a b qa qb z : Plane) (r : ℝ)
    (hdis : Disjoint (closedRoundDisk z r) (segment ℝ a b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε|<δ →
      segment ℝ (a+ε • qa) (b+ε • qb) ⊆ {x | r^2 < squaredLength (x-z)} := by
  have hout : segment ℝ a b ⊆ {x | r^2 < squaredLength (x-z)} := by
    intro x hx
    change r^2 < squaredLength (x-z)
    by_contra hh
    have hmem : x ∈ closedRoundDisk z r := by
      change squaredLength (x-z) ≤ r^2
      exact not_lt.mp hh
    exact Set.disjoint_left.mp hdis hmem hx
  have he := eventually_moving_segment_outside_disk (fun ε : ℝ => a+ε • qa)
    (fun ε : ℝ => b+ε • qb) (by fun_prop) (by fun_prop) z r (by simpa using hout)
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ,hδ,fun ε hε => hh (by simpa [Real.dist_eq] using hε)⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_NormalOffsetExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_normal_offset (w d : Plane) (hd : d ≠ 0) (hpar : det2 d w=0) (ε : ℝ) :
    squaredLength (w+ε • normalShift d)=squaredLength w+ε^2/squaredLength d := by
  have hL := ne_of_gt (squaredLength_pos d hd)
  have hcross : dot2 w (rotateQuarter d)=0 := by
    dsimp [dot2,rotateQuarter,det2] at *
    linarith
  have hrot : squaredLength (rotateQuarter d)=squaredLength d := by
    dsimp [squaredLength,rotateQuarter]
    ring
  unfold normalShift
  rw [smul_smul,squaredLength_add_smul,hrot,hcross]
  field_simp
  ring

theorem normal_offset_segment_exterior (o p d q : Plane) (r ε ℓ : ℝ)
    (hd : d ≠ 0) (hp : squaredLength (p-o)=r^2)
    (hpar : det2 d (p-o)=0) (hout : 0 ≤ ℓ*dot2 (p-o) d) (hε : ε ≠ 0)
    (hq : q-(p+ε • normalShift d)=ℓ • d) :
    segment ℝ (p+ε • normalShift d) q ⊆ {x | r^2 < squaredLength (x-o)} := by
  apply exterior_segment_of_dot
  · have he : p+ε • normalShift d-o=(p-o)+ε • normalShift d := by abel
    rw [he,squaredLength_normal_offset _ d hd hpar,hp]
    exact lt_add_of_pos_right _ (div_pos (sq_pos_of_ne_zero hε) (squaredLength_pos d hd))
  · rw [hq]
    have he : dot2 (p+ε • normalShift d-o) (ℓ • d)=ℓ*dot2 (p-o) d := by
      dsimp [dot2,normalShift,rotateQuarter]
      ring
    rwa [he]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_RadialTracks
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial track displacements and connector clearance from other disks and tracks. -/

section

/-! Endpoint radial directions have the correct sign in the fixed left-to-right edge orientation. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem dot2_scaled_self (v : Plane) (a b : ℝ) : dot2 (a • v) (b • v)=a*b*squaredLength v := by
  dsimp [dot2,squaredLength]
  ring

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem start_radial_dot_pos (e : Edge) :
    0 < dot2 (V.startPort e-D.vertex ((graph.src e))) (trackDirection (V.vertices e) 0) := by
  have hp := V.pieces_pos e
  have hα := (radialPort_parameter_half ((V.chain e).vertices 0) ((V.chain e).vertices 1)
    V.radius V.radius_pos (V.short e).1).1
  have hβ := (V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 0
  have he : V.startPort e-D.vertex ((graph.src e))=
      (V.chain e).startFraction V.radius • trackDirection (V.chain e).vertices 0 := by
    have hh := radialPort_sub ((V.chain e).vertices 0) ((V.chain e).vertices 1) V.radius
    change (V.chain e).startPort V.radius-(V.chain e).vertices 0=
      (V.chain e).startFraction V.radius • trackDirection (V.chain e).vertices 0 at hh
    simpa only [startPort,(V.chain e).first] using hh
  rw [he]
  change 0 < dot2 _ (trackDirection ((V.chain e).truncatedVertices V.radius) 0)
  rw [(V.chain e).truncated_direction V.radius 0 hp,dot2_scaled_self]
  exact mul_pos (mul_pos hα hβ)
    (squaredLength_pos _ ((V.chain e).minimum_piece_ne_zero (V.minimal e) 0 hp))

theorem end_radial_dot_neg (e : Edge) :
    dot2 (V.endPort e-D.vertex ((graph.dst e)))
      (trackDirection (V.vertices e) (V.pieces e-1)) < 0 := by
  have hp := V.pieces_pos e
  have hp' : 0 < (V.chain e).pieces := hp
  have hi : V.pieces e-1 < V.pieces e := by omega
  have hα := (radialPort_parameter_half ((V.chain e).vertices ((V.chain e).pieces-1))
    ((V.chain e).vertices (V.chain e).pieces) V.radius V.radius_pos (V.short e).2).1
  have hβ := (V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 (V.pieces e-1)
  have he : V.endPort e-D.vertex ((graph.dst e))=
      (-(V.chain e).endFraction V.radius) • trackDirection (V.chain e).vertices (V.pieces e-1) := by
    have hh : (V.chain e).endPort V.radius-(V.chain e).vertices (V.chain e).pieces=
        (-(V.chain e).endFraction V.radius) • trackDirection (V.chain e).vertices (V.pieces e-1) := by
      rw [(V.chain e).endPort_eq_fraction]
      simp only [trackDirection,pieces,show (V.chain e).pieces-1+1=(V.chain e).pieces by omega,neg_smul]
      abel
    simpa only [endPort,(V.chain e).last] using hh
  rw [he]
  change dot2 _ (trackDirection ((V.chain e).truncatedVertices V.radius) (V.pieces e-1)) < 0
  rw [(V.chain e).truncated_direction V.radius _ hi,dot2_scaled_self]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hα) hβ)
    (squaredLength_pos _ ((V.chain e).minimum_piece_ne_zero (V.minimal e) _ hi))

theorem bend_ne_zero (e : Edge) (i : ℕ) (hi0 : 0 < i) (hin : i < V.pieces e) :
    det2 (trackDirection (V.vertices e) (i-1)) (trackDirection (V.vertices e) i) ≠ 0 := by
  exact (V.chain e).truncated_bend_ne_zero (V.minimal e) V.radius V.radius_pos
    (V.short e).1 (V.short e).2 i hi0 hin

theorem exists_forward_radius (e : Edge) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ i : Fin (V.pieces e),
      ∃ ℓ : ℝ, 0<ℓ ∧ shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)-
        shiftedTrack (V.vertices e) (V.pieces e) ε i.val=ℓ • trackDirection (V.vertices e) i.val :=
  exists_forward_shiftedTrack_radius (V.vertices e) (V.pieces e) (V.direction_ne_zero e) (V.bend_ne_zero e)

end VertexTruncation
end Paper170Geometry

end
end

section

/-! The actual first and last shifted segments remain outside their incident vertex disks. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem shifted_first_piece_exterior (e : Edge) (ε ℓ : ℝ)
    (hε : ε ≠ 0) (hℓ : 0<ℓ)
    (hdir : shiftedTrack (V.vertices e) (V.pieces e) ε 1-
      shiftedTrack (V.vertices e) (V.pieces e) ε 0=ℓ • trackDirection (V.vertices e) 0) :
    segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε 0)
      (shiftedTrack (V.vertices e) (V.pieces e) ε 1) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex ((graph.src e)))} := by
  have hstart : shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      V.startPort e+ε • normalShift (trackDirection (V.vertices e) 0) := by
    simp [shiftedTrack,trackOffset,V.vertices_first]
  have hc : squaredLength (V.startPort e-D.vertex ((graph.src e)))=V.radius^2 := by
    simpa only [V.spokePort_left] using V.spokePort_circle ((graph.src e)) (V.leftIncident e)
  have hp : det2 (trackDirection (V.vertices e) 0) (V.startPort e-D.vertex ((graph.src e)))=0 := by
    simpa [spokeDirection,spokeIndex,leftIncident,spokePort,drawingSpokePort,startPort] using
      V.spokeDirection_parallel ((graph.src e)) (V.leftIncident e)
  rw [hstart] at hdir ⊢
  exact normal_offset_segment_exterior _ _ _ _ _ ε ℓ (V.direction_ne_zero e 0 (V.pieces_pos e))
    hc hp (mul_nonneg hℓ.le (V.start_radial_dot_pos e).le) hε hdir

theorem shifted_last_piece_exterior (e : Edge) (ε ℓ : ℝ)
    (hε : ε ≠ 0) (hℓ : 0<ℓ)
    (hdir : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)-
      shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1)=
        ℓ • trackDirection (V.vertices e) (V.pieces e-1)) :
    segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1))
      (shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex ((graph.dst e)))} := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  have hi : V.pieces e-1 < V.pieces e := by have hh := V.pieces_pos e; omega
  have hend : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      V.endPort e+ε • normalShift (trackDirection (V.vertices e) (V.pieces e-1)) := by
    simp [shiftedTrack,trackOffset,hn,V.vertices_last]
  have hc : squaredLength (V.endPort e-D.vertex ((graph.dst e)))=V.radius^2 := by
    simpa only [V.spokePort_right] using V.spokePort_circle ((graph.dst e)) (V.rightIncident e)
  have hp : det2 (trackDirection (V.vertices e) (V.pieces e-1)) (V.endPort e-D.vertex ((graph.dst e)))=0 := by
    simpa [spokeDirection,spokeIndex,rightIncident,spokePort,drawingSpokePort,endPort,(graph.loopless e).symm] using
      V.spokeDirection_parallel ((graph.dst e)) (V.rightIncident e)
  have hrev : shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e-1)-
      (V.endPort e+ε • normalShift (trackDirection (V.vertices e) (V.pieces e-1)))=
        (-ℓ) • trackDirection (V.vertices e) (V.pieces e-1) := by
    rw [neg_smul,← hdir,hend]
    abel
  rw [segment_symm,hend]
  exact normal_offset_segment_exterior _ _ _ _ _ ε (-ℓ) (V.direction_ne_zero e _ hi)
    hc hp (mul_nonneg_of_nonpos_of_nonpos (by linarith) (V.end_radial_dot_neg e).le) hε hrev

end Paper170Geometry.VertexTruncation

end
end

section

/-! Actual connectors stay on the displaced supporting line and avoid their own original spoke piece. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem det2_segmentPoint_sub (d p a b : Plane) (t : ℝ) :
    det2 d (segmentPoint a b t-p)=(1-t)*det2 d (a-p)+t*det2 d (b-p) := by
  dsimp [det2,segmentPoint]
  ring

theorem segment_line_level_zero (a b p : Plane) (hp : p=a ∨ p=b) (t : ℝ) :
    det2 (b-a) (segmentPoint a b t-p)=0 := by
  rcases hp with rfl | rfl <;> dsimp [det2,segmentPoint] <;> ring

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem spokePort_is_piece_endpoint (j : Vertex) (e : IncidentEdges graph j) :
    V.spokePort j e=V.vertices e.val (V.spokeIndex j e) ∨
      V.spokePort j e=V.vertices e.val (V.spokeIndex j e+1) := by
  unfold spokePort drawingSpokePort spokeIndex
  split_ifs
  · exact Or.inl (V.vertices_first e.val).symm
  · right
    have hp := V.pieces_pos e.val
    rw [show V.pieces e.val-1+1=V.pieces e.val by omega]
    exact (V.vertices_last e.val).symm

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_tangentPort (j : Vertex) (e : IncidentEdges graph j) :
    Continuous (C.tangentPort j e) := by
  change Continuous (fun ε : ℝ => V.spokePort j e+ε • normalShift (V.spokeDirection j e))
  fun_prop

theorem tangentPort_zero (j : Vertex) (e : IncidentEdges graph j) :
    C.tangentPort j e 0=V.spokePort j e := by simp [tangentPort]

theorem tangentPort_level (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.tangentPort j e ε-V.spokePort j e)=ε := by
  simp only [tangentPort,add_sub_cancel_left,det2_smul_right,
    det2_normalShift _ (V.spokeDirection_ne_zero j e),mul_one]

theorem connector_level (j : Vertex) (e : IncidentEdges graph j) (ε t : ℝ) :
    det2 (V.spokeDirection j e)
      (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-V.spokePort j e)=ε := by
  rw [det2_segmentPoint_sub,C.shiftedPort_level,C.tangentPort_level]
  ring

theorem connector_avoids_incident_piece (j : Vertex) (e : IncidentEdges graph j)
    (ε : ℝ) (hε : ε ≠ 0) :
    ¬ ClosedSegmentsMeet (V.vertices e.val (V.spokeIndex j e))
      (V.vertices e.val (V.spokeIndex j e+1)) (C.shiftedPort j e ε) (C.tangentPort j e ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hzero := segment_line_level_zero (V.vertices e.val (V.spokeIndex j e))
    (V.vertices e.val (V.spokeIndex j e+1)) (V.spokePort j e) (V.spokePort_is_piece_endpoint j e) s
  change det2 (V.spokeDirection j e)
    (segmentPoint (V.vertices e.val (V.spokeIndex j e)) (V.vertices e.val (V.spokeIndex j e+1)) s-V.spokePort j e)=0 at hzero
  rw [he,C.connector_level] at hzero
  exact hε hzero

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! One genuine radius keeps every shifted exterior edge track outside every vertex disk. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem exists_nonincident_shift_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j e (i : Fin (V.pieces e)),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=V.pieces e)) →
      segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
        (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)) ⊆
          {x | V.radius^2 < squaredLength (x-D.vertex j)} := by
  classical
  let Bad := Σ j : Vertex, Σ e : Edge,
    {i : Fin (V.pieces e) // ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=V.pieces e))}
  have hdis (b : Bad) : Disjoint (closedRoundDisk (D.vertex b.1) V.radius)
      (segment ℝ (V.vertices b.2.1 b.2.2.val.val) (V.vertices b.2.1 (b.2.2.val.val+1))) := by
    exact (V.piece_clearance b.1 b.2.1 b.2.2.val b.2.2.property).mono_right
      ((V.chain b.2.1).truncated_piece_subset V.radius V.radius_pos
        (V.weak_short b.2.1).1 (V.weak_short b.2.1).2 _ b.2.2.val.isLt)
  have hex (b : Bad) := exists_shifted_segment_disk_radius
    (V.vertices b.2.1 b.2.2.val.val) (V.vertices b.2.1 (b.2.2.val.val+1))
    (trackOffset (V.vertices b.2.1) (V.pieces b.2.1) b.2.2.val.val)
    (trackOffset (V.vertices b.2.1) (V.pieces b.2.1) (b.2.2.val.val+1))
    (D.vertex b.1) V.radius (hdis b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j e i hi
  exact hprop ⟨j,e,⟨i,hi⟩⟩ ε (hε.trans (hbound ⟨j,e,⟨i,hi⟩⟩ (Finset.mem_univ _)))

theorem exists_all_vertex_disk_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j e (i : Fin (V.pieces e)),
      segment ℝ (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
        (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1)) ⊆
          {x | V.radius^2 < squaredLength (x-D.vertex j)} := by
  classical
  obtain ⟨δ₀,hδ₀,hclear⟩ := V.exists_nonincident_shift_radius
  choose radius hpos hforward using V.exists_forward_radius
  obtain ⟨δ₁,hδ₁,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun e _ => hpos e)
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hsmall j e i
  obtain ⟨ℓ,hℓ,hdir⟩ := hforward e ε
    (hsmall.trans_le (min_le_right _ _ ) |>.trans (hbound e (Finset.mem_univ _))) i
  by_cases hleft : j=(graph.src e) ∧ i.val=0
  · rcases hleft with ⟨rfl,hi⟩
    simpa only [hi,zero_add] using V.shifted_first_piece_exterior e ε ℓ hε hℓ (by simpa only [hi,zero_add] using hdir)
  · by_cases hright : j=(graph.dst e) ∧ i.val+1=V.pieces e
    · rcases hright with ⟨rfl,hi⟩
      have hi' : i.val=V.pieces e-1 := by omega
      have hn : V.pieces e-1+1=V.pieces e := by omega
      simpa only [hi',hn] using V.shifted_last_piece_exterior e ε ℓ hε hℓ (by simpa only [hi',hn] using hdir)
    · exact hclear ε (hsmall.trans_le (min_le_left _ _)) j e i (not_or.mpr ⟨hleft,hright⟩)

end Paper170Geometry.VertexTruncation

end
end

section

/-! Every shrinking circle connector stays outside all other vertex disks at one common radius. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped Topology
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem exists_connector_other_disks_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j k, j ≠ k → ∀ f : IncidentEdges graph j,
      segment ℝ (C.shiftedPort j f ε) (C.tangentPort j f ε) ⊆
        {x | V.radius^2 < squaredLength (x-D.vertex k)} := by
  classical
  let Pair := Σ j : Vertex, Σ k : {k : Vertex // j ≠ k}, IncidentEdges graph j
  have hstart (b : Pair) : segment ℝ (C.shiftedPort b.1 b.2.2 0) (C.tangentPort b.1 b.2.2 0) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex b.2.1.val)} := by
    rw [C.shiftedPort_zero,C.tangentPort_zero,segment_same]
    intro x hx
    have he : x=V.spokePort b.1 b.2.2 := hx
    subst x
    change V.radius^2 < squaredLength (V.spokePort b.1 b.2.2-D.vertex b.2.1.val)
    by_contra hh
    have hj : V.spokePort b.1 b.2.2 ∈ closedRoundDisk (D.vertex b.1) V.radius := by
      change squaredLength (V.spokePort b.1 b.2.2-D.vertex b.1) ≤ V.radius^2
      rw [V.spokePort_circle]
    have hk : V.spokePort b.1 b.2.2 ∈ closedRoundDisk (D.vertex b.2.1.val) V.radius := not_lt.mp hh
    exact Set.disjoint_left.mp (V.disks_disjoint b.1 b.2.1.val b.2.1.property) hj hk
  have hevent (b : Pair) := eventually_moving_segment_outside_disk
    (C.shiftedPort b.1 b.2.2) (C.tangentPort b.1 b.2.2)
    (C.continuous_shiftedPort b.1 b.2.2) (C.continuous_tangentPort b.1 b.2.2)
    (D.vertex b.2.1.val) V.radius (hstart b)
  have hex (b : Pair) := Metric.eventually_nhds_iff.mp (hevent b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j k hjk f
  exact hprop ⟨j,⟨k,hjk⟩,f⟩ (by simpa [Real.dist_eq] using hε.trans (hbound ⟨j,⟨k,hjk⟩,f⟩ (Finset.mem_univ _)))

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! One two-sided physical radius excludes every connector/track meeting, including shared edges. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped Topology
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_nonincident_connector_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (f : IncidentEdges graph j) e (i : Fin (V.pieces e)),
      ¬ (e=f.val ∧ i.val=V.spokeIndex j f) →
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  classical
  let Bad := Σ j : Vertex, Σ f : IncidentEdges graph j, Σ e : Edge,
    {i : Fin (V.pieces e) // ¬ (e=f.val ∧ i.val=V.spokeIndex j f)}
  have hnot (b : Bad) : ¬ ClosedSegmentsMeet
      (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1))
      (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) := by
    rintro ⟨s,hs,t,ht,he⟩
    have he0 : segmentPoint (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) t=V.spokePort b.1 b.2.1 := by
      unfold segmentPoint
      rw [← add_smul]
      simp
    rw [he0] at he
    have hx : V.spokePort b.1 b.2.1 ∈
        segment ℝ (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1)) := by
      rw [← Path.range_segment]
      refine ⟨⟨s,hs⟩,?_⟩
      simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
    exact b.2.2.2.property (V.spokePort_piece_unique hnorm b.1 b.2.1 b.2.2.1 b.2.2.2.val hx)
  have hevent (b : Bad) := eventually_moving_disjoint_segments
    (V.vertices b.2.2.1 b.2.2.2.val.val) (V.vertices b.2.2.1 (b.2.2.2.val.val+1))
    (V.spokePort b.1 b.2.1) (V.spokePort b.1 b.2.1) (C.shiftedPort b.1 b.2.1) (C.tangentPort b.1 b.2.1)
    (C.continuous_shiftedPort b.1 b.2.1).continuousAt (C.continuous_tangentPort b.1 b.2.1).continuousAt
    (C.shiftedPort_zero b.1 b.2.1) (C.tangentPort_zero b.1 b.2.1) (hnot b)
  have hex (b : Bad) := Metric.eventually_nhds_iff.mp (hevent b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j f e i hi
  exact hprop ⟨j,f,e,⟨i,hi⟩⟩ (by simpa [Real.dist_eq] using hε.trans (hbound ⟨j,f,e,⟨i,hi⟩⟩ (Finset.mem_univ _)))

theorem exists_all_connector_track_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j (f : IncidentEdges graph j) e (i : Fin (V.pieces e)),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_nonincident_connector_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall j f e i
  by_cases hi : e=f.val ∧ i.val=V.spokeIndex j f
  · rcases hi with ⟨rfl,hi⟩
    simpa only [hi] using C.connector_avoids_incident_piece j f ε hε
  · exact hh ε hsmall j f e i hi

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_RoundDiskChords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem round_chord_subset_closed_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2) :
    segment ℝ a b ⊆ closedRoundDisk z r := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  change squaredLength (Path.segment a b t-z) ≤ r^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  have he : squaredLength (segmentPoint a b t.val-z)=
      (1-t.val)*squaredLength (a-z)+t.val*squaredLength (b-z)-
        t.val*(1-t.val)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  change squaredLength (segmentPoint a b t.val-z) ≤ r^2
  rw [he,ha,hb]
  have hnon : 0 ≤ t.val*(1-t.val)*squaredLength (b-a) := by
    have ht0 := t.property.1
    have ht1 := sub_nonneg.mpr t.property.2
    dsimp [squaredLength]
    positivity
  linarith

theorem round_chord_boundary_endpoints (z a b x : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hx : x ∈ segment ℝ a b) (hboundary : squaredLength (x-z)=r^2) : x=a ∨ x=b := by
  by_cases hab : a=b
  · subst b
    exact Or.inl (by simpa only [segment_same,Set.mem_singleton_iff] using hx)
  · rw [← Path.range_segment] at hx
    obtain ⟨t,rfl⟩ := hx
    by_cases ht0 : t.val=0
    · left
      simp only [Path.segment_apply,AffineMap.lineMap_apply_module,ht0,sub_zero,one_smul,zero_smul,add_zero]
    · by_cases ht1 : t.val=1
      · right
        simp only [Path.segment_apply,AffineMap.lineMap_apply_module,ht1,sub_self,one_smul,zero_smul,zero_add]
      · have hstrict := round_chord_in_open_disk z a b r ha hb hab t.val
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
        have hb' : squaredLength (segmentPoint a b t.val-z)=r^2 := by
          simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hboundary
        rw [hb'] at hstrict
        exact False.elim (lt_irrefl _ hstrict)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_VertexChords
attribute [-instance] _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform spoke radii, vertex chords, and separation from exterior tracks. -/

section

/-! Common physical radii for every vertex of the actual drawing, fixed before any cycle choices. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem port_injective (C : TruncatedSpokeCoordinates V) (j : Vertex) : Function.Injective (V.spokePort j) := by
  intro e f he
  apply C.node_injective j
  apply circlePoint_injective
  apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
  simpa only [C.point_eq] using he

theorem exists_uniform_endpoint_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j : Vertex,
      (∀ e f : IncidentEdges graph j, V.spokePort j e ≠ C.shiftedPort j f ε) ∧
      Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e ε) := by
  classical
  choose radius hpos hprop using C.exists_endpoint_separation_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun ε hε hsmall j => hprop j ε hε (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

theorem exists_uniform_scale_radius [Fintype Vertex] [Fintype Edge] (_C : TruncatedSpokeCoordinates V) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j (e : IncidentEdges graph j), |V.spokeScale j e*ε|<1 := by
  let Spoke := Σ j : Vertex, IncidentEdges graph j
  obtain ⟨δ,hδ,hbound⟩ := finite_scaled_radius
    (fun s : Spoke => V.spokeScale s.1 s.2) (fun _ => (1 : ℝ)) (by intro s; norm_num)
  exact ⟨δ,hδ,fun ε hε j e => hbound ε hε ⟨j,e⟩⟩

theorem exists_uniform_average_radius [Fintype Vertex] [Fintype Edge] :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges graph j),
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  choose radius hpos hprop using C.exists_vertex_average_radius
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun j _ => hpos j)
  exact ⟨δ,hδ,fun t ht hsmall j => hprop j t ht (hsmall.trans (hbound j (Finset.mem_univ _)))⟩

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Actual local chords have transverse meetings and avoid the exterior connector seams. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem shifted_chords_transverse (j : Vertex) (a b c d : IncidentEdges graph j)
    (ε : ℝ) (hsmall : ∀ e : IncidentEdges graph j, |V.spokeScale j e*ε|≤1)
    (hsep : ∀ e f : IncidentEdges graph j, V.spokePort j e ≠ C.shiftedPort j f ε)
    (hinj : Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e ε))
    (hab : a ≠ b) (hcd : c ≠ d) :
    SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c ε) (C.shiftedPort j d ε) :=
  round_circle_chords_transverse (D.vertex j) _ _ _ _ V.radius
    (V.spokePort_circle j a) (V.spokePort_circle j b)
    (C.shiftedPort_circle j c ε (hsmall c)) (C.shiftedPort_circle j d ε (hsmall d))
    ((C.port_injective j).ne hab) (hinj.ne hcd) (hsep a c) (hsep a d) (hsep b c) (hsep b d)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Original exterior tracks avoid every shifted vertex chord, including at boundary seams. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem track_in_disk_is_port (j : Vertex) (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (V.path e)) (hmem : x ∈ closedRoundDisk (D.vertex j) V.radius) :
    ∃ f : IncidentEdges graph j, x=V.spokePort j f := by
  rcases V.vertex_disk_cases j e x hx with ⟨hj,he⟩ | ⟨hj,he⟩ | hout
  · refine ⟨⟨e,Or.inl hj⟩,?_⟩
    simpa only [spokePort,drawingSpokePort,ite_eq_left hj,startPort] using he
  · have hnot : j ≠ (graph.src e) := by
      intro hh
      exact (graph.loopless e) (hh.symm.trans hj)
    refine ⟨⟨e,Or.inr hj⟩,?_⟩
    simpa only [spokePort,drawingSpokePort,ite_eq_right hnot,endPort] using he
  · exact False.elim (not_lt_of_ge hmem hout)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem track_shifted_chord_disjoint (j : Vertex) (c d : IncidentEdges graph j)
    (ε : ℝ) (hc : |V.spokeScale j c*ε|≤1) (hd : |V.spokeScale j d*ε|≤1)
    (hsep : ∀ f g : IncidentEdges graph j, V.spokePort j f ≠ C.shiftedPort j g ε)
    (e : Edge) (i : Fin (V.pieces e)) :
    ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
      (C.shiftedPort j c ε) (C.shiftedPort j d ε) := by
  intro hmeet
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter _ _ _ _).mp hmeet
  have hcirclec := C.shiftedPort_circle j c ε hc
  have hcircled := C.shiftedPort_circle j d ε hd
  have hmem := round_chord_subset_closed_disk (D.vertex j) _ _ V.radius hcirclec hcircled hy
  obtain ⟨f,hf⟩ := V.track_in_disk_is_port j e x (V.piece_subset_range e i.val i.isLt hx) hmem
  have hboundary : squaredLength (x-D.vertex j)=V.radius^2 := by rw [hf,V.spokePort_circle]
  rcases round_chord_boundary_endpoints (D.vertex j) _ _ x V.radius hcirclec hcircled hy hboundary with h | h
  · exact hsep f c (hf.symm.trans h)
  · exact hsep f d (hf.symm.trans h)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! All disk/exterior and different-disk segment interactions are genuinely disjoint. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

theorem round_chord_exterior_disjoint (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hout : segment ℝ c d ⊆ {x | r^2 < squaredLength (x-z)}) : ¬ ClosedSegmentsMeet a b c d := by
  intro hh
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter _ _ _ _).mp hh
  have hle := round_chord_subset_closed_disk z a b r ha hb hx
  have hlt : r^2 < squaredLength (x-z) := hout hy
  change squaredLength (x-z) ≤ r^2 at hle
  exact not_lt_of_ge hle hlt

namespace TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem different_vertex_chords_disjoint (j k : Vertex) (hjk : j ≠ k)
    (a b : IncidentEdges graph j) (c d : IncidentEdges graph k) (ε : ℝ)
    (hc : |V.spokeScale k c*ε|≤1) (hd : |V.spokeScale k d*ε|≤1) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  apply not_closedSegmentsMeet_of_disjoint
  exact (V.disks_disjoint j k hjk).mono
    (round_chord_subset_closed_disk _ _ _ _ (V.spokePort_circle j a) (V.spokePort_circle j b))
    (round_chord_subset_closed_disk _ _ _ _ (C.shiftedPort_circle k c ε hc) (C.shiftedPort_circle k d ε hd))

theorem chord_connector_disjoint_all_passages (j : Vertex) (a b f : IncidentEdges graph j)
    (ε : ℝ) (hne : ε ≠ 0) (hsmall : |V.spokeScale j f*ε|<1)
    (ha : V.spokePort j a ≠ C.shiftedPort j f ε) (hb : V.spokePort j b ≠ C.shiftedPort j f ε) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hx : segmentPoint (V.spokePort j a) (V.spokePort j b) s ∈ segment ℝ (V.spokePort j a) (V.spokePort j b) := by
    rw [← Path.range_segment]
    exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
  have hinside := round_chord_subset_closed_disk (D.vertex j) _ _ V.radius
    (V.spokePort_circle j a) (V.spokePort_circle j b) hx
  by_cases htp : 0<t
  · have hout := C.connector_strictly_outside j f ε hsmall hne t htp
    rw [← he] at hout
    exact not_lt_of_ge hinside hout
  · have ht0 : t=0 := by linarith [ht.1]
    rw [ht0,segmentPoint_zero] at he
    have hboundary : squaredLength (segmentPoint (V.spokePort j a) (V.spokePort j b) s-D.vertex j)=V.radius^2 := by
      rw [he]
      exact C.shiftedPort_circle j f ε hsmall.le
    rcases round_chord_boundary_endpoints (D.vertex j) _ _ _ V.radius
      (V.spokePort_circle j a) (V.spokePort_circle j b) hx hboundary with h | h
    · exact ha (h.symm.trans he)
    · exact hb (h.symm.trans he)

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! One radius verifies every track, connector and chord interaction needed for actual closed-walk assembly. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_cross_type_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (f : IncidentEdges graph j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j f ε) (C.tangentPort j f ε)) ∧
      (∀ j (c d : IncidentEdges graph j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j c ε) (C.shiftedPort j d ε)) ∧
      (∀ j (a b : IncidentEdges graph j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
          (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1))) ∧
      (∀ j k (a b : IncidentEdges graph j) (f : IncidentEdges graph k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (C.shiftedPort k f ε) (C.tangentPort k f ε)) ∧
      (∀ j k (a b : IncidentEdges graph j) (c d : IncidentEdges graph k), a ≠ b → c ≠ d →
        SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) ∧
      (∀ j k, j ≠ k → ∀ (a b : IncidentEdges graph j) (c d : IncidentEdges graph k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) := by
  obtain ⟨δ₀,hδ₀,htracks⟩ := V.exists_all_vertex_disk_radius
  obtain ⟨δ₁,hδ₁,hconnectors⟩ := C.exists_all_connector_track_radius hnorm
  obtain ⟨δ₂,hδ₂,hother⟩ := C.exists_connector_other_disks_radius
  obtain ⟨δ₃,hδ₃,hseparate⟩ := C.exists_uniform_endpoint_radius
  obtain ⟨δ₄,hδ₄,hscale⟩ := C.exists_uniform_scale_radius
  let δ := min δ₀ (min δ₁ (min δ₂ (min δ₃ δ₄)))
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ hδ₄)))
  have hb₀ : δ≤δ₀ := min_le_left _ _
  have hb₁ : δ≤δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb₂ : δ≤δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb₃ : δ≤δ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb₄ : δ≤δ₄ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  have hs := hscale ε (hsmall.trans_le hb₄)
  have hsep := hseparate ε hε (hsmall.trans_le hb₃)
  refine ⟨hconnectors ε hε (hsmall.trans_le hb₁),?_,?_,?_,?_,?_⟩
  · intro j c d e i
    exact C.track_shifted_chord_disjoint j c d ε (hs j c).le (hs j d).le (hsep j).1 e i
  · intro j a b e i
    exact round_chord_exterior_disjoint (D.vertex j) _ _ _ _ V.radius
      (V.spokePort_circle j a) (V.spokePort_circle j b) (htracks ε hε (hsmall.trans_le hb₀) j e i)
  · intro j k a b f
    by_cases hjk : j=k
    · subst k
      exact C.chord_connector_disjoint_all_passages j a b f ε hε (hs j f) ((hsep j).1 a f) ((hsep j).1 b f)
    · exact round_chord_exterior_disjoint (D.vertex j) _ _ _ _ V.radius
        (V.spokePort_circle j a) (V.spokePort_circle j b)
        (hother ε (hsmall.trans_le hb₂) k j (Ne.symm hjk) f)
  · intro j k a b c d hab hcd
    by_cases hjk : j=k
    · subst k
      exact C.shifted_chords_transverse j a b c d ε (fun e => (hs j e).le) (hsep j).1 (hsep j).2 hab hcd
    · exact segmentPairTransverse_of_not_meet _ _ _ _
        (C.different_vertex_chords_disjoint j k hjk a b c d ε (hs k c).le (hs k d).le)
  · intro j k hjk a b c d
    exact C.different_vertex_chords_disjoint j k hjk a b c d ε (hs k c).le (hs k d).le

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_StraightChainIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
open scoped BigOperators
variable {O T : Set Plane} {a b c d : Plane}

theorem intersection_single_single (ha : a ∈ O) (hab : segment ℝ a b ⊆ O)
    (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) :
    polygonIntersection (single O a b ha hab).vertices (single T c d hc hcd).vertices 1 1=
      segmentCrossingSign a b c d := by simp [polygonIntersection,single]

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_StraightChainTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
open scoped BigOperators
variable {O T : Set Plane} {a b c d : Plane}

theorem transverse_single_single (ha : a ∈ O) (hab : segment ℝ a b ⊆ O)
    (hc : c ∈ T) (hcd : segment ℝ c d ⊆ T) (h : SegmentPairTransverse a b c d) :
    (single O a b ha hab).Transverse (single T c d hc hcd) := by
  intro i j
  have hi : i.val=0 := by have hh : i.val<1 := i.isLt; omega
  have hj : j.val=0 := by have hh : j.val<1 := j.isLt; omega
  simpa [single,hi,hj] using h

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CycleIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed dart and cycle intersections, passage pairing, and endpoint averaging. -/

section

/-! Actual vertex-chord chains have precisely the local two-sided averaged endpoint pairing. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem chordChain_intersection (j k : Vertex) (a b : IncidentEdges graph j)
    (c d : IncidentEdges graph k) (ε : ℝ) :
    polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=
      segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  rw [VertexTruncation.chordChain,shiftedChordChain,PolygonalChain.intersection_single_single]

theorem exists_vertex_chord_chain_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k (a b : IncidentEdges graph j) (c d : IncidentEdges graph k),
        a ≠ b → c ≠ d → (V.chordChain j a b).Transverse (C.shiftedChordChain k c d ε)) ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k, j ≠ k → ∀ (a b : IncidentEdges graph j) (c d : IncidentEdges graph k),
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=0) ∧
      (∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges graph j), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain j c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain j c d (-t)).vertices 1 1)/2=
            chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d)) := by
  obtain ⟨δ₀,hδ₀,hgeo⟩ := C.exists_cross_type_radius hnorm
  obtain ⟨δ₁,hδ₁,havg⟩ := C.exists_uniform_average_radius
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_,?_,?_⟩
  · intro ε hε hsmall j k a b c d hab hcd
    have hh := (hgeo ε hε (hsmall.trans_le (min_le_left _ _))).2.2.2.2.1 j k a b c d hab hcd
    exact PolygonalChain.transverse_single_single _ _ _ _ hh
  · intro ε hε hsmall j k hjk a b c d
    rw [C.chordChain_intersection]
    exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _
      ((hgeo ε hε (hsmall.trans_le (min_le_left _ _))).2.2.2.2.2 j k hjk a b c d)
  · intro t ht hsmall j a b c d hab hcd
    rw [C.chordChain_intersection,C.chordChain_intersection]
    exact havg t ht (hsmall.trans_le (min_le_right _ _)) j a b c d hab hcd

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! The local pairing uses one fixed coordinate chart per vertex, including shared chord endpoints. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge] {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_vertex_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ j k (a b : IncidentEdges graph j) (c d : IncidentEdges graph k), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d (-t)).vertices 1 1)/2=
            C.vertexChordPairing j k a b c d := by
  obtain ⟨δ,hδ,-,hzero,havg⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs j k a b c d hab hcd
  by_cases h : k=j
  · subst k
    have hc : incidentCast (rfl : j=j) c=c := Subtype.ext rfl
    have hd : incidentCast (rfl : j=j) d=d := Subtype.ext rfl
    rw [vertexChordPairing,dite_eq_left rfl,hc,hd]
    exact havg t ht hs j a b c d hab hcd
  · have hzplus := hzero t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using hs) j k (Ne.symm h) a b c d
    have hzminus := hzero (-t) (neg_ne_zero.mpr (ne_of_gt ht)) (by simpa only [abs_neg,abs_of_pos ht] using hs)
      j k (Ne.symm h) a b c d
    rw [hzplus,hzminus,zero_add,zero_div]
    simp only [vertexChordPairing,dite_eq_right h]

theorem exists_passage_pairing_radius_oai (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ (d f : ℕ → OrientedDart graph)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i) →
      OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j) →
      (C.passageIntersection d f hd hf i j t+C.passageIntersection d f hd hf i j (-t))/2=
        C.passagePairing d f hd hf i j := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_vertex_pairing_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs d f hd hf i j hi hj
  exact hh t ht hs _ _ _ _ _ _ (dartPassage_ne d hd i hi) (dartPassage_ne f hf j hj)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
end

theorem solution : type_of% @OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_passage_pairing_radius_oai := @OAI.Paper170Geometry.TruncatedSpokeCoordinates.exists_passage_pairing_radius_oai
