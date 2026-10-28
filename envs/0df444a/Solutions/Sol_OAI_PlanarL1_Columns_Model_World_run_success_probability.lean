-- Prove2me | solution 1 for OAI.PlanarL1.Columns.Model.World.run_success_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:59:55.665228+00:00
-- url     : https://prove2.me/submissions/7e28eeef-6022-4009-93a8-c6e4654e011b

import Mathlib
import Definitions.Def_OAIQ5T5000

section
-- module Solutions.OAIQ5_T5.PlanarL1_Noncrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
/-! ## Noncrossing column words 
These are the exact combinatorial separation tools used in the surviving-seed
packing argument. The circular set has been cut at index 0. -/

namespace ColumnOrder

/-- Geometry, Lemma `geo:skipping`: passage from one side of an index to the
other either visits it or has a step jumping strictly across it. -/
theorem visits_or_skips {n : ℕ} {G : SimpleGraph (Fin n)} {i x y : Fin n}
    (p : G.Walk x y) (hx : x < i) (hy : i < y) :
    i ∈ p.support ∨ JumpsAcross i p := by
  induction p with
  | nil => omega
  | @cons x z y hxz p ih =>
    by_cases hz : z = i
    · left
      exact List.mem_cons_of_mem x (hz ▸ p.start_mem_support)
    by_cases hzi : z < i
    · rcases ih hzi hy with hm | ⟨e, he, hcross⟩
      · left
        simp [hm]
      · right
        exact ⟨e, by simp [he], hcross⟩
    · right
      refine ⟨⟨(x, z), hxz⟩, ?_, Or.inl ⟨hx, ?_⟩⟩
      · simp
      · change i < z
        omega

end ColumnOrder

end PlanarL1

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Distance
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)
namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

/-- A column visited by a short switching path has a nearby radial midpoint.
The conclusion uses the actual path prefix, rather than a shortest path
constrained to a radial cell. -/
lemma path_radial_bound (o x y : M.Point J root) {H a : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (p : M.Path J x.column y.column)
    {i : Fin n} (hi : i ∈ p.word.support) :
    ∃ hr : (M.activeGraph J).Reachable root i,
      |dist o (⟨i, H, hH, hr⟩ : M.Point J root) - dist o (x.withHeight H hH)| ≤
        p.length x.height y.height + a := by
  obtain ⟨T, hT, q, r, hqr⟩ := p.split_at_column x.inBand y.inBand hi
  let z : M.Point J root := ⟨i, T, hT, x.reachable.trans q.word.reachable⟩
  have hd : dist x z ≤ p.length x.height y.height := by
    have hq := x.distance_le z q
    have hr := r.length_nonneg T y.height
    change dist x z ≤ q.length x.height T at hq
    linarith
  refine ⟨z.reachable, ?_⟩
  have hb := o.radial_difference_le z x hH hhalf
  rw [dist_comm z x] at hb
  change |dist o (z.withHeight H hH) - dist o (x.withHeight H hH)| ≤ _
  linarith

/-- Deterministic padding in one actual radial layer. All representatives of
all endpoints are covered because the lemma is stated on the pseudometric
space of representatives. -/
lemma radial_cell_padding (o x y : M.Point J root) {H a q D ρ : ℝ}
    (hH : H ∈ J) (ha : 0 ≤ a) (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hlow : q + ρ + 2 * a < dist o (x.withHeight H hH))
    (hupp : dist o (x.withHeight H hH) < q + D - ρ - 2 * a)
    (p : M.Path J x.column y.column) (hp : p.length x.height y.height ≤ ρ) :
    y.column ∈ ColumnOrder.componentColumns C := by
  apply ColumnOrder.componentColumns_of_walk C p.word hx
  intro i hi
  obtain ⟨hr, hb⟩ := o.path_radial_bound x y hH hhalf p hi
  obtain ⟨h₁, h₂⟩ := abs_le.mp hb
  refine ⟨hr, ?_, ?_⟩ <;> linarith

/-- A frontier midpoint is within one width of a layer threshold. The
neighbor cannot be in the same layer, since the cell is a component there. -/
lemma frontier_radial (o z : M.Point J root) {H a q D : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hz : z.column ∈ frontier (M := M) (J := J) (ColumnOrder.componentColumns C)) :
    dist o (z.withHeight H hH) < q + a ∨
      q + D - a ≤ dist o (z.withHeight H hH) := by
  obtain ⟨hzc, j, hzj, hj⟩ := hz
  let w : M.Point J root := ⟨j, H, hH, z.reachable.trans hzj.reachable⟩
  have hnot : j ∉ o.layer H hH q D := by
    intro h
    exact hj (ColumnOrder.componentColumns_adj C hzc hzj h)
  have hd : dist (z.withHeight H hH) w ≤ a :=
    (z.withHeight H hH).dist_midpoints_le w rfl rfl hhalf hzj
  have hw : ¬ (q ≤ dist o w ∧ dist o w < q + D) := by
    intro h
    exact hnot ⟨w.reachable, h⟩
  have ht₁ := dist_triangle o (z.withHeight H hH) w
  have ht₂ := dist_triangle o w (z.withHeight H hH)
  rw [dist_comm w (z.withHeight H hH)] at ht₂
  by_cases hq : dist o w < q
  · exact Or.inl (by linarith)
  · exact Or.inr (by have h := not_lt.mp hq; have h' : q + D ≤ dist o w :=
                         le_of_not_gt (fun hu => hw ⟨h, hu⟩); linarith)

/-- Exact strict avoidance of the frontier, the second assertion of
`geo:padding`. The empty-frontier case is automatic, not assigned distance 0. -/
lemma radial_frontier_distance (o x z : M.Point J root) {H a q D ρ : ℝ}
    (hH : H ∈ J) (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hlow : q + ρ + 2 * a < dist o (x.withHeight H hH))
    (hupp : dist o (x.withHeight H hH) < q + D - ρ - 2 * a)
    (hz : z.column ∈ frontier (M := M) (J := J) (ColumnOrder.componentColumns C)) :
    ρ < dist x z := by
  obtain h | h := o.frontier_radial z hH hhalf C hz
  · have hb := (abs_le.mp (o.radial_difference_le x z hH hhalf)).2
    linarith
  · have hb := (abs_le.mp (o.radial_difference_le x z hH hhalf)).1
    linarith


end Point

end Model
end Columns
end PlanarL1

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Fields
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)

namespace Field

lemma wall_nonempty {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b : Fin (k + 1)) (H : J) : (F.wall a b).Nonempty := by
  exact ⟨(F.value a H,H.val),Or.inl ⟨H,rfl⟩⟩

lemma transverse_abs {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i : Fin (k + 1)) (H : J) (hi : arcSign a b i ≠ 0) :
    |F.transverseValue a b i H| = Metric.infDist (F.value i H,H.val) (F.wall a b) := by
  rw [transverseValue,abs_mul,abs_of_nonneg Metric.infDist_nonneg]
  rcases arcSign_cases a b i with he | he | he
  · exact False.elim (hi he)
  · simp [he]
  · simp [he]

end Field

namespace Path

variable {M} {J : Set ℝ}

lemma trace_column {i j : Fin n} (p : M.Path J i j) {a b : ℝ} {z : Fin n × ℝ}
    (hz : z ∈ p.trace a b) : z.1 ∈ p.word.support := by
  induction p generalizing a with
  | nil i =>
    simpa only [word,SimpleGraph.Walk.support_nil,List.mem_singleton] using hz.1
  | cons H hH hs p ih =>
    rcases hz with hz | hz
    · exact List.mem_cons.mpr (Or.inl hz.1)
    · exact List.mem_cons_of_mem _ (ih hz)

lemma abs_split {a b T : ℝ} (hT : T ∈ Set.uIcc a b) : |a - T| + |T - b| = |a - b| := by
  rcases le_total a b with hab | hab
  · have ht : a ≤ T ∧ T ≤ b := by
      rcases Set.mem_uIcc.mp hT with ht | ht <;> constructor <;> linarith
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1),abs_of_nonpos (sub_nonpos.mpr ht.2),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · have ht : b ≤ T ∧ T ≤ a := by
      rcases Set.mem_uIcc.mp hT with ht | ht <;> constructor <;> linarith
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg (sub_nonneg.mpr ht.1),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    ring

/-- A visit admits an exact-length prefix and suffix, not just an unrelated
path to the same column. -/
lemma trace_split {i j : Fin n} (p : M.Path J i j) {a b : ℝ} {z : Fin n × ℝ}
    (hz : z ∈ p.trace a b) : ∃ (q : M.Path J i z.1) (r : M.Path J z.1 j),
      q.length a z.2 + r.length z.2 b = p.length a b := by
  induction p generalizing a with
  | nil i =>
    obtain ⟨hz,hT⟩ := hz
    subst i
    exact ⟨.nil _,.nil _,abs_split hT⟩
  | @cons i v j H hH hs p ih =>
    rcases hz with hz | hz
    · obtain ⟨hz,hT⟩ := hz
      subst i
      exact ⟨.nil _,.cons H hH hs p,by dsimp only [length]; linarith [abs_split hT]⟩
    · obtain ⟨q,r,hqr⟩ := ih hz
      refine ⟨.cons H hH hs q,r,?_⟩
      dsimp only [length]
      linarith

end Path

namespace Field

variable {M} {J : Set ℝ} {L : NNReal}

lemma vertical_intermediate (F : M.Field J L) (hJ : Set.OrdConnected J) (i : Fin n)
    (a b : J) {c : ℝ} (ha : F.value i a ≤ c) (hb : c ≤ F.value i b) :
    ∃ T ∈ Set.uIcc a.val b.val, ∃ hT : T ∈ J, F.value i ⟨T,hT⟩ = c := by
  let K := Set.uIcc a.val b.val
  let f : K → J := fun T => ⟨T.val,hJ.uIcc_subset a.property b.property T.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have : PreconnectedSpace K := Subtype.preconnectedSpace (isPreconnected_uIcc : IsPreconnected K)
  have hc := (F.vertical i).continuous.comp hf
  obtain ⟨T,hT⟩ := intermediate_value_univ
    (⟨a.val,Set.left_mem_uIcc⟩ : K) (⟨b.val,Set.right_mem_uIcc⟩ : K) hc ⟨ha,hb⟩
  exact ⟨T.val,T.property,(f T).property,hT⟩

/-- Every intermediate scalar value on a switching path is attained on its
actual trace. Switch compatibility supplies continuity across the joins. -/
lemma path_intermediate (F : M.Field J L) (hJ : Set.OrdConnected J) {i j : Fin n}
    (p : M.Path J i j) (a b : J) {c : ℝ} (ha : F.value i a ≤ c) (hb : c ≤ F.value j b) :
    ∃ (v : Fin n) (T : J), (v,T.val) ∈ p.trace a.val b.val ∧ F.value v T = c := by
  induction p generalizing a with
  | nil i =>
    obtain ⟨T,hT,hTJ,he⟩ := F.vertical_intermediate hJ i a b ha hb
    exact ⟨i,⟨T,hTJ⟩,⟨rfl,hT⟩,he⟩
  | @cons i v j H hH hs p ih =>
    by_cases hc : c ≤ F.value i ⟨H,hH⟩
    · obtain ⟨T,hT,hTJ,he⟩ := F.vertical_intermediate hJ i a ⟨H,hH⟩ ha hc
      exact ⟨i,⟨T,hTJ⟩,Or.inl ⟨rfl,hT⟩,he⟩
    · have hh : F.value v ⟨H,hH⟩ ≤ c := by
        rw [← F.switch i v ⟨H,hH⟩ hs]
        exact (lt_of_not_ge hc).le
      obtain ⟨z,T,hT,he⟩ := ih ⟨H,hH⟩ hh hb
      exact ⟨z,T,Or.inr hT,he⟩

end Field


end Model
end Columns

end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Point
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}

lemma extendValue_point (f : M.Point J root → ℝ) (x : M.Point J root) :
    extendValue f x.column ⟨x.height,x.inBand⟩ = f x := by
  simp only [extendValue,dite_eq_left x.reachable]

/-- A continuous scalar intermediate value is attained on an actual shortest
switching path, with the exact metric betweenness identity. -/
lemma intermediate_between {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f)
    (hJ : IsClosed J) (hI : Set.OrdConnected J) (x y : M.Point J root) {c : ℝ}
    (hx : f x ≤ c) (hy : c ≤ f y) :
    ∃ z : M.Point J root, f z=c ∧ dist x z+dist z y=dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hJ y
  have hx' : (extendField f hf).value x.column ⟨x.height,x.inBand⟩ ≤ c := by
    simpa only [extendField,extendValue_point] using hx
  have hy' : c ≤ (extendField f hf).value y.column ⟨y.height,y.inBand⟩ := by
    simpa only [extendField,extendValue_point] using hy
  obtain ⟨i,H,hT,hF⟩ := (extendField f hf).path_intermediate hI p
    ⟨x.height,x.inBand⟩ ⟨y.height,y.inBand⟩ hx' hy'
  obtain ⟨q,r,hqr⟩ := p.trace_split hT
  let z : M.Point J root := ⟨i,H.val,H.property,x.reachable.trans q.word.reachable⟩
  have hz : f z=c := by
    change extendValue f z.column ⟨z.height,z.inBand⟩=c at hF
    rwa [extendValue_point] at hF
  refine ⟨z,hz,le_antisymm ?_ (dist_triangle x z y)⟩
  have hq := x.distance_le z q
  have hr := z.distance_le y r
  change dist x z ≤ q.length x.height H.val at hq
  change dist z y ≤ r.length H.val y.height at hr
  rw [← hp]
  linarith

end PlanarL1.Columns.Model.Point


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Crossings
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.ColumnOrder

/-- The combinatorial core of overlapping traversals: a path reaching a
middle profile value intersects any path crossing that value if each switch
has small profile error. Monotonicity is needed only on their common arc. -/
lemma overlapping_words {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S : Set (Fin n)} {q : Fin n → ℝ}
    (hq : MonotoneOn q S) {x x' y y' i : Fin n}
    (p : G.Walk x x') (r : G.Walk y y')
    (hp : ∀ v ∈ p.support, v ∈ S) (hr : ∀ v ∈ r.support, v ∈ S)
    (hi : i ∈ p.support) {δ : ℝ}
    (hx : q x + δ < q i) (hy : q y < q i) (hy' : q i < q y')
    (hs : ∀ e ∈ r.darts, |q e.fst - q e.snd| ≤ δ) :
    ∃ v, v ∈ p.support ∧ v ∈ r.support := by
  have order {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (h : q u < q v) : u < v := by
    by_contra hn
    have := hq hv hu (le_of_not_gt hn)
    linarith
  have hiy : y < i := order (hr y r.start_mem_support) (hp i hi) hy
  have hiy' : i < y' := order (hp i hi) (hr y' r.end_mem_support) hy'
  rcases visits_or_skips r hiy hiy' with hm | ⟨e,he,hea⟩
  · exact ⟨i,hi,hm⟩
  have hef : e.fst ∈ r.support := r.dart_fst_mem_support_of_mem_darts he
  have hes : e.snd ∈ r.support := r.dart_snd_mem_support_of_mem_darts he
  have core (a b : Fin n) (hab : G.Adj a b)
      (ha : a ∈ r.support) (hb : b ∈ r.support)
      (hai : a < i) (hib : i < b) (hgap : |q a - q b| ≤ δ) :
      ∃ v, v ∈ p.support ∧ v ∈ r.support := by
    have hibq := hq (hp i hi) (hr b hb) hib.le
    have hxa : q x < q a := by
      have hh := (abs_le.mp hgap).1
      linarith
    have hxa' := order (hp x p.start_mem_support) (hr a ha) hxa
    let t := (p.takeUntil i hi).reverse
    have hmem : ∀ v ∈ t.support, v ∈ p.support := by
      intro v hv
      apply (p.isSubwalk_takeUntil hi).support_subset
      simpa only [t,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    rcases chord_separation hnc hab t ⟨hai,hib⟩ (Or.inl hxa') with hm | hm
    · exact ⟨a,hmem a hm,ha⟩
    · exact ⟨b,hmem b hm,hb⟩
  rcases hea with hea | hea
  · exact core e.fst e.snd e.adj hef hes hea.1 hea.2 (hs e he)
  · exact core e.snd e.fst e.adj.symm hes hef hea.1 hea.2
      (by simpa only [abs_sub_comm] using hs e he)

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model

namespace Field

variable {n : ℕ} {M : Model n} {J : Set ℝ} {L : NNReal}

lemma profile_error (F : M.Field J L) {η : ℝ}
    (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η) (i : Fin n) (H T : J) :
    |F.value i H - F.value i T| ≤ L*η := by
  have he := (F.vertical i).dist_le_mul H T
  simp only [Real.dist_eq,Subtype.dist_eq] at he
  exact he.trans (mul_le_mul_of_nonneg_left (hw _ H.property _ T.property) L.coe_nonneg)

lemma profile_switch_error (F : M.Field J L) {η : ℝ}
    (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η) (H : J) {i j : Fin n}
    (hij : (M.activeGraph J).Adj i j) :
    |F.value i H - F.value j H| ≤ 2*(L*η) := by
  obtain ⟨T,hT,hs⟩ := hij
  have hi := F.profile_error hw i H ⟨T,hT⟩
  have hj := F.profile_error hw j ⟨T,hT⟩ H
  rw [← F.switch i j ⟨T,hT⟩ hs] at hj
  have ht := abs_sub_le (F.value i H) (F.value i ⟨T,hT⟩) (F.value j H)
  linarith

end Field
end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

/-- Stop at the first vertex outside a set. The constructed walk consists
only of original visited columns, and its last step crosses the set boundary. -/
lemma first_exit {V : Type*} {G : SimpleGraph V} {S : Set V} {x y : V}
    (p : G.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ a b, G.Adj a b ∧ a ∈ S ∧ b ∉ S ∧
      ∃ r : G.Walk x b,
        (∀ v ∈ r.support, v ∈ p.support) ∧
        (∀ v ∈ r.support, v ∈ S ∨ v = b) := by
  induction p with
  | nil => exact False.elim (hy hx)
  | @cons x z y hxz p ih =>
    by_cases hz : z ∈ S
    · obtain ⟨a,b,hab,ha,hb,r,hr,hS⟩ := ih hz hy
      refine ⟨a,b,hab,ha,hb,r.cons hxz,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons_of_mem _ (hr v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact Or.inl (hv ▸ hx)
        · exact hS v hv
    · refine ⟨x,z,hxz,hx,hz,(.nil : G.Walk z z).cons hxz,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · have he : v = z := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
          exact List.mem_cons_of_mem _ (he ▸ p.start_mem_support)
      · intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · exact Or.inl (hv ▸ hx)
        · right
          simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hv

/-- A discrete traversal of a value band. Every visited column lies in the
band enlarged by one switch error; no continuous path-parameter choice or
first/last hitting time is postulated. -/
lemma traverse_band {V : Type*} {G : SimpleGraph V} (q : V → ℝ) {δ u v : ℝ}
    (hδ : 0 ≤ δ) (huv : u < v) (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x y : V} (p : G.Walk x y) (hx : q x ≤ u) (hy : v ≤ q y) :
    ∃ a b, ∃ r : G.Walk a b,
      q a ≤ u ∧ v ≤ q b ∧
      (∀ z ∈ r.support, z ∈ p.support) ∧
      (∀ z ∈ r.support, u-δ ≤ q z ∧ q z ≤ v+δ) := by
  obtain ⟨a,b,hab,ha,hb,s,hs,hS⟩ := first_exit p
    (S := {z | q z < v}) (by dsimp; linarith) (by dsimp; linarith)
  change q a < v at ha
  change ¬q b < v at hb
  have hb' : v ≤ q b := le_of_not_gt hb
  have hbup : q b ≤ v+δ := by
    have := (abs_le.mp (hedge hab)).1
    linarith
  have hsupper (z) (hz : z ∈ s.support) : q z ≤ v+δ := by
    rcases hS z hz with hz | rfl
    · change q z < v at hz
      linarith
    · exact hbup
  obtain ⟨c,d,hcd,hc,hd,t,ht,hT⟩ := first_exit s.reverse
    (S := {z | u < q z}) (by dsimp; linarith) (by dsimp; linarith)
  change u < q c at hc
  change ¬u < q d at hd
  have hd' : q d ≤ u := le_of_not_gt hd
  have hdlow : u-δ ≤ q d := by
    have := (abs_le.mp (hedge hcd)).2
    linarith
  refine ⟨d,b,t.reverse,hd',hb',?_,?_⟩
  · intro z hz
    have hzt : z ∈ t.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    have hzs : z ∈ s.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht z hzt
    exact hs z hzs
  · intro z hz
    have hzt : z ∈ t.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    have hzs : z ∈ s.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht z hzt
    refine ⟨?_,hsupper z hzs⟩
    rcases hT z hzt with hz | rfl
    · change u < q z at hz
      linarith
    · exact hdlow

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model

namespace Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Every visited column of a path of length A from x has a point genuinely
reachable within A, even when the ambient metric permits leaving J. -/
lemma near_path (hJI : J ⊆ I) (x : M.Point I root) (hx : x.height ∈ J)
    {j : Fin n} (p : M.Path J x.column j) {H A : ℝ} (hH : H ∈ J)
    (hA : p.length x.height H ≤ A) :
    x.NearColumns J A {v | v ∈ p.word.support} := by
  intro v hv
  obtain ⟨T,hT,q,r,hqr⟩ := p.split_at_column hx hH hv
  let z : M.Point I root := ⟨v,T,hJI hT,x.reachable.trans (q.widen hJI).word.reachable⟩
  refine ⟨z,rfl,hT,?_⟩
  have hd := x.distance_le z (q.widen hJI)
  rw [Path.length_widen] at hd
  have hn := r.length_nonneg T H
  change x.distance z ≤ A
  dsimp only [z] at hd
  linarith

/-- Metric completion of the overlapping-traversal argument. Only one
vertical transfer is needed, hence eta rather than the source's 2 eta. -/
lemma dist_le_of_near_intersection (x y : M.Point I root) {A B η : ℝ}
    {S T : Set (Fin n)} (hx : x.NearColumns J A S) (hy : y.NearColumns J B T)
    (hw : ∀ a ∈ J, ∀ b ∈ J, |a-b| ≤ η) {v : Fin n} (hvS : v ∈ S) (hvT : v ∈ T) :
    dist x y ≤ A+B+η := by
  obtain ⟨z,hz,hzJ,hxz⟩ := hx v hvS
  obtain ⟨w,hwv,hwJ,hyw⟩ := hy v hvT
  have he := Point.dist_same_column z w (hz.trans hwv.symm)
  have hd := hw z.height hzJ w.height hwJ
  have h₁ := dist_triangle x z y
  have h₂ := dist_triangle z w y
  rw [dist_comm w y] at h₂
  linarith

end Point
end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

/-- A crosslink joining the two monotone arcs separates all strict lower
profile values from all strict upper values. This uses noncrossing of the
ambient graph, not an assumed connectivity of a scalar level set. -/
lemma ordered_chord_barrier {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) (f : Fin n → ℝ) (m : Fin n)
    (hleft : ∀ i j, i ≤ j → j ≤ m → f i ≤ f j)
    (hright : ∀ i j, m ≤ i → i ≤ j → f j ≤ f i)
    {a b x y : Fin n} (ham : a ≤ m) (hmb : m ≤ b)
    (hab : G.Adj a b) (heq : f a = f b)
    (p : G.Walk x y) (hx : f x < f a) (hy : f a < f y) :
    a ∈ p.support ∨ b ∈ p.support := by
  have hay : a < y := by
    by_contra hn
    have := hleft y a (le_of_not_gt hn) ham
    linarith
  have hyb : y < b := by
    by_contra hn
    have := hright b y hmb (le_of_not_gt hn)
    linarith
  have hside : x < a ∨ b < x := by
    by_cases hxm : x ≤ m
    · left
      by_contra hn
      have := hleft a x (le_of_not_gt hn) hxm
      linarith
    · right
      by_contra hn
      have := hright x b (le_of_not_ge hxm) (le_of_not_gt hn)
      linarith
  have hc := chord_separation hnc hab p.reverse ⟨hay,hyb⟩ hside
  simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hc

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k + 1)} {I J : Set ℝ} {L : NNReal}

lemma arcSign_one_lt {a b i : Fin (k+1)} (h : arcSign a b i = 1) :
    (finCycle a).symm i < (finCycle a).symm b := by
  unfold arcSign at h
  split_ifs at h with hbd hlt
  · norm_num at h
  · exact hlt
  · norm_num at h

lemma arcSign_neg_one_gt {a b i : Fin (k+1)} (h : arcSign a b i = -1) :
    (finCycle a).symm b < (finCycle a).symm i := by
  unfold arcSign at h
  split_ifs at h with hbd hlt
  · norm_num at h
  · norm_num at h
  · have hib : i ≠ b := fun he => hbd (Or.inr he)
    have he : (finCycle a).symm i ≠ (finCycle a).symm b := fun he => hib ((finCycle a).symm.injective he)
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)

/-- Actual crosslink barrier for arbitrary finite paths in any band. The
crosslink itself may be outside that band, as required by the empty-wall
rectangle argument. -/
lemma crosslink_barrier (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (H : I) {u v : Fin (k+1)} (hs : H.val ∈ M.heights u v)
    (hu : arcSign a b u = 1) (hv : arcSign a b v = -1)
    {x y : Fin (k+1)} (p : (M.activeGraph J).Walk x y)
    (hx : F.value x H < F.value u H) (hy : F.value u H < F.value y H) :
    u ∈ p.support ∨ v ∈ p.support := by
  let e := finCycle a
  let f := (SimpleGraph.Iso.comap e M.link).symm.toHom
  let q := (p.mapLe (M.active_subgraph J)).map f
  have hnc := ColumnOrder.noncrossing_comap_cycle M.noncrossing a
  have heq : F.value (e (e.symm u)) H = F.value (e (e.symm v)) H := by
    simpa only [e.apply_symm_apply] using F.switch u v H hs
  have hc := ColumnOrder.ordered_chord_barrier hnc (fun i => F.value (e i) H) (e.symm b)
    (ho.2.1 H) (ho.2.2 H) (arcSign_one_lt hu).le (arcSign_neg_one_gt hv).le
    (a := e.symm u) (b := e.symm v) (by change M.link.Adj (e (e.symm u)) (e (e.symm v)); simpa only [e.apply_symm_apply] using M.permitted u v H.val hs)
    heq q
    (by change F.value (e (e.symm x)) H < F.value (e (e.symm u)) H; simpa only [e.apply_symm_apply] using hx)
    (by change F.value (e (e.symm u)) H < F.value (e (e.symm y)) H; simpa only [e.apply_symm_apply] using hy)
  have mem (z : Fin (k+1)) (hz : e.symm z ∈ q.support) : z ∈ p.support := by
    rw [SimpleGraph.Walk.support_map,SimpleGraph.Walk.support_mapLe_eq_support,List.mem_map] at hz
    obtain ⟨w,hw,he⟩ := hz
    have hwe : w = z := e.symm.injective he
    exact hwe ▸ hw
  exact hc.elim (fun h => Or.inl (mem u h)) (fun h => Or.inr (mem v h))

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Two controlled column sets each hitting an endpoint of the same actual
link can be joined through that link at its prescribed height. -/
lemma dist_le_of_near_link (x y : M.Point I root) {A B D H : ℝ}
    {S T : Set (Fin n)} (hx : x.NearColumns J A S) (hy : y.NearColumns J B T)
    (hD : ∀ t ∈ J, |t-H| ≤ D) (hH : H ∈ I)
    {u v : Fin n} (hlink : H ∈ M.heights u v)
    (hp : u ∈ S ∨ v ∈ S) (hq : u ∈ T ∨ v ∈ T) :
    dist x y ≤ A+B+2*D := by
  have core (z w : M.Point I root) (hz : z.height ∈ J) (hw : w.height ∈ J)
      (hxz : dist x z ≤ A) (hyw : dist y w ≤ B)
      (hzw : z.column = w.column ∨ H ∈ M.heights z.column w.column) :
      dist x y ≤ A+B+2*D := by
    have hd : dist z w ≤ 2*D := by
      rcases hzw with hzw | hzw
      · rw [Point.dist_same_column z w hzw]
        have he := abs_sub_le z.height H w.height
        have hzD := hD z.height hz
        have hwD := hD w.height hw
        rw [abs_sub_comm H w.height] at he
        linarith
      · have he := z.dist_le_switch w hH hzw
        have hzD := hD z.height hz
        have hwD := hD w.height hw
        rw [abs_sub_comm H w.height] at he
        linarith
    have ht := dist_triangle x z y
    have ht' := dist_triangle z w y
    rw [dist_comm w y] at ht'
    linarith
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx u hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy u hq
    exact core z w hzJ hwJ hxz hyw (Or.inl (hz.trans hw.symm))
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx u hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy v hq
    exact core z w hzJ hwJ hxz hyw (Or.inr (by simpa only [hz,hw] using hlink))
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx v hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy u hq
    exact core z w hzJ hwJ hxz hyw (Or.inr (by simpa only [hz,hw,M.symm v u] using hlink))
  · obtain ⟨z,hz,hzJ,hxz⟩ := hx v hp
    obtain ⟨w,hw,hwJ,hyw⟩ := hy v hq
    exact core z w hzJ hwJ hxz hyw (Or.inl (hz.trans hw.symm))

end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal} {root : Fin (k+1)}

/-- Empty-wall rectangle, in its geometric form before inserting the source
constants. A hypothetical wall point between both controlled traversals
creates a quantitatively short ambient path. -/
lemma wall_traversal_distance (F : M.Field I L) {a b : Fin (k+1)}
    (ho : F.OrderedFrom a b) (H : I) {c A B D : ℝ}
    (hw : (c,H.val) ∈ F.wall a b)
    (x y : M.Point I root) {x₀ x₁ y₀ y₁ : Fin (k+1)}
    (p : (M.activeGraph J).Walk x₀ x₁) (q : (M.activeGraph J).Walk y₀ y₁)
    (hp : x.NearColumns J A {v | v ∈ p.support})
    (hq : y.NearColumns J B {v | v ∈ q.support})
    (hD : ∀ t ∈ J, |t-H.val| ≤ D)
    (hx₀ : F.value x₀ H < c) (hx₁ : c < F.value x₁ H)
    (hy₀ : F.value y₀ H < c) (hy₁ : c < F.value y₁ H) :
    dist x y ≤ A+B+2*D := by
  rcases hw with ⟨T,he⟩ | ⟨T,he⟩ | ⟨u,v,T,hs,hu,hv,he⟩
  · have hT : T = H := Subtype.ext (congrArg Prod.snd he).symm
    subst T
    have hc : c = F.value a H := congrArg Prod.fst he
    have := ho.1 H x₀
    exfalso
    linarith
  · have hT : T = H := Subtype.ext (congrArg Prod.snd he).symm
    subst T
    have hc : c = F.value b H := congrArg Prod.fst he
    have := F.ordered_maximum ho H x₁
    exfalso
    linarith
  · have hT : T = H := Subtype.ext (congrArg Prod.snd he).symm
    subst T
    have hc : c = F.value u H := congrArg Prod.fst he
    have hpu := F.crosslink_barrier ho H hs hu hv p (by rwa [← hc]) (by rwa [← hc])
    have hqu := F.crosslink_barrier ho H hs hu hv q (by rwa [← hc]) (by rwa [← hc])
    exact x.dist_le_of_near_link y hp hq hD H.property hs hpu hqu

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {L : NNReal} {root : Fin n}

namespace Excursions

variable {F : M.Field I L} {hJI : J ⊆ I} {z : M.Point I root} {A ε : ℝ}

lemma near_traversal (E : F.Excursions hJI z A ε) :
    z.NearColumns J A {v | v ∈ E.traversal.support} := by
  have hlo := z.near_path hJI E.inBand E.lowPath E.lowHeight.property E.lowLength
  have hhi := z.near_path hJI E.inBand E.highPath E.highHeight.property E.highLength
  intro v hv
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
  · exact hlo v (by
      change v ∈ E.lowPath.word.support
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv)
  · exact hhi v hv

lemma low_profile (E : F.Excursions hJI z A ε) (H : I) {D : ℝ}
    (hD : ∀ t ∈ J, |t-H.val| ≤ D) :
    F.value E.lowColumn H < F.eval z - ε + L*D := by
  have h := (F.vertical E.lowColumn).dist_le_mul
    (⟨E.lowHeight.val,hJI E.lowHeight.property⟩ : I) H
  simp only [Real.dist_eq,Subtype.dist_eq] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left (hD _ E.lowHeight.property) L.coe_nonneg)
  have h'' := (abs_le.mp h').1
  linarith [E.lowValue]

lemma high_profile (E : F.Excursions hJI z A ε) (H : I) {D : ℝ}
    (hD : ∀ t ∈ J, |t-H.val| ≤ D) :
    F.eval z + ε - L*D < F.value E.highColumn H := by
  have h := (F.vertical E.highColumn).dist_le_mul
    (⟨E.highHeight.val,hJI E.highHeight.property⟩ : I) H
  simp only [Real.dist_eq,Subtype.dist_eq] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left (hD _ E.highHeight.property) L.coe_nonneg)
  have h'' := (abs_le.mp h').2
  linarith [E.highValue]

end Excursions

/-- The closed wall-free rectangle with the manuscript's exact numerical
margins, uniform in every field, every finite column model and every size. -/
lemma empty_rectangle {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {root : Fin (k+1)}
    (F : M.Field I 4) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    {R η : ℝ} (hR : 0 < R) (hη : η ≤ R/1000000)
    (hJI : J ⊆ I) (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ η)
    (x y : M.Point I root)
    (Ex : F.Excursions hJI x (2*R) (2*R/5))
    (Ey : F.Excursions hJI y (2*R) (2*R/5))
    (hclose : |F.eval x-F.eval y| ≤ R/1000)
    (hfar : 4*R+2*(R/50+η) < dist x y)
    (H : I) {c : ℝ} (hc : |c-F.eval x| ≤ R/5) (hH : |H.val-x.height| ≤ R/50) :
    (c,H.val) ∉ F.wall a b := by
  intro hwall
  have hD : ∀ t ∈ J, |t-H.val| ≤ R/50+η := by
    intro t ht
    have h := abs_sub_le t x.height H.val
    have h' := hw t ht x.height Ex.inBand
    rw [abs_sub_comm x.height H.val] at h
    linarith
  have hxlo := Ex.low_profile H hD
  have hxhi := Ex.high_profile H hD
  have hylo := Ey.low_profile H hD
  have hyhi := Ey.high_profile H hD
  have hcv := abs_le.mp hc
  have hxy := abs_le.mp hclose
  norm_num only [NNReal.coe_ofNat] at hxlo hxhi hylo hyhi
  have hd := F.wall_traversal_distance ho H hwall x y Ex.traversal Ey.traversal
    Ex.near_traversal Ey.near_traversal hD
    (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- Quantitative wall avoidance implies an infimum-distance bound at any
center whose max-norm ball fits into the verified empty rectangle. -/
lemma infDist_lower_of_rectangle {k : ℕ} {M : Model (k+1)} {I : Set ℝ} {L : NNReal}
    (F : M.Field I L) (a b : Fin (k+1)) (T : I)
    {s h U V r : ℝ}
    (hempty : ∀ (c : ℝ) (H : I), |c-s| ≤ U → |H.val-h| ≤ V → (c,H.val) ∉ F.wall a b)
    (i : Fin (k+1)) (hU : |F.value i T-s|+r ≤ U) (hV : |T.val-h|+r ≤ V) :
    r ≤ Metric.infDist (F.value i T,T.val) (F.wall a b) := by
  apply (Metric.le_infDist (F.wall_nonempty a b T)).mpr
  intro z hz
  by_contra hn
  have hd : dist (F.value i T,T.val) z < r := lt_of_not_ge hn
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff] at hd
  have hzu : |z.1-s| ≤ U := by
    have ht := abs_sub_le z.1 (F.value i T) s
    rw [abs_sub_comm z.1 (F.value i T)] at ht
    linarith
  have hzv : |z.2-h| ≤ V := by
    have ht := abs_sub_le z.2 T.val h
    rw [abs_sub_comm z.2 T.val] at ht
    linarith
  have hzI : z.2 ∈ I := by
    rcases hz with ⟨H,rfl⟩ | ⟨H,rfl⟩ | ⟨u,v,H,_,_,_,rfl⟩ <;> exact H.property
  exact hempty z.1 ⟨z.2,hzI⟩ hzu hzv hz

end PlanarL1.Columns.Model.Field

namespace PlanarL1.ColumnOrder

/-- Discrete profile intervals suffice for overlap. The midpoint visit is
constructed by stopping at the first exiting column, including its switch error. -/
lemma overlapping_ranges {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {S : Set (Fin n)} {q : Fin n → ℝ} (hq : MonotoneOn q S)
    {δ u v : ℝ} (hgap : 2*δ < v-u)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x x' y y' : Fin n} (p : G.Walk x x') (r : G.Walk y y')
    (hp : ∀ z ∈ p.support, z ∈ S) (hr : ∀ z ∈ r.support, z ∈ S)
    (hx : q x ≤ u) (hx' : v ≤ q x') (hy : q y ≤ u) (hy' : v ≤ q y')
    (hδ : 0 ≤ δ) : ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  obtain ⟨a,b,hab,ha,hb,t,ht,_⟩ := first_exit p
    (S := {z | q z < (u+v)/2}) (by dsimp; linarith) (by dsimp; linarith)
  change q a < (u+v)/2 at ha
  change ¬q b < (u+v)/2 at hb
  have hb' : (u+v)/2 ≤ q b := le_of_not_gt hb
  have hbup : q b < (u+v)/2+δ := by
    have := (abs_le.mp (hedge hab)).1
    linarith
  exact overlapping_words hnc hq p r hp hr (ht b t.end_mem_support)
    (by linarith) (by linarith) (by linarith) (fun e _ => hedge e.adj)

lemma overlapping_ranges_anti {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {S : Set (Fin n)} {q : Fin n → ℝ} (hq : AntitoneOn q S)
    {δ u v : ℝ} (hgap : 2*δ < v-u)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x x' y y' : Fin n} (p : G.Walk x x') (r : G.Walk y y')
    (hp : ∀ z ∈ p.support, z ∈ S) (hr : ∀ z ∈ r.support, z ∈ S)
    (hx : q x ≤ u) (hx' : v ≤ q x') (hy : q y ≤ u) (hy' : v ≤ q y')
    (hδ : 0 ≤ δ) : ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  have hmono : MonotoneOn (fun z => -q z) S := by
    intro i hi j hj hij
    exact neg_le_neg (hq hi hj hij)
  have he {a b} (h : G.Adj a b) : |(-q a)-(-q b)| ≤ δ := by
    simpa only [neg_sub_neg,abs_sub_comm] using hedge h
  have hp' : ∀ z ∈ p.reverse.support, z ∈ S := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse]
  have hr' : ∀ z ∈ r.reverse.support, z ∈ S := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse]
  obtain ⟨z,hz,hz'⟩ := overlapping_ranges hnc hmono (u := -v) (v := -u)
    (by linarith) he p.reverse r.reverse hp' hr'
    (by linarith) (by linarith) (by linarith) (by linarith) hδ
  exact ⟨z,by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz,
    by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz'⟩

lemma walk_label_const {V K : Type*} {G : SimpleGraph V} {S : Set V} (label : V → K)
    (hedge : ∀ {a b}, G.Adj a b → a ∈ S → b ∈ S → label a = label b)
    {x y : V} (p : G.Walk x y) (hp : ∀ v ∈ p.support, v ∈ S) :
    ∀ v ∈ p.support, label v = label x := by
  induction p with
  | @nil x =>
    intro v hv
    have hv' : v = x := by simpa using hv
    subst v
    rfl
  | @cons x z y hxz p ih =>
    have hp' : ∀ v ∈ p.support, v ∈ S := fun v hv => hp v (List.mem_cons_of_mem x hv)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · rfl
    · exact (ih hp' v hv).trans (hedge hxz (hp x (List.mem_cons_self ..))
        (hp' z p.start_mem_support)).symm

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal}

/-- Profile overlap on either open arc; the cyclic relabelling and the
antitone second arc are both explicit. -/
lemma same_arc_overlap (F : M.Field I L) {a b : Fin (k+1)}
    (ho : F.OrderedFrom a b) (H : I) {δ u v σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hδ : 0 ≤ δ) (hgap : 2*δ < v-u)
    (hedge : ∀ {i j}, (M.activeGraph J).Adj i j → |F.value i H-F.value j H| ≤ δ)
    {x x' y y' : Fin (k+1)} (p : (M.activeGraph J).Walk x x')
    (r : (M.activeGraph J).Walk y y')
    (hp : ∀ z ∈ p.support, arcSign a b z = σ)
    (hr : ∀ z ∈ r.support, arcSign a b z = σ)
    (hx : F.value x H ≤ u) (hx' : v ≤ F.value x' H)
    (hy : F.value y H ≤ u) (hy' : v ≤ F.value y' H) :
    ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  let e := finCycle a
  let f := (SimpleGraph.Iso.comap e (M.activeGraph J)).symm.toHom
  let P := p.map f
  let Q := r.map f
  let S : Set (Fin (k+1)) := {i | arcSign a b (e i) = σ}
  have mem {i j : Fin (k+1)} (t : (M.activeGraph J).Walk i j) {z}
      (hz : z ∈ (t.map f).support) : e z ∈ t.support := by
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    change e (e.symm w) ∈ t.support
    simpa only [e.apply_symm_apply] using hw
  have hP : ∀ z ∈ P.support, z ∈ S := fun z hz => hp _ (mem p hz)
  have hQ : ∀ z ∈ Q.support, z ∈ S := fun z hz => hr _ (mem r hz)
  have he {i j} (h : ((M.activeGraph J).comap e).Adj i j) :
      |F.value (e i) H-F.value (e j) H| ≤ δ := hedge h
  have hx0 : F.value (e (e.symm x)) H ≤ u := by simpa only [e.apply_symm_apply] using hx
  have hx1 : v ≤ F.value (e (e.symm x')) H := by simpa only [e.apply_symm_apply] using hx'
  have hy0 : F.value (e (e.symm y)) H ≤ u := by simpa only [e.apply_symm_apply] using hy
  have hy1 : v ≤ F.value (e (e.symm y')) H := by simpa only [e.apply_symm_apply] using hy'
  have hnc := ColumnOrder.noncrossing_comap_cycle (M.active_noncrossing J) a
  have hit : ∃ z, z ∈ P.support ∧ z ∈ Q.support := by
    rcases hσ with rfl | rfl
    · have hmono : MonotoneOn (fun i => F.value (e i) H) S := by
        intro i hi j hj hij
        have hjb := arcSign_one_lt hj
        simp only [e,Equiv.symm_apply_apply] at hjb
        exact ho.2.1 H i j hij hjb.le
      exact ColumnOrder.overlapping_ranges hnc hmono hgap he P Q hP hQ hx0 hx1 hy0 hy1 hδ
    · have hanti : AntitoneOn (fun i => F.value (e i) H) S := by
        intro i hi j hj hij
        have hib := arcSign_neg_one_gt hi
        simp only [e,Equiv.symm_apply_apply] at hib
        exact ho.2.2 H i j hib.le hij
      exact ColumnOrder.overlapping_ranges_anti hnc hanti hgap he P Q hP hQ hx0 hx1 hy0 hy1 hδ
  obtain ⟨z,hz,hz'⟩ := hit
  exact ⟨e z,mem p hz,mem r hz'⟩

/-- An empty wall rectangle rules out every boundary column and every
side-changing active switch in a slightly narrower reference-profile strip. -/
lemma strip_arc_const (F : M.Field I L) (a b : Fin (k+1)) (T : I)
    (hJI : J ⊆ I) {s h U V W D : ℝ}
    (hempty : ∀ (c : ℝ) (H : I), |c-s| ≤ U → |H.val-h| ≤ V → (c,H.val) ∉ F.wall a b)
    (hT : |T.val-h| ≤ V) (hD : ∀ t ∈ J, |t-T.val| ≤ D)
    (hV : ∀ t ∈ J, |t-h| ≤ V) (hW : W+L*D ≤ U) (hD0 : 0 ≤ D) :
    (∀ i, |F.value i T-s| ≤ W → arcSign a b i ≠ 0) ∧
    (∀ {i j}, (M.activeGraph J).Adj i j → |F.value i T-s| ≤ W →
      |F.value j T-s| ≤ W → arcSign a b i = arcSign a b j) := by
  constructor
  · intro i hi hz
    exact hempty _ T (by nlinarith [L.coe_nonneg]) hT (F.wall_of_boundary a b i T hz)
  · intro i j hij hi _
    by_contra hne
    obtain ⟨t,ht,hs⟩ := hij
    let H : I := ⟨t,hJI ht⟩
    have hlip := (F.vertical i).dist_le_mul H T
    simp only [Real.dist_eq,Subtype.dist_eq] at hlip
    have he : |F.value i H-F.value i T| ≤ L*D := hlip.trans
      (mul_le_mul_of_nonneg_left (hD t ht) L.coe_nonneg)
    have hc : |F.value i H-s| ≤ U :=
      (abs_sub_le _ _ _).trans (by linarith)
    exact hempty _ H hc (hV t ht) (F.wall_of_switch a b i j H hs hne)

end PlanarL1.Columns.Model.Field

namespace PlanarL1.ColumnOrder

/-- A center-to-exit traversal of a scalar strip, with the visited center
retained and the support enlarged by only one edge error. -/
lemma center_exit_band {V : Type*} {G : SimpleGraph V} (q : V → ℝ)
    {s r c δ : ℝ} (hcr : c < r) (hδ : 0 ≤ δ)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    {x y : V} (p : G.Walk x y) (hx : |q x-s| ≤ c) (hy : s+r ≤ q y) :
    ∃ a b, ∃ t : G.Walk a b,
      (∀ z ∈ t.support, z ∈ p.support) ∧ x ∈ t.support ∧
      (∀ z ∈ t.support, |q z-s| ≤ r+δ) ∧
      ((q a ≤ s+c ∧ s+r ≤ q b) ∨ (q a ≤ s-r ∧ s-c ≤ q b)) := by
  obtain ⟨a,b,hab,ha,hb,t,ht,hT⟩ := first_exit p
    (S := {z | |q z-s| < r}) (lt_of_le_of_lt hx hcr)
    (by intro h; change |q y-s| < r at h; have := (abs_lt.mp h).2; linarith)
  change |q a-s| < r at ha
  change ¬|q b-s| < r at hb
  have hbabs : |q b-s| ≤ r+δ := by
    have hed := hedge hab
    rw [abs_sub_comm] at hed
    exact (abs_sub_le _ _ _).trans (by linarith)
  have hband : ∀ z ∈ t.support, |q z-s| ≤ r+δ := by
    intro z hz
    rcases hT z hz with hz | rfl
    · change |q z-s| < r at hz
      linarith
    · exact hbabs
  have hout : q b ≤ s-r ∨ s+r ≤ q b := by
    by_contra hn
    push Not at hn
    exact hb (abs_lt.mpr ⟨by linarith,by linarith⟩)
  rcases hout with hlo | hhi
  · refine ⟨b,x,t.reverse,?_,?_,?_,Or.inr ⟨hlo,?_⟩⟩
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ht
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using t.start_mem_support
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hband
    · have := (abs_le.mp hx).1; linarith
  · refine ⟨x,b,t,ht,t.start_mem_support,hband,Or.inl ⟨?_,hhi⟩⟩
    have := (abs_le.mp hx).2; linarith

end PlanarL1.ColumnOrder

namespace PlanarL1.ColumnOrder

/-- Two disjoint low-to-high traversals, each issuing from a central column,
must have opposite central labels when the strip has precisely two lanes and
same-lane overlapping ranges intersect. This is the finite-word form of the
last two paragraphs of 's two-side argument. -/
lemma two_lane_centers {V : Type*} {G : SimpleGraph V} (q label : V → ℝ)
    {s r c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hgap : 2*δ < r-c)
    (hedge : ∀ {a b}, G.Adj a b → |q a-q b| ≤ δ)
    (hlabels : ∀ z, |q z-s| ≤ r+δ → label z = 1 ∨ label z = -1)
    (hconstant : ∀ {a b}, G.Adj a b → |q a-s| ≤ r+δ → |q b-s| ≤ r+δ → label a = label b)
    (hover : ∀ {a b d e : V} (p : G.Walk a b) (t : G.Walk d e) {u v σ : ℝ},
      σ = 1 ∨ σ = -1 → 2*δ < v-u →
      (∀ z ∈ p.support, label z = σ) → (∀ z ∈ t.support, label z = σ) →
      q a ≤ u → v ≤ q b → q d ≤ u → v ≤ q e →
      ∃ z, z ∈ p.support ∧ z ∈ t.support)
    {x₀ x₁ y₀ y₁ x y : V} (P : G.Walk x₀ x₁) (Q : G.Walk y₀ y₁)
    (U : G.Walk x x₁) (Vw : G.Walk y y₁)
    (hU : ∀ z ∈ U.support, z ∈ P.support) (hV : ∀ z ∈ Vw.support, z ∈ Q.support)
    (hx₀ : q x₀ ≤ s-r) (hx₁ : s+r ≤ q x₁)
    (hy₀ : q y₀ ≤ s-r) (hy₁ : s+r ≤ q y₁)
    (hx : |q x-s| ≤ c) (hy : |q y-s| ≤ c)
    (hdisj : ∀ z ∈ P.support, z ∉ Q.support) : label x ≠ label y := by
  have hr : 0 < r := by linarith
  have hcr : c < r := by linarith
  have fullgap : 2*δ < (s+r)-(s-r) := by linarith
  have band {z : V} (hz : s-r-δ ≤ q z ∧ q z ≤ s+r+δ) : |q z-s| ≤ r+δ :=
    abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  obtain ⟨a,b,p,ha,hb,hp,hpb⟩ := traverse_band q hδ (by linarith : s-r < s+r) hedge P hx₀ hx₁
  obtain ⟨d,e,t,hd,he,ht,htb⟩ := traverse_band q hδ (by linarith : s-r < s+r) hedge Q hy₀ hy₁
  have hpa : ∀ z ∈ p.support, label z = label a :=
    walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant p (fun z hz => band (hpb z hz))
  have htd : ∀ z ∈ t.support, label z = label d :=
    walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant t (fun z hz => band (htb z hz))
  have hα := hlabels a (band (hpb a p.start_mem_support))
  have hβ := hlabels d (band (htb d t.start_mem_support))
  have hαβ : label a ≠ label d := by
    intro heq
    obtain ⟨z,hz,hz'⟩ := hover p t hα fullgap hpa
      (fun z hz => (htd z hz).trans heq.symm) ha hb hd he
    exact hdisj z (hp z hz) (ht z hz')
  obtain ⟨a',b',p',hp',hxp',hp'b,hprange⟩ := center_exit_band q hcr hδ hedge U hx hx₁
  obtain ⟨d',e',t',ht',hyt',ht'b,htrange⟩ := center_exit_band q hcr hδ hedge Vw hy hy₁
  have hpx : ∀ z ∈ p'.support, label z = label x := by
    have hl := walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant p' hp'b
    intro z hz
    exact (hl z hz).trans (hl x hxp').symm
  have hty : ∀ z ∈ t'.support, label z = label y := by
    have hl := walk_label_const label (S := {z | |q z-s| ≤ r+δ}) hconstant t' ht'b
    intro z hz
    exact (hl z hz).trans (hl y hyt').symm
  have hγ := hlabels x (by linarith : |q x-s| ≤ r+δ)
  intro hxy
  by_cases hαx : label a = label x
  · have htt : ∀ z ∈ t'.support, label z = label a :=
      fun z hz => (hty z hz).trans (hxy.symm.trans hαx.symm)
    have hit : ∃ z, z ∈ p.support ∧ z ∈ t'.support := by
      rcases htrange with hl | hl
      · exact hover p t' hα (by linarith : 2*δ < (s+r)-(s+c)) hpa htt
          (by linarith) hb hl.1 hl.2
      · exact hover p t' hα (by linarith : 2*δ < (s-c)-(s-r)) hpa htt
          ha (by linarith) hl.1 hl.2
    obtain ⟨z,hz,hz'⟩ := hit
    exact hdisj z (hp z hz) (hV z (ht' z hz'))
  · have hβx : label d = label x := by
      rcases hα with hα | hα
      · rcases hβ with hβ | hβ
        · exact False.elim (hαβ (hα.trans hβ.symm))
        · rcases hγ with hγ | hγ
          · exact False.elim (hαx (hα.trans hγ.symm))
          · exact hβ.trans hγ.symm
      · rcases hβ with hβ | hβ
        · rcases hγ with hγ | hγ
          · exact hβ.trans hγ.symm
          · exact False.elim (hαx (hα.trans hγ.symm))
        · exact False.elim (hαβ (hα.trans hβ.symm))
    have hpp : ∀ z ∈ p'.support, label z = label d := fun z hz => (hpx z hz).trans hβx.symm
    have hit : ∃ z, z ∈ p'.support ∧ z ∈ t.support := by
      rcases hprange with hl | hl
      · exact hover p' t hβ (by linarith : 2*δ < (s+r)-(s+c)) hpp htd
          hl.1 hl.2 (by linarith) he
      · exact hover p' t hβ (by linarith : 2*δ < (s-c)-(s-r)) hpp htd
          hl.1 hl.2 hd (by linarith)
    obtain ⟨z,hz,hz'⟩ := hit
    exact hdisj z (hU z (hp' z hz)) (ht z hz')

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal}

/-- Quantitative opposite-arc conclusion from genuine short excursions. The
only extra displayed inequality says exactly that the constructed short join
would contradict the given separation; at R=10^-8 it follows from d≥1. -/
lemma two_side_arcs (F : M.Field I 4) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    {root : Fin (k+1)} {R η : ℝ} (hR : 0 < R) (hη : η ≤ R/1000000)
    (hJI : J ⊆ I) (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ η)
    (x y : M.Point I root)
    (Ex : F.Excursions hJI x (2*R) (2*R/5))
    (Ey : F.Excursions hJI y (2*R) (2*R/5))
    (hclose : |F.eval x-F.eval y| ≤ R/1000)
    (hfar : 4*R+2*(R/50+η) < dist x y) :
    arcSign a b x.column ≠ 0 ∧ arcSign a b y.column ≠ 0 ∧
    arcSign a b x.column ≠ arcSign a b y.column ∧
    R/100 ≤ Metric.infDist (F.eval x,x.height) (F.wall a b) ∧
    R/100 ≤ Metric.infDist (F.eval y,y.height) (F.wall a b) := by
  let T : I := ⟨x.height,x.inBand⟩
  let s := F.eval x
  let q : Fin (k+1) → ℝ := fun i => F.value i T
  have hη0 : 0 ≤ η := by simpa using hw x.height Ex.inBand x.height Ex.inBand
  have hD : ∀ t ∈ J, |t-T.val| ≤ η := fun t ht => hw t ht x.height Ex.inBand
  have hempty : ∀ (c : ℝ) (H : I), |c-s| ≤ R/5 → |H.val-x.height| ≤ R/50 →
      (c,H.val) ∉ F.wall a b := fun c H hc hH =>
    F.empty_rectangle ho hR hη hJI hw x y Ex Ey hclose hfar H hc hH
  have hstrip := F.strip_arc_const a b T hJI (s := s) (h := x.height)
    (U := R/5) (V := R/50) (W := R/6+8*η) (D := η) hempty
    (by dsimp [T]; rw [sub_self,abs_zero]; linarith) hD
    (fun t ht => (hD t ht).trans (by linarith))
    (by norm_num; linarith) hη0
  have he {i j} (hij : (M.activeGraph J).Adj i j) : |q i-q j| ≤ 8*η := by
    have hh := (F.restrict hJI).profile_switch_error hw (⟨x.height,Ex.inBand⟩ : J) hij
    change |q i-q j| ≤ 2*(4*η) at hh
    linarith
  have hlabels (z) (hz : |q z-s| ≤ R/6+8*η) : arcSign a b z = 1 ∨ arcSign a b z = -1 := by
    rcases arcSign_cases a b z with hz0 | hz1 | hz1
    · exact False.elim (hstrip.1 z hz hz0)
    · exact Or.inl hz1
    · exact Or.inr hz1
  have hqx : |q x.column-s| ≤ R/100 := by simp only [q,T,s,eval,sub_self,abs_zero]; linarith
  have hqy : |q y.column-s| ≤ R/100 := by
    have hp := (F.restrict hJI).profile_error hw y.column
      (⟨x.height,Ex.inBand⟩ : J) ⟨y.height,Ey.inBand⟩
    change |q y.column-F.eval y| ≤ 4*η at hp
    have hh := abs_sub_le (q y.column) (F.eval y) s
    have hcl : |F.eval y-s| ≤ R/1000 := by simpa only [s,abs_sub_comm] using hclose
    linarith
  have hxl := Ex.low_profile T hD
  have hxh := Ex.high_profile T hD
  have hyl := Ey.low_profile T hD
  have hyh := Ey.high_profile T hD
  norm_num only [NNReal.coe_ofNat] at hxl hxh hyl hyh
  have hcl := abs_le.mp hclose
  have disj : ∀ z ∈ Ex.traversal.support, z ∉ Ey.traversal.support := by
    intro z hz hz'
    have hd := x.dist_le_of_near_intersection y Ex.near_traversal Ey.near_traversal hw hz hz'
    linarith
  have hU : ∀ z ∈ Ex.highPath.word.support, z ∈ Ex.traversal.support := by
    intro z hz
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr hz)
  have hV : ∀ z ∈ Ey.highPath.word.support, z ∈ Ey.traversal.support := by
    intro z hz
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr hz)
  have hneq := ColumnOrder.two_lane_centers q (arcSign a b) (s := s)
    (r := R/6) (c := R/100) (δ := 8*η) (by linarith) (by linarith) (by linarith)
    he hlabels hstrip.2
    (fun {i j l m} p t {u v σ} hσ hg hp ht hl hh hl' hh' => F.same_arc_overlap ho T hσ
      (by linarith) hg he p t hp ht hl hh hl' hh')
    Ex.traversal Ey.traversal Ex.highPath.word Ey.highPath.word hU hV
    (by change F.value Ex.lowColumn T ≤ F.eval x-R/6; linarith)
    (by change F.eval x+R/6 ≤ F.value Ex.highColumn T; linarith)
    (by change F.value Ey.lowColumn T ≤ F.eval x-R/6; linarith)
    (by change F.eval x+R/6 ≤ F.value Ey.highColumn T; linarith)
    hqx hqy disj
  refine ⟨hstrip.1 x.column (by linarith),hstrip.1 y.column (by linarith),hneq,?_,?_⟩
  · exact F.infDist_lower_of_rectangle a b T hempty x.column
      (by change |F.eval x-F.eval x|+R/100 ≤ R/5; rw [sub_self,abs_zero]; linarith)
      (by change |x.height-x.height|+R/100 ≤ R/50; rw [sub_self,abs_zero]; linarith)
  · exact F.infDist_lower_of_rectangle a b ⟨y.height,y.inBand⟩ hempty y.column
      (by change |F.eval y-F.eval x|+R/100 ≤ R/5; rw [abs_sub_comm]; linarith)
      (by have hh := hw y.height Ey.inBand x.height Ex.inBand; dsimp; linarith)

lemma abs_add_eq_abs_sub_of_opposite {u v : ℝ} (huv : u*v < 0) : |u|+|v| = |u-v| := by
  by_cases hu : 0 ≤ u
  · have hv : v < 0 := by nlinarith
    rw [abs_of_nonneg hu,abs_of_neg hv,abs_of_nonneg (by linarith : 0 ≤ u-v)]
    ring
  · have hu' : u < 0 := lt_of_not_ge hu
    have hv : 0 < v := by nlinarith
    rw [abs_of_neg hu',abs_of_pos hv,abs_of_neg (by linarith : u-v < 0)]
    ring

/-- Full quantitative two-side lemma (, ord:two-side) in intrinsic
band coordinates. An ambient application uses the source hypothesis d_I=d. -/
theorem two_side (F : M.Field I 4) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (hI : IsClosed I) {root : Fin (k+1)} {η : ℝ}
    (hη : η ≤ (1:ℝ)/100000000/1000000)
    (hJI : J ⊆ I) (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ η)
    (x y : M.Point I root) (hlo : 1 ≤ dist x y) (hhi : dist x y ≤ 2)
    (Ex : F.Excursions hJI x (2*((1:ℝ)/100000000)) (2*((1:ℝ)/100000000)/5))
    (Ey : F.Excursions hJI y (2*((1:ℝ)/100000000)) (2*((1:ℝ)/100000000)/5))
    (hclose : |F.eval x-F.eval y| ≤ (1:ℝ)/100000000/1000) :
    (F.transverse (by norm_num) a b).eval x * (F.transverse (by norm_num) a b).eval y < 0 ∧
    (1:ℝ)/100000000/100 ≤ |(F.transverse (by norm_num) a b).eval x| ∧
    (1:ℝ)/100000000/100 ≤ |(F.transverse (by norm_num) a b).eval y| ∧
    |(F.transverse (by norm_num) a b).eval x| ≤ 8 ∧
    |(F.transverse (by norm_num) a b).eval y| ≤ 8 := by
  obtain ⟨hx,hy,hneq,hDx,hDy⟩ := F.two_side_arcs ho (by norm_num) hη hJI hw x y Ex Ey hclose (by linarith)
  let tx := (F.transverse (by norm_num) a b).eval x
  let ty := (F.transverse (by norm_num) a b).eval y
  have hax : |tx| = Metric.infDist (F.eval x,x.height) (F.wall a b) :=
    F.transverse_abs a b x.column ⟨x.height,x.inBand⟩ hx
  have hay : |ty| = Metric.infDist (F.eval y,y.height) (F.wall a b) :=
    F.transverse_abs a b y.column ⟨y.height,y.inBand⟩ hy
  have hDx0 : 0 < Metric.infDist (F.eval x,x.height) (F.wall a b) := lt_of_lt_of_le (by norm_num) hDx
  have hDy0 : 0 < Metric.infDist (F.eval y,y.height) (F.wall a b) := lt_of_lt_of_le (by norm_num) hDy
  have hprod : tx*ty < 0 := by
    change (arcSign a b x.column * _) * (arcSign a b y.column * _) < 0
    rcases arcSign_cases a b x.column with hx0 | hx1 | hx1
    · exact False.elim (hx hx0)
    · rcases arcSign_cases a b y.column with hy0 | hy1 | hy1
      · exact False.elim (hy hy0)
      · exact False.elim (hneq (hx1.trans hy1.symm))
      · rw [hx1,hy1,one_mul,neg_one_mul,mul_neg]
        exact neg_neg_of_pos (mul_pos hDx0 hDy0)
    · rcases arcSign_cases a b y.column with hy0 | hy1 | hy1
      · exact False.elim (hy hy0)
      · rw [hx1,hy1,one_mul,neg_one_mul,neg_mul]
        exact neg_neg_of_pos (mul_pos hDx0 hDy0)
      · exact False.elim (hneq (hx1.trans hy1.symm))
  have hd := ((F.transverse (by norm_num) a b).lipschitz hI root).dist_le_mul x y
  change dist tx ty ≤ (4:NNReal)*dist x y at hd
  rw [Real.dist_eq] at hd
  norm_num only [NNReal.coe_ofNat] at hd
  have hsum := abs_add_eq_abs_sub_of_opposite hprod
  refine ⟨hprod,by rwa [hax],by rwa [hay],?_,?_⟩ <;> linarith [abs_nonneg tx,abs_nonneg ty]

end PlanarL1.Columns.Model.Field


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SeedPacking
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
/-! ## The metric counting step of the restricted packing bound
Padded surviving seeds lie near two short paths, giving a cardinality
estimate without a doubling assumption.
-/
namespace Packing

lemma same_bucket_close {t u ε : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (h : ⌊t / ε⌋₊ = ⌊u / ε⌋₊) : |t - u| < ε := by
  have ht₀ := Nat.floor_le (div_nonneg ht hε.le)
  have hu₀ := Nat.floor_le (div_nonneg hu hε.le)
  have ht₁ := Nat.lt_floor_add_one (t / ε)
  have hu₁ := Nat.lt_floor_add_one (u / ε)
  rw [h] at ht₀ ht₁
  have htu : t / ε - u / ε < 1 := by linarith
  have hut : u / ε - t / ε < 1 := by linarith
  rw [← sub_div, div_lt_one hε] at htu hut
  rw [abs_lt]
  constructor <;> linarith

/-- Points on two parameter intervals, separated by at least `ε` on each
interval, have cardinality at most `2 + 2*L/ε`. -/
theorem two_intervals_count {S : Type*} [Fintype S] {L ε : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) (side : S → Fin 2) (time : S → ℝ)
    (ht : ∀ i, 0 ≤ time i ∧ time i ≤ L)
    (hsep : ∀ i j, i ≠ j → side i = side j → ε ≤ |time i - time j|) :
    (Fintype.card S : ℝ) ≤ 2 + 2 * L / ε := by
  let bucket : S → Fin 2 × Fin (⌊L / ε⌋₊ + 1) := fun i =>
    (side i, ⟨⌊time i / ε⌋₊, Nat.lt_succ_of_le
      (Nat.floor_mono ((div_le_div_iff_of_pos_right hε).mpr (ht i).2))⟩)
  have hinj : Function.Injective bucket := by
    intro i j hij
    have hs : side i = side j := congrArg Prod.fst hij
    have hb : ⌊time i / ε⌋₊ = ⌊time j / ε⌋₊ := congrArg (fun x => x.2.val) hij
    by_contra hne
    exact (same_bucket_close hε (ht i).1 (ht j).1 hb).not_ge (hsep i j hne hs)
  have hc := Fintype.card_le_of_injective bucket hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hcreal : (Fintype.card S : ℝ) ≤ 2 * (⌊L / ε⌋₊ + 1) := by exact_mod_cast hc
  have hf := Nat.floor_le (div_nonneg hL hε.le)
  calc
    (Fintype.card S : ℝ) ≤ 2 * (⌊L / ε⌋₊ + 1) := hcreal
    _ ≤ 2 + 2 * L / ε := by nlinarith [mul_div_assoc (2 : ℝ) L ε]

end Packing


end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Path

variable {n : ℕ} {M : Model n} {J I : Set ℝ}

lemma trace_atTime {i j : Fin n} (p : M.Path J i j) {a b : ℝ} {z : Fin n × ℝ}
    (hz : z ∈ p.trace a b) : ∃ t, p.AtTime a b z t := by
  induction p generalizing a with
  | nil i => exact ⟨|a-z.2|,hz.1,hz.2,rfl⟩
  | cons H hH hs p ih =>
    rcases hz with hz | hz
    · exact ⟨|a-z.2|,Or.inl ⟨hz.1,hz.2,rfl⟩⟩
    · obtain ⟨t,ht⟩ := ih hz
      exact ⟨|a-H|+t,Or.inr (by simpa only [add_sub_cancel_left] using ht)⟩

lemma atTime_split {i j : Fin n} (p : M.Path J i j) {a b t : ℝ} {z : Fin n × ℝ}
    (hz : p.AtTime a b z t) : ∃ (q : M.Path J i z.1) (r : M.Path J z.1 j),
      q.length a z.2 = t ∧ r.length z.2 b = p.length a b-t := by
  induction p generalizing a t with
  | nil i =>
    obtain ⟨hz,hs,ht⟩ := hz
    subst i
    exact ⟨.nil _,.nil _,ht.symm,by dsimp only [length]; linarith [abs_split hs]⟩
  | @cons i v j H hH hs p ih =>
    rcases hz with ⟨hz,hu,ht⟩ | hz
    · subst i
      refine ⟨.nil _,.cons H hH hs p,ht.symm,?_⟩
      dsimp only [length]
      linarith [abs_split hu]
    · obtain ⟨q,r,hq,hr⟩ := ih hz
      refine ⟨.cons H hH hs q,r,?_,?_⟩ <;> dsimp only [length] <;> linarith

lemma atTime_bounds {i j : Fin n} (p : M.Path J i j) {a b t : ℝ} {z : Fin n × ℝ}
    (hz : p.AtTime a b z t) : 0 ≤ t ∧ t ≤ p.length a b := by
  obtain ⟨q,r,hq,hr⟩ := p.atTime_split hz
  constructor <;> linarith [q.length_nonneg a z.2,r.length_nonneg z.2 b]

lemma vertical_offset {a b x y : ℝ} (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a b) :
    |x-y| = |(|a-x|)-(|a-y|)| := by
  rcases le_total a b with hab | hab
  · have hx' : a ≤ x := by rcases Set.mem_uIcc.mp hx with hx | hx <;> linarith
    have hy' : a ≤ y := by rcases Set.mem_uIcc.mp hy with hy | hy <;> linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hx'),abs_of_nonpos (sub_nonpos.mpr hy')]
    congr 1
    ring
  · have hx' : x ≤ a := by rcases Set.mem_uIcc.mp hx with hx | hx <;> linarith
    have hy' : y ≤ a := by rcases Set.mem_uIcc.mp hy with hy | hy <;> linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hx'),abs_of_nonneg (sub_nonneg.mpr hy')]
    have he : a-x-(a-y) = y-x := by ring
    rw [he,abs_sub_comm]

/-- Subpaths between actual arclength visits have no greater length than the
arclength difference. This is proved on the finite words, without assuming an
unconstructed continuous parametrization. -/
lemma between_atTime {i j : Fin n} (p : M.Path J i j) {a b t u : ℝ} {z w : Fin n × ℝ}
    (hz : p.AtTime a b z t) (hw : p.AtTime a b w u) :
    ∃ q : M.Path J z.1 w.1, q.length z.2 w.2 ≤ |t-u| := by
  induction p generalizing a t u with
  | nil i =>
    obtain ⟨hz,hs,ht⟩ := hz
    obtain ⟨hw,hr,hu⟩ := hw
    have he : z.1 = w.1 := hz.trans hw.symm
    let q : M.Path J z.1 w.1 := he ▸ .nil z.1
    refine ⟨q,?_⟩
    have hlen : q.length z.2 w.2 = |z.2-w.2| := by
      cases z with
      | mk zi zh =>
        cases w with
        | mk wi wh =>
          dsimp at he
          subst wi
          rfl
    rw [hlen,ht,hu,vertical_offset hs hr]
  | @cons i v j H hH hs p ih =>
    rcases hz with ⟨hz,hz',ht⟩ | hz <;> rcases hw with ⟨hw,hw',hu⟩ | hw
    · have he : z.1 = w.1 := hz.trans hw.symm
      let q : M.Path J z.1 w.1 := he ▸ .nil z.1
      refine ⟨q,?_⟩
      have hlen : q.length z.2 w.2 = |z.2-w.2| := by
        cases z with
        | mk zi zh =>
          cases w with
          | mk wi wh =>
            dsimp at he
            subst wi
            rfl
      rw [hlen,ht,hu,vertical_offset hz' hw']
    · obtain ⟨q,r,hq,_⟩ := p.atTime_split hw
      subst i
      refine ⟨.cons H hH hs q,?_⟩
      dsimp only [length]
      rw [hq]
      have he := abs_split hz'
      have htu : t ≤ u := by linarith [p.atTime_bounds hw,abs_nonneg (z.2-H)]
      rw [abs_of_nonpos (sub_nonpos.mpr htu)]
      linarith
    · obtain ⟨q,r,hq,_⟩ := p.atTime_split hz
      subst i
      let vq : M.Path J w.1 z.1 := .cons H hH hs q
      refine ⟨vq.reverse,?_⟩
      rw [length_reverse]
      change |w.2-H|+q.length H z.2 ≤ |t-u|
      rw [hq]
      have he := abs_split hw'
      have hut : u ≤ t := by linarith [p.atTime_bounds hz,abs_nonneg (w.2-H)]
      rw [abs_of_nonneg (sub_nonneg.mpr hut)]
      linarith
    · obtain ⟨q,hq⟩ := ih hz hw
      refine ⟨q,?_⟩
      have he : t-|a-H|-(u-|a-H|) = t-u := by ring
      rwa [he] at hq

lemma dist_atTime {i j root : Fin n} (p : M.Path J i j) (hJI : J ⊆ I)
    {a b t u : ℝ} (z w : M.Point I root)
    (hz : p.AtTime a b (z.column,z.height) t) (hw : p.AtTime a b (w.column,w.height) u) :
    dist z w ≤ |t-u| := by
  obtain ⟨q,hq⟩ := p.between_atTime hz hw
  exact (z.distance_le w (q.widen hJI)).trans (by simpa only [length_widen] using hq)

end PlanarL1.Columns.Model.Path

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- The source's two-path packing bound for the actual finite switching paths,
including all their vertical representatives and repeated visits. -/
theorem near_two_traces_count {S : Type*} [Fintype S] {L b ρ : ℝ}
    (hJI : J ⊆ I) (hb : 0 < b) (hL : 0 ≤ L) (hρ : ρ ≤ b/4)
    (start finish : Fin 2 → Fin n) (p : ∀ a, M.Path J (start a) (finish a))
    (A B : Fin 2 → ℝ) (hp : ∀ a, (p a).length (A a) (B a) ≤ L)
    (seed near : S → M.Point I root) (side : S → Fin 2)
    (htrace : ∀ i, ((near i).column,(near i).height) ∈
      (p (side i)).trace (A (side i)) (B (side i)))
    (hne : ∀ i j, i ≠ j → b ≤ dist (seed i) (seed j))
    (hnear : ∀ i, dist (seed i) (near i) ≤ ρ) :
    (Fintype.card S : ℝ) ≤ 2+4*L/b := by
  classical
  choose time htime using (fun i => (p (side i)).trace_atTime (htrace i))
  have ht : ∀ i, 0 ≤ time i ∧ time i ≤ L := by
    intro i
    exact ⟨((p (side i)).atTime_bounds (htime i)).1,
      ((p (side i)).atTime_bounds (htime i)).2.trans (hp (side i))⟩
  have hsep : ∀ i j, i ≠ j → side i = side j → b/2 ≤ |time i-time j| := by
    intro i j hij hs
    have hi := htime i
    rw [hs] at hi
    have hmid := (p (side j)).dist_atTime hJI (near i) (near j) hi (htime j)
    have htri := dist_triangle4 (seed i) (near i) (near j) (seed j)
    rw [dist_comm (near j) (seed j)] at htri
    linarith [hne i j hij,hnear i,hnear j]
  have hc := Packing.two_intervals_count (by positivity : 0 < b/2) hL side time ht hsep
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

/-- A connected low set lying on the far side of a chord has no vertex in
its open interval, provided neither endpoint belongs to that set. -/
lemma gap_of_chord {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {S : Set (Fin n)} (hS : (G.induce S).Preconnected) {a b c : Fin n}
    (hab : G.Adj a b) (ha : a ∉ S) (hb : b ∉ S) (hc : c ∈ S)
    (hcside : c < a ∨ b < c) : ∀ v ∈ S, v < a ∨ b < v := by
  intro v hv
  by_contra h
  obtain ⟨p⟩ := hS ⟨v,hv⟩ ⟨c,hc⟩
  let q := p.map (SimpleGraph.Embedding.induce S).toHom
  have hmem : ∀ t ∈ q.support, t ∈ S := by
    intro t ht
    obtain ⟨w,_,hw⟩ := List.mem_map.mp (by simpa only [q,SimpleGraph.Walk.support_map] using ht)
    exact hw ▸ w.property
  have hav : a ≠ v := fun he => ha (he ▸ hv)
  have hbv : b ≠ v := fun he => hb (he ▸ hv)
  have hvside : a < v ∧ v < b := by push Not at h; constructor <;> omega
  rcases chord_separation hnc hab q hvside hcside with hm | hm
  · exact ha (hmem a hm)
  · exact hb (hmem b hm)

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns

lemma not_consecutive_of_between {n : ℕ} {a b w c : Fin n}
    (hw : a < w ∧ w < b) (hc : c < a ∨ b < c) : ¬ Consecutive a b := by
  intro h
  rcases h with h | h | ⟨h,h'⟩ | ⟨h,h'⟩ <;>
    rcases hc with hc | hc <;> simp only [Fin.lt_def] at hw hc <;> omega

namespace Model.Path

variable {n : ℕ} {M : Model n} {J : Set ℝ}

lemma trace_start {i j : Fin n} (p : M.Path J i j) (a b : ℝ) :
    (i,a) ∈ p.trace a b := by
  cases p with
  | nil => exact ⟨rfl,Set.left_mem_uIcc⟩
  | cons => exact Or.inl ⟨rfl,Set.left_mem_uIcc⟩

lemma trace_on_column {i j : Fin n} (p : M.Path J i j) {a b : ℝ}
    (ha : a ∈ J) {v : Fin n} (hv : v ∈ p.word.support) :
    ∃ H ∈ J, (v,H) ∈ p.trace a b := by
  induction p generalizing a with
  | nil i =>
    have he : v = i := by simpa only [word,SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
    exact ⟨a,ha,he,Set.left_mem_uIcc⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      exact ⟨a,ha,Or.inl ⟨rfl,Set.left_mem_uIcc⟩⟩
    · obtain ⟨T,hT,ht⟩ := ih hH hv
      exact ⟨T,hT,Or.inr ht⟩

/-- Every dart of the word is an actual switch at a height visited on both
of its representatives by the original path. -/
lemma dart_on_trace {i j : Fin n} (p : M.Path J i j) (a b : ℝ)
    (e : (M.activeGraph J).Dart) (he : e ∈ p.word.darts) :
    ∃ H ∈ J, H ∈ M.heights e.fst e.snd ∧
      (e.fst,H) ∈ p.trace a b ∧ (e.snd,H) ∈ p.trace a b := by
  induction p generalizing a with
  | nil => simp only [word,SimpleGraph.Walk.darts_nil,List.not_mem_nil] at he
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact ⟨H,hH,hs,Or.inl ⟨rfl,Set.right_mem_uIcc⟩,Or.inr (p.trace_start H b)⟩
    · obtain ⟨T,hT,ht,he₁,he₂⟩ := ih H he
      exact ⟨T,hT,ht,Or.inr he₁,Or.inr he₂⟩

end Model.Path

end PlanarL1.Columns

namespace PlanarL1.ColumnOrder

lemma visits_or_skips_left {n : ℕ} {G : SimpleGraph (Fin n)} {i x y : Fin n}
    (p : G.Walk x y) (hx : i < x) (hy : y < i) :
    i ∈ p.support ∨ JumpsAcross i p := by
  induction p with
  | nil => omega
  | @cons x z y hxz p ih =>
    by_cases hz : z = i
    · left
      exact List.mem_cons_of_mem x (hz ▸ p.start_mem_support)
    by_cases hzi : i < z
    · rcases ih hzi hy with hm | ⟨e,he,hcross⟩
      · left
        simp [hm]
      · right
        exact ⟨e,by simp [he],hcross⟩
    · right
      refine ⟨⟨(x,z),hxz⟩,?_,Or.inr ⟨?_,hx⟩⟩
      · simp
      · change z < i
        omega

/-- The two extremal words cover every intermediate column by a visit or a
strictly skipping dart. No connectedness of the seed set is asserted. -/
lemma extreme_words {n : ℕ} {G : SimpleGraph (Fin n)} {l r c w : Fin n}
    (p : G.Walk c l) (q : G.Walk c r) (hl : l ≤ w) (hr : w ≤ r) :
    (w ∈ p.support ∨ JumpsAcross w p) ∨ (w ∈ q.support ∨ JumpsAcross w q) := by
  rcases lt_trichotomy w c with h | h | h
  · left
    by_cases he : l = w
    · exact Or.inl (he ▸ p.end_mem_support)
    exact visits_or_skips_left p h (lt_of_le_of_ne hl he)
  · left
    left
    exact h ▸ p.start_mem_support
  · right
    by_cases he : w = r
    · exact Or.inl (he ▸ q.end_mem_support)
    exact visits_or_skips q h (lt_of_le_of_ne hr he)

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

namespace Point

lemma dist_le_trace_length (hJI : J ⊆ I) (c e : M.Point I root) {v : Fin n}
    (p : M.Path J c.column v) {H : ℝ} (he : (e.column,e.height) ∈ p.trace c.height H) :
    dist c e ≤ p.length c.height H := by
  obtain ⟨q,r,hqr⟩ := p.trace_split he
  have hd := c.distance_le e (q.widen hJI)
  rw [Path.length_widen] at hd
  have hn := r.length_nonneg e.height H
  change dist c e ≤ q.length c.height e.height at hd
  linarith

/-- Every actual trace representative is an intrinsic point of the same
larger-band component as the start, not an assumed representative choice. -/
lemma point_on_trace (hJI : J ⊆ I) (c : M.Point I root) {v k : Fin n}
    (p : M.Path J c.column v) {H T : ℝ} (hT : T ∈ J)
    (ht : (k,T) ∈ p.trace c.height H) :
    ∃ e : M.Point I root, e.column = k ∧ e.height = T ∧ dist c e ≤ p.length c.height H := by
  obtain ⟨q,_,_⟩ := p.trace_split ht
  let e : M.Point I root := ⟨k,T,hJI hT,c.reachable.trans (q.widen hJI).word.reachable⟩
  exact ⟨e,rfl,rfl,c.dist_le_trace_length hJI e p ht⟩

end Point

end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- A visited seed column is vertically near a point of the original trace;
leaving the individual radial cell is allowed throughout. -/
lemma visited_seed_near_trace (hJI : J ⊆ I) {a : ℝ}
    (hw : ∀ s ∈ I, ∀ t ∈ I, |s-t| ≤ a) (c x : M.Point I root)
    (hc : c.height ∈ J) {v : Fin n} (p : M.Path J c.column v) {H : ℝ}
    (hx : x.column ∈ p.word.support) :
    ∃ e : M.Point I root, (e.column,e.height) ∈ p.trace c.height H ∧ dist x e ≤ a := by
  obtain ⟨T,hT,ht⟩ := p.trace_on_column hc hx
  obtain ⟨e,hecol,heheight,_⟩ := c.point_on_trace hJI p hT ht
  refine ⟨e,by rwa [hecol,heheight],?_⟩
  rw [x.dist_same_column e hecol.symm]
  exact hw x.height x.inBand e.height e.inBand

end PlanarL1.Columns.Model.Field


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Bands
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns

lemma consecutive_rotate {n : ℕ} (i j : Fin (n+1)) :
    Consecutive (finRotate (n+1) i) (finRotate (n+1) j) ↔ Consecutive i j := by
  by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n
  · subst i; subst j
    simp [Consecutive, eq_comm]
  · subst i
    rw [finRotate_last]
    simp only [Consecutive, Fin.val_zero, Fin.val_last, coe_finRotate_of_ne_last hj]
    have := j.isLt
    have hjv : j.val ≠ n := fun h => hj (Fin.ext h)
    clear hj
    try simp only [true_and, and_true]
    omega
  · subst j
    rw [finRotate_last]
    simp only [Consecutive, Fin.val_zero, Fin.val_last, coe_finRotate_of_ne_last hi]
    have := i.isLt
    have hiv : i.val ≠ n := fun h => hi (Fin.ext h)
    clear hi
    try simp only [true_and, and_true]
    omega
  · simp only [Consecutive, coe_finRotate_of_ne_last hi, coe_finRotate_of_ne_last hj]
    have := i.isLt
    have := j.isLt
    have hiv : i.val ≠ n := fun h => hi (Fin.ext h)
    clear hi
    have hjv : j.val ≠ n := fun h => hj (Fin.ext h)
    clear hj
    try simp only [true_and, and_true]
    omega


lemma consecutive_iterate {n : ℕ} (k : ℕ) (i j : Fin (n+1)) :
    Consecutive ((finRotate (n+1))^[k] i) ((finRotate (n+1))^[k] j) ↔
      Consecutive i j := by
  induction k generalizing i j with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, consecutive_rotate]

lemma consecutive_cycle {n : ℕ} (a i j : Fin (n+1)) :
    Consecutive (finCycle a i) (finCycle a j) ↔ Consecutive i j := by
  rw [finCycle_eq_finRotate_iterate]
  exact consecutive_iterate a.val i j

namespace Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J : Set ℝ} {root i j : Fin n}

lemma Point.dist_unlabel (x y : (M.relabel e hnc hcon).Point J root) :
    dist x.unlabel y.unlabel = dist x y := by
  apply le_antisymm
  · change x.unlabel.distance y.unlabel ≤ _
    have := x.paths_nonempty y
    apply le_ciInf
    intro p
    exact (x.unlabel.distance_le y.unlabel p.unlabel).trans_eq (p.length_unlabel _ _)
  · change x.distance y ≤ x.unlabel.distance y.unlabel
    have := x.unlabel.paths_nonempty y.unlabel
    apply le_ciInf
    intro p
    let q := p.label (hnc := hnc) (hcon := hcon)
    have he₁ : e.symm x.unlabel.column = x.column := e.symm_apply_apply _
    have he₂ : e.symm y.unlabel.column = y.column := e.symm_apply_apply _
    have hd := x.distance_le y (q.cast he₁ he₂)
    exact hd.trans_eq ((Path.length_cast q he₁ he₂ x.height y.height).trans
      (Path.length_label p x.height y.height))

end Model
end PlanarL1.Columns

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

namespace Path

/-- The vertical connection to a tip uses only the thin band, not the much
wider old chart band where scalar distance fields are defined. -/
lemma tip_connection {i l b : Fin n} {s H a : ℝ}
    (hsJ : s ∈ J) (hHJ : H ∈ J) (hs : H ∈ M.heights l b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a) (hi : i = l ∨ i = b) :
    ∃ p : M.Path J i l, p.length s H ≤ a := by
  rcases hi with rfl | rfl
  · exact ⟨.nil _,hw s hsJ H hHJ⟩
  · refine ⟨.cons H hHJ (by rwa [M.symm]) (.nil _),?_⟩
    simpa only [length,sub_self,abs_zero,add_zero] using hw s hsJ H hHJ

end Path

namespace Field

namespace BandDescent

variable {F : M.Field I 1} {x : M.Point I root} {ε : ℝ}

lemma column_prefix (D : F.BandDescent J x ε) (hJI : J ⊆ I)
    {v : Fin n} (hv : v ∈ D.path.word.support) :
    ∃ z : M.Point I root, z.column = v ∧ z.height ∈ J ∧
      ∃ q : M.Path J x.column z.column,
        q.length x.height z.height ≤ (1:ℝ)/50 ∧
        F.eval z ≤ F.eval x-q.length x.height z.height+ε := by
  obtain ⟨T,hT,q,r,hqr⟩ := D.path.split_at_column D.start_in D.target_in hv
  let z : M.Point I root := ⟨v,T,hJI hT,x.reachable.trans (q.widen hJI).word.reachable⟩
  have hf := F.path_bound (r.widen hJI) ⟨T,hJI hT⟩ ⟨D.target.height,D.target.inBand⟩
  rw [NNReal.coe_one,one_mul,Path.length_widen] at hf
  have hzval : F.eval z-F.eval D.target ≤ r.length T D.target.height :=
    (le_abs_self _).trans hf
  have hn := r.length_nonneg T D.target.height
  have hu := D.upper
  have hd := D.drop
  refine ⟨z,rfl,hT,q,?_,?_⟩
  all_goals dsimp only [z]; linarith

/-- Actual bounded-length path to a separating tip, even when the witness's
broad-band component was not known to be the seed's component beforehand. -/
lemma path_to_tip (D : F.BandDescent J x ε) (hJI : J ⊆ I)
    (e : M.Point I root) {b : Fin n} {a : ℝ}
    (heJ : e.height ∈ J) (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hx : e.column < x.column ∧ x.column < b)
    (hz : D.target.column < e.column ∨ b < D.target.column) :
    ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ (1:ℝ)/50+a := by
  have hadj : (M.activeGraph J).Adj e.column b := ⟨e.height,heJ,hs⟩
  have hv := ColumnOrder.chord_separation (M.active_noncrossing J) hadj D.path.word hx hz
  have hcase {v : Fin n} (hv : v ∈ D.path.word.support) (he : v = e.column ∨ v = b) :
      ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ (1:ℝ)/50+a := by
    obtain ⟨z,hz,hzJ,q,hq,_⟩ := D.column_prefix hJI hv
    obtain ⟨r,hr⟩ := Path.tip_connection hzJ heJ hs hw (hz ▸ he)
    exact ⟨q.append r,(q.length_append_le r x.height z.height e.height).trans (add_le_add hq hr)⟩
  exact hv.elim (fun h => hcase h (Or.inl rfl)) (fun h => hcase h (Or.inr rfl))

/-- The fine near-tip bound is witnessed by a path in the CURRENT broad band.
Only scalar evaluation, not path geometry, uses the old chart. -/
lemma short_path_to_tip (D : F.BandDescent J x ε) (hJI : J ⊆ I)
    (e : M.Point I root) {b : Fin n} {a j : ℝ}
    (heJ : e.height ∈ J) (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hx : e.column < x.column ∧ x.column < b)
    (hz : D.target.column < e.column ∨ b < D.target.column)
    (hlow : F.eval x-j ≤ F.eval e) :
    ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ j+ε+2*a := by
  have hadj : (M.activeGraph J).Adj e.column b := ⟨e.height,heJ,hs⟩
  have hv := ColumnOrder.chord_separation (M.active_noncrossing J) hadj D.path.word hx hz
  have hcase {v : Fin n} (hv : v ∈ D.path.word.support) (he : v = e.column ∨ v = b) :
      ∃ p : M.Path J x.column e.column, p.length x.height e.height ≤ j+ε+2*a := by
    obtain ⟨z,hz,hzJ,q,_,hdrop⟩ := D.column_prefix hJI hv
    obtain ⟨r,hr⟩ := Path.tip_connection hzJ heJ hs hw (hz ▸ he)
    have hf := F.path_bound (r.widen hJI) ⟨z.height,z.inBand⟩ ⟨e.height,e.inBand⟩
    rw [NNReal.coe_one,one_mul,Path.length_widen] at hf
    have hlo : F.eval e-F.eval z ≤ a := by
      have hn := (neg_le_abs (F.eval z-F.eval e)).trans (hf.trans hr)
      simpa only [neg_sub] using hn
    refine ⟨q.append r,?_⟩
    have hb := q.length_append_le r x.height z.height e.height
    linarith
  exact hv.elim (fun h => hcase h (Or.inl rfl)) (fun h => hcase h (Or.inr rfl))

end BandDescent
end Field
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

lemma sublevel_link_preconnected (hI : IsClosed I) (o : M.Point I root)
    (H : ℝ) (hH : H ∈ I) (t : ℝ) :
    (M.link.induce (o.sublevel H hH t)).Preconnected := by
  intro x y
  obtain ⟨p⟩ := o.sublevel_preconnected hI H hH t x y
  let f : (M.activeGraph I).induce (o.sublevel H hH t) →g
      M.link.induce (o.sublevel H hH t) :=
    { toFun := id, map_rel' := fun {_ _} h => M.active_subgraph I h }
  exact ⟨p.map f⟩

/-- The actual target of each almost-descending broad-band path is a member
of the old-distance low sublevel. Width is used only for the broad band J. -/
lemma descent_target_low (o w x : M.Point I root) (hJI : J ⊆ I)
    {ε a B δ : ℝ} (D : o.radialField.BandDescent J x ε) {H : ℝ} (hHJ : H ∈ J)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hclose : dist o x ≤ dist o w+B)
    (hsmall : B+ε+a < (1:ℝ)/100000-δ) :
    D.target.column ∈ o.sublevel H (hJI hHJ) (dist o w-δ) := by
  rw [o.mem_sublevel_iff D.target H (hJI hHJ)]
  have hd := D.drop
  rw [radialField_eval,radialField_eval] at hd
  have hv := D.target.dist_withHeight H (hJI hHJ)
  have hv' : dist D.target (D.target.withHeight H (hJI hHJ)) ≤ a := by
    rw [hv]
    exact hw _ D.target_in _ hHJ
  have ht := dist_triangle o D.target (D.target.withHeight H (hJI hHJ))
  have hl := D.lower
  linarith

/-- The same old-distance sublevel misses EVERY visited column of a short
center path. This establishes the manuscript's avoidance condition rather
than postulating it of a chosen set. -/
lemma short_path_avoids_low (o w c : M.Point I root) (hJI : J ⊆ I)
    {a A δ : ℝ} {H : ℝ} (hHJ : H ∈ J)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hcJ : c.height ∈ J) (hcw : dist c w ≤ A) (hsmall : 2*A+a < δ)
    {v : Fin n} (p : M.Path J c.column v) {T : ℝ}
    (hp : p.length c.height T ≤ A) :
    ∀ k ∈ p.word.support, k ∉ o.sublevel H (hJI hHJ) (dist o w-δ) := by
  intro k hk hlow
  obtain ⟨U,hU,hu⟩ := p.trace_on_column hcJ hk
  obtain ⟨z,hzk,hzU,hcz⟩ := c.point_on_trace hJI p hU hu
  have hl : dist o (z.withHeight H (hJI hHJ)) ≤ dist o w-δ := by
    exact (o.mem_sublevel_iff z H (hJI hHJ) _).mp (hzk.symm ▸ hlow)
  have hz : dist z (z.withHeight H (hJI hHJ)) ≤ a := by
    rw [z.dist_withHeight,hzU]
    exact hw _ hU _ hHJ
  have hzw : dist w z ≤ 2*A := by
    have ht := dist_triangle w c z
    rw [dist_comm w c] at ht
    linarith
  have ht₁ := dist_triangle o (z.withHeight H (hJI hHJ)) z
  have ht₂ := dist_triangle o z w
  rw [dist_comm (z.withHeight H (hJI hHJ)) z] at ht₁
  rw [dist_comm z w] at ht₂
  linarith

end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J K : Set ℝ} {root : Fin n}

lemma BandDescent.partner_outside_tip {F : M.Field I 1} {ε a A : ℝ}
    (x y e : M.Point I root) (D : F.BandDescent K y ε) (hKI : K ⊆ I)
    {b : Fin n} (heK : e.height ∈ K) (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hz : D.target.column < e.column ∨ b < D.target.column)
    (hxy : 1 ≤ dist x y) (hxe : dist x e ≤ A) (hsmall : (1:ℝ)/50+a+A < 1) :
    y.column < e.column ∨ b < y.column := by
  by_contra h
  have hle : e.column ≤ y.column ∧ y.column ≤ b := by push Not at h; exact h
  have hd : ∃ p : M.Path K y.column e.column,
      p.length y.height e.height ≤ (1:ℝ)/50+a := by
    by_cases hy : y.column = e.column
    · obtain ⟨p,hp⟩ := Path.tip_connection D.start_in heK hs hw (Or.inl hy)
      exact ⟨p,by linarith⟩
    by_cases hy' : y.column = b
    · obtain ⟨p,hp⟩ := Path.tip_connection D.start_in heK hs hw (Or.inr hy')
      exact ⟨p,by linarith⟩
    exact D.path_to_tip hKI e heK hs hw
      ⟨lt_of_le_of_ne hle.1 (Ne.symm hy),lt_of_le_of_ne hle.2 hy'⟩ hz
  obtain ⟨p,hp⟩ := hd
  have hd := y.distance_le e (p.widen hKI)
  rw [Path.length_widen] at hd
  change dist y e ≤ _ at hd
  have ht := dist_triangle x e y
  rw [dist_comm e y] at ht
  linarith

/-- The skipped-seed estimate keeps the old chart, broad current band and
narrow center-path band distinct. Its conclusion contains an ACTUAL broad-band
path to the trace, not just a distance in the larger old chart. -/
lemma skipped_seed_broad_path (F : M.Field I 1)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJK : J ⊆ K) (hKI : K ⊆ I) {a A j ε : ℝ}
    (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (c x y : M.Point I root) (Dx : F.BandDescent K x ε) (Dy : F.BandDescent K y ε)
    (hxS : Dx.target.column ∈ S) (hyS : Dy.target.column ∈ S)
    (hxy : 1 ≤ dist x y) (hcx : dist c x ≤ A) (hA : 2*A ≤ 1)
    (hsmall : (1:ℝ)/50+a+2*A < 1) (hretain : F.NoLowTip x y J j)
    {v : Fin n} (p : M.Path J c.column v) {H : ℝ} (hp : p.length c.height H ≤ A)
    (havoid : ∀ k ∈ p.word.support, k ∉ S) (hskip : ColumnOrder.JumpsAcross x.column p.word) :
    ∃ e : M.Point I root, e.height ∈ J ∧ (e.column,e.height) ∈ p.trace c.height H ∧
      ∃ q : M.Path K x.column e.column, q.length x.height e.height ≤ j+ε+2*a := by
  obtain ⟨d,hd,hcross⟩ := hskip
  obtain ⟨T,hT,hs,ht₁,ht₂⟩ := p.dart_on_trace c.height H d hd
  have hcase {l r : Fin n} (hlr : l < x.column ∧ x.column < r)
      (hs : T ∈ M.heights l r) (htl : (l,T) ∈ p.trace c.height H)
      (htr : (r,T) ∈ p.trace c.height H) :
      ∃ e : M.Point I root, e.height ∈ J ∧ (e.column,e.height) ∈ p.trace c.height H ∧
        ∃ q : M.Path K x.column e.column, q.length x.height e.height ≤ j+ε+2*a := by
    have hl : l ∉ S := havoid l (p.trace_column htl)
    have hr : r ∉ S := havoid r (p.trace_column htr)
    have hcl : cut < l := lt_of_le_of_ne (hmin l) (fun h => hl (h ▸ hcut))
    have hgap := ColumnOrder.gap_of_chord M.noncrossing hS
      (M.permitted l r T hs) hl hr hcut (Or.inl hcl)
    obtain ⟨e,hecol,heheight,helen⟩ := c.point_on_trace (hJK.trans hKI) p hT htl
    have hetrace : (e.column,e.height) ∈ p.trace c.height H := by rwa [hecol,heheight]
    have hxe : dist x e ≤ 2*A := by
      have ht := dist_triangle x c e
      rw [dist_comm x c] at ht
      linarith
    have hes : e.height ∈ M.heights e.column r := by rwa [hecol,heheight]
    have heJ : e.height ∈ J := heheight ▸ hT
    have hyp : y.column < e.column ∨ r < y.column := Dy.partner_outside_tip x y e hKI
      (hJK heJ) hes hw (by simpa only [hecol] using hgap _ hyS) hxy hxe hsmall
    have hnc : ¬ Consecutive e.column r := by
      rw [hecol]
      exact not_consecutive_of_between hlr (Or.inl hcl)
    have hlow := (hretain e r heJ hes hnc
      (Or.inl ⟨by simpa only [hecol] using hlr.1,hlr.2,hyp⟩) (Or.inl (hxe.trans hA))).1
    refine ⟨e,heJ,hetrace,Dx.short_path_to_tip hKI e (hJK heJ) hes hw ?_ ?_ hlow⟩
    · simpa only [hecol] using hlr
    · simpa only [hecol] using hgap _ hxS
  rcases hcross with hc | hc
  · exact hcase hc hs ht₁ ht₂
  · exact hcase hc (by rwa [M.symm]) ht₂ ht₁

theorem restricted_broad_packing {W : Type*} [Fintype W]
    (F : M.Field I 1)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJK : J ⊆ K) (hKI : K ⊆ I) {a A j ε b : ℝ} (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (c : M.Point K root) (hc : c.height ∈ J) (hcS : c.column ∉ S)
    (seed : W → M.Point K root) (partner : W → M.Point I root)
    (Dx : ∀ w, F.BandDescent K ((seed w).widen hKI) ε) (Dy : ∀ w, F.BandDescent K (partner w) ε)
    (hxS : ∀ w, (Dx w).target.column ∈ S) (hyS : ∀ w, (Dy w).target.column ∈ S)
    (hxy : ∀ w, 1 ≤ dist ((seed w).widen hKI) (partner w))
    (hretain : ∀ w, F.NoLowTip ((seed w).widen hKI) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (havoid : ∀ w k, k ∈ (cp w).word.support → k ∉ S)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card W : ℝ) ≤ 2+4*A/b := by
  classical
  let endpoint : Option W → M.Point K root := Option.elim' c seed
  let path : ∀ w : Option W, M.Path J c.column (endpoint w).column := fun w =>
    Option.rec (.nil c.column) cp w
  have hlen : ∀ w, (path w).length c.height (endpoint w).height ≤ A := by
    intro w
    cases w with
    | none => simpa only [path,endpoint,Option.elim',Path.length,sub_self,abs_zero] using hA₀
    | some w => exact hp w
  have hav : ∀ w k, k ∈ (path w).word.support → k ∉ S := by
    intro w k hk
    cases w with
    | none =>
      have he : k = c.column := by
        change k ∈ [c.column] at hk
        exact List.mem_singleton.mp hk
      exact he ▸ hcS
    | some w => exact havoid w k hk
  obtain ⟨l,_,hl⟩ := Finset.exists_min_image (Finset.univ : Finset (Option W))
    (fun w => (endpoint w).column) ⟨none,Finset.mem_univ _⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Option W))
    (fun w => (endpoint w).column) ⟨none,Finset.mem_univ _⟩
  let select : Fin 2 → Option W := ![l,r]
  let paths (s : Fin 2) := path (select s)
  have hone (w : W) (v : Option W)
      (hv : (seed w).column ∈ (path v).word.support ∨
        ColumnOrder.JumpsAcross (seed w).column (path v).word) :
      ∃ e : M.Point K root, (e.column,e.height) ∈ (path v).trace c.height (endpoint v).height ∧
        dist (seed w) e ≤ j+ε+2*a := by
    rcases hv with hv | hv
    · obtain ⟨e,he,hnear⟩ := visited_seed_near_trace hJK hw c (seed w) hc (path v) hv
      exact ⟨e,he,hnear.trans hvisit⟩
    · have hcs : dist c (seed w) ≤ A := by
        have hd := c.distance_le (seed w) ((cp w).widen hJK)
        rw [Path.length_widen] at hd
        exact hd.trans (hp w)
      obtain ⟨e,heJ,he,q,hq⟩ := F.skipped_seed_broad_path hS hcut hmin hJK hKI hw
        (c.widen hKI) ((seed w).widen hKI) (partner w) (Dx w) (Dy w) (hxS w) (hyS w)
        (hxy w) ((c.dist_widen_le (seed w) hKI).trans hcs) hA hsmall (hretain w)
        (path v) (hlen v) (hav v) hv
      let eb : M.Point K root := ⟨e.column,e.height,hJK heJ,
        (seed w).reachable.trans q.word.reachable⟩
      exact ⟨eb,he,((seed w).distance_le eb q).trans hq⟩
  have hprox : ∀ w : W, ∃ (s : Fin 2) (e : M.Point K root),
      (e.column,e.height) ∈ (paths s).trace c.height (endpoint (select s)).height ∧
        dist (seed w) e ≤ j+ε+2*a := by
    intro w
    have h := ColumnOrder.extreme_words (path l).word (path r).word
      (hl (some w) (Finset.mem_univ _)) (hr (some w) (Finset.mem_univ _))
    rcases h with h | h
    · obtain ⟨e,he,hnear⟩ := hone w l h
      exact ⟨0,e,by simpa only [paths,select,Matrix.cons_val_zero] using he,hnear⟩
    · obtain ⟨e,he,hnear⟩ := hone w r h
      exact ⟨1,e,by simpa only [paths,select,Matrix.cons_val_one,Matrix.cons_val_zero] using he,hnear⟩
  choose side near htrace hnear using hprox
  exact near_two_traces_count hJK hb hA₀ hpad (fun _ => c.column)
    (fun s => (endpoint (select s)).column) paths (fun _ => c.height)
    (fun s => (endpoint (select s)).height) (fun s => hlen (select s))
    seed near side htrace hsep hnear


end PlanarL1.Columns.Model.Field


namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J I : Set ℝ} {root : Fin n}

lemma Point.dist_label (x y : M.Point J (e root)) :
    dist (x.label (hnc := hnc) (hcon := hcon)) y.label = dist x y := by
  rw [← Point.dist_unlabel,Point.unlabel_label,Point.unlabel_label]

end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field

lemma circularTip_rotate {n : ℕ} (a b x y : Fin (n+1)) :
    CircularTipSeparates (finRotate (n+1) a) (finRotate (n+1) b)
      (finRotate (n+1) x) (finRotate (n+1) y) ↔ CircularTipSeparates a b x y := by
  have hval (i : Fin (n+1)) : (finRotate (n+1) i).val =
      if i.val = n then 0 else i.val+1 := by
    split_ifs with hi
    · have he : i = Fin.last n := Fin.ext hi
      rw [he,finRotate_last]
      rfl
    · exact coe_finRotate_of_ne_last (fun h => hi (congrArg Fin.val h))
  unfold CircularTipSeparates TipSeparates
  simp only [Fin.lt_def,hval]
  split_ifs <;> omega

lemma circularTip_iterate {n : ℕ} (k : ℕ) (a b x y : Fin (n+1)) :
    CircularTipSeparates ((finRotate (n+1))^[k] a) ((finRotate (n+1))^[k] b)
      ((finRotate (n+1))^[k] x) ((finRotate (n+1))^[k] y) ↔ CircularTipSeparates a b x y := by
  induction k generalizing a b x y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,
      Function.iterate_succ_apply,Function.iterate_succ_apply,ih,circularTip_rotate]

lemma circularTip_cycle {n : ℕ} (c a b x y : Fin (n+1)) :
    CircularTipSeparates (finCycle c a) (finCycle c b) (finCycle c x) (finCycle c y) ↔
      CircularTipSeparates a b x y := by
  rw [finCycle_eq_finRotate_iterate]
  exact circularTip_iterate c.val a b x y

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J I : Set ℝ} {root : Fin n}

lemma Path.support_word_label {i j : Fin n} (p : M.Path J i j) :
    (p.label (hnc := hnc) (hcon := hcon)).word.support = p.word.support.map e.symm := by
  induction p with
  | nil => rfl
  | cons H hH hs p ih =>
    change _ :: p.label.word.support = _ :: p.word.support.map e.symm
    rw [ih]

namespace Field

lemma NoLowCircular.toNoLowTip {F : M.Field I 1} {x y : M.Point I root} {j : ℝ}
    (h : F.NoLowCircular x y J j) : F.NoLowTip x y J j := by
  intro v b hJ hs hc ht hd
  exact h v b hJ hs hc (Or.inl ht) hd

lemma NoLowCircular.label {F : M.Field I 1} {x y : M.Point I (e root)} {j : ℝ}
    (h : F.NoLowCircular x y J j)
    (hcirc : ∀ a b v w, CircularTipSeparates (e a) (e b) (e v) (e w) ↔
      CircularTipSeparates a b v w) :
    (F.label (hnc := hnc) (hcon := hcon)).NoLowCircular x.label y.label J j := by
  intro v b hvJ hvs hvc hvsep hvdist
  have h₁ : dist x v.unlabel = dist x.label v := by
    simpa only [Point.unlabel_label] using
      (Point.dist_unlabel (x.label (hnc := hnc) (hcon := hcon)) v)
  have h₂ : dist y v.unlabel = dist y.label v := by
    simpa only [Point.unlabel_label] using
      (Point.dist_unlabel (y.label (hnc := hnc) (hcon := hcon)) v)
  have hsep := (hcirc v.column b x.label.column y.label.column).mpr hvsep
  simp only [Point.label,e.apply_symm_apply] at hsep
  have hc : ¬Consecutive v.unlabel.column (e b) := fun hh => hvc ((hcon _ _).mp hh)
  have hh := h v.unlabel (e b) hvJ hvs hc hsep (by simpa only [h₁,h₂] using hvdist)
  simpa only [Field.eval_label,Field.eval_unlabel,Point.unlabel_label] using hh

end Field
end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

lemma preconnected_comap {n : ℕ} {G : SimpleGraph (Fin n)} {S : Set (Fin n)}
    (hS : (G.induce S).Preconnected) (e : Equiv.Perm (Fin n)) :
    ((G.comap e).induce (e ⁻¹' S)).Preconnected := by
  let f : G.induce S →g (G.comap e).induce (e ⁻¹' S) :=
    { toFun := fun v => ⟨e.symm v.val,by simpa only [Set.mem_preimage,e.apply_symm_apply] using v.property⟩
      map_rel' := fun {_ _} h => by
        change G.Adj _ _ at h
        change G.Adj (e (e.symm _)) (e (e.symm _))
        simpa only [e.apply_symm_apply, Function.Embedding.subtype_apply] using h }
  intro x y
  obtain ⟨p⟩ := hS ⟨e x.val,x.property⟩ ⟨e y.val,y.property⟩
  have hx : f ⟨e x.val,x.property⟩ = x := by
    apply Subtype.ext
    exact e.symm_apply_apply _
  have hy : f ⟨e y.val,y.property⟩ = y := by
    apply Subtype.ext
    exact e.symm_apply_apply _
  exact ⟨(p.map f).copy hx hy⟩

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model.Field

/-- Restricted geometric packing with NO privileged linear cut. The proof
rotates the actual model, fields, paths and all distance data at a low column.
The result measures separation in the BROAD current intrinsic component. -/
theorem circular_broad_packing {n : ℕ} {M : Model (n+1)} {I J K : Set ℝ} {root : Fin (n+1)}
    {W : Type*} [Fintype W] (F : M.Field I 1)
    {S : Set (Fin (n+1))} (hS : (M.link.induce S).Preconnected)
    {cut : Fin (n+1)} (hcut : cut ∈ S)
    (hJK : J ⊆ K) (hKI : K ⊆ I) {a A j ε b : ℝ}
    (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (c : M.Point K root) (hc : c.height ∈ J) (hcS : c.column ∉ S)
    (seed : W → M.Point K root) (partner : W → M.Point I root)
    (Dx : ∀ w, F.BandDescent K ((seed w).widen hKI) ε)
    (Dy : ∀ w, F.BandDescent K (partner w) ε)
    (hxS : ∀ w, (Dx w).target.column ∈ S) (hyS : ∀ w, (Dy w).target.column ∈ S)
    (hxy : ∀ w, 1 ≤ dist ((seed w).widen hKI) (partner w))
    (hretain : ∀ w, F.NoLowCircular ((seed w).widen hKI) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (havoid : ∀ w k, k ∈ (cp w).word.support → k ∉ S)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card W : ℝ) ≤ 2+4*A/b := by
  let e := finCycle cut
  obtain ⟨r,rfl⟩ := e.surjective root
  let hnc := ColumnOrder.noncrossing_comap_cycle M.noncrossing cut
  let hcon := consecutive_cycle cut
  let N := M.relabel e hnc hcon
  let F' : N.Field I 1 := F.label
  let c' : N.Point K r := c.label
  let seed' (w : W) : N.Point K r := (seed w).label
  let partner' (w : W) : N.Point I r := (partner w).label
  let dy' (w : W) : F'.BandDescent K (partner' w) ε := (Dy w).label
  -- Use the explicit transported data, so target membership is not lost
  -- behind a propositional existence witness.
  let dx' (w : W) : F'.BandDescent K ((seed' w).widen hKI) ε := (Dx w).label
  have hzero : e 0 = cut := by simp only [e,finCycle_apply,zero_add]
  refine F'.restricted_broad_packing (S := e ⁻¹' S)
    (ColumnOrder.preconnected_comap hS e) (cut := 0) (by simpa only [Set.mem_preimage,hzero] using hcut)
    (fun v => Fin.zero_le v) hJK hKI hw hA₀ hA hsmall hb hpad hvisit c' hc
    (by simpa only [c',Point.label,Set.mem_preimage,e.apply_symm_apply] using hcS)
    seed' partner' dx' dy' ?_ ?_ ?_ ?_ (fun w => (cp w).label) ?_ ?_ ?_
  · intro w
    simpa only [dx',Field.BandDescent.label,Point.label,Set.mem_preimage,e.apply_symm_apply] using hxS w
  · intro w
    simpa only [dy',Field.BandDescent.label,Point.label,Set.mem_preimage,e.apply_symm_apply] using hyS w
  · intro w
    exact (hxy w).trans_eq
      (Point.dist_label (hnc := hnc) (hcon := hcon) ((seed w).widen hKI) (partner w)).symm
  · intro w
    exact ((hretain w).label (hnc := hnc) (hcon := hcon) (circularTip_cycle cut)).toNoLowTip
  · intro w
    simpa only [c',seed',Point.label,Path.length_label] using hp w
  · intro w k hk
    change k ∈ ((cp w).label (hnc := hnc) (hcon := hcon)).word.support at hk
    rw [Path.support_word_label] at hk
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hk
    change e (e.symm v) ∉ S
    simpa only [e.apply_symm_apply] using havoid w v hv
  · intro w v hwv
    exact (hsep w v hwv).trans_eq
      (Point.dist_label (hnc := hnc) (hcon := hcon) (seed w) (seed v)).symm

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Field

/-- The low-set and circular-gap hypotheses of geometric packing are DERIVED
from the actual old chart distance and actual witness descents. This is the
band-faithful application of `pack:bound` to surviving seeds. -/
theorem radial_surviving_packing {n : ℕ} {M : Model (n+1)} {I J K : Set ℝ}
    {root : Fin (n+1)} {W : Type*} [Fintype W]
    (hI : IsClosed I) (hJK : J ⊆ K) (hKI : K ⊆ I)
    {a A E δ j ε b : ℝ} (hw : ∀ s ∈ K, ∀ t ∈ K, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hE : 0 ≤ E)
    (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hlow : 2*A+E+ε+a < (1:ℝ)/100000-δ) (hhigh : 2*A+a < δ)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (o : M.Point I root) (c : M.Point K root) (hc : c.height ∈ J)
    (seed : W → M.Point K root) (partner : W → M.Point I root)
    (hseed : ∀ w, (seed w).height ∈ J)
    (Dx : ∀ w, o.radialField.BandDescent K ((seed w).widen hKI) ε)
    (Dy : ∀ w, o.radialField.BandDescent K (partner w) ε)
    (hxy : ∀ w, 1 ≤ dist ((seed w).widen hKI) (partner w))
    (hfield : ∀ w, |dist o (partner w)-dist o ((seed w).widen hKI)| ≤ E)
    (hretain : ∀ w, o.radialField.NoLowCircular ((seed w).widen hKI) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card W : ℝ) ≤ 2+4*A/b := by
  classical
  by_cases hn : Nonempty W
  · obtain ⟨w₀⟩ := hn
    let star := (seed w₀).widen hKI
    let H := (seed w₀).height
    have hHJ : H ∈ J := hseed w₀
    have hHI : H ∈ I := hKI (hJK hHJ)
    let S := o.sublevel H hHI (dist o star-δ)
    have hcs (w : W) : dist (c.widen hKI) ((seed w).widen hKI) ≤ A := by
      apply (c.dist_widen_le (seed w) hKI).trans
      exact (c.distance_le (seed w) ((cp w).widen hJK)).trans
        (by simpa only [Path.length_widen] using hp w)
    have hclose (w : W) : dist o ((seed w).widen hKI) ≤ dist o star+2*A+E := by
      have h₁ := dist_triangle o star (c.widen hKI)
      have h₂ := dist_triangle o (c.widen hKI) ((seed w).widen hKI)
      have hc₀ := hcs w₀
      change dist (c.widen hKI) star ≤ A at hc₀
      rw [dist_comm (c.widen hKI) star] at hc₀
      linarith [hcs w]
    have hclosePartner (w : W) : dist o (partner w) ≤ dist o star+(2*A+E) := by
      have h₁ := dist_triangle o star (c.widen hKI)
      have h₂ := dist_triangle o (c.widen hKI) ((seed w).widen hKI)
      have hc₀ := hcs w₀
      change dist (c.widen hKI) star ≤ A at hc₀
      rw [dist_comm (c.widen hKI) star] at hc₀
      have hf := (abs_le.mp (hfield w)).2
      linarith [hcs w]
    have hxS (w : W) : (Dx w).target.column ∈ S := by
      exact o.descent_target_low star ((seed w).widen hKI) hKI (Dx w) (hJK hHJ) hw
        (by linarith [hclose w]) hlow
    have hyS (w : W) : (Dy w).target.column ∈ S := by
      exact o.descent_target_low star (partner w) hKI (Dy w) (hJK hHJ) hw (hclosePartner w) hlow
    have hav (w : W) : ∀ k ∈ (cp w).word.support, k ∉ S := by
      exact o.short_path_avoids_low star (c.widen hKI) (hJK.trans hKI) hHJ
        (fun s hs t ht => hw s (hJK hs) t (hJK ht)) hc (hcs w₀) hhigh (cp w) (hp w)
    exact o.radialField.circular_broad_packing (o.sublevel_link_preconnected hI H hHI _)
      (hxS w₀) hJK hKI hw hA₀ hA hsmall hb hpad hvisit c hc
      (hav w₀ c.column (cp w₀).word.start_mem_support)
      seed partner Dx Dy hxS hyS hxy hretain cp hp hav hsep
  · have : IsEmpty W := not_nonempty_iff.mp hn
    simp only [Fintype.card_of_isEmpty,Nat.cast_zero]
    positivity

end PlanarL1.Columns.Model.Field



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Clipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Clipping

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

/-- The source main raise-or-descend alternative, including the empty frontier.
The radius interval is obtained from actual radial padding and weak diameter
when this lemma is applied to the literal full-column frontier. -/
lemma raise_or_descending_endpoint {S : Set X} {s F H : X → ℝ}
    (hS : IsCompact S) (hs : ContinuousOn s S) (w : X) (cap ζ E ε : ℝ)
    (happrox : envelope S s cap (1-ζ) w-5*E ≤ F w)
    (hshield : s w+2*E < H w) (hcap : s w+7*E < cap)
    (hrad : ∀ z ∈ S, (0.00001:ℝ) ≤ dist w z ∧ dist w z ≤ 0.02)
    (hzeta : 0 ≤ ζ) (herr : ζ*0.02+7*E ≤ ε) :
    s w+2*E < clip s F H w ∨
      ∃ z ∈ S, (0.00001:ℝ) ≤ dist w z ∧ dist w z ≤ 0.02 ∧
        s z ≤ s w-dist w z+ε := by
  by_cases hraise : s w+2*E < clip s F H w
  · exact Or.inl hraise
  · right
    have hc : min (F w) (H w) ≤ s w+2*E :=
      (le_max_right _ _).trans (not_lt.mp hraise)
    have hFw : F w ≤ s w+2*E := (min_le_iff.mp hc).resolve_right (not_le.mpr hshield)
    have he : envelope S s cap (1-ζ) w ≤ s w+7*E := by linarith
    obtain h | ⟨z,hz,h⟩ := envelope_cases hS hs cap (1-ζ) w
    · rw [h] at he
      exact (not_le.mpr hcap he).elim
    · refine ⟨z,hz,(hrad z hz).1,(hrad z hz).2,?_⟩
      rw [h] at he
      have hm := mul_le_mul_of_nonneg_left (hrad z hz).2 hzeta
      nlinarith

end PlanarL1.Clipping


end

section

namespace PlanarL1.Clipping
open scoped NNReal

lemma heightShield_plateau {lo a s α H : ℝ} (ha : 0 < a)
    (hl : lo+9*a/100 ≤ H) (hr : H ≤ lo+a-9*a/100) :
    heightShield lo a s α H = s+2+α := by
  have hb : 0 < 9*a/100 := by positivity
  have hm : 9*a/100 ≤ min (H-lo) (lo+a-H) := le_min (by linarith) (by linarith)
  have hq : 1 ≤ max 0 (min (H-lo) (lo+a-H)) / (9*a/100) := by
    apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using hm.trans (le_max_right _ _)
  rw [heightShield,min_eq_left hq]
  ring

end PlanarL1.Clipping


end

section

namespace PlanarL1.Clipping
variable {X : Type*}

lemma orderedBranch_seed {pc radius α p : ℝ} {L : X → ℝ} {x : X} (hr : 0 < radius)
    (hα : 0 ≤ α) (hL : |L x-pc| ≤ (10/1000000:ℝ)*radius)
    (hp : |p-pc| ≤ (60/1000000:ℝ)*radius) :
    p+radius/25 < orderedBranch pc radius α L x := by
  have hl := (abs_le.mp hL).1
  have hu := (abs_le.mp hp).2
  dsimp only [orderedBranch]
  linarith

end PlanarL1.Clipping




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Increments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Increment
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

lemma positive_plateau {a r t : ℝ} (ha : 0 < a) (hl : 2*a ≤ t) (hu : t ≤ 8*r) :
    positivePart a r t = t := by
  by_cases he : t = 2*a
  · rw [positivePart,splice,ite_eq_left (by linarith),low,quadratic,clamp_right hl,he]
    field_simp
    ring
  · rw [positivePart,splice,ite_eq_right (by intro h; exact he (le_antisymm h hl)),high,splice,ite_eq_left hu]
    rfl

lemma scalar_plateau {a r t : ℝ} (ha : 0 < a) (hl : 2*a ≤ |t|) (hu : |t| ≤ 8*r) :
    scalar a r t = t := by
  unfold scalar splice
  split_ifs with ht
  · dsimp only
    rw [abs_of_nonpos ht] at hl hu
    rw [positive_plateau ha hl hu,neg_neg]
  · rw [abs_of_pos (by linarith)] at hl hu
    exact positive_plateau ha hl hu

section Taper
variable {X : Type*} [PseudoMetricSpace X]
open Metric

lemma taper_one {S : Set X} {r : ℝ} {x : X} (hr : 0 < r)
    (hx : S.Nonempty → r ≤ infDist x S) : taper S r x = 1 := by
  unfold taper
  split_ifs with h
  · apply min_eq_left
    exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hx h)
  · rfl

end Taper

lemma opposite_sign_gain (p q : ℝ) : |q| ≤ |p+q| ∨ |q| ≤ |p-q| := by
  by_contra h
  push Not at h
  have ht := abs_sub_le (p+q) 0 (p-q)
  have he : |(p+q)-(p-q)| = 2*|q| := by
    rw [show (p+q)-(p-q) = 2*q by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [he,sub_zero,zero_sub,abs_neg] at ht
  linarith


end PlanarL1.Increment



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.FiniteRandom

attribute [local instance] Classical.propDecidable

lemma mem_event {Ω : Type*} [Fintype Ω] (P : Ω → Prop) (w : Ω) : w ∈ event P ↔ P w := by
  classical
  simp [event]

lemma prob_eq_sum {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    prob P = (∑ w, if P w then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  simp [prob, event, Finset.sum_boole]

lemma prob_mono {Ω : Type*} [Fintype Ω] {P Q : Ω → Prop} (h : ∀ w, P w → Q w) :
    prob P ≤ prob Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show event P ⊆ event Q from
    fun w hw => (mem_event Q w).mpr (h w ((mem_event P w).mp hw)))

lemma prob_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (e : Ω ≃ Λ) (P : Λ → Prop) :
    prob (fun w => P (e w)) = prob P := by
  classical
  rw [prob_eq_sum, prob_eq_sum, Fintype.card_congr e]
  exact congrArg (fun z : ℝ => z / Fintype.card Λ)
    (e.sum_comp (fun z : Λ => if P z then (1 : ℝ) else 0))

lemma prob_prod {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (P : Ω × Λ → Prop) :
    prob P = (∑ w : Ω, prob (fun z : Λ => P (w,z))) / Fintype.card Ω := by
  classical
  simp only [prob_eq_sum, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div]
  ring

lemma prob_prod_bound {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (P : Ω × Λ → Prop) {b : ℝ} (h : ∀ w, prob (fun z : Λ => P (w,z)) ≤ b) :
    prob P ≤ b := by
  rw [prob_prod]
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    ∑ w : Ω, prob (fun z : Λ => P (w,z)) ≤ ∑ _w : Ω, b := Finset.sum_le_sum (fun w _ => h w)
    _ = b * Fintype.card Ω := by simp [mul_comm]

lemma prob_union_bound {Ω ι : Type*} [Fintype Ω] (S : Finset ι) (P : ι → Ω → Prop) :
    prob (fun w => ∃ i ∈ S, P i w) ≤ ∑ i ∈ S, prob (P i) := by
  classical
  unfold prob
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he : event (fun w => ∃ i ∈ S, P i w) =
      S.biUnion (fun i => event (P i)) := by
    ext w
    simp [mem_event]
  rw [he]
  exact_mod_cast (Finset.card_biUnion_le :
    (S.biUnion (fun i => event (P i))).card ≤
      ∑ i ∈ S, (event (P i)).card)

/-- An interval of radius t meets at most 2t/step+1 equally spaced points.
This argument is exact and includes both endpoints of the grid. -/
lemma grid_count (m : ℕ) {step t : ℝ} (hstep : 0 < step) (ht : 0 ≤ t) (c : ℝ) :
    ((event (fun i : Fin (m + 1) => |c + step * i.val| ≤ t)).card : ℝ) * step ≤
      2 * t + step := by
  classical
  let A := event (fun i : Fin (m + 1) => |c + step * i.val| ≤ t)
  by_cases hA : A.Nonempty
  · let a := A.min' hA
    let b := A.max' hA
    have ha : a ∈ A := A.min'_mem hA
    have hb : b ∈ A := A.max'_mem hA
    have hab : a.val ≤ b.val := A.min'_le b hb
    have hsub : A.image Fin.val ⊆ Finset.Icc a.val b.val := by
      rintro i hi
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_Icc.mpr ⟨A.min'_le z hz, A.le_max' z hz⟩
    have hcard : A.card ≤ b.val + 1 - a.val := by
      have hc := Finset.card_le_card hsub
      simpa only [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] using hc
    have hcard' : (A.card : ℝ) ≤ (b.val : ℝ) - a.val + 1 := by
      have he : b.val + 1 - a.val + a.val = b.val + 1 := Nat.sub_add_cancel (by omega)
      have hh : (b.val + 1 - a.val : ℕ) + a.val ≤ b.val + 1 := he.le
      have hi : A.card + a.val ≤ b.val + 1 := by omega
      have hir : (A.card : ℝ) + a.val ≤ (b.val : ℝ) + 1 := by exact_mod_cast hi
      linarith
    have ham : |c + step * a.val| ≤ t := (mem_event _ a).mp ha
    have hbm : |c + step * b.val| ≤ t := (mem_event _ b).mp hb
    have ha' := (abs_le.mp ham).1
    have hb' := (abs_le.mp hbm).2
    have hm := mul_le_mul_of_nonneg_right hcard' hstep.le
    change (A.card : ℝ) * step ≤ 2 * t + step
    nlinarith
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change (A.card : ℝ) * step ≤ 2 * t + step
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith

/-- Uniform endpoint grid estimate in the normalization used by the paper. -/
lemma grid_probability (m : ℕ) (hm : 0 < m) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) (c : ℝ) :
    prob (fun i : Fin (m + 1) => |c + q / m * i.val| ≤ t) ≤ (2 * t + q / m) / q := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < q / m := div_pos hq hm'
  have hcount := grid_count m hs ht c
  have hc : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  unfold prob
  rw [Fintype.card_fin]
  apply (div_le_iff₀ hc).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hq).mpr
  have hn : (0 : ℝ) ≤ (event (fun i : Fin (m + 1) => |c + q / m * i.val| ≤ t)).card :=
    Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right hcount hm'.le
  have hmul : q / (m : ℝ) * m = q := div_mul_cancel₀ q (ne_of_gt hm')
  rw [mul_assoc, hmul] at hh
  push_cast
  nlinarith

end PlanarL1.FiniteRandom

namespace PlanarL1.FiniteRandom

attribute [local instance] Classical.propDecidable

/-- Independent uniform grid coordinates can be exposed one at a time by an
actual equivalence of finite sample spaces. -/
lemma coordinate_probability {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (m : ℕ) (hm : 0 < m) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t)
    (F : (I → Fin (m + 1)) → ℝ)
    (hF : ∀ α : I → Fin (m + 1), ∃ c : ℝ,
      (∀ r : Fin (m + 1), F (Function.update α i r) = c + q / m * r.val) ∨
      (∀ r : Fin (m + 1), F (Function.update α i r) = c - q / m * r.val)) :
    prob (fun α => |F α| ≤ t) ≤ (2 * t + q / m) / q := by
  classical
  let e : (I → Fin (m + 1)) ≃ ({j : I // j ≠ i} → Fin (m + 1)) × Fin (m + 1) :=
    (Equiv.funSplitAt i (Fin (m + 1))).trans (Equiv.prodComm _ _)
  have he := prob_equiv e.symm (fun α => |F α| ≤ t)
  rw [← he]
  apply prob_prod_bound
  intro rest
  let α : I → Fin (m + 1) := e.symm (rest, 0)
  have hu (r : Fin (m + 1)) : e.symm (rest,r) = Function.update α i r := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, α, Equiv.funSplitAt_symm_apply]
    · simp [e, α, Equiv.funSplitAt_symm_apply, hj]
  obtain ⟨c, hc⟩ := hF α
  rcases hc with hc | hc
  · have hp := prob_mono (fun r (hr : |F (e.symm (rest,r))| ≤ t) =>
      (show |c + q / m * r.val| ≤ t by simpa only [hu r, hc r] using hr))
    exact hp.trans (grid_probability m hm hq ht c)
  · have hp := prob_mono (fun r (hr : |F (e.symm (rest,r))| ≤ t) =>
      (show |-c + q / m * r.val| ≤ t by
        rw [hu r, hc r] at hr
        rw [show -c + q / m * r.val = -(c - q / m * r.val) by ring, abs_neg]
        exact hr))
    exact hp.trans (grid_probability m hm hq ht (-c))

lemma prob_false {Ω : Type*} [Fintype Ω] : prob (fun _ : Ω => False) = 0 := by
  simp [prob, event]

lemma prob_pair_bound {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (S : Finset ι) (P : ι → ι → Ω → Prop) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → prob (P i j) ≤ b) :
    prob (fun w => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ P i j w) ≤ (S.card : ℝ)^2 * b := by
  classical
  have he : (fun w => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ P i j w) =
      (fun w => ∃ ij ∈ S ×ˢ S, ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) := by
    funext w
    simp only [Finset.mem_product, Prod.exists]
    aesop
  rw [he]
  calc
    prob (fun w => ∃ ij ∈ S ×ˢ S, ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) ≤
        ∑ ij ∈ S ×ˢ S, prob (fun w => ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) := prob_union_bound _ _
    _ ≤ ∑ _ij ∈ S ×ˢ S, b := by
      apply Finset.sum_le_sum
      intro ij hij
      by_cases heq : ij.1 = ij.2
      · have hz : prob (fun w => ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) = 0 := by
          simpa only [heq, ne_eq, not_true_eq_false, false_and] using (prob_false (Ω := Ω))
        rw [hz]
        exact hb
      · exact (prob_mono (fun _ hw => hw.2)).trans
          (h ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2 heq)
    _ = (S.card : ℝ)^2 * b := by simp [pow_two]

end PlanarL1.FiniteRandom

end

section

namespace PlanarL1.FiniteRandom
lemma prob_prod_bound_left {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Λ]
    (P : Ω × Λ → Prop) {b : ℝ} (h : ∀ z, prob (fun w : Ω => P (w,z)) ≤ b) :
    prob P ≤ b := by
  rw [← prob_equiv (Equiv.prodComm Λ Ω) P]
  exact prob_prod_bound _ h
end PlanarL1.FiniteRandom


end

section

namespace PlanarL1.FiniteRandom

/-- Expose one independent finite coordinate, retaining every other coordinate.
This is the conditional probability step used between distinct seed groups. -/
lemma prob_update_bound {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Nonempty Ω] (i : I) (P : (I → Ω) → Prop) {b : ℝ}
    (h : ∀ α, prob (fun r : Ω => P (Function.update α i r)) ≤ b) :
    prob P ≤ b := by
  classical
  let e : (I → Ω) ≃ ({j : I // j ≠ i} → Ω) × Ω :=
    (Equiv.funSplitAt i Ω).trans (Equiv.prodComm _ _)
  rw [← prob_equiv e.symm P]
  apply prob_prod_bound
  intro rest
  let α : I → Ω := e.symm (rest, Classical.arbitrary Ω)
  have hu (r : Ω) : e.symm (rest,r) = Function.update α i r := by
    funext j
    by_cases hj : j=i
    · subst j; simp [e,α,Equiv.funSplitAt_symm_apply]
    · simp [e,α,Equiv.funSplitAt_symm_apply,hj]
  simpa only [hu] using h α

end PlanarL1.FiniteRandom


end

section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable

lemma prob_singleton {Ω : Type*} [Fintype Ω] (x : Ω) :
    prob (fun ω => ω=x) = 1/(Fintype.card Ω : ℝ) := by
  classical
  have he : event (fun ω : Ω => ω=x)={x} := by
    ext ω
    simp only [mem_event,Finset.mem_singleton]
  rw [prob,he]
  simp

/-- Exact probability of any finite prescribed set of independent fair coins.
Unprescribed coins are unrestricted, so their number does not affect the bound. -/
lemma prob_prescribed {I : Type*} [Fintype I] (S : Finset I) (b : I → Bool) :
    prob (fun ω : I → Bool => ∀ i ∈ S, ω i=b i) = 1/(2:ℝ)^S.card := by
  classical
  let e : (I → Bool) ≃ ({i : I // i ∉ S} → Bool) × ({i : I // i ∈ S} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).trans (Equiv.prodComm _ _)
  let f : {i : I // i ∈ S} → Bool := fun i => b i
  have he (ω : ({i : I // i ∉ S} → Bool) × ({i : I // i ∈ S} → Bool)) :
      (∀ i ∈ S, e.symm ω i=b i) ↔ ω.2=f := by
    constructor
    · intro h
      funext i
      simpa [e,f,Equiv.piEquivPiSubtypeProd] using h i i.property
    · intro h i hi
      simpa [e,f,Equiv.piEquivPiSubtypeProd,hi] using congrFun h ⟨i,hi⟩
  rw [← prob_equiv e.symm (fun ω : I → Bool => ∀ i ∈ S, ω i=b i)]
  simp_rw [he]
  rw [prob_prod]
  simp_rw [prob_singleton]
  have hc : (Fintype.card ({i : I // i ∉ S} → Bool) : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hc]
  simp

lemma prob_two_coins {I : Type*} [Fintype I] (i j : I) (hij : i ≠ j) (a b : Bool) :
    prob (fun ω : I → Bool => ω i=a ∧ ω j=b) = (1:ℝ)/4 := by
  classical
  have h := prob_prescribed ({i,j} : Finset I) (Function.update (fun _ => b) i a)
  have hp (ω : I → Bool) : (∀ k ∈ ({i,j} : Finset I),
      ω k=Function.update (fun _ => b) i a k) ↔ ω i=a ∧ ω j=b := by
    simp [Function.update,Ne.symm hij]
  have hc : ({i,j} : Finset I).card=2 := by simp [hij]
  simpa only [hp,hc,pow_two,show (2:ℝ)*2=4 by norm_num] using h

/-- Any event forced by at most k independently prescribed group/cell coins
has probability at least 2⁻ᵏ. -/
lemma prob_at_least_prescription {I : Type*} [Fintype I]
    (S : Finset I) (b : I → Bool) (P : (I → Bool) → Prop) {k : ℕ}
    (hk : S.card ≤ k) (h : ∀ ω, (∀ i ∈ S, ω i=b i) → P ω) :
    1/(2:ℝ)^k ≤ prob P := by
  calc
    _ ≤ 1/(2:ℝ)^S.card := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hk
    _ = prob (fun ω : I → Bool => ∀ i ∈ S, ω i=b i) := (prob_prescribed S b).symm
    _ ≤ prob P := prob_mono h

end PlanarL1.FiniteRandom



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
/-! ## The deterministic clamping core of thin-band interpolation
No probabilistic or geometric claim is assumed by
these lemmas; they establish the scalar inequalities used at each actual node. -/

namespace Interpolation

/-- The obstruction in `int:depth`: a distant node cannot pass an accurate
parent value unchanged. The constants 6, 7 and 13 are the source's constants. -/
theorem distant_node_overwrites {parent upper lower tentative p δ : ℝ}
    (hδ : 0 < δ) (hp : |parent - p| ≤ 6 * δ)
    (hu : p + 7 * δ < upper) (hl : lower < p - 7 * δ)
    (ht : p + 13 * δ < tentative) :
    p + 7 * δ < nodeValue parent upper lower tentative ∧
      nodeValue parent upper lower tentative ≠ parent := by
  have habs := abs_le.mp hp
  have hup : parent < upper := by linarith
  have hlow : lower < parent := by linarith
  have hv : p + 7 * δ < nodeValue parent upper lower tentative := by
    simp only [nodeValue, max_eq_right hup.le, min_eq_right hlow.le]
    exact lt_min hu ((by linarith : p + 7 * δ < tentative).trans_le (le_max_right _ _))
  refine ⟨hv, ?_⟩
  intro heq
  rw [heq] at hv
  linarith

/-- A name from before the current node can only be selected by literally
inheriting the parent's atom. In particular its scalar value is inherited too. -/
lemma nodeNamed_old {parent upper lower tentative : NamedValue} {cutoff : ℕ}
    (hu : cutoff ≤ upper.name) (hl : cutoff ≤ lower.name)
    (ht : cutoff ≤ tentative.name)
    (h : (nodeNamed parent upper lower tentative).name < cutoff) :
    nodeNamed parent upper lower tentative = parent := by
  rcases nodeNamed_mem parent upper lower tentative with heq | heq | heq | heq
  · exact heq
  all_goals rw [heq] at h; omega


end Interpolation



end PlanarL1

end

section

namespace PlanarL1.Interpolation
open scoped NNReal

/-- A continuous finite selection cannot change its recorded branch on a ball
without a near tie at the center. This includes the old-field branch of a
clipping, even though that branch has no fresh offset of its own. -/
lemma selection_near_tie {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (F : X → NamedValue) (atom : ℕ → X → ℝ) (S : Finset ℕ)
    (hF : LipschitzWith K (fun z => (F z).value))
    (hA : ∀ i ∈ S, LipschitzWith K (atom i)) (x : X) {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hlist : ∀ z, dist x z ≤ ρ → (F z).name ∈ S ∧ (F z).value = atom (F z).name z)
    (hbad : ∃ z, dist x z ≤ ρ ∧ (F z).name ≠ (F x).name) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ |atom i x-atom j x| ≤ 2*K*ρ := by
  obtain ⟨z,hz,hn⟩ := hbad
  have hx := hlist x (by simpa using hρ)
  have hz' := hlist z hz
  refine ⟨(F x).name,hx.1,(F z).name,hz'.1,Ne.symm hn,?_⟩
  have hf := hF.dist_le_mul x z
  have ha := (hA (F z).name hz'.1).dist_le_mul z x
  rw [Real.dist_eq,dist_comm z x,← hz'.2] at ha
  rw [Real.dist_eq] at hf
  rw [← hx.2]
  have ht := abs_sub_le (F x).value (F z).value (atom (F z).name x)
  have hm := mul_le_mul_of_nonneg_left hz K.coe_nonneg
  linarith

lemma selection_probability {X Ω : Type*} [PseudoMetricSpace X] [Fintype Ω]
    {K : ℝ≥0} (F : Ω → X → NamedValue) (atom : Ω → ℕ → X → ℝ)
    (S : Finset ℕ) (hF : ∀ ω, LipschitzWith K (fun z => (F ω z).value))
    (hA : ∀ ω i, i ∈ S → LipschitzWith K (atom ω i)) (x : X) {ρ b : ℝ}
    (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (hlist : ∀ ω z, dist x z ≤ ρ → (F ω z).name ∈ S ∧
      (F ω z).value = atom ω (F ω z).name z)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      FiniteRandom.prob (fun ω => |atom ω i x-atom ω j x| ≤ 2*K*ρ) ≤ b) :
    FiniteRandom.prob (fun ω => ∃ z, dist x z ≤ ρ ∧ (F ω z).name ≠ (F ω x).name) ≤
      S.card^2*b := by
  apply (FiniteRandom.prob_mono (fun ω h =>
    selection_near_tie (F ω) (atom ω) S (hF ω) (hA ω) x hρ (hlist ω) h)).trans
  exact FiniteRandom.prob_pair_bound S _ hb hpair

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

lemma clipNames_card (S : Finset ℕ) : (clipNames S).card ≤ S.card+2 := by
  calc
    _ ≤ (insert 1 (S.image (fun i => i+2))).card+1 := Finset.card_insert_le _ _
    _ ≤ (S.image (fun i => i+2)).card+1+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
    _ ≤ S.card+2 := by have h := Finset.card_image_le (s := S) (f := fun i => i+2); omega

lemma mem_clipNames {S : Finset ℕ} {i : ℕ} :
    i ∈ clipNames S ↔ i = 0 ∨ i = 1 ∨ (2 ≤ i ∧ i-2 ∈ S) := by
  simp only [clipNames,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro (h | h | ⟨j,hj,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨by omega,by simpa using hj⟩)
  · rintro (h | h | ⟨hi,hS⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i-2,hS,by omega⟩)

lemma namedClip_list {X : Type*} (F : X → NamedValue) (atom : ℕ → X → ℝ)
    (old shield : X → ℝ) (S : Finset ℕ) (x : X)
    (hm : (F x).name ∈ S) (he : (F x).value = atom (F x).name x) :
    (namedClip F old shield x).name ∈ clipNames S ∧
      (namedClip F old shield x).value = clipAtom atom old shield (namedClip F old shield x).name x := by
  rcases clippedNamed_mem ⟨0,old x⟩ ⟨(F x).name+2,(F x).value⟩ ⟨1,shield x⟩ with h | h | h
  · change namedClip F old shield x = _ at h
    rw [h]
    simp [clipNames,clipAtom]
  · change namedClip F old shield x = _ at h
    rw [h]
    dsimp only
    have hz : (F x).name+2 ≠ 0 := by omega
    have ho : (F x).name+2 ≠ 1 := by omega
    constructor
    · exact mem_clipNames.mpr (Or.inr (Or.inr ⟨by omega,by simpa using hm⟩))
    · simpa only [clipAtom,ite_eq_right hz,ite_eq_right ho,Nat.add_sub_cancel] using he
  · change namedClip F old shield x = _ at h
    rw [h]
    simp [clipNames,clipAtom]

lemma clipAtom_lipschitz {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (atom : ℕ → X → ℝ) (old shield : X → ℝ)
    (hA : ∀ i, LipschitzWith K (atom i)) (ho : LipschitzWith K old)
    (hh : LipschitzWith K shield) (i : ℕ) :
    LipschitzWith K (clipAtom atom old shield i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  dsimp only [clipAtom]
  split_ifs with hi hi'
  · exact ho.dist_le_mul x y
  · exact hh.dist_le_mul x y
  · exact (hA (i-2)).dist_le_mul x y

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

lemma secondaryNames_card (S : Finset ℕ) : (secondaryNames S).card ≤ S.card+3 := by
  unfold secondaryNames
  calc
    _ ≤ ((S.image (fun i => i+3)).card+1)+1+1 := by
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right
          (Finset.card_insert_le _ _) 1)) 1)
    _ ≤ S.card+3 := by have h := Finset.card_image_le (s := S) (f := fun i => i+3); omega

lemma mem_secondaryNames {S : Finset ℕ} {i : ℕ} :
    i ∈ secondaryNames S ↔ i=0 ∨ i=1 ∨ i=2 ∨ (3 ≤ i ∧ i-3 ∈ S) := by
  classical
  simp only [secondaryNames,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro (h | h | h | ⟨j,hj,h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      exact ⟨by omega,by simpa only [← h,Nat.add_sub_cancel] using hj⟩
  · rintro (h | h | h | ⟨hi,h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      exact ⟨i-3,h,by omega⟩

lemma secondaryNamed_list {X : Type*} (F : X → NamedValue) (atom : ℕ → X → ℝ)
    (old ordered shield : X → ℝ) (ordinary : Bool) (S : Finset ℕ) (x : X)
    (hm : (F x).name ∈ S) (he : (F x).value = atom (F x).name x) :
    (secondaryNamed F old ordered shield ordinary x).name ∈ secondaryNames S ∧
      (secondaryNamed F old ordered shield ordinary x).value =
        secondaryAtom atom old ordered shield (secondaryNamed F old ordered shield ordinary x).name x := by
  rcases secondaryNamed_mem F old ordered shield ordinary x with h | h | h | h
  · rw [h]; simp [secondaryNames,secondaryAtom]
  · rw [h]; simp [secondaryNames,secondaryAtom]
  · rw [h]; simp [secondaryNames,secondaryAtom]
  · rw [h]
    dsimp only
    have h0 : (F x).name+3 ≠ 0 := by omega
    have h1 : (F x).name+3 ≠ 1 := by omega
    have h2 : (F x).name+3 ≠ 2 := by omega
    constructor
    · exact mem_secondaryNames.mpr (Or.inr (Or.inr (Or.inr ⟨by omega,by simpa using hm⟩)))
    · simpa only [secondaryAtom,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,Nat.add_sub_cancel] using he

lemma secondaryAtom_lipschitz {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (atom : ℕ → X → ℝ) (old ordered shield : X → ℝ)
    (hA : ∀ i, LipschitzWith K (atom i)) (ho : LipschitzWith K old)
    (hO : LipschitzWith K ordered) (hh : LipschitzWith K shield) (i : ℕ) :
    LipschitzWith K (secondaryAtom atom old ordered shield i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  dsimp only [secondaryAtom]
  split_ifs with hi hi' hi''
  · exact ho.dist_le_mul x y
  · exact hh.dist_le_mul x y
  · exact hO.dist_le_mul x y
  · exact (hA (i-3)).dist_le_mul x y

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

lemma familyName_inj {k : ℕ} (g h : Fin k) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    familyName g i = familyName h j ↔ g=h ∧ i=j := by
  simp only [familyName,ite_eq_right hi,ite_eq_right hj,Nat.add_right_cancel_iff,Nat.pair_eq_pair]
  constructor
  · rintro ⟨hg,hs⟩
    exact ⟨Fin.ext hg,by omega⟩
  · rintro ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩

lemma mem_familyNames {k : ℕ} {S : Fin k → Finset ℕ} {i : ℕ} :
    i ∈ familyNames S ↔ i=0 ∨ ∃ g, ∃ j ∈ S g, familyName g j=i := by
  classical
  simp [familyNames]

lemma familyAtom_zero {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (x : X) : familyAtom old A 0 x = old x := by
  simp [familyAtom]

lemma familyAtom_name {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (g : Fin k) {i : ℕ} (hi : i ≠ 0) (x : X) :
    familyAtom old A (familyName g i) x = A g i x := by
  have hg := g.isLt
  simp [familyAtom,familyName,hi,Nat.unpair_pair,hg,show i-1+1=i by omega]

lemma familySelection_list {X : Type*} {k : ℕ} (old : X → ℝ)
    (F : Fin k → X → NamedValue) (A : Fin k → ℕ → X → ℝ) (S : Fin k → Finset ℕ)
    (hzero : ∀ g x, A g 0 x = old x) (x : X)
    (hlist : ∀ g, (F g x).name ∈ S g ∧ (F g x).value = A g (F g x).name x) :
    (familySelection old F x).name ∈ familyNames S ∧
      (familySelection old F x).value = familyAtom old A (familySelection old F x).name x := by
  rcases maxSelection_mem (fun x => ⟨0,old x⟩)
    (List.ofFn (fun g => fun x => ⟨familyName g (F g x).name,(F g x).value⟩)) x with h | ⟨G,hG,h⟩
  · change familySelection old F x = _ at h
    rw [h]
    exact ⟨mem_familyNames.mpr (Or.inl rfl),(familyAtom_zero old A x).symm⟩
  · obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
    change familySelection old F x = _ at h
    rw [h]
    dsimp only
    constructor
    · exact mem_familyNames.mpr (Or.inr ⟨g,(F g x).name,(hlist g).1,rfl⟩)
    · rw [(hlist g).2]
      by_cases he : (F g x).name=0
      · rw [he,familyName_zero,familyAtom_zero,hzero]
      · rw [familyAtom_name old A g he]

end PlanarL1.Interpolation


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_RadialTree
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)

namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

/-! ### The actual radial-node tree and its interpolation formulas
The geometric data below use precisely the thin-band constants. Nodes and their
parent maps are induced-graph components, not an assumed abstract hierarchy. -/

namespace RadialTree

variable (R : RadialTree (M := M) (J := J) (root := root))

open Interpolation

lemma formula_child_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node (k + 1))
    (v : M.Point J root) (hv : v = (R.portals C).left ∨ v = (R.portals C).right) :
    |(R.formula p α k (R.parent C) v).value - p v| ≤ 5 * R.δ := by
  have hn : R.portalDistance (R.parent C) v ≤ R.δ + 220 * R.a := by
    simpa only [portalDistance, dist_comm v] using R.parent_near C v hv
  have hd : R.δ - 10 * R.a ≤ R.portalDistance (R.parent C) v :=
    le_min (R.parent_separated C _ v (Or.inl rfl) hv)
      (R.parent_separated C _ v (Or.inr rfl) hv)
  exact (R.formula_near_accuracy hp hα k (R.parent C) v hn).2
    (R.portal_spacing.trans (mul_le_mul_of_nonneg_left hd R.zeta_pos.le))

/-- A name older than a chosen depth is inherited literally all the way back
through the actual hierarchy. Intercepts are not re-evaluated or renamed. -/
lemma formula_inherits (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (j : ℕ) (hj : j ≤ k) (v : M.Point J root)
    (hname : (R.formula p α k C v).name < 3 * n * j) :
    R.formula p α k C v = R.formula p α j (R.ancestor C j hj) v := by
  induction k generalizing j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rw [R.ancestor_self]
  | succ k ih =>
    by_cases hlast : j = k + 1
    · subst j
      rw [R.ancestor_self]
    · have hjk : j ≤ k := by omega
      have hstep : R.formula p α (k + 1) C v = R.formula p α k (R.parent C) v := by
        change nodeNamed _ _ _ _ = _
        apply nodeNamed_old (cutoff := 3 * n * j)
        · exact (Nat.mul_le_mul_left (3 * n) hj).trans (R.upperCone_names _ _ C v).1
        · exact (Nat.mul_le_mul_left (3 * n) hj).trans (R.lowerCone_names _ _ C v).1
        · exact (Nat.mul_le_mul_left (3 * n) hj).trans (R.tentative_names p α C v).1
        · exact hname
      have hi := ih (R.parent C) j hjk (by simpa only [hstep] using hname)
      rw [R.ancestor_parent C hjk] at hi
      exact hstep.trans hi

/-- A far node cannot output an accurate value carrying an earlier name. -/
lemma formula_far_name {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root)
    (hfar : 13 * R.δ < R.ζ * R.portalDistance C v)
    (hacc : |(R.formula p α (k + 1) C v).value - p v| ≤ 6 * R.δ) :
    3 * n * (k + 1) ≤ (R.formula p α (k + 1) C v).name := by
  by_contra hn
  have hn' := lt_of_not_ge hn
  let F := R.formula p α k (R.parent C)
  have hF : ∀ w, w = (R.portals C).left ∨ w = (R.portals C).right →
      |(F w).value - p w| ≤ 5 * R.δ := R.formula_child_accuracy hp hα C
  obtain ⟨hA, hB⟩ := R.cone_bounds hp hα C F hF v
  have hT := (R.tentative_bounds hp hα C v).1
  have hsame : R.formula p α (k + 1) C v = F v := by
    apply nodeNamed_old (R.upperCone_names F α C v).1 (R.lowerCone_names F α C v).1
      (R.tentative_names p α C v).1 hn'
  have hparent : |(F v).value - p v| ≤ 6 * R.δ := by simpa only [hsame] using hacc
  have hneq := (distant_node_overwrites R.delta_pos hparent
    (show p v + 7 * R.δ < (R.upperCone F α C v).value by linarith [R.q_small, R.delta_pos])
    (show (R.lowerCone F α C v).value < p v - 7 * R.δ by linarith [R.q_small, R.delta_pos])
    (show p v + 13 * R.δ < (R.tentative p α C v).value by linarith [R.q_pos])).2
  apply hneq
  have heq := congrArg NamedValue.value hsame
  simpa only [formula, nodeNamed_value, F] using heq

lemma lookback_large : 15 ≤ R.ζ * (R.lookback : ℝ) := by
  have hh := Nat.le_ceil (15 / R.ζ)
  have hb : 15 / R.ζ ≤ (R.lookback : ℝ) := by
    dsimp [lookback]
    push_cast
    linarith
  have h := (div_le_iff₀ R.zeta_pos).mp hb
  nlinarith

lemma ancestor_distance {k j : ℕ} (C : R.Node k) (hj : j ≤ k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) :
    ((k : ℝ) - j) * R.δ - 3 * R.a ≤ R.portalDistance (R.ancestor C j hj) v := by
  let D := R.ancestor C j hj
  have hver : dist v (v.withHeight R.base.height R.base.inBand) ≤ R.a / 2 := by
    rw [v.dist_withHeight, abs_sub_comm]
    exact R.half_width v.height v.inBand
  have hrad := dist_triangle R.base v (v.withHeight R.base.height R.base.inBand)
  have single (w : M.Point J root) (hw : dist R.base w < (j : ℝ) * R.δ + R.a) :
      ((k : ℝ) - j) * R.δ - 3 * R.a ≤ dist w v := by
    nlinarith [dist_triangle R.base w v, R.width_pos]
  exact le_min (single (R.portals D).left (R.portals D).left_radial.2)
    (single (R.portals D).right (R.portals D).right_radial.2)

lemma far_after_lookback {r : ℝ} (hr : (R.lookback : ℝ) * R.δ - 3 * R.a ≤ r) :
    13 * R.δ < R.ζ * r := by
  have h₁ := mul_le_mul_of_nonneg_left hr R.zeta_pos.le
  have h₂ := mul_le_mul_of_nonneg_right R.lookback_large R.delta_pos.le
  have h₃ : R.ζ * R.a ≤ R.a := by
    have hh := mul_lt_mul_of_pos_right R.zeta_lt_one R.width_pos
    linarith
  nlinarith [R.width_small, R.delta_pos]

/-- Selected names of an accurate node at high radial points originate no
more than `lookback` generations earlier. This is not an assumed depth bound. -/
lemma formula_recent_bound {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (ha : |(R.formula p α k C v).value - p v| ≤ 6 * R.δ) :
    3 * n * (k - R.lookback) ≤ (R.formula p α k C v).name := by
  by_cases hk : k ≤ R.lookback
  · simp only [Nat.sub_eq_zero_of_le hk, Nat.mul_zero, Nat.zero_le]
  · have hmk : k - R.lookback ≤ k := Nat.sub_le _ _
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
      (show k - R.lookback ≠ 0 by omega)
    have hjk : j + 1 ≤ k := by omega
    by_contra hname
    have hn : (R.formula p α k C v).name < 3 * n * (j + 1) := by
      simpa only [hj] using lt_of_not_ge hname
    have heq := R.formula_inherits p α k C (j + 1) hjk v hn
    let D := R.ancestor C (j + 1) hjk
    have hacc : |(R.formula p α (j + 1) D v).value - p v| ≤ 6 * R.δ := by
      simpa only [heq] using ha
    have hfar := R.ancestor_distance C hjk v hv
    have hcast : (k : ℝ) - (j + 1 : ℕ) = R.lookback := by
      have hn : k = j + 1 + R.lookback := by omega
      exact_mod_cast (show (k : ℤ) - (j + 1) = R.lookback by omega)
    rw [hcast] at hfar
    have hnew := R.formula_far_name hp hα D v (R.far_after_lookback hfar) hacc
    rw [heq] at hn
    exact hn.not_ge hnew


lemma nodeNames_card {k : ℕ} (C : R.Node k) : (R.nodeNames C).card ≤ 6 := by
  calc
    (R.nodeNames C).card ≤ (Finset.univ : Finset (Fin 2 × Fin 3)).card := Finset.card_image_le
    _ = 6 := by simp

lemma nodeNames_mem {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) :
    atomName k (R.portalAt C i) t ∈ R.nodeNames C := by
  exact Finset.mem_image.mpr ⟨(i, t), Finset.mem_univ _, rfl⟩

lemma nodeNames_left {k : ℕ} (C : R.Node k) (t : Fin 3) :
    atomName k (R.portals C).left t ∈ R.nodeNames C := by
  simpa [portalAt] using R.nodeNames_mem C 0 t

lemma nodeNames_right {k : ℕ} (C : R.Node k) (t : Fin 3) :
    atomName k (R.portals C).right t ∈ R.nodeNames C := by
  simpa only [portalAt, show (1 : Fin 2) ≠ 0 by decide, ite_false] using R.nodeNames_mem C 1 t

lemma nodeNames_bounds {k : ℕ} (C : R.Node k) {m : ℕ} (hm : m ∈ R.nodeNames C) :
    3 * n * k ≤ m ∧ m < 3 * n * (k + 1) := by
  obtain ⟨⟨i,t⟩, _, rfl⟩ := Finset.mem_image.mp hm
  exact atomName_bounds k (R.portalAt C i) t

lemma tentative_name_mem (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    (R.tentative p α C v).name ∈ R.nodeNames C := by
  rcases minNamed_mem _ _ with h | h
  · rw [tentative, h]; exact R.nodeNames_left C 0
  · rw [tentative, h]; exact R.nodeNames_right C 0

lemma upperCone_name_mem (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    (R.upperCone F α C v).name ∈ R.nodeNames C := by
  rcases minNamed_mem _ _ with h | h
  · rw [upperCone, h]; exact R.nodeNames_left C 1
  · rw [upperCone, h]; exact R.nodeNames_right C 1

lemma lowerCone_name_mem (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    (R.lowerCone F α C v).name ∈ R.nodeNames C := by
  rcases maxNamed_mem _ _ with h | h
  · rw [lowerCone, h]; exact R.nodeNames_left C 2
  · rw [lowerCone, h]; exact R.nodeNames_right C 2

lemma formula_name_origin (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (v : M.Point J root) :
    ∃ j : ℕ, ∃ hj : j ≤ k,
      (R.formula p α k C v).name ∈ R.nodeNames (R.ancestor C j hj) := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    rw [R.ancestor_self]
    exact R.tentative_name_mem p α C v
  | succ k ih =>
    rw [formula]
    rcases nodeNamed_mem _ _ _ _ with h | h | h | h
    · obtain ⟨j, hj, hm⟩ := ih (R.parent C)
      refine ⟨j, hj.trans (Nat.le_succ k), ?_⟩
      rw [h, ← R.ancestor_parent C hj]
      exact hm
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [h, R.ancestor_self]
      exact R.upperCone_name_mem _ _ C v
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [h, R.ancestor_self]
      exact R.lowerCone_name_mem _ _ C v
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [h, R.ancestor_self]
      exact R.tentative_name_mem _ _ C v

lemma recentNames_card {k : ℕ} (C : R.Node k) (L : ℕ) :
    (R.recentNames C L).card ≤ 6 * (L + 1) := by
  calc
    (R.recentNames C L).card ≤
        ∑ j ∈ (Finset.Icc (k - L) k).attach,
          (R.nodeNames (R.ancestor C j (Finset.mem_Icc.mp j.property).2)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ (Finset.Icc (k - L) k).attach, 6 :=
      Finset.sum_le_sum (fun _ _ => R.nodeNames_card _)
    _ = (k + 1 - (k - L)) * 6 := by simp
    _ ≤ 6 * (L + 1) := by omega

lemma mem_recentNames {k j : ℕ} (C : R.Node k) (L : ℕ) (hj : j ≤ k) (hl : k - L ≤ j)
    {m : ℕ} (hm : m ∈ R.nodeNames (R.ancestor C j hj)) : m ∈ R.recentNames C L := by
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨j, Finset.mem_Icc.mpr ⟨hl, hj⟩⟩, Finset.mem_attach _ _, hm⟩

lemma formula_name_recent {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (ha : |(R.formula p α k C v).value - p v| ≤ 6 * R.δ) :
    (R.formula p α k C v).name ∈ R.recentNames C R.lookback := by
  obtain ⟨j, hj, hm⟩ := R.formula_name_origin p α k C v
  have hlow := R.formula_recent_bound hp hα k C v hv ha
  have hu := (R.nodeNames_bounds _ hm).2
  have hn : 0 < n := Nat.zero_lt_of_lt v.column.isLt
  have hmul : 0 < 3 * n := by omega
  have hjlow : k - R.lookback ≤ j := by
    by_contra h
    have hj' : j + 1 ≤ k - R.lookback := by omega
    have hle := Nat.mul_le_mul_left (3 * n) hj'
    omega
  exact R.mem_recentNames C R.lookback hj hjlow hm

lemma formula_noise_congr (p : M.Point J root → ℝ) (α β : Noise (n := n))
    (k : ℕ) (h : ∀ j ≤ k, ∀ i t, α j i t = β j i t)
    (C : R.Node k) (v : M.Point J root) : R.formula p α k C v = R.formula p β k C v := by
  induction k generalizing v with
  | zero => simp only [formula, tentative, h 0 le_rfl]
  | succ k ih =>
    have he : R.formula p α k (R.parent C) = R.formula p β k (R.parent C) :=
      funext (fun w => ih (fun j hj => h j (hj.trans (Nat.le_succ k))) (R.parent C) w)
    simp only [formula, he, upperCone, lowerCone, tentative, h (k + 1) le_rfl]

lemma parentValue_noise_congr (p : M.Point J root → ℝ) (α β : Noise (n := n))
    (k : ℕ) (h : ∀ j < k, ∀ i t, α j i t = β j i t)
    (C : R.Node k) (v : M.Point J root) : R.parentValue p α k C v = R.parentValue p β k C v := by
  cases k with
  | zero => rfl
  | succ k => exact congrArg NamedValue.value (R.formula_noise_congr p α β k
      (fun j hj => h j (Nat.lt_succ_of_le hj)) (R.parent C) v)

lemma atomIntercept_noise_congr (p : M.Point J root → ℝ) (α β : Noise (n := n))
    (k : ℕ) (h : ∀ j < k, ∀ i t, α j i t = β j i t)
    (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) :
    R.atomIntercept p α C i t v = R.atomIntercept p β C i t v := by
  simp only [atomIntercept, R.parentValue_noise_congr p α β k h]

lemma nodeAtom_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) :
    LipschitzWith 1 (fun v => (R.nodeAtom p α C i t v).value) := by
  let c := (if t = 0 then p (R.portalAt C i) else R.parentValue p α k C (R.portalAt C i)) +
    (if t = 1 then -α k (R.portalAt C i).column t else α k (R.portalAt C i).column t)
  by_cases ht : t = 2
  · have he : (fun v => (R.nodeAtom p α C i t v).value) = (fun v => c - dist (R.portalAt C i) v) := by
      funext v
      simp only [nodeAtom, atomIntercept, ite_eq_left ht]
      dsimp only [c]
      ring
    rw [he]
    exact (distance_cone_lipschitz (R.portalAt C i) c).2
  · have he : (fun v => (R.nodeAtom p α C i t v).value) = (fun v => c + dist (R.portalAt C i) v) := by
      funext v
      simp only [nodeAtom, atomIntercept, ite_eq_right ht]
      dsimp only [c]
      ring
    rw [he]
    exact (distance_cone_lipschitz (R.portalAt C i) c).1

lemma chainName_bounds {k : ℕ} (C : R.Node k) (u : ChainIndex k) :
    3 * n * u.1.val ≤ R.chainName C u ∧ R.chainName C u < 3 * n * (u.1.val + 1) :=
  atomName_bounds _ _ _

lemma chainAtom_eq_of_name (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (u u' : ChainIndex k) (h : R.chainName C u = R.chainName C u') :
    R.chainAtom p α C u = R.chainAtom p α C u' := by
  have h₁ := R.chainName_bounds C u
  have h₂ := R.chainName_bounds C u'
  have hd : u.1.val = u'.1.val := by
    rcases lt_trichotomy u.1.val u'.1.val with hl | he | hr
    · have hb := Nat.mul_le_mul_left (3 * n) (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one] at hb
      omega
    · exact he
    · have hb := Nat.mul_le_mul_left (3 * n) (Nat.succ_le_of_lt hr)
      simp only [Nat.succ_eq_add_one] at hb
      omega
  rcases u with ⟨j, i, t⟩
  rcases u' with ⟨j', i', t'⟩
  have hj : j = j' := Fin.ext hd
  subst j'
  exact R.nodeAtom_eq_of_name p α _ i i' t t' h

lemma representative_name {k : ℕ} (C : R.Node k) (L m : ℕ)
    (hm : m ∈ R.recentNames C L) : R.chainName C (R.representative C L m hm) = m :=
  (R.recentNames_representation C L m hm).choose_spec

lemma listedAtom_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (L m : ℕ) :
    LipschitzWith 1 (fun v => (R.listedAtom p α C L m v).value) := by
  unfold listedAtom
  split_ifs with hm
  · exact R.nodeAtom_lipschitz p α _ _ _
  · exact (LipschitzWith.const (0 : ℝ)).weaken (by simp)

lemma formula_eq_listed {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (ha : |(R.formula p α k C v).value - p v| ≤ 6 * R.δ) :
    R.formula p α k C v = R.listedAtom p α C R.lookback (R.formula p α k C v).name v := by
  have hm := R.formula_name_recent hp hα k C v hv ha
  obtain ⟨j, hj, i, t, he⟩ := R.formula_eq_atom p α k C v
  rw [listedAtom, dite_eq_left hm]
  let u : ChainIndex k := (⟨j, Nat.lt_succ_of_le hj⟩, i, t)
  have hu : R.chainName C u = (R.formula p α k C v).name := (congrArg NamedValue.name he).symm
  have hn := R.representative_name C R.lookback (R.formula p α k C v).name hm
  have heq := congrFun (R.chainAtom_eq_of_name p α C u _ (hu.trans hn.symm)) v
  exact he.trans heq

lemma replaceNoise_self (α : Noise (n := n)) (d : ℕ) (c : Fin n) (t : Fin 3) (r : ℝ) :
    replaceNoise α d c t r d c t = r := by simp [replaceNoise]

lemma replaceNoise_other (α : Noise (n := n)) (d j : ℕ) (c i : Fin n) (t s : Fin 3) (r : ℝ)
    (h : ¬ (j = d ∧ i = c ∧ s = t)) : replaceNoise α d c t r j i s = α j i s := by
  simp only [replaceNoise, ite_eq_right h]

lemma atomIntercept_replace (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k d : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root)
    (hd : k ≤ d) (c : Fin n) (s : Fin 3) (r : ℝ) :
    R.atomIntercept p (replaceNoise α d c s r) C i t v = R.atomIntercept p α C i t v := by
  apply R.atomIntercept_noise_congr
  intro j hj u w
  exact replaceNoise_other α d j c u s w r (by omega)

lemma nodeAtom_replace_self (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) (r : ℝ) :
    (R.nodeAtom p (replaceNoise α k (R.portalAt C i).column t r) C i t v).value =
      R.atomIntercept p α C i t v + (if t = 1 then -r else r) := by
  simp only [nodeAtom, R.atomIntercept_replace p α C i t v le_rfl,
    replaceNoise_self]

lemma nodeAtom_replace_other (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k d : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root)
    (hd : k ≤ d) (c : Fin n) (s : Fin 3) (r : ℝ)
    (h : ¬ (k = d ∧ (R.portalAt C i).column = c ∧ t = s)) :
    R.nodeAtom p (replaceNoise α d c s r) C i t v = R.nodeAtom p α C i t v := by
  simp only [nodeAtom, R.atomIntercept_replace p α C i t v hd,
    replaceNoise_other α d k c (R.portalAt C i).column s t r h]

/-- Every distinct pair on the ancestor chain has a fresh coordinate: after
all other noises are fixed, their difference is affine with slope ±1 in it. -/
lemma chainPair_fresh (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k)
    (u u' : ChainIndex k) (hne : R.chainName C u ≠ R.chainName C u') (v : M.Point J root) :
    ∃ d ≤ k, ∃ c : Fin n, ∃ s : Fin 3,
      ∀ α : Noise (n := n), ∃ b : ℝ,
        (∀ r : ℝ, (R.chainAtom p (replaceNoise α d c s r) C u v).value -
          (R.chainAtom p (replaceNoise α d c s r) C u' v).value = b + r) ∨
        (∀ r : ℝ, (R.chainAtom p (replaceNoise α d c s r) C u v).value -
          (R.chainAtom p (replaceNoise α d c s r) C u' v).value = b - r) := by
  let D := R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)
  let D' := R.ancestor C u'.1 (Nat.le_of_lt_succ u'.1.isLt)
  have hcoord : ¬ (u.1.val = u'.1.val ∧
      (R.portalAt D u.2.1).column = (R.portalAt D' u'.2.1).column ∧ u.2.2 = u'.2.2) := by
    rintro ⟨hd, hc, ht⟩
    apply hne
    simp only [chainName, atomName]
    change 3 * (n * u.1.val + (R.portalAt D u.2.1).column.val) + u.2.2.val =
      3 * (n * u'.1.val + (R.portalAt D' u'.2.1).column.val) + u'.2.2.val
    simp only [hd, hc, ht]
  by_cases hd : u.1.val ≤ u'.1.val
  · refine ⟨u'.1, Nat.le_of_lt_succ u'.1.isLt, (R.portalAt D' u'.2.1).column, u'.2.2, ?_⟩
    intro α
    refine ⟨(R.chainAtom p α C u v).value - R.atomIntercept p α D' u'.2.1 u'.2.2 v, ?_⟩
    by_cases hs : u'.2.2 = 1
    · left
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D _ _ v hd _ _ r hcoord,
        R.nodeAtom_replace_self p α D' _ _ v r, ite_eq_left hs]
      ring
    · right
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D _ _ v hd _ _ r hcoord,
        R.nodeAtom_replace_self p α D' _ _ v r, ite_eq_right hs]
      ring
  · have hd' : u'.1.val ≤ u.1.val := by omega
    have hcoord' : ¬ (u'.1.val = u.1.val ∧
        (R.portalAt D' u'.2.1).column = (R.portalAt D u.2.1).column ∧ u'.2.2 = u.2.2) := by
      rintro ⟨he, hc, ht⟩
      exact hcoord ⟨he.symm, hc.symm, ht.symm⟩
    refine ⟨u.1, Nat.le_of_lt_succ u.1.isLt, (R.portalAt D u.2.1).column, u.2.2, ?_⟩
    intro α
    refine ⟨R.atomIntercept p α D u.2.1 u.2.2 v - (R.chainAtom p α C u' v).value, ?_⟩
    by_cases hs : u.2.2 = 1
    · right
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D' _ _ v hd' _ _ r hcoord',
        R.nodeAtom_replace_self p α D _ _ v r, ite_eq_left hs]
      ring
    · left
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D' _ _ v hd' _ _ r hcoord',
        R.nodeAtom_replace_self p α D _ _ v r, ite_eq_right hs]
      ring

lemma gridNoise_update (cap m : ℕ) (ω : GridSample (n := n) cap m)
    (d : ℕ) (hd : d < cap) (c : Fin n) (s : Fin 3) (r : Fin (m + 1)) :
    R.gridNoise cap m (Function.update ω (⟨d,hd⟩,c,s) r) =
      replaceNoise (R.gridNoise cap m ω) d c s (R.q + R.q / m * r.val) := by
  funext j i t
  by_cases hj : j < cap
  · by_cases he : (⟨j,hj⟩,i,t) = ((⟨d,hd⟩ : Fin cap),c,s)
    · have hparts := Prod.mk.inj he
      have hjd : j = d := congrArg Fin.val hparts.1
      obtain ⟨hic, hts⟩ := Prod.mk.inj hparts.2
      subst j
      subst i
      subst t
      simp only [gridNoise, dite_eq_left hd, Function.update_self, replaceNoise_self]
    · have hne : ¬ (j = d ∧ i = c ∧ t = s) := by
        rintro ⟨hjd, hic, hts⟩
        exact he (by subst j; subst i; subst t; rfl)
      rw [replaceNoise_other _ d j c i s t _ hne]
      simp only [gridNoise, dite_eq_left hj, Function.update_of_ne he]
  · have hne : ¬ (j = d ∧ i = c ∧ t = s) := fun h => hj (h.1 ▸ hd)
    rw [replaceNoise_other _ d j c i s t _ hne]
    simp only [gridNoise, dite_eq_right hj]

lemma depth_le_layerDepth {k : ℕ} (v : M.Point J root)
    (hk : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) :
    k ≤ R.layerDepth v := by
  apply Nat.le_floor
  exact (le_div_iff₀ R.delta_pos).mpr hk


lemma chainPair_probability (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k)
    (u u' : ChainIndex k) (hne : R.chainName C u ≠ R.chainName C u')
    (v : M.Point J root) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.chainAtom p (R.gridNoise cap m ω) C u v).value -
        (R.chainAtom p (R.gridNoise cap m ω) C u' v).value| ≤ t) ≤
      (2 * t + R.q / m) / R.q := by
  classical
  obtain ⟨d, hd, c, s, hf⟩ := R.chainPair_fresh p C u u' hne v
  have hdc : d < cap := hd.trans_lt hk
  apply FiniteRandom.coordinate_probability (⟨d,hdc⟩,c,s) m hm R.q_pos ht
  intro ω
  obtain ⟨b, hb⟩ := hf (R.gridNoise cap m ω)
  rcases hb with hb | hb
  · refine ⟨b + R.q, Or.inl ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω d hdc c s r, hb]
    ring
  · refine ⟨b - R.q, Or.inr ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω d hdc c s r, hb]
    ring

lemma listedPair_probability (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k)
    (L i j : ℕ) (hi : i ∈ R.recentNames C L) (hj : j ∈ R.recentNames C L) (hne : i ≠ j)
    (v : M.Point J root) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.listedAtom p (R.gridNoise cap m ω) C L i v).value -
        (R.listedAtom p (R.gridNoise cap m ω) C L j v).value| ≤ t) ≤
      (2 * t + R.q / m) / R.q := by
  have hn : R.chainName C (R.representative C L i hi) ≠
      R.chainName C (R.representative C L j hj) := by
    simpa only [R.representative_name] using hne
  simpa only [listedAtom, dite_eq_left hi, dite_eq_left hj] using
    R.chainPair_probability p C _ _ hn v cap m hk hm ht

end RadialTree


end Point

end Model
end Columns
end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Point.RadialTree
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : RadialTree (M := M) (J := J) (root := root))

/-- Comparison with a fixed old field uses the current atom's own offset, not
an unjustified independence assertion about its inherited intercept. -/
lemma chainConstant_probability (p : M.Point J root → ℝ) {k : ℕ}
    (C : R.Node k) (u : ChainIndex k) (v : M.Point J root) (c : ℝ)
    (cap m : ℕ) (hk : k < cap) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.chainAtom p (R.gridNoise cap m ω) C u v).value-c| ≤ t) ≤
      (2*t+R.q/m)/R.q := by
  let D := R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)
  have hd : u.1.val < cap := (Nat.le_of_lt_succ u.1.isLt).trans_lt hk
  apply FiniteRandom.coordinate_probability
    (⟨u.1,hd⟩,(R.portalAt D u.2.1).column,u.2.2) m hm R.q_pos ht
  intro ω
  by_cases hs : u.2.2 = 1
  · refine ⟨R.atomIntercept p (R.gridNoise cap m ω) D u.2.1 u.2.2 v-c-R.q,Or.inr ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω u.1 hd (R.portalAt D u.2.1).column u.2.2 r]
    dsimp only [chainAtom]
    rw [R.nodeAtom_replace_self p _ D _ _ v _,ite_eq_left hs]
    ring
  · refine ⟨R.atomIntercept p (R.gridNoise cap m ω) D u.2.1 u.2.2 v-c+R.q,Or.inl ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω u.1 hd (R.portalAt D u.2.1).column u.2.2 r]
    dsimp only [chainAtom]
    rw [R.nodeAtom_replace_self p _ D _ _ v _,ite_eq_right hs]
    ring

lemma listedConstant_probability (p : M.Point J root → ℝ) {k : ℕ}
    (C : R.Node k) (L i : ℕ) (hi : i ∈ R.recentNames C L)
    (v : M.Point J root) (c : ℝ) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.listedAtom p (R.gridNoise cap m ω) C L i v).value-c| ≤ t) ≤
      (2*t+R.q/m)/R.q := by
  simpa only [listedAtom,dite_eq_left hi] using
    R.chainConstant_probability p C (R.representative C L i hi) v c cap m hk hm ht

end PlanarL1.Columns.Model.Point.RadialTree




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainCells
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model

open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

namespace MainCell
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

/-- The literal main test: the proposal is the actual interpolated compact
frontier envelope, and failure to raise constructs an attaining path in J. -/
lemma raise_or_descent (hJ : IsCompact J) (v w : M.Point J root)
    (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hw : w.column ∈ ColumnOrder.componentColumns C)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ (1:ℝ)/100)
    (hζ : R.ζ = ε/100) (hδ : R.δ = (ε/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (H : M.Point J root → ℝ) (hH : old F hJI v+2 ≤ H w)
    (hlow : q+(1:ℝ)/100000+2*R.a < dist R.base (w.withHeight R.base.height R.base.inBand))
    (hupp : dist R.base (w.withHeight R.base.height R.base.inBand) < q+(1:ℝ)/1000-(1:ℝ)/100000-2*R.a) :
    old F hJI w+2*(ε/1000) <
        Clipping.clip (old F hJI) (proposal F hJI R q C v α (ε/1000)) H w ∨
      Nonempty (F.BandDescent J (w.widen hJI) ε) := by
  have hthin : R.a ≤ (1/1000:ℝ)/1000 := by
    have hb := R.width_bound
    have hm := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
    rw [hδ] at hb hm
    nlinarith
  have hvw := abs_le.mp (variation F hJI R q C hthin v w hv hw)
  have hrad : ∀ z ∈ boundary R q C, (0.00001:ℝ) ≤ dist w z ∧ dist w z ≤ 0.02 := by
    intro z hz
    have hl := R.base.radial_frontier_distance w z R.base.inBand R.half_width C hlow hupp hz
    have hu := R.base.radial_cell_diameter R.closed_band R.base.inBand R.width_pos hthin
      R.half_width C w z hw hz.1
    constructor <;> linarith
  have hraise := Clipping.raise_or_descending_endpoint (H := H) (boundary_compact R q C hJ)
    (old_lipschitz F hJI R).continuous.continuousOn w (old F hJI v+1) R.ζ (ε/1000) ε
    (proposal_accuracy F hJI R q C hJ v w hα (by linarith) hδ).1
    (by linarith) (by linarith) hrad R.zeta_pos.le (by rw [hζ]; linarith)
  rcases hraise with hh | ⟨z,hz,hlo,hup,hdrop⟩
  · exact Or.inl hh
  · right
    obtain ⟨p,_,hp⟩ := w.exists_shortest R.closed_band z
    refine ⟨{
      start_in := w.inBand
      target := z.widen hJI
      target_in := z.inBand
      path := p
      shortest := ?_
      lower := ?_
      upper := ?_
      drop := ?_ }⟩
    · intro p'
      change p.length w.height z.height ≤ p'.length w.height z.height
      rw [hp]
      exact w.distance_le z p'
    · change (1:ℝ)/100000 ≤ p.length w.height z.height
      rw [hp]
      linarith
    · change p.length w.height z.height ≤ (1:ℝ)/50
      rw [hp]
      linarith
    · change old F hJI z ≤ old F hJI w-p.length w.height z.height+ε
      rwa [hp]

end MainCell
end PlanarL1.Columns.Model


end

section

namespace PlanarL1.Columns.Model.Point
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}

/-- A shortest path leaving any full-column cell meets its actual frontier
before using more than its total length. No shape/convexity of the cell is used. -/
lemma near_frontier_of_not_mem (hJ : IsClosed J) (S : Set (Fin n))
    (x y : M.Point J root) (hx : x.column ∈ S) (hy : y.column ∉ S) :
    ∃ z : M.Point J root, z.column ∈ frontier (M := M) (J := J) S ∧ dist x z ≤ dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hJ y
  obtain ⟨u,v,T,hT,hs,hu,hv,q,r,hqr⟩ :=
    p.crosses_set Sᶜ (by simpa only [Set.mem_compl_iff,not_not] using hx) hy x.height y.height
  have huS : u ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hu
  let z : M.Point J root := ⟨u,T,hT,x.reachable.trans q.word.reachable⟩
  refine ⟨z,⟨huS,v,⟨T,hT,hs⟩,hv⟩,?_⟩
  have hd := x.distance_le z q
  change dist x z ≤ q.length x.height T at hd
  rw [hp] at hqr
  linarith [r.length_nonneg T y.height]

end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.MainCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

lemma shield_lipschitz (v : M.Point J root) (β lo : ℝ) :
    LipschitzWith (replacementConstant R)
      (fun z : M.Point J root => Clipping.heightShield lo R.a (old F hJI v) β z.height) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ht := (Clipping.heightShield_lipschitz lo (old F hJI v) β R.width_pos).dist_le_mul x.height y.height
  have hx := x.height_change_le y
  change |x.height-y.height| ≤ dist x y at hx
  change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
  change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at ht
  rw [Real.dist_eq] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_left hx (by positivity [R.width_pos])).trans
    (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma localClipAtom_lipschitz {k : ℕ} (A : R.Node k) (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : ℕ) :
    LipschitzWith (replacementConstant R) (localClipAtom F hJI R q C A v α E β lo i) := by
  apply clipAtom_lipschitz
  · intro i
    apply LipschitzWith.weaken (K := 1) _ (le_max_left _ _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using
      (R.listedAtom_lipschitz (input F hJI R q C v) α A R.lookback i).dist_le_mul x y
  · exact (old_lipschitz F hJI R).weaken (le_max_left _ _)
  · exact shield_lipschitz F hJI R v β lo


lemma localClipPair_probability_lt {k : ℕ} (A : R.Node k) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ clipNames (R.recentNames A R.lookback))
    (hj : j ∈ clipNames (R.recentNames A R.lookback)) (hij : i < j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × Fin (m+1) =>
      |localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo i x-
       localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  have hpos₁ : 0 ≤ (2*t+R.q/m)/R.q := by positivity [R.q_pos]
  have hpos₂ : 0 ≤ (2*t+B/m)/B := by positivity
  by_cases hjlow : j < 2
  · have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst i; subst j
    apply FiniteRandom.prob_prod_bound
    intro ω
    let c := Clipping.heightShield lo R.a (old F hJI v) 0 x.height-old F hJI x
    apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
      ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hpos₁))
    have he : c+B/m*r.val =
        localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo 1 x-
        localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo 0 x := by
      simp only [localClipAtom,clipAtom,reduceCtorEq,ite_true,ite_false,c,Clipping.heightShield]
      ring
    rw [he,abs_sub_comm]
    exact h
  · have hj2 : 2 ≤ j := by omega
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hjS : j-2 ∈ R.recentNames A R.lookback := by
      rcases mem_clipNames.mp hj with h | h | h
      · omega
      · omega
      · exact h.2
    apply FiniteRandom.prob_prod_bound_left
    intro r
    by_cases hi2 : 2 ≤ i
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      have hiS : i-2 ∈ R.recentNames A R.lookback := by
        rcases mem_clipNames.mp hi with h | h | h
        · omega
        · omega
        · exact h.2
      have hp := R.listedPair_probability (input F hJI R q C v) A R.lookback (i-2) (j-2)
        hiS hjS (by omega) x cap m hk hm ht
      apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
        (hp.trans (le_add_of_nonneg_right hpos₂))
      simpa only [localClipAtom,clipAtom,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hj0,ite_eq_right hj1,
        sub_sub_sub_cancel_right] using h
    · let c := if i = 0 then old F hJI x else Clipping.heightShield lo R.a (old F hJI v) (B/m*r.val) x.height
      have hc (ω : Point.RadialTree.GridSample (n := n) cap m) :
          localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo i x = c := by
        by_cases hi0 : i = 0
        · simp only [localClipAtom,clipAtom,ite_eq_left hi0,c]
        · have hi1 : i = 1 := by omega
          simp only [localClipAtom,clipAtom,ite_eq_right hi0,ite_eq_left hi1,c]
      have hp := R.listedConstant_probability (input F hJI R q C v) A R.lookback (j-2)
        hjS x (c+4*E) cap m hk hm ht
      apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
        (hp.trans (le_add_of_nonneg_right hpos₂))
      rw [hc] at h
      have he : (R.listedAtom (input F hJI R q C v) (R.gridNoise cap m ω) A R.lookback (j-2) x).value-(c+4*E) =
          localClipAtom F hJI R q C A v (R.gridNoise cap m ω) E (B/m*r.val) lo j x-c := by
        simp only [localClipAtom,clipAtom,ite_eq_right hj0,ite_eq_right hj1]
        ring
      rw [he,abs_sub_comm]
      exact h

lemma localClipPair_probability {k : ℕ} (A : R.Node k) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ clipNames (R.recentNames A R.lookback))
    (hj : j ∈ clipNames (R.recentNames A R.lookback)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × Fin (m+1) =>
      |localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo i x-
       localClipAtom F hJI R q C A v (R.gridNoise cap m ω.1) E (B/m*ω.2.val) lo j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact localClipPair_probability_lt F hJI R q C A v x E lo B hB cap m hk hm i j hi hj hij ht
  · simpa only [abs_sub_comm] using
      localClipPair_probability_lt F hJI R q C A v x E lo B hB cap m hk hm j i hj hi hji ht


/-- The main clipping part of chart persistence. This is
for the literal interpolated, shifted, height-clipped proposal, including the
old field's retaining branch and inherited names through interpolation layers. -/
lemma namedReplacement_probability (hJ : IsCompact J) (v x : M.Point J root)
    (E lo B : ℝ) (hB : 0 < B) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius)
    (m : ℕ) (hm : 0 < m) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) =>
      ∃ z : M.Point J root, dist x z ≤ ρ ∧
        (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).name ≠
        (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo x).name) ≤
      (6*(R.lookback+1)+2 : ℕ)^2 *
        ((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q +
          (4*(replacementConstant R : ℝ)*ρ+B/m)/B) := by
  classical
  obtain ⟨k,A,hlo,heq⟩ := R.common_formula x hρ hs
  have hk : k < R.depthCap :=
    (R.depth_le_layerDepth x (hlo x (by simpa using hρ))).trans_lt (R.layerDepth_lt_cap x)
  have hlist (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1))
      (z : M.Point J root) (hz : dist x z ≤ ρ) :
      (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).name ∈
        clipNames (R.recentNames A R.lookback) ∧
      (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).value =
        localClipAtom F hJI R q C A v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo
          (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).name z := by
    let p := input F hJI R q C v
    let α := R.gridNoise R.depthCap m ω.1
    have hα := R.gridNoise_bounds R.depthCap m hm ω.1
    have hp := input_lipschitz F hJI R q C hJ v
    have ha : |(R.formula p α k A z).value-p z| ≤ 6*R.δ := by
      rw [← heq p α hα z hz]
      exact R.pasted_accuracy hp hα z
    have hn : (R.pasted p α z).name ∈ R.recentNames A R.lookback := by
      rw [heq p α hα z hz]
      exact R.formula_name_recent hp hα k A z (hlo z hz) ha
    have hv : R.pasted p α z = R.listedAtom p α A R.lookback (R.pasted p α z).name z := by
      rw [heq p α hα z hz]
      exact R.formula_eq_listed hp hα k A z (hlo z hz) ha
    apply namedClip_list
      (fun z => ⟨(R.pasted p α z).name,(R.pasted p α z).value-4*E⟩)
      (fun i z => (R.listedAtom p α A R.lookback i z).value-4*E)
      (old F hJI) (fun z => Clipping.heightShield lo R.a (old F hJI v) (B/m*ω.2.val) z.height)
      (R.recentNames A R.lookback) z hn
    exact congrArg (fun Z : NamedValue => Z.value-4*E) hv
  let b : ℝ := (4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q +
      (4*(replacementConstant R : ℝ)*ρ+B/m)/B
  have hb : 0 ≤ b := by dsimp [b]; positivity [R.q_pos]
  have hF (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1)) :
      LipschitzWith (replacementConstant R)
        (fun z => (namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo z).value) := by
    simpa only [namedReplacement_value] using
      replacement_lipschitz F hJI R q C v (R.gridNoise_bounds _ _ hm ω.1) E (B/m*ω.2.val) lo
  have hp := selection_probability
    (fun ω : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) =>
      namedReplacement F hJI R q C v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo)
    (fun ω => localClipAtom F hJI R q C A v (R.gridNoise R.depthCap m ω.1) E (B/m*ω.2.val) lo)
    (clipNames (R.recentNames A R.lookback)) hF
    (fun ω i _ => localClipAtom_lipschitz F hJI R q C A v _ E _ lo i) x hρ hb hlist
    (fun i hi j hj hij => by
      simpa only [show 2*(2*(replacementConstant R : ℝ)*ρ) = 4*(replacementConstant R : ℝ)*ρ by ring] using
        localClipPair_probability F hJI R q C A v x E lo B hB R.depthCap m hk hm i j hi hj hij
          (t := 2*(replacementConstant R : ℝ)*ρ) (by positivity))
  refine hp.trans ?_
  apply mul_le_mul_of_nonneg_right _ hb
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast (clipNames_card (R.recentNames A R.lookback)).trans
    (Nat.add_le_add_right (R.recentNames_card A R.lookback) 2)


lemma namedReplacement_near_frontier (hJ : IsCompact J) (v x z : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8) (β lo : ℝ)
    (hz : z ∈ boundary R q C) (hd : 2*dist x z < 3*E) :
    namedReplacement F hJI R q C v α E β lo x = ⟨0,old F hJI x⟩ := by
  apply clippedNamed_retains
  change proposal F hJI R q C v α E x < old F hJI x
  have hm := frontier_margin F hJI R q C hJ v hα hE hδ hz
  have hxz := (proposal_lipschitz F hJI R q C v hα E).dist_le_mul x z
  have hs := (old_lipschitz F hJI R).dist_le_mul z x
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hxz hs
  rw [dist_comm z x] at hs
  have hp := (abs_le.mp hxz).2
  have ho := (abs_le.mp hs).2
  linarith

/-- Crossing a main-cell boundary causes no identifier loss at all. This is
exactly why no radial padding error proportional to the band width is needed
in the source persistence bound. -/
lemma namedReplacement_retained_on_touched_ball (hJ : IsCompact J)
    (v x : M.Point J root) {ρ : ℝ} {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8)
    (β lo : ℝ) (hρ : 4*ρ < 3*E)
    (hex : ∃ y : M.Point J root, dist x y ≤ ρ ∧ y.column ∉ ColumnOrder.componentColumns C) :
    ∀ w : M.Point J root, dist x w ≤ ρ → w.column ∈ ColumnOrder.componentColumns C →
      namedReplacement F hJI R q C v α E β lo w = ⟨0,old F hJI w⟩ := by
  intro w hw hwC
  obtain ⟨y,hy,hyC⟩ := hex
  obtain ⟨z,hz,hd⟩ := Point.near_frontier_of_not_mem R.closed_band
    (ColumnOrder.componentColumns C) w y hwC hyC
  apply namedReplacement_near_frontier F hJI R q C hJ v w z hα hE hδ β lo hz
  have ht := dist_triangle w x y
  rw [dist_comm w x] at ht
  linarith

end PlanarL1.Columns.Model.MainCell



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_OrderedState
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BState
variable (S : BState M κ lam Ω μ)

lemma oldValue_eq (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1))
    (h : S.name i H=a) : S.oldValue i H =
      κ*(S.chart a).value lam i ⟨H,by simpa only [h] using S.height_in i H⟩ := by
  subst a
  rfl

end BState
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Execution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1

namespace Execution
attribute [local instance] Classical.propDecidable
variable {α β : Type*}

lemma mean_add (E : Execution α) (f g : α → ℝ) :
    E.mean (fun x => f x+g x)=E.mean f+E.mean g := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [mean,ih,Finset.sum_add_distrib,add_div]

lemma mean_smul (E : Execution α) (c : ℝ) (f : α → ℝ) :
    E.mean (fun x => c*f x)=c*E.mean f := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [mean,ih,← Finset.mul_sum]; ring

lemma mean_bind (E : Execution α) (F : α → Execution β) (f : β → ℝ) :
    (E.bind F).mean f = E.mean (fun x => (F x).mean f) := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp only [bind,mean,ih]

lemma prob_bind (E : Execution α) (F : α → Execution β) (P : β → Prop) :
    (E.bind F).prob P=E.mean (fun x => (F x).prob P) := E.mean_bind F _

lemma prob_nonneg (E : Execution α) (P : α → Prop) : 0 ≤ E.prob P := by
  classical
  exact E.mean_nonneg (by intro x; split_ifs <;> norm_num)

lemma prob_le_one (E : Execution α) (P : α → Prop) : E.prob P ≤ 1 := by
  classical
  simpa only [prob,mean_const] using E.mean_mono (f := fun x => if P x then 1 else 0)
    (g := fun _ => (1:ℝ)) (by intro x; split_ifs <;> norm_num)

lemma prob_compl (E : Execution α) (P : α → Prop) : E.prob (fun x => ¬P x)=1-E.prob P := by
  classical
  have h : E.prob P+E.prob (fun x => ¬P x)=1 := by
    unfold prob
    rw [← mean_add]
    calc
      _=E.mean (fun _ => 1) := by
        congr 1
        funext x
        by_cases hx : P x <;> simp [hx]
      _=1 := E.mean_const 1
  linarith

lemma prob_mono (E : Execution α) {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    E.prob P ≤ E.prob Q := by
  classical
  apply E.mean_mono
  intro x
  by_cases hp : P x
  · simp [hp,h x hp]
  · simp only [hp, ite_false]; split_ifs <;> norm_num

lemma mean_lower_of_event (E : Execution α) {P : α → Prop} {f : α → ℝ} {c : ℝ}
    (hf : ∀ x, 0 ≤ f x) (h : ∀ x, P x → c ≤ f x) : c*E.prob P ≤ E.mean f := by
  classical
  rw [prob,← mean_smul]
  apply E.mean_mono
  intro x
  by_cases hx : P x <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  · exact h x hx
  · exact hf x

/-- Conditional failure bounds compose even when later grids and cell choices
are chosen using the entire previous history. -/
lemma conditional_loss (E : Execution α) (F : α → Execution β)
    (P : α → Prop) (Q : β → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, P x → (F x).prob (fun y => ¬Q y) ≤ ε) :
    (E.bind F).prob (fun y => ¬Q y) ≤ E.prob (fun x => ¬P x)+ε := by
  classical
  rw [prob_bind]
  calc
    _ ≤ E.mean (fun x => (if ¬P x then 1 else 0)+ε) := by
      apply E.mean_mono
      intro x
      by_cases hx : P x
      · simpa only [hx,not_true_eq_false,ite_false,zero_add] using h x hx
      · simpa only [hx,not_false_eq_true,ite_true] using (F x).prob_le_one (fun y => ¬Q y) |>.trans (le_add_of_nonneg_right hε)
    _ = _ := by
      rw [mean_add,mean_const]
      unfold prob
      congr 2
      funext x
      by_cases hx : P x <;> simp [hx]

lemma conditional_success (E : Execution α) (F : α → Execution β)
    (P : α → Prop) (Q : β → Prop) {p : ℝ}
    (h : ∀ x, P x → p ≤ (F x).prob Q) :
    p*E.prob P ≤ (E.bind F).prob Q := by
  rw [prob_bind]
  exact E.mean_lower_of_event (fun x => (F x).prob_nonneg Q) h

end Execution
end PlanarL1

namespace PlanarL1.Execution
variable {α β ι : Type*}

lemma mean_uniform [Fintype α] [Nonempty α] (f : α → ℝ) :
    (uniform (α := α)).mean f=(∑ x, f x)/Fintype.card α := by
  classical
  unfold uniform
  simp only [mean]
  have he : (∑ i : Fin (Fintype.card α-1+1), f (((finCongr
    (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance))).trans
      (Fintype.equivFin α).symm) i))=∑ x, f x := Equiv.sum_comp _ _
  rw [he]
  have h : 0 < Fintype.card α := Fintype.card_pos
  have hc : (↑(Fintype.card α-1):ℝ)+1=Fintype.card α := by
    exact_mod_cast Nat.sub_add_cancel h
  rw [hc]

lemma prob_uniform [Fintype α] [Nonempty α] (P : α → Prop) :
    (uniform (α := α)).prob P=FiniteRandom.prob P := by
  classical
  rw [prob,mean_uniform]
  unfold FiniteRandom.prob
  congr 1
  simp only [Finset.sum_boole,FiniteRandom.event]

end PlanarL1.Execution


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Tiling
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.FiniteRandom
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma integer_interval_count (s : Finset ℤ) {step t : ℝ} (hs : 0 < step)
    (ht : 0≤t) (c : ℝ) (hbound : ∀ i ∈ s, |c-step*i|≤t) :
    ((s.card:ℝ)-1)*step ≤ 2*t := by
  classical
  by_cases hn : s.Nonempty
  · let a := s.min' hn
    let b := s.max' hn
    have ha : a ∈ s := s.min'_mem hn
    have hb : b ∈ s := s.max'_mem hn
    have hab : a≤b := s.min'_le b hb
    have hc := Finset.card_le_card (show s ⊆ Finset.Icc a b from
      fun i hi => Finset.mem_Icc.mpr ⟨s.min'_le i hi,s.le_max' i hi⟩)
    have hd : (s.card:ℝ) ≤ (b:ℝ)-a+1 := by
      rw [Int.card_Icc] at hc
      have he : 0≤b+1-a := by omega
      have he' : ((b+1-a).toNat:ℤ)=b+1-a := Int.toNat_of_nonneg he
      have hh : (s.card:ℤ)≤b+1-a := by omega
      have hh' : (s.card:ℝ)≤(b:ℝ)+1-a := by exact_mod_cast hh
      linarith
    have hx := abs_le.mp (hbound a ha)
    have hy := abs_le.mp (hbound b hb)
    have hh := mul_le_mul_of_nonneg_right hd hs.le
    nlinarith
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_sub,neg_mul,one_mul]
    linarith

/-- Uniformly shifting a periodic tiling has its true one-dimensional bound.
The extra two grid points cover both endpoints, independently of the band index. -/
lemma periodic_probability (m : ℕ) (hm : 0 < m) {a t : ℝ} (ha : 0<a)
    (ht : 0≤t) (h : ℝ) :
    prob (fun i : Fin (m+1) => Tiling.NearBoundary a (a/m*i.val) h t) ≤
      (2*t+2*a/m)/a := by
  classical
  let A := event (fun i : Fin (m+1) => Tiling.NearBoundary a (a/m*i.val) h t)
  let B := A.erase (Fin.last m)
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hmI : (0:ℤ)< m := by exact_mod_cast hm
  have hb (i : B) : Tiling.NearBoundary a (a/m*i.val.val) h t :=
    (mem_event _ i.val).mp (Finset.mem_of_mem_erase i.property)
  choose k hk using hb
  let f (i : B) : ℤ := (m:ℤ)*k i+i.val.val
  have hlt (i : B) : (i.val.val:ℤ)< m := by
    have hn : i.val ≠ Fin.last m := (Finset.mem_erase.mp i.property).1
    have hv : i.val.val≠m := fun he => hn (Fin.ext he)
    exact_mod_cast (show i.val.val< m by omega)
  have hf : Function.Injective f := by
    intro i j he
    have hi := congrArg (fun z : ℤ => z % (m:ℤ)) he
    have hei (u : B) : f u % (m:ℤ) = u.val.val := by
      dsimp [f]
      rw [Int.add_emod,Int.mul_emod]
      simp only [Int.emod_self,zero_mul,Int.zero_emod,zero_add]
      rw [Int.emod_eq_of_lt (by positivity) (hlt u)]
      exact Int.emod_eq_of_lt (by positivity) (hlt u)
    rw [hei i,hei j] at hi
    exact Subtype.ext (Fin.ext (by exact_mod_cast hi))
  let S := B.attach.image f
  have hcard : S.card=B.card := by rw [Finset.card_image_of_injective _ hf,Finset.card_attach]
  have hcount := integer_interval_count S (div_pos ha hmR) ht h (by
    rintro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    have eqn : a/m*(f i:ℝ)=a/m*i.val.val+(k i:ℝ)*a := by
      dsimp [f]
      push_cast
      field_simp
      ring
    rw [eqn]
    exact hk i)
  have hAB : A.card≤B.card+1 :=
    (Finset.card_le_card (show A ⊆ insert (Fin.last m) B from by
      intro i hi
      by_cases he : i=Fin.last m
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he,hi⟩)))).trans
        (Finset.card_insert_le _ _)
  have hAB' : (A.card:ℝ)≤B.card+1 := by exact_mod_cast hAB
  rw [hcard] at hcount
  have hs : 0<a/m := div_pos ha hmR
  have hfinal : (A.card:ℝ)*(a/m)≤2*t+2*(a/m) := by nlinarith
  have hcoef : a/m*(m:ℝ)=a := div_mul_cancel₀ a (ne_of_gt hmR)
  have hfinal' := mul_le_mul_of_nonneg_right hfinal hmR.le
  rw [mul_assoc,hcoef] at hfinal'
  have hnonneg : 0≤(2*t+2*a/m)/a := by positivity
  change (A.card:ℝ)/(Fintype.card (Fin (m+1)):ℝ) ≤ _
  rw [Fintype.card_fin]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(m+1:ℕ))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  push_cast
  have he : 2*t+2*(a/(m:ℝ))=2*t+2*a/m := by ring
  rw [he] at hfinal'
  exact hfinal'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end PlanarL1.FiniteRandom

end


section

namespace PlanarL1.Tiling

lemma NearBoundary.mono {a q h s t : ℝ} (hm : s≤t) :
    NearBoundary a q h s → NearBoundary a q h t := fun ⟨k,hk⟩ => ⟨k,hk.trans hm⟩

lemma NearBoundary.perturb {a q h x t : ℝ} (hn : NearBoundary a q x t) :
    NearBoundary a q h (t+|x-h|) := by
  obtain ⟨k,hk⟩ := hn
  refine ⟨k,?_⟩
  have ht := abs_sub_le h x (q+k*a)
  rw [abs_sub_comm h x] at ht
  linarith

lemma padded_pair {a q h x t e : ℝ} (ha : 0<a) (he : |x-h|≤e)
    (hn : ¬NearBoundary a q h (t+e)) : Padded a q h t ∧ Padded a q x t := by
  have he0 : 0≤e := (abs_nonneg _).trans he
  exact ⟨padded_of_avoid ha (fun hh => hn (hh.mono (by linarith))),
    padded_of_avoid ha (fun hh => hn (hh.perturb.mono (by linarith)))⟩

end PlanarL1.Tiling

namespace PlanarL1.FiniteRandom

lemma prob_or_le {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) :
    prob (fun ω => P ω ∨ Q ω)≤prob P+prob Q := by
  classical
  have h := prob_union_bound (Finset.univ : Finset Bool) (fun b => if b then P else Q)
  simpa only [Finset.mem_univ,true_and,Bool.exists_bool,Bool.false_eq_true,ite_false,ite_true,
    Fintype.sum_bool,or_comm] using h

lemma prob_eval_bound {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (i : I) (P : Ω → Prop) {b : ℝ} (h : prob P≤b) :
    prob (fun ω : I → Ω => P (ω i))≤b := by
  classical
  apply prob_update_bound i
  intro α
  simpa only [Function.update_self] using h

end PlanarL1.FiniteRandom

namespace PlanarL1.Tiling
open Parameters FiniteRandom

/-- The two endpoint height tests use one shift, so their failures are bounded
by an enlarged interval, not by a union bound over the vertices or columns. -/
lemma height_pair_probability (m : ℕ) (hm : 10000 ≤ m) {a h x : ℝ} (ha : 0<a)
    (htrim : a₂≤a) (hd : |x-h|≤a₂/10000) :
    prob (fun i : Fin (m+1) => ¬(Padded a (a/m*i.val) h (a/10) ∧
      Padded a (a/m*i.val) x (a/10)))≤21/100 := by
  classical
  have hm0 : 0 < m := by omega
  have hbad : prob (fun i : Fin (m+1) => ¬(Padded a (a/m*i.val) h (a/10) ∧
      Padded a (a/m*i.val) x (a/10))) ≤
      prob (fun i : Fin (m+1) => NearBoundary a (a/m*i.val) h (a/10+a₂/10000)) := by
    apply prob_mono
    intro i hi
    by_contra hh
    exact hi (padded_pair ha hd hh)
  have hp := periodic_probability m hm0 ha (show 0≤a/10+a₂/10000 by have hb := interpolationB.2.1; positivity) h
  apply hbad.trans (hp.trans _)
  have hmR : (10000:ℝ) ≤ m := by exact_mod_cast hm
  have hmesh : a/m≤a/10000 := div_le_div_of_nonneg_left ha.le (by norm_num) hmR
  apply (div_le_iff₀ ha).mpr
  rw [mul_div_assoc]
  linarith

end PlanarL1.Tiling

end


end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainStep
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma contains_named (S : OrdinaryState M κ Ω μ) (i : Fin n) (H : ℝ)
    (a : Fin (S.count+1)) (he : S.name i H=a) : (S.chart a).Contains i H := by
  subst a
  exact ⟨S.height_in i H,S.component_in i H⟩

end OrdinaryState
end PlanarL1.Columns.Model


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
namespace OrdinaryState.MainStep
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

lemma indicator_inside (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (U.patch.apply.activity ω).indicator i H =
      Threshold.chartValue H (κ*(U.data.constant+U.data.orientation*
        MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
          U.noise U.error U.shield_offset U.lo (MainCell.cellPoint U.tree U.phase U.cell i H hi)))
        ((S.labels U.index).lift.value ω) := by
  simp only [Activity.indicator,U.patch_inside ω i H hi,Threshold.active,
    Threshold.chartValue,Threshold.half]

end OrdinaryState.MainStep
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainPersistence
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace OrdinaryState.MainBatch
variable {κ : ℝ} {S : OrdinaryState M κ Ω μ} (B : MainBatch S)
lemma choose_eq {i j : Fin n} {H T : ℝ}
    (he : ∀ q, (B.step q).choose i H=(B.step q).choose j T) :
    B.choose i H=B.choose j T := by
  have h : B.chosen i H=B.chosen j T := by
    funext a
    simp only [chosen,he a.1]
  unfold choose
  simp only [h]

lemma name_eq [SFinite μ] {i j : Fin n} {H T : ℝ}
    (hold : S.name i H=S.name j T) (he : B.choose i H=B.choose j T) :
    B.apply.name i H=B.apply.name j T := by
  dsimp only [apply,OrdinaryState.append,OrdinaryState.lift]
  rw [he,hold]
end OrdinaryState.MainBatch

namespace MainCell
variable {I J : Set ℝ} {root : Fin n} (F : M.Field I 1) (hJI : J ⊆ I)
  (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
  (C : Cell R q)
lemma choose_eq_of_name (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) {i j : Fin n} {H T : ℝ}
    (hi : H ∈ domain R q C i) (hj : T ∈ domain R q C j)
    (hn : (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hi)).name=
      (namedReplacement F hJI R q C v α E β lo (cellPoint R q C j T hj)).name) :
    choose F hJI R q C v α E β lo i H=choose F hJI R q C v α E β lo j T := by
  simp only [choose,dite_eq_left hi,dite_eq_left hj]
  simp only [hn]

lemma choose_none_of_name (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) {i : Fin n} {H : ℝ}
    (hi : H ∈ domain R q C i)
    (hn : (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hi)).name=0) :
    choose F hJI R q C v α E β lo i H=none := by
  simp only [choose,dite_eq_left hi,dite_eq_left hn]
end MainCell
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Tiling
lemma near_band_unique {a q h t H : ℝ} (ha : 0<a) (_ht : 0≤t)
    (hp : Padded a q h t) (hd : |H-h|≤t) {b : ℤ} (hb : H ∈ band a q b) :
    b=index a q h := by
  rcases lt_trichotomy b (index a q h) with hl | he | hu
  · have hbl : (b:ℝ)+1≤(index a q h:ℝ) := by
      exact_mod_cast (show b+1≤ index a q h by omega)
    have hv := mul_le_mul_of_nonneg_right hbl ha.le
    have hlo := hp.1
    change q+(index a q h:ℝ)*a+t<h at hlo
    have hh := hb.2
    change H≤q+((b:ℝ)+1)*a at hh
    have hd' := (abs_le.mp hd).1
    linarith
  · exact he
  · have hbl : (index a q h:ℝ)+1≤(b:ℝ) := by
      exact_mod_cast (show index a q h+1≤b by omega)
    have hv := mul_le_mul_of_nonneg_right hbl ha.le
    have hup := hp.2
    change h<q+((index a q h:ℝ)+1)*a-t at hup
    have hh := hb.1
    change q+(b:ℝ)*a≤H at hh
    have hd' := (abs_le.mp hd).2
    linarith

lemma near_mem_band {a q h t H : ℝ} (_ha : 0<a) (_ht : 0≤t)
    (hp : Padded a q h t) (hd : |H-h|≤t) : H ∈ band a q (index a q h) := by
  change q+(index a q h:ℝ)*a≤H ∧ H≤q+((index a q h:ℝ)+1)*a
  have hlo := hp.1
  have hup := hp.2
  change q+(index a q h:ℝ)*a+t<h at hlo
  change h<q+((index a q h:ℝ)+1)*a-t at hup
  have hd' := abs_le.mp hd
  constructor <;> linarith
end PlanarL1.Tiling

namespace PlanarL1.Columns.Model
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace Point
lemma local_center {J : Set ℝ} {r s : Fin (k+1)}
    (x y : M.Point Set.univ r) (y' : M.Point J s)
    (hy : y'.column=y.column) (_hY : y'.height=y.height) {ρ : ℝ} (hρ : 0≤ρ)
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J) (hd : dist x y≤ρ) :
    ∃ x' : M.Point J s, x'.column=x.column ∧ x'.height=x.height := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_univ y
  obtain ⟨q,_⟩ := p.restrict_of_length x.height y.height x.height ρ hJ (by simpa [hp] using hd)
  have hxJ : x.height ∈ J := hJ _ (by simpa using hρ)
  refine ⟨⟨x.column,x.height,hxJ,?_⟩,rfl,rfl⟩
  exact y'.reachable.trans (hy.symm ▸ q.word.reachable.symm)
end Point
namespace MainFamily
open Parameters
variable (A : Ambient M) {q L U : ℝ}
  (phase : BandComponent (M := M) q L U → ℝ)
  (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
  (hp : Tiling.Padded a₁ q x.height ρ)

include hρ hp
lemma touched_band {c : CellIndex q L U phase} {y : M.Point Set.univ A.root}
    (hy : dist x y≤ρ) (hc : y.height ∈ domain phase c y.column) :
    c.1.1.val=Tiling.index a₁ q x.height := by
  apply Tiling.near_band_unique interpolationA.2.1 hρ hp _ (domain_band phase c hc)
  rw [abs_sub_comm]
  exact (x.height_change_le y).trans hy

lemma touched_envelope {c : CellIndex q L U phase} {y : M.Point Set.univ A.root}
    (hy : dist x y≤ρ) (hc : y.height ∈ domain phase c y.column) :
    ∀ H, |H-x.height|≤ρ → H ∈ BandTrees.band broad (lower q L U c.1.1) := by
  intro H hH
  have he := touched_band A phase x hρ hp hy hc
  have hb := Tiling.near_mem_band interpolationA.2.1 hρ hp hH
  rw [←he] at hb
  change q+(c.1.1.val:ℝ)*a₁≤H ∧ H≤q+(c.1.1.val:ℝ)*a₁+a₁
  dsimp only [Tiling.band,Set.mem_Icc] at hb
  constructor <;> linarith [hb.1,hb.2]

lemma local_center {c : CellIndex q L U phase} {y : M.Point Set.univ A.root}
    (hy : dist x y≤ρ) (hc : y.height ∈ domain phase c y.column) :
    ∃ x' : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2),
      x'.column=x.column ∧ x'.height=x.height :=
  Point.local_center x y (MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 _ _ hc)
    rfl rfl hρ (touched_envelope A phase x hρ hp hy hc) hy

lemma local_ball {c : CellIndex q L U phase}
    (x' : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    (hx : x'.column=x.column) (hX : x'.height=x.height)
    {y : M.Point Set.univ A.root} (hy : dist x y≤ρ)
    (hc : c.1.1.val=Tiling.index a₁ q x.height) :
    ∃ y' : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2),
      y'.column=y.column ∧ y'.height=y.height ∧ dist x' y'=dist x y := by
  apply Point.local_point x y x' hx hX isClosed_univ (Set.subset_univ _) _ hy
  intro H hH
  have hb := Tiling.near_mem_band interpolationA.2.1 hρ hp hH
  rw [←hc] at hb
  change q+(c.1.1.val:ℝ)*a₁≤H ∧ H≤q+(c.1.1.val:ℝ)*a₁+a₁
  dsimp only [Tiling.band,Set.mem_Icc] at hb
  constructor <;> linarith [hb.1,hb.2]
end MainFamily
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace Point
lemma eq_of_coordinates {J : Set ℝ} {r : Fin (k+1)} (x y : M.Point J r)
    (hc : x.column=y.column) (hh : x.height=y.height) : x=y := by
  cases x
  cases y
  cases hc
  cases hh
  rfl
end Point
namespace MainFamily
open Parameters
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hsmall : 4*ρ<3*EA)

include hρ hp hsmall
/-- An actual available main cell does not install an identifier anywhere in a
small padded ball if that ball has a column outside the cell. -/
lemma choose_none_crossed (c : Kept A S phase omega)
    (hex : ∃ y : M.Point Set.univ A.root, dist x y≤ρ ∧
      y.column ∉ ColumnOrder.componentColumns c.val.2.2)
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ) :
    (keptStep A S phase hm omega c).choose z.column z.height=none := by
  let V := keptStep A S phase hm omega c
  change MainCell.choose V.comparison V.sub_old V.tree V.phase V.cell V.anchor
    V.noise V.error V.shield_offset V.lo z.column z.height=none
  by_cases hd : z.height ∈ domain phase c.val z.column
  · obtain ⟨x',hx,hX⟩ := local_center A phase x hρ hp hz hd
    have hb := touched_band A phase x hρ hp hz hd
    obtain ⟨w,hw,hW,hdw⟩ := local_ball A phase x hρ hp x' hx hX hz hb
    have hw' : w=MainCell.cellPoint V.tree V.phase V.cell z.column z.height hd :=
      Point.eq_of_coordinates _ _ hw hW
    obtain ⟨y,hy,hout⟩ := hex
    obtain ⟨y',hy',hY,hdy⟩ := local_ball A phase x hρ hp x' hx hX hy hb
    have hh := MainCell.namedReplacement_retained_on_touched_ball V.comparison V.sub_old
      V.tree V.phase V.cell isCompact_Icc V.anchor x' V.noise_bounds
      interpolationA.1.le (show V.tree.δ=EA/8 by rfl) V.shield_offset V.lo hsmall
      ⟨y',by simpa only [hdy] using hy,by
        change y'.column ∉ ColumnOrder.componentColumns c.val.2.2
        rwa [hy']⟩
      w (by simpa only [hdw] using hz) (by
        rw [hw]
        exact ((MainCell.mem_domain _ _ _).mp hd).1)
    apply MainCell.choose_none_of_name V.comparison V.sub_old V.tree V.phase V.cell
      V.anchor V.noise V.error V.shield_offset V.lo hd
    rw [←hw']
    exact congrArg PlanarL1.Interpolation.NamedValue.name hh
  · exact MainCell.choose_none_outside V.comparison V.sub_old V.tree V.phase V.cell
      V.anchor V.noise V.error V.shield_offset V.lo _ _ hd

/-- If two main cells are seen by the center ball, every cell's chosen name is
none on the ball. This also covers two representatives of the same quotient
point and arbitrarily many touched cells. -/
lemma all_choices_none_crossed (c : CellIndex q L U phase)
    (hc : x.height ∈ domain phase c x.column)
    (hex : ∃ y : M.Point Set.univ A.root, dist x y≤ρ ∧
      y.column ∉ ColumnOrder.componentColumns c.2.2)
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ)
    (d : Kept A S phase omega) :
    (keptStep A S phase hm omega d).choose z.column z.height=none := by
  by_cases hd : z.height ∈ domain phase d.val z.column
  · apply choose_none_crossed A S phase hm omega x hρ hp hsmall d _ z hz
    by_cases he : c=d.val
    · subst c
      exact hex
    · refine ⟨x,by simpa using hρ,?_⟩
      intro hx
      have hb := touched_band A phase x hρ hp hz hd
      have hcband := touched_band A phase x hρ hp (y := x) (by simpa using hρ) hc
      have hband : c.1.1=d.val.1.1 := Subtype.ext (hcband.trans hb.symm)
      have hxd : x.height ∈ domain phase d.val x.column :=
        (MainCell.mem_domain _ _ _).mpr ⟨hx,touched_envelope A phase x hρ hp hz hd
          x.height (by simpa using hρ)⟩
      exact he (unique_in_band phase hband hc hxd)
  · exact MainCell.choose_none_outside
      (keptStep A S phase hm omega d).comparison (keptStep A S phase hm omega d).sub_old
      (tree phase d.val) (radial phase d.val) d.val.2.2 (anchor phase d.val)
      (keptStep A S phase hm omega d).noise EA (keptStep A S phase hm omega d).shield_offset
      (lower q L U d.val.1.1) z.column z.height hd
end MainFamily
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.FiniteRandom
lemma prob_pi_eval_bound {I : Type*} {D : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] (i : I) (P : D i → Prop)
    {b : ℝ} (h : prob P≤b) : prob (fun f : ∀ i, D i => P (f i))≤b := by
  classical
  let e := Equiv.piSplitAt i D
  have he (u : D i × (∀ j : {j // j≠i}, D j.val)) : (e.symm u) i=u.1 :=
    congrArg Prod.fst (e.apply_symm_apply u)
  rw [←prob_equiv e.symm]
  apply prob_prod_bound_left
  intro f
  simpa only [he] using h
end PlanarL1.FiniteRandom

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hsmall : 4*ρ<3*EA)

include hρ hp in
lemma choose_none_other (c : CellIndex q L U phase)
    (hfull : ∀ z : M.Point Set.univ A.root, dist x z≤ρ → z.height ∈ domain phase c z.column)
    (d : Kept A S phase omega) (hne : d.val≠c)
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ) :
    (keptStep A S phase hm omega d).choose z.column z.height=none := by
  apply MainCell.choose_none_outside
  intro hd
  have hd' : z.height ∈ domain phase d.val z.column := hd
  have hb := touched_band A phase x hρ hp hz hd'
  have hcband := touched_band A phase x hρ hp hz (hfull z hz)
  exact hne (unique_in_band phase (Subtype.ext (hb.trans hcband.symm)) hd' (hfull z hz))

include hρ hp hsmall in
lemma result_name_eq [SFinite μ] (c : CellIndex q L U phase)
    (hc : x.height ∈ domain phase c x.column)
    (hcontrol : ∀ hav : Available A S phase c,
      let x' := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 x.column x.height hc
      ∀ z, dist x' z≤ρ →
        sampleName A S phase c hav ((omega c).1,(omega c).2.1) z=
          sampleName A S phase c hav ((omega c).1,(omega c).2.1) x')
    (z : M.Point Set.univ A.root) (hz : dist x z≤ρ)
    (hold : S.name z.column z.height=S.name x.column x.height) :
    (result A S phase hm omega).name z.column z.height=
      (result A S phase hm omega).name x.column x.height := by
  apply OrdinaryState.MainBatch.name_eq _ hold
  apply OrdinaryState.MainBatch.choose_eq
  intro j
  let d : Kept A S phase omega := (Fintype.equivFin (Kept A S phase omega)).symm j
  change (keptStep A S phase hm omega d).choose z.column z.height=
    (keptStep A S phase hm omega d).choose x.column x.height
  by_cases hex : ∃ y : M.Point Set.univ A.root, dist x y≤ρ ∧
      y.column ∉ ColumnOrder.componentColumns c.2.2
  · rw [all_choices_none_crossed A S phase hm omega x hρ hp hsmall c hc hex z hz d,
      all_choices_none_crossed A S phase hm omega x hρ hp hsmall c hc hex x (by simpa using hρ) d]
  · have hfull (y : M.Point Set.univ A.root) (hy : dist x y≤ρ) :
        y.height ∈ domain phase c y.column := by
      apply (MainCell.mem_domain _ _ _).mpr
      refine ⟨?_,?_⟩
      · by_contra hn
        exact hex ⟨y,hy,hn⟩
      · apply touched_envelope A phase x hρ hp (by simpa using hρ) hc
        rw [abs_sub_comm]
        exact (x.height_change_le y).trans hy
    by_cases he : d.val=c
    · subst c
      let V := keptStep A S phase hm omega d
      have hdz := hfull z hz
      apply MainCell.choose_eq_of_name V.comparison V.sub_old V.tree V.phase V.cell V.anchor
        V.noise V.error V.shield_offset V.lo hdz hc
      let x' := MainCell.cellPoint (tree phase d.val) (radial phase d.val) d.val.2.2
        x.column x.height hc
      have hb := touched_band A phase x hρ hp (by simpa using hρ) hc
      obtain ⟨z',hz',hZ,hd⟩ := local_ball A phase x hρ hp x' rfl rfl hz hb
      have hd' : dist x' z'≤ρ := hd.le.trans hz
      have hn := hcontrol d.property.1 z' hd'
      have hzP : z'=MainCell.cellPoint (tree phase d.val) (radial phase d.val) d.val.2.2
          z.column z.height hdz := Point.eq_of_coordinates _ _ hz' hZ
      rw [hzP] at hn
      exact hn
    · rw [choose_none_other A S phase hm omega x hρ hp c hfull d he z hz,
        choose_none_other A S phase hm omega x hρ hp c hfull d he x (by simpa using hρ)]
end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

lemma localLoss_nonneg (c : CellIndex q L U phase) {ρ : ℝ} (hρ : 0≤ρ) (m : ℕ) :
    0≤localLoss phase c ρ m := by
  unfold localLoss
  positivity [(tree phase c).q_pos,interpolationA.1]

lemma sampleName_probability (c : CellIndex q L U phase) (hc : Available A S phase c)
    (x : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    {ρ : ℝ} (hρ : 0≤ρ) (hr : ρ≤(tree phase c).radius) (m : ℕ) (hm : 0 < m) :
    prob (fun omega : Sample phase m => ∃ z, dist x z≤ρ ∧
      sampleName A S phase c hc ((omega c).1,(omega c).2.1) z≠
        sampleName A S phase c hc ((omega c).1,(omega c).2.1) x)≤localLoss phase c ρ m := by
  classical
  apply prob_pi_eval_bound (D := fun d => CellSample phase d m) c
    (fun w => ∃ z, dist x z≤ρ ∧
      sampleName A S phase c hc (w.1,w.2.1) z≠sampleName A S phase c hc (w.1,w.2.1) x)
  let e := Equiv.prodAssoc
    (Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m) (Fin (m+1)) Bool
  rw [←prob_equiv e]
  apply prob_prod_bound_left
  intro b
  exact MainCell.namedReplacement_probability (S.chart (index A S phase c hc)).comparison
    (sub_old A S phase c hc) (tree phase c) (radial phase c) c.2.2 isCompact_Icc
    (anchor phase c) x EA (lower q L U c.1.1) EA interpolationA.1 hρ hr m hm

/-- Chart persistence for the **whole literal main mode**, conditional on the
padded height band. No factor depending on the number of graph cells occurs. -/
lemma persistence_probability [SFinite μ] (x : M.Point Set.univ A.root)
    (c : CellIndex q L U phase) (hc : x.height ∈ domain phase c x.column)
    {ρ : ℝ} (hρ : 0≤ρ) (hp : Tiling.Padded a₁ q x.height ρ)
    (hsmall : 4*ρ<3*EA) (hr : ρ≤(tree phase c).radius)
    (hold : ∀ z : M.Point Set.univ A.root, dist x z≤ρ →
      S.name z.column z.height=S.name x.column x.height)
    (m : ℕ) (hm : 0 < m) :
    prob (fun omega : Sample phase m => ∃ z : M.Point Set.univ A.root, dist x z≤ρ ∧
      (result A S phase hm omega).name z.column z.height≠
        (result A S phase hm omega).name x.column x.height) ≤ localLoss phase c ρ m := by
  classical
  by_cases hav : Available A S phase c
  · let x' := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 x.column x.height hc
    apply (prob_mono (Q := fun omega : Sample phase m => ∃ z, dist x' z≤ρ ∧
      sampleName A S phase c hav ((omega c).1,(omega c).2.1) z≠
        sampleName A S phase c hav ((omega c).1,(omega c).2.1) x') _).trans
      (sampleName_probability A S phase c hav x' hρ hr m hm)
    intro omega hbad
    by_contra hn
    obtain ⟨z,hz,hz'⟩ := hbad
    apply hz'
    apply result_name_eq A S phase hm omega x hρ hp hsmall c hc _ z hz (hold z hz)
    intro hc'
    dsimp only
    intro y hy
    exact not_ne_iff.mp (fun he => hn ⟨y,hy,he⟩)
  · have hzero : prob (fun omega : Sample phase m => ∃ z : M.Point Set.univ A.root,
        dist x z≤ρ ∧ (result A S phase hm omega).name z.column z.height≠
          (result A S phase hm omega).name x.column x.height)≤prob (fun _ : Sample phase m => False) := by
      apply prob_mono
      intro omega ⟨z,hz,hz'⟩
      exact hz' (result_name_eq A S phase hm omega x hρ hp hsmall c hc
        (fun hc' => False.elim (hav hc')) z hz (hold z hz))
    rw [prob_false] at hzero
    exact hzero.trans (localLoss_nonneg phase c hρ m)
end PlanarL1.Columns.Model.MainFamily

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryCells
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.SecondaryCell
open scoped NNReal
open Metric

variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))

lemma shallow_seed (hζ : R.ζ = (1:ℝ)/10) {radius pc : ℝ} (hr : 0 < radius)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) {w : M.Point J root} (hw : w ∈ S) {p : ℝ}
    (hp : |p-pc| ≤ (60/1000000:ℝ)*radius) :
    p+radius/25 < shallow R S pc radius α w := by
  have h := (abs_le.mp (approx_accuracy R S hζ hδ hα w)).2
  rw [seedDistance_seed S hw,mul_zero,sub_zero] at h
  have hpc := (abs_le.mp hp).2
  dsimp only [shallow]
  linarith

end PlanarL1.Columns.Model.SecondaryCell


end

section



namespace PlanarL1.Columns.Model.SecondaryCell
open Set MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))
variable (old L : M.Point J root → ℝ) (ordinary : Bool)

lemma replacement_seed (hζ : R.ζ = (1:ℝ)/10) {pc radius αo αh lo : ℝ}
    (hr : 0 < radius) (hrsmall : radius ≤ (1:ℝ)/100) (hαo : 0 ≤ αo) (hαh : 0 ≤ αh)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {w : M.Point J root} (hw : w ∈ S) (hp : |old w-pc| ≤ (60/1000000:ℝ)*radius)
    (hL : ordinary = true → |L w-pc| ≤ (10/1000000:ℝ)*radius)
    (hl : lo+9*R.a/100 ≤ w.height) (hh : w.height ≤ lo+R.a-9*R.a/100) :
    old w+radius/25 < replacement R S old L ordinary pc radius αo αh lo α w := by
  apply lt_of_lt_of_le _ (le_max_right _ _)
  apply lt_min
  · have hT := shallow_seed R S hζ hr hδ hα hw hp
    cases ordinary with
    | false => exact hT
    | true => exact lt_min hT (Clipping.orderedBranch_seed hr hαo (hL rfl) hp)
  · rw [Clipping.heightShield_plateau R.width_pos hl hh]
    have h := (abs_le.mp hp).2
    linarith

end PlanarL1.Columns.Model.SecondaryCell




end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)

lemma orderedBranch_lipschitz (hL : LipschitzWith 1 L) (pc radius αo : ℝ) :
    LipschitzWith 4 (Clipping.orderedBranch pc radius αo L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hL.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  change |(pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo)| ≤ 4*dist x y
  rw [show (pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo) =
    4*(L x-L y) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  linarith

lemma shield_lipschitz (pc αh lo : ℝ) :
    LipschitzWith (replacementConstant R)
      (fun x : M.Point J root => Clipping.heightShield lo R.a pc αh x.height) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (Clipping.heightShield_lipschitz lo pc αh R.width_pos).dist_le_mul x.height y.height
  have hh := x.height_change_le y
  change |x.height-y.height| ≤ dist x y at hh
  change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
  change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at h
  rw [Real.dist_eq x.height y.height] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hh (by positivity [R.width_pos])).trans
    (mul_le_mul_of_nonneg_right (le_max_right (5:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma localAtom_lipschitz (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    {k : ℕ} (A : R.Node k) (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (i : ℕ) :
    LipschitzWith (replacementConstant R) (localAtom R S old L A pc radius αo αh lo α i) := by
  apply secondaryAtom_lipschitz
  · intro i
    apply LipschitzWith.weaken _ (show (1:ℝ≥0) ≤ replacementConstant R from
      (by norm_num : (1:ℝ≥0) ≤ 5).trans (le_max_left _ _))
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_left] using (R.listedAtom_lipschitz (input S) α A R.lookback i).dist_le_mul x y
  · exact hOld.weaken (le_max_left _ _)
  · exact (orderedBranch_lipschitz L hL pc radius αo).weaken
      ((by norm_num : (4:ℝ≥0) ≤ 5).trans (le_max_left _ _))
  · exact shield_lipschitz R pc αh lo

lemma localAtomPair_probability_lt {k : ℕ} (A : R.Node k) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ secondaryNames (R.recentNames A R.lookback))
    (hj : j ∈ secondaryNames (R.recentNames A R.lookback)) (hij : i < j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      |localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) i x-
       localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  have hp : 0 ≤ (2*t+R.q/m)/R.q := by positivity [R.q_pos]
  have hq : 0 ≤ (2*t+B/m)/B := by positivity
  by_cases hj1 : j=1
  · have hi0 : i=0 := by omega
    subst i; subst j
    apply FiniteRandom.prob_prod_bound
    intro ω
    apply FiniteRandom.prob_prod_bound
    intro r
    let c := Clipping.heightShield lo R.a pc 0 x.height-old x
    apply (FiniteRandom.prob_mono (fun s h => ?_)).trans
      ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
    have he : c+B/m*s.val =
        localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 1 x-
        localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 0 x := by
      simp only [localAtom,secondaryAtom, reduceCtorEq,ite_true,ite_false,c,Clipping.heightShield]
      ring
    rw [he,abs_sub_comm]
    exact h
  · by_cases hi1 : i=1
    · subst i
      have hj0 : j ≠ 0 := by omega
      apply FiniteRandom.prob_prod_bound
      intro ω
      apply FiniteRandom.prob_prod_bound
      intro r
      let c := Clipping.heightShield lo R.a pc 0 x.height-
        localAtom R S old L A pc radius (B/m*r.val) 0 lo (R.gridNoise cap m ω) j x
      apply (FiniteRandom.prob_mono (fun s h => ?_)).trans
        ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
      have he : c+B/m*s.val =
          localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 1 x-
          localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) j x := by
        simp only [localAtom,secondaryAtom, reduceCtorEq,ite_true,ite_false,ite_eq_right hj0,ite_eq_right hj1,c,Clipping.heightShield]
        split_ifs <;> ring
      rwa [he]
    · by_cases hj2 : j=2
      · have hi0 : i=0 := by omega
        subst i; subst j
        apply FiniteRandom.prob_prod_bound
        intro ω
        apply FiniteRandom.prob_prod_bound_left
        intro s
        let c := Clipping.orderedBranch pc radius 0 L x-old x
        apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
          ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
        have he : c+B/m*r.val =
            localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 2 x-
            localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 0 x := by
          simp only [localAtom,secondaryAtom, reduceCtorEq, show (2:ℕ) ≠ 1 by decide,ite_true,ite_false,c,Clipping.orderedBranch]
          ring
        rw [he,abs_sub_comm]
        exact h
      · have hj3 : 3 ≤ j := by omega
        have hj0 : j ≠ 0 := by omega
        have hjS : j-3 ∈ R.recentNames A R.lookback := by
          rcases mem_secondaryNames.mp hj with h | h | h | h
          · omega
          · exact (hj1 h).elim
          · exact (hj2 h).elim
          · exact h.2
        by_cases hi2 : i=2
        · subst i
          apply FiniteRandom.prob_prod_bound
          intro ω
          apply FiniteRandom.prob_prod_bound_left
          intro s
          let c := Clipping.orderedBranch pc radius 0 L x-
            (pc+radius/20-(R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (j-3) x).value)
          apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
            ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
          have he : c+B/m*r.val =
              localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 2 x-
              localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) j x := by
            simp only [localAtom,secondaryAtom, reduceCtorEq, show (2:ℕ) ≠ 1 by decide,ite_true,ite_false,ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2,c,Clipping.orderedBranch]
            ring
          rwa [he]
        · by_cases hi0 : i=0
          · subst i
            apply FiniteRandom.prob_prod_bound_left
            intro rs
            apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
              ((R.listedConstant_probability (input S) A R.lookback (j-3) hjS x
                (pc+radius/20-old x) cap m hk hm ht).trans (le_add_of_nonneg_right hq))
            have he : (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (j-3) x).value-
                (pc+radius/20-old x) =
              localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) 0 x-
              localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) j x := by
              simp only [localAtom,secondaryAtom, reduceCtorEq,ite_true,ite_false,ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2]
              ring
            rwa [he]
          · have hiS : i-3 ∈ R.recentNames A R.lookback := by
              rcases mem_secondaryNames.mp hi with h | h | h | h
              · exact (hi0 h).elim
              · exact (hi1 h).elim
              · exact (hi2 h).elim
              · exact h.2
            have hi3 : 3 ≤ i := by omega
            have hneq : i-3 ≠ j-3 := by omega
            apply FiniteRandom.prob_prod_bound_left
            intro rs
            apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
              ((R.listedPair_probability (input S) A R.lookback (i-3) (j-3) hiS hjS hneq x cap m hk hm ht).trans
                (le_add_of_nonneg_right hq))
            have he :
                localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) i x-
                localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) j x =
                (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (j-3) x).value-
                (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (i-3) x).value := by
              simp only [localAtom,secondaryAtom,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2]
              ring
            rw [he,abs_sub_comm] at h
            exact h


lemma localAtomPair_probability {k : ℕ} (A : R.Node k) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ secondaryNames (R.recentNames A R.lookback))
    (hj : j ∈ secondaryNames (R.recentNames A R.lookback)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      |localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) i x-
       localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact localAtomPair_probability_lt R S old L A x pc radius lo B hB cap m hk hm i j hi hj hij ht
  · simpa only [abs_sub_comm] using
      localAtomPair_probability_lt R S old L A x pc radius lo B hB cap m hk hm j i hj hi hji ht

end PlanarL1.Columns.Model.SecondaryCell



end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)

include R in
/-- When a small ball meets the complement of the seed-ball domain, every
inside point is close to its actual distance frontier. -/
lemma near_seed_frontier (x y z : M.Point J root) {ρ radius : ℝ}
    (hy : dist x y ≤ ρ) (hz : dist x z ≤ ρ)
    (hout : radius ≤ seedDistance S y) (hin : seedDistance S z ≤ radius) :
    ∃ w : M.Point J root, seedDistance S w=radius ∧ dist z w ≤ 2*ρ := by
  obtain ⟨w,hw,hd⟩ := Point.intermediate_between (seedDistance S) (seedDistance_lipschitz S)
    R.closed_band R.interval_band z y hin hout
  refine ⟨w,hw,?_⟩
  have hzy : dist z y ≤ 2*ρ := by linarith [dist_triangle z x y,dist_comm z x]
  linarith [dist_nonneg (x := w) (y := y)]

/-- The .199R spatial margin defeats the total 4+5 scalar slopes. Consequently
an entire ball touching outside is unchanged, without paying the much larger
height-shield Lipschitz constant. -/
lemma replacement_boundary_ball (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    (hL : LipschitzWith 1 L) (hζ : R.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (αh lo : ℝ) (x y : M.Point J root) {ρ : ℝ}
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*radius)
    (hy : dist x y ≤ ρ) (hout : radius ≤ seedDistance S y)
    (z : M.Point J root) (hz : dist x z ≤ ρ) (hin : seedDistance S z ≤ radius) :
    replacement R S old L ordinary pc radius αo αh lo α z = old z := by
  obtain ⟨w,hw,hd⟩ := near_seed_frontier R S x y z hy hz hout hin
  have hb := spatial_boundary R S old L ordinary hS hζ hr hαo hδ hα hord hadmit hw
  have hs := (spatial_lipschitz R S L ordinary pc radius αo hα hL).dist_le_mul z w
  have ho := hOld.dist_le_mul z w
  rw [Real.dist_eq] at hs ho
  change |spatial R S L ordinary pc radius αo α z-spatial R S L ordinary pc radius αo α w| ≤ 4*dist z w at hs
  change |old z-old w| ≤ 5*dist z w at ho
  have hsz := (abs_le.mp hs).2
  have hoz := (abs_le.mp ho).1
  apply max_eq_left
  exact (min_le_left _ _).trans (by linarith)

end PlanarL1.Columns.Model.SecondaryCell



end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ)

lemma localAtomConstant_probability {k : ℕ} (A : R.Node k) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i : ℕ) (hi : i ∈ secondaryNames (R.recentNames A R.lookback)) (hi0 : i ≠ 0)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      |localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) i x-c| ≤ t) ≤
      (2*t+R.q/m)/R.q+(2*t+B/m)/B := by
  have hp : 0 ≤ (2*t+R.q/m)/R.q := by positivity [R.q_pos]
  have hq : 0 ≤ (2*t+B/m)/B := by positivity
  by_cases hi1 : i=1
  · subst i
    apply FiniteRandom.prob_prod_bound
    intro ω
    apply FiniteRandom.prob_prod_bound
    intro r
    let d := Clipping.heightShield lo R.a pc 0 x.height-c
    apply (FiniteRandom.prob_mono (fun s h => ?_)).trans
      ((FiniteRandom.grid_probability m hm hB ht d).trans (le_add_of_nonneg_left hp))
    have he : d+B/m*s.val =
        localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 1 x-c := by
      simp only [localAtom,secondaryAtom,reduceCtorEq,ite_true,ite_false,d,Clipping.heightShield]
      ring
    rwa [he]
  · by_cases hi2 : i=2
    · subst i
      apply FiniteRandom.prob_prod_bound
      intro ω
      apply FiniteRandom.prob_prod_bound_left
      intro s
      let d := Clipping.orderedBranch pc radius 0 L x-c
      apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
        ((FiniteRandom.grid_probability m hm hB ht d).trans (le_add_of_nonneg_left hp))
      have he : d+B/m*r.val =
          localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 2 x-c := by
        simp only [localAtom,secondaryAtom,reduceCtorEq,show (2:ℕ) ≠ 1 by decide,
          ite_true,ite_false,d,Clipping.orderedBranch]
        ring
      rwa [he]
    · have hiS : i-3 ∈ R.recentNames A R.lookback := by
        rcases mem_secondaryNames.mp hi with h | h | h | h
        · exact (hi0 h).elim
        · exact (hi1 h).elim
        · exact (hi2 h).elim
        · exact h.2
      apply FiniteRandom.prob_prod_bound_left
      intro rs
      apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
        ((R.listedConstant_probability (input S) A R.lookback (i-3) hiS x
          (pc+radius/20-c) cap m hk hm ht).trans (le_add_of_nonneg_right hq))
      have he : (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (i-3) x).value-(pc+radius/20-c) =
          -(localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) i x-c) := by
        simp only [localAtom,secondaryAtom,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2]
        ring
      rwa [he,abs_neg]

/-- All seed groups may use the same geometric radial hierarchy. The hierarchy
and the whole local list are chosen before their independent samples. -/
lemma namedReplacement_local_list (hζ : R.ζ = (1:ℝ)/10)
    {k : ℕ} (A : R.Node k) (x : M.Point J root) {ρ : ℝ}
    (hlo : ∀ z : M.Point J root, dist x z ≤ ρ →
      (k:ℝ)*R.δ ≤ dist R.base (z.withHeight R.base.height R.base.inBand))
    (heq : ∀ (p : M.Point J root → ℝ) (α : Point.RadialTree.Noise (n := n)),
      R.NoiseBounds α → ∀ z : M.Point J root, dist x z ≤ ρ →
        R.pasted p α z = R.formula p α k A z)
    (ordinary : Bool) (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (hα : R.NoiseBounds α)
    (z : M.Point J root) (hz : dist x z ≤ ρ) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α z).name ∈
        secondaryNames (R.recentNames A R.lookback) ∧
      (namedReplacement R S old L ordinary pc radius αo αh lo α z).value =
        localAtom R S old L A pc radius αo αh lo α
          (namedReplacement R S old L ordinary pc radius αo αh lo α z).name z := by
  have hp := input_lipschitz R S hζ
  have ha : |(R.formula (input S) α k A z).value-input S z| ≤ 6*R.δ := by
    rw [← heq (input S) α hα z hz]
    exact R.pasted_accuracy hp hα z
  have hn : (R.pasted (input S) α z).name ∈ R.recentNames A R.lookback := by
    rw [heq (input S) α hα z hz]
    exact R.formula_name_recent hp hα k A z (hlo z hz) ha
  have hv : R.pasted (input S) α z = R.listedAtom (input S) α A R.lookback (R.pasted (input S) α z).name z := by
    rw [heq (input S) α hα z hz]
    exact R.formula_eq_listed hp hα k A z (hlo z hz) ha
  apply secondaryNamed_list
    (fun z => ⟨(R.pasted (input S) α z).name,pc+radius/20-(R.pasted (input S) α z).value⟩)
    (fun i z => pc+radius/20-(R.listedAtom (input S) α A R.lookback i z).value)
    old (Clipping.orderedBranch pc radius αo L)
    (fun z => Clipping.heightShield lo R.a pc αh z.height)
    ordinary (R.recentNames A R.lookback) z hn
  exact congrArg (fun Z : NamedValue => pc+radius/20-Z.value) hv


lemma sampledReplacement_lipschitz (ordinary : Bool)
    (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius lo B : ℝ) (cap m : ℕ) (hm : 0 < m)
    (ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1))) :
    LipschitzWith (replacementConstant R) (fun z =>
      (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val)
        (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) z).value) := by
  simp only [namedReplacement_value]
  exact replacement_lipschitz R S old L ordinary hOld hL _ _ _ _ _
    (R.gridNoise_bounds cap m hm ω.1)

end PlanarL1.Columns.Model.SecondaryCell



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryFamily
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma support_seed_near (positive : Bool) (C : G.Component)
    (ho : G.data.isOrdinary=true)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) (hx : x ∈ G.allSeeds C) :
    |(G.support positive).field.value x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩-
      G.pc positive|≤10*g := by
  obtain ⟨w,hw,hc,hH⟩ := (G.allSeeds_description C x).mp hx
  have h := (((G.support positive).field.restrict G.sub_old).lipschitz G.broad_closed
    G.broad_root).dist_le_mul w G.representative
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at h
  change |(G.support positive).field.value w.column ⟨w.height,G.sub_old w.inBand⟩-
    (G.support positive).field.value G.representative.column
      ⟨G.representative.height,G.sub_old G.representative.inBand⟩|≤dist w G.representative at h
  rw [(G.support positive).at_center ho] at h
  have he : (G.support positive).field.value w.column ⟨w.height,G.sub_old w.inBand⟩=
      (G.support positive).field.value x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩ := by
    exact congrArg₂ (G.support positive).field.value hc (Subtype.ext hH)
  rw [he] at h
  exact h.trans (G.diameter w hw G.representative G.representative_mem)

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_ScaleHistory
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {r s : Fin n}
namespace Field
lemma ext_value {K : ℝ≥0} {F G : M.Field I K} (h : F.value=G.value) : F=G := by
  cases F
  cases G
  cases h
  rfl
end Field
namespace Point
lemma radialValue_reRoot (h : (M.activeGraph I).Reachable s r) (o : M.Point I r)
    (i : Fin n) (H : I) : (o.reRoot h).radialValue i H=o.radialValue i H := by
  by_cases hi : (M.activeGraph I).Reachable r i
  · have hs := h.trans hi
    simp only [radialValue,dite_eq_left hi,dite_eq_left hs]
    exact dist_coordinates _ _ _ _ rfl rfl rfl rfl
  · have hs : ¬(M.activeGraph I).Reachable s i := fun hs => hi (h.symm.trans hs)
    simp only [radialValue,dite_eq_right hi,dite_eq_right hs]
lemma radialField_reRoot (h : (M.activeGraph I).Reachable s r) (o : M.Point I r) :
    (o.reRoot h).radialField=o.radialField := by
  apply Field.ext_value
  funext i H
  exact radialValue_reRoot h o i H
end Point

namespace Field
variable {F : M.Field I 1} {ε : ℝ}

lemma NoLowCircular.reRoot (h : (M.activeGraph I).Reachable s r)
    {x y : M.Point I r} {j : ℝ} (H : F.NoLowCircular x y J j) :
    F.NoLowCircular (x.reRoot h) (y.reRoot h) J j := by
  intro v b hv hs hn ht hd
  have hd' : dist x (v.reRoot h.symm)≤1 ∨ dist y (v.reRoot h.symm)≤1 := by
    have hx := Point.dist_coordinates (x.reRoot h) v x (v.reRoot h.symm) rfl rfl rfl rfl
    have hy := Point.dist_coordinates (y.reRoot h) v y (v.reRoot h.symm) rfl rfl rfl rfl
    simpa only [hx,hy] using hd
  exact H (v.reRoot h.symm) b hv hs hn ht hd'

lemma constant_no_descent (c ε : ℝ) (hε : ε < (1:ℝ)/100000) (x : M.Point I r) :
    ¬Nonempty ((constant M I c).BandDescent J x ε) := by
  rintro ⟨D⟩
  have hd := D.drop
  change c ≤ c-D.path.length x.height D.target.height+ε at hd
  linarith [D.lower]
end Field
namespace OrdinaryData
/-- Constant ordinary charts cannot survive the genuine descending-path test.
A surviving source is relocated to the bookkeeping root of the current band. -/
lemma source_of_descent (D : OrdinaryData M) {root : Fin n}
    (x : M.Point D.band root) (hx : D.Contains x.column x.height)
    {ε : ℝ} (hε : ε < (1:ℝ)/100000)
    (hd : Nonempty (D.comparison.BandDescent J x ε)) :
    ∃ o : M.Point D.band root, D.comparison=o.radialField := by
  cases ho : D.origin with
  | none =>
    have hh : ¬Nonempty (D.comparison.BandDescent J x ε) := by
      simpa only [comparison,ho] using Field.constant_no_descent (M := M) 0 ε hε x
    exact (hh hd).elim
  | some o =>
    have hr := x.reachable.trans (hx.2 o.1 o.2 ho).symm
    refine ⟨o.2.reRoot hr,?_⟩
    rw [Point.radialField_reRoot]
    simp only [comparison,ho]
end OrdinaryData
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SurvivingSeeds
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.BandTrees
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n) (P : Parameters.Interpolation) (lo : ℝ)
variable (C : Component M P lo)

variable {M P lo C} {width phase : ℝ}

lemma radial_unique (hw : 0<width) {K L : RadialIndex M P lo C width phase} {i : Fin n}
    (hi : i ∈ ColumnOrder.componentColumns K.2) (hj : i ∈ ColumnOrder.componentColumns L.2) : K=L := by
  have he : K.1=L.1 := Subtype.ext (same_level M P lo C hw
    (ColumnOrder.componentColumns_subset K.2 hi) (ColumnOrder.componentColumns_subset L.2 hj))
  obtain ⟨K,Ck⟩ := K
  obtain ⟨L,Cl⟩ := L
  dsimp only at he
  subst L
  have he' : Ck=Cl := same_component hi hj
  subst Cl
  rfl

lemma radial_separated (hw : 0<width) {K L : RadialIndex M P lo C width phase} (hKL : K≠L)
    (x y : M.Point (band P lo) (root M P lo C))
    (hx : x.column ∈ ColumnOrder.componentColumns K.2)
    (hy : y.column ∈ ColumnOrder.componentColumns L.2) {b : ℝ}
    (hl : phase+(K.1.val:ℝ)*width+b+2*P.width <
      dist (base M P lo C) (x.withHeight (middle P lo) (middle_mem P lo)))
    (hu : dist (base M P lo C) (x.withHeight (middle P lo) (middle_mem P lo)) <
      phase+(K.1.val:ℝ)*width+width-b-2*P.width) : b<dist x y := by
  by_contra h
  have hd : dist x y≤b := le_of_not_gt h
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_Icc y
  have hyK := (base M P lo C).radial_cell_padding x y (middle_mem P lo) P.width_pos.le
    (tree M P lo C).half_width K.2 hx hl hu p (hp ▸ hd)
  exact hKL (radial_unique hw hyK hy)

end PlanarL1.Columns.Model.BandTrees

end


section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (lo : ℝ) (C : BandTrees.Component M broad lo) (lo₂ phase : ℝ)

namespace Position
variable {A SA SB lo C lo₂ phase} (p : Position A SA SB lo C lo₂ phase)
lemma contains : (SA.chart p.indexA).Contains p.point.column p.point.height :=
  SA.contains_named _ _ _ (p.commonA.center A (by norm_num))
end Position

variable {A SA SB lo C lo₂ phase}
namespace Seed
variable (w : Seed A SA SB lo C lo₂ phase)
lemma source : ∃ o : M.Point (SA.chart w.indexA).band (BandTrees.root M broad lo C),
    (SA.chart w.indexA).comparison=o.radialField :=
  (SA.chart w.indexA).source_of_descent (w.point.widen w.toPosition.subA)
    w.toPosition.contains (by norm_num [epsilon]) ⟨w.descent⟩
end Seed

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν}
variable {lo : ℝ} {C : BandTrees.Component M broad lo} {lo₂ phase : ℝ}
namespace Seed
variable (w : Seed A SA SB lo C lo₂ phase) {a : Fin (SA.count+1)}
lemma apartAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    1≤dist (w.point.widen hsub) (w.partnerAt he) := by subst a; exact w.apart
lemma closeAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    |(SA.chart a).comparison.eval (w.partnerAt he)-
    (SA.chart a).comparison.eval (w.point.widen hsub)|≤EA := by subst a; exact w.close
lemma retainedAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    (SA.chart a).comparison.NoLowCircular
    (w.point.widen hsub) (w.partnerAt he) (BandTrees.band narrow lo₂) j := by
  subst a; exact w.retained
end Seed

variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)
variable (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)

include hsub in
omit [Fintype W] in
/-- Coincidence of BOTH old names at the center is derived from literal
eligibility. No bound on the pre-existing number of chart identifiers is used. -/
lemma center_names (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (cp : ∀ w, M.Path (BandTrees.band narrow lo₂) c.column (s w).point.column)
    (hp : ∀ w, (cp w).length c.height (s w).point.height≤4*R) (w : W) :
    SA.name c.column c.height=(s w).indexA ∧ SB.name c.column c.height=(s w).indexB := by
  have hd : dist (A.point (s w).point.column (s w).point.height) (A.point c.column c.height)≤5 := by
    rw [dist_comm]
    apply (MainFamily.ambient_dist_le (A := A) c (s w).point).trans
    apply (c.distance_le (s w).point ((cp w).widen hsub)).trans
    have h := hp w
    simp only [Path.length_widen]
    exact h.trans (by norm_num [R])
  exact ⟨(s w).commonA (A.point c.column c.height) hd,
    (s w).commonB (A.point c.column c.height) hd⟩

include hsub in
/-- The concrete restricted packing estimate for retained endpoints: choose
one seed per actual group meeting the narrow ball, rather than assume a
bounded overlap of proposal domains. -/
theorem packing (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (hc : c.height ∈ BandTrees.band narrow lo₂)
    (cp : ∀ w, M.Path (BandTrees.band narrow lo₂) c.column (s w).point.column)
    (hp : ∀ w, (cp w).length c.height (s w).point.height≤4*R)
    (hkey : Function.Injective (key s)) : (Fintype.card W : ℝ)≤2+1600*R/g := by
  classical
  by_cases hn : Nonempty W
  · let w₀ : W := Classical.choice hn
    have sameA (w : W) : (s w).indexA=(s w₀).indexA :=
      (center_names s hsub c cp hp w).1.symm.trans (center_names s hsub c cp hp w₀).1
    have sameB (w : W) : (s w).indexB=(s w₀).indexB :=
      (center_names s hsub c cp hp w).2.symm.trans (center_names s hsub c cp hp w₀).2
    let hKI := (s w₀).toPosition.subA
    obtain ⟨o,ho⟩ := (s w₀).source
    let partner (w : W) := (s w).partnerAt (sameA w)
    have Dx (w : W) : o.radialField.BandDescent (BandTrees.band broad lo)
        ((s w).point.widen hKI) epsilon := by
      rw [← ho]; exact (s w).descentAt (sameA w) hKI
    have Dy (w : W) : o.radialField.BandDescent (BandTrees.band broad lo) (partner w) epsilon := by
      rw [← ho]; exact (s w).partnerDescentAt (sameA w)
    have hf (w : W) : |dist o (partner w)-dist o ((s w).point.widen hKI)|≤EA := by
      have h := (s w).closeAt (sameA w) hKI
      rw [ho] at h
      simpa only [Point.radialField_eval] using h
    have hr (w : W) : o.radialField.NoLowCircular ((s w).point.widen hKI)
        (partner w) (BandTrees.band narrow lo₂) j := by
      rw [← ho]; exact (s w).retainedAt (sameA w) hKI
    have hsep (w v : W) (h : w≠v) : g/100≤dist (s w).point (s v).point := by
      have he : (s w).cell≠(s v).cell := by
        intro he
        apply h (hkey ?_)
        change ((s w).cell,(s w).indexA,(s w).indexB)=((s v).cell,(s v).indexA,(s v).indexB)
        rw [he,sameA w,sameA v,sameB w,sameB v]
      exact (BandTrees.radial_separated (by norm_num [g]) he (s w).point (s v).point
        (s w).cell_mem (s v).cell_mem (s w).lower_pad (s w).upper_pad).le
    have hb := Field.radial_surviving_packing (SA.chart (s w₀).indexA).closed hsub hKI
      (a := a₁) (A := 4*R) (E := EA) (δ := (1:ℝ)/200000) (j := j) (ε := epsilon) (b := g/100)
      (by
        intro H hH T hT
        change lo≤H ∧ H≤lo+a₁ at hH
        change lo≤T ∧ T≤lo+a₁ at hT
        exact abs_le.mpr ⟨by linarith [hH.1,hH.2,hT.1,hT.2],by linarith [hH.1,hH.2,hT.1,hT.2]⟩)
      (by norm_num [R]) (by norm_num [R]) (by norm_num [EA,epsilon])
      (by norm_num [a₁,R]) (by norm_num [R,EA,epsilon,a₁]) (by norm_num [R,a₁])
      (by norm_num [g]) (by norm_num [j,epsilon,a₁,g]) (by norm_num [j,epsilon,a₁])
      o c hc (fun w => (s w).point) partner (fun w => (s w).narrow_height) Dx Dy
      (fun w => (s w).apartAt (sameA w) hKI) hf hr cp hp hsep
    convert hb using 1; norm_num [R,g]
  · have : IsEmpty W := not_nonempty_iff.mp hn
    simp only [Fintype.card_of_isEmpty,Nat.cast_zero]
    norm_num [R,g]

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν}
variable {lo : ℝ} {C : BandTrees.Component M broad lo} {lo₂ phase : ℝ}
variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)

lemma packBound_real : 2+1600*R/g≤(packBound : ℝ) := by
  dsimp only [packBound]
  push_cast
  linarith [Nat.le_ceil (1600*R/g)]

lemma touching_card (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)
    (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (hc : c.height ∈ BandTrees.band narrow lo₂) : Fintype.card (Hits s c)≤packBound := by
  classical
  let w : Hits s c → W := fun q => Classical.choose q.property
  have hw (q : Hits s c) : key s (w q)=q.val.val := (Classical.choose_spec q.property).1
  let p (q : Hits s c) : M.Path (BandTrees.band narrow lo₂) c.column (s (w q)).point.column :=
    Classical.choose (Classical.choose_spec q.property).2
  have hp (q : Hits s c) : (p q).length c.height (s (w q)).point.height≤4*R :=
    Classical.choose_spec (Classical.choose_spec q.property).2
  have hinj : Function.Injective (key (fun q : Hits s c => s (w q))) := by
    intro q q' he
    apply Subtype.ext
    apply Subtype.ext
    exact (hw q).symm.trans (he.trans (hw q'))
  have hb := packing (fun q : Hits s c => s (w q)) hsub c hc p hp hinj
  exact_mod_cast hb.trans packBound_real

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace OrderedData
/-- The literal old-field cutoff controls the fixed ordered part; the
auxiliary field is already 100-Lipschitz by its recorded history. -/
lemma base_close_of_value (D : OrderedData M) {root : Fin (k+1)}
    (x y : M.Point D.band root) (hnear : dist x y≤2)
    (hcut : |D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩|≤R/10000) :
    |D.base.eval x-D.base.eval y|≤R/1000 := by
  have hu := (D.auxiliary.lipschitz D.closed root).dist_le_mul x y
  change |D.auxiliary.eval x-D.auxiliary.eval y|≤100*dist x y at hu
  have haux : |D.auxiliary.eval x-D.auxiliary.eval y|≤200 := by linarith
  have hl : (0:ℝ)≤(SecondaryGeometry.Group.lam:ℝ) := NNReal.coe_nonneg _
  have hnum : R/10000+(SecondaryGeometry.Group.lam:ℝ)*200≤R/1000 := by
    change R/10000+lambda*200≤R/1000
    norm_num [lambda,R]
  have hh := abs_sub (D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩)
    ((SecondaryGeometry.Group.lam:ℝ)*(D.auxiliary.eval x-D.auxiliary.eval y))
  have he : (D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩)-
      (SecondaryGeometry.Group.lam:ℝ)*(D.auxiliary.eval x-D.auxiliary.eval y)=
      D.base.eval x-D.base.eval y := by simp only [value,Field.eval]; ring
  rw [he,abs_mul,abs_of_nonneg hl] at hh
  exact hh.trans ((add_le_add hcut (mul_le_mul_of_nonneg_left haux hl)).trans hnum)
end OrderedData

namespace SecondaryGeometry.Group
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G H : SecondaryGeometry.Group A S)

/-- No admitted endpoint gives the genuine transverse separation. All sphere
witnesses and paths are obtained from the admission failures, not assumed. -/
theorem two_side_of_rejected {D : OrderedData M}
    (he : G.data=.ordered D) (hf : H.data=.ordered D) (hl : H.lower=G.lower)
    (C : G.Component) (E : H.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (v : M.Point (BandTrees.band narrow H.lower) (H.root E))
    (hw : w ∈ G.allSeeds C) (hv : v ∈ H.allSeeds E)
    (hwp : ¬G.Admitted true C w) (hwn : ¬G.Admitted false C w)
    (hvp : ¬H.Admitted true E v) (hvn : ¬H.Admitted false E v)
    {root : Fin (k+1)} (x y : M.Point D.band root)
    (hxc : x.column=w.column) (hxh : x.height=w.height)
    (hyc : y.column=v.column) (hyh : y.height=v.height)
    (hlo : 1≤dist x y) (hhi : dist x y≤2)
    (hcut : |D.value lam x.column ⟨x.height,x.inBand⟩-
      D.value lam y.column ⟨y.height,y.inBand⟩|≤R/10000) :
    (D.base.transverse (by norm_num) D.lower D.upper).eval x *
      (D.base.transverse (by norm_num) D.lower D.upper).eval y < 0 ∧
    R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x| ∧
    R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y| ∧
    |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8 ∧
    |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8 := by
  let Ex := G.excursions_of_rejected he C w hw hwp hwn x hxc hxh
  have Ey : D.base.Excursions (G.narrow_sub_ordered he) y (2*R) (2*R/5) := by
    have e := H.excursions_of_rejected hf E v hv hvp hvn y hyc hyh
    simpa only [hl] using e
  have width : ∀ s ∈ BandTrees.band narrow G.lower,
      ∀ t ∈ BandTrees.band narrow G.lower, |s-t|≤a₂ := by
    intro s hs t ht
    change G.lower ≤ s ∧ s≤G.lower+a₂ at hs
    change G.lower ≤ t ∧ t≤G.lower+a₂ at ht
    exact abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [ht.1,hs.2]⟩
  have hclose := D.base_close_of_value x y hhi hcut
  have eqR : R=(1:ℝ)/100000000 := by norm_num [R]
  rw [eqR] at Ex Ey hclose ⊢
  exact D.base.two_side D.ordered D.closed (by norm_num [a₂])
    (G.narrow_sub_ordered he) width x y hlo hhi Ex Ey hclose

end SecondaryGeometry.Group
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Separation
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace Ambient
variable (A : Ambient M)
lemma taper_of_ball {region : Set (M.Point Set.univ A.root)}
    (x : M.Point Set.univ A.root)
    (hx : ∀ z, dist x z≤1 → z ∈ region) : Increment.taper regionᶜ 1 x=1 := by
  apply Increment.taper_one (by norm_num)
  intro hn
  apply (Metric.le_infDist hn).mpr
  intro z hz
  exact le_of_not_gt (fun hd => hz (hx z hd.le))
end Ambient

namespace OrderedData
variable (D : OrderedData M) {A : Ambient M}
variable (H : A.History (R/200))
variable (region : Set (M.Point Set.univ A.root))
variable (hcross : ∀ j, 10≤(R/200)*H.radius j)
variable (hrec : (BData.ordered D).Recorded H (by norm_num [R]) (by norm_num [R]))

include hrec in
lemma incrementField_eq (e : Bool) {root : Fin (k+1)} (x : M.Point D.band root)
    (hx : ∀ z, dist (A.point x.column x.height) z≤1 → z ∈ region)
    (hl : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x|)
    (hu : |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8) :
    (D.incrementField H region hcross e).eval x =
      D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩+
        (SecondaryGeometry.Group.lam:ℝ)*
          (if e then (D.base.transverse (by norm_num) D.lower D.upper).eval x
            else -(D.base.transverse (by norm_num) D.lower D.upper).eval x) := by
  have hd := BData.increment_difference D H 1 region e (by norm_num [R])
    (by norm_num [R]) (by norm_num) (by simpa using hcross) hrec
    SecondaryGeometry.Group.lam SecondaryGeometry.Group.lam_bound
    x.column ⟨x.height,x.inBand⟩
  have ht := A.taper_of_ball (A.point x.column x.height) hx
  have hs := Increment.scalar_plateau (a := R/200*1) (r := 1)
    (t := (D.base.transverse (by norm_num) D.lower D.upper).eval x)
    (by norm_num [R]) (by linarith) (by simpa using hu)
  change (D.incrementField H region hcross e).eval x-
    D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩ = _ at hd
  simp only [Increment.signedDamped,Increment.damped,Field.eval] at hd hs ⊢
  rw [hs,ht,mul_one] at hd
  linarith

include hrec in
/-- Genuine append-only histories have a favorable fair sign. The old field
may be arbitrary and is not discarded in this difference calculation. -/
lemma exists_increment_gain {root : Fin (k+1)} (x y : M.Point D.band root)
    (hx : ∀ z, dist (A.point x.column x.height) z≤1 → z ∈ region)
    (hy : ∀ z, dist (A.point y.column y.height) z≤1 → z ∈ region)
    (ho : (D.base.transverse (by norm_num) D.lower D.upper).eval x *
      (D.base.transverse (by norm_num) D.lower D.upper).eval y<0)
    (hlx : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x|)
    (hly : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y|)
    (hux : |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8)
    (huy : |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8) :
    ∃ e : Bool, lambda*R/50 ≤
      |(D.incrementField H region hcross e).eval x-(D.incrementField H region hcross e).eval y| := by
  let tx := (D.base.transverse (by norm_num) D.lower D.upper).eval x
  let ty := (D.base.transverse (by norm_num) D.lower D.upper).eval y
  let p := D.value SecondaryGeometry.Group.lam x.column ⟨x.height,x.inBand⟩-
    D.value SecondaryGeometry.Group.lam y.column ⟨y.height,y.inBand⟩
  have hb : R/50≤|tx-ty| := by
    rw [← Field.abs_add_eq_abs_sub_of_opposite ho]
    linarith
  have hgain : lambda*R/50≤|(SecondaryGeometry.Group.lam:ℝ)*(tx-ty)| := by
    rw [abs_mul,abs_of_nonneg (NNReal.coe_nonneg _)]
    change lambda*R/50≤lambda*|tx-ty|
    have h := mul_le_mul_of_nonneg_left hb (by norm_num [lambda,R] : 0≤lambda)
    linarith
  rcases Increment.opposite_sign_gain p ((SecondaryGeometry.Group.lam:ℝ)*(tx-ty)) with h | h
  · refine ⟨true,?_⟩
    rw [D.incrementField_eq H region hcross hrec true x hx hlx hux,
      D.incrementField_eq H region hcross hrec true y hy hly huy]
    simp only [ite_true]
    convert hgain.trans h using 1
    all_goals try with_reducible_and_instances rfl
    try dsimp only [p,tx,ty]
    try congr 1
    ring
  · refine ⟨false,?_⟩
    rw [D.incrementField_eq H region hcross hrec false x hx hlx hux,
      D.incrementField_eq H region hcross hrec false y hy hly huy]
    simp only [Bool.false_eq_true,ite_false]
    convert hgain.trans h using 1
    all_goals try with_reducible_and_instances rfl
    try dsimp only [p,tx,ty]
    try congr 1
    ring

end OrderedData
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} (S : BState M κ lam Ω μ)

lemma common_separation (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) :
    S.sets.separation i H j T=max |H-T| |S.oldValue i H-S.oldValue j T| := by
  unfold SetSystem.separation
  simp_rw [S.old_indicator,hi,hj]
  exact (S.labels a).distance _ _ _ _

lemma common_separation_field (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) (hκ : 0≤κ)
    (hH : H ∈ (S.chart a).band) (hT : T ∈ (S.chart a).band) :
    κ*|(S.chart a).value lam i ⟨H,hH⟩-(S.chart a).value lam j ⟨T,hT⟩|≤
      S.sets.separation i H j T := by
  rw [S.common_separation i j H T a hi hj,S.oldValue_eq i H a hi,S.oldValue_eq j T a hj,
    ←mul_sub,abs_mul,abs_of_nonneg hκ]
  exact le_max_right _ _

lemma fieldUpdate_separation (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0≤κ) (hsmall : κ*5≤1/2) (hlam : lam≤(1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T → |S.newValue F i H-S.oldValue i H|≤|H-T|/8)
    (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) :
    (S.fieldUpdate F hk hsmall hlam hd).separation i H j T=
      max |H-T| |S.newValue F i H-S.newValue F j T| := by
  unfold SetSystem.separation
  change (∫ ω, |(S.fieldActivity F hk hsmall hlam hd ω).indicator i H-
    (S.fieldActivity F hk hsmall hlam hd ω).indicator j T| ∂μ)=_
  simp_rw [S.field_indicator,hi,hj]
  exact (S.labels a).distance _ _ _ _
end BState

namespace OrdinaryState
variable {κ : ℝ} (S : OrdinaryState M κ Ω μ)
lemma common_separation (i j : Fin (k+1)) (H T : ℝ) (a : Fin (S.count+1))
    (hi : S.name i H=a) (hj : S.name j T=a) (hκ : 0≤κ)
    (hH : H ∈ (S.chart a).band) (hT : T ∈ (S.chart a).band) :
    S.sets.separation i H j T=max |H-T|
      (κ*|(S.chart a).comparison.value i ⟨H,hH⟩-(S.chart a).comparison.value j ⟨T,hT⟩|) := by
  have h := (BState.ofOrdinary (lam := (0:ℝ≥0)) S).common_separation i j H T a hi hj
  rw [BState.oldValue_eq _ i H a hi,BState.oldValue_eq _ j T a hj] at h
  change S.sets.separation i H j T=max |H-T|
    |κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value i ⟨H,hH⟩)-
      κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value j ⟨T,hT⟩)| at h
  rw [h]
  congr 1
  rw [show κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value i ⟨H,hH⟩)-
      κ*((S.chart a).constant+(S.chart a).orientation*(S.chart a).comparison.value j ⟨T,hT⟩)=
      κ*(S.chart a).orientation*((S.chart a).comparison.value i ⟨H,hH⟩-
        (S.chart a).comparison.value j ⟨T,hT⟩) by ring,
    abs_mul,abs_mul,abs_of_nonneg hκ,(S.chart a).unit_orientation,mul_one]
end OrdinaryState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.VertexTests
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)

private lemma ordinary_value_transport {D E : OrdinaryData M} (he : D=E)
    (i : Fin (k+1)) (H : ℝ) (hD : H ∈ D.band) (hE : H ∈ E.band) :
    D.comparison.value i ⟨H,hD⟩=E.comparison.value i ⟨H,hE⟩ := by subst E; rfl
private lemma full_value_transport {D E : BData M} (he : D=E)
    (i : Fin (k+1)) (H : ℝ) (hD : H ∈ D.band) (hE : H ∈ E.band) :
    D.value SecondaryGeometry.Group.lam i ⟨H,hD⟩=
    E.value SecondaryGeometry.Group.lam i ⟨H,hE⟩ := by subst E; rfl

lemma Cutoffs.symm {x y : V} (h : Cutoffs A SA SB v x y) : Cutoffs A SA SB v y x := by
  simpa only [Cutoffs,abs_sub_comm] using h

/-- A failed literal cutoff already supplies an actual cut separation. No
rescaling, refinement, or desired probability is hidden in this alternative. -/
lemma separation_of_cutoff_failure {x y : V} (h : Eligible A SA SB v x y)
    (hf : ¬Cutoffs A SA SB v x y) :
    cutoffGain≤SA.sets.separation (v x).column (v x).height (v y).column (v y).height ∨
    cutoffGain≤SB.sets.separation (v x).column (v x).height (v y).column (v y).height := by
  have hA := h.namesA A SA SB v
  have hB := h.namesB A SA SB v
  have hey : SA.name (v y).column (v y).height=indexA A SA v x := hA
  have hty : (v y).height ∈ (SA.chart (indexA A SA v x)).band := by
    rw [←hA]
    exact SA.height_in (v y).column (v y).height
  have hby : SB.name (v y).column (v y).height=indexB A SB v x := hB
  have htb : (v y).height ∈ (SB.chart (indexB A SB v x)).band := by
    rw [←hB]
    exact SB.height_in (v y).column (v y).height
  have hs := SA.common_separation (v x).column (v y).column (v x).height (v y).height
    (indexA A SA v x) rfl hey verticalA.1 (SA.height_in _ _) hty
  have ha : (SA.chart (indexA A SA v x)).comparison.value (v y).column ⟨(v y).height,hty⟩=
      ordinaryValue A SA v y := by
    exact ordinary_value_transport (congrArg SA.chart hA.symm) _ _ _ _
  rw [ha] at hs
  change SA.sets.separation (v x).column (v x).height (v y).column (v y).height =
    max |(v x).height-(v y).height| (kappaA*|ordinaryValue A SA v x-ordinaryValue A SA v y|) at hs
  by_cases hh : |(v x).height-(v y).height|<a₂/10000
  · by_cases hv : |ordinaryValue A SA v x-ordinaryValue A SA v y|<EA
    · have hb : R/10000≤|fullValue A SB v x-fullValue A SB v y| :=
        le_of_not_gt (fun hb => hf ⟨hh,hv,hb⟩)
      right
      have hd := SB.common_separation_field (v x).column (v y).column (v x).height (v y).height
        (indexB A SB v x) rfl hby verticalB.1 (SB.height_in _ _) htb
      have he : (SB.chart (indexB A SB v x)).value SecondaryGeometry.Group.lam
          (v y).column ⟨(v y).height,htb⟩=fullValue A SB v y := by
        exact full_value_transport (congrArg SB.chart hB.symm) _ _ _ _
      rw [he] at hd
      change kappaB*|fullValue A SB v x-fullValue A SB v y|≤_ at hd
      have hb' := mul_le_mul_of_nonneg_left hb verticalB.1
      calc cutoffGain ≤ kappaB*R/10000 := (min_le_right _ _).trans (min_le_right _ _)
           _ ≤ kappaB*|fullValue A SB v x-fullValue A SB v y| := by linarith
           _ ≤ _ := hd
    · left
      rw [hs]
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_gt hv) verticalA.1).trans (le_max_right _ _))
  · left
    rw [hs]
    exact (min_le_left _ _).trans ((le_of_not_gt hh).trans (le_max_left _ _))

end PlanarL1.Columns.Model.VertexTests

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PairGeometry
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Threshold.labelMeasure_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Threshold.Variables
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma measurable_slab (Z : Variables Ω μ) (b : Bool) (lo hi : ℝ) :
    MeasurableSet (Z.slab b lo hi) :=
  ((measurableSet_singleton b).prod measurableSet_Ico).preimage Z.preserving.measurable
lemma mem_slab (Z : Variables Ω μ) (b : Bool) (lo hi : ℝ) (ω : Ω) :
    ω ∈ Z.slab b lo hi ↔ (Z.value ω).1=b ∧ lo ≤ (Z.value ω).2 ∧ (Z.value ω).2 < hi := by
  simp only [slab,mem_preimage,mem_prod,mem_singleton_iff,mem_Ico]
lemma measure_slab (Z : Variables Ω μ) (b : Bool) {lo hi : ℝ} (hh : lo ≤ hi) :
    μ.real (Z.slab b lo hi)=(hi-lo)/2 := by
  unfold Measure.real slab
  rw [Z.preserving.measure_preimage (((measurableSet_singleton b).prod measurableSet_Ico).nullMeasurableSet),
    labelMeasure_eq,Measure.prod_prod, fair,Measure.smul_apply,smul_eq_mul,
    Measure.count_singleton,mul_one,Real.volume_Ico,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hh)]
  norm_num
  ring
end PlanarL1.Threshold.Variables

namespace PlanarL1.Columns.Model.OrdinaryState
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (S : OrdinaryState M kappaA Ω μ)

/-- The elementary barrier rectangle in one literal ordinary chart. All three
memberships and its uniform real mass are produced, rather than assumed. -/
lemma barrier_labels (a : Fin (S.count+1)) {root : Fin n}
    (x y e : M.Point (S.chart a).band root)
    (hx : S.name x.column x.height=a) (hy : S.name y.column y.height=a)
    (he : S.name e.column e.height=a)
    {lo : ℝ} (hxH : x.height ∈ Set.Icc lo (lo+a₂))
    (hyH : y.height ∈ Set.Icc lo (lo+a₂)) (heH : e.height ∈ Set.Icc lo (lo+a₂))
    (hclose : |(S.chart a).comparison.eval x-(S.chart a).comparison.eval y| ≤ EA)
    (hdrop : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j ∨
      (S.chart a).comparison.eval e < (S.chart a).comparison.eval y-j) :
    ∃ E : Set Ω, MeasurableSet E ∧ kappaA*j/4 ≤ μ.real E ∧
      (∀ ω ∈ E, (S.sets.activity ω).active x.column x.height) ∧
      (∀ ω ∈ E, (S.sets.activity ω).active y.column y.height) ∧
      (∀ ω ∈ E, ¬(S.sets.activity ω).active e.column e.height) := by
  let sx := (S.chart a).comparison.eval x
  let sy := (S.chart a).comparison.eval y
  let se := (S.chart a).comparison.eval e
  let τ := (S.chart a).orientation
  let c := (S.chart a).constant
  obtain ⟨b,hb⟩ : ∃ b : Bool, (if b then (1:ℝ) else -1)=τ := by
    obtain h | h := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp (S.chart a).unit_orientation
    · exact ⟨true,h.symm⟩
    · exact ⟨false,h.symm⟩
  let tx := x.height+kappaA*τ*c+kappaA*sx
  let ty := y.height+kappaA*τ*c+kappaA*sy
  let te := e.height+kappaA*τ*c+kappaA*se
  have hsx : j-EA ≤ sx-se := by
    dsimp only [sx,sy,se] at *
    obtain h | h := hdrop
    · linarith [show 0 ≤ EA by norm_num [EA,epsilon]]
    · linarith [(abs_le.mp hclose).1]
  have hsy : j-EA ≤ sy-se := by
    dsimp only [sx,sy,se] at *
    obtain h | h := hdrop
    · linarith [(abs_le.mp hclose).2]
    · linarith [show 0 ≤ EA by norm_num [EA,epsilon]]
  have hk : 0 < kappaA := by norm_num [kappaA,a₁]
  have hj : 0 < j := by norm_num [j,R]
  have hnum : kappaA*j/2 ≤ kappaA*(j-EA)-a₂ := by
    norm_num [kappaA,a₁,j,R,EA,epsilon,a₂]
  have htx : kappaA*j/2 ≤ tx-te := by
    have := mul_le_mul_of_nonneg_left hsx hk.le
    dsimp only [tx,te]
    nlinarith [hxH.1,heH.2]
  have hty : kappaA*j/2 ≤ ty-te := by
    have := mul_le_mul_of_nonneg_left hsy hk.le
    dsimp only [ty,te]
    nlinarith [hyH.1,heH.2]
  have hmin : kappaA*j/2 ≤ min tx ty-te := by
    rw [← min_sub_sub_right]
    exact le_min htx hty
  have hle : te ≤ min tx ty := by nlinarith
  have hformula (z : M.Point (S.chart a).band root) :
      (if b then z.height+kappaA*(S.chart a).value z.column ⟨z.height,z.inBand⟩
      else z.height-kappaA*(S.chart a).value z.column ⟨z.height,z.inBand⟩)=
        z.height+kappaA*τ*c+kappaA*(S.chart a).comparison.eval z := by
    cases b  <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hb ⊢  <;>
      dsimp only [OrdinaryData.value,Field.eval] 
    · have hτ : (S.chart a).orientation = -1 := hb.symm
      simp only [hτ]
      dsimp only [τ,c]
      rw [hτ]
      ring
    · have hτ : (S.chart a).orientation = 1 := hb.symm
      simp only [hτ]
      dsimp only [τ,c]
      rw [hτ]
      ring
  let E := (S.labels a).slab b te (min tx ty)
  refine ⟨E,(S.labels a).measurable_slab b te (min tx ty),?_,?_,?_,?_⟩
  · rw [(S.labels a).measure_slab b hle]
    linarith
  · intro ω hω
    obtain ⟨hωb,_,hω⟩ := ((S.labels a).mem_slab b te (min tx ty) ω).mp hω
    rw [S.represents_named ω _ _ a hx x.inBand]
    unfold Threshold.active
    rw [hωb,hformula x]
    exact hω.trans_le (min_le_left _ _)
  · intro ω hω
    obtain ⟨hωb,_,hω⟩ := ((S.labels a).mem_slab b te (min tx ty) ω).mp hω
    rw [S.represents_named ω _ _ a hy y.inBand]
    unfold Threshold.active
    rw [hωb,hformula y]
    exact hω.trans_le (min_le_right _ _)
  · intro ω hω ha
    obtain ⟨hωb,hω,_⟩ := ((S.labels a).mem_slab b te (min tx ty) ω).mp hω
    rw [S.represents_named ω _ _ a he e.inBand] at ha
    unfold Threshold.active at ha
    rw [hωb,hformula e] at ha
    exact (not_lt_of_ge hω) ha
end PlanarL1.Columns.Model.OrdinaryState

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace OrdinaryState.MainStep
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

/-- The other endpoint can be in another broad component. Only its actual old
identifier and its absence from this cell matter for the indicator calculation. -/
lemma pair_distance_external (x : M.Point J root) (j : Fin n) (T : ℝ)
    (hT : T ∈ U.data.band) (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : T ∉ MainCell.domain U.tree U.phase U.cell j) (hyn : S.name j T=U.index) :
    (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator j T| ∂(μ.prod Threshold.fair)) =
      max |x.height-T| (κ*|MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x-U.comparison.value j ⟨T,hT⟩|) := by
  have hxi := (MainCell.mem_domain U.tree U.phase U.cell).mpr ⟨hx,x.inBand⟩
  have he : MainCell.cellPoint U.tree U.phase U.cell x.column x.height hxi=x := by cases x; rfl
  have hid (ω : Ω × Bool) :
      (U.patch.apply.activity ω).indicator j T =
        Threshold.chartValue T (κ*(U.data.constant+U.data.orientation*U.comparison.value j ⟨T,hT⟩))
          ((S.labels U.index).lift.value ω) := by
    have hr := S.represents_named ω.1 j T U.index hyn hT
    have hp := U.patch.unchanged hy ω
    simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
    exact if_congr (hp.trans hr) rfl rfl
  simp_rw [U.indicator_inside _ _ _ hxi,he,hid]
  rw [(S.labels U.index).lift.distance]
  congr 1
  rw [show κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
      U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo x)-
      κ*(U.data.constant+U.data.orientation*U.comparison.value j ⟨T,hT⟩) =
      κ*U.data.orientation*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x-U.comparison.value j ⟨T,hT⟩) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]

lemma separation_of_raise_external (x : M.Point J root) (j : Fin n) (T : ℝ)
    (hT : T ∈ U.data.band) (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : T ∉ MainCell.domain U.tree U.phase U.cell j) (hyn : S.name j T=U.index) (hκ : 0<κ)
    (hclose : |MainCell.old U.comparison U.sub_old x-U.comparison.value j ⟨T,hT⟩| ≤ U.error)
    (hraise : MainCell.old U.comparison U.sub_old x+2*U.error <
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x) :
    κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator j T| ∂(μ.prod Threshold.fair)) := by
  rw [U.pair_distance_external x j T hT hx hy hyn]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  apply mul_lt_mul_of_pos_left _ hκ
  have hb := (abs_le.mp hclose).1
  have ha := le_abs_self (MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
    U.anchor U.noise U.error U.shield_offset U.lo x-U.comparison.value j ⟨T,hT⟩)
  linarith

lemma pair_separation_external (x : M.Point J root) (j : Fin n) (T : ℝ)
    (hT : T ∈ U.data.band) (hx : x.column ∈ ColumnOrder.componentColumns U.cell)
    (hy : T ∉ MainCell.domain U.tree U.phase U.cell j) (hyn : S.name j T=U.index) (hκ : 0<κ)
    {ε : ℝ} (hε : 0<ε) (hεsmall : ε ≤ (1:ℝ)/100)
    (hζ : U.tree.ζ=ε/100) (hE : U.error=ε/1000)
    (hclose : |MainCell.old U.comparison U.sub_old x-U.comparison.value j ⟨T,hT⟩| ≤ U.error)
    (hshield : MainCell.old U.comparison U.sub_old U.anchor+2 ≤
      Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset x.height)
    (hlow : U.phase+(1:ℝ)/100000+2*U.tree.a <
      dist U.tree.base (x.withHeight U.tree.base.height U.tree.base.inBand))
    (hupp : dist U.tree.base (x.withHeight U.tree.base.height U.tree.base.inBand) <
      U.phase+(1:ℝ)/1000-(1:ℝ)/100000-2*U.tree.a)
    (hno : ¬Nonempty (U.comparison.BandDescent J (x.widen U.sub_old) ε)) :
    κ*U.error < (∫ ω, |(U.patch.apply.activity ω).indicator x.column x.height-
        (U.patch.apply.activity ω).indicator j T| ∂(μ.prod Threshold.fair)) := by
  apply U.separation_of_raise_external x j T hT hx hy hyn hκ hclose
  have hδ : U.tree.δ=(ε/1000)/8 := by rw [U.delta_eq,hE]
  have hh := MainCell.raise_or_descent U.comparison U.sub_old U.tree U.phase U.cell
    U.compact_band U.anchor x U.anchor_mem hx hε hεsmall hζ hδ U.noise_bounds
      (fun z => Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
        U.shield_offset z.height) hshield hlow hupp
  rcases hh with hh | hh
  · simpa only [hE,MainCell.replacement] using hh
  · exact (hno hh).elim
end OrdinaryState.MainStep
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PairSelection
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.BandTrees
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {lo : ℝ} {C : Component M broad lo}

lemma radial_difference (x y : M.Point (band broad lo) (root M broad lo C)) :
    |radialValue x-radialValue y|≤dist x y+a₁ :=
  (base M broad lo C).radial_difference_le x y (middle_mem broad lo)
    (tree M broad lo C).half_width

lemma radialInterior_of_avoid {width phase : ℝ}
    (x : M.Point (band broad lo) (root M broad lo C))
    (hn : ¬Tiling.NearBoundary width phase (radialValue x) (width/50+a₁)) :
    RadialInterior width phase x := by
  intro y hy hn'
  have hd := radial_difference y x
  rw [dist_comm y x,hy,zero_add] at hd
  exact hn (hn'.perturb.mono (by linarith))

end PlanarL1.Columns.Model.BandTrees

namespace PlanarL1.FiniteRandom
open Parameters Tiling

/-- Two canonical representatives, possibly in the same component, suffice
for the source 0.081 radial allowance. No count of columns is involved. -/
lemma radial_pair_probability {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (hm : 10000 ≤ m) (i j : I) (x y : ℝ) {width : ℝ}
    (hw : 0<width) (hsmall : a₁≤width/100000) :
    prob (fun ω : I → Fin (m+1) =>
      NearBoundary width (width/m*(ω i).val) x (width/50+a₁) ∨
      NearBoundary width (width/m*(ω j).val) y (width/50+a₁)) ≤81/1000 := by
  have hm0 : 0 < m := by omega
  have hmR : (10000:ℝ) ≤ m := by exact_mod_cast hm
  have hmesh : width/m≤width/10000 := div_le_div_of_nonneg_left hw.le (by norm_num) hmR
  have hb : (2*(width/50+a₁)+2*width/m)/width≤81/2000 := by
    apply (div_le_iff₀ hw).mpr
    rw [mul_div_assoc]
    linarith
  have hp (h : ℝ) := (periodic_probability m hm0 hw
    (show 0≤width/50+a₁ by have ha := interpolationA.2.1; positivity) h).trans hb
  have h₁ := prob_eval_bound i (fun r : Fin (m+1) =>
    NearBoundary width (width/m*r.val) x (width/50+a₁)) (hp x)
  have h₂ := prob_eval_bound j (fun r : Fin (m+1) =>
    NearBoundary width (width/m*r.val) y (width/50+a₁)) (hp y)
  exact (prob_or_le _ _).trans (by linarith)

end PlanarL1.FiniteRandom

end



section

namespace PlanarL1.Tiling
lemma same_index_of_padded {a q h x t : ℝ} (ha : 0<a)
    (hp : Padded a q h t) (hx : |x-h|≤t) : index a q x=index a q h := by
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  exact index_eq_of_mem_lt ha _ (by linarith [hp.1]) (by linarith [hp.2])
end PlanarL1.Tiling

end



section

namespace PlanarL1.Execution
lemma prob_bind_pure {α β : Type*} (E : Execution α) (f : α → β) (P : β → Prop) :
    (E.bind (fun x => .pure (f x))).prob P=E.prob (fun x => P (f x)) := by
  rw [prob_bind]
  rfl
end PlanarL1.Execution

namespace PlanarL1.Columns.Model.VertexBands
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)

lemma radial_pair_failure (m : ℕ) (hm : 10000 ≤ m) (q : ℝ) (x y : V)
    {width : ℝ} (hw : 0<width) (hs : a₁≤width/100000) :
    prob (fun r : MainFamily.BandComponent (M := M) q L U → Fin (m+1) =>
      ¬(radial A v (hv := hv) q width (phase width r) x ∧
        radial A v (hv := hv) q width (phase width r) y))≤81/1000 := by
  let i := bandComponent A v L U hv q x
  let j := bandComponent A v L U hv q y
  let X := BandTrees.radialValue (point A v L U hv q x)
  let Y := BandTrees.radialValue (point A v L U hv q y)
  apply (prob_mono (P := fun r => ¬(radial A v (hv := hv) q width (phase width r) x ∧
    radial A v (hv := hv) q width (phase width r) y))
    (Q := fun r => Tiling.NearBoundary width (width/m*(r i).val) X (width/50+a₁) ∨
      Tiling.NearBoundary width (width/m*(r j).val) Y (width/50+a₁)) ?_).trans
    (radial_pair_probability m hm i j X Y hw hs)
  intro r hr
  by_contra hn
  push Not at hn
  exact hr ⟨BandTrees.radialInterior_of_avoid _ hn.1,BandTrees.radialInterior_of_avoid _ hn.2⟩

lemma radial_both_failure (m : ℕ) (hm : 10000 ≤ m) (q : ℝ) (x y : V) :
    prob (fun r : RadialChoices m q L U M =>
      ¬(radial A v (hv := hv) q D (phase D r.1) x ∧
        radial A v (hv := hv) q D (phase D r.1) y ∧
        radial A v (hv := hv) q g (phase g r.2) x ∧
        radial A v (hv := hv) q g (phase g r.2) y))≤81/500 := by
  let P := fun r : RadialChoices m q L U M =>
    ¬(radial A v (hv := hv) q D (phase D r.1) x ∧ radial A v (hv := hv) q D (phase D r.1) y)
  let Q := fun r : RadialChoices m q L U M =>
    ¬(radial A v (hv := hv) q g (phase g r.2) x ∧ radial A v (hv := hv) q g (phase g r.2) y)
  have hp : prob P≤81/1000 := prob_prod_bound_left P (fun _ =>
    radial_pair_failure A v hv m hm q x y (width := D) (by norm_num [D]) (by norm_num [a₁,D]))
  have hq : prob Q≤81/1000 := prob_prod_bound Q (fun _ =>
    radial_pair_failure A v hv m hm q x y (width := g) (by norm_num [g]) (by norm_num [a₁,g]))
  apply (prob_mono (Q := fun r => P r ∨ Q r) ?_).trans ((prob_or_le P Q).trans (by linarith))
  intro r hr
  by_contra hn
  have hP : ¬P r := (not_or.mp hn).1
  have hQ : ¬Q r := (not_or.mp hn).2
  exact hr ⟨(not_not.mp hP).1,(not_not.mp hP).2,(not_not.mp hQ).1,(not_not.mp hQ).2⟩

/-- A literal finite sequence of shifts followed by component-indexed radial
origins. Component types may depend on the height shifts; using bind avoids a
spurious uniform law on a dependent sum. -/
lemma interior_pair_probability (m : ℕ) (hm : 10000 ≤ m) (x y : V)
    (hd : |(v y).height-(v x).height|≤a₂/10000) :
    1/4≤(geometricExecution m L U M).prob
      (fun c => InteriorAt A v hv c x ∧ InteriorAt A v hv c y) := by
  let H := fun h : HeightChoices m =>
    Tiling.Padded a₁ (shift m a₁ h.1) (v x).height (a₁/10) ∧
    Tiling.Padded a₁ (shift m a₁ h.1) (v y).height (a₁/10) ∧
    Tiling.Padded a₂ (shift m a₂ h.2) (v x).height (a₂/10) ∧
    Tiling.Padded a₂ (shift m a₂ h.2) (v y).height (a₂/10)
  let P := fun h : HeightChoices m => ¬(Tiling.Padded a₁ (shift m a₁ h.1) (v x).height (a₁/10) ∧
    Tiling.Padded a₁ (shift m a₁ h.1) (v y).height (a₁/10))
  let Q := fun h : HeightChoices m => ¬(Tiling.Padded a₂ (shift m a₂ h.2) (v x).height (a₂/10) ∧
    Tiling.Padded a₂ (shift m a₂ h.2) (v y).height (a₂/10))
  have hp : prob P≤21/100 := prob_prod_bound_left _ (fun _ =>
    Tiling.height_pair_probability m hm interpolationA.2.1 (by norm_num [a₁,a₂]) hd)
  have hq : prob Q≤21/100 := prob_prod_bound _ (fun _ =>
    Tiling.height_pair_probability m hm interpolationB.2.1 le_rfl hd)
  have hheight : Execution.uniform.prob (fun h : HeightChoices m => ¬H h)≤21/50 := by
    rw [Execution.prob_uniform]
    apply (prob_mono (Q := fun h => P h ∨ Q h) ?_).trans ((prob_or_le P Q).trans (by linarith))
    intro h hh
    by_contra hn
    have hP : ¬P h := (not_or.mp hn).1
    have hQ : ¬Q h := (not_or.mp hn).2
    exact hh ⟨(not_not.mp hP).1,(not_not.mp hP).2,(not_not.mp hQ).1,(not_not.mp hQ).2⟩
  have hl := Execution.conditional_loss (Execution.uniform (α := HeightChoices m))
    (fun h => Execution.uniform.bind (fun r : RadialChoices m (shift m a₁ h.1) L U M =>
      .pure (⟨h,r⟩ : Choices m L U M))) H
    (fun c => InteriorAt A v hv c x ∧ InteriorAt A v hv c y)
    (show (0:ℝ)≤81/500 by norm_num) (by
      intro h hh
      rw [Execution.prob_bind_pure,Execution.prob_uniform]
      apply (prob_mono (Q := fun r : RadialChoices m (shift m a₁ h.1) L U M =>
        ¬(radial A v (hv := hv) _ D (phase D r.1) x ∧
          radial A v (hv := hv) _ D (phase D r.1) y ∧
          radial A v (hv := hv) _ g (phase g r.2) x ∧
          radial A v (hv := hv) _ g (phase g r.2) y)) ?_).trans
        (radial_both_failure A v hv m hm _ x y)
      intro r hr hs
      dsimp [InteriorAt,Interior] at hr
      exact hr ⟨⟨hh.1,hh.2.2.1,hs.1,hs.2.2.1⟩,⟨hh.2.1,hh.2.2.2,hs.2.1,hs.2.2.2⟩⟩)
  change (geometricExecution m L U M).prob
    (fun c => ¬(InteriorAt A v hv c x ∧ InteriorAt A v hv c y))≤_ at hl
  rw [Execution.prob_compl] at hl
  linarith

end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model.OrdinaryState
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (S : OrdinaryState M kappaA Ω μ)

/-- Failure of the actual circular low-tip test produces the literal source
certificate, including its tip and measurable positive label mass. -/
lemma low_tip_certificate (a : Fin (S.count+1)) {root : Fin n}
    (x y : M.Point (S.chart a).band root) (lo : ℝ)
    (hx : S.name x.column x.height=a) (hy : S.name y.column y.height=a)
    (hxH : x.height ∈ Set.Icc lo (lo+a₂)) (hyH : y.height ∈ Set.Icc lo (lo+a₂))
    (hclose : |(S.chart a).comparison.eval x-(S.chart a).comparison.eval y| ≤ EA)
    (hnear : ∀ e : M.Point (S.chart a).band root,
      (dist x e ≤ 1 ∨ dist y e ≤ 1) → S.name e.column e.height=a)
    (hf : ¬(S.chart a).comparison.NoLowCircular x y (Set.Icc lo (lo+a₂)) j) :
    ∃ (e : M.Point (S.chart a).band root) (b : Fin n) (E : Set Ω),
      e.height ∈ M.heights e.column b ∧ ¬Consecutive e.column b ∧
      Field.CircularTipSeparates e.column b x.column y.column ∧
      (dist x e ≤ 1 ∨ dist y e ≤ 1) ∧
      MeasurableSet E ∧ kappaA*j/4 ≤ μ.real E ∧
      (∀ ω ∈ E, (S.sets.activity ω).active x.column x.height) ∧
      (∀ ω ∈ E, (S.sets.activity ω).active y.column y.height) ∧
      (∀ ω ∈ E, ¬(S.sets.activity ω).active e.column e.height) := by
  unfold Field.NoLowCircular at hf
  push Not at hf
  obtain ⟨e,b,heH,hlink,hn,hsep,hd,hdrop⟩ := hf
  have hdrop' : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j ∨
      (S.chart a).comparison.eval e < (S.chart a).comparison.eval y-j := by
    by_cases h : (S.chart a).comparison.eval e < (S.chart a).comparison.eval x-j
    · exact Or.inl h
    · exact Or.inr (hdrop (le_of_not_gt h))
  obtain ⟨E,hE,hm,hX,hY,hN⟩ := S.barrier_labels a x y e hx hy (hnear e hd) hxH hyH heH hclose hdrop'
  exact ⟨e,b,E,hlink,hn,hsep,hd,hE,hm,hX,hY,hN⟩

end PlanarL1.Columns.Model.OrdinaryState

end



section

namespace PlanarL1.Columns.Model
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J K : Set ℝ} {r s : Fin n}
namespace Point
lemma eq_coordinates (x y : M.Point I r) (hc : x.column=y.column) (hh : x.height=y.height) : x=y := by
  cases x
  cases y
  cases hc
  cases hh
  rfl
end Point
namespace Field
variable {F : M.Field I 1} {ε j : ℝ}
lemma BandDescent.coordinates {x : M.Point I r} {y : M.Point I s}
    (D : F.BandDescent J x ε) (hc : x.column=y.column) (hh : x.height=y.height) :
    Nonempty (F.BandDescent J y ε) := by
  have hr : (M.activeGraph I).Reachable s r := y.reachable.trans (hc ▸ x.reachable).symm
  have he : x.reRoot hr=y := Point.eq_coordinates _ _ hc hh
  exact he ▸ ⟨D.reRoot hr⟩

lemma NoLowCircular.symm {x y : M.Point I r} (h : F.NoLowCircular x y J j) :
    F.NoLowCircular y x J j := by
  intro v b hv hs hn ht hd
  have ht' : CircularTipSeparates v.column b x.column y.column := by
    simpa only [CircularTipSeparates,TipSeparates,or_comm] using ht
  exact (h v b hv hs hn ht' hd.symm).symm

lemma NoLowCircular.coordinates {x y : M.Point I r} {x' y' : M.Point I s}
    (H : F.NoLowCircular x y J j)
    (hxc : x.column=x'.column) (hxh : x.height=x'.height)
    (hyc : y.column=y'.column) (hyh : y.height=y'.height) : F.NoLowCircular x' y' J j := by
  have hr : (M.activeGraph I).Reachable s r := x'.reachable.trans (hxc ▸ x.reachable).symm
  have he : x.reRoot hr=x' := Point.eq_coordinates _ _ hxc hxh
  have hf : y.reRoot hr=y' := Point.eq_coordinates _ _ hyc hyh
  exact he ▸ hf ▸ H.reRoot hr
end Field
namespace OrdinaryData
lemma descent_coordinates {D E : OrdinaryData M} (hDE : D=E) {J K : Set ℝ} (hJK : J=K)
    {r s : Fin n} (x : M.Point D.band r) (y : M.Point E.band s) {ε : ℝ}
    (h : Nonempty (D.comparison.BandDescent J x ε))
    (hc : x.column=y.column) (hh : x.height=y.height) :
    Nonempty (E.comparison.BandDescent K y ε) := by
  subst E
  subst K
  exact h.some.coordinates hc hh
lemma noLow_coordinates {D E : OrdinaryData M} (hDE : D=E) {J K : Set ℝ} (hJK : J=K)
    {r s : Fin n} (x y : M.Point D.band r) (x' y' : M.Point E.band s) {j : ℝ}
    (h : D.comparison.NoLowCircular x y J j)
    (hxc : x.column=x'.column) (hxh : x.height=x'.height)
    (hyc : y.column=y'.column) (hyh : y.height=y'.height) : E.comparison.NoLowCircular x' y' K j := by
  subst E
  subst K
  exact h.coordinates hxc hxh hyc hyh
end OrdinaryData
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (hd : dist (v x) (v y)<2)

include hi hc in
lemma broad_lower_eq : VertexBands.lower A v L U hv q y=VertexBands.lower A v L U hv q x := by
  have hxy : |(v y).height-(v x).height|≤a₁/10 := by
    rw [abs_sub_comm]
    exact hc.1.le.trans (by norm_num [a₂,a₁])
  have hn := Tiling.same_index_of_padded interpolationA.2.1 hi.1 hxy
  change q+(Tiling.index a₁ q (v y).height:ℝ)*a₁=q+(Tiling.index a₁ q (v x).height:ℝ)*a₁
  rw [hn]

include hi hc in
lemma narrow_lower_eq : narrowLower A v p y=narrowLower A v p x := by
  have hxy : |(v y).height-(v x).height|≤a₂/10 := by
    rw [abs_sub_comm]
    exact hc.1.le.trans (by norm_num [a₂])
  have hn := Tiling.same_index_of_padded interpolationB.2.1 hi.2.1 hxy
  unfold narrowLower
  rw [hn]

include hc in
lemma Retained.symm (hr : Retained A SA SB v hv he hi hd) :
    Retained A SA SB v hv (he.symm A SA SB v) hj (by simpa only [dist_comm] using hd) := by
  have hD : SA.chart (indexA A SA v x)=SA.chart (indexA A SA v y) :=
    congrArg SA.chart (he.namesA A SA SB v).symm
  have hJ : BandTrees.band broad (VertexBands.lower A v L U hv q x)=
      BandTrees.band broad (VertexBands.lower A v L U hv q y) :=
    congrArg (BandTrees.band broad) (broad_lower_eq A SA SB v hv hi hc).symm
  have hK : BandTrees.band narrow (narrowLower A v p x)=BandTrees.band narrow (narrowLower A v p y) :=
    congrArg (BandTrees.band narrow) (narrow_lower_eq A SA SB v hv hi hc).symm
  let he' := he.symm A SA SB v
  have hd' : dist (v y) (v x)<2 := by simpa only [dist_comm] using hd
  have hyc : (partner A SA SB v hv he hi hd).column=
      ((position A SA SB v hv he' hj).point.widen (position A SA SB v hv he' hj).subA).column :=
    partner_column A SA SB v hv he hi hd
  have hyh : (partner A SA SB v hv he hi hd).height=
      ((position A SA SB v hv he' hj).point.widen (position A SA SB v hv he' hj).subA).height :=
    partner_height A SA SB v hv he hi hd
  have hxc : ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA).column=
      (partner A SA SB v hv he' hj hd').column :=
    (partner_column A SA SB v hv he' hj hd').symm
  have hxh : ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA).height=
      (partner A SA SB v hv he' hj hd').height :=
    (partner_height A SA SB v hv he' hj hd').symm
  exact ⟨OrdinaryData.descent_coordinates hD hJ _ _ hr.2.1 hyc hyh,
    OrdinaryData.descent_coordinates hD hJ _ _ hr.1 hxc hxh,
    OrdinaryData.noLow_coordinates hD hK _ _ _ _ hr.2.2.symm hyc hyh hxc hxh⟩
end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.Ambient
variable {k : ℕ} {M : Model (k+1)} (A : Ambient M)
lemma coordinate_dist_le {J : Set ℝ} {r : Fin (k+1)} (x y : M.Point J r) :
    dist (A.point x.column x.height) (A.point y.column y.height) ≤ dist x y := by
  calc
    _ = dist (x.widen (Set.subset_univ _)) (y.widen (Set.subset_univ _)) :=
      Point.dist_coordinates _ _ _ _ rfl rfl rfl rfl
    _ ≤ _ := x.dist_widen_le y (Set.subset_univ _)
end PlanarL1.Columns.Model.Ambient

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hc : Cutoffs A SA SB v x y) (hd : dist (v x) (v y)<2)

include hc in
lemma certificate_of_excluded
    (hf : ¬(SA.chart (indexA A SA v x)).comparison.NoLowCircular
      ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)
      (partner A SA SB v hv he hi hd) (BandTrees.band narrow (narrowLower A v p x)) j) :
    Certificate A SA v (x := x) (y := y) (kappaA*j/4) := by
  let u : M.Point (SA.chart (indexA A SA v x)).band
      (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)) := (position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA
  let z := partner A SA SB v hv he hi hd
  have hxH : u.height ∈ Set.Icc (narrowLower A v p x) (narrowLower A v p x+a₂) :=
    narrow_height A v p x
  have hyH : z.height ∈ Set.Icc (narrowLower A v p x) (narrowLower A v p x+a₂) := by
    have hy := narrow_height A v p y
    rw [narrow_lower_eq A SA SB v hv hi hc] at hy
    simpa only [z,partner_height,BandTrees.band,narrow] using hy
  have hn : SA.name z.column z.height=indexA A SA v x := by
    rw [partner_column,partner_height]
    exact he.namesA A SA SB v
  have hnear (e : M.Point (SA.chart (indexA A SA v x)).band
      (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)))
      (h : dist u e≤1 ∨ dist z e≤1) : SA.name e.column e.height=indexA A SA v x := by
    rcases h with h | h
    · have hb := (A.coordinate_dist_le u e).trans h
      change dist (A.point (v x).column (v x).height) (A.point e.column e.height)≤1 at hb
      rw [A.coordinate_point] at hb
      exact he.1 _ (hb.trans (by norm_num))
    · have hb := (A.coordinate_dist_le z e).trans h
      rw [partner_column,partner_height,A.coordinate_point] at hb
      exact he.2.1 _ (hb.trans (by norm_num))
  have hclose : |(SA.chart (indexA A SA v x)).comparison.eval u-
      (SA.chart (indexA A SA v x)).comparison.eval z|≤EA := by
    calc
      _ = |ordinaryValue A SA v x-ordinaryValue A SA v y| :=
        congrArg₂ (fun a b : ℝ => |a-b|) (position_value A SA SB v hv he hi)
          (partner_value A SA SB v hv he hi hd)
      _ ≤ _ := hc.2.1.le
  obtain ⟨e,c,E,hlink,hnot,hsep,_,hE,hm,hX,hY,hN⟩ :=
    SA.low_tip_certificate (indexA A SA v x) u z (narrowLower A v p x) rfl hn hxH hyH hclose hnear hf
  refine ⟨e.column,c,e.height,E,hlink,hnot,?_,hE,hm,hX,?_,hN⟩
  · change Field.CircularTipSeparates e.column c (v x).column z.column at hsep
    simpa only [z,partner_column] using hsep
  · simpa only [z,partner_column,partner_height] using hY
end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

lemma distinct_cells (x y : M.Point Set.univ A.root)
    (ha : 1≤dist x y) (c d : CellIndex q L U phase)
    (hx : x.height ∈ domain phase c x.column) (hy : y.height ∈ domain phase d y.column) : c≠d := by
  intro he
  subst d
  have h := cell_diameter A phase c hx hy
  rw [A.coordinate_point x,A.coordinate_point y] at h
  linarith

end PlanarL1.Columns.Model.MainFamily

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainGain
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

lemma unique_at_padded {c d : CellIndex q L U phase} {i : Fin (k+1)} {H : ℝ}
    (hp : Tiling.Padded a₁ q H (a₁/10))
    (hc : H ∈ domain phase c i) (hd : H ∈ domain phase d i) : c=d := by
  apply unique_in_band phase _ hc hd
  apply Subtype.ext
  exact (Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp
    (domain_band phase c hc)).trans
    (Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp
      (domain_band phase d hd)).symm

variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
lemma batch_inside_kept (c : Kept A S phase omega) (w : Ω × Bool)
    (i : Fin (k+1)) (H : ℝ) (hH : H ∈ domain phase c.val i) :
    ((batch A S phase hm omega).sets.activity w).active i H ↔
      ((keptStep A S phase hm omega c).patch.apply.activity w).active i H := by
  apply SetPatch.batch_inside _ (batch A S phase hm omega).overlap
  · apply List.mem_ofFn.mpr
    let e := @Fintype.equivFin (Kept A S phase omega) (instFintypeKept A S phase omega)
    refine ⟨e c, ?_⟩
    exact congrArg (fun d => (keptStep A S phase hm omega d).patch) (e.symm_apply_apply c)
  · exact hH

lemma batch_old_suppressed (c : CellIndex q L U phase) (w : Ω × Bool)
    (i : Fin (k+1)) (H : ℝ) (hH : H ∈ domain phase c i)
    (hp : Tiling.Padded a₁ q H (a₁/10)) (hoff : (omega c).2.2=false) :
    ((batch A S phase hm omega).sets.activity w).active i H ↔
      (S.lift.sets.activity w).active i H := by
  apply SetPatch.batch_old _ (batch A S phase hm omega).overlap
  intro P hP
  obtain ⟨d,rfl⟩ := List.mem_ofFn.mp hP
  apply ((batch A S phase hm omega).step d).patch.unchanged
  intro hd
  let d' : Kept A S phase omega := (Fintype.equivFin _).symm d
  have hd' : H ∈ domain phase d'.val i := hd
  have he : c=d'.val := unique_at_padded phase hp hH hd'
  have ht := d'.property.2
  rw [←he,hoff] at ht
  cases ht

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable
lemma prob_second {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (P : Λ → Prop) : prob (fun z : Ω × Λ => P z.2)=prob P := by
  rw [prob_prod]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by positivity)

end PlanarL1.FiniteRandom

namespace PlanarL1.Columns.Model.MainFamily
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {q L U : ℝ}
variable (phase : BandComponent (M := M) q L U → ℝ) (m : ℕ)
lemma prob_coins (P : (CellIndex q L U phase → Bool) → Prop) :
    prob (fun omega : Sample phase m => P (fun c => (omega c).2.2))=prob P := by
  let e := (restructure phase m).trans (coinProduct (Uncoined phase m))
  have he := prob_equiv e.symm (fun omega : Sample phase m => P (fun c => (omega c).2.2))
  change prob (fun f : (∀ c, Uncoined phase m c) × (CellIndex q L U phase → Bool) => P f.2)=_ at he
  exact he.symm.trans (prob_second P)
lemma prob_keep_suppress (c d : CellIndex q L U phase) (hne : c≠d) :
    prob (fun omega : Sample phase m => (omega c).2.2=true ∧ (omega d).2.2=false)=1/4 := by
  apply (prob_coins phase m (fun f => f c=true ∧ f d=false)).trans
  convert prob_two_coins c d hne true false using 1
  all_goals try with_reducible_and_instances rfl
  exact congrArg (fun F : Fintype (CellIndex q L U phase → Bool) =>
    @prob _ F (fun f => f c=true ∧ f d=false)) (Subsingleton.elim _ _)
end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)

lemma batch_pair_kept_suppressed (c : Kept A S phase omega) (d : CellIndex q L U phase)
    (ii jj : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ domain phase c.val ii) (hy : T ∈ domain phase d jj)
    (hp : Tiling.Padded a₁ q T (a₁/10)) (hoff : (omega d).2.2=false) :
    (∫ w, |((batch A S phase hm omega).sets.activity w).indicator ii H-
      ((batch A S phase hm omega).sets.activity w).indicator jj T| ∂(μ.prod Threshold.fair)) =
    (∫ w, |((keptStep A S phase hm omega c).patch.apply.activity w).indicator ii H-
      ((keptStep A S phase hm omega c).patch.apply.activity w).indicator jj T| ∂(μ.prod Threshold.fair)) := by
  have hout : T ∉ domain phase c.val jj := by
    intro hc
    have he := unique_at_padded phase hp hy hc
    have ht := c.property.2
    rw [←he,hoff] at ht
    cases ht
  apply integral_congr_ae
  filter_upwards [] with w
  have heX := batch_inside_kept A S phase hm omega c w ii H hx
  have heY := batch_old_suppressed A S phase hm omega d w jj T hy hp hoff
  have hpY := (keptStep A S phase hm omega c).patch.unchanged hout w
  simp only [Activity.indicator,heX,heY,hpY]

lemma padded_height {c : CellIndex q L U phase} {i : Fin (k+1)} {H : ℝ}
    (hx : H ∈ domain phase c i) (hp : Tiling.Padded a₁ q H (a₁/10)) :
    lower q L U c.1.1+a₁/10 < H ∧ H < lower q L U c.1.1+a₁-a₁/10 := by
  have he := Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp
    (domain_band phase c hx)
  unfold Tiling.Padded at hp
  rw [←he] at hp
  change q+(c.1.1.val:ℝ)*a₁+a₁/10 < H ∧ H < q+(c.1.1.val:ℝ)*a₁+a₁-a₁/10
  constructor <;> linarith [hp.1,hp.2]

lemma kept_shield (c : Kept A S phase omega)
    (x : M.Point (BandTrees.band broad (lower q L U c.val.1.1))
      (BandTrees.root M broad (lower q L U c.val.1.1) c.val.1.2))
    (hx : x.height ∈ domain phase c.val x.column)
    (hp : Tiling.Padded a₁ q x.height (a₁/10)) :
    MainCell.old (keptStep A S phase hm omega c).comparison
      (keptStep A S phase hm omega c).sub_old (keptStep A S phase hm omega c).anchor+2 ≤
    Clipping.heightShield (keptStep A S phase hm omega c).lo (keptStep A S phase hm omega c).tree.a
      (MainCell.old (keptStep A S phase hm omega c).comparison
        (keptStep A S phase hm omega c).sub_old (keptStep A S phase hm omega c).anchor)
      (keptStep A S phase hm omega c).shield_offset x.height := by
  have hpad := padded_height phase hx hp
  have he := Clipping.heightShield_plateau (s :=
    MainCell.old (keptStep A S phase hm omega c).comparison
      (keptStep A S phase hm omega c).sub_old (keptStep A S phase hm omega c).anchor)
    (α := (keptStep A S phase hm omega c).shield_offset)
    interpolationA.2.1 (lo := lower q L U c.val.1.1) (H := x.height)
    (by linarith [hpad.1]) (by linarith [hpad.2])
  change _ ≤ Clipping.heightShield (lower q L U c.val.1.1) a₁ _ _ x.height
  rw [he]
  have hpos : 0 ≤ EA/(m:ℝ)*((omega c.val).2.1.val:ℝ) :=
    mul_nonneg (div_nonneg interpolationA.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  change _ ≤ _+2+EA/(m:ℝ)*((omega c.val).2.1.val:ℝ)
  linarith

/-- A literal missing descent in an available padded cell produces the gain
in the *whole* simultaneous main update on the keep/suppress coin event. -/
lemma no_descent_gain (c d : CellIndex q L U phase) (hc : Available A S phase c)
    (x : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    (ii : Fin (k+1)) (T : ℝ)
    (hx : x.column ∈ ColumnOrder.componentColumns c.2.2)
    (hy : T ∈ domain phase d ii)
    (hpx : Tiling.Padded a₁ q x.height (a₁/10)) (hpy : Tiling.Padded a₁ q T (a₁/10))
    (hr : BandTrees.RadialInterior D (phase c.1) x)
    (hn : S.name ii T=index A S phase c hc)
    (hT : T ∈ (S.chart (index A S phase c hc)).band)
    (hclose : |(S.chart (index A S phase c hc)).comparison.eval
        (x.widen (sub_old A S phase c hc))-
        (S.chart (index A S phase c hc)).comparison.value ii ⟨T,hT⟩| ≤ EA)
    (hno : ¬Nonempty ((S.chart (index A S phase c hc)).comparison.BandDescent
      (BandTrees.band broad (lower q L U c.1.1)) (x.widen (sub_old A S phase c hc)) epsilon))
    (hon : (omega c).2.2=true) (hoff : (omega d).2.2=false) :
    kappaA*EA < (∫ w, |((batch A S phase hm omega).sets.activity w).indicator x.column x.height-
      ((batch A S phase hm omega).sets.activity w).indicator ii T| ∂(μ.prod Threshold.fair)) := by
  let ck : Kept A S phase omega := ⟨c,hc,hon⟩
  let V := keptStep A S phase hm omega ck
  have hxi : x.height ∈ domain phase c x.column := (MainCell.mem_domain _ _ _).mpr ⟨hx,x.inBand⟩
  rw [batch_pair_kept_suppressed A S phase hm omega ck d _ _ _ _ hxi hy hpy hoff]
  have hout : T ∉ domain phase c ii := by
    intro hzc
    have he := unique_at_padded phase hpy hy hzc
    rw [he,hon] at hoff
    cases hoff
  have hr' : BandTrees.RadialInterior (1/1000) (phase c.1) x := by
    norm_num [D] at hr ⊢
    exact hr
  have hp := BandTrees.radialInterior_padding (by norm_num) (by norm_num [a₁]) x hr' c.2 hx
  apply V.pair_separation_external x ii T hT hx hout hn (by norm_num [kappaA,a₁])
    (ε := epsilon) (by norm_num [epsilon]) (by norm_num [epsilon]) rfl rfl hclose
    (kept_shield A S phase hm omega ck x hxi hpx) _ _ hno
  · change radial phase c+1/100000+2*a₁ < BandTrees.radialValue x
    norm_num [radial] at hp ⊢
    exact hp.1
  · change BandTrees.radialValue x < radial phase c+1/1000-1/100000-2*a₁
    norm_num [radial] at hp ⊢
    exact hp.2

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) 

lemma no_descent_probability (c d : CellIndex q L U phase) (hc : Available A S phase c)
    (x : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2))
    (ii : Fin (k+1)) (T : ℝ)
    (hx : x.column ∈ ColumnOrder.componentColumns c.2.2)
    (hy : T ∈ domain phase d ii)
    (hpx : Tiling.Padded a₁ q x.height (a₁/10)) (hpy : Tiling.Padded a₁ q T (a₁/10))
    (hr : BandTrees.RadialInterior D (phase c.1) x)
    (hn : S.name ii T=index A S phase c hc)
    (hT : T ∈ (S.chart (index A S phase c hc)).band)
    (hclose : |(S.chart (index A S phase c hc)).comparison.eval
        (x.widen (sub_old A S phase c hc))-
        (S.chart (index A S phase c hc)).comparison.value ii ⟨T,hT⟩| ≤ EA)
    (hno : ¬Nonempty ((S.chart (index A S phase c hc)).comparison.BandDescent
      (BandTrees.band broad (lower q L U c.1.1)) (x.widen (sub_old A S phase c hc)) epsilon))
    (hne : c≠d) :
    1/4 ≤ FiniteRandom.prob (fun omega : Sample phase m =>
      kappaA*EA < (∫ w, |((batch A S phase hm omega).sets.activity w).indicator x.column x.height-
        ((batch A S phase hm omega).sets.activity w).indicator ii T| ∂(μ.prod Threshold.fair))) := by
  rw [←prob_keep_suppress phase m c d hne]
  exact FiniteRandom.prob_mono (fun omega h => no_descent_gain A S phase hm omega c d hc x ii T
    hx hy hpx hpy hr hn hT hclose hno h.1 h.2)

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests VertexBands
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (ha : 1≤dist (v x) (v y))

lemma main_index : MainFamily.index A SA phaseD (mainCell A v hv phaseD x) (main_available A SA SB v hv he)=indexA A SA v x :=
  (MainFamily.same_name A SA phaseD _ (main_available A SA SB v hv he) _ _ (mainCell_mem A v hv phaseD x)).symm

private lemma comparison_coordinates {D E : OrdinaryData M} (hDE : D=E)
    {i j : Fin (k+1)} (hij : i=j) {H T : ℝ} (hHT : H=T) (hD : H∈D.band) (hE : T∈E.band) :
    D.comparison.value i ⟨H,hD⟩=E.comparison.value j ⟨T,hE⟩ := by
  subst E; subst j; subst T; rfl

include hj hc ha in
lemma no_descent_probability {m : ℕ} (hm : 0 < m)
    (hno : ¬Nonempty ((SA.chart (indexA A SA v x)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q x))
      ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA) epsilon)) :
    1/4≤FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      kappaA*EA < (MainFamily.batch A SA phaseD hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height) := by
  let c := mainCell A v hv phaseD x
  let d := mainCell A v hv phaseD y
  let hav := main_available A SA SB v hv he (phaseD := phaseD)
  have hidx := main_index A SA SB v hv he (phaseD := phaseD)
  have hn : SA.name (v y).column (v y).height=MainFamily.index A SA phaseD c hav :=
    (he.namesA A SA SB v).trans hidx.symm
  have hT : (v y).height∈(SA.chart (MainFamily.index A SA phaseD c hav)).band := by
    rw [←hn]; exact SA.height_in _ _
  have hclose : |(SA.chart (MainFamily.index A SA phaseD c hav)).comparison.eval
      ((point A v L U hv q x).widen (MainFamily.sub_old A SA phaseD c hav))-
      (SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value
        (v y).column ⟨(v y).height,hT⟩|≤EA := by
    have hx := comparison_coordinates (congrArg SA.chart hidx) (i := (v x).column) rfl
      (H := (v x).height) rfl
      (MainFamily.sub_old A SA phaseD c hav (height_mem A v L U hv q x)) (SA.height_in _ _)
    have hy := comparison_coordinates (congrArg SA.chart (hidx.trans (he.namesA A SA SB v).symm))
      (i := (v y).column) rfl (H := (v y).height) rfl hT (SA.height_in _ _)
    change |(SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v x).column _-
      (SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v y).column _|≤EA
    have hb : |(SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v x).column ⟨(v x).height,MainFamily.sub_old A SA phaseD c hav (height_mem A v L U hv q x)⟩ - (SA.chart (MainFamily.index A SA phaseD c hav)).comparison.value (v y).column ⟨(v y).height,hT⟩| ≤ EA := by
      rw [hx,hy]
      exact hc.2.1.le
    exact hb
  apply MainFamily.no_descent_probability A SA phaseD hm c d hav (point A v L U hv q x)
    (v y).column (v y).height (mainCell_column A v hv phaseD x) (mainCell_mem A v hv phaseD y)
    hi.1 hj.1 hi.2.2.1 hn hT hclose _
    (MainFamily.distinct_cells A phaseD (v x) (v y) ha c d (mainCell_mem A v hv phaseD x) (mainCell_mem A v hv phaseD y))
  intro h
  apply hno
  exact OrdinaryData.descent_coordinates (congrArg SA.chart hidx) rfl _ _ h rfl rfl
end PlanarL1.Columns.Model.PairGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryGain
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable (hp : Tiling.Padded a₁ q c.height (a₁/10)) (hn : Tiling.Padded a₂ p c.height (a₂/10))
include hc hp hn

lemma localHit_injective : Function.Injective
    (localHit A SA SB v hv b c hc hp hn (phaseD := phaseD) (phaseG := phaseG)) := by
  intro i j he
  have hi := touch_block A SA SB v hv b c hc hp hn i.property
  have hj := touch_block A SA SB v hv b c hc hp hn j.property
  rcases i with ⟨⟨d,i⟩,hi'⟩
  rcases j with ⟨⟨e,j⟩,hj'⟩
  dsimp only at hi hj
  subst d
  subst e
  have hraw : i=j := congrArg Subtype.val he
  subst j
  rfl

/-- Universal packing for the whole actual, finitely selected family. Both
old identifiers are derived by the local packing theorem, not assumed. -/
lemma touching_card : Fintype.card (Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))≤
    SurvivingGroups.packBound := by
  let := SurvivingGroups.instFintypeHits
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c
  have hb := SurvivingGroups.touching_card
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) b.sub c hc
  apply le_trans _ hb
  exact Fintype.card_le_of_injective _ (localHit_injective A SA SB v hv b c hc hp hn)

lemma touching_finset_card :
    (Finset.univ.filter (Touch A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))).card≤
      SurvivingGroups.packBound := by
  simpa only [Hits,Fintype.card_subtype] using touching_card A SA SB v hv b c hc hp hn

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma seed_cellPoint (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C) :
    SecondaryCell.point (G.admittedSeeds positive C) R x.column x.height (G.seed_domain positive C x hx)=x := by
  have hc := SecondaryCell.point_column (G.admittedSeeds positive C) R (G.seed_domain positive C x hx)
  have ht := SecondaryCell.point_height (G.admittedSeeds positive C) R (G.seed_domain positive C x hx)
  generalize SecondaryCell.point (G.admittedSeeds positive C) R x.column x.height
    (G.seed_domain positive C x hx) = y at hc ht ⊢
  cases x
  cases y
  cases hc
  cases ht
  rfl

lemma step_gain (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty)
    (noise : Point.RadialTree.Noise (n := k+1)) (hnoise : (G.tree C).NoiseBounds noise)
    (alpha beta : ℝ) (ha : alpha ≤ EB) (hb : beta ≤ EB) (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C)
    (hl : G.lower+9*a₂/100 ≤ x.height) (hu : x.height ≤ G.lower+a₂-9*a₂/100) :
    G.old positive C x+R/25 < (G.step positive C hC noise hnoise alpha beta ha hb).replacement x := by
  let U := G.step positive C hC noise hnoise alpha beta ha hb
  apply SecondaryCell.replacement_seed U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.zeta_eq (show 0 < R by norm_num [R]) U.radius_small ha0 hb0 U.delta_eq U.noise_bounds hx
    (U.seed_near x hx) _ hl hu
  intro ho
  exact (G.support_seed_near positive C ho x (Finset.mem_filter.mp hx).1).trans (show 10*g ≤ (10/1000000:ℝ)*R by norm_num [g,R])

lemma full_step_gain (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty)
    (noise : Point.RadialTree.Noise (n := k+1)) (hnoise : (G.tree C).NoiseBounds noise)
    (alpha beta : ℝ) (ha : alpha ≤ EB) (hb : beta ≤ EB) (ha0 : 0 ≤ alpha) (hb0 : 0 ≤ beta)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C)
    (hl : G.lower+9*a₂/100 ≤ x.height) (hu : x.height ≤ G.lower+a₂-9*a₂/100) :
    G.old positive C x+R/25 < (G.step positive C hC noise hnoise alpha beta ha hb).fullReplacement
      x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩ := by
  let U := G.step positive C hC noise hnoise alpha beta ha hb
  change G.old positive C x+R/25 < U.fullReplacement x.column
    ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩
  rw [U.fullReplacement_inside x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩
    (show x.height ∈ SecondaryCell.domain U.seeds U.radius x.column from G.seed_domain positive C x hx)]
  change G.old positive C x+R/25 < U.replacement
    (SecondaryCell.point (G.admittedSeeds positive C) R x.column x.height (G.seed_domain positive C x hx))
  have he := G.seed_cellPoint positive C x hx
  rw [he]
  exact G.step_gain positive C hC noise hnoise alpha beta ha hb ha0 hb0 x hx hl hu

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma domain_near (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty) (i : Fin (k+1)) (H : ℝ)
    (hx : H ∈ SecondaryCell.domain (G.admittedSeeds positive C) R i) :
    H ∈ BandTrees.band narrow G.lower ∧ ∃ v ∈ G.seeds,
      ∃ p : M.Path (BandTrees.band narrow G.lower) i v.column, p.length H v.height ≤ R := by
  obtain ⟨x,hi,hH,hd⟩ := (SecondaryCell.mem_domain _ _).mp hx
  obtain ⟨w,hw,he⟩ := SecondaryCell.seedDistance_attained _ hC x
  obtain ⟨v,hv,hc,hvH⟩ := (G.allSeeds_description C w).mp (Finset.mem_filter.mp hw).1
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_Icc w
  refine ⟨hH ▸ x.inBand,v,hv,?_⟩
  have hh := hp.le.trans (he.symm.le.trans hd)
  refine ⟨p.cast hi hc.symm,?_⟩
  calc
    _ = p.length H v.height := PlanarL1.Columns.Model.Path.length_cast p hi hc.symm H v.height
    _ ≤ R := by simpa only [←hH,hvH] using hh

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

lemma domain_touch (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
    (positive : Bool) (C : (group A SA SB v hv i).Component)
    (hC : ((group A SA SB v hv i).admittedSeeds positive C).Nonempty)
    (hd : c.height ∈ SecondaryCell.domain ((group A SA SB v hv i).admittedSeeds positive C) R c.column) :
    Touch A SA SB v hv b c i := by
  obtain ⟨hH,z,hz,path,hpath⟩ := (group A SA SB v hv i).domain_near positive C hC c.column c.height hd
  obtain ⟨w,hw,he⟩ := (SurvivingGroups.seed_mem
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1) i.2).mp hz
  subst z
  refine ⟨hH,w,hw,path,hpath.trans ?_⟩
  norm_num [R]

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S)

/-- A whole secondary group, not only the selected narrow component, stays
away from the other endpoint of a distance-scale pair. -/
lemma far_not_domain (x : M.Point G.broad G.broad_root) (hx : x ∈ G.seeds)
    (j : Fin (k+1)) (T : ℝ) (hfar : 1 ≤ dist (A.point x.column x.height) (A.point j T))
    (positive : Bool) (C : G.Component) (hC : (G.admittedSeeds positive C).Nonempty) :
    T ∉ SecondaryCell.domain (G.admittedSeeds positive C) R j := by
  intro hy
  obtain ⟨y,hj,hT,hd⟩ := (SecondaryCell.mem_domain _ _).mp hy
  obtain ⟨w,hw,he⟩ := SecondaryCell.seedDistance_attained _ hC y
  obtain ⟨v,hv,hc,hH⟩ := (G.allSeeds_description C w).mp (Finset.mem_filter.mp hw).1
  have hvw : A.point v.column v.height=A.point w.column w.height := by rw [hc,hH]
  have h₁ := (MainFamily.ambient_dist_le A x v).trans (G.diameter x hx v hv)
  have h₂ := MainFamily.ambient_dist_le A w y
  rw [dist_comm w y,← he] at h₂
  have htri := dist_triangle (A.point x.column x.height) (A.point v.column v.height) (A.point j T)
  rw [hvw] at h₁
  rw [hvw,←hj,←hT] at htri
  have hsmall : 10*g+R < (1:ℝ) := by norm_num [g,R]
  rw [←hj,←hT] at hfar
  linarith

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Interpolation
lemma maxSelection_ge_member {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (F : X → NamedValue) (hF : F ∈ Fs) (x : X) :
    (F x).value ≤ (maxSelection old Fs x).value := by
  induction Fs with
  | nil => simp at hF
  | cons G gs ih =>
    rw [maxSelection,maxNamed_value]
    rcases List.mem_cons.mp hF with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)
lemma familySelection_ge {X : Type*} {n : ℕ} (old : X → ℝ)
    (F : Fin n → X → NamedValue) (q : Fin n) (x : X) :
    (F q x).value ≤ (familySelection old F x).value :=
  maxSelection_ge_member (fun x => ⟨0,old x⟩)
    (List.ofFn (fun q => fun x => ⟨familyName q (F q x).name,(F q x).value⟩))
    (fun x => ⟨familyName q (F q x).name,(F q x).value⟩)
    (List.mem_ofFn.mpr ⟨q,rfl⟩) x
end PlanarL1.Interpolation

namespace PlanarL1.Columns.Model.BState.SecondaryBatch
open MeasureTheory
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
variable (B : SecondaryBatch S)

lemma selected_ge (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) :
    κ*(B.step q).fullReplacement i (B.groupHeight q H) ≤ (B.selected i H).value := by
  rw [←B.groupNamed_value]
  exact familySelection_ge (fun H => κ*B.comparison.value i H) (fun q => B.groupNamed q i) q H

lemma indicator_inside (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (h : H ∈ B.domain i) :
    (B.patch.apply.activity w).indicator i H=
      Threshold.chartValue H (B.converted i H) ((S.labels B.index).lift.value w) := by
  simp only [Activity.indicator,B.patch.inside h w]
  rfl

lemma indicator_outside (w : Ω × Bool) (j : Fin (k+1)) (T : ℝ)
    (hT : T ∈ B.data.band) (hy : T ∉ B.domain j) (hn : S.name j T=B.index) :
    (B.patch.apply.activity w).indicator j T=
      Threshold.chartValue T (κ*(B.data.offset+B.data.orientation B.positive*
        B.comparison.value j ⟨T,hT⟩)) ((S.labels B.index).lift.value w) := by
  have hr := S.represents_named w.1 j T B.index hn hT
  have he := B.data.comparison_convert lam B.lambda_bound B.positive j ⟨T,hT⟩
  change (S.sets.activity w.1).active j T ↔
    Threshold.active (S.labels B.index) T (κ*B.data.value lam j ⟨T,hT⟩) w.1 at hr
  rw [he] at hr
  have hp := B.patch.unchanged hy w
  simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
  exact if_congr (hp.trans hr) rfl rfl

lemma pair_separation_external (i j : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ B.domain i) (hT : T ∈ B.data.band) (hy : T ∉ B.domain j)
    (hn : S.name j T=B.index) :
    B.patch.apply.separation i H j T=max |H-T|
      |(B.selected i ⟨H,B.domain_band hx⟩).value-κ*B.comparison.value j ⟨T,hT⟩| := by
  unfold SetSystem.separation
  simp_rw [B.indicator_inside _ i H hx,B.indicator_outside _ j T hT hy hn]
  rw [(S.labels B.index).lift.distance,B.converted_on i H (B.domain_band hx)]
  congr 1
  rw [show κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,B.domain_band hx⟩).value-
      κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value j ⟨T,hT⟩)=
      B.data.orientation B.positive*((B.selected i ⟨H,B.domain_band hx⟩).value-
        κ*B.comparison.value j ⟨T,hT⟩) by ring,
    abs_mul,B.data.orientation_unit,one_mul]

/-- Overlapping proposals at the raised endpoint can only help. It is enough
for the other endpoint to stay outside all acting domains of its identifier. -/
lemma gain_external (q : Fin B.count) (i j : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i)
    (hT : T ∈ B.data.band) (hy : T ∉ B.domain j) (hn : S.name j T=B.index)
    {r : ℝ} (hr : 0 < r) (hk : 0 < κ)
    (hclose : |B.comparison.value i ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩-
      B.comparison.value j ⟨T,hT⟩| ≤ r/10000)
    (hgain : (B.step q).comparison.value i
        (B.groupHeight q ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩)+r/25 <
      (B.step q).fullReplacement i
        (B.groupHeight q ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩)) :
    κ*r/50 < B.patch.apply.separation i H j T := by
  rw [B.pair_separation_external i j H T (B.mem_domain.mpr ⟨q,hx⟩) hT hy hn]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  have hs := B.selected_ge q i ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩
  rw [B.step_comparison] at hgain
  have hg := mul_lt_mul_of_pos_left hgain hk
  have hc := mul_le_mul_of_nonneg_left (abs_le.mp hclose).1 hk.le
  have ha := le_abs_self ((B.selected i ⟨H,B.domain_band (B.mem_domain.mpr ⟨q,hx⟩)⟩).value-
    κ*B.comparison.value j ⟨T,hT⟩)
  nlinarith [mul_pos hk hr]
end PlanarL1.Columns.Model.BState.SecondaryBatch

end



section

namespace PlanarL1.Columns.Model.BState.SecondaryLayer
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
variable (L : SecondaryLayer S)

lemma inside (a : Fin (S.count+1)) (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ (L.batch a).domain i) :
    (L.sets.activity w).active i H ↔ ((L.batch a).patch.apply.activity w).active i H :=
  SetPatch.batch_inside _ L.overlap (List.mem_ofFn.mpr ⟨a,rfl⟩) w i H hi

lemma outside (a : Fin (S.count+1)) (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∉ (L.batch a).domain i) (hn : S.name i H=a) :
    (L.sets.activity w).active i H ↔ ((L.batch a).patch.apply.activity w).active i H := by
  apply Iff.trans _ ((L.batch a).patch.unchanged hi w).symm
  apply SetPatch.batch_old _ L.overlap w i H
  intro P hP
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
  apply (L.batch q).patch.unchanged _ w
  intro hq
  have he := (L.batch q).domain_name hq
  rw [L.same_index,hn] at he
  exact hi (he ▸ hq)

lemma pair_external (a : Fin (S.count+1)) (i j : Fin (k+1)) (H T : ℝ)
    (hx : H ∈ (L.batch a).domain i) (hy : T ∉ (L.batch a).domain j)
    (hn : S.name j T=a) :
    L.sets.separation i H j T=(L.batch a).patch.apply.separation i H j T := by
  unfold SetSystem.separation
  congr 1
  funext w
  simp only [Activity.indicator,L.inside a w i H hx,L.outside a w j T hy hn]

end PlanarL1.Columns.Model.BState.SecondaryLayer

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open Parameters MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
variable {m : ℕ} (hm : 0 < m) (omega : Sample G m)

omit [Fintype I] in
lemma actingStep_gain (a : Fin (S.count+1)) (q : Acting G omega a)
    (x : M.Point (BandTrees.band narrow (G q.val.1).lower) ((G q.val.1).root q.val.2))
    (hx : x ∈ (G q.val.1).admittedSeeds (omega.1 a) q.val.2)
    (hl : (G q.val.1).lower+9*a₂/100 ≤ x.height)
    (hu : x.height ≤ (G q.val.1).lower+a₂-9*a₂/100) :
    (actingStep G hm omega a q).comparison.value x.column
      ⟨x.height,(G q.val.1).sub_old ((G q.val.1).narrow_sub x.inBand)⟩+R/25 <
      (actingStep G hm omega a q).fullReplacement x.column
        ⟨x.height,(G q.val.1).sub_old ((G q.val.1).narrow_sub x.inBand)⟩ := by
  exact (G q.val.1).full_step_gain (omega.1 a) q.val.2 q.property.2.2 _ _ _ _ _ _
    (mul_nonneg (div_nonneg interpolationB.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (mul_nonneg (div_nonneg interpolationB.1.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) x hx hl hu

lemma gain_external (a : Fin (S.count+1)) (q : Acting G omega a)
    (x : M.Point (BandTrees.band narrow (G q.val.1).lower) ((G q.val.1).root q.val.2))
    (hx : x ∈ (G q.val.1).admittedSeeds (omega.1 a) q.val.2)
    (hl : (G q.val.1).lower+9*a₂/100 ≤ x.height)
    (hu : x.height ≤ (G q.val.1).lower+a₂-9*a₂/100)
    (j : Fin (k+1)) (T : ℝ) (hT : T ∈ (S.chart a).band)
    (hy : T ∉ (batch G hm omega a).domain j) (hn : S.name j T=a)
    (hclose : ∀ hH : x.height ∈ (S.chart a).band,
      |((S.chart a).comparison Group.lam Group.lam_bound (omega.1 a)).value x.column ⟨x.height,hH⟩-
       ((S.chart a).comparison Group.lam Group.lam_bound (omega.1 a)).value j ⟨T,hT⟩| ≤ R/10000) :
    kappaB*R/50 < (layer G hm omega).sets.separation x.column x.height j T := by
  let e := @Fintype.equivFin (Acting G omega a) (instFintypeActing G omega a)
  have hd : x.height ∈ SecondaryCell.domain ((batch G hm omega a).step (e q)).seeds
      ((batch G hm omega a).step (e q)).radius x.column := by
    change x.height ∈ SecondaryCell.domain
      (G (e.symm (e q)).val.1 |>.admittedSeeds (omega.1 a) (e.symm (e q)).val.2) R x.column
    rw [e.symm_apply_apply]
    exact (G q.val.1).seed_domain (omega.1 a) q.val.2 x hx
  have hdom := (batch G hm omega a).mem_domain.mpr ⟨e q,hd⟩
  rw [(layer G hm omega).pair_external a x.column j x.height T hdom hy hn]
  apply (batch G hm omega a).gain_external (e q) x.column j x.height T hd hT hy hn
    (by norm_num [R]) (by norm_num [kappaB,a₂]) (hclose _) 
  have gain (q' : Acting G omega a) (he : q'=q)
      (H : (actingStep G hm omega a q').data.band) (hH : H.val=x.height) :
      (actingStep G hm omega a q').comparison.value x.column H+R/25 <
        (actingStep G hm omega a q').fullReplacement x.column H := by
    subst q'
    obtain ⟨T,hT⟩ := H
    dsimp only at hH
    subst T
    exact actingStep_gain G hm omega a q x hx hl hu
  exact gain (e.symm (e q)) (e.symm_apply_apply q) _ rfl

end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
variable (x : M.Point (group A SA SB v hv i).broad (group A SA SB v hv i).broad_root)
variable (hx : x ∈ (group A SA SB v hv i).seeds)
variable (hfar : 1≤dist (A.point x.column x.height) (A.point c.column c.height))
variable {m : ℕ} (hm : 0 < m)
variable (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)

include hx hfar in
lemma batch_not_domain (a : Fin (SB.count+1))
    (hs : ∀ j, Touch A SA SB v hv b c j → j≠i → omega.2.1 j=false) :
    c.height ∉ (batch (group A SA SB v hv) hm omega a).domain c.column := by
  intro h
  obtain ⟨n,hn⟩ := (batch (group A SA SB v hv) hm omega a).mem_domain.mp h
  let e := @Fintype.equivFin (Acting (group A SA SB v hv) omega a)
    (instFintypeActing (group A SA SB v hv) omega a)
  let z := e.symm n
  change c.height ∈ SecondaryCell.domain
    ((group A SA SB v hv (e.symm n).val.1).admittedSeeds (omega.1 a) (e.symm n).val.2) R c.column at hn
  change c.height ∈ SecondaryCell.domain
    ((group A SA SB v hv z.val.1).admittedSeeds (omega.1 a) z.val.2) R c.column at hn
  by_cases hz : z.val.1=i
  · have haway (j : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
        (hj : j=i) (C : (group A SA SB v hv j).Component)
        (hC : ((group A SA SB v hv j).admittedSeeds (omega.1 a) C).Nonempty) :
        c.height ∉ SecondaryCell.domain ((group A SA SB v hv j).admittedSeeds (omega.1 a) C) R c.column := by
      subst j
      exact (group A SA SB v hv i).far_not_domain x hx c.column c.height hfar (omega.1 a) C hC
    exact haway z.val.1 hz z.val.2 z.property.2.2 hn
  · have ht := domain_touch A SA SB v hv b c z.val.1 (omega.1 a) z.val.2 z.property.2.2 hn
    have hf := hs z.val.1 ht hz
    have hk := z.property.2.1
    change omega.2.1 z.val.1=true at hk
    rw [hf] at hk
    contradiction
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable

lemma prob_mono_instances {Ω : Type*} (F F' : Fintype Ω) {P Q : Ω → Prop}
    (h : ∀ w, P w → Q w) : @prob Ω F P ≤ @prob Ω F' Q := by
  cases Subsingleton.elim F' F
  exact @prob_mono Ω F P Q h

lemma prob_first {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Λ]
    (P : Ω → Prop) : prob (fun z : Ω × Λ => P z.1)=prob P := by
  rw [←prob_equiv (Equiv.prodComm Λ Ω)]
  exact prob_second P

lemma prob_rectangle {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : Ω → Prop) (Q : Λ → Prop) :
    prob (fun z : Ω × Λ => P z.1 ∧ Q z.2)=prob P*prob Q := by
  rw [prob_prod]
  have he (w : Ω) : prob (fun z : Λ => P w ∧ Q z)=(if P w then (1:ℝ) else 0)*prob Q := by
    by_cases h : P w
    · simp only [h,true_and,ite_true,one_mul]
    · simp only [h,false_and,ite_false,zero_mul,prob_false]
  simp_rw [he]
  rw [←Finset.sum_mul,prob_eq_sum P]
  ring

lemma prob_coin {I : Type*} [Fintype I] (i : I) (b : Bool) :
    prob (fun f : I → Bool => f i=b)=1/2 := by
  simpa using prob_prescribed ({i} : Finset I) (fun _ => b)

lemma prob_keep_outside {I : Type*} [Fintype I] (i : I) (T : Finset I) {N : ℕ}
    (hT : T.card≤N) :
    1/(2:ℝ)^(N+1) ≤ prob (fun f : I → Bool => f i=true ∧ ∀ j ∈ T, j≠i → f j=false) := by
  apply prob_at_least_prescription (insert i T) (fun j => if j=i then true else false)
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro f hf
    refine ⟨?_,?_⟩
    · simpa using hf i (Finset.mem_insert_self _ _)
    · intro j hj hji
      simpa [hji] using hf j (Finset.mem_insert_of_mem hj)
end PlanarL1.FiniteRandom

namespace PlanarL1.Columns.Model.SecondaryGeometry
open Parameters MeasureTheory FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S) (m : ℕ)

lemma prob_orientation_coins (P : (Fin (S.count+1) → Bool) → Prop) (Q : (I → Bool) → Prop) :
    prob (fun omega : Sample G m => P omega.1 ∧ Q omega.2.1)=prob P*prob Q := by
  let e := (Equiv.prodAssoc (Fin (S.count+1) → Bool) (I → Bool)
    (∀ i C, ComponentSample G i C m)).symm
  rw [←prob_equiv e.symm]
  calc
    _ = prob (fun z : (Fin (S.count+1) → Bool) × (I → Bool) => P z.1 ∧ Q z.2) :=
      prob_first _
    _ = _ := prob_rectangle P Q

lemma prob_orient_keep_suppress (a : Fin (S.count+1)) (positive : Bool) (i : I)
    (T : Finset I) {N : ℕ} (hT : T.card≤N) :
    1/(2:ℝ)^(N+2) ≤ prob (fun omega : Sample G m =>
      omega.1 a=positive ∧ omega.2.1 i=true ∧ ∀ j ∈ T, j≠i → omega.2.1 j=false) := by
  rw [prob_orientation_coins G m (fun f => f a=positive) (fun f => f i=true ∧ ∀ j ∈ T, j≠i → f j=false)]
  have hc : prob (fun f : Fin (S.count+1) → Bool => f a=positive)=(1/2:ℝ) := by
    convert prob_coin a positive using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (fun F : Fintype (Fin (S.count+1) → Bool) =>
      @prob _ F (fun f => f a=positive)) (Subsingleton.elim _ _)
  have h := prob_keep_outside i T hT
  calc
    _ = (1/2:ℝ)*(1/2^(N+1)) := by rw [show N+2=(N+1)+1 by omega,pow_succ]; ring
    _ ≤ (1/2:ℝ)*prob (fun f : I → Bool => f i=true ∧ ∀ j ∈ T, j≠i → f j=false) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := congrArg (fun t => t*prob (fun f : I → Bool => f i=true ∧ ∀ j ∈ T, j≠i → f j=false)) hc.symm
end PlanarL1.Columns.Model.SecondaryGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_LocalPersistence
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (T : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)
lemma namedReplacement_eq_old_of_value (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root)
    (he : replacement T S old L ordinary pc radius αo αh lo α x=old x) :
    namedReplacement T S old L ordinary pc radius αo αh lo α x=⟨0,old x⟩ := by
  apply clippedNamed_eq_old_of_value rfl
  exact (namedReplacement_value T S old L ordinary pc radius αo αh lo α x).trans he

lemma namedReplacement_boundary_ball (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    (hL : LipschitzWith 1 L) (hζ : T.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : T.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : T.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (αh lo : ℝ) (x y : M.Point J root) {ρ : ℝ}
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*radius)
    (hy : dist x y ≤ ρ) (hout : radius ≤ seedDistance S y)
    (z : M.Point J root) (hz : dist x z ≤ ρ) (hin : seedDistance S z ≤ radius) :
    namedReplacement T S old L ordinary pc radius αo αh lo α z=⟨0,old z⟩ :=
  namedReplacement_eq_old_of_value T S old L ordinary pc radius αo αh lo α z
    (replacement_boundary_ball T S old L ordinary hS hOld hL hζ hr hαo hδ hα hord hadmit
      αh lo x y hsmall hy hout z hz hin)
end PlanarL1.Columns.Model.SecondaryCell

namespace PlanarL1.Columns.Model.BState
open MeasureTheory PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
namespace SecondaryBatch
variable (B : SecondaryBatch S)
lemma chosen_name (i : Fin (k+1)) (H : B.data.band) (a : B.NewIndex)
    (ha : B.chosen i H.val a) :
    (B.selected i H).name=familyName a.1 (a.2.val+1) := by
  obtain ⟨hb,_,he⟩ := ha
  exact congrArg NamedValue.name he
lemma newIndex_names_injective : Function.Injective (fun a : B.NewIndex => familyName a.1 (a.2.val+1)) := by
  intro a b hab
  obtain ⟨ha,hb⟩ := (familyName_inj a.1 b.1 (by omega) (by omega)).mp hab
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  dsimp only at ha hb
  subst b
  have he : i=j := Fin.ext (by omega)
  subst j
  rfl
lemma chosen_iff_name (i : Fin (k+1)) (H : B.data.band) (a : B.NewIndex) :
    B.chosen i H.val a ↔ (B.selected i H).name=familyName a.1 (a.2.val+1) := by
  constructor
  · exact B.chosen_name i H a
  · intro he
    have hn : (B.selected i H).name≠0 := by rw [he]; exact familyName_ne_zero _ (by omega)
    obtain ⟨b,hb⟩ := B.exists_chosen i H hn
    have he' : b=a := B.newIndex_names_injective ((B.chosen_name i H b hb).symm.trans he)
    exact he' ▸ hb
lemma choose_eq_of_name {i j : Fin (k+1)} (H T : B.data.band)
    (hn : (B.selected i H).name=(B.selected j T).name) :
    B.choose i H.val=B.choose j T.val := by
  have he : B.chosen i H.val=B.chosen j T.val := by
    funext a
    exact propext ((B.chosen_iff_name i H a).trans (hn ▸ (B.chosen_iff_name j T a).symm))
  unfold choose
  simp only [he]
lemma choose_none_of_old_name {i : Fin (k+1)} {H : ℝ} (hne : S.name i H≠B.index) :
    B.choose i H=none := by
  have hn : ¬∃ a, B.chosen i H a := by
    rintro ⟨a,ha⟩
    exact hne (B.domain_name (B.mem_domain.mpr ⟨a.1,B.chosen_domain i H a ha⟩))
  exact dite_eq_right hn
end SecondaryBatch
namespace SecondaryLayer
variable (B : SecondaryLayer S)
lemma choose_eq {i j : Fin (k+1)} {H T : ℝ}
    (he : ∀ a, (B.batch a).choose i H=(B.batch a).choose j T) :
    B.choose i H=B.choose j T := by
  have h : B.chosen i H=B.chosen j T := by
    funext a
    simp only [chosen,he a.1]
  unfold choose
  simp only [h]
lemma name_eq [SFinite μ] {i j : Fin (k+1)} {H T : ℝ}
    (hold : S.name i H=S.name j T) (he : B.choose i H=B.choose j T) :
    B.apply.name i H=B.apply.name j T := by
  dsimp only [apply,BState.append,BState.lift]
  rw [he,hold]
lemma name_eq_of_selected [SFinite μ] {i j : Fin (k+1)} {H T : ℝ}
    (a : Fin (S.count+1)) (hH : H ∈ (B.batch a).data.band) (hT : T ∈ (B.batch a).data.band)
    (hi : S.name i H=a) (hj : S.name j T=a)
    (hn : ((B.batch a).selected i ⟨H,hH⟩).name=((B.batch a).selected j ⟨T,hT⟩).name) :
    B.apply.name i H=B.apply.name j T := by
  apply B.name_eq (hi.trans hj.symm)
  apply B.choose_eq
  intro b
  by_cases hb : b=a
  · subst b
    exact (B.batch a).choose_eq_of_name _ _ hn
  · rw [(B.batch b).choose_none_of_old_name (by simpa only [hi,B.same_index] using Ne.symm hb),
      (B.batch b).choose_none_of_old_name (by simpa only [hj,B.same_index] using Ne.symm hb)]
end SecondaryLayer
end PlanarL1.Columns.Model.BState

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
variable (hp : Tiling.Padded a₁ q c.height ρ) (hn : Tiling.Padded a₂ p c.height τ)
include hc hρ hτ hp hn

lemma localHit_injective_small : Function.Injective
    (localHit_small A SA SB v hv b c hc hρ hτ hp hn (phaseD := phaseD) (phaseG := phaseG)) := by
  intro i j he
  have hi := touch_block_small A SA SB v hv b c hc hρ hτ hp hn i.property
  have hj := touch_block_small A SA SB v hv b c hc hρ hτ hp hn j.property
  rcases i with ⟨⟨d,i⟩,hi'⟩
  rcases j with ⟨⟨e,j⟩,hj'⟩
  dsimp only at hi hj
  subst d
  subst e
  have hraw : i=j := congrArg Subtype.val he
  subst j
  rfl

/-- Universal packing for the whole actual, finitely selected family. Both
old identifiers are derived by the local packing theorem, not assumed. -/
lemma touching_card_small : Fintype.card (Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))≤
    SurvivingGroups.packBound := by
  let := SurvivingGroups.instFintypeHits
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c
  have hb := SurvivingGroups.touching_card
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) b.sub c hc
  apply le_trans _ hb
  exact Fintype.card_le_of_injective _ (localHit_injective_small A SA SB v hv b c hc hρ hτ hp hn)

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.FiniteRandom
attribute [local irreducible] prob
lemma prob_update_bound_pi {I : Type*} {D : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] (i : I) (P : (∀ i, D i) → Prop) {b : ℝ}
    (h : ∀ α, prob (fun r : D i => P (Function.update α i r)) ≤ b) : prob P≤b := by
  classical
  let e := (Equiv.piSplitAt i D).trans (Equiv.prodComm _ _)
  rw [←prob_equiv e.symm P]
  apply prob_prod_bound
  intro rest
  let α : ∀ i, D i := e.symm (rest, Classical.arbitrary (D i))
  have hu (r : D i) : e.symm (rest,r)=Function.update α i r := by
    funext j
    by_cases hj : j=i
    · subst j; simp [e,α,Equiv.piSplitAt]
    · simp [e,α,Equiv.piSplitAt,hj]
  simpa only [hu] using h α
end PlanarL1.FiniteRandom

namespace PlanarL1.Interpolation
attribute [local irreducible] FiniteRandom.prob
lemma familyAtomPair_probability_pi {X I : Type*} {D : I → Type*} {k : ℕ}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (ι : Fin k → I) (hinj : Function.Injective ι)
    (old : X → ℝ) (A : ∀ g : Fin k, D (ι g) → ℕ → X → ℝ) (S : Fin k → Finset ℕ)
    (x : X) {t b : ℝ}
    (hpair : ∀ g i, i ∈ S g → ∀ j, j ∈ S g → i ≠ j →
      FiniteRandom.prob (fun ω => |A g ω i x-A g ω j x| ≤ t) ≤ b)
    (hconst : ∀ g i, i ∈ S g → i ≠ 0 → ∀ c : ℝ,
      FiniteRandom.prob (fun ω => |A g ω i x-c| ≤ t) ≤ b)
    (i j : ℕ) (hi : i ∈ familyNames S) (hj : j ∈ familyNames S) (hne : i ≠ j) :
    FiniteRandom.prob (fun ω : ∀ i, D i =>
      |familyAtom old (fun g => A g (ω (ι g))) i x-familyAtom old (fun g => A g (ω (ι g))) j x| ≤ t) ≤ b := by
  classical
  rcases mem_familyNames.mp hi with rfl | ⟨g,a,ha,rfl⟩
  · obtain ⟨h,c,hc,hcj⟩ := (mem_familyNames.mp hj).resolve_left (Ne.symm hne)
    subst j
    have hc0 : c ≠ 0 := by intro he; subst c; simp only [familyName_zero] at hne; exact hne rfl
    simp only [familyAtom_zero,familyAtom_name old _ h hc0]
    apply FiniteRandom.prob_update_bound_pi (ι h)
    intro ω
    simpa only [Function.update_self,abs_sub_comm] using hconst h c hc hc0 (old x)
  · rcases mem_familyNames.mp hj with rfl | ⟨h,c,hc,rfl⟩
    · have ha0 : a ≠ 0 := by intro he; subst a; simp only [familyName_zero] at hne; exact hne rfl
      simp only [familyAtom_name old _ g ha0,familyAtom_zero]
      apply FiniteRandom.prob_update_bound_pi (ι g)
      intro ω
      simpa only [Function.update_self] using hconst g a ha ha0 (old x)
    · by_cases ha0 : a=0
      · subst a
        have hc0 : c ≠ 0 := by intro he; subst c; simp only [familyName_zero] at hne; exact hne rfl
        simp only [familyName_zero,familyAtom_zero,familyAtom_name old _ h hc0]
        apply FiniteRandom.prob_update_bound_pi (ι h)
        intro ω
        simpa only [Function.update_self,abs_sub_comm] using hconst h c hc hc0 (old x)
      · by_cases hc0 : c=0
        · subst c
          simp only [familyName_zero,familyAtom_zero,familyAtom_name old _ g ha0]
          apply FiniteRandom.prob_update_bound_pi (ι g)
          intro ω
          simpa only [Function.update_self] using hconst g a ha ha0 (old x)
        · simp only [familyAtom_name old _ g ha0,familyAtom_name old _ h hc0]
          by_cases hgh : g=h
          · subst h
            have hac : a ≠ c := by intro he; subst c; exact hne rfl
            apply FiniteRandom.prob_update_bound_pi (ι g)
            intro ω
            simpa only [Function.update_self] using hpair g a ha c hc hac
          · apply FiniteRandom.prob_update_bound_pi (ι g)
            intro ω
            simpa only [Function.update_self,Function.update_of_ne (fun he => hgh (hinj he).symm)] using
              hconst g a ha ha0 (A h (ω (ι h)) c x)


lemma familyNames_card_sparse {k N : ℕ} (S : Fin k → Finset ℕ) (T : Finset (Fin k))
    (hS : ∀ g ∈ T, (S g).card≤N) (hout : ∀ g, g∉T → S g⊆{0}) :
    (familyNames S).card≤1+T.card*N := by
  classical
  have hsub : familyNames S⊆insert 0 (T.biUnion (fun g => (S g).image (familyName g))) := by
    intro i hi
    rcases mem_familyNames.mp hi with rfl | ⟨g,j,hj,rfl⟩
    · exact Finset.mem_insert_self _ _
    · by_cases hg : g∈T
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩)
      · have hj0 : j=0 := Finset.mem_singleton.mp (hout g hg hj)
        rw [hj0,familyName_zero]
        exact Finset.mem_insert_self _ _
  calc
    _ ≤ (insert 0 (T.biUnion (fun g => (S g).image (familyName g)))).card := Finset.card_le_card hsub
    _ ≤ (T.biUnion (fun g => (S g).image (familyName g))).card+1 := Finset.card_insert_le _ _
    _ ≤ (∑ g∈T, ((S g).image (familyName g)).card)+1 := Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _g∈T, N)+1 := Nat.add_le_add_right (Finset.sum_le_sum (fun g hg =>
      (Finset.card_image_le (s := S g) (f := familyName g)).trans (hS g hg))) 1
    _ = 1+T.card*N := by simp [Nat.add_comm]

lemma selection_near_tie_modulus {X : Type*} (F : X → NamedValue)
    (atom : ℕ → X → ℝ) (S : Finset ℕ) (x : X) (P : X → Prop) (hx : P x) {e : ℝ}
    (hF : ∀ z, P z → |(F x).value-(F z).value|≤e)
    (hA : ∀ i∈S, ∀ z, P z → |atom i z-atom i x|≤e)
    (hlist : ∀ z, P z → (F z).name∈S ∧ (F z).value=atom (F z).name z)
    (hbad : ∃ z, P z ∧ (F z).name≠(F x).name) :
    ∃ i∈S, ∃ j∈S, i≠j ∧ |atom i x-atom j x|≤2*e := by
  obtain ⟨z,hz,hn⟩ := hbad
  refine ⟨(F x).name,(hlist x hx).1,(F z).name,(hlist z hz).1,Ne.symm hn,?_⟩
  have hf := hF z hz
  have ha := hA (F z).name (hlist z hz).1 z hz
  rw [←(hlist z hz).2] at ha
  rw [←(hlist x hx).2]
  have ht := abs_sub_le (F x).value (F z).value (atom (F z).name x)
  linarith

lemma selection_probability_modulus {X Ω : Type*} [Fintype Ω]
    (F : Ω → X → NamedValue) (atom : Ω → ℕ → X → ℝ) (S : Finset ℕ)
    (x : X) (P : X → Prop) (hx : P x) {e b : ℝ} (hb : 0≤b)
    (hF : ∀ ω z, P z → |(F ω x).value-(F ω z).value|≤e)
    (hA : ∀ ω i, i∈S → ∀ z, P z → |atom ω i z-atom ω i x|≤e)
    (hlist : ∀ ω z, P z → (F ω z).name∈S ∧ (F ω z).value=atom ω (F ω z).name z)
    (hpair : ∀ i∈S, ∀ j∈S, i≠j →
      FiniteRandom.prob (fun ω => |atom ω i x-atom ω j x|≤2*e)≤b) :
    FiniteRandom.prob (fun ω => ∃ z, P z ∧ (F ω z).name≠(F ω x).name)≤S.card^2*b := by
  apply (FiniteRandom.prob_mono (fun ω h => selection_near_tie_modulus (F ω) (atom ω) S x P hx
    (hF ω) (hA ω) (hlist ω) h)).trans
  exact FiniteRandom.prob_pair_bound S _ hb hpair

lemma maxSelection_modulus {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (x z : X) {e : ℝ}
    (ho : |(old x).value-(old z).value|≤e)
    (hF : ∀ F∈Fs, |(F x).value-(F z).value|≤e) :
    |(maxSelection old Fs x).value-(maxSelection old Fs z).value|≤e := by
  induction Fs with
  | nil => exact ho
  | cons F Fs ih =>
    simp only [maxSelection,maxNamed_value]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hF F (by simp))
      (ih (fun G hG => hF G (List.mem_cons_of_mem _ hG))))

lemma familySelection_modulus {X : Type*} {k : ℕ} (old : X → ℝ)
    (F : Fin k → X → NamedValue) (x z : X) {e : ℝ}
    (ho : |old x-old z|≤e) (hF : ∀ g, |(F g x).value-(F g z).value|≤e) :
    |(familySelection old F x).value-(familySelection old F z).value|≤e := by
  apply maxSelection_modulus _ _ _ _ ho
  intro G hG
  obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
  exact hF g

lemma familyAtom_modulus {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (x z : X) {e : ℝ}
    (ho : |old z-old x|≤e) (hA : ∀ g i, |A g i z-A g i x|≤e) (i : ℕ) :
    |familyAtom old A i z-familyAtom old A i x|≤e := by
  simp only [familyAtom]
  split_ifs with h h'
  · exact ho
  · exact hA _ _
  · exact ho

/-- Sparse, genuinely independent component samples in the literal maximum.
The full family numbering is retained even for groups irrelevant to the ball. -/
lemma familySelection_probability_sparse {X I : Type*} {D : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {k N B : ℕ} (ι : Fin k → I) (hinj : Function.Injective ι)
    (old : X → ℝ) (F : ∀ g : Fin k, D (ι g) → X → NamedValue)
    (A : ∀ g : Fin k, D (ι g) → ℕ → X → ℝ)
    (S : Fin k → Finset ℕ) (T : Finset (Fin k))
    (hcard : ∀ g∈T, (S g).card≤N) (hout : ∀ g, g∉T → S g⊆{0}) (hT : T.card≤B)
    (x : X) (P : X → Prop) (hx : P x) {e b : ℝ} (hb : 0≤b)
    (ho : ∀ z, P z → |old x-old z|≤e)
    (hF : ∀ g ω z, P z → |(F g ω x).value-(F g ω z).value|≤e)
    (hA : ∀ g ω i z, P z → |A g ω i z-A g ω i x|≤e)
    (hzero : ∀ g ω z, A g ω 0 z=old z)
    (hlist : ∀ g ω z, P z → (F g ω z).name∈S g ∧ (F g ω z).value=A g ω (F g ω z).name z)
    (hpair : ∀ g i, i∈S g → ∀ j, j∈S g → i≠j →
      FiniteRandom.prob (fun ω => |A g ω i x-A g ω j x|≤2*e)≤b)
    (hconst : ∀ g i, i∈S g → i≠0 → ∀ c : ℝ,
      FiniteRandom.prob (fun ω => |A g ω i x-c|≤2*e)≤b) :
    FiniteRandom.prob (fun ω : ∀ i, D i => ∃ z, P z ∧
      (familySelection old (fun g => F g (ω (ι g))) z).name≠
        (familySelection old (fun g => F g (ω (ι g))) x).name) ≤ (1+B*N : ℕ)^2*b := by
  have hp := selection_probability_modulus
    (fun ω : ∀ i, D i => familySelection old (fun g => F g (ω (ι g))))
    (fun ω => familyAtom old (fun g => A g (ω (ι g)))) (familyNames S) x P hx hb
    (fun ω z hz => familySelection_modulus old _ x z (ho z hz) (fun g => hF g _ z hz))
    (fun ω i _ z hz => familyAtom_modulus old _ x z ((abs_sub_comm _ _).trans_le (ho z hz))
      (fun g j => hA g _ j z hz) i)
    (fun ω z hz => familySelection_list old _ _ S (fun g y => hzero g _ y) z (fun g => hlist g _ z hz))
    (fun i hi j hj hij => familyAtomPair_probability_pi ι hinj old A S x hpair hconst i j hi hj hij)
  refine hp.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg (familyNames S).card) ?_ 2) hb)
  exact_mod_cast (familyNames_card_sparse S T hcard hout).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right N hT) 1)
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Interpolation

lemma LocalList.family_probability {X I : Type*} {D : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {k N B : ℕ} (ι : Fin k → I) (hinj : Function.Injective ι)
    (old : X → ℝ) (F : ∀ g : Fin k, D (ι g) → X → NamedValue)
    (x : X) {e b : ℝ} (hb : 0≤b) (ho : ∀ z, |old x-old z|≤e)
    (L : ∀ g, LocalList old (F g) x e b) (T : Finset (Fin k))
    (hc : ∀ g∈T, (L g).names.card≤N) (hout : ∀ g, g∉T → (L g).names⊆{0}) (hT : T.card≤B) :
    FiniteRandom.prob (fun w : ∀ i, D i => ∃ z,
      (familySelection old (fun g => F g (w (ι g))) z).name≠
        (familySelection old (fun g => F g (w (ι g))) x).name)≤(1+B*N : ℕ)^2*b := by
  simpa only [true_and] using familySelection_probability_sparse ι hinj old F
    (fun g => (L g).atom) (fun g => (L g).names) T hc hout hT x (fun _ => True) trivial hb
    (fun z _ => ho z) (fun g w z _ => (L g).field_variation w z)
    (fun g w i z _ => (L g).atom_variation w i z) (fun g => (L g).zero)
    (fun g w z _ => (L g).selected w z) (fun g => (L g).pair_test) (fun g => (L g).constant_test)
end PlanarL1.Interpolation

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ)

/-- Literal secondary field has a bounded local atom expansion on any lifted
ball. The chosen radial node and the whole list precede all fresh offsets. -/
lemma sampled_local_list {X : Type*} (lift : X → M.Point J root) (x : X) {ρ : ℝ}
    (hρ : 0≤ρ) (hs : ρ≤R.radius) (hd : ∀ z, dist (lift x) (lift z)≤ρ)
    (ordinary : Bool) (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (hζ : R.ζ=(1:ℝ)/10) (pc radius lo B : ℝ) (hB : 0 < B) (m : ℕ) (hm : 0 < m) :
    ∃ C : LocalList (fun z => old (lift z))
      (fun (w : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) × Fin (m+1)) z =>
        namedReplacement R S old L ordinary pc radius (B/m*w.2.1.val) (B/m*w.2.2.val) lo
          (R.gridNoise R.depthCap m w.1) (lift z)) x ((replacementConstant R : ℝ)*ρ)
      (((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q)+(4*(replacementConstant R : ℝ)*ρ+B/m)/B),
      C.names.card≤6*(R.lookback+1)+3 := by
  classical
  obtain ⟨k,A,hlo,heq⟩ := R.common_formula (lift x) hρ hs
  have hk : k < R.depthCap := (R.depth_le_layerDepth (lift x) (hlo _ (by simpa using hρ))).trans_lt
    (R.layerDepth_lt_cap _)
  let atom := fun (w : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) × Fin (m+1))
    (i : ℕ) z => localAtom R S old L A pc radius (B/m*w.2.1.val) (B/m*w.2.2.val) lo
      (R.gridNoise R.depthCap m w.1) i (lift z)
  have ha (w : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) × Fin (m+1)) (i : ℕ) : LipschitzWith (replacementConstant R)
      (localAtom R S old L A pc radius (B/m*w.2.1.val) (B/m*w.2.2.val) lo
        (R.gridNoise R.depthCap m w.1) i) := localAtom_lipschitz R S old L hOld hL A _ _ _ _ _ _ i
  refine ⟨{ names := secondaryNames (R.recentNames A R.lookback)
            atom := atom
            zero := ?_
            selected := ?_
            field_variation := ?_
            atom_variation := ?_
            pair_test := ?_
            constant_test := ?_ }, ?_⟩
  · intro w z
    simp [atom,localAtom,secondaryAtom]
  · intro w z
    exact namedReplacement_local_list R S old L hζ A (lift x) hlo heq ordinary _ _ _ _ _ _
      (R.gridNoise_bounds _ _ hm _) (lift z) (hd z)
  · intro w z
    exact ((sampledReplacement_lipschitz R S old L ordinary hOld hL pc radius lo B _ m hm w).dist_le_mul
      (lift x) (lift z)).trans (mul_le_mul_of_nonneg_left (hd z) (NNReal.coe_nonneg _))
  · intro w i z
    have hh := (ha w i).dist_le_mul (lift z) (lift x)
    rw [Real.dist_eq,dist_comm (lift z)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hd z) (NNReal.coe_nonneg _))
  · intro i hi j hj hij
    simpa only [atom,show 2*(2*((replacementConstant R : ℝ)*ρ))=4*(replacementConstant R : ℝ)*ρ by ring] using
      localAtomPair_probability R S old L A (lift x) pc radius lo B hB _ m hk hm i j hi hj hij
        (show 0≤2*((replacementConstant R : ℝ)*ρ) by positivity)
  · intro i hi hi0 c
    simpa only [atom,show 2*(2*((replacementConstant R : ℝ)*ρ))=4*(replacementConstant R : ℝ)*ρ by ring] using
      localAtomConstant_probability R S old L A (lift x) pc radius lo B hB _ m hk hm i hi hi0 c
        (show 0≤2*((replacementConstant R : ℝ)*ρ) by positivity)
  · exact (secondaryNames_card _).trans (Nat.add_le_add_right (R.recentNames_card A R.lookback) 3)
end PlanarL1.Columns.Model.SecondaryCell

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_FamilyPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace SecondaryCell
variable {J : Set ℝ} {root : Fin (k+1)}
lemma mem_domain_iff_distance (seeds : Finset (M.Point J root)) (radius : ℝ)
    (x : M.Point J root) : x.height ∈ domain seeds radius x.column ↔ seedDistance seeds x ≤ radius := by
  constructor
  · intro h
    obtain ⟨z,hc,hH,hd⟩ := (mem_domain seeds radius).mp h
    exact Point.eq_of_coordinates z x hc hH ▸ hd
  · intro h
    exact (mem_domain seeds radius).mpr ⟨x,rfl,rfl,h⟩
lemma point_eq (seeds : Finset (M.Point J root)) (radius : ℝ) (x : M.Point J root)
    (h : x.height ∈ domain seeds radius x.column) : point seeds radius _ _ h=x :=
  Point.eq_of_coordinates _ _ (point_column _ _ _) (point_height _ _ _)
end SecondaryCell
namespace BState.SecondaryStep
open PlanarL1.Interpolation
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)
lemma fullNamed_at (z : M.Point J root) (hz : SecondaryCell.seedDistance U.seeds z≤U.radius) :
    U.fullNamed z.column ⟨z.height,U.sub_old z.inBand⟩=U.named z := by
  have hd := (SecondaryCell.mem_domain_iff_distance U.seeds U.radius z).mpr hz
  simp only [fullNamed,dite_eq_left hd,SecondaryCell.point_eq]

/-- A crossed seed-domain is identically old on the small ball, including its
actual deterministic branch name. No independence or pruning assumption. -/
lemma fullNamed_boundary_ball (x y : M.Point J root) {ρ : ℝ}
    (hsmall : 18*ρ≤(199/1000:ℝ)*U.radius) (hy : dist x y≤ρ)
    (hout : y.height ∉ SecondaryCell.domain U.seeds U.radius y.column)
    (z : M.Point J root) (hz : dist x z≤ρ) :
    U.fullNamed z.column ⟨z.height,U.sub_old z.inBand⟩=⟨0,U.old z⟩ := by
  by_cases hd : z.height ∈ SecondaryCell.domain U.seeds U.radius z.column
  · have hin := (SecondaryCell.mem_domain_iff_distance U.seeds U.radius z).mp hd
    rw [U.fullNamed_at z hin]
    have hyout : U.radius≤SecondaryCell.seedDistance U.seeds y := le_of_lt (lt_of_not_ge
      (fun h => hout ((SecondaryCell.mem_domain_iff_distance U.seeds U.radius y).mpr h)))
    exact SecondaryCell.namedReplacement_boundary_ball U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.seeds_nonempty U.old_lipschitz U.support_lipschitz U.zeta_eq U.radius_nonneg
      U.ordered_bound U.delta_eq U.noise_bounds U.support_le U.admitted U.shield_offset U.lo
      x y hsmall hy hyout z hz hin
  · rw [fullNamed,dite_eq_right hd]
    rfl
end BState.SecondaryStep
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
variable (hp : Tiling.Padded a₂ p x.height ρ)
variable (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
variable (positive : Bool) (C : (group A SA SB v hv i).Component)
variable {z : M.Point Set.univ A.root} (hz : dist x z≤ρ)
variable (hd : z.height ∈ SecondaryCell.domain ((group A SA SB v hv i).admittedSeeds positive C) R z.column)
include hρ hp hz hd
lemma group_touched_band : i.1.2.val.val=Tiling.index a₂ p x.height := by
  apply Tiling.near_band_unique interpolationB.2.1 hρ hp _
    (i.1.narrow_eq ▸ SecondaryCell.inBand_of_mem _ _ hd)
  rw [abs_sub_comm]
  exact (x.height_change_le z).trans hz
lemma group_touched_envelope : ∀ H, |H-x.height|≤ρ → H ∈ BandTrees.band narrow (group A SA SB v hv i).lower := by
  intro H hH
  have he := group_touched_band A SA SB v hv x hρ hp i positive C hz hd
  have hb := Tiling.near_mem_band interpolationB.2.1 hρ hp hH
  rw [←he,←i.1.narrow_eq] at hb
  exact hb
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace Field
lemma ball_variation {J : Set ℝ} {r : Fin (k+1)} {K : ℝ≥0} (F : M.Field J K)
    (x z : M.Point Set.univ r) {ρ : ℝ} (hρ : 0≤ρ)
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J) (hz : dist x z≤ρ) :
    ∃ (hx : x.height ∈ J) (hZ : z.height ∈ J),
      |F.value x.column ⟨x.height,hx⟩-F.value z.column ⟨z.height,hZ⟩|≤(K:ℝ)*ρ := by
  have hx := hJ x.height (by simpa using hρ)
  have hZ := hJ z.height (by rw [abs_sub_comm]; exact (x.height_change_le z).trans hz)
  obtain ⟨p,_,hp⟩ := x.exists_shortest isClosed_univ z
  obtain ⟨q,hq⟩ := p.restrict_of_length x.height z.height x.height ρ hJ (by simpa [hp] using hz)
  refine ⟨hx,hZ,(F.path_bound q ⟨x.height,hx⟩ ⟨z.height,hZ⟩).trans ?_⟩
  rw [hq,hp]
  exact mul_le_mul_of_nonneg_left hz (NNReal.coe_nonneg K)
end Field
namespace BState.SecondaryStep
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root r : Fin (k+1)}
variable (U : SecondaryStep S J root)

lemma point_dist (x z : M.Point Set.univ r) {ρ : ℝ}
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J) (hz : dist x z≤ρ)
    (hx : x.height ∈ SecondaryCell.domain U.seeds U.radius x.column)
    (hZ : z.height ∈ SecondaryCell.domain U.seeds U.radius z.column) :
    dist (SecondaryCell.point U.seeds U.radius _ _ hx) (SecondaryCell.point U.seeds U.radius _ _ hZ)=dist x z := by
  obtain ⟨z',hc,hH,hd⟩ := Point.local_point x z (SecondaryCell.point _ _ _ _ hx)
    (SecondaryCell.point_column _ _ _) (SecondaryCell.point_height _ _ _) isClosed_univ
    (Set.subset_univ _) hJ hz
  have he : z'=SecondaryCell.point U.seeds U.radius _ _ hZ := Point.eq_of_coordinates _ _
    (hc.trans (SecondaryCell.point_column _ _ _).symm) (hH.trans (SecondaryCell.point_height _ _ _).symm)
  rwa [he] at hd

/-- Crossing the domain anywhere on the ambient small ball makes this actual
proposal identically old on that ball. Intrinsic paths are derived by height
padding, rather than silently identified with ambient paths. -/
lemma fullNamed_boundary_global (x y z : M.Point Set.univ r) {ρ : ℝ} (hρ : 0≤ρ)
    (hJ : ∀ H, |H-x.height|≤ρ → H ∈ J)
    (hsmall : 18*ρ≤(199/1000:ℝ)*U.radius) (hy : dist x y≤ρ)
    (hout : y.height ∉ SecondaryCell.domain U.seeds U.radius y.column)
    (hz : dist x z≤ρ) (hZ : z.height ∈ U.data.band) :
    U.fullNamed z.column ⟨z.height,hZ⟩=⟨0,U.comparison.value z.column ⟨z.height,hZ⟩⟩ := by
  by_cases hd : z.height ∈ SecondaryCell.domain U.seeds U.radius z.column
  · let zp := SecondaryCell.point U.seeds U.radius _ _ hd
    obtain ⟨xp,hxc,hxh⟩ := Point.local_center x z zp
      (SecondaryCell.point_column _ _ _) (SecondaryCell.point_height _ _ _) hρ hJ hz
    obtain ⟨yp,hyc,hyh,hdy⟩ := Point.local_point x y xp hxc hxh isClosed_univ (Set.subset_univ _) hJ hy
    obtain ⟨zz,hzc,hzh,hdz⟩ := Point.local_point x z xp hxc hxh isClosed_univ (Set.subset_univ _) hJ hz
    have hout' : yp.height ∉ SecondaryCell.domain U.seeds U.radius yp.column := by rwa [hyc,hyh]
    have he := U.fullNamed_boundary_ball xp yp hsmall (hdy.le.trans hy) hout' zz (hdz.le.trans hz)
    have hzz : zz.column=z.column := hzc
    have hZZ : zz.height=z.height := hzh
    simpa only [hzz,hZZ,old] using he
  · rw [fullNamed,dite_eq_right hd]
end BState.SecondaryStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Parameters
open scoped NNReal
lemma secondaryTestLoss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ secondaryTestLoss ρ m := by
  unfold secondaryTestLoss
  positivity [show 0 < secondaryQ by norm_num [secondaryQ,zetaB,EB,R],interpolationB.1]
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S) (positive : Bool) (C : G.Component)
variable (hC : (G.admittedSeeds positive C).Nonempty) {m : ℕ} (hm : 0  <  m)

variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0 ≤ ρ)
variable (hBand : ∀ z : Ball x (ρ := ρ), z.val.height∈G.data.band)

lemma component_local_list
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
    (hOld : ∀ z, |G.oldOnBall positive x hBand (ballCenter x hρ)-G.oldOnBall positive x hBand z| ≤ (secondaryK:ℝ)*ρ)
    (hEnv : (∃ z : Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column) →
      ∀ H, |H-x.height| ≤ ρ → H ∈ BandTrees.band narrow G.lower) :
    ∃ L : LocalList (G.oldOnBall positive x hBand) (G.sampledOnBall positive C hC hm x hBand)
      (ballCenter x hρ) ((secondaryK:ℝ)*ρ) (secondaryTestLoss ρ m),
      L.names.card ≤ secondaryN ∧
      ((¬∀ z : Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column) → L.names={0}) := by
  classical
  by_cases hfull : ∀ z : Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column
  · let lift := fun z : Ball x (ρ := ρ) => SecondaryCell.point _ _ _ _ (hfull z)
    let w0 : Offset G C (m := m) := Classical.arbitrary _
    let U := G.sampledStep positive C hC hm w0
    have hJ := hEnv ⟨ballCenter x hρ,hfull _⟩
    have hdist z : dist (lift (ballCenter x hρ)) (lift z) ≤ ρ := by
      have he := U.point_dist x z.val hJ z.property (hfull (ballCenter x hρ)) (hfull z)
      exact he.le.trans z.property
    have hrad : ρ ≤ U.tree.radius := hr
    have hex := SecondaryCell.sampled_local_list U.tree U.seeds U.old U.supportValue lift
      (ballCenter x hρ) hρ hrad hdist U.data.isOrdinary U.old_lipschitz U.support_lipschitz U.zeta_eq
      U.pc U.radius U.lo EB interpolationB.1 m hm
    have ho : (fun z => U.old (lift z))=G.oldOnBall positive x hBand := by
      funext z
      simp only [BState.SecondaryStep.old,lift,SecondaryCell.point_column,SecondaryCell.point_height]
      rfl
    have hf : (fun (w : Offset G C (m := m)) z =>
        SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue U.data.isOrdinary U.pc U.radius
          (EB/m*w.2.1.val) (EB/m*w.2.2.val) U.lo (U.tree.gridNoise U.tree.depthCap m w.1) (lift z))=
        G.sampledOnBall positive C hC hm x hBand := by
      funext w z
      unfold sampledOnBall BState.SecondaryStep.fullNamed
      split
      · rfl
      · rename_i hn
        exact False.elim (hn (hfull z))
    have heK : SecondaryCell.replacementConstant U.tree=secondaryK := rfl
    have heQ : U.tree.q=secondaryQ := rfl
    erw [ho,hf,heK,heQ] at hex
    obtain ⟨L,hh⟩ := hex
    exact ⟨L,hh,fun hn => False.elim (hn hfull)⟩
  · have he : G.sampledOnBall positive C hC hm x hBand=fun (_ : Offset G C (m := m)) z =>
        ⟨0,G.oldOnBall positive x hBand z⟩ := by
      funext w z
      obtain ⟨y,hy⟩ := not_forall.mp hfull
      by_cases hz : z.val.height∈SecondaryCell.domain (G.admittedSeeds positive C) R z.val.column
      · exact (G.sampledStep positive C hC hm w).fullNamed_boundary_global x y.val z.val hρ
          (hEnv ⟨z,hz⟩) hsmall y.property hy z.property (hBand z)
      · unfold sampledOnBall BState.SecondaryStep.fullNamed
        split
        · exact False.elim (hz ‹_›)
        · rfl
    rw [he]
    refine ⟨oldLocalList (G.oldOnBall positive x hBand) (ballCenter x hρ) hOld,?_,fun _ => rfl⟩
    change ({0} : Finset ℕ).card ≤ secondaryN
    simp only [Finset.card_singleton]
    unfold secondaryN
    omega
end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Interpolation
lemma maxNamed_scale {c : ℝ} (hc : 0 < c) (a b : NamedValue) :
    maxNamed (scaleNamed c a) (scaleNamed c b)=scaleNamed c (maxNamed a b) := by
  simp only [maxNamed,scaleNamed,mul_lt_mul_iff_right₀ hc,mul_right_inj' hc.ne']
  split_ifs <;> rfl
lemma maxSelection_scale {X : Type*} {c : ℝ} (hc : 0 < c)
    (old : X → NamedValue) (Fs : List (X → NamedValue)) (x : X) :
    maxSelection (fun z => scaleNamed c (old z))
      (Fs.map (fun F z => scaleNamed c (F z))) x=scaleNamed c (maxSelection old Fs x) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simpa only [List.map_cons,maxSelection,ih] using maxNamed_scale hc _ _
lemma familySelection_scale {X : Type*} {k : ℕ} {c : ℝ} (hc : 0 < c)
    (old : X → ℝ) (F : Fin k → X → NamedValue) (x : X) :
    familySelection (fun z => c*old z) (fun g z => scaleNamed c (F g z)) x=
      scaleNamed c (familySelection old F x) := by
  unfold familySelection
  rw [←maxSelection_scale hc]
  congr 2
  rw [List.map_ofFn]
  rfl
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
variable (o : Fin (S.count+1) → Bool) (c : I → Bool) {m : ℕ}
lemma coord_injective (a : Fin (S.count+1)) : Function.Injective (coord G o c (m := m) a) := by
  intro i j he
  apply (Fintype.equivFin (Acting G (fixedSample G o c (m := m)) a)).symm.injective
  exact Subtype.ext he

lemma selected_flat (hm : 0 < m) (w : Offsets G m) (a : Fin (S.count+1))
    (i : Fin (k+1)) (H : (S.chart a).band) :
    ((batch G hm (flatSample G o c w) a).selected i H).name=
      (familySelection (fun T : (S.chart a).band => ((S.chart a).comparison Group.lam Group.lam_bound (o a)).value i T)
        (fun j T => ((G (coord G o c (m := m) a j).1).sampledStep (o a) (coord G o c (m := m) a j).2
          (slot G o c (m := m) a j).property.2.2 hm (w (coord G o c (m := m) a j))).fullNamed i
            ⟨T.val,slot_band G o c (m := m) a j T⟩) H).name := by
  change (familySelection (fun T : (S.chart a).band => kappaB*((S.chart a).comparison Group.lam Group.lam_bound (o a)).value i T)
    (fun j T => scaleNamed kappaB (((G (coord G o c (m := m) a j).1).sampledStep (o a) (coord G o c (m := m) a j).2
      (slot G o c (m := m) a j).property.2.2 hm (w (coord G o c (m := m) a j))).fullNamed i
        ⟨T.val,slot_band G o c (m := m) a j T⟩)) H).name=_
  rw [familySelection_scale (by norm_num [kappaB,a₂])]
  rfl
end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Interpolation
lemma maxSelection_eq_fold {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (x : X) :
    maxSelection old Fs x=(Fs.map (fun F => F x)).foldr maxNamed (old x) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simpa only [maxSelection,List.map_cons,List.foldr_cons] using congrArg (maxNamed (F x)) ih
lemma familySelection_congr_at {X Y : Type*} {k : ℕ} (old : X → ℝ) (old' : Y → ℝ)
    (F : Fin k → X → NamedValue) (F' : Fin k → Y → NamedValue)
    (x : X) (y : Y) (ho : old x=old' y) (hF : ∀ g, F g x=F' g y) :
    familySelection old F x=familySelection old' F' y := by
  simp only [familySelection,maxSelection_eq_fold,List.map_ofFn,ho]
  congr 2
  funext g
  dsimp only [Function.comp_apply]
  rw [hF g]
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters PlanarL1.Interpolation FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
variable (o : Fin (S.count+1) → Bool) (c : I → Bool) {m : ℕ}
variable (a : Fin (S.count+1)) (x : M.Point Set.univ A.root) {ρ : ℝ}
variable (hBand : ∀ z : Group.Ball x (ρ := ρ), z.val.height∈(S.chart a).band)
lemma ballOld_eq (j : Slot G o c a (m := m)) :
    (G (coord G o c (m := m) a j).1).oldOnBall (o a) x (ball_slot_band G o c (m := m) a x hBand j)=ballOld o a x hBand := by
  funext z
  unfold Group.oldOnBall Group.comparison ballOld
  simp only [Group.data]
  have heval (b : Fin (S.count+1)) (hb : z.val.height∈(S.chart b).band) (he : b=a) :
      ((S.chart b).comparison Group.lam Group.lam_bound (o a)).value z.val.column ⟨z.val.height,hb⟩ =
      ((S.chart a).comparison Group.lam Group.lam_bound (o a)).value z.val.column ⟨z.val.height,hBand z⟩ := by
    subst b
    rfl
  exact heval _ _ (coord_index G o c (m := m) a j)
lemma selected_ball (hm : 0 < m) (w : Offsets G m) (z : Group.Ball x (ρ := ρ)) :
    ((batch G hm (flatSample G o c w) a).selected z.val.column ⟨z.val.height,hBand z⟩).name=
      (familySelection (ballOld o a x hBand) (fun j => ballFamily G o c a x hBand hm j (w (coord G o c (m := m) a j))) z).name := by
  apply (selected_flat G o c hm w a z.val.column ⟨z.val.height,hBand z⟩).trans
  apply congrArg NamedValue.name
  refine familySelection_congr_at _ _ _ _ _ _ ?_ ?_
  · rfl
  · intro j
    rfl

lemma persistence_flat [SFinite μ] (hρ : 0 ≤ ρ) (hm : 0 < m)
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
    (hOld : ∀ z, |ballOld o a x hBand (Group.ballCenter x hρ)-ballOld o a x hBand z| ≤ (secondaryK:ℝ)*ρ)
    (hold : ∀ z : Group.Ball x (ρ := ρ), S.name z.val.column z.val.height=a)
    (hEnv : ∀ j : Slot G o c a (m := m),
      (∃ z : Group.Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain
        ((G (coord G o c (m := m) a j).1).admittedSeeds (o a) (coord G o c (m := m) a j).2) R z.val.column) →
      ∀ H, |H-x.height| ≤ ρ → H ∈ BandTrees.band narrow (G (coord G o c (m := m) a j).1).lower)
    {B : ℕ} (hpack : (wholeBallSlots G o c a x (ρ := ρ) (m := m)).card ≤ B) :
    prob (fun w : Offsets G m => ∃ z : Group.Ball x (ρ := ρ),
      (result G hm (flatSample G o c w)).name z.val.column z.val.height≠
        (result G hm (flatSample G o c w)).name x.column x.height) ≤
      (1+B*secondaryN : ℕ)^2*secondaryTestLoss ρ m := by
  classical
  have hList (j : Slot G o c a (m := m)) :
      ∃ L : LocalList (ballOld o a x hBand) (ballFamily G o c a x hBand hm j)
        (Group.ballCenter x hρ) ((secondaryK:ℝ)*ρ) (secondaryTestLoss ρ m),
        L.names.card ≤ secondaryN ∧ (j∉wholeBallSlots G o c a x (ρ := ρ) (m := m) → L.names={0}) := by
    have ho := hOld
    rw [←ballOld_eq G o c (m := m) a x hBand j] at ho
    have he := (G (coord G o c (m := m) a j).1).component_local_list (o a) (coord G o c (m := m) a j).2
      (slot G o c (m := m) a j).property.2.2 hm x hρ (ball_slot_band G o c (m := m) a x hBand j)
      hsmall hr ho (hEnv j)
    erw [ballOld_eq G o c (m := m) a x hBand j] at he
    obtain ⟨L,hN,hout⟩ := he
    exact ⟨L,hN,fun hn => hout (by simpa only [wholeBallSlots,Finset.mem_filter,Finset.mem_univ,true_and] using hn)⟩
  choose L hN hout using hList
  have hprob := LocalList.family_probability (D := fun u : Coordinate G => ComponentSample G u.1 u.2 m)
    (coord G o c (m := m) a) (coord_injective G o c (m := m) a) (ballOld o a x hBand)
    (ballFamily G o c a x hBand hm) (Group.ballCenter x hρ) (secondaryTestLoss_nonneg hρ m) hOld L
    (wholeBallSlots G o c a x (ρ := ρ) (m := m)) (fun j _ => hN j)
    (fun j hj => (hout j hj).le) hpack
  apply (prob_mono (Q := fun w : Offsets G m => ∃ z : Group.Ball x (ρ := ρ),
    (familySelection (ballOld o a x hBand) (fun j => ballFamily G o c a x hBand hm j (w (coord G o c (m := m) a j))) z).name≠
      (familySelection (ballOld o a x hBand) (fun j => ballFamily G o c a x hBand hm j (w (coord G o c (m := m) a j))) (Group.ballCenter x hρ)).name) ?_).trans hprob
  rintro w ⟨z,hz⟩
  refine ⟨z,fun he => hz ?_⟩
  apply (layer G hm (flatSample G o c w)).name_eq_of_selected a (hBand z) (hBand (Group.ballCenter x hρ))
    (hold z) (hold (Group.ballCenter x hρ))
  exact (selected_ball G o c a x hBand hm w z).trans
    (he.trans (selected_ball G o c a x hBand hm w (Group.ballCenter x hρ)).symm)
end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω} {A : Ambient M}
  {S : BState M kappaB lam Ω μ} (G : SecondaryGeometry.Group A S)
lemma component_eq_of_domain (positive : Bool) (C D : G.Component) (i : Fin (k+1)) (H : ℝ)
    (hC : H ∈ SecondaryCell.domain (G.admittedSeeds positive C) R i)
    (hD : H ∈ SecondaryCell.domain (G.admittedSeeds positive D) R i) : C=D := by
  let x := SecondaryCell.point _ _ _ _ hC
  let y := SecondaryCell.point _ _ _ _ hD
  have hc : x.column=i := SecondaryCell.point_column _ _ _
  have hd : y.column=i := SecondaryCell.point_column _ _ _
  have h1 := BandTrees.reachable_mem M narrow G.lower C x.reachable
  have h2 := BandTrees.reachable_mem M narrow G.lower D y.reachable
  rw [hc] at h1
  rw [hd] at h2
  exact ((SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp h1).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff D i).mp h2)
end PlanarL1.Columns.Model.SecondaryGeometry.Group

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
variable (hp : Tiling.Padded a₁ q c.height ρ) (hn : Tiling.Padded a₂ p c.height τ)
variable {m : ℕ} (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)
variable (a : Fin (SB.count+1))

include hc hρ hτ hp hn in
lemma centerActs_card : (centerActs A SA SB v hv b c omega a).card≤SurvivingGroups.packBound := by
  let f : (centerActs A SA SB v hv b c omega a) → Hits A SA SB v hv b c
      (phaseD := phaseD) (phaseG := phaseG) := fun u =>
    ⟨u.val.val.1, domain_touch A SA SB v hv b c _ (omega.1 a) _ u.val.property.2.2
      (Finset.mem_filter.mp u.property).2⟩
  have hf : Function.Injective f := by
    intro u w he
    have hi := congrArg Subtype.val he
    change u.val.val.1=w.val.val.1 at hi
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext hi
    cases u with | mk u hu =>
      cases w with | mk w hw =>
        cases u with | mk u hu' =>
          cases w with | mk w hw' =>
            cases u with | mk i C =>
              cases w with | mk j D =>
                dsimp only at hi
                subst j
                apply heq_of_eq
                exact (group A SA SB v hv i).component_eq_of_domain (omega.1 a) C D c.column c.height
                  (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hw).2
  have he := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at he
  exact he.trans (touching_card_small A SA SB v hv b c hc hρ hτ hp hn)
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root)

lemma center_point_of_domain
    (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
    (positive : Bool) (C : (group A SA SB v hv i).Component)
    (hC : ((group A SA SB v hv i).admittedSeeds positive C).Nonempty)
    (hd : x.height∈SecondaryCell.domain ((group A SA SB v hv i).admittedSeeds positive C) R x.column) :
    ∃ z : M.Point (BandTrees.band broad i.1.lower) (BandTrees.root M broad i.1.lower i.1.1.2),
      z.column=x.column ∧ z.height=x.height ∧ z.height∈BandTrees.band narrow i.1.lower₂ := by
  obtain ⟨hH,w,_,path,_⟩ := (group A SA SB v hv i).domain_near positive C hC x.column x.height hd
  refine ⟨{ column := x.column
            height := x.height
            inBand := i.1.sub hH
            reachable := w.reachable.trans (path.widen i.1.sub).word.reachable.symm }, rfl,rfl,hH⟩

lemma wholeBallSlots_card (o : Fin (SB.count+1) → Bool)
    (coins : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) → Bool)
    (a : Fin (SB.count+1)) {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hn : Tiling.Padded a₂ p x.height ρ) :
    (wholeBallSlots (group A SA SB v hv) o coins a x (ρ := ρ) (m := m)).card ≤ SurvivingGroups.packBound := by
  classical
  let G := group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)
  let T := wholeBallSlots G o coins a x (ρ := ρ) (m := m)
  by_cases he : T.Nonempty
  · obtain ⟨j,hj⟩ := he
    have hd := (Finset.mem_filter.mp hj).2 (Group.ballCenter x hρ)
    obtain ⟨z,hzc,hzh,hzband⟩ := center_point_of_domain A SA SB v hv x (coord G o coins (m := m) a j).1
      (o a) (coord G o coins (m := m) a j).2 (slot G o coins (m := m) a j).property.2.2 hd
    let b := (coord G o coins (m := m) a j).1.1
    let omega := fixedSample G o coins (m := m)
    let f : T → centerActs A SA SB v hv b z omega a := fun t =>
      ⟨slot G o coins (m := m) a t.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        change z.height∈SecondaryCell.domain
          ((G (coord G o coins (m := m) a t.val).1).admittedSeeds (o a) (coord G o coins (m := m) a t.val).2) R z.column
        rw [hzc,hzh]
        exact (Finset.mem_filter.mp t.property).2 (Group.ballCenter x hρ)⟩⟩
    have hf : Function.Injective f := by
      intro s t he
      apply Subtype.ext
      exact (Fintype.equivFin (Acting G omega a)).symm.injective (congrArg Subtype.val he)
    have hh := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe,Fintype.card_coe] at hh
    exact hh.trans (centerActs_card A SA SB v hv b z hzband hρ hρ
      (by simpa only [hzh] using hp) (by simpa only [hzh] using hn) omega a)
  · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)).le.trans (Nat.zero_le _)
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Parameters
open scoped NNReal
lemma mainQ_pos : 0 < mainQ := by norm_num [mainQ,zetaA,EA,epsilon]
lemma secondaryQ_pos : 0 < secondaryQ := by norm_num [secondaryQ,zetaB,EB,R]
lemma persistence_main_small {ρ : ℝ} (h : ρ≤persistenceRadius) : 4*ρ<3*EA := by
  have h' := h.trans (min_le_left _ _)
  have hE := interpolationA.1
  linarith
lemma persistence_main_radius {ρ : ℝ} (h : ρ≤persistenceRadius) : ρ ≤ mainRadius :=
  h.trans (le_trans (min_le_right (EA/20) _) (min_le_left mainRadius _))
lemma persistence_secondary_small {ρ : ℝ} (h : ρ≤persistenceRadius) : 18*ρ≤(199/1000:ℝ)*R := by
  have h' := h.trans (le_trans (min_le_right (EA/20) _) (le_trans (min_le_right mainRadius _) (min_le_left ((199/18000:ℝ)*R) _)))
  linarith
lemma persistence_secondary_radius {ρ : ℝ} (h : ρ≤persistenceRadius) : ρ ≤ secondaryRadius :=
  h.trans (le_trans (min_le_right (EA/20) _) (le_trans (min_le_right mainRadius _) (min_le_right ((199/18000:ℝ)*R) _)))
end PlanarL1.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SelectedGain
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.BData
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

lemma comparison_distance (D : BData M) (lam : ℝ≥0) (hlam : lam≤(1:ℝ≥0)/100)
    (positive : Bool) (i j : Fin (k+1)) (H T : D.band) :
    |(D.comparison lam hlam positive).value i H-(D.comparison lam hlam positive).value j T|=
      |D.value lam i H-D.value lam j T| := by
  rw [D.comparison_convert lam hlam positive i H,D.comparison_convert lam hlam positive j T]
  rw [show D.offset+D.orientation positive*(D.comparison lam hlam positive).value i H-
      (D.offset+D.orientation positive*(D.comparison lam hlam positive).value j T)=
      D.orientation positive*((D.comparison lam hlam positive).value i H-
        (D.comparison lam hlam positive).value j T) by ring,
    abs_mul,D.orientation_unit,one_mul]
end PlanarL1.Columns.Model.BData

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG))
variable (w : M.Point (group A SA SB v hv i).broad (group A SA SB v hv i).broad_root)
variable (hw : w ∈ (group A SA SB v hv i).seeds)
variable (hfar : 1≤dist (A.point w.column w.height) (A.point c.column c.height))
variable (C : (group A SA SB v hv i).Component)
variable (x : M.Point (BandTrees.band narrow (group A SA SB v hv i).lower)
  ((group A SA SB v hv i).root C))
variable (positive : Bool) (hx : x ∈ (group A SA SB v hv i).admittedSeeds positive C)
variable (hl : (group A SA SB v hv i).lower+9*a₂/100 ≤ x.height)
variable (hu : x.height ≤ (group A SA SB v hv i).lower+a₂-9*a₂/100)
variable (hT : c.height ∈ (group A SA SB v hv i).data.band)
variable (hn : SB.name c.column c.height=(group A SA SB v hv i).index)
variable (hclose : ∀ hH : x.height ∈ (group A SA SB v hv i).data.band,
    |(group A SA SB v hv i).data.value Group.lam x.column ⟨x.height,hH⟩-
      (group A SA SB v hv i).data.value Group.lam c.column ⟨c.height,hT⟩|≤R/10000)
variable {m : ℕ} (hm : 0 < m)

include hw hfar hx hl hu hn hclose in
lemma gain_of_suppression
    (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)
    (ho : omega.1 (group A SA SB v hv i).index=positive)
    (hk : omega.2.1 i=true)
    (hs : ∀ j, Touch A SA SB v hv b c j → j≠i → omega.2.1 j=false) :
    kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation x.column x.height c.column c.height := by
  let a := (group A SA SB v hv i).index
  have hx' : x ∈ (group A SA SB v hv i).admittedSeeds (omega.1 a) C := by
    rw [ho]
    exact hx
  let z : Acting (group A SA SB v hv) omega a := ⟨⟨i,C⟩,rfl,hk,⟨x,hx'⟩⟩
  have hy := batch_not_domain A SA SB v hv b c i w hw hfar hm omega a hs
  apply gain_external (group A SA SB v hv) hm omega a z x hx' hl hu c.column c.height hT hy hn
  intro hH
  calc
    _ = |(group A SA SB v hv i).data.value Group.lam x.column ⟨x.height,hH⟩-
      (group A SA SB v hv i).data.value Group.lam c.column ⟨c.height,hT⟩| :=
      (group A SA SB v hv i).data.comparison_distance Group.lam Group.lam_bound _ _ _ _ _
    _ ≤ _ := hclose hH

include hw hfar hx hl hu hn hclose in
lemma admitted_probability
    (hc : c.height ∈ BandTrees.band narrow b.lower₂)
    (hp : Tiling.Padded a₁ q c.height (a₁/10)) (hN : Tiling.Padded a₂ p c.height (a₂/10)) :
    1/(2:ℝ)^(SurvivingGroups.packBound+2) ≤ FiniteRandom.prob
      (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
        kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation x.column x.height c.column c.height) := by
  let T := Finset.univ.filter (Touch A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))
  have hcard : T.card≤SurvivingGroups.packBound := touching_finset_card A SA SB v hv b c hc hp hN
  have hprob := prob_orient_keep_suppress (group A SA SB v hv) m (group A SA SB v hv i).index positive i T hcard
  refine hprob.trans (@FiniteRandom.prob_mono_instances (Sample (group A SA SB v hv) m) _ _ _ _ ?_)
  intro omega he
  apply gain_of_suppression A SA SB v hv b c i w hw hfar C x positive hx hl hu hT hn hclose hm omega he.1 he.2.1
  intro j hj hji
  exact he.2.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩) hji
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma endpoint_mem (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) :
    G.endpoint w hw ∈ G.allSeeds (G.componentOf w) :=
  (G.allSeeds_description _ _).mpr ⟨w,hw,rfl,rfl⟩

lemma endpoint_admitted (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) (positive : Bool) :
    G.endpoint w hw ∈ G.admittedSeeds positive (G.componentOf w) ↔
      G.Admitted positive (G.componentOf w) (G.endpoint w hw) := by
  simp only [admittedSeeds,Finset.mem_filter,G.endpoint_mem w hw,true_and]
end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
private lemma bvalue_transport {D E : BData M} (h : D=E) (j : Fin (k+1)) (H : ℝ)
    (hD : H∈D.band) (hE : H∈E.band) :
    D.value Group.lam j ⟨H,hD⟩=E.value Group.lam j ⟨H,hE⟩ := by subst E; rfl

variable (w : Endpoint A SA SB v L U hv q p phaseD phaseG)

lemma groupOf_lower : (group A SA SB v hv (groupOf A SA SB v hv w)).lower=PairGeometry.narrowLower A v p w.val := rfl

lemma selectedPoint_mem : selectedPoint A SA SB v hv w ∈
    (group A SA SB v hv (groupOf A SA SB v hv w)).allSeeds (selectedComponent A SA SB v hv w) :=
  Group.endpoint_mem _ _ _

lemma selectedPoint_plateau :
    (group A SA SB v hv (groupOf A SA SB v hv w)).lower+9*a₂/100≤(selectedPoint A SA SB v hv w).height ∧
    (selectedPoint A SA SB v hv w).height≤(group A SA SB v hv (groupOf A SA SB v hv w)).lower+a₂-9*a₂/100 := by
  have h := (witness A SA SB v hv w).interior.2.1
  have hh := h
  dsimp only [Tiling.Padded] at hh
  change _≤(v w.val).height ∧ (v w.val).height≤_
  rw [groupOf_lower]
  dsimp [PairGeometry.narrowLower]
  have ha : 0<a₂ := by norm_num [a₂]
  constructor <;> linarith [hh.1,hh.2]

variable {y : V}
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)

variable (he : Eligible A SA SB v w.val y) (ha : 1≤dist (v w.val) (v y))
variable (hc : Cutoffs A SA SB v w.val y)
variable (positive : Bool)
variable (had : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted positive
  (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
variable {m : ℕ} (hm : 0 < m)

include hi he ha hc had in
lemma selected_admitted_probability :
    1/(2:ℝ)^(SurvivingGroups.packBound+2) ≤ FiniteRandom.prob
      (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
        kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
          (v w.val).column (v w.val).height (v y).column (v y).height) := by
  let b := blockFor A v hv hi
  let c := VertexBands.point A v L U hv q y
  let i := groupOf A SA SB v hv w
  let G := group A SA SB v hv i
  have hT : c.height∈G.data.band := by
    change (v y).height∈(SB.chart (indexB A SB v w.val)).band
    rw [←he.namesB A SA SB v]
    exact SB.height_in _ _
  have hn : SB.name c.column c.height=G.index := he.namesB A SA SB v
  have hfar : 1≤dist (A.point (rawSeed A SA SB v hv w).point.column (rawSeed A SA SB v hv w).point.height)
      (A.point c.column c.height) := by
    change 1≤dist (A.point (v w.val).column (v w.val).height) (A.point (v y).column (v y).height)
    simpa only [A.coordinate_point] using ha
  have had' : selectedPoint A SA SB v hv w ∈ G.admittedSeeds positive (selectedComponent A SA SB v hv w) :=
    (Group.endpoint_admitted _ _ _ _).mpr had
  have hclose (hH : (selectedPoint A SA SB v hv w).height∈G.data.band) :
      |G.data.value Group.lam (selectedPoint A SA SB v hv w).column ⟨(selectedPoint A SA SB v hv w).height,hH⟩-
        G.data.value Group.lam c.column ⟨c.height,hT⟩|≤R/10000 := by
    change |fullValue A SB v w.val-(SB.chart (indexB A SB v w.val)).value Group.lam (v y).column ⟨(v y).height,hT⟩|≤_
    have hh := bvalue_transport (congrArg SB.chart (he.namesB A SA SB v).symm)
      (v y).column (v y).height hT (SB.height_in _ _)
    rw [hh]
    exact hc.2.2.le
  exact admitted_probability A SA SB v hv b c i (rawSeed A SA SB v hv w).point
    (groupOf_seed A SA SB v hv w) hfar (selectedComponent A SA SB v hv w)
    (selectedPoint A SA SB v hv w) positive had' (selectedPoint_plateau A SA SB v hv w).1
    (selectedPoint_plateau A SA SB v hv w).2 hT hn hclose hm
    (PairGeometry.narrow_height A v p y) hi.1 hi.2.1
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BData
variable {A : Ambient M} (H : A.History (R/200)) (region : Set (M.Point Set.univ A.root))
variable (hcross : ∀ j, 10≤(R/200)*H.radius j)
lemma normalizedIncrement_coordinates {D E : BData M} (h : D=E)
    {i j : Fin (k+1)} {s t : ℝ} (hi : i=j) (hs : s=t)
    (hI : s∈D.band) (hJ : t∈E.band) (e : Bool) :
    (normalizedIncrement H region hcross D e).value i ⟨s,hI⟩=
      (normalizedIncrement H region hcross E e).value j ⟨t,hJ⟩ := by
  subst E; subst j; subst t; rfl
end BData

namespace IncrementStep
variable (A : Ambient M) (S : BState M kappaB SecondaryGeometry.Group.lam Ω μ)
variable (hist : Fin (S.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (S.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))

lemma separation_lower (sign : Fin (S.count+1) → Bool) (a : Fin (S.count+1))
    (i j : Fin (k+1)) (s t : ℝ) (hi : S.name i s=a) (hj : S.name j t=a)
    (hs : s∈(S.chart a).band) (ht : t∈(S.chart a).band) :
    kappaB*|(BData.normalizedIncrement (hist a) (S.region A a) (hcross a) (S.chart a) (sign a)).value i ⟨s,hs⟩-
      (BData.normalizedIncrement (hist a) (S.region A a) (hcross a) (S.chart a) (sign a)).value j ⟨t,ht⟩|≤
      (update A S hist hcross hrec sign).sets.separation i s j t := by
  let F := S.incrementFields A hist sign (by norm_num [R]) (by norm_num [R])
    (by norm_num : (0:ℝ)<1) (by simpa using hcross) SecondaryGeometry.Group.lam_bound
  have he := S.fieldUpdate_separation F verticalB.1 (by norm_num [kappaB,a₂])
    SecondaryGeometry.Group.lam_bound
    (S.increment_boundary (r := 1) A hist sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
      (by simpa using hcross) hrec verticalB.1 SecondaryGeometry.Group.lam_bound
      (by change kappaB*lambda*10≤1/8; norm_num [kappaB,a₂,lambda,R])) i j s t a hi hj
  change (update A S hist hcross hrec sign).sets.separation i s j t=
    max |s-t| |S.newValue F i s-S.newValue F j t| at he
  rw [he,S.newValue_eq F i s a hi,S.newValue_eq F j t a hj,
    ←mul_sub,abs_mul,abs_of_nonneg verticalB.1]
  exact le_max_right _ _

variable {a : Fin (S.count+1)} {D : OrderedData M}
variable (hD : S.chart a=.ordered D) {root : Fin (k+1)} (x y : M.Point D.band root)
variable (hx : A.Common S.name (A.point x.column x.height) 1 a)
variable (hy : A.Common S.name (A.point y.column y.height) 1 a)
variable (ho : (D.base.transverse (by norm_num) D.lower D.upper).eval x *
  (D.base.transverse (by norm_num) D.lower D.upper).eval y<0)
variable (hlx : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x|)
variable (hly : R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y|)
variable (hux : |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8)
variable (huy : |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8)

include hD hx hy ho hlx hly hux huy in
/-- The actual simultaneous append of every old ordered history has at least
one favorable value of the common identifier's fair coin. -/
lemma favorable_sign : ∃ e : Bool, ∀ sign : Fin (S.count+1) → Bool, sign a=e →
    kappaB*lambda*R/50≤(update A S hist hcross hrec sign).sets.separation
      x.column x.height y.column y.height := by
  have hr : (BData.ordered D).Recorded (hist a) (by norm_num [R]) (by norm_num [R]) := by
    rw [←hD]
    exact hrec a
  obtain ⟨e,he⟩ := D.exists_increment_gain (hist a) (S.region A a) (hcross a) hr x y hx hy
    ho hlx hly hux huy
  refine ⟨e,fun sign hs => ?_⟩
  have hxi : S.name x.column x.height=a := hx.center A (by norm_num)
  have hyi : S.name y.column y.height=a := hy.center A (by norm_num)
  have hi := S.height_named x.column x.height a hxi
  have hj := S.height_named y.column y.height a hyi
  have hb := separation_lower A S hist hcross hrec sign a x.column y.column x.height y.height hxi hyi hi hj
  rw [hs] at hb
  have ex := BData.normalizedIncrement_coordinates (hist a) (S.region A a) (hcross a) hD
    (i := x.column) rfl (s := x.height) rfl hi x.inBand e
  have ey := BData.normalizedIncrement_coordinates (hist a) (S.region A a) (hcross a) hD
    (i := y.column) rfl (s := y.height) rfl hj y.inBand e
  rw [ex,ey] at hb
  have hh := mul_le_mul_of_nonneg_left he verticalB.1
  change kappaB*(lambda*R/50)≤kappaB*|_ - _| at hh
  calc
    kappaB*lambda*R/50 = kappaB*(lambda*R/50) := by ring
    _ ≤ _ := hh
    _ ≤ _ := hb

include hD hx hy ho hlx hly hux huy in
lemma success_probability : 1/2≤FiniteRandom.prob (fun sign : Fin (S.count+1) → Bool =>
    kappaB*lambda*R/50≤(update A S hist hcross hrec sign).sets.separation
      x.column x.height y.column y.height) := by
  obtain ⟨e,he⟩ := favorable_sign A S hist hcross hrec hD x y hx hy ho hlx hly hux huy
  rw [←FiniteRandom.prob_coin a e]
  exact @FiniteRandom.prob_mono_instances (Fin (S.count+1) → Bool) _ _ _ _ he
end IncrementStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}

variable (w z : Endpoint A SA SB v L U hv q p phaseD phaseG)
variable (he : Eligible A SA SB v w.val z.val) (hc : Cutoffs A SA SB v w.val z.val)
variable (ha : 1≤dist (v w.val) (v z.val)) (hd : dist (v w.val) (v z.val)<2)

lemma ordered_of_rejected
    (hn : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)) :
    ∃ D : OrderedData M, SB.chart (indexB A SB v w.val)=.ordered D := by
  cases hD : SB.chart (indexB A SB v w.val) with
  | ordinary C =>
    apply False.elim
    apply hn
    left
    change (SB.chart (indexB A SB v w.val)).isOrdinary=true
    rw [hD]
    rfl
  | ordered D => exact ⟨D,rfl⟩

include he hc ha hd in
/-- The two actual retained endpoint groups, rather than hypothetical seeds,
force transverse values in their actual common old ordered chart. -/
theorem transverse_of_rejected
    (hwp : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hwn : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted false
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hzp : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted true
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z))
    (hzn : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted false
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)) :
    ∃ (D : OrderedData M) (_hD : SB.chart (indexB A SB v w.val)=.ordered D)
      (x y : M.Point D.band (v w.val).column),
      x.column=(v w.val).column ∧ x.height=(v w.val).height ∧
      y.column=(v z.val).column ∧ y.height=(v z.val).height ∧
      (D.base.transverse (by norm_num) D.lower D.upper).eval x *
        (D.base.transverse (by norm_num) D.lower D.upper).eval y < 0 ∧
      R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval x| ∧
      R/100≤|(D.base.transverse (by norm_num) D.lower D.upper).eval y| ∧
      |(D.base.transverse (by norm_num) D.lower D.upper).eval x|≤8 ∧
      |(D.base.transverse (by norm_num) D.lower D.upper).eval y|≤8 := by
  obtain ⟨D,hD⟩ := ordered_of_rejected A SA SB v hv w hwp
  have hband : (SB.chart (indexB A SB v w.val)).band=D.band := congrArg BData.band hD
  let x : M.Point D.band (v w.val).column :=
    ⟨(v w.val).column,(v w.val).height,hband ▸ SB.height_in _ _,SimpleGraph.Reachable.refl _⟩
  have hsub : {H : ℝ | |H-(v w.val).height|≤2} ⊆ D.band := by
    rw [←hband]
    exact SB.ball_band A he.2.2.1 (fun H hH => by rw [abs_sub_comm]; exact hH.trans (by norm_num))
  obtain ⟨y,hyc,hyh,hdy⟩ := Point.local_point (v w.val) (v z.val) x rfl rfl
    isClosed_univ (Set.subset_univ _) hsub hd.le
  have hG : (group A SA SB v hv (groupOf A SA SB v hv w)).data=.ordered D := hD
  have hH : (group A SA SB v hv (groupOf A SA SB v hv z)).data=.ordered D := by
    change SB.chart (indexB A SB v z.val)=.ordered D
    rw [he.namesB A SA SB v]
    exact hD
  have hl : (group A SA SB v hv (groupOf A SA SB v hv z)).lower=
      (group A SA SB v hv (groupOf A SA SB v hv w)).lower := by
    rw [groupOf_lower,groupOf_lower]
    exact PairGeometry.narrow_lower_eq A SA SB v hv (witness A SA SB v hv w).interior hc
  have hcut : |D.value Group.lam x.column ⟨x.height,x.inBand⟩-
      D.value Group.lam y.column ⟨y.height,y.inBand⟩|≤R/10000 := by
    have value_coordinates {D E : BData M} (h : D=E)
        {i j : Fin (k+1)} {H T : ℝ} (hc : i=j) (hH : H=T)
        (hI : H∈D.band) (hJ : T∈E.band) :
        D.value Group.lam i ⟨H,hI⟩=E.value Group.lam j ⟨T,hJ⟩ := by
      subst E; subst j; subst T; rfl
    have hx : D.value Group.lam x.column ⟨x.height,x.inBand⟩=fullValue A SB v w.val :=
      value_coordinates hD.symm rfl rfl _ _
    have hy : D.value Group.lam y.column ⟨y.height,y.inBand⟩=fullValue A SB v z.val :=
      value_coordinates (hD.symm.trans (congrArg SB.chart (he.namesB A SA SB v).symm)) hyc hyh _ _
    rw [hx,hy]
    exact hc.2.2.le
  refine ⟨D,hD,x,y,rfl,rfl,hyc,hyh,?_⟩
  exact Group.two_side_of_rejected _ _ hG hH hl _ _ _ _
    (selectedPoint_mem A SA SB v hv w) (selectedPoint_mem A SA SB v hv z)
    hwp hwn hzp hzn x y rfl rfl hyc hyh (by rw [hdy]; exact ha)
    (by rw [hdy]; exact hd.le) hcut
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (hist : Fin (SB.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (SB.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))
variable (w z : Endpoint A SA SB v L U hv q p phaseD phaseG)
variable (he : Eligible A SA SB v w.val z.val) (hc : Cutoffs A SA SB v w.val z.val)
variable (ha : 1≤dist (v w.val) (v z.val)) (hd : dist (v w.val) (v z.val)<2)

include he hc ha hd in
/-- Both actual endpoint rejections force success of the genuine simultaneous
history increment with one favorable independent fair identifier coin. -/
lemma rejected_increment_probability
    (hwp : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hwn : ¬(group A SA SB v hv (groupOf A SA SB v hv w)).Admitted false
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w))
    (hzp : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted true
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z))
    (hzn : ¬(group A SA SB v hv (groupOf A SA SB v hv z)).Admitted false
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)) :
    1/2≤FiniteRandom.prob (fun sign : Fin (SB.count+1) → Bool =>
      kappaB*lambda*R/50≤(IncrementStep.update A SB hist hcross hrec sign).sets.separation
        (v w.val).column (v w.val).height (v z.val).column (v z.val).height) := by
  obtain ⟨D,hD,x,y,hxc,hxh,hyc,hyh,ho,hlx,hly,hux,huy⟩ :=
    transverse_of_rejected A SA SB v hv w z he hc ha hd hwp hwn hzp hzn
  have hx : A.Common SB.name (A.point x.column x.height) 1 (indexB A SB v w.val) := by
    rw [hxc,hxh,A.coordinate_point]
    exact fun z hz => he.2.2.1 z (hz.trans (by norm_num))
  have hy : A.Common SB.name (A.point y.column y.height) 1 (indexB A SB v w.val) := by
    rw [hyc,hyh,A.coordinate_point]
    exact fun z hz => he.2.2.2 z (hz.trans (by norm_num))
  have h := IncrementStep.success_probability A SB hist hcross hrec hD x y hx hy ho hlx hly hux huy
  simpa only [hxc,hxh,hyc,hyh] using h
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SetSystem
open MeasureTheory
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma separation_comm (S : SetSystem M Ω μ) (i : Fin (k+1)) (H : ℝ) (j : Fin (k+1)) (T : ℝ) :
    S.separation i H j T=S.separation j T i H := by
  unfold separation
  congr 1
  funext ω
  exact abs_sub_comm _ _
end PlanarL1.Columns.Model.SetSystem

namespace PlanarL1.Parameters
lemma secondaryChance_pos : 0 < secondaryChance := by unfold secondaryChance; positivity
lemma secondaryChance_le_quarter : secondaryChance≤1/4 := by
  unfold secondaryChance
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  calc
    (4:ℝ) = 2^2 := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory SecondaryGeometry VertexTests RetainedSelection
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (ha : 1≤dist (v x) (v y)) (hd : dist (v x) (v y)<2)
variable (hist : Fin (SB.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (SB.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))

include hj hc ha in
lemma retained_alternative {m : ℕ} (hm : 0 < m) (hr : Retained A SA SB v hv he hi hd) :
    secondaryChance ≤ FiniteRandom.prob
      (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
        kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
          (v x).column (v x).height (v y).column (v y).height) ∨
    1/2 ≤ FiniteRandom.prob (fun sign : Fin (SB.count+1) → Bool =>
      kappaB*lambda*R/50 ≤ (IncrementStep.update A SB hist hcross hrec sign).sets.separation
        (v x).column (v x).height (v y).column (v y).height) := by
  have hxmem : x ∈ remaining A SA SB v L U hv q p phaseD phaseG :=
    (mem_remaining A SA SB v hv x).mpr ⟨⟨y,⟨ha,hd,he⟩,hc,hi,hj,hr⟩⟩
  have hymem : y ∈ remaining A SA SB v L U hv q p phaseD phaseG :=
    (mem_remaining A SA SB v hv y).mpr ⟨⟨x,⟨by simpa only [dist_comm] using ha,
      by simpa only [dist_comm] using hd,he.symm A SA SB v⟩,hc.symm A SA SB v,hj,hi,
      hr.symm A SA SB v hv he hi hj hc hd⟩⟩
  let w : Endpoint A SA SB v L U hv q p phaseD phaseG := ⟨x,hxmem⟩
  let z : Endpoint A SA SB v L U hv q p phaseD phaseG := ⟨y,hymem⟩
  have hw (positive : Bool)
      (had : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted positive
        (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)) :
      secondaryChance ≤ FiniteRandom.prob
        (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
          kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
            (v x).column (v x).height (v y).column (v y).height) :=
    selected_admitted_probability A SA SB v hv w hj he ha hc positive had hm
  have hz (positive : Bool)
      (had : (group A SA SB v hv (groupOf A SA SB v hv z)).Admitted positive
        (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)) :
      secondaryChance ≤ FiniteRandom.prob
        (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
          kappaB*R/50 < (layer (group A SA SB v hv) hm omega).sets.separation
            (v x).column (v x).height (v y).column (v y).height) := by
    have hh := selected_admitted_probability A SA SB v hv z hi (he.symm A SA SB v)
      (by simpa only [dist_comm] using ha) (hc.symm A SA SB v) positive had hm
    exact hh.trans (FiniteRandom.prob_mono (fun omega h => by
      simpa only [SetSystem.separation_comm] using h))
  by_cases hwp : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted true
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)
  · exact Or.inl (hw true hwp)
  by_cases hwn : (group A SA SB v hv (groupOf A SA SB v hv w)).Admitted false
      (selectedComponent A SA SB v hv w) (selectedPoint A SA SB v hv w)
  · exact Or.inl (hw false hwn)
  by_cases hzp : (group A SA SB v hv (groupOf A SA SB v hv z)).Admitted true
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)
  · exact Or.inl (hz true hzp)
  by_cases hzn : (group A SA SB v hv (groupOf A SA SB v hv z)).Admitted false
      (selectedComponent A SA SB v hv z) (selectedPoint A SA SB v hv z)
  · exact Or.inl (hz false hzn)
  exact Or.inr (rejected_increment_probability A SA SB v hv hist hcross hrec w z he hc ha hd hwp hwn hzp hzn)
end PlanarL1.Columns.Model.PairGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_CoupledState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.VertexBands
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {L U : ℝ}

lemma height_padding_loss (m : ℕ) (hm : 0 < m) (H : ℝ) {ρ : ℝ} (hρ : 0≤ρ) :
    (geometricExecution m L U M).prob (fun c => ¬HeightPadded c H ρ)≤heightLoss ρ m := by
  let P := fun h : HeightChoices m => ¬Tiling.Padded a₁ (shift m a₁ h.1) H ρ
  let Q := fun h : HeightChoices m => ¬Tiling.Padded a₂ (shift m a₂ h.2) H ρ
  have hp : prob P≤(2*ρ+2*a₁/m)/a₁ := by
    apply prob_prod_bound_left
    intro j
    apply (prob_mono (Q := fun i => Tiling.NearBoundary a₁ (a₁/m*i.val) H ρ) ?_).trans
      (periodic_probability m hm interpolationA.2.1 hρ H)
    intro i hi
    by_contra hn
    exact hi (Tiling.padded_of_avoid interpolationA.2.1 hn)
  have hq : prob Q≤(2*ρ+2*a₂/m)/a₂ := by
    apply prob_prod_bound
    intro i
    apply (prob_mono (Q := fun j => Tiling.NearBoundary a₂ (a₂/m*j.val) H ρ) ?_).trans
      (periodic_probability m hm interpolationB.2.1 hρ H)
    intro j hj
    by_contra hn
    exact hj (Tiling.padded_of_avoid interpolationB.2.1 hn)
  have he : (geometricExecution m L U M).prob (fun c => ¬HeightPadded c H ρ)=
      prob (fun h : HeightChoices m => P h ∨ Q h) := by
    unfold geometricExecution
    rw [Execution.prob_bind]
    simp only [Execution.prob_bind_pure,HeightPadded,not_and_or]
    change Execution.uniform.mean (fun h : HeightChoices m =>
      Execution.uniform.prob (fun _ : RadialChoices m (shift m a₁ h.1) L U M => P h ∨ Q h))=_
    have hc (h : HeightChoices m) :
        Execution.uniform.prob (fun _ : RadialChoices m (shift m a₁ h.1) L U M => P h ∨ Q h)=
          if P h ∨ Q h then 1 else 0 := by
      by_cases hh : P h ∨ Q h <;> simp only [Execution.prob,hh,ite_true,ite_false,Execution.mean_const]
    simp_rw [hc]
    calc
      _ = Execution.uniform.prob (fun h : HeightChoices m => P h ∨ Q h) := by
        unfold Execution.prob
        congr 1
        funext h
        by_cases hh : P h ∨ Q h <;> simp [hh]
      _ = _ := Execution.prob_uniform _
  rw [he]
  exact (prob_or_le P Q).trans (add_le_add hp hq)

lemma conditional_persistence {β : Type*} (m : ℕ) (hm : 0 < m) (H : ℝ)
    {ρ b : ℝ} (hρ : 0≤ρ) (hb : 0≤b)
    (F : Choices m L U M → Execution β) (P : β → Prop)
    (hF : ∀ c, HeightPadded c H ρ → (F c).prob (fun z => ¬P z)≤b) :
    ((geometricExecution m L U M).bind F).prob (fun z => ¬P z)≤heightLoss ρ m+b :=
  (Execution.conditional_loss _ F (fun c => HeightPadded c H ρ) P hb hF).trans
    (add_le_add (height_padding_loss (M := M) (L := L) (U := U) m hm H hρ) le_rfl)
end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}

namespace SetSystem
lemma lift_separation (S : SetSystem M Ω μ) (i j : Fin (k+1)) (H T : ℝ) :
    S.lift.separation i H j T=S.separation i H j T := by
  let hp := measurePreserving_fst (μ := μ) (ν := Threshold.fair)
  change (∫ z : Ω × Bool, |(S.activity z.1).indicator i H-(S.activity z.1).indicator j T| ∂μ.prod Threshold.fair)=_
  have he := integral_map_of_stronglyMeasurable (μ := μ.prod Threshold.fair) hp.measurable
    (((S.measurable_indicator i H).sub (S.measurable_indicator j T)).abs.stronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm
end SetSystem

namespace PairGeometry
variable {V : Type*} {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {v : V → M.Point Set.univ A.root} {x y : V} {b d : ℝ}
lemma Certificate.mono (h : Certificate A SA v (x := x) (y := y) b) (hdb : d≤b) :
    Certificate A SA v (x := x) (y := y) d := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  exact ⟨a,c,H,E,hH,hac,hsep,hE,hdb.trans hm,hx,hy,hn⟩
lemma Certificate.lift (h : Certificate A SA v (x := x) (y := y) b) :
    Certificate A SA.lift v (x := x) (y := y) b := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  refine ⟨a,c,H,Prod.fst ⁻¹' E,hH,hac,hsep,hE.preimage measurable_fst,?_,?_,?_,?_⟩
  · rw [(measurePreserving_fst (μ := μ) (ν := Threshold.fair)).measureReal_preimage hE.nullMeasurableSet]
    exact hm
  · intro z hz; exact hx z.1 hz
  · intro z hz; exact hy z.1 hz
  · intro z hz; exact hn z.1 hz
end PairGeometry

namespace CoupledState
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)

variable {V : Type*} (v : V → M.Point Set.univ A.root)
lemma Successful.lift {b : ℝ} {x y : V} (h : S.Successful v b x y) : S.lift.Successful v b x y := by
  rcases h with h|h|h
  · exact Or.inl (by simpa only [CoupledState.lift,OrdinaryState.lift,SetSystem.lift_separation] using h)
  · exact Or.inr (Or.inl (by simpa only [CoupledState.lift,BState.lift,SetSystem.lift_separation] using h))
  · exact Or.inr (Or.inr h.lift)
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Execution
variable {α : Type*}
lemma choose_lower (n : ℕ) (E : Fin (n+1) → Execution α) (P : α → Prop) (i : Fin (n+1)) :
    (E i).prob P/(n+1) ≤ (Execution.choose n E).prob P := by
  change _ ≤ (∑ j, (E j).prob P)/(n+1)
  exact div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (E j).prob_nonneg P) (Finset.mem_univ i)) (by positivity)
lemma choose4_lower (E : Fin 4 → Execution α) (P : α → Prop) (i : Fin 4) :
    (E i).prob P/4 ≤ (Execution.choose 3 E).prob P := by
  convert choose_lower 3 E P i using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma prob_pure (x : α) (P : α → Prop) [Decidable (P x)] :
    (Execution.pure x).prob P=if P x then 1 else 0 := by
  classical
  by_cases h : P x <;> simp only [prob,mean,h,ite_true,ite_false]
lemma prob_pure_of (x : α) (P : α → Prop) (h : P x) : (Execution.pure x).prob P=1 := by
  classical
  simp only [prob_pure,h,ite_true]
end PlanarL1.Execution

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Movement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Execution
variable {α β : Type*}
lemma holds_of_forall (E : Execution α) {P : α → Prop} (h : ∀ x, P x) : E.Holds P := by
  induction E with
  | pure x => exact h x
  | choose n E ih => exact ih
lemma Holds.mono {E : Execution α} {P Q : α → Prop} (h : E.Holds P)
    (hp : ∀ x, P x → Q x) : E.Holds Q := by
  induction E with
  | pure x => exact hp x h
  | choose n E ih => exact fun i => ih i (h i)
lemma Holds.bind {E : Execution α} {P : α → Prop} (h : E.Holds P)
    (F : α → Execution β) {Q : β → Prop} (hf : ∀ x, P x → (F x).Holds Q) :
    (E.bind F).Holds Q := by
  induction E with
  | pure x => exact hf x h
  | choose n E ih => exact fun i => ih i (h i)
lemma holds_bind_of_forall (E : Execution α) (F : α → Execution β) {Q : β → Prop}
    (h : ∀ x, (F x).Holds Q) : (E.bind F).Holds Q :=
  (E.holds_of_forall (fun _ => True.intro)).bind F (fun x _ => h x)
lemma Holds.mean_mono {E : Execution α} {f g : α → ℝ} (h : E.Holds (fun x => f x≤g x)) :
    E.mean f≤E.mean g := by
  induction E with
  | pure x => exact h
  | choose n E ih =>
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun i _ => ih i (h i))) (by positivity)
lemma Holds.prob_mono {E : Execution α} {P Q : α → Prop} (h : E.Holds (fun x => P x → Q x)) :
    E.prob P≤E.prob Q := by
  classical
  apply Holds.mean_mono
  apply h.mono
  intro x hp
  by_cases hx : P x
  · simp [hx,hp hx]
  · simp only [hx,ite_false]; split_ifs <;> norm_num
lemma Holds.prob_eq_one {E : Execution α} {P : α → Prop} (h : E.Holds P) : E.prob P=1 := by
  have hh := h.mono (Q := fun x => True → P x) (fun _ hx _ => hx)
  apply le_antisymm (E.prob_le_one P)
  have he : E.prob (fun _ => True)=1 := by simp [prob,E.mean_const]
  simpa only [he] using hh.prob_mono
end PlanarL1.Execution

end



section

namespace PlanarL1.FiniteRandom
lemma prob_eq_instances {Ω : Type*} (F F' : Fintype Ω) (P : Ω → Prop) :
    @prob Ω F P = @prob Ω F' P := by
  cases Subsingleton.elim F' F
  rfl
lemma prob_bound_of_instances {Ω : Type*} {F F' : Fintype Ω} (P : Ω → Prop) {b : ℝ}
    (h : @prob Ω F' P ≤ b) : @prob Ω F P ≤ b :=
  (prob_eq_instances F F' P).trans_le h
lemma prob_prod_bound_any {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (F : Fintype (Ω × Λ)) (P : Ω × Λ → Prop) {b : ℝ}
    (h : ∀ w, prob (fun z : Λ => P (w,z)) ≤ b) : @prob (Ω × Λ) F P ≤ b := by
  rw [prob_eq_instances F (instFintypeProd Ω Λ) P]
  exact prob_prod_bound P h
end PlanarL1.FiniteRandom

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Persistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry FiniteRandom
open scoped NNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0 ≤ ρ)
variable (hp : Tiling.Padded a₁ q x.height ρ) (hn : Tiling.Padded a₂ p x.height ρ)
variable (a : Fin (SB.count+1)) (hold : A.Common SB.name x ρ a)
variable (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
variable {m : ℕ} (hm : 0 < m)

include hρ hp hn hold hsmall hr hm

attribute [local instance] OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeOffsetsGroupIndexGroup
lemma persistence_fixed [SFinite ν]
    (o : Fin (SB.count+1) → Bool)
    (coins : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) → Bool) :
    prob (fun w : Offsets (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m => ∃ z : Group.Ball x (ρ := ρ),
      (SecondaryGeometry.result (group A SA SB v hv) hm (flatSample (group A SA SB v hv) o coins w)).name z.val.column z.val.height≠
      (SecondaryGeometry.result (group A SA SB v hv) hm (flatSample (group A SA SB v hv) o coins w)).name x.column x.height) ≤
      (1+SurvivingGroups.packBound*secondaryN : ℕ)^2*secondaryTestLoss ρ m := by
  classical
  let G := group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)
  have hBand (z : Group.Ball x (ρ := ρ)) : z.val.height∈(SB.chart a).band :=
    SB.height_named _ _ _ (hold z.val z.property)
  apply prob_bound_of_instances
  apply persistence_flat G o coins a x hBand hρ hm hsmall hr _
    (fun z => hold z.val z.property) _ (wholeBallSlots_card A SA SB v hv x o coins a hρ hp hn)
  · intro z
    have hb : ∀ H, |H-x.height|≤ρ → H∈(SB.chart a).band := by
      intro H hH
      exact SB.ball_band A hold (J := {T | |T-x.height|≤ρ})
        (fun T hT => by simpa only [Set.mem_ofPred_eq,abs_sub_comm] using hT) hH
    obtain ⟨hX,hZ,he⟩ := ((SB.chart a).comparison Group.lam Group.lam_bound (o a)).ball_variation x z.val hρ hb z.property
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ hρ
    exact_mod_cast (le_max_left (5 : ℝ≥0) ⟨3/(9*a₂/100),by norm_num [a₂]⟩)
  · intro j ⟨z,hz⟩ H hH
    exact group_touched_envelope A SA SB v hv x hρ hn
      (coord G o coins (m := m) a j).1 (o a) (coord G o coins (m := m) a j).2
      z.property hz H hH

attribute [local instance] OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeForallForallComponentSampleGroupIndexGroup
lemma persistence_probability [SFinite ν] :
    prob (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
      ∃ z : Group.Ball x (ρ := ρ),
      (SecondaryGeometry.result (group A SA SB v hv) hm omega).name z.val.column z.val.height≠
      (SecondaryGeometry.result (group A SA SB v hv) hm omega).name x.column x.height) ≤
      (1+SurvivingGroups.packBound*secondaryN : ℕ)^2*secondaryTestLoss ρ m := by
  classical
  let G := group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)
  apply prob_prod_bound_any
  intro o
  apply prob_prod_bound_any
  intro coins
  rw [←prob_equiv (Equiv.piCurry (fun i C => ComponentSample G i C m))]
  apply prob_bound_of_instances
  exact persistence_fixed A SA SB v hv x hρ hp hn a hold hsmall hr hm o coins
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Execution
variable {α : Type*}
lemma choose_upper (n : ℕ) (E : Fin (n+1) → Execution α) (P : α → Prop) {b : ℝ}
    (h : ∀ i, (E i).prob P ≤ b) : (Execution.choose n E).prob P ≤ b := by
  change (∑ i, (E i).prob P)/(n+1) ≤ b
  have hp : (0:ℝ)<n+1 := by positivity
  apply (div_le_iff₀ hp).mpr
  calc
    _  ≤  ∑ _ : Fin (n+1), b := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp; ring
end PlanarL1.Execution

namespace PlanarL1.Parameters
lemma mainLoss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ mainLoss ρ m := by
  unfold mainLoss mainTestLoss
  positivity [mainQ_pos,interpolationA.1]
lemma secondaryLoss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ secondaryLoss ρ m :=
  mul_nonneg (sq_nonneg _) (secondaryTestLoss_nonneg hρ m)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)

variable (ht : 1 ≤ t) (hgap : 10 ≤ (R/200)*t)
variable [SFinite μ] [SFinite ν] [Fintype V]
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
variable (x : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hr : ρ ≤ persistenceRadius) (hold : S.Coherent (v x) ρ)

omit [SFinite ν] [Fintype V] in
include hv hρ hr hold in
lemma main_persistence (hp : Tiling.Padded a₁ q (v x).height ρ) :
    FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      ¬(S.main ht phaseD hm omega).Coherent (v x) ρ) ≤ mainLoss ρ m := by
  let c := mainCell A v hv phaseD x
  have hh := MainFamily.persistence_probability A S.left phaseD (v x) c
    (mainCell_mem A v hv phaseD x) hρ hp (persistence_main_small hr)
    (persistence_main_radius hr) (fun z hz => (hold z hz).1) m hm
  apply (FiniteRandom.prob_mono (Q := fun omega : MainFamily.Sample phaseD m =>
    ∃ z : M.Point Set.univ A.root, dist (v x) z ≤ ρ ∧
      (MainFamily.result A S.left phaseD hm omega).name z.column z.height≠
      (MainFamily.result A S.left phaseD hm omega).name (v x).column (v x).height) ?_).trans hh
  intro omega hb
  by_contra hn
  apply hb
  intro z hz
  exact ⟨not_ne_iff.mp (fun he => hn ⟨z,hz,he⟩),(hold z hz).2⟩

omit [SFinite μ] in
include hv hρ hr hold in
lemma secondary_persistence (hp : Tiling.Padded a₁ q (v x).height ρ)
    (hn : Tiling.Padded a₂ p (v x).height ρ) :
    FiniteRandom.prob (fun omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m =>
      ¬(S.secondary ht v hv phaseD hm p phaseG omega).Coherent (v x) ρ) ≤ secondaryLoss ρ m := by
  have hh := RetainedSelection.persistence_probability A S.left S.right v hv (phaseD := phaseD) (phaseG := phaseG) (v x) hρ hp hn
    (S.right.name (v x).column (v x).height) (fun z hz => (hold z hz).2)
    (persistence_secondary_small hr) (persistence_secondary_radius hr) hm
  apply (FiniteRandom.prob_mono (Q := fun omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m =>
      ∃ z : Group.Ball (v x) (ρ := ρ),
      (SecondaryGeometry.result (S.groups v hv phaseD p phaseG) hm omega).name z.val.column z.val.height≠
      (SecondaryGeometry.result (S.groups v hv phaseD p phaseG) hm omega).name (v x).column (v x).height) ?_).trans hh
  intro omega hb
  by_contra hn
  apply hb
  intro z hz
  exact ⟨(hold z hz).1,not_ne_iff.mp (fun he => hn ⟨⟨z,hz⟩,he⟩)⟩

include hv hρ hr hold in
lemma modes_persistence (hp : Tiling.Padded a₁ q (v x).height ρ)
    (hn : Tiling.Padded a₂ p (v x).height ρ) :
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => ¬z.Coherent (v x) ρ) ≤ 
      mainLoss ρ m+secondaryLoss ρ m := by
  have hA := mainLoss_nonneg hρ m
  have hB := secondaryLoss_nonneg hρ m
  apply Execution.choose_upper
  intro i
  fin_cases i
  · change (Execution.pure (S.unchanged ht)).prob (fun z => ¬z.Coherent (v x) ρ) ≤ _
    have hg : (S.unchanged ht).Coherent (v x) ρ := hold
    simp only [Execution.prob_pure,hg,not_true_eq_false,ite_false]
    exact add_nonneg hA hB
  · change (Execution.uniform.bind (fun omega => .pure (S.main ht phaseD hm omega))).prob
      (fun z => ¬z.Coherent (v x) ρ) ≤ _
    rw [Execution.prob_bind_pure,Execution.prob_uniform]
    exact (S.main_persistence ht v hv phaseD hm x hρ hr hold hp).trans (le_add_of_nonneg_right hB)
  · change (Execution.uniform.bind (fun omega => .pure (S.secondary ht v hv phaseD hm p phaseG omega))).prob
      (fun z => ¬z.Coherent (v x) ρ) ≤ _
    rw [Execution.prob_bind_pure,Execution.prob_uniform]
    exact (S.secondary_persistence ht v hv phaseD hm p phaseG x hρ hr hold hp hn).trans (le_add_of_nonneg_left hA)
  · change (Execution.uniform.bind (fun sign => .pure (S.increment ht hgap sign))).prob
      (fun z => ¬z.Coherent (v x) ρ) ≤ _
    rw [Execution.prob_bind_pure,Execution.prob_uniform]
    have hh : ∀ sign, (S.increment ht hgap sign).Coherent (v x) ρ := fun _ => hold
    have he : (fun sign => ¬(S.increment ht hgap sign).Coherent (v x) ρ)=(fun _ => False) :=
      funext (fun sign => propext (iff_false_intro (not_not.mpr (hh sign))))
    rw [he,FiniteRandom.prob_false]
    exact add_nonneg hA hB

include hv hρ hr hold in
lemma step_persistence : (S.step ht hgap v hv hm).prob (fun z => ¬z.Coherent (v x) ρ) ≤ persistenceLoss ρ m := by
  apply VertexBands.conditional_persistence m hm (v x).height hρ
    (add_nonneg (mainLoss_nonneg hρ m) (secondaryLoss_nonneg hρ m))
  intro c hc
  exact S.modes_persistence ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2) x hρ hr hold hc.1 hc.2
end PlanarL1.Columns.Model.CoupledState

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {q : ℝ} (hq : 0 < q)
namespace SetSystem
lemma dilate_separation (S : SetSystem M Ω μ) (i j : Fin (k+1)) (H T : ℝ) :
    (S.dilate hq).separation i (q*H) j (q*T)=q*S.separation i H j T := by
  simp only [separation,dilate,Activity.dilate_indicator,integral_smul_measure,
    smul_eq_mul,ENNReal.toReal_ofReal hq.le,mul_div_cancel_left₀ _ hq.ne']
end SetSystem
namespace PairGeometry
variable {SA : OrdinaryState M kappaA Ω μ} {v : V → M.Point Set.univ A.root}
variable {x y : V} {b : ℝ}
lemma Certificate.dilate (h : Certificate A SA v (x := x) (y := y) b) :
    Certificate (A.dilate hq) (SA.dilate hq) (fun x => A.scaleEquiv hq (v x))
      (x := x) (y := y) (q*b) := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  refine ⟨a,c,q*H,E,⟨H,hH,rfl⟩,hac,hsep,hE,?_,?_,?_,?_⟩
  · simpa only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq.le] using mul_le_mul_of_nonneg_left hm hq.le
  · intro w hw
    change (SA.sets.activity w).active (v x).column (q*(v x).height/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hx w hw
  · intro w hw
    change (SA.sets.activity w).active (v y).column (q*(v y).height/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hy w hw
  · intro w hw
    change ¬(SA.sets.activity w).active a (q*H/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hn w hw
end PairGeometry
namespace CoupledState
variable {t : ℝ} (S : CoupledState A Ω Ξ μ ν t) (v : V → M.Point Set.univ A.root)
lemma Successful.dilate {x y : V} {b : ℝ} (h : S.Successful v b x y) :
    (S.dilate hq).Successful (fun x => A.scaleEquiv hq (v x)) (q*b) x y := by
  rcases h with h|h|h
  · apply Or.inl
    change q*b ≤ (S.left.sets.dilate hq).separation _ (q*_) _ (q*_)
    rw [SetSystem.dilate_separation]
    exact mul_le_mul_of_nonneg_left h hq.le
  · apply Or.inr ∘ Or.inl
    change q*b ≤ (S.right.sets.dilate hq).separation _ (q*_) _ (q*_)
    rw [SetSystem.dilate_separation]
    exact mul_le_mul_of_nonneg_left h hq.le
  · exact Or.inr (Or.inr (h.dilate hq))
lemma coherent_dilate (x : M.Point Set.univ A.root) (ρ : ℝ) :
    (S.dilate hq).Coherent (A.scaleEquiv hq x) (q*ρ) ↔ S.Coherent x ρ := by
  constructor
  · intro h z hz
    have hh := h (A.scaleEquiv hq z) (by rw [A.scaleEquiv_dist]; exact mul_le_mul_of_nonneg_left hz hq.le)
    change S.left.name z.column (q*z.height/q)=S.left.name x.column (q*x.height/q) ∧
      S.right.name z.column (q*z.height/q)=S.right.name x.column (q*x.height/q) at hh
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hh
  · intro h z hz
    obtain ⟨z,rfl⟩ := (A.scaleEquiv hq).surjective z
    rw [A.scaleEquiv_dist] at hz
    have hh := h z (by nlinarith only [hz,hq])
    change S.left.name z.column (q*z.height/q)=S.left.name x.column (q*x.height/q) ∧
      S.right.name z.column (q*z.height/q)=S.right.name x.column (q*x.height/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hh
end CoupledState
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_StepSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Parameters
lemma successGain_cutoff : successGain≤Columns.Model.VertexTests.cutoffGain := min_le_left _ _
lemma successGain_certificate : successGain≤kappaA*j/4 :=
  (min_le_right _ _).trans (min_le_left _ _)
lemma successGain_main : successGain≤kappaA*EA :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
lemma successGain_secondary : successGain≤kappaB*R/50 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
lemma successGain_increment : successGain≤kappaB*lambda*R/50 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
lemma successChance_pos : 0 < successChance := div_pos secondaryChance_pos (by norm_num)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable (ht : 1≤t) (hgap : 10≤(R/200)*t)
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {x y : V} {b : ℝ}

omit [SFinite μ] [SFinite ν] [Fintype V] in
lemma unchanged_success (h : S.Successful v b x y) :
    (S.unchanged ht).Successful v b x y :=
  Successful.lift (S.weaken ht) v h

lemma modes_unchanged (h : S.Successful v b x y) :
    1/4≤(S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 0
  change (Execution.pure (S.unchanged ht)).prob (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_pure_of (S.unchanged ht) (fun z => z.Successful v b x y) (S.unchanged_success ht v h)] at hh
  exact hh

lemma modes_main :
    FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      b≤(MainFamily.batch A S.left phaseD hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height)/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 1
  change (Execution.uniform.bind (fun omega => .pure (S.main ht phaseD hm omega))).prob
    (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_bind_pure,Execution.prob_uniform] at hh
  exact (div_le_div_of_nonneg_right (FiniteRandom.prob_mono (fun _ h => Or.inl h)) (by norm_num)).trans hh

lemma modes_secondary :
    FiniteRandom.prob (fun omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m =>
      b≤(SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height)/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 2
  change (Execution.uniform.bind (fun omega => .pure (S.secondary ht v hv phaseD hm p phaseG omega))).prob
    (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_bind_pure,Execution.prob_uniform] at hh
  exact (div_le_div_of_nonneg_right (FiniteRandom.prob_mono (fun _ h => Or.inr (Or.inl h))) (by norm_num)).trans hh

lemma modes_increment :
    FiniteRandom.prob (fun sign : Fin (S.right.count+1) → Bool =>
      b≤(IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).sets.separation
        (v x).column (v x).height (v y).column (v y).height)/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 3
  change (Execution.uniform.bind (fun sign => .pure (S.increment ht hgap sign))).prob
    (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_bind_pure,Execution.prob_uniform] at hh
  apply (div_le_div_of_nonneg_right (FiniteRandom.prob_mono ?_) (by norm_num)).trans hh
  intro sign hs
  apply Or.inr ∘ Or.inl
  change b≤(IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).sets.lift.separation _ _ _ _
  simpa only [SetSystem.lift_separation] using hs

end PlanarL1.Columns.Model.CoupledState

end



section

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests PairGeometry
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable (ht : 1≤t) (hgap : 10≤(R/200)*t)
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {x y : V}
variable (he : Eligible A S.left S.right v x y)
variable (hi : Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A S.left S.right v x y)
variable (ha : 1≤dist (v x) (v y)) (hd : dist (v x) (v y)<2)

include he hi hj hc ha hd in
lemma interior_success : secondaryChance/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v successGain x y) := by
  have hmain (h : 1/4≤FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      kappaA*EA < (MainFamily.batch A S.left phaseD hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height)) : secondaryChance/4≤
        (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v successGain x y) := by
    have hp := (secondaryChance_le_quarter.trans h).trans
      (FiniteRandom.prob_mono (fun _ h => successGain_main.trans h.le))
    exact (div_le_div_of_nonneg_right hp (by norm_num)).trans
      (S.modes_main ht hgap v hv phaseD hm p phaseG)
  by_cases hx : Nonempty ((S.left.chart (indexA A S.left v x)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q x))
      ((position A S.left S.right v hv he hi).point.widen (position A S.left S.right v hv he hi).subA) epsilon)
  swap
  · exact hmain (PairGeometry.no_descent_probability A S.left S.right v hv he hi hj hc ha hm hx)
  let he' := he.symm A S.left S.right v
  have hd' : dist (v y) (v x)<2 := by simpa only [dist_comm] using hd
  by_cases hy : Nonempty ((S.left.chart (indexA A S.left v y)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q y))
      ((position A S.left S.right v hv he' hj).point.widen (position A S.left S.right v hv he' hj).subA) epsilon)
  swap
  · have hh := PairGeometry.no_descent_probability A S.left S.right v hv he' hj hi
      (hc.symm A S.left S.right v) (by simpa only [dist_comm] using ha) hm hy
    exact hmain (hh.trans (FiniteRandom.prob_mono (fun _ h => by
      simpa only [SetSystem.separation_comm] using h)))
  have hyp : Nonempty ((S.left.chart (indexA A S.left v x)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q x)) (partner A S.left S.right v hv he hi hd) epsilon) := by
    apply OrdinaryData.descent_coordinates (congrArg S.left.chart (he.namesA A S.left S.right v))
      (congrArg (BandTrees.band broad) (broad_lower_eq A S.left S.right v hv hi hc)) _ _ hy
    · exact (partner_column A S.left S.right v hv he hi hd).symm
    · exact (partner_height A S.left S.right v hv he hi hd).symm
  by_cases hl : (S.left.chart (indexA A S.left v x)).comparison.NoLowCircular
      ((position A S.left S.right v hv he hi).point.widen (position A S.left S.right v hv he hi).subA)
      (partner A S.left S.right v hv he hi hd) (BandTrees.band narrow (narrowLower A v p x)) j
  swap
  · have hh := certificate_of_excluded A S.left S.right v hv he hi hc hd hl
    have hp := S.modes_unchanged ht hgap v hv phaseD hm p phaseG
      (Or.inr (Or.inr (hh.mono successGain_certificate)))
    exact (by linarith [secondaryChance_le_quarter] : secondaryChance/4≤1/4).trans hp
  have hr : Retained A S.left S.right v hv he hi hd := ⟨hx,hyp,hl⟩
  rcases retained_alternative A S.left S.right v hv he hi hj hc ha hd
      S.histories.history (S.cross hgap) S.histories.recorded hm hr with hsec|hinc
  · have hp := hsec.trans (FiniteRandom.prob_mono (fun _ h => successGain_secondary.trans h.le))
    exact (div_le_div_of_nonneg_right hp (by norm_num)).trans
      (S.modes_secondary ht hgap v hv phaseD hm p phaseG)
  · have hp := ((by linarith [secondaryChance_le_quarter] : secondaryChance≤1/2).trans hinc).trans
      (FiniteRandom.prob_mono (fun _ h => successGain_increment.trans h))
    exact (div_le_div_of_nonneg_right hp (by norm_num)).trans
      (S.modes_increment ht hgap v hv phaseD hm p phaseG)

include he ha hd in
/-- Quantitative success of the actual coupled four-mode step. All randomness
and surviving groups are sampled by the construction itself. -/
lemma step_success (hmany : 10000 ≤ m) : successChance≤
    (S.step ht hgap v hv hm).prob (fun z => z.Successful v successGain x y) := by
  rw [step,Execution.prob_bind]
  by_cases hc : Cutoffs A S.left S.right v x y
  · let E := geometricExecution m L U M
    let P := fun c : Choices m L U M => InteriorAt A v hv c x ∧ InteriorAt A v hv c y
    let f := fun c : Choices m L U M =>
      (S.modes ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2)).prob
        (fun z => z.Successful v successGain x y)
    have hp : 1/4≤E.prob P := interior_pair_probability A v hv m hmany x y
      (by simpa only [abs_sub_comm] using hc.1.le)
    have hg : secondaryChance/4*E.prob P≤E.mean f := E.mean_lower_of_event
      (fun c => Execution.prob_nonneg _ _) (fun c h =>
        S.interior_success ht hgap v hv _ hm _ _ he h.1 h.2 hc ha hd)
    change successChance≤E.mean f
    apply le_trans _ hg
    dsimp only [successChance]
    have hs := mul_le_mul_of_nonneg_left hp (div_nonneg secondaryChance_pos.le (by norm_num : (0:ℝ)≤4))
    linarith
  · have hs : S.Successful v successGain x y := by
      rcases separation_of_cutoff_failure A S.left S.right v he hc with h|h
      · exact Or.inl (successGain_cutoff.trans h)
      · exact Or.inr (Or.inl (successGain_cutoff.trans h))
    have hl : successChance≤1/4 := by
      unfold successChance
      linarith [secondaryChance_le_quarter]
    have hh := (geometricExecution m L U M).mean_mono (f := fun _ => (1:ℝ)/4)
      (fun c => S.modes_unchanged ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2) hs)
    rw [Execution.mean_const] at hh
    exact hl.trans hh
end PlanarL1.Columns.Model.CoupledState

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_CutExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters

namespace World
attribute [instance] measurable sfinite
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (hQ : 0 < Q) (h1 : 1 ≤ Q) (hgap : 10 ≤ (R/200)*Q)
variable (W : World k V Q)

omit [Fintype V] in
lemma after_distance (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) (x y : V) :
    (W.after hQ T).distance x y=Q*W.distance x y := W.ambient.scaleEquiv_dist hQ _ _
omit [Fintype V] in
lemma after_coherent (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) (x : V) (ρ : ℝ) :
    (W.after hQ T).Coherent x (Q*ρ) ↔ T.Coherent (W.vertex x) ρ :=
  T.coherent_dilate hQ _ _
omit [Fintype V] in
lemma after_successful (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure))
    {x y : V} {b : ℝ} (h : T.Successful W.vertex b x y) : (W.after hQ T).Successful (Q*b) x y := h.dilate hQ T W.vertex

lemma step_distances {m : ℕ} (hm : 0 < m) : (W.step hQ h1 hgap hm).Holds
    (fun Z => ∀ x y, Z.distance x y=Q*W.distance x y) := by
  apply Execution.holds_bind_of_forall
  intro T x y
  exact W.after_distance hQ T x y

lemma step_persistence {m : ℕ} (hm : 0 < m) {x : V} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hr : ρ ≤ persistenceRadius) (hold : W.Coherent x ρ) :
    (W.step hQ h1 hgap hm).prob (fun Z => ¬Z.Coherent x (Q*ρ)) ≤ persistenceLoss ρ m := by
  rw [step,Execution.prob_bind_pure]
  have he : (fun T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure) =>
      ¬(W.after hQ T).Coherent x (Q*ρ))=(fun T => ¬T.Coherent (W.vertex x) ρ) := by
    funext T
    exact propext (not_congr (W.after_coherent hQ T x ρ))
  rw [he]
  exact W.state.step_persistence h1 hgap W.vertex W.height_bounds hm x hρ hr hold

omit [Fintype V] in
lemma coherent_eligible {x y : V} (h : W.Coherent x 20) (hd : W.distance x y < 2) :
    VertexTests.Eligible W.ambient W.state.left W.state.right W.vertex x y := by
  refine ⟨?_,?_,?_,?_⟩
  · intro z hz
    exact (h z (hz.trans (by norm_num))).1
  · intro z hz
    have hxz : dist (W.vertex x) z ≤ 20 := by
      have ht := dist_triangle (W.vertex x) (W.vertex y) z
      change dist (W.vertex x) (W.vertex y)<2 at hd
      linarith
    exact (h z hxz).1
  · intro z hz
    exact (h z (hz.trans (by norm_num))).2
  · intro z hz
    have hxz : dist (W.vertex x) z ≤ 20 := by
      have ht := dist_triangle (W.vertex x) (W.vertex y) z
      change dist (W.vertex x) (W.vertex y)<2 at hd
      linarith
    exact (h z hxz).2

lemma step_success {m : ℕ} (hm : 0 < m) (hmany : 10000 ≤ m) {x y : V}
    (hc : W.Coherent x 20) (hlo : 1 ≤ W.distance x y) (hhi : W.distance x y < 2) :
    successChance ≤ (W.step hQ h1 hgap hm).prob (fun Z => Z.Successful (Q*successGain) x y) := by
  rw [step,Execution.prob_bind_pure]
  apply le_trans (W.state.step_success h1 hgap W.vertex W.height_bounds hm (W.coherent_eligible hc hhi) hlo hhi hmany)
  apply Execution.prob_mono
  intro T hT
  exact W.after_successful hQ T hT

end World
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Schedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Parameters
open scoped NNReal
lemma persistenceSlope_nonneg : 0 ≤ persistenceSlope := by
  unfold persistenceSlope
  apply add_nonneg
  · apply add_nonneg
    · exact add_nonneg (div_nonneg (by norm_num) interpolationA.2.1.le) (div_nonneg (by norm_num) interpolationB.2.1.le)
    · apply mul_nonneg (sq_nonneg _)
      exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) mainQ_pos.le)
        (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) interpolationA.1.le)
  · apply mul_nonneg (sq_nonneg _)
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) secondaryQ_pos.le)
      (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) interpolationB.1.le)
lemma persistenceCount_pos : 0 < persistenceCount := by
  unfold persistenceCount
  have h1 := sq_nonneg (mainN:ℝ)
  have h2 := sq_nonneg ((1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ):ℝ)
  linarith
lemma persistenceLoss_eq (ρ : ℝ) {m : ℕ} (hm : 0 < m) :
    persistenceLoss ρ m=persistenceSlope*ρ+persistenceCount/m := by
  have hm' : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hA := (interpolationA.2.1).ne'
  have hB := (interpolationB.2.1).ne'
  have heA := interpolationA.1.ne'
  have heB := interpolationB.1.ne'
  have hqA := mainQ_pos.ne'
  have hqB := secondaryQ_pos.ne'
  unfold persistenceLoss heightLoss mainLoss mainTestLoss secondaryLoss secondaryTestLoss persistenceSlope persistenceCount
  field_simp
  ring

end PlanarL1.Parameters

end



section

namespace PlanarL1.Execution
variable {α β γ : Type*}
lemma iterate_loss (F : α → Execution α) (E : Execution α) (P : ℕ → α → Prop)
    (ε : ℕ → ℝ) (N : ℕ) (hε : ∀ n<N, 0 ≤ ε n)
    (h : ∀ n<N, ∀ x, P n x → (F x).prob (fun y => ¬P (n+1) y) ≤ ε n) :
    (iterate F E N).prob (fun x => ¬P N x) ≤
      E.prob (fun x => ¬P 0 x)+∑ n ∈ Finset.range N, ε n := by
  induction N with
  | zero => simp only [iterate,Finset.range_zero,Finset.sum_empty,add_zero,le_refl]
  | succ N ih =>
    have hh := conditional_loss (iterate F E N) F (P N) (P (N+1))
      (hε N (Nat.lt_succ_self N)) (h N (Nat.lt_succ_self N))
    have ih' := ih (fun n hn => hε n (Nat.lt_succ_of_lt hn)) (fun n hn => h n (Nat.lt_succ_of_lt hn))
    simp only [iterate] at hh ⊢
    rw [Finset.sum_range_succ]
    linarith
lemma Holds.prob_compl_zero {E : Execution α} {P : α → Prop} (h : E.Holds P) : E.prob (fun x => ¬P x)=0 := by
  rw [E.prob_compl P,h.prob_eq_one,sub_self]
end PlanarL1.Execution

end



section

namespace PlanarL1.Parameters
lemma targetRadius_nonneg {Q : ℝ} (hQ : 0 < Q) (f n : ℕ) : 0 ≤ targetRadius Q f n := by
  unfold targetRadius
  positivity
lemma targetRadius_self {Q : ℝ} (hQ : 0 < Q) (f : ℕ) : targetRadius Q f f=20 := by
  unfold targetRadius
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ hQ.ne')
lemma targetRadius_succ (Q : ℝ) (f n : ℕ) : targetRadius Q f (n+1)=Q*targetRadius Q f n := by
  unfold targetRadius
  rw [pow_succ]
  ring
lemma targetRadius_small {Q : ℝ} (hQ : 1 < Q) {f n : ℕ} (hn : n<f) :
    targetRadius Q f n ≤ 20/Q := by
  have hp : 0 < Q := by linarith
  apply (div_le_div_iff₀ (pow_pos hp f) hp).mpr
  have hh := pow_le_pow_right₀ hQ.le (Nat.succ_le_of_lt hn)
  rw [pow_succ] at hh
  nlinarith
lemma sum_targetRadius {Q : ℝ} (hQ : 1 < Q) (f : ℕ) :
    ∑ n ∈ Finset.range f, targetRadius Q f n ≤ 20/(Q-1) := by
  have hp : 0 < Q := by linarith
  have hm : 0 < Q-1 := by linarith
  have he : (∑ n ∈ Finset.range f, targetRadius Q f n)*(Q-1)=20*(Q^f-1)/Q^f := by
    simp only [targetRadius,← Finset.sum_div,← Finset.mul_sum]
    rw [div_mul_eq_mul_div, mul_assoc,geom_sum_mul]
  apply (le_div_iff₀ hm).mpr
  rw [he]
  apply (div_le_iff₀ (pow_pos hp f)).mpr
  linarith
lemma sum_persistenceLoss {Q : ℝ} (hQ : GoodSpacing Q) {m : ℕ} (hm : 0 < m)
    (f : ℕ) (hf : (f:ℝ)*persistenceCount/m ≤ 1/4) :
    ∑ n ∈ Finset.range f, persistenceLoss (targetRadius Q f n) m ≤ 1/2 := by
  have hs := sum_targetRadius (show 1 < Q by linarith [hQ.1]) f
  have he : (∑ n ∈ Finset.range f, persistenceLoss (targetRadius Q f n) m) =
      persistenceSlope*(∑ n ∈ Finset.range f, targetRadius Q f n)+(f:ℝ)*persistenceCount/m := by
    simp only [persistenceLoss_eq _ hm,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hs persistenceSlope_nonneg
  have hb := hQ.2.2.2.1
  have he' : persistenceSlope*(20/(Q-1))=20*persistenceSlope/(Q-1) := by ring
  rw [he'] at hh
  linarith

end PlanarL1.Parameters

end



section

namespace PlanarL1.Parameters.GoodSpacing
variable {Q : ℝ} (h : GoodSpacing Q)
include h
lemma gt_one : 1 < Q := by linarith [h.1]
end PlanarL1.Parameters.GoodSpacing

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
omit [Fintype V] in
lemma distances_zero : W.Distances 0 W := by intro x y; simp [distance]
lemma next_distances {n : ℕ} {Z : World k V Q} (h : W.Distances n Z) :
    (Z.step g.pos g.one g.gap hm).Holds (W.Distances (n+1)) := by
  apply (Z.step_distances g.pos g.one g.gap hm).mono
  intro T hT x y
  rw [hT,h,pow_succ]
  ring
lemma target_failure {f n : ℕ} (hn : n<f) {x : V} {Z : World k V Q} (h : W.TargetGood f x n Z) :
    (Z.step g.pos g.one g.gap hm).prob (fun T => ¬W.TargetGood f x (n+1) T) ≤
      persistenceLoss (targetRadius Q f n) m := by
  have hp := Z.step_persistence g.pos g.one g.gap hm (targetRadius_nonneg g.pos f n)
    ((targetRadius_small g.gt_one hn).trans g.2.2.1) h.2
  rw [← targetRadius_succ] at hp
  apply le_trans ?_ hp
  apply Execution.Holds.prob_mono
  apply (W.next_distances g hm h.1).mono
  intro T ht hn
  exact fun hc => hn ⟨ht,hc⟩
lemma run_target_failure {f : ℕ} {x : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) :
    (W.run g hm f).prob (fun Z => ¬W.TargetGood f x f Z) ≤ 1/2 := by
  have h0 : (Execution.pure W).Holds (W.TargetGood f x 0) := ⟨W.distances_zero,hstart⟩
  have hh := Execution.iterate_loss (fun Z : World k V Q => Z.step g.pos g.one g.gap hm)
    (.pure W) (W.TargetGood f x) (fun n => persistenceLoss (targetRadius Q f n) m) f
    (fun n hn => by
      rw [persistenceLoss_eq _ hm]
      exact add_nonneg (mul_nonneg persistenceSlope_nonneg (targetRadius_nonneg g.pos f n))
        (div_nonneg persistenceCount_pos.le (Nat.cast_nonneg m)))
    (fun n hn Z hZ => W.target_failure g hm hn hZ)
  rw [h0.prob_compl_zero,zero_add] at hh
  exact hh.trans (sum_persistenceLoss g hm f hmesh)
lemma run_success_probability_oai {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) :
    successChance/2 ≤ (W.run g hm (f+1)).prob (fun Z => Z.Successful (Q*successGain) x y) := by
  have hf := W.run_target_failure g hm hstart hmesh
  rw [Execution.prob_compl] at hf
  have hh := Execution.conditional_success (W.run g hm f)
    (fun Z : World k V Q => Z.step g.pos g.one g.gap hm) (W.TargetGood f x f)
    (fun Z => Z.Successful (Q*successGain) x y) (p := successChance) (by
      intro Z hZ
      apply Z.step_success g.pos g.one g.gap hm hmany
      · simpa only [targetRadius_self g.pos] using hZ.2
      · rw [hZ.1]; exact hlo
      · rw [hZ.1]; exact hhi)
  have hp := mul_le_mul_of_nonneg_left (show 1/2≤(W.run g hm f).prob (W.TargetGood f x f) by linarith) successChance_pos.le
  have hp' : successChance/2 ≤ successChance*(W.run g hm f).prob (W.TargetGood f x f) := by
    nlinarith
  exact hp'.trans hh
end PlanarL1.Columns.Model.World

end



end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarL1.Columns.Model.World.run_success_probability_oai.{u_1} := @OAI.PlanarL1.Columns.Model.World.run_success_probability_oai.{u_1}
