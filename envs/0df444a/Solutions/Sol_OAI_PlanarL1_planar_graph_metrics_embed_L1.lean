-- Prove2me | solution 1 for OAI.PlanarL1.planar_graph_metrics_embed_L1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:00:18.309011+00:00
-- url     : https://prove2.me/submissions/a0b043f3-98df-459c-8fa8-c6095cb4892c

import Mathlib
import Definitions.Def_PlanarL1
import Definitions.Def_OAIQ5T5002
import Theorems.Thm_OAI_PlanarL1_Columns_Model_World_run_success_probability

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

omit [PseudoMetricSpace X] in
lemma clip_movement {s F H : X → ℝ} {B : ℝ} (hB : 0 ≤ B) (x : X)
    (hF : F x ≤ s x+B) : 0 ≤ clip s F H x-s x ∧ clip s F H x-s x ≤ B := by
  constructor
  · exact sub_nonneg.mpr (le_max_left _ _)
  · have : clip s F H x ≤ s x+B := max_le (by linarith) ((min_le_left _ _).trans hF)
    linarith

end PlanarL1.Clipping


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Cuts
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model

namespace Activity

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {M : Model n} (A : Activity M)

lemma graph_le : A.graph ≤ M.link := by
  rintro i j ⟨H,hH,_⟩
  exact M.permitted i j H hH

lemma sum_vector (i : Fin n) (H : ℝ) :
    ∑ S : Set (Fin n), A.vector i H S = A.indicator i H := by
  classical
  by_cases h : A.active i H
  · simp only [A.vector_active h, indicator,h,ite_true]
    simp
  · rw [A.vector_inactive h]
    simp only [Pi.zero_apply,Finset.sum_const_zero,indicator,h,ite_false]

lemma dominates_indicator (i j : Fin n) (s t : ℝ) :
    |A.indicator i s-A.indicator j t| ≤ A.cost i j s t := by
  rw [← A.sum_vector i s,← A.sum_vector j t,← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

lemma cost_of_active_distinct {i j : Fin n} {s t : ℝ}
    (hi : A.active i s) (hj : A.active j t) (hne : A.component i ≠ A.component j) :
    A.cost i j s t = 2 := by
  classical
  have hr : ∀ S : Set (Fin n), |A.vector i s S-A.vector j t S| =
      (if S = A.component i then 1 else 0)+(if S = A.component j then 1 else 0) := by
    intro S
    rw [A.vector_active hi,A.vector_active hj]
    by_cases h₁ : S = A.component i <;> by_cases h₂ : S = A.component j
    · exact False.elim (hne (h₁.symm.trans h₂))
    · simp only [ite_eq_left h₁,ite_eq_right h₂]; norm_num
    · simp only [ite_eq_right h₁,ite_eq_left h₂]; norm_num
    · simp only [ite_eq_right h₁,ite_eq_right h₂]; norm_num
  simp only [cost,hr,Finset.sum_add_distrib]
  norm_num

/-- An inactive terminal tip isolates BOTH of its endpoint columns in the
active-link graph. This uses the terminal-switch standing hypothesis. -/
lemma terminal_isolated {a b : Fin n} {H : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b) (hA : ¬ A.active a H) :
    (∀ k, ¬ A.graph.Adj a k) ∧ (∀ k, ¬ A.graph.Adj b k) := by
  obtain ⟨T,hT,ht⟩ := M.terminal a b (M.permitted a b H hH) hn
  have he : H = T := by simpa only [hT,Set.mem_singleton_iff] using hH
  subst T
  constructor
  · rintro k ⟨U,hU,hu⟩
    exact hA (A.increasing a U H (ht k U (Or.inl hU)) hu)
  · rintro k ⟨U,hU,hu⟩
    exact hA ((A.switch a b H hH).mpr (A.increasing b U H (ht k U (Or.inr hU)) hu))

lemma separated_components {a b x y : Fin n} {H : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b) (hA : ¬ A.active a H)
    (hx : a < x ∧ x < b) (hy : y < a ∨ b < y) : A.component x ≠ A.component y := by
  intro he
  obtain ⟨p⟩ := (A.component_eq_iff x y).mp he
  have hxy : x ≠ y := by omega
  have hp := SimpleGraph.Walk.not_nil_of_ne (p := p) hxy
  obtain ⟨ha,hb⟩ := A.terminal_isolated hH hn hA
  have hsep := ColumnOrder.chord_separation M.noncrossing (M.permitted a b H hH)
    (p.mapLe A.graph_le) hx hy
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hsep
  rcases hsep with hsep | hsep
  · obtain ⟨k,_,hk⟩ := SimpleGraph.adj_of_mem_walk_support p hp hsep
    exact ha k hk
  · obtain ⟨k,_,hk⟩ := SimpleGraph.adj_of_mem_walk_support p hp hsep
    exact hb k hk

/-- Exact labelwise component-certificate separation (sets:component-refinement).
The other switches may change arbitrarily, subject only to the invariants. -/
lemma terminal_certificate {a b x y : Fin n} {H s t : ℝ}
    (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b) (hA : ¬ A.active a H)
    (hx : a < x ∧ x < b) (hy : y < a ∨ b < y)
    (hs : A.active x s) (ht : A.active y t) : A.cost x y s t = 2 :=
  A.cost_of_active_distinct hs ht (A.separated_components hH hn hA hx hy)

end Activity
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model
open MeasureTheory

namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} (A : SetSystem M Ω μ)

lemma integral_pathCost_le {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    (∫ ω, (A.activity ω).pathCost p s t ∂μ) ≤ p.length s t := by
  induction p generalizing s with
  | nil => exact A.vertical_bound _ _ _
  | @cons i k j H _ _ p ih =>
    change (∫ ω, |(A.activity ω).indicator i s-(A.activity ω).indicator i H|+
      (A.activity ω).pathCost p H t ∂μ) ≤ |s-H|+p.length H t
    rw [integral_add (A.vertical_integrable i s H) (A.pathCost_integrable p H t)]
    exact add_le_add (A.vertical_bound i s H) (ih H)

lemma integral_cost_le_length {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    (∫ ω, (A.activity ω).cost i j s t ∂μ) ≤ p.length s t := by
  apply le_trans _ (A.integral_pathCost_le p s t)
  exact integral_mono (A.cost_integrable p s t) (A.pathCost_integrable p s t)
    (fun ω => (A.activity ω).cost_le_pathCost p s t)

lemma integral_cost_le_dist {J : Set ℝ} {root : Fin n} (hJ : IsClosed J)
    (x y : M.Point J root) :
    (∫ ω, (A.activity ω).cost x.column y.column x.height y.height ∂μ) ≤ dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hJ y
  exact (A.integral_cost_le_length p x.height y.height).trans_eq hp

variable [SFinite μ]

attribute [local instance] OAI.PlanarL1.Columns.Model.SetSystem.componentMeasurableSpace
lemma integral_norm_coordinates {J : Set ℝ} {i j : Fin n}
    (p : M.Path J i j) (s t : ℝ) :
    (∫ z, ‖A.coordinateDifference i j s t z‖ ∂μ.prod Measure.count) =
      ∫ ω, (A.activity ω).cost i j s t ∂μ := by
  rw [integral_prod _ (A.integrable_coordinateDifference p s t).norm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only
    rw [integral_count]
    simp only [coordinateDifference,Real.norm_eq_abs,Activity.cost]

lemma norm_refinedMap_sub {J : Set ℝ} {root : Fin n} (o x y : M.Point J root) :
    ‖A.refinedMap o x-A.refinedMap o y‖ =
      ∫ ω, (A.activity ω).cost x.column y.column x.height y.height ∂μ := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ z, ‖(A.refinedMap o x-A.refinedMap o y) z‖ ∂μ.prod Measure.count) =
        ∫ z, ‖A.coordinateDifference x.column y.column x.height y.height z‖ ∂μ.prod Measure.count := by
      apply integral_congr_ae
      have hx := (A.integrable_coordinateDifference (Classical.choice (x.paths_nonempty o))
        x.height o.height).coeFn_toL1
      have hy := (A.integrable_coordinateDifference (Classical.choice (y.paths_nonempty o))
        y.height o.height).coeFn_toL1
      filter_upwards [Lp.coeFn_sub (A.refinedMap o x) (A.refinedMap o y),hx,hy] with z hz hx hy
      change (A.refinedMap o x) z = _ at hx
      change (A.refinedMap o y) z = _ at hy
      rw [hz,Pi.sub_apply,hx,hy]
      congr 1
      simp only [coordinateDifference]
      ring
    _ = _ := A.integral_norm_coordinates (Classical.choice (x.paths_nonempty y)) x.height y.height

omit [SFinite μ] in
lemma unrefined_integrable {J : Set ℝ} {i j : Fin n}
    (p : M.Path J i j) (s t : ℝ) :
    Integrable (fun ω => |(A.activity ω).indicator i s-(A.activity ω).indicator j t|) μ := by
  apply (A.cost_integrable p s t).mono' (((A.measurable_indicator i s).sub
    (A.measurable_indicator j t)).abs.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_abs]
    exact (A.activity ω).dominates_indicator i j s t

lemma refinedMap_dominates {J : Set ℝ} {root : Fin n} (o x y : M.Point J root) :
    (∫ ω, |(A.activity ω).indicator x.column x.height-
      (A.activity ω).indicator y.column y.height| ∂μ) ≤
      ‖A.refinedMap o x-A.refinedMap o y‖ := by
  rw [A.norm_refinedMap_sub]
  let p := Classical.choice (x.paths_nonempty y)
  exact integral_mono (A.unrefined_integrable p x.height y.height)
    (A.cost_integrable p x.height y.height)
    (fun ω => (A.activity ω).dominates_indicator _ _ _ _)

/-- The actual final certificate yields twice its label mass in the refined
real L1 map. Its mass is necessarily finite, although μ itself is infinite. -/
lemma refinedMap_terminal_certificate {J : Set ℝ} {root : Fin n} (o x y : M.Point J root)
    {a b : Fin n} {H : ℝ} (hH : H ∈ M.heights a b) (hn : ¬ Consecutive a b)
    (hx : a < x.column ∧ x.column < b) (hy : y.column < a ∨ b < y.column)
    (E : Set Ω) (hE : MeasurableSet E)
    (hA : ∀ ω ∈ E, ¬ (A.activity ω).active a H)
    (hX : ∀ ω ∈ E, (A.activity ω).active x.column x.height)
    (hY : ∀ ω ∈ E, (A.activity ω).active y.column y.height) :
    μ E < ⊤ ∧ 2*μ.real E ≤ ‖A.refinedMap o x-A.refinedMap o y‖ := by
  classical
  have hbnd : ∀ ω, ‖E.indicator (fun _ => (2:ℝ)) ω‖ ≤
      (A.activity ω).cost x.column y.column x.height y.height := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω,
        (A.activity ω).terminal_certificate hH hn (hA ω hω) hx hy (hX ω hω) (hY ω hω)]
      norm_num
    · rw [Set.indicator_of_notMem hω,norm_zero]
      exact (A.activity ω).cost_nonneg _ _ _ _
  have hi : Integrable (E.indicator (fun _ => (2:ℝ))) μ :=
    (A.cost_integrable (Classical.choice (x.paths_nonempty y)) x.height y.height).mono'
      (measurable_const.indicator hE).aestronglyMeasurable (Filter.Eventually.of_forall hbnd)
  constructor
  · have ht := (integrableOn_const_iff (C := (2:ℝ))).mp
      ((integrable_indicator_iff hE).mp hi)
    simpa using ht
  · rw [A.norm_refinedMap_sub]
    calc
      2*μ.real E = ∫ ω, E.indicator (fun _ => (2:ℝ)) ω ∂μ := by
        rw [integral_indicator_const _ hE,smul_eq_mul,mul_comm]
      _ ≤ _ := integral_mono hi
        (A.cost_integrable (Classical.choice (x.paths_nonempty y)) x.height y.height)
        (fun ω => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbnd ω))

end SetSystem
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Gluing
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.SetPatch
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {A : SetSystem M Ω μ}

lemma selectActive_choice (L : List (SetPatch A)) (i : Fin n) (H : ℝ) :
    (∀ ω, selectActive L ω i H ↔ (A.activity ω).active i H) ∨
      ∃ P ∈ L, ∀ ω, selectActive L ω i H ↔ (P.apply.activity ω).active i H := by
  induction L with
  | nil => exact Or.inl (fun _ => Iff.rfl)
  | cons P L ih =>
    by_cases hi : H ∈ P.domain i
    · right
      refine ⟨P,List.mem_cons_self,?_⟩
      intro ω
      simpa only [selectActive,ite_eq_left hi] using (P.inside hi ω).symm
    · rcases ih with h | ⟨Q,hQ,h⟩
      · left
        intro ω
        simpa only [selectActive,ite_eq_right hi] using h ω
      · right
        refine ⟨Q,List.mem_cons_of_mem P hQ,?_⟩
        intro ω
        simpa only [selectActive,ite_eq_right hi] using h ω

/-- Simultaneous disjoint main clipping has the one-patch movement bound,
not the sum over cells. Covers all points, not just the listed vertices. -/
lemma batch_movement (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    {b : ℝ} (hb : 0 ≤ b)
    (hp : ∀ P ∈ L, ∀ i H, (∫ ω, |(P.apply.activity ω).indicator i H-(A.activity ω).indicator i H| ∂μ) ≤ b)
    (i : Fin n) (H : ℝ) :
    (∫ ω, |((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H| ∂μ) ≤ b := by
  rcases selectActive_choice L i H with h | ⟨P,hP,h⟩
  · have he : (fun ω => |((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H|) =
        fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,batch_active,h,sub_self,abs_zero]
    rw [he,integral_zero]
    exact hb
  · have he : (fun ω => |((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H|) =
        fun ω => |(P.apply.activity ω).indicator i H-(A.activity ω).indicator i H| := by
      funext ω
      simp only [Activity.indicator,batch_active,h]
    rw [he]
    exact hp P hP i H

lemma batch_movement_integrable (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    (hp : ∀ P ∈ L, ∀ i H, Integrable
      (fun ω => (P.apply.activity ω).indicator i H-(A.activity ω).indicator i H) μ)
    (i : Fin n) (H : ℝ) : Integrable
      (fun ω => ((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H) μ := by
  rcases selectActive_choice L i H with h | ⟨P,hP,h⟩
  · have he : (fun ω => ((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H) =
        fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,batch_active,h,sub_self]
    rw [he]
    exact integrable_zero _ _ _
  · have he : (fun ω => ((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H) =
        fun ω => (P.apply.activity ω).indicator i H-(A.activity ω).indicator i H := by
      funext ω
      simp only [Activity.indicator,batch_active,h]
    rw [he]
    exact hp P hP i H

end PlanarL1.Columns.Model.SetPatch


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

lemma movement (hJ : IsCompact J) (hthin : R.a ≤ (1/1000:ℝ)/1000)
    (v x : M.Point J root) (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E)
    (hδ : R.δ = E/8) (H : M.Point J root → ℝ) :
    0 ≤ Clipping.clip (old F hJI) (proposal F hJI R q C v α E) H x-old F hJI x ∧
    Clipping.clip (old F hJI) (proposal F hJI R q C v α E) H x-old F hJI x ≤ 1+(1:ℝ)/100 := by
  apply Clipping.clip_movement (by norm_num)
  have hf := (proposal_accuracy F hJI R q C hJ v x hα hE hδ).2
  have hc := Clipping.envelope_le_cap (boundary R q C) (old F hJI) (old F hJI v+1) (1-R.ζ) x
  have hvx := (abs_le.mp (variation F hJI R q C hthin v x hv hx)).2
  change input F hJI R q C v x ≤ old F hJI v+1 at hc
  linarith

end MainCell
end PlanarL1.Columns.Model


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Ambient
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
variable {k : ℕ} {M : Model (k+1)}

namespace BData
variable {A : Ambient M} {c : ℝ}

lemma increment_magnitude (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) (hrec : D.Recorded H hc hcr)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (T : D.band) :
    |(D.auxiliaryField (D.incrementAuxiliary H r region e hc hcr hr hcross) lam hlam).value i T -
      D.value lam i T| ≤ (lam:ℝ)*10*r := by
  cases D with
  | ordinary D =>
    change |D.value i T-D.value i T| ≤ _
    rw [sub_self,abs_zero]
    positivity
  | ordered D =>
    dsimp only [BData.value]
    erw [increment_difference D H r region e hc hcr hr hcross hrec lam hlam,
      abs_mul,abs_of_nonneg lam.coe_nonneg]
    have hb : |Increment.signedDamped e (c*r) r
        ((D.base.transverse (by norm_num) D.lower D.upper).value i)
        (fun U : D.band => Increment.taper regionᶜ r (A.point i U.val)) T| ≤ 10*r := by
      have hs := Increment.scalar_magnitude (mul_pos hc hr) hr (by nlinarith : 2*(c*r) ≤ 8*r)
        (t := (D.base.transverse (by norm_num) D.lower D.upper).value i T)
      have ht := Increment.taper_bounds (S := regionᶜ) hr (A.point i T.val)
      have hh : |Increment.damped (c*r) r
          ((D.base.transverse (by norm_num) D.lower D.upper).value i)
          (fun U : D.band => Increment.taper regionᶜ r (A.point i U.val)) T| ≤ 10*r := by
        unfold Increment.damped
        rw [abs_mul,abs_of_nonneg ht.1]
        exact (mul_le_mul hs ht.2 ht.1 (by positivity)).trans_eq (mul_one _)
      cases e <;> simpa only [Increment.signedDamped,Bool.false_eq_true,ite_false,ite_true,abs_neg] using hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb lam.coe_nonneg

end BData

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  (S : BState M κ lam Ω μ) (A : Ambient M)

lemma increment_movement {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) (i : Fin (k+1)) (H : ℝ) :
    (∫ ω, |((S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).sets.activity ω).indicator i H-
      (S.sets.activity ω).indicator i H| ∂μ) ≤ κ*(lam:ℝ)*10*r := by
  change (∫ ω, |(S.fieldActivity (S.incrementFields A hist sign hc hcr hr hcross hlam)
    hk hsmall hlam (S.increment_boundary A hist sign hc hcr hr hcross hrec hk hlam hboundary) ω).indicator i H-(S.sets.activity ω).indicator i H| ∂μ) ≤ _
  simp_rw [S.field_indicator,S.old_indicator]
  rw [(S.labels (S.name i H)).distance,sub_self,abs_zero,max_eq_right (abs_nonneg _)]
  unfold newValue oldValue
  rw [← mul_sub,abs_mul,abs_of_nonneg hk]
  have hb := (S.chart (S.name i H)).increment_magnitude (hist (S.name i H)) r
    (S.region A (S.name i H)) (sign (S.name i H)) hc hcr hr (hcross (S.name i H))
    (hrec (S.name i H)) lam hlam i ⟨H,S.height_in i H⟩
  simpa only [mul_assoc,incrementFields] using mul_le_mul_of_nonneg_left hb hk

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

lemma mean_lower_of_event (E : Execution α) {P : α → Prop} {f : α → ℝ} {c : ℝ}
    (hf : ∀ x, 0 ≤ f x) (h : ∀ x, P x → c ≤ f x) : c*E.prob P ≤ E.mean f := by
  classical
  rw [prob,← mean_smul]
  apply E.mean_mono
  intro x
  by_cases hx : P x <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  · exact h x hx
  · exact hf x

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

lemma mean_sum (E : Execution α) [Fintype ι] (f : ι → α → ℝ) :
    E.mean (fun x => ∑ i, f i x)=∑ i, E.mean (f i) := by
  classical
  induction E with
  | pure x => rfl
  | choose n F ih =>
    simp only [mean,ih]
    rw [Finset.sum_comm,Finset.sum_div]

end PlanarL1.Execution


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_FiniteL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.FiniteL1

open MeasureTheory

variable {I : Type*} [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I]

lemma norm_ofFunction (f : I → ℝ) : ‖ofFunction f‖ = ∑ i, |f i| := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ i, ‖ofFunction f i‖ ∂Measure.count) = ∫ i, |f i| ∂Measure.count := by
      apply integral_congr_ae
      exact (MemLp.coeFn_toLp (MemLp.of_discrete : MemLp f 1 Measure.count)).mono fun i h => by
        change ‖(MemLp.of_discrete : MemLp f 1 Measure.count).toLp f i‖ = |f i|
        rw [h,Real.norm_eq_abs]
    _ = _ := integral_count _

lemma ofFunction_sub (f g : I → ℝ) :
    ofFunction f - ofFunction g = ofFunction (fun i => f i-g i) := by
  exact (MemLp.toLp_sub (MemLp.of_discrete : MemLp f 1 Measure.count)
    (MemLp.of_discrete : MemLp g 1 Measure.count)).symm

lemma norm_sub (f g : I → ℝ) : ‖ofFunction f-ofFunction g‖ = ∑ i, |f i-g i| := by
  rw [ofFunction_sub,norm_ofFunction]

lemma norm_cutMap {V : Type*} (cut : I → Set V) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (x y : V) :
    ‖cutMap cut weight x-cutMap cut weight y‖ =
      ∑ i, weight i*|((cut i).indicator (fun _ => (1:ℝ)) x)-
        ((cut i).indicator (fun _ => (1:ℝ)) y)| := by
  classical
  rw [cutMap,cutMap,norm_sub]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ cut i <;> by_cases hy : y ∈ cut i <;>
    simp [hx,hy,abs_of_nonneg (hweight i)]

end PlanarL1.FiniteL1



end

section

namespace PlanarL1.FiniteL1
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] (μ : Measure Ω)

namespace BinarySystem
variable {μ} (B : BinarySystem (V := V) μ)

lemma measurable_fiber (S : Set V) : MeasurableSet (B.fiber S) := by
  have he : B.fiber S = ⋂ v, {ω | B.active ω v ↔ v ∈ S} := by ext ω; simp [fiber]
  rw [he]
  apply MeasurableSet.iInter
  intro v
  by_cases hv : v ∈ S
  · simpa only [hv,iff_true] using B.measurable v
  · simpa only [hv,iff_false,Set.compl_ofPred] using (B.measurable v).compl

lemma measurable_fiberValue (S : Set V) : Measurable (B.fiberValue S) :=
  Measurable.ite (B.measurable_fiber S) measurable_const measurable_const

lemma measurable_contribution (S : Set V) : Measurable (B.contribution S) := by
  unfold contribution
  split_ifs
  · exact B.measurable_fiberValue S
  · exact measurable_const

lemma integrable_contribution (S : Set V) : Integrable (B.contribution S) μ := by
  by_cases hp : Proper S
  · obtain ⟨x,hx⟩ := hp.1
    obtain ⟨y,hy⟩ := hp.2
    apply (B.integrable x y).mono' (B.measurable_contribution S).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (B.contribution_nonneg S ω)]
    by_cases hf : ω ∈ B.fiber S
    · have hfx := (hf x).mpr hx
      have hfy : ¬B.active ω y := fun h => hy ((hf y).mp h)
      simp only [contribution,ite_eq_left hp,fiberValue,ite_eq_left hf,ite_eq_left hfx,ite_eq_right hfy,
        sub_zero,abs_one,le_refl]
    · simp only [contribution,ite_eq_left hp,fiberValue,ite_eq_right hf]
      exact abs_nonneg _
  · have he : B.contribution S = fun _ => 0 := by
      funext ω
      exact ite_eq_right hp
    rw [he]
    exact integrable_zero _ _ _

omit [Fintype V] in
lemma cutCost_eq_zero_of_not_proper {S : Set V} (hS : ¬Proper S) (x y : V) :
    cutCost S x y = 0 := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp [cutCost,hx,hy]
  · exact (hS ⟨⟨x,hx⟩,⟨y,hy⟩⟩).elim
  · exact (hS ⟨⟨y,hy⟩,⟨x,hx⟩⟩).elim
  · simp [cutCost,hx,hy]

lemma sum_contribution (x y : V) (ω : Ω) :
    ∑ S : Set V, B.contribution S ω * cutCost S x y =
      |B.indicator x ω-B.indicator y ω| := by
  classical
  let S₀ : Set V := {v | B.active ω v}
  have hf : ω ∈ B.fiber S₀ := by intro v; rfl
  have ho : ∀ S, S ≠ S₀ → B.contribution S ω = 0 := by
    intro S hS
    have hnf : ω ∉ B.fiber S := by
      intro h
      apply hS
      ext v
      exact (h v).symm
    simp only [contribution,fiberValue,ite_eq_right hnf,ite_self]
  rw [Finset.sum_eq_single S₀ (fun S _ hs => by rw [ho S hs,zero_mul])
    (fun h => (h (Finset.mem_univ _)).elim)]
  have hc : cutCost S₀ x y = |B.indicator x ω-B.indicator y ω| := by
    simp only [cutCost,Set.indicator_apply,indicator,S₀,Set.mem_ofPred_eq]
  by_cases hp : Proper S₀
  · rw [contribution,ite_eq_left hp,fiberValue,ite_eq_left hf,one_mul,hc]
  · rw [contribution,ite_eq_right hp,zero_mul,← hc,cutCost_eq_zero_of_not_proper hp]

/-- Exact cut coefficients, not a finite-dimensional approximation of the label
metric. Empty/full cuts are zero; proper weights are finite by pair integrability. -/
lemma cut_decomposition (x y : V) :
    ∑ S : Set V, B.weight S * cutCost S x y =
      ∫ ω, |B.indicator x ω-B.indicator y ω| ∂μ := by
  classical
  calc
    _ = ∑ S : Set V, ∫ ω, B.contribution S ω*cutCost S x y ∂μ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [integral_mul_const]
      rfl
    _ = ∫ ω, ∑ S : Set V, B.contribution S ω*cutCost S x y ∂μ := by
      symm
      exact integral_finsetSum _ (fun S _ => (B.integrable_contribution S).mul_const _)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (B.sum_contribution x y))

end BinarySystem
end PlanarL1.FiniteL1


end

section

namespace PlanarL1.FiniteL1
open MeasureTheory

namespace CutFamily
variable {V α ι : Type*} [Fintype V]

lemma distance_nonneg (C : CutFamily V) (x y : V) : 0 ≤ C.distance x y := by
  classical
  exact Finset.sum_nonneg (fun S _ => mul_nonneg (C.nonneg S) (abs_nonneg _))

lemma distance_ofBinary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : BinarySystem (V := V) μ) (x y : V) :
    (ofBinary B).distance x y=∫ ω, |B.indicator x ω-B.indicator y ω| ∂μ :=
  B.cut_decomposition x y

lemma distance_add (C D : CutFamily V) (x y : V) :
    (C.add D).distance x y=C.distance x y+D.distance x y := by
  classical
  simp only [distance,add,add_mul,Finset.sum_add_distrib]

lemma distance_sum [Fintype ι] (C : ι → CutFamily V) (x y : V) :
    (sum C).distance x y=∑ i, (C i).distance x y := by
  classical
  simp only [distance,sum,Finset.sum_mul]
  exact Finset.sum_comm

lemma distance_average (E : Execution α) (C : α → CutFamily V) (x y : V) :
    (average E C).distance x y=E.mean (fun a => (C a).distance x y) := by
  classical
  simp only [distance,average,Execution.mean_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [mul_comm,← Execution.mean_smul]
  congr 1
  funext a
  exact mul_comm _ _

lemma distance_scale (c : ℝ) (hc : 0 ≤ c) (C : CutFamily V) (x y : V) :
    (scale c hc C).distance x y=c*C.distance x y := by
  classical
  simp only [distance,scale,Finset.mul_sum,mul_assoc]

attribute [local instance] OAI.PlanarL1.FiniteL1.CutFamily.instMeasurableSpaceSet
lemma norm_embedding (C : CutFamily V) (x y : V) :
    ‖C.embedding x-C.embedding y‖=C.distance x y := by
  classical
  exact norm_cutMap id C.weight C.nonneg x y

/-- The last rescaling step in the manuscript, using actual real Lp1. The
geometric lower bound is a prerequisite proved by the random construction. -/
theorem embedding_of_bounds (C : CutFamily V) (d : V → V → ℝ) {a b : ℝ}
    (ha : 0 < a) (hl : ∀ x y, a*d x y ≤ C.distance x y)
    (hu : ∀ x y, C.distance x y ≤ b*d x y) :
    ∃ f : V → Lp ℝ 1 (Measure.count : Measure (Set V)),
      ∀ x y, d x y ≤ ‖f x-f y‖ ∧ ‖f x-f y‖ ≤ (b/a)*d x y := by
  refine ⟨(scale a⁻¹ (inv_nonneg.mpr ha.le) C).embedding,?_⟩
  intro x y
  rw [norm_embedding,distance_scale]
  constructor
  · have h := mul_le_mul_of_nonneg_left (hl x y) (inv_nonneg.mpr ha.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using h
  · have h := mul_le_mul_of_nonneg_left (hu x y) (inv_nonneg.mpr ha.le)
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

end CutFamily
end PlanarL1.FiniteL1



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

lemma old_indicator (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (S.lift.sets.activity ω).indicator i H =
      Threshold.chartValue H (κ*(U.data.constant+U.data.orientation*
        MainCell.old U.comparison U.sub_old (MainCell.cellPoint U.tree U.phase U.cell i H hi)))
        ((S.labels U.index).lift.value ω) := by
  simp only [Activity.indicator,← U.old_agreement ω i H hi,Threshold.active,
    Threshold.chartValue,Threshold.half]

/-- Actual label mass moved by one kept main cell equals the oriented scalar
raise times κ. This compares the new sets with the lifted old sets. -/
lemma movement_exact (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (∫ ω, |(U.patch.apply.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H| ∂(μ.prod Threshold.fair)) =
      κ*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
          U.noise U.error U.shield_offset U.lo (MainCell.cellPoint U.tree U.phase U.cell i H hi)-
        MainCell.old U.comparison U.sub_old (MainCell.cellPoint U.tree U.phase U.cell i H hi)) := by
  simp_rw [U.indicator_inside _ i H hi,U.old_indicator _ i H hi]
  rw [(S.labels U.index).lift.distance]
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg _)]
  have hm := MainCell.movement U.comparison U.sub_old U.tree U.phase U.cell
    U.compact_band U.thin U.anchor (MainCell.cellPoint U.tree U.phase U.cell i H hi)
      U.anchor_mem ((MainCell.mem_domain U.tree U.phase U.cell).mp hi).1
      U.noise_bounds U.error_pos.le U.delta_eq
        (fun x => Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
          U.shield_offset x.height)
  rw [show κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
      U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo
        (MainCell.cellPoint U.tree U.phase U.cell i H hi))-
    κ*(U.data.constant+U.data.orientation*MainCell.old U.comparison U.sub_old
        (MainCell.cellPoint U.tree U.phase U.cell i H hi)) =
    κ*U.data.orientation*(MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo (MainCell.cellPoint U.tree U.phase U.cell i H hi)-
      MainCell.old U.comparison U.sub_old (MainCell.cellPoint U.tree U.phase U.cell i H hi)) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]
  congr 1
  exact abs_of_nonneg hm.1

lemma movement_integrable (i : Fin n) (H : ℝ) :
    Integrable (fun ω => (U.patch.apply.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H) (μ.prod Threshold.fair) := by
  by_cases hi : H ∈ MainCell.domain U.tree U.phase U.cell i
  · simp_rw [U.indicator_inside _ i H hi,U.old_indicator _ i H hi]
    exact (S.labels U.index).lift.integrable_difference _ _ _ _
  · have he : (fun ω => (U.patch.apply.activity ω).indicator i H-
        (S.lift.sets.activity ω).indicator i H) = fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,U.patch.unchanged hi ω,sub_self]
    rw [he]
    exact integrable_zero _ _ _

lemma movement_bound (i : Fin n) (H : ℝ) :
    (∫ ω, |(U.patch.apply.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H| ∂(μ.prod Threshold.fair)) ≤ κ*(1+(1:ℝ)/100) := by
  by_cases hi : H ∈ MainCell.domain U.tree U.phase U.cell i
  · rw [U.movement_exact i H hi]
    apply mul_le_mul_of_nonneg_left _ U.kappa_nonneg
    exact (MainCell.movement U.comparison U.sub_old U.tree U.phase U.cell
      U.compact_band U.thin U.anchor (MainCell.cellPoint U.tree U.phase U.cell i H hi)
      U.anchor_mem ((MainCell.mem_domain U.tree U.phase U.cell).mp hi).1
      U.noise_bounds U.error_pos.le U.delta_eq _).2
  · have he : (fun ω => |(U.patch.apply.activity ω).indicator i H-
        (S.lift.sets.activity ω).indicator i H|) = fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,U.patch.unchanged hi ω,sub_self,abs_zero]
    rw [he,integral_zero]
    positivity [U.kappa_nonneg]

end OrdinaryState.MainStep
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainFamily
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.OrdinaryState.MainBatch
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : OrdinaryState M κ Ω μ} (B : MainBatch S)

lemma point_description (i : Fin n) (H : ℝ) :
    (∃ q : Fin B.count, ∀ ω, (B.sets.activity ω).active i H ↔
      ((B.step q).patch.apply.activity ω).active i H) ∨
    (∀ ω, (B.sets.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H) := by
  classical
  by_cases h : ∃ q : Fin B.count, H ∈ (B.step q).patch.domain i
  · obtain ⟨q,hq⟩ := h
    exact Or.inl ⟨q,fun ω => SetPatch.batch_inside _ B.overlap
      (List.mem_ofFn.mpr ⟨q,rfl⟩) ω i H hq⟩
  · right
    intro ω
    apply SetPatch.batch_old _ B.overlap ω i H
    intro P hP
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
    exact (B.step q).patch.unchanged (fun hh => h ⟨q,hh⟩) ω

lemma movement_integrable (i : Fin n) (H : ℝ) :
    Integrable (fun ω => (B.sets.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H) (μ.prod Threshold.fair) := by
  rcases B.point_description i H with ⟨q,hq⟩ | h
  · have he (ω) : (B.sets.activity ω).indicator i H=((B.step q).patch.apply.activity ω).indicator i H := by
      simp only [Activity.indicator,hq ω]
    simp_rw [he]
    exact (B.step q).movement_integrable i H
  · have he (ω) : (B.sets.activity ω).indicator i H=(S.lift.sets.activity ω).indicator i H := by
      simp only [Activity.indicator,h ω]
    simp only [he,sub_self]
    exact integrable_zero _ _ _

/-- The number of simultaneous cells never enters the movement bound. -/
lemma movement_bound (hκ : 0≤κ) (i : Fin n) (H : ℝ) :
    (∫ ω, |(B.sets.activity ω).indicator i H-
      (S.lift.sets.activity ω).indicator i H| ∂(μ.prod Threshold.fair)) ≤ κ*(1+(1:ℝ)/100) := by
  rcases B.point_description i H with ⟨q,hq⟩ | h
  · have he (ω) : (B.sets.activity ω).indicator i H=((B.step q).patch.apply.activity ω).indicator i H := by
      simp only [Activity.indicator,hq ω]
    simp_rw [he]
    exact (B.step q).movement_bound i H
  · have he (ω) : (B.sets.activity ω).indicator i H=(S.lift.sets.activity ω).indicator i H := by
      simp only [Activity.indicator,h ω]
    simp only [he,sub_self,abs_zero,integral_zero]
    positivity

end PlanarL1.Columns.Model.OrdinaryState.MainBatch

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

lemma seedDistance_nonneg (x : M.Point J root) : 0 ≤ seedDistance S x := infDist_nonneg

lemma shallow_cap (hζ : R.ζ = (1:ℝ)/10) {radius pc : ℝ} (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (x : M.Point J root) :
    shallow R S pc radius α x ≤ pc+(51/1000:ℝ)*radius := by
  have h := (abs_le.mp (approx_accuracy R S hζ hδ hα x)).1
  dsimp only [shallow]
  linarith [seedDistance_nonneg S x]

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

lemma replacement_movement (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    (hζ : R.ζ = (1:ℝ)/10) {pc radius αo αh lo : ℝ} (hr : 0 ≤ radius)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    {x : M.Point J root} (hx : seedDistance S x ≤ radius) :
    |replacement R S old L ordinary pc radius αo αh lo α x-old x| ≤ (51/10:ℝ)*radius := by
  have hold : old x ≤ replacement R S old L ordinary pc radius αo αh lo α x := le_max_left _ _
  rw [abs_of_nonneg (sub_nonneg.mpr hold)]
  apply sub_le_iff_le_add.mpr
  apply max_le
  · linarith
  · apply (min_le_left _ _).trans
    have hsp : spatial R S L ordinary pc radius αo α x ≤ shallow R S pc radius α x := by
      cases ordinary
      · exact le_rfl
      · exact min_le_left _ _
    have hcap := shallow_cap R S hζ hδ hα x (pc := pc)
    have hnear := (abs_le.mp (replacement_near S old hS hOld hseed hx)).1
    linarith

end PlanarL1.Columns.Model.SecondaryCell




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
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SetSystem
lemma separation_nonneg (S : SetSystem M Ω μ) (i j : Fin (k+1)) (H T : ℝ) :
    0≤S.separation i H j T := integral_nonneg (fun _ => abs_nonneg _)
end SetSystem

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

lemma cutoffGain_pos : 0 < cutoffGain := by norm_num [cutoffGain,a₂,kappaA,a₁,EA,epsilon,kappaB,R]

end PlanarL1.Columns.Model.VertexTests

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

namespace PlanarL1.Columns.Model.BState.SecondaryBatch
open MeasureTheory
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
variable (B : SecondaryBatch S)

lemma indicator_inside (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (h : H ∈ B.domain i) :
    (B.patch.apply.activity w).indicator i H=
      Threshold.chartValue H (B.converted i H) ((S.labels B.index).lift.value w) := by
  simp only [Activity.indicator,B.patch.inside h w]
  rfl

end PlanarL1.Columns.Model.BState.SecondaryBatch

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

namespace PlanarL1.Parameters
open scoped NNReal
lemma mainRadius_pos : 0 < mainRadius := by norm_num [mainRadius,zetaA,EA,epsilon]
lemma secondaryRadius_pos : 0 < secondaryRadius := by norm_num [secondaryRadius,zetaB,EB,R]
lemma persistenceRadius_pos : 0 < persistenceRadius := by
  exact lt_min (div_pos interpolationA.1 (by norm_num))
    (lt_min mainRadius_pos (lt_min (by norm_num [R]) secondaryRadius_pos))
end PlanarL1.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SelectedGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Parameters
lemma secondaryChance_pos : 0 < secondaryChance := by unfold secondaryChance; positivity
end PlanarL1.Parameters

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

namespace PlanarL1.Columns.Model.BState
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}

namespace SecondaryStep
variable {J : Set ℝ} {root : Fin (k+1)} (U : SecondaryStep S J root)
lemma full_movement (i : Fin (k+1)) (H : U.data.band) :
    |U.fullReplacement i H-U.comparison.value i H| ≤ (51/1000:ℝ) := by
  by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · rw [U.fullReplacement_inside i H hd,←U.point_old hd]
    have hh := SecondaryCell.replacement_movement U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      (αo := U.ordered_offset) (αh := U.shield_offset) (lo := U.lo)
      U.seeds_nonempty U.old_lipschitz U.zeta_eq U.radius_nonneg U.delta_eq U.noise_bounds
      U.seed_near (SecondaryCell.point_distance U.seeds U.radius hd)
    exact hh.trans (by linarith [U.radius_small])
  · rw [U.fullReplacement_outside i H hd,sub_self,abs_zero]
    norm_num
end SecondaryStep

namespace SecondaryBatch
variable (B : SecondaryBatch S)
lemma selected_movement (i : Fin (k+1)) (H : B.data.band) :
    |(B.selected i H).value-κ*B.comparison.value i H| ≤ κ*(51/1000:ℝ) := by
  rcases B.selected_cases i H with he|⟨a,he⟩
  · rw [he]; simp only [sub_self,abs_zero]
    exact mul_nonneg B.kappa_nonneg (by norm_num)
  · rw [he]; change |(B.groupNamed a i H).value-κ*B.comparison.value i H| ≤ _
    rw [B.groupNamed_value,←B.step_comparison a i H,←mul_sub,abs_mul,abs_of_nonneg B.kappa_nonneg]
    exact mul_le_mul_of_nonneg_left ((B.step a).full_movement i (B.groupHeight a H)) B.kappa_nonneg

lemma old_indicator_inside (w : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (hd : H ∈ B.domain i) :
    (S.lift.sets.activity w).indicator i H=Threshold.chartValue H
      (κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,B.domain_band hd⟩))
      ((S.labels B.index).lift.value w) := by
  have hr := S.represents_named w.1 i H B.index (B.domain_name hd) (B.domain_band hd)
  have he := B.data.comparison_convert lam B.lambda_bound B.positive i ⟨H,B.domain_band hd⟩
  change (S.sets.activity w.1).active i H ↔ Threshold.active (S.labels B.index) H
    (κ*B.data.value lam i ⟨H,B.domain_band hd⟩) w.1 at hr
  rw [he] at hr
  change (S.sets.activity w.1).indicator i H=_
  simp only [Activity.indicator,Threshold.chartValue,Threshold.half,Threshold.active] at *
  exact if_congr hr rfl rfl

lemma movement_integrable (i : Fin (k+1)) (H : ℝ) : Integrable
    (fun w => (B.patch.apply.activity w).indicator i H-(S.lift.sets.activity w).indicator i H)
      (μ.prod Threshold.fair) := by
  by_cases hd : H ∈ B.domain i
  · simp_rw [B.indicator_inside _ i H hd,B.old_indicator_inside _ i H hd]
    exact (S.labels B.index).lift.integrable_difference _ _ _ _
  · have he (w : Ω × Bool) : (B.patch.apply.activity w).indicator i H=(S.lift.sets.activity w).indicator i H := by
      simp only [Activity.indicator,B.patch.unchanged hd w]
    simp only [he,sub_self]
    exact integrable_zero _ _ _

lemma movement_bound (i : Fin (k+1)) (H : ℝ) :
    (∫ w, |(B.patch.apply.activity w).indicator i H-(S.lift.sets.activity w).indicator i H| ∂μ.prod Threshold.fair)
      ≤ κ*(51/1000:ℝ) := by
  by_cases hd : H ∈ B.domain i
  · simp_rw [B.indicator_inside _ i H hd,B.old_indicator_inside _ i H hd]
    rw [(S.labels B.index).lift.distance,sub_self,abs_zero,max_eq_right (abs_nonneg _),
      B.converted_on i H (B.domain_band hd)]
    rw [show κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,B.domain_band hd⟩).value-
      κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,B.domain_band hd⟩)=
      B.data.orientation B.positive*((B.selected i ⟨H,B.domain_band hd⟩).value-κ*B.comparison.value i ⟨H,B.domain_band hd⟩) by ring,
      abs_mul,B.data.orientation_unit,one_mul]
    exact B.selected_movement i ⟨H,B.domain_band hd⟩
  · have he (w : Ω × Bool) : (B.patch.apply.activity w).indicator i H=(S.lift.sets.activity w).indicator i H := by
      simp only [Activity.indicator,B.patch.unchanged hd w]
    simp only [he,sub_self,abs_zero,integral_zero]
    exact mul_nonneg B.kappa_nonneg (by norm_num)
end SecondaryBatch

namespace SecondaryLayer
variable (B : SecondaryLayer S)
lemma movement_integrable (i : Fin (k+1)) (H : ℝ) : Integrable
    (fun w => (B.sets.activity w).indicator i H-(S.lift.sets.activity w).indicator i H)
      (μ.prod Threshold.fair) := by
  apply SetPatch.batch_movement_integrable
  intro P hP i H
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.batch a).movement_integrable i H
lemma movement_bound (hκ : 0 ≤ κ) (i : Fin (k+1)) (H : ℝ) :
    (∫ w, |(B.sets.activity w).indicator i H-(S.lift.sets.activity w).indicator i H| ∂μ.prod Threshold.fair)
      ≤ κ*(51/1000:ℝ) := by
  apply SetPatch.batch_movement _ _ (mul_nonneg hκ (by norm_num))
  intro P hP i H
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.batch a).movement_bound i H
end SecondaryLayer
end PlanarL1.Columns.Model.BState

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
namespace SetSystem
variable (S T : SetSystem M Ω μ)
lemma separation_survival {J : Set ℝ} {r : Fin (k+1)} (x y : M.Point J r)
    (hmove : ∀ i H, Integrable (fun w => (T.activity w).indicator i H-(S.activity w).indicator i H) μ) :
    S.separation x.column x.height y.column y.height ≤
      T.separation x.column x.height y.column y.height+
        S.movement T x.column x.height+S.movement T y.column y.height := by
  let p := Classical.choice (x.paths_nonempty y)
  have hi := T.unrefined_integrable p x.height y.height
  have hx := (hmove x.column x.height).abs
  have hy := (hmove y.column y.height).abs
  have hp (w : Ω) : |(S.activity w).indicator x.column x.height-(S.activity w).indicator y.column y.height| ≤
      |(T.activity w).indicator x.column x.height-(T.activity w).indicator y.column y.height|+
        |(T.activity w).indicator x.column x.height-(S.activity w).indicator x.column x.height|+
        |(T.activity w).indicator y.column y.height-(S.activity w).indicator y.column y.height| := by
    linarith [abs_sub_le ((S.activity w).indicator x.column x.height)
      ((T.activity w).indicator x.column x.height) ((S.activity w).indicator y.column y.height),
      abs_sub_le ((T.activity w).indicator x.column x.height)
      ((T.activity w).indicator y.column y.height) ((S.activity w).indicator y.column y.height),
      abs_sub_comm ((S.activity w).indicator x.column x.height) ((T.activity w).indicator x.column x.height)]
  have he := integral_mono (S.unrefined_integrable p x.height y.height) ((hi.add hx).add hy) hp
  simp only [Pi.add_apply] at he
  have he1 := integral_add (hi.add hx) hy
  have he2 := integral_add hi hx
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2] at he
  exact he
end SetSystem

namespace PairGeometry
variable {V : Type*} {A : Ambient M} {S T : OrdinaryState M Parameters.kappaA Ω μ}
variable {v : V → M.Point Set.univ A.root} {x y : V} {b B : ℝ}
lemma Certificate.survive (h : Certificate A S v (x := x) (y := y) b) (hb : 0<b)
    (hmove : ∀ i H, Integrable (fun w => (T.sets.activity w).indicator i H-(S.sets.activity w).indicator i H) μ)
    (hbound : ∀ i H, S.sets.movement T.sets i H≤B) :
    Certificate A T v (x := x) (y := y) (b-3*B) := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  have hfin : μ E<⊤ := by
    by_contra hh
    have ht : μ E=⊤ := top_unique (not_lt.mp hh)
    have hz : μ.real E=0 := by simp [Measure.real,ht]
    linarith
  let F : Set Ω := E ∩ {w | (T.sets.activity w).active (v x).column (v x).height} ∩
      {w | (T.sets.activity w).active (v y).column (v y).height} ∩
      {w | ¬(T.sets.activity w).active a H}
  have hF : MeasurableSet F := ((hE.inter (T.sets.measurable_active _ _)).inter
    (T.sets.measurable_active _ _)).inter (T.sets.measurable_active _ _).compl
  have hFE : F⊆E := fun _ h => h.1.1.1
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hE).mpr ((integrableOn_const_iff).mpr (Or.inr hfin))
  have hJ : Integrable (F.indicator (fun _ => (1:ℝ))) μ :=
    (integrable_indicator_iff hF).mpr ((integrableOn_const_iff).mpr (Or.inr ((measure_mono hFE).trans_lt hfin)))
  have hC (w : Ω) : E.indicator (fun _ => (1:ℝ)) w ≤
      F.indicator (fun _ => (1:ℝ)) w+
      |(T.sets.activity w).indicator (v x).column (v x).height-(S.sets.activity w).indicator (v x).column (v x).height|+
      |(T.sets.activity w).indicator (v y).column (v y).height-(S.sets.activity w).indicator (v y).column (v y).height|+
      |(T.sets.activity w).indicator a H-(S.sets.activity w).indicator a H| := by
    by_cases hw : w∈E
    · have h1 := hx w hw; have h2 := hy w hw; have h3 := hn w hw
      by_cases htx : (T.sets.activity w).active (v x).column (v x).height <;>
      by_cases hty : (T.sets.activity w).active (v y).column (v y).height <;>
      by_cases hta : (T.sets.activity w).active a H <;>
      simp [F,hw,htx,hty,hta,Activity.indicator,h1,h2,h3]
    · have hf : w∉F := fun he => hw (hFE he)
      simp only [Set.indicator_of_notMem hw,Set.indicator_of_notMem hf,zero_add]
      positivity
  have he := integral_mono hI (((hJ.add (hmove _ _).abs).add (hmove _ _).abs).add (hmove _ _).abs) hC
  simp only [Pi.add_apply] at he
  rw [integral_add,integral_add,integral_add] at he
  · rw [integral_indicator_const _ hE,integral_indicator_const _ hF,smul_eq_mul,smul_eq_mul,mul_one,mul_one] at he
    refine ⟨a,c,H,F,hH,hac,hsep,hF,?_,?_,?_,?_⟩
    · have h1 := hbound (v x).column (v x).height
      have h2 := hbound (v y).column (v y).height
      have h3 := hbound a H
      change (∫ w, |(T.sets.activity w).indicator (v x).column (v x).height-(S.sets.activity w).indicator (v x).column (v x).height| ∂μ)≤B at h1
      change (∫ w, |(T.sets.activity w).indicator (v y).column (v y).height-(S.sets.activity w).indicator (v y).column (v y).height| ∂μ)≤B at h2
      change (∫ w, |(T.sets.activity w).indicator a H-(S.sets.activity w).indicator a H| ∂μ)≤B at h3
      linarith
    · exact fun _ h => h.1.1.2
    · exact fun _ h => h.1.2
    · exact fun _ h => h.2
  all_goals first | exact hJ | exact (hmove _ _).abs | exact hJ.add (hmove _ _).abs | exact (hJ.add (hmove _ _).abs).add (hmove _ _).abs
end PairGeometry
end PlanarL1.Columns.Model

end



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

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
namespace SetSystem
lemma lift_movement (S T : SetSystem M Ω μ) (i : Fin (k+1)) (H : ℝ) :
    S.lift.movement T.lift i H=S.movement T i H := by
  let hp := measurePreserving_fst (μ := μ) (ν := Threshold.fair)
  change (∫ z : Ω × Bool, |(T.activity z.1).indicator i H-(S.activity z.1).indicator i H| ∂μ.prod Threshold.fair)=_
  have he := integral_map_of_stronglyMeasurable (μ := μ.prod Threshold.fair) hp.measurable
    (((T.measurable_indicator i H).sub (S.measurable_indicator i H)).abs.stronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm
end SetSystem

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} (S : BState M κ lam Ω μ) (A : Ambient M)
lemma increment_integrable {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) (i : Fin (k+1)) (H : ℝ) : Integrable
      (fun w => ((S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).sets.activity w).indicator i H-
        (S.sets.activity w).indicator i H) μ := by
  change Integrable (fun w => (S.fieldActivity (S.incrementFields A hist sign hc hcr hr hcross hlam)
    hk hsmall hlam (S.increment_boundary A hist sign hc hcr hr hcross hrec hk hlam hboundary) w).indicator i H-
    (S.sets.activity w).indicator i H) μ
  simp_rw [S.field_indicator,S.old_indicator]
  exact (S.labels (S.name i H)).integrable_difference _ _ _ _
end BState

namespace CoupledState
open Parameters SecondaryGeometry VertexBands
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable {t' : ℝ}

lemma Moves.successful {T : CoupledState A (Ω × Bool) (Ξ × Bool) (μ.prod Threshold.fair) (ν.prod Threshold.fair) t'}
    {B : ℝ} (h : S.Moves T B) (hB : 0 ≤ B) {V : Type*} (v : V → M.Point Set.univ A.root)
    {b : ℝ} {x y : V} (hs : S.Successful v b x y) : T.Successful v (b-3*B) x y := by
  by_cases hb : 0<b
  · have hs' := hs.lift S v
    rcases hs' with hs'|hs'|hs'
    · change b  ≤  S.left.lift.sets.separation (v x).column (v x).height (v y).column (v y).height at hs'
      have he := S.left.lift.sets.separation_survival T.left.sets (v x) (v y) h.1
      exact Or.inl (by linarith [h.2.2.1 (v x).column (v x).height,h.2.2.1 (v y).column (v y).height])
    · change b  ≤  S.right.lift.sets.separation (v x).column (v x).height (v y).column (v y).height at hs'
      have he := S.right.lift.sets.separation_survival T.right.sets (v x) (v y) h.2.1
      exact Or.inr (Or.inl (by linarith [h.2.2.2 (v x).column (v x).height,h.2.2.2 (v y).column (v y).height]))
    · exact Or.inr (Or.inr (hs'.survive hb h.1 h.2.2.1))
  · exact Or.inl (le_trans (by linarith) (T.left.sets.separation_nonneg _ _ _ _))

variable (ht : 1 ≤ t) (hgap : 10 ≤ (R/200)*t)
lemma unchanged_moves : S.Moves (S.unchanged ht) 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i H; simp only [unchanged,weaken,lift,sub_self]; exact integrable_zero _ _ _
  · intro i H; simp only [unchanged,weaken,lift,sub_self]; exact integrable_zero _ _ _
  · intro i H; simp only [SetSystem.movement,Activity.movement,unchanged,weaken,lift,sub_self,abs_zero,integral_zero]; norm_num
  · intro i H; simp only [SetSystem.movement,Activity.movement,unchanged,weaken,lift,sub_self,abs_zero,integral_zero]; norm_num

variable [SFinite μ] [SFinite ν]
variable {V : Type*} [Fintype V] (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
omit [SFinite ν] [Fintype V] in
lemma main_moves (omega : MainFamily.Sample phaseD m) : S.Moves (S.main ht phaseD hm omega) 1 := by
  refine ⟨(MainFamily.batch A S.left phaseD hm omega).movement_integrable,?_,?_,?_⟩
  · intro i H; simp only [main,sub_self]; exact integrable_zero _ _ _
  · intro i H
    exact ((MainFamily.batch A S.left phaseD hm omega).movement_bound verticalA.1 i H).trans (by norm_num [kappaA,a₁])
  · intro i H; simp only [SetSystem.movement,Activity.movement,main,sub_self,abs_zero,integral_zero]; norm_num
omit [SFinite μ] in
lemma secondary_moves (omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m) :
    S.Moves (S.secondary ht v hv phaseD hm p phaseG omega) 1 := by
  refine ⟨?_,(SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega).movement_integrable,?_,?_⟩
  · intro i H; simp only [secondary,sub_self]; exact integrable_zero _ _ _
  · intro i H; simp only [SetSystem.movement,Activity.movement,secondary,sub_self,abs_zero,integral_zero]; norm_num
  · intro i H
    exact ((SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega).movement_bound verticalB.1 i H).trans (by norm_num [kappaB,a₂])
omit [SFinite μ] [SFinite ν] [Fintype V] in
lemma increment_moves (sign : Fin (S.right.count+1) → Bool) : S.Moves (S.increment ht hgap sign) 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i H; simp only [increment,sub_self]; exact integrable_zero _ _ _
  · intro i H
    have hi := S.right.increment_integrable (r := 1) A _ sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
      (by simpa using S.cross hgap) S.histories.recorded verticalB.1 (by norm_num [kappaB,a₂]) Group.lam_bound
      (by change kappaB*lambda*10 ≤ 1/8; norm_num [kappaB,a₂,lambda,R]) i H
    exact (measurePreserving_fst (μ := ν) (ν := Threshold.fair)).integrable_comp_of_integrable hi
  · intro i H; simp only [SetSystem.movement,Activity.movement,increment,sub_self,abs_zero,integral_zero]; norm_num
  · intro i H
    change S.right.sets.lift.movement (IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).sets.lift i H ≤ 1
    rw [SetSystem.lift_movement]
    exact (S.right.increment_movement A _ sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
      (by simpa using S.cross hgap) S.histories.recorded verticalB.1 (by norm_num [kappaB,a₂]) Group.lam_bound
      (by change kappaB*lambda*10 ≤ 1/8; norm_num [kappaB,a₂,lambda,R]) i H).trans
      (by change kappaB*lambda*10*1 ≤ 1; norm_num [kappaB,a₂,lambda,R])
lemma modes_moves : (S.modes ht hgap v hv phaseD hm p phaseG).Holds (fun T => S.Moves T 1) := by
  intro i
  fin_cases i
  · exact S.unchanged_moves ht
  · apply Execution.holds_bind_of_forall
    intro omega
    exact S.main_moves ht phaseD hm omega
  · apply Execution.holds_bind_of_forall
    intro omega
    exact S.secondary_moves ht v hv phaseD hm p phaseG omega
  · apply Execution.holds_bind_of_forall
    intro sign
    exact S.increment_moves ht hgap sign
lemma step_moves : (S.step ht hgap v hv hm).Holds (fun T => S.Moves T 1) := by
  apply Execution.holds_bind_of_forall
  intro c
  exact S.modes_moves ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2)
end CoupledState
end PlanarL1.Columns.Model

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
lemma successGain_pos : 0 < successGain := by
  unfold successGain
  refine lt_min Columns.Model.VertexTests.cutoffGain_pos ?_
  norm_num [kappaA,a₁,j,EA,epsilon,kappaB,a₂,R,lambda]
lemma successChance_pos : 0 < successChance := div_pos secondaryChance_pos (by norm_num)
end PlanarL1.Parameters

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
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M}
namespace SetSystem
variable [Fintype V] (S : SetSystem M Ω μ) (v : V → M.Point Set.univ A.root)
variable [SFinite μ]
attribute [local instance] OAI.PlanarL1.Columns.Model.SetSystem.instMeasurableSpaceSetFinHAddNatOfNat
lemma cuts_distance (x y : V) :
    (S.cuts v).distance x y=∫ w, (S.activity w).cost (v x).column (v y).column (v x).height (v y).height ∂μ := by
  rw [cuts,FiniteL1.CutFamily.distance_ofBinary]
  rw [← S.integral_norm_coordinates (Classical.choice ((v x).paths_nonempty (v y))) (v x).height (v y).height]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  by_cases hx : (S.activity w.1).active (v x).column (v x).height ∧ w.2=(S.activity w.1).component (v x).column <;>
    by_cases hy : (S.activity w.1).active (v y).column (v y).height ∧ w.2=(S.activity w.1).component (v y).column <;>
    simp [Real.norm_eq_abs,SetSystem.coordinateDifference,Activity.vector,FiniteL1.BinarySystem.indicator,refinedBinary,hx,hy]
lemma cuts_upper (x y : V) : (S.cuts v).distance x y ≤ dist (v x) (v y) := by
  rw [S.cuts_distance]
  exact S.integral_cost_le_dist isClosed_univ _ _
lemma cuts_dominates (x y : V) : S.separation (v x).column (v x).height (v y).column (v y).height ≤ (S.cuts v).distance x y := by
  rw [S.cuts_distance,← S.norm_refinedMap_sub (v x)]
  exact S.refinedMap_dominates _ _ _
end SetSystem
namespace PairGeometry
variable [SFinite μ] [Fintype V] {SA : OrdinaryState M kappaA Ω μ}
variable {v : V → M.Point Set.univ A.root} {x y : V} {b : ℝ}
lemma Certificate.cuts (h : Certificate A SA v (x := x) (y := y) b) :
    b ≤ (SA.sets.cuts v).distance x y := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  rw [SA.sets.cuts_distance,← SA.sets.norm_refinedMap_sub (v x)]
  have bound {a c : Fin (k+1)} (hH : H ∈ M.heights a c) (hac : ¬Consecutive a c)
      (hsep : Field.TipSeparates a c (v x).column (v y).column)
      (hn : ∀ w ∈ E, ¬(SA.sets.activity w).active a H) :
      2*μ.real E ≤ ‖SA.sets.refinedMap (v x) (v x)-SA.sets.refinedMap (v x) (v y)‖ := by
    rcases hsep with ⟨h1,h2,hout⟩|⟨h1,h2,hout⟩
    · exact (SA.sets.refinedMap_terminal_certificate (v x) (v x) (v y) hH hac ⟨h1,h2⟩ hout E hE hn hx hy).2
    · simpa only [norm_sub_rev] using (SA.sets.refinedMap_terminal_certificate (v x) (v y) (v x) hH hac ⟨h1,h2⟩ hout E hE hn hy hx).2
  have hh : 2*μ.real E ≤ ‖SA.sets.refinedMap (v x) (v x)-SA.sets.refinedMap (v x) (v y)‖ := by
    rcases hsep with hsep|hsep
    · exact bound hH hac hsep hn
    · apply bound (M.symm a c ▸ hH) (fun h => hac (by simpa only [Consecutive,or_comm,or_left_comm,or_assoc] using h)) hsep
      intro w hw hwa
      exact hn w hw ((SA.sets.activity w).switch a c H hH |>.mpr hwa)
  linarith [measureReal_nonneg (μ := μ) (s := E)]
end PairGeometry
namespace CoupledState
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {t : ℝ} (S : CoupledState A Ω Ξ μ ν t) (v : V → M.Point Set.univ A.root)
lemma cuts_upper (x y : V) : (S.cuts v).distance x y ≤ 2*dist (v x) (v y) := by
  rw [CoupledState.cuts,FiniteL1.CutFamily.distance_add]
  linarith [S.left.sets.cuts_upper v x y,S.right.sets.cuts_upper v x y]
lemma Successful.cuts {x y : V} {b : ℝ} (h : S.Successful v b x y) : b ≤ (S.cuts v).distance x y := by
  rw [CoupledState.cuts,FiniteL1.CutFamily.distance_add]
  rcases h with h|h|h
  · exact (h.trans (S.left.sets.cuts_dominates v x y)).trans (le_add_of_nonneg_right (FiniteL1.CutFamily.distance_nonneg _ _ _))
  · exact (h.trans (S.right.sets.cuts_dominates v x y)).trans (le_add_of_nonneg_left (FiniteL1.CutFamily.distance_nonneg _ _ _))
  · exact h.cuts.trans (le_add_of_nonneg_right (FiniteL1.CutFamily.distance_nonneg _ _ _))
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters

namespace World
attribute [instance] measurable sfinite
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (hQ : 0 < Q) (h1 : 1 ≤ Q) (hgap : 10 ≤ (R/200)*Q)
variable (W : World k V Q)
lemma cuts_upper (x y : V) : W.cuts.distance x y ≤ 2*W.distance x y := W.state.cuts_upper W.vertex x y
lemma Successful.cuts {b : ℝ} {x y : V} (h : W.Successful b x y) : b ≤ W.cuts.distance x y := CoupledState.Successful.cuts W.state W.vertex h

omit [Fintype V] in
lemma after_distance (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) (x y : V) :
    (W.after hQ T).distance x y=Q*W.distance x y := W.ambient.scaleEquiv_dist hQ _ _
omit [Fintype V] in
lemma after_successful (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure))
    {x y : V} {b : ℝ} (h : T.Successful W.vertex b x y) : (W.after hQ T).Successful (Q*b) x y := h.dilate hQ T W.vertex

lemma step_distances {m : ℕ} (hm : 0 < m) : (W.step hQ h1 hgap hm).Holds
    (fun Z => ∀ x y, Z.distance x y=Q*W.distance x y) := by
  apply Execution.holds_bind_of_forall
  intro T x y
  exact W.after_distance hQ T x y

lemma step_survives {m : ℕ} (hm : 0 < m) {x y : V} {b : ℝ} (h : W.Successful b x y) :
    (W.step hQ h1 hgap hm).Holds (fun Z => Z.Successful (Q*(b-3)) x y) := by
  apply (W.state.step_moves h1 hgap W.vertex W.height_bounds hm).bind
  intro T hT
  exact W.after_successful hQ T (by simpa only [mul_one] using hT.successful W.state (by norm_num) W.vertex h)

omit [Fintype V] in
lemma initial_coherent {M : Model (k+1)} (A : Ambient M) (v : V → M.Point Set.univ A.root) (x : V) (ρ : ℝ) :
    (initial (Q := Q) A v).Coherent x ρ := by
  intro z hz
  exact ⟨rfl,rfl⟩
end World
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_DiskCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! ## Planar disk crossing by covering-angle lifting. -/

namespace PlanarL1.Topology
open Complex Real

/-- The planar rectangle crossing obstruction, proved by lifting angles rather
than assuming a Jordan separation theorem. -/
lemma rectangle_zero (F : C(unitInterval × unitInterval, ℂ))
    (hleft : ∀ t, (F (0,t)).re < 0)
    (hright : ∀ t, 0 < (F (1,t)).re)
    (hbottom : ∀ s, 0 < (F (s,0)).im)
    (htop : ∀ s, (F (s,1)).im < 0) :
    ∃ p, F p=0 := by
  by_contra! hn
  let cov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2*π)
  let H : C(unitInterval × unitInterval, Real.Angle) :=
    ⟨fun p => (Complex.arg (F p) : Real.Angle), by
      apply continuous_iff_continuousAt.mpr
      intro p
      exact (Complex.continuousAt_arg_coe_angle (hn p)).comp F.continuous.continuousAt⟩
  have left_cont : Continuous (fun t : unitInterval => Complex.arg (-F (0,t))+π) := by
    apply Continuous.add_const
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Complex.continuousAt_arg (by
      left
      simpa using neg_pos.mpr (hleft t))).comp
      ((F.continuous.comp (continuous_const.prodMk continuous_id)).neg.continuousAt)
  let L : C(unitInterval, ℝ) := ⟨fun t => Complex.arg (-F (0,t))+π,left_cont⟩
  have hL (t : unitInterval) : H (0,t) = (L t : Real.Angle) := by
    dsimp [H,L]
    rw [Complex.arg_neg_coe_angle (hn _)]
    simp only [add_assoc,Real.Angle.coe_pi_add_coe_pi,add_zero]
  let θ := cov.liftHomotopy H L hL
  have θ_left : ∀ t, θ (0,t)=L t := cov.liftHomotopy_zero H L hL
  have θ_lifts (p : unitInterval × unitInterval) : (θ p : Real.Angle)=H p :=
    congr_fun (cov.liftHomotopy_lifts H L hL) p
  have arg_cont (f : C(unitInterval, ℂ)) (hf : ∀ t, f t ∈ Complex.slitPlane) :
      Continuous (fun t => Complex.arg (f t)) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      (Complex.continuousAt_arg (hf t)).comp f.continuous.continuousAt
  have bottom_cont : Continuous (fun s : unitInterval => Complex.arg (F (s,0))) := by
    apply arg_cont ⟨fun s => F (s,0),F.continuous.comp (continuous_id.prodMk continuous_const)⟩
    intro s
    exact Or.inr (ne_of_gt (hbottom s))
  have top_cont : Continuous (fun s : unitInterval => Complex.arg (F (s,1))) := by
    apply arg_cont ⟨fun s => F (s,1),F.continuous.comp (continuous_id.prodMk continuous_const)⟩
    intro s
    exact Or.inr (ne_of_lt (htop s))
  have right_cont : Continuous (fun t : unitInterval => Complex.arg (F (1,t))) := by
    apply arg_cont ⟨fun t => F (1,t),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    intro t
    exact Or.inl (hright t)
  have hbottom_eq : (fun s : unitInterval => θ (s,0)) = fun s => Complex.arg (F (s,0)) := by
    refine cov.eq_of_comp_eq
      (θ.continuous.comp (continuous_id.prodMk continuous_const)) bottom_cont ?_ 0 ?_
    · exact funext fun s => θ_lifts (s,0)
    · rw [θ_left]
      dsimp [L]
      rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos (hbottom 0)]
      ring
  have hright_eq : (fun t : unitInterval => θ (1,t)) = fun t => Complex.arg (F (1,t)) := by
    refine cov.eq_of_comp_eq
      (θ.continuous.comp (continuous_const.prodMk continuous_id)) right_cont ?_ 0 ?_
    · exact funext fun t => θ_lifts (1,t)
    · exact congr_fun hbottom_eq 1
  have htop_eq : (fun s : unitInterval => θ (s,1)) =
      fun s => Complex.arg (F (s,1))+2*π := by
    refine cov.eq_of_comp_eq
      (θ.continuous.comp (continuous_id.prodMk continuous_const)) (top_cont.add_const _) ?_ 0 ?_
    · funext s
      change (θ (s,1) : Real.Angle) = ((Complex.arg (F (s,1))+2*π : ℝ) : Real.Angle)
      rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
      exact θ_lifts (s,1)
    · rw [θ_left]
      dsimp [L]
      rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (htop 0)]
      ring
  have hb := congr_fun htop_eq 1
  have hr := congr_fun hright_eq 1
  have := Real.pi_pos
  linarith

lemma disk_re_lt_one {z : ℂ} (h : ‖z‖ ≤ 1) (hne : z ≠ 1) : z.re < 1 := by
  have hre := Complex.re_le_norm z
  have hs := Complex.sq_norm_sub_sq_re z
  have hn := norm_nonneg z
  by_contra! hc
  have he : z.re=1 := by linarith
  have hi : z.im=0 := by nlinarith [sq_nonneg z.im]
  exact hne (Complex.ext (by simpa using he) (by simpa using hi))

lemma disk_im_lt_one {z : ℂ} (h : ‖z‖ ≤ 1) (hne : z ≠ Complex.I) : z.im < 1 := by
  have him := Complex.im_le_norm z
  have hs := Complex.sq_norm_sub_sq_im z
  have hn := norm_nonneg z
  by_contra! hc
  have he : z.im=1 := by linarith
  have hr : z.re=0 := by nlinarith [sq_nonneg z.re]
  exact hne (Complex.ext (by simpa using hr) (by simpa using he))

/-- Opposite endpoints in a disk force two continuous arcs to meet. This is
one normal form of nonalternation. -/
lemma disk_opposite_arcs_meet (f g : C(unitInterval, ℂ))
    (hf : ∀ s, ‖f s‖ ≤ 1) (hg : ∀ t, ‖g t‖ ≤ 1)
    (hf0 : f 0 = -1) (hf1 : f 1 = 1)
    (hg0 : g 0 = -Complex.I) (hg1 : g 1 = Complex.I) :
    ∃ s t, f s=g t := by
  by_contra! hn
  let F : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => f p.1-g p.2,(f.continuous.comp continuous_fst).sub
      (g.continuous.comp continuous_snd)⟩
  have hleft (t : unitInterval) : (F (0,t)).re < 0 := by
    have hne : -g t ≠ (1 : ℂ) := by
      intro he
      apply hn 0 t
      rw [hf0]
      exact (neg_eq_iff_eq_neg.mp he).symm
    have hh := disk_re_lt_one (z := -g t) (by simpa using hg t) hne
    dsimp [F]
    simp only [Complex.neg_re] at hh
    simp only [hf0,Complex.neg_re,Complex.one_re]
    linarith
  have hright (t : unitInterval) : 0 < (F (1,t)).re := by
    have hh := disk_re_lt_one (hg t) (by
      intro he
      exact hn 1 t (hf1.trans he.symm))
    dsimp [F]
    simp only [hf1,Complex.one_re]
    linarith
  have hbottom (s : unitInterval) : 0 < (F (s,0)).im := by
    have hne : -f s ≠ Complex.I := by
      intro he
      exact hn s 0 ((neg_eq_iff_eq_neg.mp he).trans hg0.symm)
    have hh := disk_im_lt_one (z := -f s) (by simpa using hf s) hne
    dsimp [F]
    simp only [hg0,Complex.neg_im,Complex.I_im] at *
    linarith
  have htop (s : unitInterval) : (F (s,1)).im < 0 := by
    have hh := disk_im_lt_one (hf s) (by
      intro he
      exact hn s 1 (he.trans hg1.symm))
    dsimp [F]
    simp only [hg1,Complex.I_im]
    linarith
  obtain ⟨⟨s,t⟩,h⟩ := rectangle_zero F hleft hright hbottom htop
  exact hn s t (sub_eq_zero.mp h)

end PlanarL1.Topology



end

section

/-! ## General cyclic-endpoint disk separation -/

namespace PlanarL1.Topology
open Complex Real Set

/- An explicit annular extension reduces arbitrary cyclic boundary endpoints
  to the already-proved cardinal-endpoint disk crossing obstruction. -/

lemma norm_annularConnector (a b : ℝ) (t : unitInterval) :
    ‖annularConnector a b t‖ = 1 + (t : ℝ) := by
  change ‖((1 + (t : ℝ) : ℝ) : ℂ) *
    (Circle.exp ((1 - (t : ℝ)) * a + (t : ℝ) * b) : ℂ)‖ = _
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith [t.2.1])]

lemma annularConnector_disjoint {a a' b b' : ℝ}
    (ha : a < a') (ha' : a' - a < 2 * π)
    (hb : b < b') (hb' : b' - b < 2 * π) :
    Disjoint (range (annularConnector a b)) (range (annularConnector a' b')) := by
  rw [Set.disjoint_left]
  rintro z ⟨s, hs⟩ ⟨t, ht⟩
  have he : annularConnector a b s = annularConnector a' b' t := hs.trans ht.symm
  have hn := congrArg norm he
  rw [norm_annularConnector, norm_annularConnector] at hn
  have hst : s = t := Subtype.ext (by linarith)
  subst t
  have hs0 := s.2.1
  have hs1 := s.2.2
  let u := (1 - (s : ℝ)) * a + (s : ℝ) * b
  let v := (1 - (s : ℝ)) * a' + (s : ℝ) * b'
  have huv : u < v := by
    dsimp [u,v]
    by_cases hz : (s : ℝ) = 0
    · simpa [hz] using ha
    · have hp : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hz)
      exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr hs1))
        (mul_lt_mul_of_pos_left hb hp)
  have hspan : v - u < 2 * π := by
    dsimp [u,v]
    by_cases hz : (s : ℝ) = 0
    · simpa [hz] using ha'
    · have hp : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hz)
      have h₁ := mul_le_mul_of_nonneg_left ha'.le (sub_nonneg.mpr hs1)
      have h₂ := mul_lt_mul_of_pos_left hb' hp
      nlinarith
  have hrad : ((1 + (s : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < 1 + (s : ℝ)))
  have he' : Circle.exp u = Circle.exp v := by
    apply Subtype.ext
    exact mul_left_cancel₀ hrad he
  have heq := Circle.exp_injOn_Icc hspan
    (show u ∈ Icc u v from ⟨le_rfl,huv.le⟩)
    (show v ∈ Icc u v from ⟨huv.le,le_rfl⟩) he'
  exact (ne_of_lt huv) heq

/-- An annular connector meets the closed unit disk only at its source. -/
lemma annularConnector_disk {a b : ℝ} {z : ℂ}
    (hz : z ∈ range (annularConnector a b)) (hn : ‖z‖ ≤ 1) :
    z = (Circle.exp a : ℂ) := by
  rcases hz with ⟨t,rfl⟩
  rw [norm_annularConnector] at hn
  have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith [t.2.1])
  subst t
  exact (annularConnector a b).source

lemma annularConnector_disjoint_disk {a b : ℝ} {S : Set ℂ}
    (hS : ∀ z ∈ S, ‖z‖ ≤ 1) (ha : (Circle.exp a : ℂ) ∉ S) :
    Disjoint (range (annularConnector a b)) S := by
  rw [Set.disjoint_left]
  intro z hz hzS
  exact ha ((annularConnector_disk hz (hS z hzS)) ▸ hzS)

lemma annular_extension_bound {a c : ℝ}
    (p : Path (Circle.exp a : ℂ) (Circle.exp c : ℂ))
    (hp : ∀ t, ‖p t‖ ≤ 1) (b d : ℝ) :
    ∀ t, ‖((annularConnector a b).symm.trans
      (p.trans (annularConnector c d))) t‖ ≤ 2 := by
  intro t
  have hm := Set.mem_range_self
    (f := ((annularConnector a b).symm.trans (p.trans (annularConnector c d)))) t
  rw [Path.trans_range, Path.symm_range, Path.trans_range] at hm
  rcases hm with hm | hm | hm
  · rcases hm with ⟨s,hs⟩
    rw [← hs, norm_annularConnector]
    linarith [s.2.2]
  · rcases hm with ⟨s,hs⟩
    rw [← hs]
    exact (hp s).trans (by norm_num)
  · rcases hm with ⟨s,hs⟩
    rw [← hs, norm_annularConnector]
    linarith [s.2.2]

/-- Arbitrary four boundary endpoints in strict cyclic order, with no
  injectivity requirement on either of the two disk paths. -/
lemma disk_cyclic_arcs_meet (a₀ a₁ a₂ a₃ : ℝ)
    (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃)
    (hspan : a₃ < a₀ + 2 * π)
    (f : Path (Circle.exp a₀ : ℂ) (Circle.exp a₂ : ℂ))
    (g : Path (Circle.exp a₁ : ℂ) (Circle.exp a₃ : ℂ))
    (hf : ∀ s, ‖f s‖ ≤ 1) (hg : ∀ s, ‖g s‖ ≤ 1) :
    ∃ s t, f s = g t := by
  by_contra! hn
  have hfg : Disjoint (range f) (range g) := by
    rw [Set.disjoint_left]
    rintro z ⟨s,rfl⟩ ⟨t,ht⟩
    exact hn s t ht.symm
  let q₀ := annularConnector a₀ (-π)
  let q₁ := annularConnector a₁ (-π/2)
  let q₂ := annularConnector a₂ 0
  let q₃ := annularConnector a₃ (π/2)
  have hq₀₁ : Disjoint (range q₀) (range q₁) := by
    apply annularConnector_disjoint h₀₁ <;> linarith [Real.pi_pos]
  have hq₀₃ : Disjoint (range q₀) (range q₃) := by
    apply annularConnector_disjoint <;> linarith [Real.pi_pos]
  have hq₂₁ : Disjoint (range q₂) (range q₁) := by
    apply Disjoint.symm
    apply annularConnector_disjoint h₁₂ <;> linarith [Real.pi_pos]
  have hq₂₃ : Disjoint (range q₂) (range q₃) := by
    apply annularConnector_disjoint h₂₃ <;> linarith [Real.pi_pos]
  have hfg₀ : (Circle.exp a₀ : ℂ) ∉ range g := by
    exact fun hm => Set.disjoint_left.mp hfg f.source_mem_range hm
  have hfg₂ : (Circle.exp a₂ : ℂ) ∉ range g := by
    exact fun hm => Set.disjoint_left.mp hfg f.target_mem_range hm
  have hgf₁ : (Circle.exp a₁ : ℂ) ∉ range f := by
    exact fun hm => Set.disjoint_left.mp hfg hm g.source_mem_range
  have hgf₃ : (Circle.exp a₃ : ℂ) ∉ range f := by
    exact fun hm => Set.disjoint_left.mp hfg hm g.target_mem_range
  have hf' : ∀ z ∈ range f, ‖z‖ ≤ 1 := by rintro z ⟨s,rfl⟩; exact hf s
  have hg' : ∀ z ∈ range g, ‖z‖ ≤ 1 := by rintro z ⟨s,rfl⟩; exact hg s
  have hq₀g := annularConnector_disjoint_disk (b := -π) hg' hfg₀
  have hq₂g := annularConnector_disjoint_disk (b := 0) hg' hfg₂
  have hfq₁ := (annularConnector_disjoint_disk (b := -π/2) hf' hgf₁).symm
  have hfq₃ := (annularConnector_disjoint_disk (b := π/2) hf' hgf₃).symm
  let F := q₀.symm.trans (f.trans q₂)
  let G := q₁.symm.trans (g.trans q₃)
  have hFG : Disjoint (range F) (range G) := by
    simp only [F,G,Path.trans_range,Path.symm_range,
      Set.disjoint_union_left,Set.disjoint_union_right]
    exact ⟨⟨hq₀₁,hfq₁,hq₂₁⟩,⟨hq₀g,hfg,hq₂g⟩,hq₀₃,hfq₃,hq₂₃⟩
  let F' : C(unitInterval, ℂ) := ⟨fun s => F s / 2,by fun_prop⟩
  let G' : C(unitInterval, ℂ) := ⟨fun t => G t / 2,by fun_prop⟩
  have hF : ∀ s, ‖F' s‖ ≤ 1 := by
    intro s
    change ‖F s / 2‖ ≤ 1
    rw [norm_div, Complex.norm_ofNat]
    exact (div_le_one (by norm_num)).mpr (annular_extension_bound f hf (-π) 0 s)
  have hG : ∀ s, ‖G' s‖ ≤ 1 := by
    intro s
    change ‖G s / 2‖ ≤ 1
    rw [norm_div, Complex.norm_ofNat]
    exact (div_le_one (by norm_num)).mpr
      (annular_extension_bound g hg (-π/2) (π/2) s)
  have hF₀ : F' 0 = -1 := by
    change F 0 / 2 = -1
    rw [F.source]
    simp [Circle.coe_exp]
  have hF₁ : F' 1 = 1 := by
    change F 1 / 2 = 1
    rw [F.target]
    simp
  have hG₀ : G' 0 = -Complex.I := by
    change G 0 / 2 = -Complex.I
    rw [G.source]
    simp only [Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.exp_neg_pi_div_two_mul_I]
    ring
  have hG₁ : G' 1 = Complex.I := by
    change G 1 / 2 = Complex.I
    rw [G.target]
    simp [Circle.coe_exp, Complex.exp_pi_div_two_mul_I]
  obtain ⟨s,t,hst⟩ := disk_opposite_arcs_meet F' G' hF hG hF₀ hF₁ hG₀ hG₁
  have he : F s = G t := (div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp hst
  exact Set.disjoint_left.mp hFG (Set.mem_range_self s) (he ▸ Set.mem_range_self t)

end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Drawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Topology
open Set Metric

lemma drawing_of_planar {V : Type} {G : SimpleGraph V} (h : IsPlanar G) :
    Nonempty (Drawing G) := by
  obtain ⟨p,a,hp,ha,hi,hv,hd⟩ := h
  let e := Complex.equivRealProdCLM.symm
  refine ⟨⟨fun v => e (p v),e.injective.comp hp,
    fun u v h => ⟨⟨fun t => e (a u v h t),e.continuous.comp (a u v h).continuous⟩,
      congrArg e (ha u v h).1,congrArg e (ha u v h).2⟩,?_,?_,?_⟩⟩
  · intro u v h
    exact e.injective.comp (hi u v h)
  · intro u v h t w ht ht' he
    exact hv u v h t w ht ht' (e.injective he)
  · intro u v h x y k s t hs hs' ht ht' he
    exact hd u v h x y k s t hs hs' ht ht' (e.injective he)

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

lemma point_on_edge_iff (u v : V) (h : G.Adj u v) (w : V) (t : unitInterval) :
    D.edge u v h t=D.point w ↔ (t=0 ∧ w=u) ∨ (t=1 ∧ w=v) := by
  constructor
  · intro he
    by_cases h0 : t=0
    · left
      refine ⟨h0,?_⟩
      rw [h0,Path.source] at he
      exact (D.point_injective he).symm
    by_cases h1 : t=1
    · right
      refine ⟨h1,?_⟩
      rw [h1,Path.target] at he
      exact (D.point_injective he).symm
    exact False.elim (D.interior_avoid u v h t w
      (lt_of_le_of_ne t.2.1 (by intro he; exact h0 (Subtype.ext he.symm)))
      (lt_of_le_of_ne t.2.2 (by intro he; exact h1 (Subtype.ext he))) he)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp

lemma excludedTimes_closed (w : V) (d : G.Dart) : IsClosed (excludedTimes w d) := by
  have hu : IsClosed {t : unitInterval | w≠d.fst} := by
    by_cases h : w≠d.fst <;> simp [h]
  have hv : IsClosed {t : unitInterval | w≠d.snd} := by
    by_cases h : w≠d.snd <;> simp [h]
  exact (hu.union (isClosed_le continuous_const continuous_subtype_val)).inter
    (hv.union (isClosed_le continuous_subtype_val continuous_const))

lemma excludedTimes_avoid (w : V) (d : G.Dart) :
    D.point w ∉ D.edge d.fst d.snd d.adj '' excludedTimes w d := by
  rintro ⟨t,ht,he⟩
  rcases (D.point_on_edge_iff _ _ _ _ t).mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases ht.1 with h | h
    · exact h rfl
    · norm_num at h
  · rcases ht.2 with h | h
    · exact h rfl
    · norm_num at h

variable [Fintype V]

lemma forbidden_compact (w : V) : IsCompact (D.forbidden w) := by
  classical
  apply IsCompact.union
  · exact isCompact_iUnion (fun _ => isCompact_singleton)
  · exact isCompact_iUnion (fun d =>
      (excludedTimes_closed w d).isCompact.image (D.edge _ _ _).continuous)

omit [Fintype V] in
lemma forbidden_avoid (w : V) : D.point w ∉ D.forbidden w := by
  rintro (h | h)
  · obtain ⟨⟨v,hv⟩,he⟩ := mem_iUnion.mp h
    exact hv (D.point_injective (mem_singleton_iff.mp he).symm)
  · obtain ⟨d,hd⟩ := mem_iUnion.mp h
    exact D.excludedTimes_avoid w d hd

lemma vertex_disk (w : V) :
    ∃ r>0, ∀ z ∈ D.forbidden w, r<dist (D.point w) z := by
  have hopen := (D.forbidden_compact w).isClosed.isOpen_compl
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hopen (D.point w) (D.forbidden_avoid w)
  refine ⟨r/2,half_pos hr,fun z hz => ?_⟩
  have hnot : ¬dist z (D.point w) < r := fun h => hball h hz
  rw [dist_comm] at hnot
  linarith

/-- One common positive radius works for all vertices; arbitrary edge
oscillations and arbitrary straight-line distances between drawn vertices are
allowed. This radius is topological auxiliary data, not a metric edge scale. -/
lemma uniform_vertex_disks :
    ∃ r>0, ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => exact ⟨1,by norm_num,fun w => isEmptyElim w⟩
  | inr h =>
    choose e he hs using D.vertex_disk
    let R := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty) e
    have hR : 0<R := (Finset.lt_inf'_iff _).mpr (fun w _ => he w)
    refine ⟨R/10,by positivity,fun w z hz => ?_⟩
    have hRw : R≤e w := Finset.inf'_le e (Finset.mem_univ w)
    have hz' := hs w z hz
    linarith

end Drawing

/-- Last exit from a closed disk before a specified later time. This works
for arbitrary continuous paths, including paths which oscillate infinitely
near their endpoint. No local straightness of a topological arc is assumed. -/
lemma path_lastExit {X : Type*} [MetricSpace X] {x y : X} (p : Path x y)
    {b r : ℝ} (hb : 0<b) (hr : 0 < r)
    (hout : r<dist (p.extend b) x) :
    ∃ a : ℝ, 0<a ∧ a<b ∧ dist (p.extend a) x=r ∧
      ∀ t, a<t → t≤b → r<dist (p.extend t) x := by
  let S := Set.Icc 0 b ∩ {t : ℝ | dist (p.extend t) x ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le (p.continuous_extend.dist continuous_const) continuous_const)
  have h0 : (0:ℝ) ∈ S := by simp only [S,mem_inter_iff,mem_Icc,mem_ofPred_eq,
    Path.extend_zero,dist_self]; exact ⟨⟨le_rfl,hb.le⟩,hr.le⟩
  obtain ⟨a,ha,hamax⟩ := hS.exists_isGreatest ⟨0,h0⟩
  have hab : a<b := lt_of_le_of_ne ha.1.2 (by intro he; exact (not_le_of_gt hout) (he ▸ ha.2))
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hab.le
    (p.continuous_extend.dist continuous_const).continuousOn (⟨ha.2,hout.le⟩ :
      r ∈ Set.Icc (dist (p.extend a) x) (dist (p.extend b) x))
  have hta : t≤a := hamax ⟨⟨ha.1.1.trans ht.1,ht.2⟩,he.le⟩
  have har : dist (p.extend a) x=r := (le_antisymm hta ht.1) ▸ he
  have ha0 : 0<a := lt_of_le_of_ne ha.1.1 (by
    intro he
    rw [← he,Path.extend_zero,dist_self] at har
    exact hr.ne' har.symm)
  refine ⟨a,ha0,hab,har,fun t hat htb => ?_⟩
  by_contra! h
  exact (not_le_of_gt hat) (hamax ⟨⟨ha0.le.trans hat.le,htb⟩,h⟩)

lemma path_trimStart {X : Type*} [MetricSpace X] {x y : X} (p : Path x y)
    {b : unitInterval} {r : ℝ} (hb : 0<(b:ℝ)) (hr : 0 < r)
    (hout : ∀ t : unitInterval, b≤t → r<dist (p t) x) :
    ∃ a : unitInterval, 0<(a:ℝ) ∧ a<b ∧ dist (p a) x=r ∧
      ∀ t : unitInterval, a<t → r<dist (p t) x := by
  have hb' : r<dist (p.extend b) x := by
    rw [p.extend_apply b.property]
    exact hout b le_rfl
  obtain ⟨a,ha0,hab,he,ht⟩ := path_lastExit p hb hr hb'
  let a' : unitInterval := ⟨a,ha0.le,hab.le.trans b.2.2⟩
  refine ⟨a',ha0,hab,?_,fun t hat => ?_⟩
  · change dist (p.extend (a':ℝ)) x=r at he
    rw [p.extend_apply a'.property] at he
    exact he
  · by_cases htb : t≤b
    · have ht' := ht t hat htb
      simpa only [p.extend_apply t.property] using ht'
    · exact hout t (le_of_not_ge htb)

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

lemma edge_mem_forbidden (w : V) (d : G.Dart) (t : unitInterval)
    (h : t ∈ excludedTimes w d) :
    D.edge d.fst d.snd d.adj t ∈ D.forbidden w :=
  Or.inr (mem_iUnion.mpr ⟨d,⟨t,h,rfl⟩⟩)

lemma point_mem_forbidden (w v : V) (h : v≠w) : D.point v ∈ D.forbidden w :=
  Or.inl (mem_iUnion.mpr ⟨⟨v,h⟩,rfl⟩)

lemma edgeTrim_nonempty {r : ℝ} (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z) (d : G.Dart) :
    Nonempty (D.EdgeTrim r d) := by
  let p := D.edge d.fst d.snd d.adj
  let b : unitInterval := ⟨1/3,by norm_num,by norm_num⟩
  have hleft : ∀ t : unitInterval, b≤t → r<dist (p t) (D.point d.fst) := by
    intro t ht
    have hfor := D.edge_mem_forbidden d.fst d t
      ⟨Or.inr ht,Or.inl d.fst_ne_snd⟩
    have hh := hsep d.fst (p t) hfor
    rw [dist_comm] at hh
    linarith
  have hright : ∀ t : unitInterval, b≤t → r<dist (p.symm t) (D.point d.snd) := by
    intro t ht
    let t' : unitInterval := ⟨1-(t:ℝ),by linarith [t.2.2],by linarith [t.2.1]⟩
    have he : p.symm t=p t' := rfl
    have hfor := D.edge_mem_forbidden d.snd d t'
      ⟨Or.inl d.snd_ne_fst,Or.inr (by dsimp [t']; change (1/3:ℝ)≤(t:ℝ) at ht; linarith)⟩
    have hh := hsep d.snd (p t') hfor
    rw [dist_comm,← he] at hh
    linarith
  obtain ⟨a,ha0,hab,ha,haafter⟩ := path_trimStart p (by norm_num : 0<(b:ℝ)) hr hleft
  obtain ⟨z,hz0,hzb,hz,hzafter⟩ := path_trimStart p.symm (by norm_num : 0<(b:ℝ)) hr hright
  let last : unitInterval := ⟨1-(z:ℝ),by linarith [z.2.2],by linarith [z.2.1]⟩
  refine ⟨⟨a,last,ha0,hab,?_,?_,ha,?_,haafter,?_⟩⟩
  · change (1/3:ℝ)>(z:ℝ) at hzb
    change (2/3:ℝ)<1-(z:ℝ)
    linarith
  · change 1-(z:ℝ)<1
    linarith
  · exact hz
  · intro t ht
    let t' : unitInterval := ⟨1-(t:ℝ),by linarith [t.2.2],by linarith [t.2.1]⟩
    have ht' : z<t' := by
      change (t:ℝ)<1-(z:ℝ) at ht
      change (z:ℝ)<1-(t:ℝ)
      linarith
    have he : p.symm t'=p t := by
      change p ⟨1-(1-(t:ℝ)),_⟩=p t
      congr 1
      apply Subtype.ext
      dsimp
      ring
    simpa only [he] using hzafter t' ht'

namespace EdgeTrim
variable {D} {r : ℝ} {d : G.Dart} (T : D.EdgeTrim r d)

lemma first_lt_last : T.first<T.last := by
  have h := T.first_lt
  have h' := T.last_gt
  change (T.first:ℝ)<(T.last:ℝ)
  linarith

lemma middle_outside (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (w : V) (t : unitInterval) (hft : T.first≤t) (htl : t≤T.last) :
    r≤dist (D.edge d.fst d.snd d.adj t) (D.point w) := by
  by_cases hw : w=d.fst
  · subst w
    rcases eq_or_lt_of_le hft with h | h
    · rw [← h,T.first_sphere]
    · exact (T.after_first t h).le
  by_cases hw' : w=d.snd
  · subst w
    rcases eq_or_lt_of_le htl with h | h
    · rw [h,T.last_sphere]
    · exact (T.before_last t h).le
  have hh := hsep w _ (D.edge_mem_forbidden w d t ⟨Or.inl hw,Or.inl hw'⟩)
  rw [dist_comm] at hh
  linarith

end EdgeTrim
end Drawing

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma polygonallyJoined_of_path {S : Set E} (hS : IsOpen S) {x y : E}
    (p : Path x y) (hp : Set.range p ⊆ S) : PolygonallyJoined S x y := by
  classical
  let A := {z | z ∈ S ∧ PolygonallyJoined S x z}
  let B := S \ A
  have hA : IsOpen A := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hS z hz.1
    refine ⟨r,hr,fun w hw => ⟨hball hw,?_⟩⟩
    exact hz.2.tail ((convex_ball z r).segment_subset (by simpa using hr) hw |>.trans hball)
  have hB : IsOpen B := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hS z hz.1
    refine ⟨r,hr,fun w hw => ⟨hball hw,fun hwA => hz.2 ⟨hz.1,?_⟩⟩⟩
    exact hwA.2.tail ((convex_ball z r).segment_subset hw (by simpa using hr) |>.trans hball)
  have hd : Disjoint A B := Set.disjoint_left.mpr (fun z ha hb => hb.2 ha)
  have hu : Set.range p ⊆ A ∪ B := by
    intro z hz
    by_cases ha : z ∈ A
    · exact Or.inl ha
    · exact Or.inr ⟨hp hz,ha⟩
  have hne : (Set.range p ∩ A).Nonempty :=
    ⟨x,⟨0,p.source⟩,hp ⟨0,p.source⟩,Relation.ReflTransGen.refl⟩
  have hall := IsPreconnected.subset_left_of_subset_union hA hB hd hu hne
    (isPreconnected_range p.continuous)
  exact (hall ⟨1,p.target⟩).2

/-- Disjoint compact arcs can be simultaneously thickened, while avoiding
separate closed obstacles. No finiteness or regularity of the arcs themselves
beyond compactness is used. -/
lemma finite_disjoint_open_neighborhoods {ι X : Type*} [Fintype ι] [MetricSpace X]
    (K F : ι → Set X) (hK : ∀ i, IsCompact (K i)) (hF : ∀ i, IsClosed (F i))
    (hKF : ∀ i, Disjoint (K i) (F i)) (hKK : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧ Disjoint (U i) (F i)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  let O (i : ι) := F i ∪ ⋃ j : {j : ι // j≠i}, K j.val
  have hO (i : ι) : IsClosed (O i) :=
    (hF i).union (isClosed_iUnion_of_finite (fun j => (hK j).isClosed))
  have hKO (i : ι) : Disjoint (K i) (O i) := by
    apply Disjoint.union_right (hKF i)
    refine Set.disjoint_iUnion_right.mpr (fun j => ?_)
    exact hKK j.property.symm
  choose r hr hd using fun i => (hKO i).exists_thickenings (hK i) (hO i)
  refine ⟨fun i => Metric.thickening (r i) (K i),?_,?_⟩
  · intro i
    refine ⟨Metric.isOpen_thickening,Metric.self_subset_thickening (hr i) _,?_⟩
    exact (hd i).mono_right ((show F i ⊆ O i from Set.subset_union_left).trans
      (Metric.self_subset_thickening (hr i) _))
  · intro i j hij
    have hji : K j ⊆ O i := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨j,hij.symm⟩,hx⟩)
    have hij' : K i ⊆ O j := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨i,hij⟩,hx⟩)
    rcases le_total (r j) (r i) with h | h
    · exact (hd i).mono_right ((Metric.thickening_mono h _).trans
        (Metric.thickening_subset_of_subset _ hji))
    · exact ((hd j).mono_right ((Metric.thickening_mono h _).trans
        (Metric.thickening_subset_of_subset _ hij'))).symm

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

/-- On a radial segment, the endpoint is the only point at its maximal
radius. This is valid in every real normed space, without strict convexity. -/
lemma radial_segment_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y z : E} {r : ℝ} (hr : 0 < r) (hy : dist y x=r)
    (hz : z ∈ segment ℝ x y) (hlo : r≤dist z x) : z=y := by
  rw [segment_eq_image' ℝ x y] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he : dist (x+t•(y-x)) x=t*r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    rw [← dist_eq_norm,hy]
  have ht1 : t=1 := le_antisymm ht.2 ((le_mul_iff_one_le_left hr).mp (by simpa [he] using hlo))
  simp [ht1]

/-- Distinct radial heads on the same sphere intersect only at their center. -/
lemma radial_heads_intersect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y w z : E} {r : ℝ} (hr : 0 < r) (hy : dist y x=r) (hw : dist w x=r)
    (hne : y≠w) (hz : z ∈ segment ℝ x y) (hz' : z ∈ segment ℝ x w) : z=x := by
  rw [segment_eq_image' ℝ x y] at hz
  rw [segment_eq_image' ℝ x w] at hz'
  obtain ⟨t,ht,rfl⟩ := hz
  obtain ⟨s,hs,he⟩ := hz'
  have hn := congrArg (fun q => dist q x) he
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg ht.1,abs_of_nonneg hs.1] at hn
  rw [← dist_eq_norm,← dist_eq_norm,hw,hy] at hn
  have hst : s=t := (mul_right_cancel₀ hr.ne' hn)
  subst s
  by_cases ht0 : t=0
  · simp [ht0]
  · have hvec := add_left_cancel he
    have hew := (smul_right_injective E ht0) hvec
    exact False.elim (hne (sub_left_inj.mp hew).symm)

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

namespace EdgeTrim
variable {D} {r : ℝ} {d : G.Dart} (T : D.EdgeTrim r d)

lemma middle_range : Set.range T.middle=
    D.edge d.fst d.snd d.adj '' Set.Icc T.first T.last :=
  Path.range_subpath_of_le _ _ _ T.first_lt_last.le

lemma middle_compact : IsCompact (Set.range T.middle) :=
  isCompact_range T.middle.continuous

lemma middle_avoid_vertices (w : V) : D.point w ∉ Set.range T.middle := by
  rw [T.middle_range]
  rintro ⟨t,ht,he⟩
  exact D.interior_avoid _ _ _ t w (T.first_pos.trans_le ht.1)
    ((show (t:ℝ)≤T.last from ht.2).trans_lt T.last_lt_one) he

lemma middle_radial_head {e : G.Dart} (U : D.EdgeTrim r e) (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (hne : ¬ ((d.fst=e.fst ∧ d.snd=e.snd) ∨ (d.fst=e.snd ∧ d.snd=e.fst))) :
    Disjoint (Set.range T.middle)
      (segment ℝ (D.point e.fst) (D.edge e.fst e.snd e.adj U.first)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [T.middle_range] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he := radial_segment_boundary hr U.first_sphere hz'
    (T.middle_outside hr hsep e.fst t ht.1 ht.2)
  exact hne (D.interior_disjoint _ _ _ _ _ _ t U.first
    (T.first_pos.trans_le ht.1) ((show (t:ℝ)≤T.last from ht.2).trans_lt T.last_lt_one)
    U.first_pos (by linarith [U.first_lt]) he)

lemma middle_radial_tail {e : G.Dart} (U : D.EdgeTrim r e) (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (hne : ¬ ((d.fst=e.fst ∧ d.snd=e.snd) ∨ (d.fst=e.snd ∧ d.snd=e.fst))) :
    Disjoint (Set.range T.middle)
      (segment ℝ (D.point e.snd) (D.edge e.fst e.snd e.adj U.last)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [T.middle_range] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he := radial_segment_boundary hr U.last_sphere hz'
    (T.middle_outside hr hsep e.snd t ht.1 ht.2)
  exact hne (D.interior_disjoint _ _ _ _ _ _ t U.last
    (T.first_pos.trans_le ht.1) ((show (t:ℝ)≤T.last from ht.2).trans_lt T.last_lt_one)
    (by linarith [U.last_gt]) U.last_lt_one he)
end EdgeTrim

variable [Fintype V] [LinearOrder V] {D} {r : ℝ} (T : ∀ d : ForwardDart G, D.EdgeTrim r d.val)

omit [Fintype V] in
lemma forward_middles_disjoint : Pairwise (fun d e : ForwardDart G =>
    Disjoint (Set.range (T d).middle) (Set.range (T e).middle)) := by
  intro d e hde
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [(T d).middle_range] at hz
  rw [(T e).middle_range] at hz'
  obtain ⟨s,hs,rfl⟩ := hz
  obtain ⟨t,ht,he⟩ := hz'
  exact hde (ForwardDart.eq_of_endpoints d e (D.interior_disjoint _ _ _ _ _ _ s t
    ((T d).first_pos.trans_le hs.1) ((show (s:ℝ)≤(T d).last from hs.2).trans_lt (T d).last_lt_one)
    ((T e).first_pos.trans_le ht.1) ((show (t:ℝ)≤(T e).last from ht.2).trans_lt (T e).last_lt_one) he.symm))

lemma middleObstacle_closed (d : ForwardDart G) : IsClosed (D.middleObstacle T d) := by
  classical
  exact (Set.finite_range D.point).isClosed.union (isClosed_iUnion_of_finite (fun e =>
    (compact_segment_complex _ _).isClosed.union (compact_segment_complex _ _).isClosed))

omit [Fintype V] in
lemma middleObstacle_disjoint (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z) (d : ForwardDart G) :
    Disjoint (Set.range (T d).middle) (D.middleObstacle T d) := by
  apply Disjoint.union_right
  · apply Set.disjoint_left.mpr
    rintro z hz ⟨w,rfl⟩
    exact (T d).middle_avoid_vertices w hz
  · refine Set.disjoint_iUnion_right.mpr (fun e => ?_)
    have hne : ¬ ((d.val.fst=e.val.val.fst ∧ d.val.snd=e.val.val.snd) ∨
        (d.val.fst=e.val.val.snd ∧ d.val.snd=e.val.val.fst)) :=
      fun h => e.property (ForwardDart.eq_of_endpoints d e.val h).symm
    exact Disjoint.union_right ((T d).middle_radial_head (T e.val) hr hsep hne)
      ((T d).middle_radial_tail (T e.val) hr hsep hne)

/-- Every trimmed edge can be replaced by a literal finite segment chain,
inside mutually disjoint open tubes avoiding all other edge heads and all
vertices. This is the needed simultaneous polygonalization step. -/
lemma polygonal_middles (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z) :
    ∃ U : ForwardDart G → Set ℂ,
      (∀ d, IsOpen (U d) ∧ Disjoint (U d) (D.middleObstacle T d) ∧
        PolygonallyJoined (U d)
          (D.edge d.val.fst d.val.snd d.val.adj (T d).first)
          (D.edge d.val.fst d.val.snd d.val.adj (T d).last)) ∧
      Pairwise (fun d e => Disjoint (U d) (U e)) := by
  classical
  obtain ⟨U,hU,hd⟩ := finite_disjoint_open_neighborhoods
    (fun d => Set.range (T d).middle) (D.middleObstacle T)
    (fun d => (T d).middle_compact) (D.middleObstacle_closed T)
    (D.middleObstacle_disjoint T hr hsep) (D.forward_middles_disjoint T)
  exact ⟨U,fun d => ⟨(hU d).1,(hU d).2.2,
    polygonallyJoined_of_path (hU d).1 (T d).middle (hU d).2.1⟩,hd⟩

end Drawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_WeightedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Weighted
variable {V : Type} {G : SimpleGraph V} {l : V → V → ℝ}

lemma distance_nonneg (hl : ∀ u v, G.Adj u v → 0 ≤ l u v)
    {u v : V} (hc : G.Reachable u v) : 0 ≤ graphDistance G l u v := by
  obtain ⟨p⟩ := hc
  exact le_csInf ⟨walkLength l p,⟨p,rfl⟩⟩ (by rintro a ⟨q,rfl⟩; exact length_nonneg hl q)

lemma distance_self (hl : ∀ u v, G.Adj u v → 0 ≤ l u v) (u : V) :
    graphDistance G l u u=0 :=
  le_antisymm (distance_le_walk hl .nil) (distance_nonneg hl (.refl u))

end Weighted
end PlanarL1



end

section

/-! ## Shortest-path spanning tree . -/

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

namespace shortestParents
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma parent_step (v : V) (hv : v ≠ o) :
    G.Adj ((shortestParents hc hs hl o).parent v) v ∧
    graphDistance G l o v = graphDistance G l o ((shortestParents hc hs hl o).parent v)+
      l ((shortestParents hc hs hl o).parent v) v := by
  dsimp only [shortestParents]
  rw [dite_eq_right hv]
  exact ⟨(exists_predecessor hc hs hl o v hv).choose_spec.1,
    (exists_predecessor hc hs hl o v hv).choose_spec.2.1⟩

lemma graph_le : (shortestParents hc hs hl o).graph ≤ G := by
  intro u v h
  rcases h with ⟨hu,rfl⟩ | ⟨hv,rfl⟩
  · exact (parent_step hc hs hl o u hu).1.symm
  · exact (parent_step hc hs hl o v hv).1

end shortestParents
end PlanarL1.Weighted



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_HeightTree
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1

namespace HeightTree
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : HeightTree V)

lemma profile_eq (q : V → ℝ) (v : V) :
    T.profile q v = if _h : v = T.root then fun H => q v + |H-T.height v|
      else fun H => min (T.profile q (T.parent v) H) (q v + |H-T.height v|) := by
  rw [profile,WellFounded.fix_eq]
  rfl

lemma profile_root (q : V → ℝ) (H : ℝ) :
    T.profile q T.root H = q T.root + |H-T.height T.root| := by
  rw [profile_eq,dite_eq_left rfl]

lemma profile_child (q : V → ℝ) {v : V} (hv : v ≠ T.root) (H : ℝ) :
    T.profile q v H = min (T.profile q (T.parent v) H) (q v + |H-T.height v|) := by
  rw [profile_eq,dite_eq_right hv]

lemma profile_le_cone (q : V → ℝ) (v : V) (H : ℝ) :
    T.profile q v H ≤ q v + |H-T.height v| := by
  by_cases hv : v = T.root
  · subst v; rw [profile_root]
  · rw [profile_child _ _ hv]; exact min_le_right _ _

lemma profile_lipschitz (q : V → ℝ) (v : V) : LipschitzWith 1 (T.profile q v) := by
  induction v using T.wf.induction with
  | h v ih =>
    have hcone : LipschitzWith 1 (fun H : ℝ => q v + |H-T.height v|) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq,add_sub_add_comm,sub_self,zero_add,NNReal.coe_one,one_mul] using
        abs_dist_sub_le x y (T.height v)
    by_cases hv : v = T.root
    · rw [profile_eq,dite_eq_left hv]; exact hcone
    · rw [profile_eq,dite_eq_right hv]
      simpa only [max_self] using (ih (T.parent v) ⟨hv,rfl⟩).min hcone

lemma profile_above {q : V → ℝ} (hq : T.Compatible q) (v : V) {H : ℝ}
    (hH : T.height v ≤ H) : T.profile q v H = q v + (H-T.height v) := by
  induction v using T.wf.induction with
  | h v ih =>
    by_cases hv : v = T.root
    · subst v; rw [profile_root,abs_of_nonneg (sub_nonneg.mpr hH)]
    · rw [profile_child _ _ hv,ih (T.parent v) ⟨hv,rfl⟩ ((T.height_mono v).trans hH),
        abs_of_nonneg (sub_nonneg.mpr hH)]
      apply min_eq_right
      have hb := (abs_le.mp (hq v)).2
      linarith

lemma profile_at {q : V → ℝ} (hq : T.Compatible q) (v : V) :
    T.profile q v (T.height v) = q v := by
  simpa only [sub_self,add_zero] using T.profile_above hq v le_rfl

lemma profile_below_parent {q : V → ℝ} (hq : T.Compatible q) {v : V}
    (hv : v ≠ T.root) {H : ℝ} (hH : H ≤ T.height (T.parent v)) :
    T.profile q v H = T.profile q (T.parent v) H := by
  rw [profile_child _ _ hv]
  apply min_eq_left
  have hc := T.profile_le_cone q (T.parent v) H
  rw [abs_of_nonpos (sub_nonpos.mpr hH)] at hc
  rw [abs_of_nonpos (sub_nonpos.mpr (hH.trans (T.height_mono v)))]
  have hb := (abs_le.mp (hq v)).1
  linarith

/-- Common root prefixes receive literally the same potential on every copy. -/
lemma profile_ancestor {q : V → ℝ} (hq : T.Compatible q) {u v : V}
    (h : T.Ancestor u v) {H : ℝ} (hH : H ≤ T.height u) :
    T.profile q v H = T.profile q u H := by
  induction h with
  | refl => rfl
  | @tail v w huv hvw ih =>
    rw [T.profile_below_parent hq hvw.1 (hH.trans (T.ancestor_height huv) |>.trans_eq (congrArg T.height hvw.2)),
      ← hvw.2]
    exact ih

lemma ancestor_leafAbove [Fintype V] (v : V) : T.Ancestor v (T.leafAbove v).val :=
  (T.exists_leaf v).choose_spec.1

end HeightTree
end PlanarL1

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}

namespace ExtraDart
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma tipHeight_reverse (d : ExtraDart hc hs hl o) :
    tipHeight hc hs hl o (reverse hc hs hl o d)=tipHeight hc hs hl o d := by
  change (l d.val.snd d.val.fst + graphDistance G l o d.val.snd + graphDistance G l o d.val.fst)/2 = _
  rw [hs d.val.snd d.val.fst]
  unfold tipHeight
  ring

end ExtraDart

namespace EnlargedTree
variable (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma extra_leaf (d : ExtraDart hc hs hl o) :
    (tree hc hs hl o).IsLeaf (.inr d) := by
  intro v h
  cases v <;> exact Sum.inr_ne_inl h.2

lemma potential_reverse (z : V) (d : ExtraDart hc hs hl o) :
    potential hc hs hl o z (.inr (ExtraDart.reverse hc hs hl o d)) =
      potential hc hs hl o z (.inr d) := by
  change min
    (graphDistance G l z d.val.snd + ExtraDart.tipHeight hc hs hl o (ExtraDart.reverse hc hs hl o d) - graphDistance G l o d.val.snd)
    (graphDistance G l z d.val.fst + ExtraDart.tipHeight hc hs hl o (ExtraDart.reverse hc hs hl o d) - graphDistance G l o d.val.fst) = _
  rw [ExtraDart.tipHeight_reverse]
  exact min_comm _ _

lemma min_split_compatible {du dv a b : ℝ} (ha : 0≤a)
    (h : |du-dv|≤a+b) : |min (du+a) (dv+b)-du|≤a := by
  apply abs_le.mpr
  constructor
  · have h₁ : du-a≤du+a := by linarith
    have h₂ : du-a≤dv+b := by have := (abs_le.mp h).2; linarith
    have := le_min h₁ h₂
    linarith
  · have := min_le_left (du+a) (dv+b)
    linarith

lemma potential_compatible (z : V) :
    (tree hc hs hl o).Compatible (potential hc hs hl o z) := by
  intro v
  cases v with
  | inl v =>
    change |graphDistance G l z v - graphDistance G l z ((shortestParents hc hs hl o).parent v)| ≤
      graphDistance G l o v - graphDistance G l o ((shortestParents hc hs hl o).parent v)
    by_cases hv : v=o
    · subst v
      have hr : (shortestParents hc hs hl o).parent o=o := (shortestParents hc hs hl o).at_root
      rw [hr,sub_self,abs_zero,sub_self]
    · obtain ⟨hedge,hlen⟩ := shortestParents.parent_step hc hs hl o v hv
      have h := height_edge hc hs (fun u v h => (hl u v h).le) z hedge.symm
      rw [hs v ((shortestParents hc hs hl o).parent v)] at h
      linarith
  | inr d =>
    have ha := ExtraDart.height_le_tip hc hs hl o d
    have hd := height_edge hc hs (fun u v h => (hl u v h).le) z d.val.adj
    have hsum : (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.fst)+
        (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.snd)=l d.val.fst d.val.snd := by
      unfold ExtraDart.tipHeight
      ring
    have hx := min_split_compatible (du := graphDistance G l z d.val.fst)
      (dv := graphDistance G l z d.val.snd)
      (b := ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.snd)
      (sub_nonneg.mpr ha) (by rw [hsum]; exact hd)
    change |min (_ + _ - _) (_ + _ - _) - graphDistance G l z d.val.fst| ≤ ExtraDart.tipHeight hc hs hl o d-graphDistance G l o d.val.fst
    simpa only [add_sub_assoc] using hx

end EnlargedTree
end PlanarL1.Weighted

namespace PlanarL1.HeightTree
open Set Columns
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {n : ℕ} (T : HeightTree V)

namespace Layout
variable {T} (L : T.Layout n)

lemma ancestor_column (v : V) : T.Ancestor v (L.leaf (L.column v)) := by
  rw [column,(L.covers _ (T.leafAbove v).property).choose_spec]
  exact T.ancestor_leafAbove v

end Layout
end PlanarL1.HeightTree

namespace PlanarL1.Columns.Model
open Set
variable {n : ℕ} (M : Model n)

/-- A scalar potential compatible with every actual switch bounds the length
of every switching path, irrespective of excursions into the separate tails. -/
lemma Path.potential_le {J : Set ℝ} {i j : Fin n} (p : M.Path J i j)
    (q : Fin n → ℝ → ℝ) (hLip : ∀ i, LipschitzWith 1 (q i))
    (hSwitch : ∀ i j H, H ∈ M.heights i j → q i H=q j H) (a b : ℝ) :
    |q i a-q j b| ≤ p.length a b := by
  induction p generalizing a with
  | nil i => simpa only [Path.length,Real.dist_eq,NNReal.coe_one,one_mul] using (hLip i).dist_le_mul a b
  | @cons i j k H hH hs p ih =>
    have hl : |q i a-q i H|≤|a-H| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using (hLip i).dist_le_mul a H
    have hb := abs_sub_le (q i a) (q i H) (q k b)
    rw [hSwitch i j H hs] at hb
    exact hb.trans (add_le_add (by rwa [← hSwitch i j H hs]) (ih H))

lemma Point.potential_le {J : Set ℝ} {root : Fin n} (x y : M.Point J root)
    (q : Fin n → ℝ → ℝ) (hLip : ∀ i, LipschitzWith 1 (q i))
    (hSwitch : ∀ i j H, H ∈ M.heights i j → q i H=q j H) :
    |q x.column x.height-q y.column y.height| ≤ x.distance y := by
  have := x.paths_nonempty y
  exact le_ciInf (fun p => p.potential_le M q hLip hSwitch x.height y.height)
end PlanarL1.Columns.Model

namespace PlanarL1.HeightTree
open Set Columns
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {n : ℕ} {T : HeightTree V}

namespace Layout
variable (L : T.Layout n)

lemma leaf_column {v : V} (hv : T.IsLeaf v) : L.leaf (L.column v)=v :=
  (hv.ancestor_eq (L.ancestor_column v)).symm

lemma column_leaf (i : Fin n) : L.column (L.leaf i)=i :=
  L.injective (L.leaf_column (L.isLeaf i))

lemma profile_switch {q : V → ℝ} (hq : T.Compatible q)
    (hpair : ∀ i j, L.pair.Adj i j → q (L.leaf i)=q (L.leaf j))
    (i j : Fin n) (H : ℝ) (hs : H ∈ L.model.heights i j) :
    T.profile q (L.leaf i) H=T.profile q (L.leaf j) H := by
  rcases (L.mem_heights i j H).mp hs with ⟨a,ha,_,hH⟩ | ⟨ha,rfl⟩
  · rw [T.profile_ancestor hq ha.2.2.1 hH,T.profile_ancestor hq ha.2.2.2 hH]
  · rw [T.profile_at hq,L.paired_height i j ha,T.profile_at hq,hpair i j ha]

lemma potential_le {q : V → ℝ} (hq : T.Compatible q)
    (hpair : ∀ i j, L.pair.Adj i j → q (L.leaf i)=q (L.leaf j)) (v w : V) :
    |q v-q w|≤(L.point v).distance (L.point w) := by
  have h := (L.point v).potential_le L.model (L.point w)
    (fun i => T.profile q (L.leaf i)) (fun i => T.profile_lipschitz q (L.leaf i))
    (L.profile_switch hq hpair)
  change |T.profile q (L.leaf (L.column v)) (T.height v)-
    T.profile q (L.leaf (L.column w)) (T.height w)|≤_ at h
  rwa [T.profile_ancestor hq (L.ancestor_column v) le_rfl,
    T.profile_ancestor hq (L.ancestor_column w) le_rfl,T.profile_at hq,T.profile_at hq] at h

lemma parent_distance_le (v : V) :
    (L.point v).distance (L.point (T.parent v))≤T.height v-T.height (T.parent v) := by
  by_cases hv : v=T.root
  · subst v
    rw [T.at_root,Model.Point.distance_self,sub_self]
  · have had : T.Ancestor (T.parent v) (L.leaf (L.column v)) :=
      (Relation.ReflTransGen.single ⟨hv,rfl⟩).trans (L.ancestor_column v)
    obtain ⟨p,hp⟩ := L.exists_prefixPath had (L.ancestor_column (T.parent v))
      (T.ancestor_height (T.root_ancestor (T.parent v))) le_rfl
    have h := (L.point v).distance_le (L.point (T.parent v)) p
    have hb := p.length_start_le (T.height v) (T.height (T.parent v)) (T.height (T.parent v))
    rw [hp,add_zero,abs_of_nonneg (sub_nonneg.mpr (T.height_mono v))] at hb
    exact h.trans hb

lemma pair_distance_zero {i j : Fin n} (h : L.pair.Adj i j) :
    (L.point (L.leaf i)).distance (L.point (L.leaf j))=0 := by
  apply le_antisymm _ (Model.Point.distance_nonneg _ _)
  let p : L.model.Path univ (L.point (L.leaf i)).column (L.point (L.leaf j)).column :=
    .cons (T.height (L.leaf i)) (mem_univ _) (by
      change T.height (L.leaf i) ∈ L.heights (L.column (L.leaf i)) (L.column (L.leaf j))
      rw [L.column_leaf,L.column_leaf]
      exact (L.mem_heights _ _ _).mpr (Or.inr ⟨h,rfl⟩)) (.nil _)
  have he : p.length (T.height (L.leaf i)) (T.height (L.leaf j))=0 := by
    simp only [p,Model.Path.length,sub_self,abs_zero,L.paired_height i j h,zero_add]
  exact ((L.point (L.leaf i)).distance_le _ p).trans_eq he

end Layout
end PlanarL1.HeightTree

namespace PlanarL1.Weighted
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

namespace EnlargedTree
variable {hc hs hl o} {n : ℕ} (L : (tree hc hs hl o).Layout n)

lemma original_distance_lower (hpair : ExactPairs L) (u v : V) :
    graphDistance G l u v ≤ (L.point (.inl u)).distance (L.point (.inl v)) := by
  have hh := L.potential_le (potential_compatible hc hs hl o u) (fun i j h => by
    obtain ⟨d,hi,hj⟩ := (hpair i j).mp h
    rw [hi,hj]
    exact (potential_reverse hc hs hl o u d).symm) (.inl u) (.inl v)
  change |graphDistance G l u u-graphDistance G l u v|≤_ at hh
  rwa [distance_self (fun u v h => (hl u v h).le),zero_sub,abs_neg,
    abs_of_nonneg (distance_nonneg (fun u v h => (hl u v h).le) (hc.preconnected u v))] at hh

lemma tip_pair (hpair : ExactPairs L) (d : ExtraDart hc hs hl o) :
    L.pair.Adj (L.column (.inr d)) (L.column (.inr (ExtraDart.reverse hc hs hl o d))) := by
  apply (hpair _ _).mpr
  exact ⟨d,L.leaf_column (extra_leaf hc hs hl o d),
    L.leaf_column (extra_leaf hc hs hl o (ExtraDart.reverse hc hs hl o d))⟩

lemma tip_distance_zero (hpair : ExactPairs L) (d : ExtraDart hc hs hl o) :
    (L.point (.inr d)).distance (L.point (.inr (ExtraDart.reverse hc hs hl o d)))=0 := by
  have h := L.pair_distance_zero (tip_pair L hpair d)
  rwa [L.leaf_column (extra_leaf hc hs hl o d),
    L.leaf_column (extra_leaf hc hs hl o (ExtraDart.reverse hc hs hl o d))] at h

lemma original_parent_distance (v : V) (hv : v≠o) :
    (L.point (.inl v)).distance (L.point (.inl ((shortestParents hc hs hl o).parent v))) ≤
      l v ((shortestParents hc hs hl o).parent v) := by
  have h := L.parent_distance_le (.inl v)
  change (L.point (.inl v)).distance (L.point (.inl ((shortestParents hc hs hl o).parent v))) ≤
    graphDistance G l o v-graphDistance G l o ((shortestParents hc hs hl o).parent v) at h
  obtain ⟨_,he⟩ := shortestParents.parent_step hc hs hl o v hv
  rw [hs v ((shortestParents hc hs hl o).parent v)]
  linarith

lemma original_edge_distance (hpair : ExactPairs L) {u v : V} (h : G.Adj u v) :
    (L.point (.inl u)).distance (L.point (.inl v))≤l u v := by
  by_cases ht : (shortestParents hc hs hl o).graph.Adj u v
  · rcases ht with ⟨hu,rfl⟩ | ⟨hv,rfl⟩
    · exact original_parent_distance L u hu
    · rw [Columns.Model.Point.distance_comm,hs]
      exact original_parent_distance L v hv
  · let d : ExtraDart hc hs hl o := ⟨⟨(u,v),h⟩,ht⟩
    have hd := L.parent_distance_le (.inr d)
    have hr := L.parent_distance_le (.inr (ExtraDart.reverse hc hs hl o d))
    have hz := tip_distance_zero L hpair d
    have h₁ := (L.point (.inl u)).distance_triangle (L.point (.inr d)) (L.point (.inl v))
    have h₂ := (L.point (.inr d)).distance_triangle
      (L.point (.inr (ExtraDart.reverse hc hs hl o d))) (L.point (.inl v))
    rw [hz,zero_add] at h₂
    change (L.point (.inr d)).distance (L.point (.inl u))≤
      ExtraDart.tipHeight hc hs hl o d-graphDistance G l o u at hd
    change (L.point (.inr (ExtraDart.reverse hc hs hl o d))).distance (L.point (.inl v))≤
      ExtraDart.tipHeight hc hs hl o (ExtraDart.reverse hc hs hl o d)-graphDistance G l o v at hr
    rw [ExtraDart.tipHeight_reverse] at hr
    rw [Columns.Model.Point.distance_comm] at hd
    have hsum : (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o u)+
        (ExtraDart.tipHeight hc hs hl o d-graphDistance G l o v)=l u v := by
      dsimp [ExtraDart.tipHeight,d]
      ring
    linarith

lemma original_walk_distance (hpair : ExactPairs L) {u v : V} (p : G.Walk u v) :
    (L.point (.inl u)).distance (L.point (.inl v))≤walkLength l p := by
  induction p with
  | nil => rw [walkLength,Columns.Model.Point.distance_self]
  | @cons u w v h p ih =>
    exact ((L.point (.inl u)).distance_triangle (L.point (.inl w)) (L.point (.inl v))).trans
      (add_le_add (original_edge_distance L hpair h) ih)

/-- The original weighted graph embeds isometrically into the actual column
path metric. In particular all tails and zero-length branch incidences are
accounted for; the lower bound is certified by graph-distance potentials. -/
lemma original_distance (hpair : ExactPairs L) (u v : V) :
    (L.point (.inl u)).distance (L.point (.inl v))=graphDistance G l u v := by
  apply le_antisymm _ (original_distance_lower L hpair u v)
  obtain ⟨p,hp,_⟩ := distance_eq_length (fun u v h => (hl u v h).le) (hc.preconnected u v)
  rw [hp]
  exact original_walk_distance L hpair p.val

end EnlargedTree
end PlanarL1.Weighted



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Polygonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma PolygonallyJoined.exists_segmentChain {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) : ∃ n, Nonempty (SegmentChain S x y n) := by
  induction h with
  | refl => exact ⟨0,⟨SegmentChain.nil _⟩⟩
  | @tail y z h hyz ih =>
    obtain ⟨n,⟨P⟩⟩ := ih
    exact ⟨n+1,⟨P.append hyz⟩⟩

/-- A collinear broken segment covers the direct segment. -/
lemma collinear_segment_union {a b c : E} (h : Collinear ℝ ({a,b,c} : Set E)) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  by_cases hac : a=c
  · subst c
    simp only [segment_same,singleton_subset_iff,mem_union]
    exact Or.inl (left_mem_segment ℝ a b)
  have hb : b ∈ line[ℝ,a,c] := h.mem_affineSpan_of_mem_of_ne
    (by simp) (by simp) (by simp) hac
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hb
  apply (openSegment_subset_iff_segment_subset (𝕜 := ℝ)
    (s := segment ℝ a b ∪ segment ℝ b c)
    (Or.inl (left_mem_segment ℝ a b)) (Or.inr (right_mem_segment ℝ b c))).mp
  intro z hz
  rcases openSegment_subset_union a c (⟨t,ht⟩ : b ∈ Set.range (AffineMap.lineMap a c : ℝ → E)) hz with
    hzb | hzb | hzb
  · exact Or.inl (hzb ▸ right_mem_segment ℝ a b)
  · exact Or.inl (openSegment_subset_segment ℝ a b hzb)
  · exact Or.inr (openSegment_subset_segment ℝ b c hzb)

/-- Adjacent non-collinear segments have no intersection except their common
endpoint. This elementary fact supplies loop erasure without a Jordan theorem. -/
lemma collinear_of_adjacent_overlap {a b c z : E}
    (hz : z ∈ segment ℝ a b) (hz' : z ∈ segment ℝ b c) (hne : z≠b) :
    Collinear ℝ ({a,b,c} : Set E) := by
  have h₁ := (mem_segment_iff_wbtw.mp hz).collinear
  have h₂ := (mem_segment_iff_wbtw.mp hz').collinear
  have h₂' : Collinear ℝ ({c,b,z} : Set E) := by
    have hs : ({c,b,z} : Set E) = {b,z,c} := by
      ext w
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    rw [hs]
    exact h₂
  have hh := (h₁.collinear_insert_iff_of_ne (p₁:=c) (p₂:=b) (p₃:=z)
    (by simp) (by simp) hne.symm).mpr h₂'
  exact Collinear.subset (by
    intro w hw
    simp only [mem_insert_iff,mem_singleton_iff] at hw ⊢
    tauto) hh

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

lemma minimal_vertex_injective (h : P.IsMinimal) : Set.InjOn P.vertex (Set.Iic n) := by
  intro i hi j hj heq
  change i ≤ n at hi
  change j ≤ n at hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh := h (n-j+i) ⟨P.eraseLoop i j hij hj heq⟩
    omega
  · have hh := h (n-i+j) ⟨P.eraseLoop j i hji hi heq.symm⟩
    omega

lemma minimal_nonadjacent (h : P.IsMinimal) {i j : ℕ} (hij : i+1<j) (hjn : j<n) :
    Disjoint (segment ℝ (P.vertex i) (P.vertex (i+1)))
      (segment ℝ (P.vertex j) (P.vertex (j+1))) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hh := h (n-j+i+1) ⟨P.shortcutAt i j (by omega) hjn z hzi hzj⟩
  omega

lemma minimal_adjacent (h : P.IsMinimal) {i : ℕ} (hi : i+1<n) {z : E}
    (hzi : z ∈ segment ℝ (P.vertex i) (P.vertex (i+1)))
    (hzj : z ∈ segment ℝ (P.vertex (i+1)) (P.vertex (i+1+1))) : z=P.vertex (i+1) := by
  by_contra hne
  have hcol := collinear_of_adjacent_overlap hzi hzj hne
  have hseg : segment ℝ (P.vertex i) (P.vertex (i+1+1)) ⊆ S :=
    (collinear_segment_union hcol).trans (Set.union_subset (P.segment_mem i (by omega))
      (P.segment_mem (i+1) hi))
  have hh := h (n-(i+1+1)+i+1) ⟨P.shortcut i (i+1+1) (by omega) (by omega) hseg⟩
  omega

lemma minimal_simple (h : P.IsMinimal) : P.IsSimple := by
  refine ⟨P.minimal_vertex_injective h,fun i j hij hjn z hzi hzj => ?_⟩
  by_cases heq : j=i+1
  · subst j
    exact ⟨rfl,P.minimal_adjacent h hjn hzi hzj⟩
  · exact False.elim (Set.disjoint_left.mp (P.minimal_nonadjacent h (by omega) hjn) hzi hzj)
end SegmentChain

/-- Every finite polygonal connection contains a simple finite polygonal
connection with the same endpoints and no larger trace. -/
lemma PolygonallyJoined.exists_simple_segmentChain {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) :
    ∃ n, ∃ P : SegmentChain S x y n, P.IsSimple := by
  classical
  let hh := h.exists_segmentChain
  let n := Nat.find hh
  let P := Classical.choice (Nat.find_spec hh)
  exact ⟨n,P,P.minimal_simple (fun m hm => Nat.find_min' hh hm)⟩

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

lemma trace_subset (hx : x ∈ S) : P.trace ⊆ S := by
  rintro z (rfl | hz)
  · exact hx
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact P.segment_mem i i.isLt hi

lemma vertex_mem_trace (i : ℕ) (hi : i ≤ n) : P.vertex i ∈ P.trace := by
  by_cases h0 : i=0
  · simp [h0,P.start,trace]
  · have hi' : i-1<n := by omega
    exact Or.inr (mem_iUnion.mpr ⟨⟨i-1,hi'⟩,by
      have he : i-1+1=i := by omega
      simpa only [he] using right_mem_segment ℝ (P.vertex (i-1)) (P.vertex i)⟩)

lemma start_mem_trace : x ∈ P.trace := Or.inl rfl
lemma finish_mem_trace : y ∈ P.trace := by
  have h := P.vertex_mem_trace n le_rfl
  rwa [P.finish] at h

end SegmentChain

lemma radial_segment_dist_le {x y z : E} {r : ℝ} (hr : 0 ≤ r) (hy : dist y x=r)
    (hz : z ∈ segment ℝ x y) : dist z x ≤ r := by
  exact (convex_closedBall x r).segment_subset (by simpa using hr)
    (by simp [Metric.mem_closedBall,hy] : y ∈ closedBall x r) hz

namespace Drawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
variable {r : ℝ} (T : ∀ d : ForwardDart G, D.EdgeTrim r d.val)

lemma port_sphere (d : ForwardDart G) (b : Bool) :
    dist (D.port T d b) (D.point (portVertex d b))=r := by
  cases b
  · exact (T d).first_sphere
  · exact (T d).last_sphere

lemma head_dist {d : ForwardDart G} {b : Bool} {z : ℂ} (hr : 0 < r)
    (hz : z ∈ D.head T d b) : dist z (D.point (portVertex d b)) ≤ r :=
  radial_segment_dist_le hr.le (D.port_sphere T d b) hz

lemma ports_distinct {d e : ForwardDart G} (hde : d≠e) (b c : Bool) :
    D.port T d b ≠ D.port T e c := by
  intro he
  have h (d : ForwardDart G) (b : Bool) :
      0<((if b then (T d).last else (T d).first : unitInterval):ℝ) ∧
      ((if b then (T d).last else (T d).first : unitInterval):ℝ)<1 := by
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact ⟨(T d).first_pos,by linarith [(T d).first_lt]⟩
    · exact ⟨by linarith [(T d).last_gt],(T d).last_lt_one⟩
  exact hde (ForwardDart.eq_of_endpoints d e (D.interior_disjoint _ _ _ _ _ _ _ _
    (h d b).1 (h d b).2 (h e c).1 (h e c).2 he))

lemma heads_intersect (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {d e : ForwardDart G} (hde : d≠e) {b c : Bool} {z : ℂ}
    (hz : z ∈ D.head T d b) (hz' : z ∈ D.head T e c) :
    z=D.point (portVertex d b) ∧ z=D.point (portVertex e c) := by
  have heq : portVertex d b=portVertex e c := by
    by_contra hne
    have hfar := hsep (portVertex d b) (D.point (portVertex e c))
      (D.point_mem_forbidden _ _ (fun h => hne h.symm))
    have ht := dist_triangle (D.point (portVertex d b)) z (D.point (portVertex e c))
    have h₁ := D.head_dist T hr hz
    have h₂ := D.head_dist T hr hz'
    rw [dist_comm z (D.point (portVertex d b))] at h₁
    linarith
  have hw : dist (D.port T e c) (D.point (portVertex d b))=r :=
    heq ▸ D.port_sphere T e c
  have he : z=D.point (portVertex d b) := radial_heads_intersect hr
    (D.port_sphere T d b) hw (D.ports_distinct T hde b c) hz (by simpa [head,heq] using hz')
  exact ⟨he,he.trans (congrArg D.point heq)⟩

lemma vertex_mem_head (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {d : ForwardDart G} {b : Bool} {w : V} (hw : D.point w ∈ D.head T d b) :
    w=portVertex d b := by
  by_contra hne
  have hfar := hsep (portVertex d b) (D.point w) (D.point_mem_forbidden _ _ hne)
  have hn := D.head_dist T hr hw
  rw [dist_comm] at hn
  linarith

lemma head_mem_obstacle {d e : ForwardDart G} (hde : e≠d) (b : Bool) :
    D.head T e b ⊆ D.middleObstacle T d := by
  intro z hz
  apply Or.inr
  refine mem_iUnion.mpr ⟨⟨e,hde⟩,?_⟩
  cases b
  · exact Or.inl hz
  · exact Or.inr hz

lemma region_joined {U : ForwardDart G → Set ℂ} (d : ForwardDart G)
    (h : PolygonallyJoined (U d) (D.port T d false) (D.port T d true)) :
    PolygonallyJoined (D.edgeRegion T U d) (D.point d.val.fst) (D.point d.val.snd) := by
  have h₁ : PolygonallyJoined (D.edgeRegion T U d) (D.point d.val.fst) (D.port T d false) :=
    Relation.ReflTransGen.single (fun _ hz => Or.inr (Or.inl hz))
  have h₂ : PolygonallyJoined (D.edgeRegion T U d) (D.port T d true) (D.point d.val.snd) :=
    Relation.ReflTransGen.single (fun _ hz => Or.inr (Or.inr (by
      simpa [head,portVertex,segment_symm] using hz)))
  exact (h₁.trans (h.mono Set.subset_union_left)).trans h₂

lemma region_vertex (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {U : ForwardDart G → Set ℂ} (hU : ∀ d, Disjoint (U d) (D.middleObstacle T d))
    {d : ForwardDart G} {w : V} (hw : D.point w ∈ D.edgeRegion T U d) :
    w=d.val.fst ∨ w=d.val.snd := by
  rcases hw with hw | hw | hw
  · exact False.elim (Set.disjoint_left.mp (hU d) hw (Or.inl ⟨w,rfl⟩))
  · exact Or.inl (D.vertex_mem_head T hr hsep hw)
  · exact Or.inr (D.vertex_mem_head T hr hsep hw)

lemma regions_intersect (hr : 0 < r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {U : ForwardDart G → Set ℂ} (hU : ∀ d, Disjoint (U d) (D.middleObstacle T d))
    (hUU : Pairwise (fun d e => Disjoint (U d) (U e)))
    {d e : ForwardDart G} (hde : d≠e) {z : ℂ}
    (hz : z ∈ D.edgeRegion T U d) (hz' : z ∈ D.edgeRegion T U e) :
    (z=D.point d.val.fst ∨ z=D.point d.val.snd) ∧
      (z=D.point e.val.fst ∨ z=D.point e.val.snd) := by
  have leftHead (b : Bool) (hb : z ∈ D.head T d b) : z ∉ U e := by
    intro hu
    exact Set.disjoint_left.mp (hU e) hu (D.head_mem_obstacle T hde b hb)
  have rightHead (b : Bool) (hb : z ∈ D.head T e b) : z ∉ U d := by
    intro hu
    exact Set.disjoint_left.mp (hU d) hu (D.head_mem_obstacle T hde.symm b hb)
  rcases hz with hz | hz | hz <;> rcases hz' with hz' | hz' | hz'
  · exact False.elim (Set.disjoint_left.mp (hUU hde) hz hz')
  · exact False.elim (rightHead false hz' hz)
  · exact False.elim (rightHead true hz' hz)
  · exact False.elim (leftHead false hz hz')
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inl he.1,Or.inl he.2⟩
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inl he.1,Or.inr he.2⟩
  · exact False.elim (leftHead true hz hz')
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inr he.1,Or.inl he.2⟩
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inr he.1,Or.inr he.2⟩

end Drawing
end PlanarL1.Topology

namespace PlanarL1.Topology
open Set

namespace SegmentChain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S T : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

lemma mapSet_simple (h : S ⊆ T) (hP : P.IsSimple) : (P.mapSet h).IsSimple := hP

end SegmentChain

/-- Simultaneous polygonalization of a finite topological graph drawing.
The original positions of all vertices are retained. -/
lemma Drawing.polygonal {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V}
    (D : Drawing G) : ∃ P : PLDrawing G, P.point=D.point := by
  classical
  obtain ⟨r,hr,hsep⟩ := D.uniform_vertex_disks
  let T (d : ForwardDart G) : D.EdgeTrim r d.val :=
    Classical.choice (D.edgeTrim_nonempty hr hsep d.val)
  obtain ⟨U,hU,hUU⟩ := D.polygonal_middles T hr hsep
  have hj (d : ForwardDart G) := D.region_joined T d (hU d).2.2
  choose n P hP using fun d => (hj d).exists_simple_segmentChain
  have hstart (d : ForwardDart G) : D.point d.val.fst ∈ D.edgeRegion T U d :=
    Or.inr (Or.inl (left_mem_segment ℝ _ _))
  refine ⟨⟨D.point,D.point_injective,n,fun d => (P d).mapSet (Set.subset_univ _),
    fun d => (P d).mapSet_simple _ (hP d),?_,?_⟩,rfl⟩
  · intro d w hw
    apply D.region_vertex T hr hsep (fun d => (hU d).2.1)
    exact (P d).trace_subset (hstart d) hw
  · intro d e hde z hz hz'
    exact D.regions_intersect T hr hsep (fun d => (hU d).2.1) hUU hde
      ((P d).trace_subset (hstart d) hz) ((P e).trace_subset (hstart e) hz')

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Boundary points of a convex neighbourhood have a unique positive radial
coordinate. This will keep the extended leaf ports disjoint when shrinking
an embedded finite tree inside a convex merging region. -/
lemma convex_frontier_radial_injective {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p q : E} (hp : p ∈ frontier S) (hq : q ∈ frontier S)
    {s t : ℝ} (hs : 0 < s) (ht : 0<t) (he : s • p=t • q) : s=t ∧ p=q := by
  have hp' : gauge S p=1 := (gauge_eq_one_iff_mem_frontier hS h0).mpr hp
  have hq' : gauge S q=1 := (gauge_eq_one_iff_mem_frontier hS h0).mpr hq
  have h := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg hs.le, gauge_smul_of_nonneg ht.le, hp',hq'] at h
  simp only [smul_eq_mul,mul_one] at h
  refine ⟨h,?_⟩
  subst t
  exact smul_right_injective E hs.ne' he

/-- The outer radial tails from different ports never meet, including their
endpoints. -/
lemma convex_frontier_tails_disjoint {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p q : E} (hp : p ∈ frontier S) (hq : q ∈ frontier S)
    (hpq : p≠q) {c : ℝ} (hc : 0 < c) (hc1 : c≤1) :
    Disjoint (segment ℝ (c•p) p) (segment ℝ (c•q) q) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [segment_eq_image' ℝ (c•p) p] at hz
  rw [segment_eq_image' ℝ (c•q) q] at hz'
  obtain ⟨s,hs,rfl⟩ := hz
  obtain ⟨t,ht,he⟩ := hz'
  have hform (u : ℝ) (v : E) : c•v+u•(v-c•v)=(c+u*(1-c))•v := by
    module
  dsimp only at he
  rw [hform,hform] at he
  have hs' : 0 < c+s*(1-c) := by nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hc1)]
  have ht' : 0 < c+t*(1-c) := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc1)]
  exact hpq (convex_frontier_radial_injective hS h0 hp hq hs' ht' he.symm).2

lemma convex_frontier_tail_core {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p z : E} (hp : p ∈ frontier S)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hz : z ∈ segment ℝ (c•p) p) (hcore : z ∈ (fun x : E => c•x) '' closure S) : z=c•p := by
  rw [segment_eq_image' ℝ (c•p) p] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  obtain ⟨w,hw,he⟩ := hcore
  have hform : c•p+t•(p-c•p)=(c+t*(1-c))•p := by module
  dsimp only at he ⊢
  rw [hform] at he ⊢
  have hg := congrArg (gauge S) he
  have hp' := (gauge_eq_one_iff_mem_frontier hS h0).mpr hp
  have hcoef : 0 ≤ c+t*(1-c) := add_nonneg hc.le (mul_nonneg ht.1 (sub_nonneg.mpr hc1))
  rw [gauge_smul_of_nonneg hc.le,gauge_smul_of_nonneg hcoef,hp',smul_eq_mul,smul_eq_mul,mul_one] at hg
  have hw' : gauge S w≤1 := (gauge_le_one_iff_mem_closure hS h0).mpr hw
  have hle : c+t*(1-c) ≤ c := by nlinarith
  have hge : c ≤ c+t*(1-c) := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc1)]
  rw [le_antisymm hle hge]

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set Metric Filter

/-- A straight selected tree piece has an arbitrarily thin bounded convex
merging region avoiding every closed nonincident obstacle. -/
lemma convex_tube_avoiding {a b : ℂ} {F : Set ℂ} (hF : IsClosed F)
    (hdisj : Disjoint (segment ℝ a b) F) :
    ∃ S : Set ℂ, Convex ℝ S ∧ IsOpen S ∧ Bornology.IsBounded S ∧
      segment ℝ a b ⊆ S ∧ Disjoint (closure S) F := by
  obtain ⟨r,hr,hsub⟩ := (compact_segment_complex a b).exists_cthickening_subset_open
    hF.isOpen_compl hdisj.subset_compl_right
  refine ⟨thickening r (segment ℝ a b),(convex_segment a b).thickening r,
    isOpen_thickening,?_,self_subset_thickening hr _,?_⟩
  · exact (compact_segment_complex a b).isBounded.thickening
  · exact Set.disjoint_left.mpr (fun z hz hzF =>
      hsub (closure_thickening_subset_cthickening r _ hz) hzF)

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma image_segment_smul (c : ℝ) (x y : E) :
    (fun z : E => c•z) '' segment ℝ x y=segment ℝ (c•x) (c•y) := by
  simp only [segment_eq_image' ℝ,Set.image_image]
  congr 1
  funext t
  module

lemma PolygonallyJoined.smul {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) (c : ℝ) :
    PolygonallyJoined ((fun z : E => c•z) '' S) (c•x) (c•y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hab ih =>
    refine ih.tail ?_
    rw [← image_segment_smul]
    exact Set.image_mono hab

lemma SegmentChain.joined_trace {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n) :
    PolygonallyJoined P.trace x y := by
  have h : ∀ i, i≤n → PolygonallyJoined P.trace x (P.vertex i) := by
    intro i
    induction i with
    | zero => intro _; rw [P.start]; exact Relation.ReflTransGen.refl
    | succ i ih =>
      intro hi
      refine (ih (by omega)).tail ?_
      intro z hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,by omega⟩,hz⟩)
  simpa only [P.finish] using h n le_rfl

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

lemma leaf_incident_unique {B : Set V}
    (hleaf : ∀ v ∈ B, ∀ a b, G.Adj v a → G.Adj v b → a=b)
    {v : V} (hv : v∈B) {d e : ForwardDart G}
    (hd : Incident d v) (he : Incident e v) : d=e := by
  rcases hd with hd | hd <;> rcases he with he | he
  · have hv' : d.val.fst=e.val.fst := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inl ⟨hv',hleaf v hv _ _ (hd.symm ▸ d.val.adj) (he.symm ▸ e.val.adj)⟩
  · have hv' : d.val.fst=e.val.snd := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inr ⟨hv',hleaf v hv _ _ (hd.symm ▸ d.val.adj) (he.symm ▸ e.val.adj.symm)⟩
  · have hv' : d.val.snd=e.val.fst := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inr ⟨hleaf v hv _ _ (hd.symm ▸ d.val.adj.symm) (he.symm ▸ e.val.adj),hv'⟩
  · have hv' : d.val.snd=e.val.snd := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inl ⟨hleaf v hv _ _ (hd.symm ▸ d.val.adj.symm) (he.symm ▸ e.val.adj.symm),hv'⟩

variable {S : Set ℂ} (hS : Convex ℝ S) (h0 : S ∈ nhds (0:ℂ))
  (hpoint : ∀ v, P.point v ∈ closure S)
  {B : Set V} (hport : ∀ v ∈ B, P.point v ∈ frontier S)
  {c : ℝ} (hc : 0 < c) (hc1 : c<1)

include hS h0 hport hc hc1

lemma port_not_core {v : V} (hv : v∈B) :
    P.point v ∉ (fun z : ℂ => c•z) '' closure S := by
  rintro ⟨z,hz,he⟩
  have hg := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg hc.le,
    (gauge_eq_one_iff_mem_frontier hS h0).mpr (hport v hv)] at hg
  have hz' := (gauge_le_one_iff_mem_closure hS h0).mpr hz
  change c*gauge S z=1 at hg
  nlinarith

include hpoint

lemma newpoint_in_tail {v w : V} (hw : w∈B)
    (hv : P.expandedPoint B c v ∈ P.portTail c w) : v=w := by
  classical
  by_cases hvB : v∈B
  · by_contra hne
    have hd := convex_frontier_tails_disjoint hS h0 (hport v hvB) (hport w hw)
      (fun h => hne (P.point_injective h)) hc hc1.le
    exact Set.disjoint_left.mp hd (right_mem_segment ℝ _ _)
      (by simpa [expandedPoint,hvB,portTail] using hv)
  · apply P.point_injective
    apply smul_right_injective ℂ hc.ne'
    exact convex_frontier_tail_core hS h0 (hport w hw) hc hc1.le
      (by simpa [expandedPoint,hvB,portTail] using hv) ⟨P.point v,hpoint v,rfl⟩

omit hpoint in
lemma newpoint_in_core {d : ForwardDart G} {v : V}
    (hv : P.expandedPoint B c v ∈ (fun z : ℂ => c•z) '' (P.chain d).trace)
    (htrace : (P.chain d).trace ⊆ closure S) : ¬v∈B ∧ Incident d v := by
  classical
  have hvB : ¬v∈B := by
    intro h
    apply P.port_not_core hS h0 hport hc hc1 h
    simpa [expandedPoint,h] using Set.image_mono htrace hv
  refine ⟨hvB,?_⟩
  obtain ⟨z,hz,he⟩ := hv
  have he' : z=P.point v := smul_right_injective ℂ hc.ne'
    (by simpa [expandedPoint,hvB] using he)
  exact P.on_vertex d v (he' ▸ hz)

lemma expandedRegion_vertex {d : ForwardDart G} {v : V}
    (htrace : (P.chain d).trace ⊆ closure S)
    (hv : P.expandedPoint B c v ∈ P.expandedRegion B c d) : Incident d v := by
  rcases hv with hv | hv
  · exact (P.newpoint_in_core hS h0 hport hc hc1 hv htrace).2
  · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hv
    have he := P.newpoint_in_tail hS h0 hpoint hport hc hc1 w.property.1 hw
    exact he ▸ w.property.2


variable (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
  (hleaf : ∀ v ∈ B, ∀ a b, G.Adj v a → G.Adj v b → a=b)
include htrace hleaf

omit hpoint in
lemma different_core_tail {d e : ForwardDart G} (hde : d≠e)
    {v : V} (hv : v∈B) (he : Incident e v) :
    Disjoint ((fun z : ℂ => c•z) '' (P.chain d).trace) (P.portTail c v) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨w,hw,rfl⟩ := hz
  have heq := convex_frontier_tail_core hS h0 (hport v hv) hc hc1.le hz'
    ⟨w,htrace d hw,rfl⟩
  have hwv : w=P.point v := smul_right_injective ℂ hc.ne' heq
  have hd : Incident d v := P.on_vertex d v (hwv ▸ hw)
  exact hde (leaf_incident_unique hleaf hv hd he)

omit hpoint htrace in
lemma different_tails {d e : ForwardDart G} (hde : d≠e)
    {v w : V} (hv : v∈B) (hw : w∈B) (hd : Incident d v) (he : Incident e w) :
    Disjoint (P.portTail c v) (P.portTail c w) := by
  apply convex_frontier_tails_disjoint hS h0 (hport v hv) (hport w hw) _ hc hc1.le
  intro h
  have hvw := P.point_injective h
  exact hde (leaf_incident_unique hleaf hv hd (hvw.symm ▸ he))

omit hpoint in
lemma expandedRegions_intersect {d e : ForwardDart G} (hde : d≠e)
    {z : ℂ} (hz : z∈P.expandedRegion B c d) (hz' : z∈P.expandedRegion B c e) :
    (z=P.expandedPoint B c d.val.fst ∨ z=P.expandedPoint B c d.val.snd) ∧
    (z=P.expandedPoint B c e.val.fst ∨ z=P.expandedPoint B c e.val.snd) := by
  classical
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · obtain ⟨w,hw,rfl⟩ := hz
    obtain ⟨w',hw',heq⟩ := hz'
    have heww : w'=w := smul_right_injective ℂ hc.ne' heq
    subst w'
    have hint := P.intersect d e hde w hw hw'
    have hnB (v : V) (h : w=P.point v) : v∉B := by
      intro hv
      exact hde (leaf_incident_unique hleaf hv (P.on_vertex d v (h ▸ hw))
        (P.on_vertex e v (h ▸ hw')))
    constructor
    · rcases hint.1 with hd | hd
      · exact Or.inl (by simp [expandedPoint,hnB _ hd,hd])
      · exact Or.inr (by simp [expandedPoint,hnB _ hd,hd])
    · rcases hint.2 with he | he
      · exact Or.inl (by simp [expandedPoint,hnB _ he,he])
      · exact Or.inr (by simp [expandedPoint,hnB _ he,he])
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz'
    exact False.elim (Set.disjoint_left.mp
      (P.different_core_tail hS h0 hport hc hc1 htrace hleaf hde v.property.1 v.property.2) hz hv)
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    exact False.elim (Set.disjoint_left.mp
      (P.different_core_tail hS h0 hport hc hc1 htrace hleaf hde.symm v.property.1 v.property.2) hz' hv)
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hz'
    exact False.elim (Set.disjoint_left.mp
      (P.different_tails hS h0 hport hc hc1 hleaf hde
        v.property.1 w.property.1 v.property.2 w.property.2) hv hw)

end PLDrawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_TreeDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Real

lemma exteriorToDisk_injective : Function.Injective exteriorToDisk := by
  intro z w h
  exact inv_injective (star_injective h)

lemma exteriorToDisk_circle (a : ℝ) : exteriorToDisk (Circle.exp a : ℂ) = Circle.exp a := by
  change star ((Circle.exp a : ℂ)⁻¹) = _
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  exact star_star _

lemma exteriorToDisk_norm {z : ℂ} (hz : 1 ≤ ‖z‖) : ‖exteriorToDisk z‖ ≤ 1 := by
  simp only [exteriorToDisk, norm_star, norm_inv]
  exact inv_le_one_of_one_le₀ hz

lemma exteriorToDisk_continuous_path {a b : ℂ} (p : Path a b)
    (hp : ∀ t, 1 ≤ ‖p t‖) : Continuous (fun t => exteriorToDisk (p t)) := by
  apply Continuous.star
  exact p.continuous.inv₀ (fun t => by
    intro h
    have := hp t
    norm_num [h] at this)

/-- The corresponding crossing theorem in the exterior of the unit disk.
Inversion fixes every endpoint and is injective; no simplicity assumption
on the two paths is needed. -/
lemma exterior_cyclic_arcs_meet (a₀ a₁ a₂ a₃ : ℝ)
    (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃)
    (hspan : a₃ < a₀ + 2 * π)
    (f : Path (Circle.exp a₀ : ℂ) (Circle.exp a₂ : ℂ))
    (g : Path (Circle.exp a₁ : ℂ) (Circle.exp a₃ : ℂ))
    (hf : ∀ s, 1 ≤ ‖f s‖) (hg : ∀ s, 1 ≤ ‖g s‖) :
    ∃ s t, f s = g t := by
  let F : Path (Circle.exp a₀ : ℂ) (Circle.exp a₂ : ℂ) :=
    ⟨⟨fun s => exteriorToDisk (f s), exteriorToDisk_continuous_path f hf⟩,
      by change exteriorToDisk (f 0) = _; rw [f.source, exteriorToDisk_circle], by change exteriorToDisk (f 1) = _; rw [f.target, exteriorToDisk_circle]⟩
  let G : Path (Circle.exp a₁ : ℂ) (Circle.exp a₃ : ℂ) :=
    ⟨⟨fun s => exteriorToDisk (g s), exteriorToDisk_continuous_path g hg⟩,
      by change exteriorToDisk (g 0) = _; rw [g.source, exteriorToDisk_circle], by change exteriorToDisk (g 1) = _; rw [g.target, exteriorToDisk_circle]⟩
  obtain ⟨s,t,h⟩ := disk_cyclic_arcs_meet a₀ a₁ a₂ a₃ h₀₁ h₁₂ h₂₃ hspan F G
    (fun s => exteriorToDisk_norm (hf s)) (fun t => exteriorToDisk_norm (hg t))
  exact ⟨s,t,exteriorToDisk_injective h⟩


/-- Mutually disjoint exterior paths imply the literal noncrossing relation
on the finite cyclic list of their boundary ports. -/
lemma noncrossing_of_exterior_arcs {n : ℕ} (G : SimpleGraph (Fin n))
    (angle : Fin n → ℝ) (horder : StrictMono angle)
    (hspan : ∀ i j, angle j - angle i < 2 * π)
    (arc : ∀ i j, G.Adj i j → Path (Circle.exp (angle i) : ℂ)
      (Circle.exp (angle j) : ℂ))
    (hout : ∀ i j h t, 1 ≤ ‖arc i j h t‖)
    (hdisjoint : ∀ i j h k l h', i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    PlanarL1.ColumnOrder.Noncrossing G := by
  intro a b c d hab hbc hcd h
  obtain ⟨s,t,hst⟩ := exterior_cyclic_arcs_meet
    (angle a) (angle b) (angle c) (angle d)
    (horder hab) (horder hbc) (horder hcd) (by linarith [hspan a d])
    (arc a c h.1) (arc b d h.2) (hout a c h.1) (hout b d h.2)
  have hd := hdisjoint a c h.1 b d h.2 (ne_of_lt hab)
    (ne_of_lt (hab.trans (hbc.trans hcd))) (ne_of_gt hbc) (ne_of_lt hcd)
  exact Set.disjoint_left.mp hd (Set.mem_range_self s) (hst ▸ Set.mem_range_self t)

lemma circle_exp_arg {z : ℂ} (hz : ‖z‖ = 1) : (Circle.exp (Complex.arg z) : ℂ) = z := by
  simpa only [Circle.coe_exp, hz, Complex.ofReal_one, one_mul]
    using Complex.norm_mul_exp_arg_mul_I z

/-- A finite collection of distinct boundary ports supplies a cyclic list;
angles in a single half-open turn handle the wrap-around without choosing a
port as a special zero-angle endpoint. -/
lemma finite_port_order {V : Type} [Fintype V] (port : V → ℂ)
    (hnorm : ∀ v, ‖port v‖ = 1) (hinj : Function.Injective port) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      StrictMono (fun i => Complex.arg (port (e i))) ∧
      (∀ i j, Complex.arg (port (e j)) - Complex.arg (port (e i)) < 2 * π) := by
  classical
  have ha : Function.Injective (fun v => Complex.arg (port v)) := by
    intro a b hab
    apply hinj
    exact (circle_exp_arg (hnorm a)).symm.trans
      ((congrArg (fun t => (Circle.exp t : ℂ)) hab).trans (circle_exp_arg (hnorm b)))
  let : LinearOrder V := LinearOrder.lift' (fun v => Complex.arg (port v)) ha
  let e := monoEquivOfFin V rfl
  refine ⟨e.toEquiv, ?_, ?_⟩
  · exact e.strictMono
  · intro i j
    change Complex.arg (port (e j)) - Complex.arg (port (e i)) < 2 * π
    linarith [Complex.arg_le_pi (port (e j)), Complex.neg_pi_lt_arg (port (e i))]

end PlanarL1.Topology




namespace PlanarL1.Columns
attribute [local instance] Classical.propDecidable

/-- An interval of selected consecutive indices is connected without using the
wrap-around edge. -/
lemma interval_reachable {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n))
    (he : ∀ i j, i.val+1=j.val → i∈S → j∈S → G.Adj i j)
    {i j : Fin n} (hij : i≤j) (hS : ∀ k, i≤k → k≤j → k∈S) :
    G.Reachable i j := by
  have go (m : ℕ) : ∀ j : Fin n, j.val-i.val=m → i≤j →
      (∀ k, i≤k → k≤j → k∈S) → G.Reachable i j := by
    induction m with
    | zero =>
      intro j hm hij _
      have : i=j := Fin.ext (by omega)
      subst j
      exact .rfl
    | succ m ih =>
      intro j hm hij hS
      have hj : 0<j.val := by omega
      let k : Fin n := ⟨j.val-1,by omega⟩
      have hik : i≤k := by change i.val≤j.val-1; omega
      have hkj : k≤j := by change j.val-1≤j.val; omega
      have hmk : k.val-i.val=m := by dsimp [k]; omega
      exact (ih k hmk hik (fun a ha hb => hS a ha (hb.trans hkj))).trans
        ((he k j (by dsimp [k]; omega) (hS k hik hkj) (hS j hij le_rfl)).reachable)
  exact go _ j rfl hij hS

/-- The elementary circular-interval criterion: if a set and its complement
have no alternating four indices, consecutive selected indices connect it. -/
lemma consecutive_connected {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n))
    (he : ∀ i j, i≠j → Consecutive i j → i∈S → j∈S → G.Adj i j)
    (halt : ∀ a b c d : Fin n, a<b → b < c → c<d →
      ¬((a∈S ∧ b∉S ∧ c∈S ∧ d∉S) ∨ (a∉S ∧ b∈S ∧ c∉S ∧ d∈S)))
    {i j : Fin n} (hi : i∈S) (hj : j∈S) : G.Reachable i j := by
  have edge : ∀ a b : Fin n, a.val+1=b.val → a∈S → b∈S → G.Adj a b := by
    intro a b hab ha hb
    exact he a b (fun h => by subst b; omega) (Or.inl hab) ha hb
  suffices h : ∀ a b : Fin n, a≤b → a∈S → b∈S → G.Reachable a b by
    rcases le_total i j with hij | hji
    · exact h i j hij hi hj
    · exact (h j i hji hj hi).symm
  intro a b hab ha hb
  by_cases hwhole : ∀ k, a≤k → k≤b → k∈S
  · exact interval_reachable G S edge hab hwhole
  push Not at hwhole
  obtain ⟨k,hak,hkb,hk⟩ := hwhole
  have hak' : a<k := lt_of_le_of_ne hak (fun h => hk (h ▸ ha))
  have hkb' : k<b := lt_of_le_of_ne hkb (fun h => hk (h.symm ▸ hb))
  have hlow (t : Fin n) (ht : t≤a) : t∈S := by
    by_contra hn
    have hta : t<a := lt_of_le_of_ne ht (fun h => hn (h.symm ▸ ha))
    exact halt t a k b hta hak' hkb' (Or.inr ⟨hn,ha,hk,hb⟩)
  have hhigh (t : Fin n) (ht : b≤t) : t∈S := by
    by_contra hn
    have hbt : b<t := lt_of_le_of_ne ht (fun h => hn (h ▸ hb))
    exact halt a k b t hak' hkb' hbt (Or.inl ⟨ha,hk,hb,hn⟩)
  let first : Fin n := ⟨0,by have := a.isLt; omega⟩
  let last : Fin n := ⟨n-1,by have := a.isLt; omega⟩
  have hfa : first≤a := by change 0≤a.val; omega
  have hbl : b≤last := by change b.val≤n-1; omega
  have hleft := interval_reachable G S edge hfa (fun t _ ht => hlow t ht)
  have hright := interval_reachable G S edge hbl (fun t ht _ => hhigh t ht)
  have hwrap : G.Reachable first last := by
    by_cases hfl : first=last
    · rw [hfl]
    · apply SimpleGraph.Adj.reachable
      apply he first last hfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl,by dsimp [last]; omega⟩))
      · exact hlow first hfa
      · exact hhigh last hbl
  exact (hleft.symm.trans hwrap).trans hright.symm

end PlanarL1.Columns



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Surgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma small_homothety_subset {S U : Set E} (hS : Bornology.IsBounded S)
    (hU : U ∈ nhds (0:E)) :
    ∃ c : ℝ, 0 < c ∧ c<1 ∧ (fun x : E => c•x) '' S ⊆ U := by
  obtain ⟨R,hR,hbound⟩ := hS.exists_pos_norm_le
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  let c := min (1/2:ℝ) (ε/(2*R))
  have hc : 0 < c := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hR))
  have hc1 : c<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨c,hc,hc1,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  apply hball
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hcr : c*R ≤ ε/2 := by
    calc c*R ≤ (ε/(2*R))*R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
         _ = ε/2 := by field_simp
  calc c*‖x‖ ≤ c*R := mul_le_mul_of_nonneg_left (hbound x hx) hc.le
       _ ≤ ε/2 := hcr
       _ < ε := by linarith

/-- The radial exit from a convex neighbourhood. Both portions of the original
segment are controlled; this is the actual cut used in a disk surgery. -/
lemma convex_radial_cut {S : Set E} (hS : Convex ℝ S) (h0 : S ∈ nhds (0:E))
    {p : E} (hp : p ∉ closure S) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ t•p ∈ frontier S ∧
      (∀ s : ℝ, 0 ≤ s → s < t → s • p ∈ interior S) ∧
      (∀ s : ℝ, t < s → s • p ∉ closure S) := by
  have hg : 1<gauge S p := lt_of_not_ge (fun h => hp ((gauge_le_one_iff_mem_closure hS h0).mp h))
  let t := (gauge S p)⁻¹
  have ht : 0<t := inv_pos.mpr (lt_trans zero_lt_one hg)
  have ht1 : t<1 := (inv_lt_one₀ (lt_trans zero_lt_one hg)).mpr hg
  have he : t*gauge S p=1 := inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hg))
  refine ⟨t,ht,ht1,?_,?_,?_⟩
  · apply (gauge_eq_one_iff_mem_frontier hS h0).mp
    simpa only [gauge_smul_of_nonneg ht.le,smul_eq_mul] using he
  · intro s hs hst
    apply (gauge_lt_one_iff_mem_interior hS h0).mp
    rw [gauge_smul_of_nonneg hs,smul_eq_mul,← he]
    exact mul_lt_mul_of_pos_right hst (lt_trans zero_lt_one hg)
  · intro s hst hs
    have hs0 : 0 ≤ s := le_of_lt (lt_trans ht hst)
    have hs' := (gauge_le_one_iff_mem_closure hS h0).mpr hs
    rw [gauge_smul_of_nonneg hs0,smul_eq_mul,← he] at hs'
    exact (mul_lt_mul_of_pos_right hst (lt_trans zero_lt_one hg)).not_ge hs'

end PlanarL1.Topology

namespace PlanarL1.Topology.PLDrawing
open Set Metric Filter
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

/-- Polygonal edge regions with exactly the prescribed intersections give a
literal simple polyline drawing, by finite loop erasure inside each region. -/
lemma ofRegions (p : V → ℂ) (hp : Function.Injective p)
    (R : ForwardDart G → Set ℂ)
    (hmem : ∀ d, p d.val.fst ∈ R d)
    (hjoin : ∀ d, PolygonallyJoined (R d) (p d.val.fst) (p d.val.snd))
    (hvertex : ∀ d v, p v ∈ R d → Incident d v)
    (hinter : ∀ d e, d≠e → ∀ z, z∈R d → z∈R e →
      (z=p d.val.fst ∨ z=p d.val.snd) ∧ (z=p e.val.fst ∨ z=p e.val.snd)) :
    ∃ Q : PLDrawing G, Q.point=p ∧ ∀ d, (Q.chain d).trace ⊆ R d := by
  classical
  choose n C hC using fun d => (hjoin d).exists_simple_segmentChain
  refine ⟨⟨p,hp,n,fun d => (C d).mapSet (Set.subset_univ _),
    fun d => (C d).mapSet_simple _ (hC d),?_,?_⟩,rfl,?_⟩
  · intro d v hv
    exact hvertex d v ((C d).trace_subset (hmem d) hv)
  · intro d e hde z hz hz'
    exact hinter d e hde z ((C d).trace_subset (hmem d) hz)
      ((C e).trace_subset (hmem e) hz')
  · intro d
    exact (C d).trace_subset (hmem d)

variable (P : PLDrawing G)

variable {S : Set ℂ} (hS : Convex ℝ S) (h0 : S ∈ nhds (0:ℂ))
  (hpoint : ∀ v, P.point v ∈ closure S)
  {B : Set V} (hport : ∀ v ∈ B, P.point v ∈ frontier S)
  {c : ℝ} (hc : 0 < c) (hc1 : c<1) {t : V → ℝ}
  (ht : ∀ v∈B, c<t v ∧ t v≤1)

include hc hc1 ht
omit hc in
lemma radial_segment_subset {v : V} (hv : v∈B) :
    segment ℝ (c•P.point v) (t v•P.point v) ⊆ P.portTail c v := by
  change segment ℝ (c•P.point v) (t v•P.point v) ⊆ segment ℝ (c•P.point v) (P.point v)
  apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
  rw [segment_eq_image' ℝ]
  refine ⟨(t v-c)/(1-c),⟨div_nonneg (sub_nonneg.mpr (ht v hv).1.le) (sub_nonneg.mpr hc1.le),?_⟩,?_⟩
  · exact (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [(ht v hv).2])
  · dsimp only
    have he : c+(t v-c)/(1-c)*(1-c)=t v := by field_simp [ne_of_gt (sub_pos.mpr hc1)]; ring
    calc c•P.point v+((t v-c)/(1-c))•(P.point v-c•P.point v)
          = (c+(t v-c)/(1-c)*(1-c))•P.point v := by module
         _ = t v•P.point v := by rw [he]

omit hc in
lemma radialRegion_subset (d : ForwardDart G) :
    P.radialRegion B c t d ⊆ P.expandedRegion B c d := by
  rintro z (hz | hz)
  · exact Or.inl hz
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨v,P.radial_segment_subset hc1 ht v.property.1 hv⟩)

include hS h0 hport
omit hc1 in
lemma radial_port_not_core {v : V} (hv : v∈B) :
    t v•P.point v ∉ (fun z : ℂ => c•z) '' closure S := by
  rintro ⟨z,hz,he⟩
  have hg := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg hc.le,gauge_smul_of_nonneg (hc.le.trans (ht v hv).1.le),
    (gauge_eq_one_iff_mem_frontier hS h0).mpr (hport v hv)] at hg
  have hz' := (gauge_le_one_iff_mem_closure hS h0).mpr hz
  simp only [smul_eq_mul,mul_one] at hg
  nlinarith [(ht v hv).1]

include hpoint
omit hc1 in
lemma radialPoint_injective : Function.Injective (P.radialPoint B c t) := by
  classical
  intro v w he
  by_cases hv : v∈B <;> by_cases hw : w∈B
  · apply P.point_injective
    exact (convex_frontier_radial_injective hS h0 (hport v hv) (hport w hw)
      (hc.trans (ht v hv).1) (hc.trans (ht w hw).1)
      (by simpa only [radialPoint,ite_eq_left hv,ite_eq_left hw] using he)).2
  · exfalso
    apply P.radial_port_not_core hS h0 hport hc ht hv
    exact ⟨P.point w,hpoint w,by simpa only [radialPoint,ite_eq_left hv,ite_eq_right hw] using he.symm⟩
  · exfalso
    apply P.radial_port_not_core hS h0 hport hc ht hw
    exact ⟨P.point v,hpoint v,by simpa only [radialPoint,ite_eq_right hv,ite_eq_left hw] using he⟩
  · apply P.point_injective
    exact smul_right_injective ℂ hc.ne' (by simpa only [radialPoint,ite_eq_right hv,ite_eq_right hw] using he)

lemma radialPoint_in_tail {v w : V} (hw : w∈B)
    (h : P.radialPoint B c t v ∈ P.portTail c w) : v=w := by
  classical
  by_cases hv : v∈B
  · by_contra hne
    have hd := convex_frontier_tails_disjoint hS h0 (hport v hv) (hport w hw)
      (fun h => hne (P.point_injective h)) hc hc1.le
    exact Set.disjoint_left.mp hd
      (P.radial_segment_subset hc1 ht hv (right_mem_segment ℝ _ _))
      (by simpa only [radialPoint,ite_eq_left hv,portTail] using h)
  · apply P.point_injective
    apply smul_right_injective ℂ hc.ne'
    exact convex_frontier_tail_core hS h0 (hport w hw) hc hc1.le
      (by simpa only [radialPoint,ite_eq_right hv,portTail] using h) ⟨P.point v,hpoint v,rfl⟩

variable (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
include htrace
lemma radialRegion_vertex {d : ForwardDart G} {v : V}
    (hv : P.radialPoint B c t v ∈ P.radialRegion B c t d) : Incident d v := by
  classical
  rcases hv with hv | hv
  · have hvB : v∉B := by
      intro hvB
      apply P.radial_port_not_core hS h0 hport hc ht hvB
      simpa only [radialPoint,ite_eq_left hvB] using Set.image_mono (htrace d) hv
    obtain ⟨z,hz,he⟩ := hv
    have he' : z=P.point v := smul_right_injective ℂ hc.ne'
      (by simpa only [radialPoint,ite_eq_right hvB] using he)
    exact P.on_vertex d v (he' ▸ hz)
  · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hv
    have he := P.radialPoint_in_tail hS h0 hpoint hport hc hc1 ht w.property.1
      (P.radial_segment_subset hc1 ht w.property.1 hw)
    exact he ▸ w.property.2


variable (hleaf : ∀ v ∈ B, ∀ a b, G.Adj v a → G.Adj v b → a=b)
include hleaf
lemma radialRegions_intersect {d e : ForwardDart G} (hde : d≠e)
    {z : ℂ} (hz : z∈P.radialRegion B c t d) (hz' : z∈P.radialRegion B c t e) :
    (z=P.radialPoint B c t d.val.fst ∨ z=P.radialPoint B c t d.val.snd) ∧
    (z=P.radialPoint B c t e.val.fst ∨ z=P.radialPoint B c t e.val.snd) := by
  classical
  have hd := P.radialRegion_subset hc1 ht d hz
  have he := P.radialRegion_subset hc1 ht e hz'
  have hint := P.expandedRegions_intersect hS h0 hport hc hc1 htrace hleaf hde hd he
  have hnot (v : V) (hv : z=P.expandedPoint B c v) : v∉B := by
    intro hvB
    exact hde (leaf_incident_unique hleaf hvB
      (P.expandedRegion_vertex hS h0 hpoint hport hc hc1 (htrace d) (hv ▸ hd))
      (P.expandedRegion_vertex hS h0 hpoint hport hc hc1 (htrace e) (hv ▸ he)))
  have heq (v : V) (hv : z=P.expandedPoint B c v) : z=P.radialPoint B c t v := by
    simpa only [expandedPoint,radialPoint,ite_eq_right (hnot v hv)] using hv
  exact ⟨hint.1.imp (heq _) (heq _),hint.2.imp (heq _) (heq _)⟩

omit hS h0 hpoint hport hc hc1 ht htrace hleaf in
lemma radialPoint_mem_region {d : ForwardDart G} {v : V} (hv : Incident d v) :
    P.radialPoint B c t v ∈ P.radialRegion B c t d := by
  classical
  by_cases hvB : v∈B
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v,hvB,hv⟩,by
      simpa only [radialPoint,ite_eq_left hvB] using right_mem_segment ℝ (c•P.point v) (t v•P.point v)⟩)
  · apply Or.inl
    refine ⟨P.point v,?_,by simp only [radialPoint,ite_eq_right hvB]⟩
    rcases hv with rfl | rfl
    · exact (P.chain d).start_mem_trace
    · exact (P.chain d).finish_mem_trace

omit hS h0 hpoint hport hc hc1 ht htrace hleaf in
lemma radialRegion_joined (B : Set V) (c : ℝ) (t : V → ℝ) (d : ForwardDart G) :
    PolygonallyJoined (P.radialRegion B c t d)
      (P.radialPoint B c t d.val.fst) (P.radialPoint B c t d.val.snd) := by
  classical
  have hseg (v : V) (hv : Incident d v) :
      segment ℝ (c•P.point v) (P.radialPoint B c t v) ⊆ P.radialRegion B c t d := by
    by_cases hvB : v∈B
    · intro z hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v,hvB,hv⟩,by simpa only [radialPoint,ite_eq_left hvB] using hz⟩)
    · simp only [radialPoint,hvB,ite_false,segment_same]
      intro z hz
      have he : z=c•P.point v := hz
      subst z
      simpa only [radialPoint,ite_eq_right hvB] using P.radialPoint_mem_region (B:=B) (c:=c) (t:=t) hv
  have hfirst : PolygonallyJoined (P.radialRegion B c t d)
      (P.radialPoint B c t d.val.fst) (c•P.point d.val.fst) :=
    Relation.ReflTransGen.single (by rw [segment_symm]; exact hseg _ (Or.inl rfl))
  have hmiddle := ((P.chain d).joined_trace.smul c).mono
    (show (fun z : ℂ => c•z) '' (P.chain d).trace ⊆ P.radialRegion B c t d from fun _ h => Or.inl h)
  exact (hfirst.trans hmiddle).tail (hseg _ (Or.inr rfl))

/-- All leaf tails may be cut at different positive radial coordinates. The
result is an actual drawing, not merely a nonintersection promise. -/
lemma radial_leaf_ports : ∃ Q : PLDrawing G,
    Q.point=P.radialPoint B c t ∧ ∀ d, (Q.chain d).trace ⊆ P.radialRegion B c t d := by
  apply ofRegions (P.radialPoint B c t) (P.radialPoint_injective hS h0 hpoint hport hc ht)
    (P.radialRegion B c t)
  · intro d
    exact P.radialPoint_mem_region (Or.inl rfl)
  · exact P.radialRegion_joined B c t
  · intro d v hv
    exact P.radialRegion_vertex hS h0 hpoint hport hc hc1 ht htrace hv
  · intro d e hde z hz hz'
    exact P.radialRegions_intersect hS h0 hpoint hport hc hc1 ht htrace hleaf hde hz hz'

omit hS h0 hpoint hport hc hc1 ht htrace hleaf in
lemma radialRegion_subset_convex {U : Set ℂ} (hU : Convex ℝ U)
    (hcore : ∀ d, (fun z : ℂ => c•z) '' (P.chain d).trace ⊆ U)
    (hnew : ∀ v∈B, t v•P.point v ∈ U) (d : ForwardDart G) :
    P.radialRegion B c t d ⊆ U := by
  rintro z (hz | hz)
  · exact hcore d hz
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    apply hU.segment_subset ?_ (hnew v v.property.1) hv
    apply hcore d
    refine ⟨P.point v,?_,rfl⟩
    rcases v.property.2 with he | he
    · rw [he]; exact (P.chain d).start_mem_trace
    · rw [he]; exact (P.chain d).finish_mem_trace

end PlanarL1.Topology.PLDrawing




namespace PlanarL1.Topology
open Set Metric Filter

lemma PolygonallyJoined.symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {x y : E} (h : PolygonallyJoined S x y) : PolygonallyJoined S y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact (Relation.ReflTransGen.single (by rw [segment_symm]; exact hab)).trans ih

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

variable {v : V} {q : ℂ} {S : Set ℂ}
  (hleaf : ∀ a b, G.Adj v a → G.Adj v b → a=b)
  (hp : P.point v∈S) (hq : q∈S)
  (hvertex : ∀ w, P.point w∈S → w=v)
  (hcross : ∀ d z, z∈(P.chain d).trace → z∈S → z=P.point v)

include hq hvertex
lemma movedPoint_injective : Function.Injective (P.movedPoint v q) := by
  classical
  intro a b he
  by_cases ha : a=v <;> by_cases hb : b=v
  · exact ha.trans hb.symm
  · exfalso
    apply hb
    apply hvertex b
    have he' : q=P.point b := by simpa only [movedPoint,ite_eq_left ha,ite_eq_right hb] using he
    exact he' ▸ hq
  · exfalso
    apply ha
    apply hvertex a
    have he' : P.point a=q := by simpa only [movedPoint,ite_eq_right ha,ite_eq_left hb] using he
    exact he'.symm ▸ hq
  · apply P.point_injective
    simpa only [movedPoint,ite_eq_right ha,ite_eq_right hb] using he

include hcross
lemma movedRegion_vertex {d : ForwardDart G} {w : V}
    (hw : P.movedPoint v q w∈P.movedRegion v S d) : Incident d w := by
  classical
  by_cases he : w=v
  · subst w
    simp only [movedPoint,ite_true,movedRegion,Set.mem_union,Set.mem_ofPred_eq] at hw
    rcases hw with hw | hw
    · have h := hcross d q hw hq
      exact P.on_vertex d v (h ▸ hw)
    · exact hw.1
  · simp only [movedPoint,ite_eq_right he,movedRegion,Set.mem_union,Set.mem_ofPred_eq] at hw
    rcases hw with hw | hw
    · exact P.on_vertex d w hw
    · exact False.elim (he (hvertex w hw.2))

include hleaf
omit hq hvertex in
lemma movedRegions_intersect {d e : ForwardDart G} (hde : d≠e) {z : ℂ}
    (hz : z∈P.movedRegion v S d) (hz' : z∈P.movedRegion v S e) :
    (z=P.movedPoint v q d.val.fst ∨ z=P.movedPoint v q d.val.snd) ∧
    (z=P.movedPoint v q e.val.fst ∨ z=P.movedPoint v q e.val.snd) := by
  classical
  have huniq : ∀ {d e : ForwardDart G}, Incident d v → Incident e v → d=e := by
    intro d e hd he
    exact leaf_incident_unique (B:={v}) (by intro w hw; have : w=v := hw; simpa [this] using hleaf)
      rfl hd he
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · have hint := P.intersect d e hde z hz hz'
    have hne (w : V) (he : z=P.point w) : w≠v := by
      intro hw
      have hev : z=P.point v := he.trans (congrArg P.point hw)
      exact hde (huniq (P.on_vertex d v (hev ▸ hz)) (P.on_vertex e v (hev ▸ hz')))
    have heq (w : V) (he : z=P.point w) : z=P.movedPoint v q w := by
      simpa only [movedPoint,ite_eq_right (hne w he)] using he
    exact ⟨hint.1.imp (heq _) (heq _),hint.2.imp (heq _) (heq _)⟩
  · have he := hcross d z hz hz'.2
    exact False.elim (hde (huniq (P.on_vertex d v (he ▸ hz)) hz'.1))
  · have he := hcross e z hz' hz.2
    exact False.elim (hde (huniq hz.1 (P.on_vertex e v (he ▸ hz'))))
  · exact False.elim (hde (huniq hz.1 hz'.1))

omit hleaf hvertex hcross in
lemma movedPoint_mem_region {d : ForwardDart G} {w : V} (hw : Incident d w) :
    P.movedPoint v q w∈P.movedRegion v S d := by
  classical
  by_cases he : w=v
  · subst w
    exact Or.inr ⟨hw,by simpa [movedPoint] using hq⟩
  · apply Or.inl
    simpa only [movedPoint,ite_eq_right he] using
      (show P.point w∈(P.chain d).trace from by
        rcases hw with rfl | rfl
        · exact (P.chain d).start_mem_trace
        · exact (P.chain d).finish_mem_trace)


omit hleaf hq hvertex hcross in
lemma movedRegion_joined (hjoin : PolygonallyJoined S (P.point v) q) (d : ForwardDart G) :
    PolygonallyJoined (P.movedRegion v S d)
      (P.movedPoint v q d.val.fst) (P.movedPoint v q d.val.snd) := by
  classical
  have hroute (w : V) (hw : Incident d w) :
      PolygonallyJoined (P.movedRegion v S d) (P.point w) (P.movedPoint v q w) := by
    by_cases he : w=v
    · subst w
      simpa [movedPoint] using hjoin.mono
        (show S ⊆ P.movedRegion v S d from fun z hz => Or.inr ⟨hw,hz⟩)
    · simp only [movedPoint,ite_eq_right he]
      exact Relation.ReflTransGen.refl
  exact ((hroute _ (Or.inl rfl)).symm.trans
    ((P.chain d).joined_trace.mono (fun _ h => Or.inl h))).trans (hroute _ (Or.inr rfl))

/-- Extending a drawn leaf along a polygonal region disjoint from the rest of
the drawing preserves a literal polyline drawing and the exact vertices. -/
lemma move_leaf (hjoin : PolygonallyJoined S (P.point v) q) :
    ∃ Q : PLDrawing G, Q.point=P.movedPoint v q ∧
      ∀ d, (Q.chain d).trace ⊆ P.movedRegion v S d := by
  apply ofRegions (P.movedPoint v q) (P.movedPoint_injective hq hvertex) (P.movedRegion v S)
  · intro d
    exact P.movedPoint_mem_region hq (Or.inl rfl)
  · exact P.movedRegion_joined hjoin
  · intro d w hw
    exact P.movedRegion_vertex hq hvertex hcross hw
  · intro d e hde z hz hz'
    exact P.movedRegions_intersect hleaf hcross hde hz hz'

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma convex_segment_cut {S : Set E} (hS : Convex ℝ S) (hopen : IsOpen S)
    {a b : E} (ha : a∈S) (hb : b∉closure S) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ a+t•(b-a)∈frontier S ∧
      (∀ s : ℝ, 0 ≤ s → s < t → a+s•(b-a)∈S) ∧
      (∀ s : ℝ, t < s → a+s•(b-a)∉closure S) := by
  let T := (fun z : E => a+z) ⁻¹' S
  have hT : Convex ℝ T := hS.translate_preimage_right a
  have hop : IsOpen T := hopen.preimage (continuous_const.add continuous_id)
  have hzero : T∈nhds (0:E) := hop.mem_nhds (by simpa [T] using ha)
  have hcl : closure T=(fun z : E => a+z) ⁻¹' closure S :=
    ((Homeomorph.addLeft a).preimage_closure S).symm
  have hfr : frontier T=(fun z : E => a+z) ⁻¹' frontier S :=
    ((Homeomorph.addLeft a).preimage_frontier S).symm
  have hb' : b-a∉closure T := by simpa [hcl] using hb
  obtain ⟨t,ht,ht1,htfr,hin,hout⟩ := convex_radial_cut hT hzero hb'
  refine ⟨t,ht,ht1,?_,?_,?_⟩
  · simpa only [hfr,Set.mem_preimage] using htfr
  · intro s hs hst
    exact (show s•(b-a)∈T from interior_subset (hin s hs hst))
  · intro s hst hs
    apply hout s hst
    simpa only [hcl,Set.mem_preimage] using hs

lemma convex_frontier_segment {S : Set E} (hS : Convex ℝ S)
    (h0 : S∈nhds (0:E)) {p q : E} (hp : p∈frontier S) (hq : q∈frontier S)
    (hseg : q∈segment ℝ 0 p) : q=p := by
  rw [segment_eq_image' ℝ 0 p] at hseg
  obtain ⟨t,ht,he⟩ := hseg
  simp only [zero_add,sub_zero] at he
  have hg := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg ht.1,(gauge_eq_one_iff_mem_frontier hS h0).mpr hp,
    (gauge_eq_one_iff_mem_frontier hS h0).mpr hq] at hg
  simp only [smul_eq_mul,mul_one] at hg
  simpa only [hg,one_smul] using he.symm

/-- Radial cuts of all unselected ports, after a sufficiently small homothety
of the bounded old disk. The selected port stays in the interior of the new
disk; it will be extended along the next exterior straight piece. -/
lemma capsule_radial_data {ι : Type*} (p : ι → ℂ) {B : Set ι} {v : ι}
    {S T : Set ℂ} (hSbound : Bornology.IsBounded S)
    (hpoint : ∀ w, p w∈closure S)
    (hT : Convex ℝ T) (hTop : IsOpen T) (hT0 : (0:ℂ)∈T)
    (hout : ∀ w∈B, w≠v → p w∉closure T) :
    ∃ (c : ℝ) (t : ι → ℝ), 0 < c ∧ c<1 ∧
      (fun z : ℂ => c•z) '' closure S ⊆ T ∧ t v=1 ∧
      (∀ w∈B, c<t w ∧ t w≤1) ∧
      (∀ w∈B, w≠v → t w•p w∈frontier T) ∧
      (∀ w∈B, w≠v → ∀ s : ℝ, t w < s → s•p w∉closure T) := by
  classical
  obtain ⟨c,hc,hc1,hcore⟩ := small_homothety_subset hSbound.closure (hTop.mem_nhds hT0)
  let W := {w : ι // w∈B ∧ w≠v}
  have hcut (w : W) := convex_radial_cut hT (hTop.mem_nhds hT0) (hout w w.property.1 w.property.2)
  choose u hu hu1 huf hin hf using hcut
  let t (w : ι) := if h : w∈B ∧ w≠v then u ⟨w,h⟩ else 1
  have hct (w : W) : c<u w := by
    have hcT : c•p w∈interior T := by rw [hTop.interior_eq]; exact hcore ⟨p w,hpoint w,rfl⟩
    have hgc := (gauge_lt_one_iff_mem_interior hT (hTop.mem_nhds hT0)).mpr hcT
    have hgu := (gauge_eq_one_iff_mem_frontier hT (hTop.mem_nhds hT0)).mpr (huf w)
    rw [gauge_smul_of_nonneg hc.le,smul_eq_mul] at hgc
    rw [gauge_smul_of_nonneg (hu w).le,smul_eq_mul] at hgu
    have hgp : 1<gauge T (p w) := lt_of_not_ge (fun h =>
      hout w w.property.1 w.property.2 ((gauge_le_one_iff_mem_closure hT (hTop.mem_nhds hT0)).mp h))
    nlinarith
  refine ⟨c,t,hc,hc1,hcore,by simp [t],?_,?_,?_⟩
  · intro w hw
    by_cases he : w=v
    · subst w; simp only [t,ne_eq,not_true_eq_false,and_false,dite_false]; exact ⟨hc1,le_rfl⟩
    · have hwv : w∈B ∧ w≠v := ⟨hw,he⟩
      simpa only [t,dite_eq_left hwv] using
        (show c<u ⟨w,hwv⟩ ∧ u ⟨w,hwv⟩ ≤ 1 from ⟨hct ⟨w,hwv⟩,(hu1 ⟨w,hwv⟩).le⟩)
  · intro w hw he
    have hwv : w∈B ∧ w≠v := ⟨hw,he⟩
    simpa only [t,dite_eq_left hwv] using huf ⟨w,hwv⟩
  · intro w hw he s hs
    have hwv : w∈B ∧ w≠v := ⟨hw,he⟩
    exact hf ⟨w,hwv⟩ s (by simpa only [t,dite_eq_left hwv] using hs)

end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

lemma forward_endpoints (u v : V) (h : G.Adj u v) :
    ((forward u v h).val.fst=u ∧ (forward u v h).val.snd=v) ∨
    ((forward u v h).val.fst=v ∧ (forward u v h).val.snd=u) := by
  classical
  by_cases huv : u<v <;> simp [forward,huv]

lemma region_eq (u v : V) (h : G.Adj u v) :
    P.region u v=(P.chain (forward u v h)).trace := by simp [region,h]

lemma region_joined (u v : V) (h : G.Adj u v) :
    PolygonallyJoined (P.region u v) (P.point u) (P.point v) := by
  rw [P.region_eq u v h]
  rcases forward_endpoints u v h with he|he
  · simpa only [he.1,he.2] using (P.chain (forward u v h)).joined_trace
  · simpa only [he.1,he.2] using (P.chain (forward u v h)).joined_trace.symm

lemma region_start (u v : V) (h : G.Adj u v) : P.point u∈P.region u v := by
  rw [P.region_eq u v h]
  rcases forward_endpoints u v h with he|he
  · simpa only [(P.chain (forward u v h)).start,he.1] using (P.chain (forward u v h)).vertex_mem_trace 0 (Nat.zero_le _)
  · have hmem := (P.chain (forward u v h)).vertex_mem_trace (P.count (forward u v h)) le_rfl
    simpa only [(P.chain (forward u v h)).finish,he.2] using hmem

lemma region_vertex (u v : V) (h : G.Adj u v) (w : V) (hw : P.point w∈P.region u v) :
    w=u ∨ w=v := by
  rw [P.region_eq u v h] at hw
  have hh := P.on_vertex _ w hw
  rcases forward_endpoints u v h with he|he
  · simpa only [he.1,he.2] using hh
  · simpa only [he.1,he.2,or_comm] using hh

lemma region_intersect (u v w x : V) (huv : G.Adj u v) (hwx : G.Adj w x)
    (hne : ¬((u=w ∧ v=x) ∨ (u=x ∧ v=w))) {z : ℂ}
    (hz : z∈P.region u v) (hz' : z∈P.region w x) :
    (z=P.point u ∨ z=P.point v) ∧ (z=P.point w ∨ z=P.point x) := by
  rw [P.region_eq u v huv] at hz
  rw [P.region_eq w x hwx] at hz'
  have hfe : forward u v huv≠forward w x hwx := by
    intro he
    have h₁ := forward_endpoints u v huv
    rw [he] at h₁
    rcases h₁ with h₁|h₁ <;> rcases forward_endpoints w x hwx with h₂|h₂
    · exact hne (Or.inl ⟨h₁.1.symm.trans h₂.1,h₁.2.symm.trans h₂.2⟩)
    · exact hne (Or.inr ⟨h₁.1.symm.trans h₂.1,h₁.2.symm.trans h₂.2⟩)
    · exact hne (Or.inr ⟨h₁.2.symm.trans h₂.2,h₁.1.symm.trans h₂.1⟩)
    · exact hne (Or.inl ⟨h₁.2.symm.trans h₂.2,h₁.1.symm.trans h₂.1⟩)
  have hi := P.intersect _ _ hfe z hz hz'
  rcases forward_endpoints u v huv with h₁|h₁ <;>
    rcases forward_endpoints w x hwx with h₂|h₂ <;>
    simpa only [h₁.1,h₁.2,h₂.1,h₂.2,or_comm] using hi

lemma ofSymmetricRegions (p : V → ℂ) (hp : Function.Injective p)
    (R : V → V → Set ℂ)
    (hmem : ∀ u v, G.Adj u v → p u∈R u v)
    (hjoin : ∀ u v, G.Adj u v → PolygonallyJoined (R u v) (p u) (p v))
    (hvertex : ∀ u v, G.Adj u v → ∀ w, p w∈R u v → w=u ∨ w=v)
    (hinter : ∀ u v w x, G.Adj u v → G.Adj w x →
      ¬((u=w ∧ v=x) ∨ (u=x ∧ v=w)) → ∀ z, z∈R u v → z∈R w x →
      (z=p u ∨ z=p v) ∧ (z=p w ∨ z=p x)) :
    ∃ Q : PLDrawing G, Q.point=p ∧ ∀ d, (Q.chain d).trace ⊆ R d.val.fst d.val.snd := by
  apply ofRegions p hp (fun d => R d.val.fst d.val.snd)
  · intro d; exact hmem _ _ d.val.adj
  · intro d; exact hjoin _ _ d.val.adj
  · intro d w hw; exact hvertex _ _ d.val.adj w hw
  · intro d e hde z hz hz'
    exact hinter _ _ _ _ d.val.adj e.val.adj
      (fun he => hde (ForwardDart.eq_of_endpoints d e he)) z hz hz'

end PLDrawing

namespace PLDrawing
variable {V W : Type} [LinearOrder V] [LinearOrder W] [LinearOrder (V⊕W)] {G : SimpleGraph V}
variable (P : PLDrawing G) (v : V) (q : W → ℂ) (A : W → Set ℂ)

/-- A finite star of genuinely disjoint polygonal arms can be attached at an
existing vertex while retaining every old vertex and edge region. -/
lemma attachLeaves
    (hq : ∀ w, q w≠P.point v)
    (hstart : ∀ w, P.point v∈A w) (hend : ∀ w, q w∈A w)
    (hjoin : ∀ w, PolygonallyJoined (A w) (P.point v) (q w))
    (hvertex : ∀ w u, P.point u∈A w → u=v)
    (hdisj : ∀ w w', w≠w' → ∀ z, z∈A w → z∈A w' → z=P.point v)
    (hold : ∀ w u x, G.Adj u x → ∀ z, z∈A w → z∈P.region u x → z=P.point v) :
    ∃ Q : PLDrawing (leafExtension (W := W) G v), Q.point=P.starPoint q ∧
      ∀ d, (Q.chain d).trace ⊆ P.starRegion A d.val.fst d.val.snd := by
  have hqold (w : W) (u : V) : q w≠P.point u := by
    intro he
    have hue : u=v := hvertex w u (he ▸ hend w)
    exact hq w (he.trans (congrArg P.point hue))
  have hqq : Function.Injective q := by
    intro w w' he
    by_contra hn
    exact hq w (hdisj w w' hn (q w) (hend w) (he ▸ hend w'))
  have hp : Function.Injective (P.starPoint q) := by
    intro x y he
    cases x with
    | inl x => cases y with
      | inl y => exact congrArg Sum.inl (P.point_injective he)
      | inr y => exact False.elim (hqold y x he.symm)
    | inr x => cases y with
      | inl y => exact False.elim (hqold x y he)
      | inr y => exact congrArg Sum.inr (hqq he)
  apply ofSymmetricRegions (P.starPoint q) hp (P.starRegion A)
  · intro x y hxy
    cases x with
    | inl x => cases y with
      | inl y => exact P.region_start x y hxy
      | inr y => have he : x=v := hxy; subst x; exact hstart y
    | inr x => cases y with
      | inl y => exact hend x
      | inr y => exact False.elim hxy
  · intro x y hxy
    cases x with
    | inl x => cases y with
      | inl y => exact P.region_joined x y hxy
      | inr y => have he : x=v := hxy; subst x; exact hjoin y
    | inr x => cases y with
      | inl y => have he : y=v := hxy; subst y; exact (hjoin x).symm
      | inr y => exact False.elim hxy
  · intro x y hxy z hz
    cases x with
    | inl x => cases y with
      | inl y =>
        cases z with
        | inl z => exact (P.region_vertex x y hxy z hz).imp (congrArg Sum.inl) (congrArg Sum.inl)
        | inr z =>
          exact False.elim (hq z (hold z x y hxy (q z) (hend z) hz))
      | inr y =>
        have he : x=v := hxy
        cases z with
        | inl z => exact Or.inl (congrArg Sum.inl ((hvertex y z hz).trans he.symm))
        | inr z =>
          by_cases hez : z=y
          · exact Or.inr (congrArg Sum.inr hez)
          · exact False.elim (hq z (hdisj z y hez (q z) (hend z) hz))
    | inr x => cases y with
      | inl y =>
        have he : y=v := hxy
        cases z with
        | inl z => exact Or.inr (congrArg Sum.inl ((hvertex x z hz).trans he.symm))
        | inr z =>
          by_cases hez : z=x
          · exact Or.inl (congrArg Sum.inr hez)
          · exact False.elim (hq z (hdisj z x hez (q z) (hend z) hz))
      | inr y => exact False.elim hxy
  · intro x y z t hxy hzt hne a ha hb
    cases x <;> cases y <;> cases z <;> cases t <;>
      simp only [leafExtension] at hxy hzt <;> try contradiction
    case inl.inl.inl.inl x y z t =>
      exact P.region_intersect x y z t hxy hzt (by simpa using hne) ha hb
    case inl.inl.inl.inr x y z t =>
      subst z
      have he := hold t x y hxy a hb ha
      subst a
      exact ⟨(P.region_vertex x y hxy v ha).imp (congrArg P.point) (congrArg P.point),Or.inl rfl⟩
    case inl.inl.inr.inl x y z t =>
      subst t
      have he := hold z x y hxy a hb ha
      subst a
      exact ⟨(P.region_vertex x y hxy v ha).imp (congrArg P.point) (congrArg P.point),Or.inr rfl⟩
    case inl.inr.inl.inl x y z t =>
      subst x
      have he := hold y z t hzt a ha hb
      subst a
      exact ⟨Or.inl rfl,(P.region_vertex z t hzt v hb).imp (congrArg P.point) (congrArg P.point)⟩
    case inr.inl.inl.inl x y z t =>
      subst y
      have he := hold x z t hzt a ha hb
      subst a
      exact ⟨Or.inr rfl,(P.region_vertex z t hzt v hb).imp (congrArg P.point) (congrArg P.point)⟩
    case inl.inr.inl.inr x y z t =>
      subst x; subst z
      have hyt : y≠t := by intro he; subst t; exact hne (Or.inl ⟨rfl,rfl⟩)
      rw [hdisj y t hyt a ha hb]
      exact ⟨Or.inl rfl,Or.inl rfl⟩
    case inl.inr.inr.inl x y z t =>
      subst x; subst t
      have hyz : y≠z := by intro he; subst z; exact hne (Or.inr ⟨rfl,rfl⟩)
      rw [hdisj y z hyz a ha hb]
      exact ⟨Or.inl rfl,Or.inr rfl⟩
    case inr.inl.inl.inr x y z t =>
      subst y; subst z
      have hxt : x≠t := by intro he; subst t; exact hne (Or.inr ⟨rfl,rfl⟩)
      rw [hdisj x t hxt a ha hb]
      exact ⟨Or.inr rfl,Or.inl rfl⟩
    case inr.inl.inr.inl x y z t =>
      subst y; subst t
      have hxz : x≠z := by intro he; subst z; exact hne (Or.inl ⟨rfl,rfl⟩)
      rw [hdisj x z hxz a ha hb]
      exact ⟨Or.inr rfl,Or.inr rfl⟩

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

lemma trace_compact : IsCompact P.trace := by
  apply isCompact_singleton.union
  apply isCompact_iUnion
  intro i
  rw [segment_eq_image' ℝ]
  exact isCompact_Icc.image (by fun_prop)

end SegmentChain

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

lemma affine_point (f : ℂ ≃ᵃ[ℝ] ℂ) (v : V) : (P.affine f).point v=f (P.point v) := rfl
lemma affine_trace (f : ℂ ≃ᵃ[ℝ] ℂ) (d : ForwardDart G) :
    ((P.affine f).chain d).trace=f '' (P.chain d).trace := by
  exact (P.chain d).affine_trace f.toAffineMap

lemma region_compact (u v : V) : IsCompact (P.region u v) := by
  classical
  by_cases h : G.Adj u v
  · rw [P.region_eq u v h]; exact (P.chain _).trace_compact
  · simp only [region,dite_eq_right h]; exact isCompact_empty

end PLDrawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Retubing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

lemma scalar_segment (p : ℂ) {a b : ℝ} (hab : a≤b) {z : ℂ}
    (hz : z∈segment ℝ (a•p) (b•p)) :
    ∃ u∈Icc a b, z=u•p := by
  rw [segment_eq_image' ℝ] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  refine ⟨a+t*(b-a),⟨by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab)],
    by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]⟩,?_⟩
  module

lemma radial_outer_tail {S : Set ℂ} {p : ℂ} {t : ℝ} (ht : t≤1)
    (hout : ∀ s : ℝ, t < s → s•p∉closure S)
    {z : ℂ} (hz : z∈segment ℝ (t•p) p) (hzS : z∈closure S) : z=t•p := by
  obtain ⟨s,hs,he⟩ := scalar_segment p ht (by simpa only [one_smul] using hz)
  have hst : s=t := le_antisymm (le_of_not_gt (fun h => hout s h (he ▸ hzS))) hs.1
  simpa only [hst] using he

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

/-- Compress a genuine finite drawing into a new convex tube and extend one
leaf along a segment external to the old disk. Every other exposed leaf is
cut exactly at the new frontier. The exterior residual tails meet the new
closed disk only at their new ports. -/
lemma retube_extend {S T : Set ℂ} {B : Set V} {v : V} {q : ℂ}
    (hS : Convex ℝ S) (hS0 : S∈nhds (0:ℂ)) (hSb : Bornology.IsBounded S)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (hport : ∀ w∈B, P.point w∈frontier S)
    (hleaf : ∀ w∈B, ∀ a b, G.Adj w a → G.Adj w b → a=b)
    (hv : v∈B) (hT : Convex ℝ T) (hTop : IsOpen T) (hT0 : (0:ℂ)∈T)
    (hTv : P.point v∈T) (hqT : q∈closure T)
    (hout : ∀ w∈B, w≠v → P.point w∉closure T)
    (hext : ∀ z, z∈segment ℝ (P.point v) q → z∈closure S → z=P.point v) :
    ∃ (c : ℝ) (t : V → ℝ) (Q : PLDrawing G), 0 < c ∧ c<1 ∧ t v=1 ∧
      (∀ w∈B, c<t w ∧ t w≤1) ∧ Q.point=P.retubePoint B c t v q ∧
      (∀ d, (Q.chain d).trace ⊆ P.retubeRegion B c t v q d) ∧
      (∀ d, (Q.chain d).trace ⊆ closure T) ∧
      (∀ w, Q.point w∈closure T) ∧
      (∀ w∈B, w≠v → Q.point w∈frontier T) ∧
      (∀ w∈B, w≠v → ∀ z, z∈segment ℝ (Q.point w) (P.point w) →
        z∈closure T → z=Q.point w) := by
  classical
  obtain ⟨c,t,hc,hc1,hcore,htv,ht,hfront,htail⟩ :=
    capsule_radial_data P.point hSb hpoint hT hTop hT0 hout
  obtain ⟨R,hRp,hR⟩ := P.radial_leaf_ports hS hS0 hpoint hport hc hc1 ht htrace hleaf
  have hRpoint (w : V) : R.point w=P.radialPoint B c t w := congrFun hRp w
  have hRpv : R.point v=P.point v := by
    rw [hRpoint]; simp only [radialPoint,ite_eq_left hv,htv,one_smul]
  have hRsubset (d : ForwardDart G) : (R.chain d).trace ⊆ closure S := by
    apply (hR d).trans
    apply P.radialRegion_subset_convex hS.closure
    · intro e z hz
      obtain ⟨z,hz,rfl⟩ := hz
      have : c•z∈segment ℝ 0 z := by
        rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc.le,hc1.le⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (htrace e hz) this
    · intro w hw
      have : t w•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨t w,⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
  have hRpts (w : V) : R.point w∈closure S := by
    rw [hRpoint]; unfold radialPoint
    split_ifs with hw
    · have : t w•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨t w,⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
    · have : c•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc.le,hc1.le⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
  have hcross (d : ForwardDart G) (z : ℂ) (hz : z∈(R.chain d).trace)
      (hz' : z∈segment ℝ (P.point v) q) : z=R.point v :=
    (hext z hz' (hRsubset d hz)).trans hRpv.symm
  have hvertex (w : V) (hw : R.point w∈segment ℝ (P.point v) q) : w=v :=
    R.point_injective ((hext (R.point w) hw (hRpts w)).trans hRpv.symm)
  obtain ⟨Q,hQp,hQ⟩ := R.move_leaf (hleaf v hv)
    (right_mem_segment ℝ _ _)
    hvertex hcross (by rw [hRpv]; exact Relation.ReflTransGen.single (fun _ h => h))
  have hpQ : Q.point=P.retubePoint B c t v q := by
    rw [hQp]; funext w
    simp only [movedPoint,retubePoint,hRpoint]
  have hregQ (d : ForwardDart G) : (Q.chain d).trace ⊆ P.retubeRegion B c t v q d := by
    intro z hz
    rcases hQ d hz with hz|hz
    · exact Or.inl (hR d hz)
    · exact Or.inr hz
  have hregT (d : ForwardDart G) : P.radialRegion B c t d ⊆ closure T := by
    apply P.radialRegion_subset_convex hT.closure
    · intro e z hz
      exact subset_closure (hcore (Set.image_mono (htrace e) hz))
    · intro w hw
      by_cases he : w=v
      · subst w; simpa only [htv,one_smul] using subset_closure hTv
      · exact frontier_subset_closure (hfront w hw he)
  refine ⟨c,t,Q,hc,hc1,htv,ht,hpQ,hregQ,?_,?_,?_,?_⟩
  · intro d z hz
    rcases hregQ d hz with hz|hz
    · exact hregT d hz
    · exact hT.closure.segment_subset (subset_closure hTv) hqT hz.2
  · intro w
    rw [congrFun hpQ w]
    simp only [retubePoint,radialPoint]
    split_ifs with he hw
    · exact hqT
    · exact frontier_subset_closure (hfront w hw he)
    · exact subset_closure (hcore ⟨P.point w,hpoint w,rfl⟩)
  · intro w hw he
    rw [congrFun hpQ w]
    simpa only [retubePoint,ite_eq_right he,radialPoint,ite_eq_left hw] using hfront w hw he
  · intro w hw he z hz hzT
    have hpw : Q.point w=t w•P.point w := by
      rw [congrFun hpQ w]; simp only [retubePoint,ite_eq_right he,radialPoint,ite_eq_left hw]
    rw [hpw] at hz ⊢
    exact radial_outer_tail (ht w hw).2 (htail w hw he) hz hzT

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

lemma radialRegion_old {S : Set ℂ} {B : Set V} {c : ℝ} {t : V → ℝ}
    (hS : Convex ℝ S) (h0 : S∈nhds (0:ℂ)) (hc : 0 ≤ c) (hc1 : c≤1)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (ht : ∀ w∈B, 0≤t w ∧ t w≤1) (d : ForwardDart G) :
    P.radialRegion B c t d ⊆ closure S := by
  apply P.radialRegion_subset_convex hS.closure
  · intro e z hz
    obtain ⟨z,hz,rfl⟩ := hz
    have : c•z∈segment ℝ 0 z := by
      rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc,hc1⟩,by simp⟩
    exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds h0)) (htrace e hz) this
  · intro w hw
    have : t w•P.point w∈segment ℝ 0 (P.point w) := by
      rw [segment_eq_image' ℝ]; exact ⟨t w,ht w hw,by simp⟩
    exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds h0)) (hpoint w) this

lemma retube_controlled {S T : Set ℂ} {B : Set V} {v : V} {q : ℂ}
    (hS : Convex ℝ S) (hS0 : S∈nhds (0:ℂ)) (hSb : Bornology.IsBounded S)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (hport : ∀ w∈B, P.point w∈frontier S)
    (hleaf : ∀ w∈B, ∀ a b, G.Adj w a → G.Adj w b → a=b)
    (hv : v∈B) (hT : Convex ℝ T) (hTop : IsOpen T) (hT0 : (0:ℂ)∈T)
    (hTv : P.point v∈T) (hqT : q∈closure T)
    (hout : ∀ w∈B, w≠v → P.point w∉closure T)
    (hext : ∀ z, z∈segment ℝ (P.point v) q → z∈closure S → z=P.point v) :
    ∃ Q : PLDrawing G, PortMove P.point Q B v q S T := by
  classical
  obtain ⟨c,t,Q,hc,hc1,htv,ht,hQ,hreg,hTQ,hpointT,hfront,htail⟩ :=
    P.retube_extend hS hS0 hSb hpoint htrace hport hleaf hv hT hTop hT0 hTv hqT hout hext
  have hp (w : V) : Q.point w=P.retubePoint B c t v q w := congrFun hQ w
  have hpv : Q.point v=q := by rw [hp]; simp [retubePoint]
  have hpw (w : V) (hw : w∈B) (he : w≠v) : Q.point w=t w•P.point w := by
    rw [hp]; simp only [retubePoint,ite_eq_right he,radialPoint,ite_eq_left hw]
  have hscl (w : V) (hw : w≠v) : Q.point w∈closure S := by
    rw [hp]; simp only [retubePoint,ite_eq_right hw,radialPoint]
    split_ifs with hwB
    · have : t w•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨t w,⟨hc.le.trans (ht w hwB).1.le,(ht w hwB).2⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
    · have : c•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc.le,hc1.le⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
  have htail_subset (w : V) (hw : w∈B) (he : w≠v) :
      segment ℝ (Q.point w) (P.point w) ⊆ segment ℝ 0 (P.point w) := by
    apply (convex_segment 0 (P.point w)).segment_subset
    · rw [hpw w hw he,segment_eq_image' ℝ]
      exact ⟨t w,⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩,by simp⟩
    · exact right_mem_segment ℝ _ _
  refine ⟨Q,⟨hpv,hpointT,hTQ,?_,?_,hfront,?_,?_,htail,?_⟩⟩
  · intro w
    by_cases he : w=v
    · subst w; exact Or.inr (hpv ▸ right_mem_segment ℝ (P.point v) q)
    · exact Or.inl (hscl w he)
  · intro d z hz
    rcases hreg d hz with hz|hz
    · exact Or.inl (P.radialRegion_old hS hS0 hc.le hc1.le hpoint htrace
        (fun w hw => ⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩) d hz)
    · exact Or.inr hz.2
  · intro w hw he
    exact hS.closure.segment_subset (hscl w he) (hpoint w)
  · intro w hw he z hz hzfr
    exact convex_frontier_segment hS hS0 (hport w hw) hzfr (htail_subset w hw he hz)
  · intro w hw he u hu hue hwu
    have hdisj := convex_frontier_tails_disjoint hS hS0 (hport w hw) (hport u hu)
      (fun h => hwu (P.point_injective h)) hc hc1.le
    apply hdisj.mono
    · rw [hpw w hw he]
      apply (convex_segment (c•P.point w) (P.point w)).segment_subset
      · rw [segment_eq_image' ℝ]
        refine ⟨(t w-c)/(1-c),?_,?_⟩
        · constructor
          · exact div_nonneg (sub_nonneg.mpr (ht w hw).1.le) (sub_nonneg.mpr hc1.le)
          · apply (div_le_one (sub_pos.mpr hc1)).mpr
            linarith [(ht w hw).2]
        · have hne : (1-c)≠0 := ne_of_gt (sub_pos.mpr hc1)
          have hs : c+((t w-c)/(1-c))*(1-c)=t w := by field_simp; ring
          calc c•P.point w+((t w-c)/(1-c))•(P.point w-c•P.point w)
            = (c+((t w-c)/(1-c))*(1-c))•P.point w := by module
            _ = t w•P.point w := by rw [hs]
      · exact right_mem_segment ℝ _ _
    · rw [hpw u hu hue]
      apply (convex_segment (c•P.point u) (P.point u)).segment_subset
      · rw [segment_eq_image' ℝ]
        refine ⟨(t u-c)/(1-c),?_,?_⟩
        · constructor
          · exact div_nonneg (sub_nonneg.mpr (ht u hu).1.le) (sub_nonneg.mpr hc1.le)
          · apply (div_le_one (sub_pos.mpr hc1)).mpr
            linarith [(ht u hu).2]
        · have hne : (1-c)≠0 := ne_of_gt (sub_pos.mpr hc1)
          have hs : c+((t u-c)/(1-c))*(1-c)=t u := by field_simp; ring
          calc c•P.point u+((t u-c)/(1-c))•(P.point u-c•P.point u)
            = (c+((t u-c)/(1-c))*(1-c))•P.point u := by module
            _ = t u•P.point u := by rw [hs]
      · exact right_mem_segment ℝ _ _

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter
namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

lemma affine_image_closure (f : ℂ ≃ᵃ[ℝ] ℂ) (S : Set ℂ) :
    closure (f '' S)=f '' closure S := by
  exact (f.toContinuousAffineEquiv.toHomeomorph.image_closure S).symm
lemma affine_image_frontier (f : ℂ ≃ᵃ[ℝ] ℂ) (S : Set ℂ) :
    frontier (f '' S)=f '' frontier S := by
  exact (f.toContinuousAffineEquiv.toHomeomorph.image_frontier S).symm

lemma PortMove.affine {p : V → ℂ} {Q : PLDrawing G} {B : Set V} {v : V} {q : ℂ} {S T : Set ℂ}
    (h : PortMove p Q B v q S T) (f : ℂ ≃ᵃ[ℝ] ℂ) :
    PortMove (fun w => f (p w)) (Q.affine f) B v (f q) (f '' S) (f '' T) := by
  have hseg (a b : ℂ) : segment ℝ (f a) (f b)=f '' segment ℝ a b := (image_segment ℝ f.toAffineMap a b).symm
  constructor
  · exact congrArg f h.selected
  · intro w; rw [affine_point,affine_image_closure]; exact ⟨Q.point w,h.point_mem w,rfl⟩
  · intro d; rw [Q.affine_trace,affine_image_closure]; exact Set.image_mono (h.trace_mem d)
  · intro w
    rw [affine_point,affine_image_closure,hseg,← Set.image_union]
    exact ⟨Q.point w,h.point_control w,rfl⟩
  · intro d
    rw [Q.affine_trace,affine_image_closure,hseg,← Set.image_union]
    exact Set.image_mono (h.trace_control d)
  · intro w hw he
    rw [affine_point,affine_image_frontier]
    exact ⟨Q.point w,h.on_frontier w hw he,rfl⟩
  · intro w hw he
    rw [affine_point,hseg,affine_image_closure]
    exact Set.image_mono (h.tail_old w hw he)
  · intro w hw he z hz hz'
    rw [affine_point,hseg] at hz
    rw [affine_image_frontier] at hz'
    obtain ⟨z,hz,rfl⟩ := hz
    obtain ⟨z',hz',hzz⟩ := hz'
    have heq : z'=z := f.injective hzz
    subst z'
    exact congrArg f (h.tail_frontier w hw he z hz hz')
  · intro w hw he z hz hz'
    rw [affine_point,hseg] at hz
    rw [affine_image_closure] at hz'
    obtain ⟨z,hz,rfl⟩ := hz
    obtain ⟨z',hz',hzz⟩ := hz'
    have heq : z'=z := f.injective hzz
    subst z'
    exact congrArg f (h.tail_new w hw he z hz hz')
  · intro w hw he u hu hue hwu
    rw [affine_point,affine_point,hseg,hseg]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
    have hxy' : y=x := f.injective hxy
    subst y
    exact Set.disjoint_left.mp (h.tails_disjoint w hw he u hu hue hwu) hx hy

lemma retube_at (P : PLDrawing G) {S T : Set ℂ} {B : Set V} {v : V} {q a : ℂ}
    (hS : Convex ℝ S) (hSopen : IsOpen S) (hSa : a∈S) (hSb : Bornology.IsBounded S)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (hport : ∀ w∈B, P.point w∈frontier S)
    (hleaf : ∀ w∈B, ∀ u w', G.Adj w u → G.Adj w w' → u=w')
    (hv : v∈B) (hT : Convex ℝ T) (hTop : IsOpen T) (hTa : a∈T)
    (hTv : P.point v∈T) (hqT : q∈closure T)
    (hout : ∀ w∈B, w≠v → P.point w∉closure T)
    (hext : ∀ z, z∈segment ℝ (P.point v) q → z∈closure S → z=P.point v) :
    ∃ Q : PLDrawing G, PortMove P.point Q B v q S T := by
  let f := AffineEquiv.constVAdd ℝ ℂ (-a)
  let R := P.affine f
  let S' := f '' S
  let T' := f '' T
  have hS' : Convex ℝ S' := hS.affine_image f.toAffineMap
  have hT' : Convex ℝ T' := hT.affine_image f.toAffineMap
  have hSop : IsOpen S' := f.toContinuousAffineEquiv.toHomeomorph.isOpenMap S hSopen
  have hTop' : IsOpen T' := f.toContinuousAffineEquiv.toHomeomorph.isOpenMap T hTop
  have h0S : (0:ℂ)∈S' := ⟨a,hSa,by simp [f]⟩
  have h0T : (0:ℂ)∈T' := ⟨a,hTa,by simp [f]⟩
  have hSb' : Bornology.IsBounded S' := by
    apply ((isCompact_of_isClosed_isBounded isClosed_closure hSb.closure).image
      f.toContinuousAffineEquiv.toHomeomorph.continuous).isBounded.subset
    exact Set.image_mono subset_closure
  have hcl (U : Set ℂ) : closure (f '' U)=f '' closure U := affine_image_closure f U
  have hfr (U : Set ℂ) : frontier (f '' U)=f '' frontier U := affine_image_frontier f U
  obtain ⟨Q,hQ⟩ := R.retube_controlled hS' (hSop.mem_nhds h0S) hSb'
    (fun w => by rw [hcl]; exact ⟨P.point w,hpoint w,rfl⟩)
    (fun d => by rw [show (R.chain d).trace=f '' (P.chain d).trace from P.affine_trace f d,hcl]; exact Set.image_mono (htrace d))
    (fun w hw => by rw [hfr]; exact ⟨P.point w,hport w hw,rfl⟩)
    hleaf hv hT' hTop' h0T (show f (P.point v)∈T' from ⟨P.point v,hTv,rfl⟩)
    (show f q∈closure T' from by rw [hcl]; exact ⟨q,hqT,rfl⟩)
    (fun w hw he hp => by
      rw [hcl] at hp
      obtain ⟨z,hz,heq⟩ := hp
      apply hout w hw he
      have heq' : z=P.point w := f.injective heq
      exact heq' ▸ hz)
    (fun z hz hz' => by
      change z∈segment ℝ (f (P.point v)) (f q) at hz
      have hs : f '' segment ℝ (P.point v) q=segment ℝ (f (P.point v)) (f q) := image_segment ℝ f.toAffineMap _ _
      rw [← hs] at hz
      rw [hcl] at hz'
      obtain ⟨z,hz,rfl⟩ := hz
      obtain ⟨z',hz',heq⟩ := hz'
      have heq' : z'=z := f.injective heq
      subst z'
      exact congrArg f (hext z hz hz'))
  have hh := hQ.affine f.symm
  refine ⟨Q.affine f.symm,?_⟩
  change PortMove (fun w => f.symm (f (P.point w))) (Q.affine f.symm)
    B v (f.symm (f q)) (f.symm '' (f '' S)) (f.symm '' (f '' T)) at hh
  simpa only [AffineEquiv.symm_apply_apply,Set.image_image,Function.comp_def,
    Set.image_id'] using hh

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

variable {V : Type}

namespace PortFrame
lemma ofMove [LinearOrder V] {G : SimpleGraph V} {p : V → ℂ} {Q : PLDrawing G} {B : Set V}
    {v : V} {q : ℂ} {S T : Set ℂ} (h : PLDrawing.PortMove p Q B v q S T) :
    PortFrame p Q.point B v q S T :=
  ⟨h.selected,h.on_frontier,h.tail_old,h.tail_frontier,h.tail_new,h.tails_disjoint⟩

lemma repoint {p a b : V → ℂ} {B : Set V} {v : V} {q r : ℂ} {S T : Set ℂ}
    (h : PortFrame p a B v q S T) (hv : b v=r) (he : ∀ w, w≠v → b w=a w) :
    PortFrame p b B v r S T := by
  constructor
  · exact hv
  · intro w hw hwv; rw [he w hwv]; exact h.on_frontier w hw hwv
  · intro w hw hwv; rw [he w hwv]; exact h.tail_old w hw hwv
  · intro w hw hwv; rw [he w hwv]; exact h.tail_frontier w hw hwv
  · intro w hw hwv; rw [he w hwv]; exact h.tail_new w hw hwv
  · intro w hw hwv u hu huv hwu
    rw [he w hwv,he u huv]; exact h.tails_disjoint w hw hwv u hu huv hwu
end PortFrame

namespace ExteriorPorts
variable {p target : V → ℂ} {B : Set V} {S : Set ℂ} (E : ExteriorPorts p target B S)

lemma end_mem (w : V) (hw : w∈B) : target w∈E.region w := by
  have hreach : ∀ y, PolygonallyJoined (E.region w) (p w) y → y∈E.region w := by
    intro y hj
    induction hj with
    | refl => exact E.start w hw
    | @tail y z h hz ih => exact hz (right_mem_segment ℝ _ _)
  exact hreach _ (E.joined w hw)

end ExteriorPorts
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y (n+1))

lemma tail_trace : P.trace=segment ℝ x (P.vertex 1) ∪ P.tail.trace := by
  apply Set.Subset.antisymm
  · rintro z (hz|hz)
    · have he : z=x := hz; subst z; exact Or.inl (left_mem_segment ℝ _ _)
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      by_cases he : (i:ℕ)=0
      · exact Or.inl (by simpa only [he,zero_add,P.start] using hi)
      · apply Or.inr; apply Or.inr; apply Set.mem_iUnion.mpr
        refine ⟨⟨i-1,by omega⟩,?_⟩
        simpa only [tail,show (i:ℕ)-1+1=i by omega] using hi
  · rintro z (hz|hz)
    · apply Or.inr; apply Set.mem_iUnion.mpr
      exact ⟨⟨0,by omega⟩,by simpa only [zero_add,P.start] using hz⟩
    · rcases hz with hz|hz
      · have he : z=P.vertex 1 := hz; subst z
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0,by omega⟩,
          by simpa only [zero_add,P.start] using right_mem_segment ℝ x (P.vertex 1)⟩)
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i+1,by omega⟩,hi⟩)

lemma tail_simple (hP : P.IsSimple) : P.tail.IsSimple := by
  constructor
  · intro i hi j hj he
    change i≤n at hi
    change j≤n at hj
    have he' := hP.1 (show i+1∈Iic (n+1) from Nat.add_le_add_right hi 1)
      (show j+1∈Iic (n+1) from Nat.add_le_add_right hj 1) he
    omega
  · intro i j hij hjn z hz hz'
    obtain ⟨he,hz⟩ := hP.2 (i+1) (j+1) (by omega) (by omega) z hz hz'
    exact ⟨by omega,hz⟩

lemma head_tail_intersection (hP : P.IsSimple) {z : E}
    (hz : z∈segment ℝ x (P.vertex 1)) (hz' : z∈P.tail.trace) : z=P.vertex 1 := by
  rcases hz' with hz'|hz'
  · exact hz'
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz'
    obtain ⟨he,he'⟩ := hP.2 0 (i+1) (by omega) (by omega) z (by simpa only [P.start,zero_add] using hz) hi
    simpa only [he,zero_add] using he'

lemma first_ne (hP : P.IsSimple) : P.vertex 1≠x := by
  intro he
  have hh := hP.1 (show 1∈Iic (n+1) from Nat.le_add_left 1 n) (show 0∈Iic (n+1) from Nat.zero_le _)
    (he.trans P.start.symm)
  omega

lemma start_not_tail (hP : P.IsSimple) : x∉P.tail.trace := by
  intro hx
  exact P.first_ne hP (P.head_tail_intersection hP (left_mem_segment ℝ _ _) hx).symm

lemma finish_not_first (P : SegmentChain S x y (n+1+1)) (hP : P.IsSimple) :
    y∉segment ℝ x (P.vertex 1) := by
  intro hy
  have hlast : y∈segment ℝ (P.vertex (n+1)) (P.vertex (n+1+1)) := by
    rw [P.finish]; exact right_mem_segment ℝ _ _
  obtain ⟨he,he'⟩ := hP.2 0 (n+1) (by omega) (by omega) y
    (by simpa only [P.start,zero_add] using hy) hlast
  have hi := hP.1 (show n+1+1∈Iic (n+1+1) from by simp)
    (show n+1∈Iic (n+1+1) from Nat.le_succ _) (P.finish.trans he')
  omega

lemma cutFirst_trace (z : E) (hz : z∈segment ℝ x (P.vertex 1)) :
    (P.cutFirst z hz).trace=segment ℝ z (P.vertex 1) ∪ P.tail.trace := by
  rw [(P.cutFirst z hz).tail_trace]
  rfl

lemma cutFirst_subset (z : E) (hz : z∈segment ℝ x (P.vertex 1)) : (P.cutFirst z hz).trace ⊆ P.trace := by
  rw [P.cutFirst_trace,P.tail_trace]
  exact Set.union_subset_union ((convex_segment x (P.vertex 1)).segment_subset hz (right_mem_segment ℝ _ _)) Set.Subset.rfl

lemma cutFirst_simple (hP : P.IsSimple) (z : E) (hz : z∈segment ℝ x (P.vertex 1))
    (hne : z≠P.vertex 1) : (P.cutFirst z hz).IsSimple := by
  have hzhead : segment ℝ z (P.vertex 1) ⊆ segment ℝ x (P.vertex 1) :=
    (convex_segment x (P.vertex 1)).segment_subset hz (right_mem_segment ℝ _ _)
  have hztail : z∉P.tail.trace := fun h => hne (P.head_tail_intersection hP hz h)
  constructor
  · intro i hi j hj he
    by_cases hi0 : i=0 <;> by_cases hj0 : j=0
    · omega
    · subst i
      have he' : z=P.vertex j := by simpa only [cutFirst,ite_true,ite_eq_right hj0] using he
      exfalso; apply hztail
      rw [he']
      have hm := P.tail.vertex_mem_trace (j-1) (by change j≤n+1 at hj; omega)
      simpa only [tail,show j-1+1=j by omega] using hm
    · subst j
      have he' : P.vertex i=z := by simpa only [cutFirst,ite_true,ite_eq_right hi0] using he
      exfalso; apply hztail
      rw [← he']
      have hm := P.tail.vertex_mem_trace (i-1) (by change i≤n+1 at hi; omega)
      simpa only [tail,show i-1+1=i by omega] using hm
    · exact hP.1 hi hj (by simpa only [cutFirst,ite_eq_right hi0,ite_eq_right hj0] using he)
  · intro i j hij hjn w hw hw'
    have hj0 : j≠0 := by omega
    have hw₂ : w∈segment ℝ (P.vertex j) (P.vertex (j+1)) := by
      simpa only [cutFirst,ite_eq_right hj0,Nat.succ_ne_zero,ite_false] using hw'
    by_cases hi0 : i=0
    · subst i
      have hw₁ : w∈segment ℝ x (P.vertex 1) := hzhead
        (by simpa only [cutFirst,ite_true,zero_add,one_ne_zero,ite_false] using hw)
      obtain ⟨he,hw⟩ := hP.2 0 j hij hjn w (by simpa only [P.start,zero_add] using hw₁) hw₂
      exact ⟨he,by simpa only [cutFirst,ite_eq_right hj0] using hw⟩
    · obtain ⟨he,hw⟩ := hP.2 i j hij hjn w
        (by simpa only [cutFirst,ite_eq_right hi0,Nat.succ_ne_zero,ite_false] using hw) hw₂
      exact ⟨he,by simpa only [cutFirst,ite_eq_right hj0] using hw⟩

end SegmentChain
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Stem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

lemma segment_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : E} (hb : b∈segment ℝ a c) :
    segment ℝ a c=segment ℝ a b ∪ segment ℝ b c := by
  apply Set.Subset.antisymm
  · rw [segment_eq_image' ℝ] at hb ⊢
    obtain ⟨t,ht,rfl⟩ := hb
    rintro z ⟨u,hu,rfl⟩
    by_cases hut : u≤t
    · left
      by_cases ht0 : t=0
      · have hu0 : u=0 := by linarith [hu.1]
        simp only [hu0,zero_smul,add_zero]; exact left_mem_segment ℝ _ _
      rw [segment_eq_image' ℝ]
      refine ⟨u/t,⟨div_nonneg hu.1 ht.1,(div_le_one (lt_of_le_of_ne ht.1 (Ne.symm ht0))).mpr hut⟩,?_⟩
      have he : (u/t)*t=u := div_mul_cancel₀ u ht0
      simp only [add_sub_cancel_left,smul_smul,he]
    · right
      have htu : t<u := lt_of_not_ge hut
      have ht1 : t<1 := lt_of_lt_of_le htu hu.2
      rw [segment_eq_image' ℝ]
      refine ⟨(u-t)/(1-t),⟨div_nonneg (sub_nonneg.mpr htu.le) (sub_nonneg.mpr ht1.le),
        (div_le_one (sub_pos.mpr ht1)).mpr (by linarith [hu.2])⟩,?_⟩
      have hne : 1-t≠0 := ne_of_gt (sub_pos.mpr ht1)
      have he : t+((u-t)/(1-t))*(1-t)=u := by field_simp; ring
      calc a+t•(c-a)+((u-t)/(1-t))•(c-(a+t•(c-a)))
        = a+(t+((u-t)/(1-t))*(1-t))•(c-a) := by module
        _ = a+u•(c-a) := by rw [he]
  · exact Set.union_subset
      ((convex_segment a c).segment_subset (left_mem_segment ℝ _ _) hb)
      ((convex_segment a c).segment_subset hb (right_mem_segment ℝ _ _))

lemma convex_frontier_segment_at {S : Set ℂ} (hS : Convex ℝ S) (hop : IsOpen S)
    {a p q : ℂ} (ha : a∈S) (hp : p∈frontier S) (hq : q∈frontier S)
    (hseg : q∈segment ℝ a p) : q=p := by
  let f := AffineEquiv.constVAdd ℝ ℂ (-a)
  have hC : Convex ℝ (f '' S) := hS.affine_image f.toAffineMap
  have hO : IsOpen (f '' S) := f.toContinuousAffineEquiv.toHomeomorph.isOpenMap S hop
  have hzero : (0:ℂ)∈f '' S := ⟨a,ha,by simp [f]⟩
  have hfr (z : ℂ) (hz : z∈frontier S) : f z∈frontier (f '' S) := by
    rw [PLDrawing.affine_image_frontier]; exact ⟨z,hz,rfl⟩
  apply f.injective
  apply convex_frontier_segment hC (hO.mem_nhds hzero) (hfr p hp) (hfr q hq)
  have hs : f '' segment ℝ a p=segment ℝ (f a) (f p) := image_segment ℝ f.toAffineMap a p
  have hz : f q∈f '' segment ℝ a p := ⟨q,hseg,rfl⟩
  simpa only [hs,show f a=0 by simp [f]] using hz

namespace ExteriorPorts
variable {V : Type} {p target : V → ℂ} {B : Set V} {S : Set ℂ}
  (E : ExteriorPorts p target B S)

lemma spoke_intersection (hinj : Function.Injective p) (hS : Convex ℝ S) (hop : IsOpen S)
    {a : ℂ} (ha : a∈S) (hport : ∀ w∈B, p w∈frontier S)
    {v w : V} (hv : v∈B) (hw : w∈B) {z : ℂ}
    (hz : z∈segment ℝ a (p v)) (hz' : z∈E.region w) : v=w ∧ z=p v := by
  have he : z=p w := E.inside w hw z hz'
    (hS.closure.segment_subset (subset_closure ha) (frontier_subset_closure (hport v hv)) hz)
  have he' : p w=p v := convex_frontier_segment_at hS hop ha (hport v hv) (hport w hw)
    (he ▸ hz)
  exact ⟨(hinj he').symm,he.trans he'⟩

lemma spoke_disjoint (hinj : Function.Injective p) (hS : Convex ℝ S) (hop : IsOpen S)
    {a : ℂ} (ha : a∈S) (hport : ∀ w∈B, p w∈frontier S)
    {v w : V} (hv : v∈B) (hw : w∈B) (hvw : v≠w) :
    Disjoint (segment ℝ a (p v)) (E.region w) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact hvw (E.spoke_intersection hinj hS hop ha hport hv hw hz hz').1

lemma obstacles_closed [Finite V] {v : V} {K U : Set ℂ} (hK : IsClosed K) (hU : IsClosed U) :
    IsClosed (K ∪ U ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w) :=
  (hK.union hU).union (isClosed_iUnion_of_finite (fun w => (E.compact w w.property.1).isClosed))

end ExteriorPorts

namespace SegmentChain
variable {S : Set ℂ} {x y : ℂ} {n : ℕ} (P : SegmentChain S x y (n+1))

lemma piece_subset_trace (i : ℕ) (hi : i<n+1) :
    segment ℝ (P.vertex i) (P.vertex (i+1)) ⊆ P.trace := by
  intro z hz
  exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hz⟩)

lemma first_segment_subset : segment ℝ x (P.vertex 1) ⊆ P.trace := by
  rw [P.tail_trace]; exact Set.subset_union_left

lemma cut_not_start (hP : P.IsSimple) {t : ℝ} (ht : 0<t) (_ht1 : t≤1) :
    x+t•(P.vertex 1-x)≠x := by
  intro he
  have he' : t•(P.vertex 1-x)=0 := add_left_cancel (he.trans (add_zero x).symm)
  rcases smul_eq_zero.mp he' with he'|he'
  · exact (ne_of_gt ht) he'
  · exact P.first_ne hP (sub_eq_zero.mp he')

lemma cut_not_next (hP : P.IsSimple) {t : ℝ} (ht : t<1) :
    x+t•(P.vertex 1-x)≠P.vertex 1 := by
  intro he
  have he' : (1-t)•(P.vertex 1-x)=0 := by
    calc (1-t)•(P.vertex 1-x)=P.vertex 1-(x+t•(P.vertex 1-x)) := by module
      _ = 0 := by rw [he,sub_self]
  rcases smul_eq_zero.mp he' with he'|he'
  · exact (ne_of_gt (sub_pos.mpr ht)) he'
  · exact P.first_ne hP (sub_eq_zero.mp he')

lemma cut_avoids_start (hP : P.IsSimple) {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    x∉(P.cutFirst (x+t•(P.vertex 1-x)) (by rw [segment_eq_image' ℝ]; exact ⟨t,⟨ht.le,ht1⟩,rfl⟩)).trace := by
  rw [P.cutFirst_trace]
  rintro (hx|hx)
  · rw [segment_eq_image' ℝ] at hx
    obtain ⟨u,hu,he⟩ := hx
    dsimp only at he
    have he' : (t+u*(1-t))•(P.vertex 1-x)=0 := by
      calc (t+u*(1-t))•(P.vertex 1-x)
          = (x+t•(P.vertex 1-x)+u•(P.vertex 1-(x+t•(P.vertex 1-x))))-x := by module
        _ = 0 := by rw [he,sub_self]
    rcases smul_eq_zero.mp he' with he'|he'
    · have : 0<t+u*(1-t) := lt_of_lt_of_le ht (le_add_of_nonneg_right (mul_nonneg hu.1 (sub_nonneg.mpr ht1)))
      exact (ne_of_gt this) he'
    · exact P.first_ne hP (sub_eq_zero.mp he')
  · exact P.start_not_tail hP hx

/-- A literal cut of the first polygonal piece at the boundary of a convex
neighborhood. All of the residual path is outside, except for that port. -/
lemma exit_frontier (hP : P.IsSimple) {T : Set ℂ} (hT : Convex ℝ T) (hop : IsOpen T)
    (hx : x∈T) (htail : Disjoint (closure T) P.tail.trace) :
    ∃ q : ℂ, ∃ hq : q∈segment ℝ x (P.vertex 1),
      q∈frontier T ∧ q≠P.vertex 1 ∧ q≠x ∧
      (∀ z∈(P.cutFirst q hq).trace, z∈closure T → z=q) := by
  have hyout : P.vertex 1∉closure T := fun hy =>
    Set.disjoint_left.mp htail hy P.tail.start_mem_trace
  obtain ⟨t,ht,ht1,htfr,hin,hout⟩ := convex_segment_cut hT hop hx hyout
  let q := x+t•(P.vertex 1-x)
  have hq : q∈segment ℝ x (P.vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨t,⟨ht.le,ht1.le⟩,rfl⟩
  refine ⟨q,hq,htfr,P.cut_not_next hP ht1,P.cut_not_start hP ht ht1.le,?_⟩
  intro z hz hzT
  rw [P.cutFirst_trace] at hz
  rcases hz with hz|hz
  · rw [segment_eq_image' ℝ] at hz
    obtain ⟨u,hu,he⟩ := hz
    dsimp only at he
    by_cases hu0 : u=0
    · simpa only [hu0,zero_smul,add_zero] using he.symm
    · have hu' : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hgt : t<t+u*(1-t) := lt_add_of_pos_right _ (mul_pos hu' (sub_pos.mpr ht1))
      apply False.elim (hout (t+u*(1-t)) hgt _)
      have he' : x+(t+u*(1-t))•(P.vertex 1-x)=z := by
        calc x+(t+u*(1-t))•(P.vertex 1-x)=q+u•(P.vertex 1-q) := by dsimp only [q]; module
          _ = z := he
      exact he'.symm ▸ hzT
  · exact False.elim (Set.disjoint_left.mp htail hzT hz)

end SegmentChain
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

variable {V : Type} [LinearOrder V] {G : SimpleGraph V} {B : Set V}

namespace DiskCore
variable (C : DiskCore G B)

lemma spoke_subset {v : V} : segment ℝ C.center (C.drawing.point v) ⊆ closure C.disk :=
  C.convex.closure.segment_subset (subset_closure C.center_mem) (C.point_mem v)

/-- Align the first residual piece with a new disk center, without consuming
any bend. A thin capsule avoids every other stem and the fixed obstacle. -/
lemma align [Finite V] {target : V → ℂ}
    (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1))
    (hP : P.IsSimple) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
    ∃ P' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1),
      P'.IsSimple ∧ C'.drawing.point v∈segment ℝ C'.center (P'.vertex 1) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  classical
  let x := C.drawing.point v
  let m := x+(1/2:ℝ)•(P.vertex 1-x)
  have hm : m∈segment ℝ x (P.vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U := (P.cutFirst m hm).trace
  have hU : IsCompact U := (P.cutFirst m hm).trace_compact
  have hUsub : U ⊆ E.region v := (P.cutFirst m hm).trace_subset (P.trace_subset (E.start v hv) (P.cutFirst_subset m hm (P.cutFirst m hm).start_mem_trace))
  have hxU : x∉U := P.cut_avoids_start hP (by norm_num) (by norm_num)
  let F := K ∪ U ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w
  have hF : IsClosed F := E.obstacles_closed hK hU.isClosed
  have hdisj : Disjoint (segment ℝ C.center x) F := by
    apply Set.disjoint_left.mpr
    intro z hz hzF
    rcases hzF with (hzK|hzU)|hzE
    · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
    · have he := E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
        C.center_mem C.port hv hv hz (hUsub hzU)
      exact hxU (show C.drawing.point v∈U from he.2 ▸ hzU)
    · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
      exact w.property.2 (E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
        C.center_mem C.port hv w.property.1 hz hw).1.symm
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hxT : x∈T := hseg (right_mem_segment ℝ _ _)
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have htail : Disjoint (closure T) P.tail.trace := by
    apply hd.mono_right
    intro z hz
    exact Or.inl (Or.inr (by change z∈(P.cutFirst m hm).trace; rw [P.cutFirst_trace]; exact Or.inr hz))
  obtain ⟨q,hq,hqfr,hqne,hqnx,hqin⟩ := P.exit_frontier hP hT hTop hxT htail
  let R := P.cutFirst q hq
  have hother (w : V) (hw : w∈B) (he : w≠v) : Disjoint (closure T) (E.region w) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨w,hw,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (frontier_subset_closure hqfr)
    (fun w hw he hz => Set.disjoint_left.mp (hother w hw he) hz (E.start w hw))
    (fun z hz hzS => E.inside v hv z
      (P.trace_subset (E.start v hv) (P.first_segment_subset ((convex_segment x (P.vertex 1)).segment_subset
        (left_mem_segment ℝ _ _) hq hz))) hzS)
  let C' : DiskCore G B := ⟨Q,T,x,hT,hTop,hTb,hxT,hQ.point_mem,hQ.trace_mem,by
    intro w hw
    by_cases he : w=v
    · subst w; rw [hQ.selected]; exact hqfr
    · exact hQ.on_frontier w hw he⟩
  let E' : ExteriorPorts C'.drawing.point target B C'.disk := E.update (PortFrame.ofMove hQ)
    C.drawing.point_injective C.port hv hother R.trace_compact R.start_mem_trace
    (R.trace_subset (P.trace_subset (E.start v hv) (P.first_segment_subset hq))) hqin R.joined_trace
  have hE' : E'.region v=R.trace := by simp [E',ExteriorPorts.update,ExteriorPorts.updatedRegion]
  have hpoint : C'.drawing.point v=q := hQ.selected
  let R' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1) :=
    ⟨R.vertex,R.start.trans hpoint.symm,R.finish,fun i hi z hz =>
      hE'.symm ▸ R.piece_subset_trace i hi hz⟩
  refine ⟨C',E',R',P.cutFirst_simple hP q hq hqne,?_,
    hd.mono_right (fun z hz => Or.inl (Or.inl hz)),?_⟩
  · change C'.drawing.point v∈segment ℝ x (P.vertex 1)
    rw [hpoint]; exact hq
  · intro w hw z hz hzK
    by_cases he : w=v
    · subst w; rw [hE'] at hz
      exact R.trace_subset (P.trace_subset (E.start v hv) (P.first_segment_subset hq)) hz
    · change z∈ExteriorPorts.updatedRegion E Q.point v R.trace w at hz
      simp only [ExteriorPorts.updatedRegion,ite_eq_right he] at hz
      rcases hz with hz|hz
      · exact False.elim (Set.disjoint_left.mp hCK (hQ.tail_old w hw he hz) hzK)
      · exact hz

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter
variable {V : Type} [LinearOrder V] [Finite V] {G : SimpleGraph V} {B : Set V}
namespace DiskCore
variable (C : DiskCore G B) {target : V → ℂ}

/-- Consuming one radial piece and cutting the next strictly decreases the
number of residual polygonal pieces. All other external stems remain disjoint. -/
lemma bend_stem (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K)
    (hEK : ∀ z∈E.region v, z∈K → z=target v)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1+1))
    (hP : P.IsSimple) (hrad : C.drawing.point v∈segment ℝ C.center (P.vertex 1)) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
    ∃ P' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1),
      P'.IsSimple ∧ C'.drawing.point v∈segment ℝ C'.center (P'.vertex 1) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  classical
  let x := C.drawing.point v
  let y := P.vertex 1
  let R := P.tail
  have hR : R.IsSimple := P.tail_simple hP
  let m := y+(1/2:ℝ)•(R.vertex 1-y)
  have hm : m∈segment ℝ y (R.vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U := (R.cutFirst m hm).trace
  have hU : IsCompact U := (R.cutFirst m hm).trace_compact
  have hUtail : U ⊆ P.tail.trace := R.cutFirst_subset m hm
  have htailP : P.tail.trace ⊆ P.trace := by rw [P.tail_trace]; exact Set.subset_union_right
  have hUsub : U ⊆ E.region v := hUtail.trans (htailP.trans (P.trace_subset (E.start v hv)))
  have hxU : x∉U := fun hx => P.start_not_tail hP (hUtail hx)
  have hyU : y∉U := R.cut_avoids_start hR (by norm_num) (by norm_num)
  have hheadE : segment ℝ x y ⊆ E.region v := P.first_segment_subset.trans (P.trace_subset (E.start v hv))
  let F := K ∪ U ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w
  have hF : IsClosed F := E.obstacles_closed hK hU.isClosed
  have hdisj : Disjoint (segment ℝ C.center y) F := by
    rw [segment_split hrad]
    apply Disjoint.union_left
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
      · have he := E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
          C.center_mem C.port hv hv hz (hUsub hzU)
        exact hxU (show C.drawing.point v∈U from he.2 ▸ hzU)
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
        exact w.property.2 (E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
          C.center_mem C.port hv w.property.1 hz hw).1.symm
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact P.finish_not_first hP ((hEK z (hheadE hz) hzK) ▸ hz)
      · have he := P.head_tail_intersection hP hz (hUtail hzU)
        exact hyU (show P.vertex 1∈U from he ▸ hzU)
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.disjoint v hv w w.property.1 (Ne.symm w.property.2)) (hheadE hz) hw
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hyT : y∈T := hseg (right_mem_segment ℝ _ _)
  have hxT : x∈T := hseg hrad
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have htail : Disjoint (closure T) R.tail.trace := by
    apply hd.mono_right
    intro z hz
    exact Or.inl (Or.inr (by change z∈(R.cutFirst m hm).trace; rw [R.cutFirst_trace]; exact Or.inr hz))
  obtain ⟨q,hq,hqfr,hqne,hqny,hqin⟩ := R.exit_frontier hR hT hTop hyT htail
  let A := R.cutFirst q hq
  have hother (w : V) (hw : w∈B) (he : w≠v) : Disjoint (closure T) (E.region w) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨w,hw,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (subset_closure hyT)
    (fun w hw he hz => Set.disjoint_left.mp (hother w hw he) hz (E.start w hw))
    (fun z hz hzS => E.inside v hv z (hheadE hz) hzS)
  have hnextTail : segment ℝ y q ⊆ P.tail.trace :=
    ((convex_segment y (R.vertex 1)).segment_subset (left_mem_segment ℝ _ _) hq).trans R.first_segment_subset
  have hmeet (z : ℂ) (hz : z∈closure C.disk ∪ segment ℝ x y) (hn : z∈segment ℝ y q) : z=y := by
    rcases hz with hz|hz
    · have he := E.inside v hv z (P.trace_subset (E.start v hv) (htailP (hnextTail hn))) hz
      exact False.elim (P.start_not_tail hP (he ▸ hnextTail hn))
    · exact P.head_tail_intersection hP hz (hnextTail hn)
  have hvertex (w : V) (hw : Q.point w∈segment ℝ y q) : w=v := by
    apply Q.point_injective
    exact (hmeet _ (hQ.point_control w) hw).trans hQ.selected.symm
  have hcross (d : ForwardDart G) (z : ℂ) (hz : z∈(Q.chain d).trace) (hz' : z∈segment ℝ y q) : z=Q.point v :=
    (hmeet z (hQ.trace_control d hz) hz').trans hQ.selected.symm
  obtain ⟨Q',hpQ',hrQ'⟩ := Q.move_leaf (hleaf v hv)
    (right_mem_segment ℝ y q) hvertex hcross
    (show PolygonallyJoined (segment ℝ y q) (Q.point v) q from
      hQ.selected.symm ▸ Relation.ReflTransGen.single Set.Subset.rfl)
  have hpv : Q'.point v=q := by rw [congrFun hpQ']; simp [PLDrawing.movedPoint]
  have hpw (w : V) (he : w≠v) : Q'.point w=Q.point w := by
    rw [congrFun hpQ']; simp [PLDrawing.movedPoint,he]
  have hnT : segment ℝ y q ⊆ closure T :=
    hT.closure.segment_subset (subset_closure hyT) (frontier_subset_closure hqfr)
  let C' : DiskCore G B := ⟨Q',T,y,hT,hTop,hTb,hyT,
    (by intro w; by_cases he : w=v
        · subst w; rw [hpv]; exact frontier_subset_closure hqfr
        · rw [hpw w he]; exact hQ.point_mem w),
    (by intro d z hz; rcases hrQ' d hz with hz|hz
        · exact hQ.trace_mem d hz
        · exact hnT hz.2),
    (by intro w hw; by_cases he : w=v
        · subst w; rw [hpv]; exact hqfr
        · rw [hpw w he]; exact hQ.on_frontier w hw he)⟩
  have hframe : PortFrame C.drawing.point Q'.point B v q C.disk T :=
    (PortFrame.ofMove hQ).repoint hpv hpw
  have hA : A.trace ⊆ E.region v := (R.cutFirst_subset q hq).trans (htailP.trans (P.trace_subset (E.start v hv)))
  let E' : ExteriorPorts C'.drawing.point target B C'.disk := E.update hframe
    C.drawing.point_injective C.port hv hother A.trace_compact A.start_mem_trace hA hqin A.joined_trace
  have hE' : E'.region v=A.trace := by simp [E',ExteriorPorts.update,ExteriorPorts.updatedRegion]
  let A' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1) :=
    ⟨A.vertex,A.start.trans hpv.symm,A.finish,fun i hi z hz => hE'.symm ▸ A.piece_subset_trace i hi hz⟩
  refine ⟨C',E',A',R.cutFirst_simple hR q hq hqne,?_,
    hd.mono_right (fun z hz => Or.inl (Or.inl hz)),?_⟩
  · change Q'.point v∈segment ℝ y (R.vertex 1)
    rw [hpv]; exact hq
  · intro w hw z hz hzK
    by_cases he : w=v
    · subst w; rw [hE'] at hz; exact hA hz
    · change z∈ExteriorPorts.updatedRegion E Q'.point v A.trace w at hz
      simp only [ExteriorPorts.updatedRegion,ite_eq_right he] at hz
      rcases hz with hz|hz
      · exact False.elim (Set.disjoint_left.mp hCK (hframe.tail_old w hw he hz) hzK)
      · exact hz

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set
variable {V : Type} [LinearOrder V] [Finite V] {G : SimpleGraph V} {B : Set V}
namespace DiskCore
variable (C : DiskCore G B) {target : V → ℂ}

/-- Before the last radial piece is swallowed, all of a closed external
barrier, including the target vertex itself, can remain outside the disk. -/
lemma prepare_radial (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K)
    (hEK : ∀ z∈E.region v, z∈K → z=target v)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1))
    (hP : P.IsSimple) (hrad : C.drawing.point v∈segment ℝ C.center (P.vertex 1)) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
      segment ℝ (C'.drawing.point v) (target v) ⊆ E'.region v ∧
      C'.drawing.point v∈segment ℝ C'.center (target v) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  induction n generalizing C with
  | zero =>
    refine ⟨C,E,?_,?_,hCK,fun _ _ _ hz _ => hz⟩
    · have hs := P.first_segment_subset.trans (P.trace_subset (E.start v hv))
      simpa only [P.finish] using hs
    · simpa only [P.finish] using hrad
  | succ n ih =>
    obtain ⟨C₁,E₁,P₁,hP₁,hr₁,hC₁,hprotect₁⟩ := C.bend_stem E hleaf hv hK hCK hEK P hP hrad
    have hE₁ : ∀ z∈E₁.region v, z∈K → z=target v := fun z hz hzK =>
      hEK z (hprotect₁ v hv z hz hzK) hzK
    obtain ⟨C₂,E₂,hseg₂,hr₂,hC₂,hprotect₂⟩ := ih C₁ E₁ hC₁ hE₁ P₁ hP₁ hr₁
    exact ⟨C₂,E₂,hseg₂,hr₂,hC₂,fun w hw z hz hzK =>
      hprotect₁ w hw z (hprotect₂ w hw z hz hzK) hzK⟩

lemma prepare_stem (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (htK : target v∈K)
    (hEK : ∀ z∈E.region v, z∈K → z=target v) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
      segment ℝ (C'.drawing.point v) (target v) ⊆ E'.region v ∧
      C'.drawing.point v∈segment ℝ C'.center (target v) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  obtain ⟨n,P,hP⟩ := (E.joined v hv).exists_simple_segmentChain
  cases n with
  | zero =>
    have he : C.drawing.point v=target v := P.start.symm.trans P.finish
    exact False.elim (Set.disjoint_left.mp hCK (he ▸ C.point_mem v) htK)
  | succ n =>
    obtain ⟨C₁,E₁,P₁,hP₁,hr₁,hC₁,hprotect₁⟩ := C.align E hleaf hv hK hCK P hP
    have hE₁ : ∀ z∈E₁.region v, z∈K → z=target v := fun z hz hzK =>
      hEK z (hprotect₁ v hv z hz hzK) hzK
    obtain ⟨C₂,E₂,hseg₂,hr₂,hC₂,hprotect₂⟩ := C₁.prepare_radial E₁ hleaf hv hK hC₁ hE₁ P₁ hP₁ hr₁
    exact ⟨C₂,E₂,hseg₂,hr₂,hC₂,fun w hw z hz hzK =>
      hprotect₁ w hw z (hprotect₂ w hw z hz hzK) hzK⟩

end DiskCore
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter
variable {V W : Type} [LinearOrder V] [Finite V] [LinearOrder W] [Finite W]
  [LinearOrder (V⊕W)] {G : SimpleGraph V} {B : Set V}

namespace DiskCore
variable (C : DiskCore G B) {target : V → ℂ}

lemma grow_star (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (hEK : Disjoint (E.region v) K)
    (hsegE : segment ℝ (C.drawing.point v) (target v) ⊆ E.region v)
    (hrad : C.drawing.point v∈segment ℝ C.center (target v))
    (child : W → ℂ) (n : W → ℕ)
    (P : ∀ w, SegmentChain Set.univ (target v) (child w) (n w+1))
    (hP : ∀ w, (P w).IsSimple)
    (hPC : ∀ w, Disjoint (closure C.disk) (P w).trace)
    (hPE : ∀ w u, u∈B → ∀ z∈(P w).trace, z∈E.region u → u=v ∧ z=target v)
    (hPP : ∀ w w', w≠w' → ∀ z∈(P w).trace, z∈(P w').trace → z=target v)
    (hPK : ∀ w, ∀ z∈(P w).trace, z∈K → z=child w)
    (hotherK : ∀ u∈B, ∀ z∈E.region u, z∈K → z=target u) :
    ∃ C' : DiskCore (leafExtension (W := W) G v) (starPorts B v),
    ∃ E' : ExteriorPorts C'.drawing.point (Sum.elim target child) (starPorts B v) C'.disk,
      C'.drawing.point (.inl v)=target v ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈starPorts B v, ∀ z∈E'.region w, z∈K → z=Sum.elim target child w) := by
  classical
  let m (w : W) := target v+(1/2:ℝ)•((P w).vertex 1-target v)
  have hm (w : W) : m w∈segment ℝ (target v) ((P w).vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U (w : W) := ((P w).cutFirst (m w) (hm w)).trace
  have hUsub (w : W) : U w ⊆ (P w).trace := (P w).cutFirst_subset _ _
  have hyU (w : W) : target v∉U w := (P w).cut_avoids_start (hP w) (by norm_num) (by norm_num)
  let F := K ∪ (⋃ w, U w) ∪ ⋃ u : {u // u∈B ∧ u≠v}, E.region u
  have hF : IsClosed F := (hK.union (isClosed_iUnion_of_finite
    (fun w => ((P w).cutFirst _ _).trace_compact.isClosed))).union
    (isClosed_iUnion_of_finite (fun u => (E.compact u u.property.1).isClosed))
  have hdisj : Disjoint (segment ℝ C.center (target v)) F := by
    rw [segment_split hrad]
    apply Disjoint.union_left
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzU
        exact Set.disjoint_left.mp (hPC w) (C.spoke_subset hz) (hUsub w hw)
      · obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.spoke_disjoint C.drawing.point_injective C.convex
          C.isOpen C.center_mem C.port hv u.property.1 (Ne.symm u.property.2)) hz hu
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact Set.disjoint_left.mp hEK (hsegE hz) hzK
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzU
        exact hyU w ((hPE w v hv z (hUsub w hw) (hsegE hz)).2 ▸ hw)
      · obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.disjoint v hv u u.property.1 (Ne.symm u.property.2)) (hsegE hz) hu
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hyT : target v∈T := hseg (right_mem_segment ℝ _ _)
  have hxT : C.drawing.point v∈T := hseg hrad
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have htail (w : W) : Disjoint (closure T) (P w).tail.trace := by
    apply hd.mono_right
    intro z hz
    apply Or.inl; apply Or.inr; apply Set.mem_iUnion.mpr
    refine ⟨w,?_⟩
    change z∈((P w).cutFirst _ _).trace
    rw [(P w).cutFirst_trace]; exact Or.inr hz
  choose q hq hqfr hqne hqny hqin using fun w =>
    (P w).exit_frontier (hP w) hT hTop hyT (htail w)
  let A (w : W) := (P w).cutFirst (q w) (hq w)
  have hAsub (w : W) : (A w).trace ⊆ (P w).trace := (P w).cutFirst_subset _ _
  have hother (u : V) (hu : u∈B) (he : u≠v) : Disjoint (closure T) (E.region u) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨u,hu,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (subset_closure hyT)
    (fun u hu he hz => Set.disjoint_left.mp (hother u hu he) hz (E.start u hu))
    (fun z hz hzS => E.inside v hv z (hsegE hz) hzS)
  let arm (w : W) := segment ℝ (target v) (q w)
  have harm (w : W) : arm w ⊆ (P w).trace :=
    ((convex_segment (target v) ((P w).vertex 1)).segment_subset (left_mem_segment ℝ _ _) (hq w)).trans
      (P w).first_segment_subset
  have harmT (w : W) : arm w ⊆ closure T :=
    hT.closure.segment_subset (subset_closure hyT) (frontier_subset_closure (hqfr w))
  have hmeet (w : W) (z : ℂ) (hz : z∈closure C.disk ∪ segment ℝ (C.drawing.point v) (target v))
      (hzP : z∈(P w).trace) : z=target v := by
    rcases hz with hz|hz
    · exact False.elim (Set.disjoint_left.mp (hPC w) hz hzP)
    · exact (hPE w v hv z hzP (hsegE hz)).2
  have hvertex (w : W) (u : V) (hu : Q.point u∈arm w) : u=v :=
    Q.point_injective ((hmeet w _ (hQ.point_control u) (harm w hu)).trans hQ.selected.symm)
  have hcross (w : W) (u x : V) (hux : G.Adj u x) (z : ℂ)
      (hz : z∈arm w) (hz' : z∈Q.region u x) : z=Q.point v := by
    rw [Q.region_eq u x hux] at hz'
    exact (hmeet w z (hQ.trace_control _ hz') (harm w hz)).trans hQ.selected.symm
  obtain ⟨R,hpR,hrR⟩ := Q.attachLeaves v q arm
    (fun w => by rw [hQ.selected]; exact hqny w)
    (fun w => hQ.selected.symm ▸ left_mem_segment ℝ _ _)
    (fun w => right_mem_segment ℝ _ _)
    (fun w => hQ.selected.symm ▸ Relation.ReflTransGen.single Set.Subset.rfl)
    hvertex
    (fun w w' hww z hz hz' => (hPP w w' hww z (harm w hz) (harm w' hz')).trans hQ.selected.symm)
    hcross
  have hpold (u : V) : R.point (.inl u)=Q.point u := congrFun hpR (.inl u)
  have hpnew (w : W) : R.point (.inr w)=q w := congrFun hpR (.inr w)
  let C' : DiskCore (leafExtension (W := W) G v) (starPorts B v) := {
    drawing := R
    disk := T
    center := target v
    convex := hT
    isOpen := hTop
    bounded := hTb
    center_mem := hyT
    point_mem := by
      intro u; cases u with
      | inl u => rw [hpold]; exact hQ.point_mem u
      | inr w => rw [hpnew]; exact frontier_subset_closure (hqfr w)
    trace_mem := by
      intro d z hz
      have hh := hrR d hz
      rcases d with ⟨⟨⟨u,x⟩,hux⟩,hord⟩
      cases u <;> cases x <;> simp only [PLDrawing.starRegion] at hh
      case inl.inl u x =>
        rw [Q.region_eq u x hux] at hh
        exact hQ.trace_mem _ hh
      case inl.inr u w => exact harmT w hh
      case inr.inl w u => exact harmT w hh
      case inr.inr w w' => exact False.elim hh
    port := by
      intro u hu; cases u with
      | inl u => rw [hpold]; exact hQ.on_frontier u hu.1 hu.2
      | inr w => rw [hpnew]; exact hqfr w }
  let E₀ := E.update (PortFrame.ofMove hQ) C.drawing.point_injective C.port hv hother
    isCompact_singleton (show target v∈({target v}:Set ℂ) from rfl)
    (Set.singleton_subset_iff.mpr (E.end_mem v hv))
    (fun z hz _ => hz) (Relation.ReflTransGen.refl)
  have hEold (u : V) (he : u≠v) :
      E₀.region u=segment ℝ (Q.point u) (C.drawing.point u) ∪ E.region u := by
    simp [E₀,ExteriorPorts.update,ExteriorPorts.updatedRegion,he]
  have hEarm (u : V) (hu : u∈B) (he : u≠v) (w : W) :
      Disjoint (E₀.region u) (A w).trace := by
    rw [hEold u he]
    apply Disjoint.union_left
    · exact (hPC w).mono (hQ.tail_old u hu he) (hAsub w)
    · apply Set.disjoint_left.mpr
      intro z hz hz'
      exact he (hPE w u hu z (hAsub w hz') hz).1
  have hyA (w : W) : target v∉(A w).trace := by
    intro hy
    exact hqny w (hqin w _ hy (subset_closure hyT)).symm
  let E' : ExteriorPorts C'.drawing.point (Sum.elim target child) (starPorts B v) C'.disk := {
    region := Sum.elim E₀.region (fun w => (A w).trace)
    compact := by
      intro u hu; cases u with
      | inl u => exact E₀.compact u hu.1
      | inr w => exact (A w).trace_compact
    start := by
      intro u hu; cases u with
      | inl u => change R.point (.inl u)∈E₀.region u; rw [hpold]; exact E₀.start u hu.1
      | inr w => change R.point (.inr w)∈(A w).trace; rw [hpnew]; exact (A w).start_mem_trace
    joined := by
      intro u hu; cases u with
      | inl u => change PolygonallyJoined (E₀.region u) (R.point (.inl u)) (target u)
                 rw [hpold]; exact E₀.joined u hu.1
      | inr w => change PolygonallyJoined (A w).trace (R.point (.inr w)) (child w)
                 rw [hpnew]; exact (A w).joined_trace
    inside := by
      intro u hu z hz hzT; cases u with
      | inl u => change z=R.point (.inl u); rw [hpold]; exact E₀.inside u hu.1 z hz hzT
      | inr w => change z=R.point (.inr w); rw [hpnew]; exact hqin w z hz hzT
    disjoint := by
      intro u hu x hx hux
      cases u with
      | inl u => cases x with
        | inl x => exact E₀.disjoint u hu.1 x hx.1 (fun he => hux (congrArg Sum.inl he))
        | inr w => exact hEarm u hu.1 hu.2 w
      | inr w => cases x with
        | inl u => exact (hEarm u hx.1 hx.2 w).symm
        | inr w' =>
          apply Set.disjoint_left.mpr
          intro z hz hz'
          exact hyA w ((hPP w w' (fun he => hux (congrArg Sum.inr he)) z (hAsub w hz) (hAsub w' hz')) ▸ hz) }
  refine ⟨C',E',(hpold v).trans hQ.selected,hd.mono_right (fun z hz => Or.inl (Or.inl hz)),?_⟩
  intro u hu z hz hzK
  cases u with
  | inl u =>
    change z∈E₀.region u at hz
    rw [hEold u hu.2] at hz
    rcases hz with hz|hz
    · exact False.elim (Set.disjoint_left.mp hCK (hQ.tail_old u hu.1 hu.2 hz) hzK)
    · exact hotherK u hu.1 z hz hzK
  | inr w => exact hPK w z (hAsub w hz) hzK

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.HeightTree
open Set
variable {V : Type} (T : HeightTree V)

lemma frontier_neighbor {S : Finset V} (hS : T.ParentClosed S) {v u : V}
    (hv : T.Frontier S v) (hu : T.Scope S u) (hvu : T.graph.Adj v u) : u=T.parent v := by
  rcases hvu with h|h
  · exact False.elim (hv.1 (h.2.symm ▸ T.scope_parent hS hu))
  · exact h.2

lemma frontier_leaf {S : Finset V} (hS : T.ParentClosed S) {v : {v // T.Scope S v}}
    (hv : T.Frontier S v.val) (u u' : {v // T.Scope S v})
    (hu : (SimpleGraph.comap Subtype.val T.graph).Adj v u)
    (hu' : (SimpleGraph.comap Subtype.val T.graph).Adj v u') : u=u' := by
  exact Subtype.ext ((T.frontier_neighbor hS hv u.property hu).trans
    (T.frontier_neighbor hS hv u'.property hu').symm)

variable [DecidableEq V]

omit [DecidableEq V] in
lemma old_child_adj {S : Finset V} (hS : T.ParentClosed S) {v u w : V}
    (hv : T.Frontier S v) (hu : T.Scope S u) (hw : T.Step v w) :
    T.graph.Adj u w ↔ u=v := by
  constructor
  · rintro (h|h)
    · exact h.2.trans hw.2.symm
    · exact False.elim (T.child_out hS hv hw (Or.inl (h.2 ▸ T.scope_parent hS hu)))
  · intro he; subst u; exact Or.inl hw

omit [DecidableEq V] in
lemma children_not_adj {v u w : V} (hu : T.Step v u) (hw : T.Step v w) :
    ¬T.graph.Adj u w := by
  rintro (h|h)
  · exact T.step_ne hu (h.2.trans hw.2.symm).symm
  · exact T.step_ne hw (h.2.trans hu.2.symm).symm

lemma extension_graph {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    Topology.leafExtension (W := {w // T.Step v w})
      (SimpleGraph.comap Subtype.val T.graph) (⟨v,Or.inr hv⟩:{u // T.Scope S u}) =
    SimpleGraph.comap (T.extensionEquiv hS hv)
      (SimpleGraph.comap Subtype.val T.graph) := by
  ext a b
  cases a with
  | inl a => cases b with
    | inl b => rfl
    | inr b =>
      change (a=⟨v,Or.inr hv⟩) ↔ T.graph.Adj a.val b.val
      rw [T.old_child_adj hS hv a.property b.property]
      exact Subtype.ext_iff
  | inr a => cases b with
    | inl b =>
      change (b=⟨v,Or.inr hv⟩) ↔ T.graph.Adj a.val b.val
      rw [T.graph.adj_comm,T.old_child_adj hS hv b.property a.property]
      exact Subtype.ext_iff
    | inr b =>
      exact iff_false_intro (T.children_not_adj a.property b.property) |>.symm

lemma extension_ports {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v)
    (a : {u // T.Scope S u} ⊕ {w // T.Step v w}) :
    a∈Topology.starPorts {w : {u // T.Scope S u} | T.Frontier S w.val} ⟨v,Or.inr hv⟩ ↔
      T.Frontier (insert v S) (T.extensionEquiv hS hv a).val := by
  rw [T.frontier_insert hS hv]
  cases a with
  | inl a =>
    change (T.Frontier S a.val ∧ a≠⟨v,Or.inr hv⟩) ↔
      (T.Frontier S a.val ∧ a.val≠v) ∨ T.Step v a.val
    have ha : ¬T.Step v a.val := fun h => T.child_out hS hv h a.property
    simp only [ha,or_false,ne_eq,Subtype.ext_iff]
  | inr a =>
    exact iff_true_intro (Or.inr a.property) |>.symm

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set
variable {V W : Type} [LinearOrder V] [LinearOrder W]
  {G : SimpleGraph V} {H : SimpleGraph W}

lemma PLDrawing.pullback (P : PLDrawing G) (f : W → V) (hf : Function.Injective f)
    (hG : ∀ u v, H.Adj u v → G.Adj (f u) (f v)) :
    ∃ Q : PLDrawing H, Q.point=P.point ∘ f ∧
      ∀ d, (Q.chain d).trace ⊆ P.region (f d.val.fst) (f d.val.snd) := by
  apply PLDrawing.ofSymmetricRegions (P.point ∘ f) (P.point_injective.comp hf)
    (fun u v => P.region (f u) (f v))
  · intro u v h; exact P.region_start _ _ (hG u v h)
  · intro u v h; exact P.region_joined _ _ (hG u v h)
  · intro u v h w hw
    exact (P.region_vertex _ _ (hG u v h) _ hw).elim (fun he => Or.inl (hf he)) (fun he => Or.inr (hf he))
  · intro u v w x h h' hne z hz hz'
    exact P.region_intersect _ _ _ _ (hG u v h) (hG w x h')
      (fun he => hne (he.elim (fun h => Or.inl ⟨hf h.1,hf h.2⟩)
        (fun h => Or.inr ⟨hf h.1,hf h.2⟩))) hz hz'

namespace DiskCore
variable {B : Set V} (C : DiskCore G B) {target : V → ℂ}

lemma region_mem (u v : V) (h : G.Adj u v) : C.drawing.region u v ⊆ closure C.disk := by
  rw [C.drawing.region_eq u v h]
  exact C.trace_mem _

/-- Relabel an actual core and all exterior paths along an injective graph map.
No drawing or disk existence is assumed beyond the supplied core. -/
lemma pullback (E : ExteriorPorts C.drawing.point target B C.disk)
    (f : W → V) (hf : Function.Injective f)
    (hG : ∀ u v, H.Adj u v → G.Adj (f u) (f v))
    {B' : Set W} (hB : ∀ w∈B', f w∈B) :
    ∃ C' : DiskCore H B', ∃ E' : ExteriorPorts C'.drawing.point (target ∘ f) B' C'.disk,
      C'.disk=C.disk ∧ (∀ w, C'.drawing.point w=C.drawing.point (f w)) ∧
      (∀ w, E'.region w=E.region (f w)) := by
  obtain ⟨Q,hQ,hsub⟩ := C.drawing.pullback f hf hG
  let C' : DiskCore H B' := ⟨Q,C.disk,C.center,C.convex,C.isOpen,C.bounded,C.center_mem,
    (fun w => by rw [hQ]; exact C.point_mem (f w)),
    (fun d => (hsub d).trans (C.region_mem _ _ (hG _ _ d.val.adj))),
    (fun w hw => by rw [hQ]; exact C.port (f w) (hB w hw))⟩
  let E' : ExteriorPorts C'.drawing.point (target ∘ f) B' C'.disk := {
    region := fun w => E.region (f w)
    compact := fun w hw => E.compact (f w) (hB w hw)
    start := fun w hw => by change Q.point w∈_; rw [hQ]; exact E.start (f w) (hB w hw)
    joined := fun w hw => by change PolygonallyJoined _ (Q.point w) _; rw [hQ]; exact E.joined (f w) (hB w hw)
    inside := fun w hw z hz hz' => by
      change z=Q.point w; rw [hQ]; exact E.inside (f w) (hB w hw) z hz hz'
    disjoint := fun w hw u hu hne => E.disjoint (f w) (hB w hw) (f u) (hB u hu) (hf.ne hne) }
  exact ⟨C',E',rfl,(fun w => congrFun hQ w),fun _ => rfl⟩

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.Topology.PLDrawing
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

lemma point_mem_carrier {S : Set V} {v : V} (hv : v∈S) : P.point v∈P.carrier S :=
  Or.inl (mem_iUnion.mpr ⟨⟨v,hv⟩,rfl⟩)

lemma region_mem_carrier {S : Set V} {u v : V} (hu : u∈S) (hv : v∈S) :
    P.region u v ⊆ P.carrier S := fun _ hz =>
  Or.inr (mem_iUnion.mpr ⟨⟨u,hu⟩,mem_iUnion.mpr ⟨⟨v,hv⟩,hz⟩⟩)

lemma carrier_mono {S T : Set V} (h : S ⊆ T) : P.carrier S ⊆ P.carrier T := by
  rintro z (hz|hz)
  · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    rcases hv with rfl
    exact P.point_mem_carrier (h v.property)
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hu
    exact P.region_mem_carrier (h u.property) (h v.property) hv

lemma carrier_compact [Finite V] (S : Set V) : IsCompact (P.carrier S) :=
  (isCompact_iUnion (fun _ => isCompact_singleton)).union
    (isCompact_iUnion (fun u => isCompact_iUnion (fun v => P.region_compact u.val v.val)))

lemma region_adj {u v : V} {z : ℂ} (hz : z∈P.region u v) : G.Adj u v := by
  classical
  by_contra h
  simp [region,h] at hz

lemma point_carrier_iff {S : Set V} {v : V} : P.point v∈P.carrier S ↔ v∈S := by
  constructor
  · rintro (hz|hz)
    · obtain ⟨w,hw⟩ := mem_iUnion.mp hz
      exact P.point_injective (mem_singleton_iff.mp hw) ▸ w.property
    · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
      obtain ⟨w,hw⟩ := mem_iUnion.mp hu
      exact (P.region_vertex _ _ (P.region_adj hw) v hw).elim
        (fun he => he ▸ u.property) (fun he => he ▸ w.property)
  · exact P.point_mem_carrier

lemma region_carrier_intersection {S : Set V} {u v : V} (h : G.Adj u v)
    (hu : u∉S) {z : ℂ} (hz : z∈P.region u v) (hzS : z∈P.carrier S) :
    z=P.point v := by
  rcases hzS with hzS|hzS
  · obtain ⟨w,hw⟩ := mem_iUnion.mp hzS
    have he := mem_singleton_iff.mp hw
    rw [he] at hz
    rcases P.region_vertex _ _ h w.val hz with he'|he'
    · exact False.elim (hu (he' ▸ w.property))
    · exact he.trans (congrArg P.point he')
  · obtain ⟨w,hw⟩ := mem_iUnion.mp hzS
    obtain ⟨x,hx⟩ := mem_iUnion.mp hw
    have hne : ¬((u=w.val ∧ v=x.val) ∨ (u=x.val ∧ v=w.val)) := by
      rintro (he|he)
      · exact hu (he.1.symm ▸ w.property)
      · exact hu (he.1.symm ▸ x.property)
    rcases (P.region_intersect _ _ _ _ h (P.region_adj hx) hne hz hx).1 with he|he
    · have : P.point u∈P.carrier S := by rw [← he]; exact P.region_mem_carrier w.property x.property hx
      exact False.elim (hu ((P.point_carrier_iff).mp this))
    · exact he

lemma carrier_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (P.carrier S) (P.carrier T) := by
  rw [disjoint_left]
  intro z hz hz'
  rcases hz with hz|hz
  · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    rw [mem_singleton_iff.mp hv] at hz'
    exact disjoint_left.mp h v.property (P.point_carrier_iff.mp hz')
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hu
    have he := P.region_carrier_intersection (P.region_adj hv)
      (fun hu => disjoint_left.mp h u.property hu) hv hz'
    rw [he] at hz'
    exact disjoint_left.mp h v.property (P.point_carrier_iff.mp hz')

lemma region_simple_chain {u v : V} (h : G.Adj u v) :
    ∃ n : ℕ, ∃ C : SegmentChain Set.univ (P.point u) (P.point v) (n+1),
      C.IsSimple ∧ C.trace ⊆ P.region u v := by
  obtain ⟨n,C,hC⟩ := (P.region_joined u v h).exists_simple_segmentChain
  cases n with
  | zero => exact False.elim (h.ne (P.point_injective (C.start.symm.trans C.finish)))
  | succ n => exact ⟨n,C.mapSet (subset_univ _),C.mapSet_simple _ hC,
      C.trace_subset (P.region_start u v h)⟩

end PlanarL1.Topology.PLDrawing




namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

lemma outside_closed (S : Finset V) : IsClosed (outside P S) :=
  (P.carrier_compact _).isClosed

omit [Fintype V] in
lemma outside_insert_subset (S : Finset V) (v : V) :
    outside P (insert v S) ⊆ outside P S :=
  P.carrier_mono (fun _ h => fun hw => h (Finset.mem_insert_of_mem hw))

omit [Fintype V] in
lemma point_outside_iff (S : Finset V) (v : V) : P.point v∈outside P S ↔ v∉S :=
  P.point_carrier_iff

namespace Growth
variable {T P}

lemma advance {S : Finset V} (hS : T.ParentClosed S) (H : T.Growth P S)
    (hG : T.graph ≤ G) {v : V} (hv : T.Frontier S v) :
    Nonempty (T.Growth P (insert v S)) := by
  classical
  let A := {u // T.Scope S u}
  let W := {w // T.Step v w}
  let a : A := ⟨v,Or.inr hv⟩
  let e := T.extensionEquiv hS hv
  let : LinearOrder (A⊕W) := LinearOrder.lift' e e.injective
  have hleaf : ∀ w : A, T.Frontier S w.val → ∀ u u',
      (SimpleGraph.comap Subtype.val T.graph).Adj w u →
      (SimpleGraph.comap Subtype.val T.graph).Adj w u' → u=u' :=
    fun _ hw _ _ h h' => T.frontier_leaf hS hw _ _ h h'
  have htK : P.point v∈outside P S := (point_outside_iff P S v).mpr hv.1
  obtain ⟨C,E,hseg,hrad,hCK,hprotect⟩ := H.core.prepare_stem H.stems hleaf
    (v := a) hv (outside_closed P S) H.avoid htK (H.contact a hv)
  have hcontact (u : A) (hu : T.Frontier S u.val) (z : ℂ) (hz : z∈E.region u)
      (hzK : z∈outside P S) : z=P.point u.val :=
    H.contact u hu z (hprotect u hu z hz hzK) hzK
  have hCK' : Disjoint (closure C.disk) (outside P (insert v S)) :=
    hCK.mono_right (outside_insert_subset P S v)
  have hvn : P.point v∉outside P (insert v S) := by
    rw [point_outside_iff]; simp
  have hEK' : Disjoint (E.region a) (outside P (insert v S)) := by
    rw [disjoint_left]; intro z hz hzK
    exact hvn (hcontact a hv z hz (outside_insert_subset P S v hzK) ▸ hzK)
  have he (w : W) : G.Adj v w.val := hG (Or.inl w.property)
  choose n Q hQ hsub using fun w : W => P.region_simple_chain (he w)
  have hout (w : W) : (Q w).trace ⊆ outside P S :=
    (hsub w).trans (P.region_mem_carrier hv.1 (fun hw =>
      T.child_out hS hv w.property (Or.inl hw)))
  have hPC (w : W) : Disjoint (closure C.disk) (Q w).trace := hCK.mono_right (hout w)
  have hPE (w : W) (u : A) (hu : T.Frontier S u.val) (z : ℂ)
      (hz : z∈(Q w).trace) (hzE : z∈E.region u) : u=a ∧ z=P.point v := by
    have hz' := hcontact u hu z hzE (hout w hz)
    have hmem : P.point u.val∈P.region v w.val := hz' ▸ hsub w hz
    rcases P.region_vertex _ _ (he w) u.val hmem with hu'|hu'
    · exact ⟨Subtype.ext hu',hz'.trans (congrArg P.point hu')⟩
    · exact False.elim (T.child_out hS hv w.property (hu' ▸ u.property))
  have hPP (w w' : W) (hne : w≠w') (z : ℂ)
      (hz : z∈(Q w).trace) (hz' : z∈(Q w').trace) : z=P.point v := by
    have hne' : ¬((v=v ∧ w.val=w'.val) ∨ (v=w'.val ∧ w.val=v)) := by
      rintro (hh|hh)
      · exact hne (Subtype.ext hh.2)
      · exact (he w).ne hh.2.symm
    rcases (P.region_intersect _ _ _ _ (he w) (he w') hne' (hsub w hz) (hsub w' hz')).1 with hh|hh
    · exact hh
    · have hm : P.point w.val∈P.region v w'.val := hh ▸ hsub w' hz'
      rcases P.region_vertex _ _ (he w') w.val hm with hh'|hh'
      · exact (he w).ne hh'.symm |>.elim
      · exact hne (Subtype.ext hh') |>.elim
  have hPK (w : W) (z : ℂ) (hz : z∈(Q w).trace)
      (hzK : z∈outside P (insert v S)) : z=P.point w.val :=
    P.region_carrier_intersection (he w) (by simp) (hsub w hz) hzK
  obtain ⟨C₁,E₁,hselected,havoid,hcontact₁⟩ := C.grow_star E hleaf hv
    (outside_closed P (insert v S)) hCK' hEK' hseg hrad (fun w : W => P.point w.val)
    n Q hQ hPC hPE hPP hPK
    (fun u hu z hz hzK => hcontact u hu z hz (outside_insert_subset P S v hzK))
  have hgraph : ∀ u u', (SimpleGraph.comap Subtype.val T.graph).Adj u u' →
      (leafExtension (W := W) (SimpleGraph.comap Subtype.val T.graph) a).Adj (e.symm u) (e.symm u') := by
    intro u u' h
    rw [T.extension_graph hS hv]
    change T.graph.Adj (e (e.symm u)).val (e (e.symm u')).val
    change T.graph.Adj u.val u'.val at h
    simpa only [Equiv.apply_symm_apply] using h
  have hports : ∀ w : {u // T.Scope (insert v S) u}, T.Frontier (insert v S) w.val →
      e.symm w∈starPorts {u : A | T.Frontier S u.val} a := by
    intro w hw
    apply (T.extension_ports hS hv (e.symm w)).mpr
    change T.Frontier (insert v S) (e (e.symm w)).val
    simpa only [Equiv.apply_symm_apply] using hw
  obtain ⟨C₂,E₂,hD,hp,hE⟩ := C₁.pullback E₁ e.symm e.symm.injective hgraph hports
  have htarget (w : {u // T.Scope (insert v S) u}) :
      (Sum.elim (fun u : A => P.point u.val) (fun u : W => P.point u.val) ∘ e.symm) w=P.point w.val := by
    have heq := congrArg Subtype.val (e.apply_symm_apply w)
    change T.extensionMap v (e.symm w)=w.val at heq
    have hm : Sum.elim (fun u : A => P.point u.val) (fun u : W => P.point u.val) (e.symm w)=
        P.point (T.extensionMap v (e.symm w)) := by cases e.symm w <;> rfl
    exact hm.trans (congrArg P.point heq)
  let E₃ := E₂.retarget (fun w => P.point w.val) htarget
  refine ⟨⟨C₂,E₃,?_,?_⟩⟩
  · rw [hD]; exact havoid
  · intro w hw z hz hzK
    have hz' : z∈E₁.region (e.symm w) := (hE w) ▸ hz
    exact (hcontact₁ (e.symm w) (hports w hw) z hz' hzK).trans (htarget w)

end Growth
end PlanarL1.HeightTree




namespace PlanarL1.HeightTree
open Set
variable {V : Type} (T : HeightTree V)

lemma root_graph :
    PlanarL1.Topology.leafExtension (W := {w // T.Step T.root w}) (⊥ : SimpleGraph PUnit) PUnit.unit =
    SimpleGraph.comap T.rootEquiv (SimpleGraph.comap Subtype.val T.graph) := by
  classical
  ext a b
  cases a with
  | inl a => cases b with
    | inl b => exact iff_false_intro (fun h : T.graph.Adj T.root T.root => h.ne rfl) |>.symm
    | inr b =>
      change a=PUnit.unit ↔ T.graph.Adj T.root b.val
      exact ⟨fun _ => Or.inl b.property,fun _ => Subsingleton.elim _ _⟩
  | inr a => cases b with
    | inl b =>
      change b=PUnit.unit ↔ T.graph.Adj a.val T.root
      exact ⟨fun _ => Or.inr a.property,fun _ => Subsingleton.elim _ _⟩
    | inr b => exact iff_false_intro (T.children_not_adj a.property b.property) |>.symm

lemma root_ports (a : PUnit ⊕ {w // T.Step T.root w}) :
    a.isRight ↔ T.Frontier {T.root} (T.rootEquiv a).val := by
  rw [T.frontier_root_iff]
  cases a with
  | inl a =>
    change (false=true) ↔ T.Step T.root T.root
    simp only [Bool.false_eq_true,false_iff]
    exact fun h => h.1 rfl
  | inr a =>
    change (true=true) ↔ T.Step T.root a.val
    exact ⟨fun _ => a.property,fun _ => rfl⟩

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set
variable {W : Type} [LinearOrder W] [Finite W] [LinearOrder (PUnit⊕W)]

/-- The first enclosing disk cuts each outgoing polygonal arm once, leaving
its entire residual trace outside. -/
lemma star_core (y : ℂ) (child : W → ℂ) (n : W → ℕ)
    (P : ∀ w, SegmentChain Set.univ y (child w) (n w+1))
    (hP : ∀ w, (P w).IsSimple)
    (hPP : ∀ w w', w≠w' → ∀ z∈(P w).trace, z∈(P w').trace → z=y)
    {K : Set ℂ} (hK : IsClosed K) (hyK : y∉K)
    (hPK : ∀ w, ∀ z∈(P w).trace, z∈K → z=child w) :
    ∃ C : DiskCore (leafExtension (W := W) (⊥ : SimpleGraph PUnit) PUnit.unit)
        {w | w.isRight},
    ∃ E : ExteriorPorts C.drawing.point (Sum.elim (fun _ => y) child) {w | w.isRight} C.disk,
      C.drawing.point (.inl PUnit.unit)=y ∧ Disjoint (closure C.disk) K ∧
      (∀ w, w.isRight → ∀ z∈E.region w, z∈K → z=Sum.elim (fun _ : PUnit => y) child w) := by
  classical
  let m (w : W) := y+(1/2:ℝ)•((P w).vertex 1-y)
  have hm (w : W) : m w∈segment ℝ y ((P w).vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U (w : W) := ((P w).cutFirst (m w) (hm w)).trace
  have hyU (w : W) : y∉U w := (P w).cut_avoids_start (hP w) (by norm_num) (by norm_num)
  let F := K ∪ ⋃ w, U w
  have hF : IsClosed F := hK.union (isClosed_iUnion_of_finite
    (fun w => ((P w).cutFirst _ _).trace_compact.isClosed))
  have hyF : y∉F := by
    rintro (h|h)
    · exact hyK h
    · obtain ⟨w,hw⟩ := mem_iUnion.mp h; exact hyU w hw
  have hdis : Disjoint (segment ℝ y y) F := by simpa only [segment_same] using disjoint_singleton_left.mpr hyF
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdis
  have hyT : y∈T := hseg (left_mem_segment ℝ _ _)
  have htail (w : W) : Disjoint (closure T) (P w).tail.trace := by
    apply hd.mono_right
    intro z hz
    apply Or.inr; apply mem_iUnion.mpr; refine ⟨w,?_⟩
    change z∈((P w).cutFirst _ _).trace
    rw [(P w).cutFirst_trace]; exact Or.inr hz
  choose q hq hqfr hqne hqny hqin using fun w =>
    (P w).exit_frontier (hP w) hT hTop hyT (htail w)
  let A (w : W) := (P w).cutFirst (q w) (hq w)
  have hAsub (w : W) : (A w).trace ⊆ (P w).trace := (P w).cutFirst_subset _ _
  let arm (w : W) := segment ℝ y (q w)
  have harm (w : W) : arm w ⊆ (P w).trace :=
    ((convex_segment y ((P w).vertex 1)).segment_subset (left_mem_segment ℝ _ _) (hq w)).trans
      (P w).first_segment_subset
  have harmT (w : W) : arm w ⊆ closure T :=
    hT.closure.segment_subset (subset_closure hyT) (frontier_subset_closure (hqfr w))
  let Q₀ := singletonDrawing y
  obtain ⟨Q,hQ,htrace⟩ := Q₀.attachLeaves PUnit.unit q arm hqny
    (fun w => left_mem_segment ℝ _ _) (fun w => right_mem_segment ℝ _ _)
    (fun w => Relation.ReflTransGen.single (by exact subset_rfl))
    (fun _ _ _ => Subsingleton.elim _ _)
    (fun w w' h z hz hz' => hPP w w' h z (harm w hz) (harm w' hz'))
    (fun _ _ _ h => False.elim h)
  let C : DiskCore (leafExtension (W := W) (⊥ : SimpleGraph PUnit) PUnit.unit) {w | w.isRight} := {
    drawing := Q
    disk := T
    center := y
    convex := hT
    isOpen := hTop
    bounded := hTb
    center_mem := hyT
    point_mem := by
      intro w; rw [hQ]; cases w with
      | inl w => exact subset_closure hyT
      | inr w => exact frontier_subset_closure (hqfr w)
    trace_mem := by
      intro d z hz
      have hh := htrace d hz
      cases ha : d.val.fst with
      | inl a => cases hb : d.val.snd with
        | inl b => have h := d.val.adj; rw [ha,hb] at h; exact False.elim h
        | inr b => rw [ha,hb] at hh; exact harmT b hh
      | inr a => cases hb : d.val.snd with
        | inl b => rw [ha,hb] at hh; exact harmT a hh
        | inr b => have h := d.val.adj; rw [ha,hb] at h; exact False.elim h
    port := by
      intro w hw; cases w with
      | inl w => simp at hw
      | inr w => rw [hQ]; exact hqfr w }
  let E : ExteriorPorts C.drawing.point (Sum.elim (fun _ => y) child) {w | w.isRight} C.disk := {
    region := Sum.elim (fun _ => ∅) (fun w => (A w).trace)
    compact := by intro w hw; cases w with
      | inl w => simp at hw
      | inr w => exact (A w).trace_compact
    start := by intro w hw; cases w with
      | inl w => simp at hw
      | inr w => change Q.point (.inr w)∈_; rw [hQ]; exact (A w).start_mem_trace
    joined := by intro w hw; cases w with
      | inl w => simp at hw
      | inr w => change PolygonallyJoined _ (Q.point (.inr w)) _; rw [hQ]; exact (A w).joined_trace
    inside := by intro w hw z hz hz'; cases w with
      | inl w => simp at hw
      | inr w => change z=Q.point (.inr w); rw [hQ]; exact hqin w z hz hz'
    disjoint := by
      intro w hw w' hw' hne
      cases w with
      | inl w => simp at hw
      | inr w => cases w' with
        | inl w' => simp at hw'
        | inr w' =>
          apply disjoint_left.mpr
          intro z hz hz'
          have he := hPP w w' (fun he => hne (congrArg Sum.inr he)) z (hAsub w hz) (hAsub w' hz')
          have he' := hqin w z hz (he.symm ▸ subset_closure hyT)
          exact hqny w (he'.symm.trans he) }
  refine ⟨C,E,?_,hd.mono_right subset_union_left,?_⟩
  · change Q.point (.inl PUnit.unit)=y; rw [hQ]; rfl
  · intro w hw z hz hzK
    cases w with
    | inl w => simp at hw
    | inr w => exact hPK w z (hAsub w hz) hzK

end PlanarL1.Topology




namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

lemma initial_growth (hG : T.graph ≤ G) : Nonempty (T.Growth P {T.root}) := by
  classical
  let W := {w // T.Step T.root w}
  let e := T.rootEquiv
  let : LinearOrder (PUnit⊕W) := LinearOrder.lift' e e.injective
  have he (w : W) : G.Adj T.root w.val := hG (Or.inl w.property)
  choose n Q hQ hsub using fun w : W => P.region_simple_chain (he w)
  have hPP (w w' : W) (hne : w≠w') (z : ℂ)
      (hz : z∈(Q w).trace) (hz' : z∈(Q w').trace) : z=P.point T.root := by
    have hne' : ¬((T.root=T.root ∧ w.val=w'.val) ∨ (T.root=w'.val ∧ w.val=T.root)) := by
      rintro (hh|hh)
      · exact hne (Subtype.ext hh.2)
      · exact (he w).ne hh.2.symm
    rcases (P.region_intersect _ _ _ _ (he w) (he w') hne' (hsub w hz) (hsub w' hz')).1 with hh|hh
    · exact hh
    · have hm : P.point w.val∈P.region T.root w'.val := hh ▸ hsub w' hz'
      rcases P.region_vertex _ _ (he w') w.val hm with hh'|hh'
      · exact (he w).ne hh'.symm |>.elim
      · exact hne (Subtype.ext hh') |>.elim
  have hyK : P.point T.root∉outside P {T.root} := by rw [point_outside_iff]; simp
  have hPK (w : W) (z : ℂ) (hz : z∈(Q w).trace)
      (hzK : z∈outside P {T.root}) : z=P.point w.val :=
    P.region_carrier_intersection (he w) (by simp) (hsub w hz) hzK
  obtain ⟨C,E,hroot,havoid,hcontact⟩ := star_core (P.point T.root) (fun w : W => P.point w.val)
    n Q hQ hPP (outside_closed P {T.root}) hyK hPK
  have hgraph : ∀ u u', (SimpleGraph.comap Subtype.val T.graph).Adj u u' →
      (leafExtension (W := W) (⊥ : SimpleGraph PUnit) PUnit.unit).Adj (e.symm u) (e.symm u') := by
    intro u u' h
    rw [T.root_graph]
    change T.graph.Adj (e (e.symm u)).val (e (e.symm u')).val
    change T.graph.Adj u.val u'.val at h
    simpa only [Equiv.apply_symm_apply] using h
  have hports : ∀ w : {u // T.Scope {T.root} u}, T.Frontier {T.root} w.val →
      (e.symm w).isRight := by
    intro w hw
    apply (T.root_ports (e.symm w)).mpr
    change T.Frontier {T.root} (e (e.symm w)).val
    simpa only [Equiv.apply_symm_apply] using hw
  obtain ⟨C₂,E₂,hD,hp,hE⟩ := C.pullback E e.symm e.symm.injective hgraph hports
  have htarget (w : {u // T.Scope {T.root} u}) :
      (Sum.elim (fun _ : PUnit => P.point T.root) (fun u : W => P.point u.val) ∘ e.symm) w=P.point w.val := by
    have heq := congrArg Subtype.val (e.apply_symm_apply w)
    change T.rootMap (e.symm w)=w.val at heq
    have hm : Sum.elim (fun _ : PUnit => P.point T.root) (fun u : W => P.point u.val) (e.symm w)=
        P.point (T.rootMap (e.symm w)) := by cases e.symm w <;> rfl
    exact hm.trans (congrArg P.point heq)
  let E₃ := E₂.retarget (fun w => P.point w.val) htarget
  refine ⟨⟨C₂,E₃,?_,?_⟩⟩
  · rw [hD]; exact havoid
  · intro w hw z hz hzK
    have hz' : z∈E.region (e.symm w) := (hE w) ▸ hz
    exact (hcontact (e.symm w) (hports w hw) z hz' hzK).trans (htarget w)

end PlanarL1.HeightTree



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

lemma growth_exists (hG : T.graph ≤ G) (S : Finset V)
    (hroot : T.root∈S) (hS : T.ParentClosed S) : Nonempty (T.Growth P S) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S={T.root}
    · subst S; exact T.initial_growth P hG
    have hne : (S.erase T.root).Nonempty := by
      by_contra hh
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hh
      apply hs
      exact (Finset.insert_erase hroot).symm.trans (by rw [hempty]; rfl)
    obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image (S.erase T.root) T.depth hne
    have hvr : v≠T.root := (Finset.mem_erase.mp hv).1
    have hvS : v∈S := (Finset.mem_erase.mp hv).2
    have hroot' : T.root∈S.erase v := Finset.mem_erase.mpr ⟨hvr.symm,hroot⟩
    have hS' : T.ParentClosed (S.erase v) := by
      intro w hw
      have hwv := (Finset.mem_erase.mp hw).1
      have hwS := (Finset.mem_erase.mp hw).2
      refine Finset.mem_erase.mpr ⟨?_,hS w hwS⟩
      intro he
      by_cases hwr : w=T.root
      · subst w; exact hvr (he.symm.trans T.at_root)
      · have hd := T.step_depth (show T.Step v w from ⟨hwr,he.symm⟩)
        exact (not_lt_of_ge (hmax w (Finset.mem_erase.mpr ⟨hwr,hwS⟩))) hd
    have hfront : T.Frontier (S.erase v) v := by
      refine ⟨(by simp),Finset.mem_erase.mpr ⟨T.parent_ne hvr,hS v hvS⟩⟩
    obtain ⟨H⟩ := ih (S.erase v) (Finset.erase_ssubset hvS) hroot' hS'
    simpa only [Finset.insert_erase hvS] using H.advance hS' hG hfront

omit [LinearOrder V] in
lemma mem_internal (v : V) : v∈T.internal ↔ ¬T.IsLeaf v := by simp [internal]

lemma internal_closed : T.ParentClosed T.internal := by
  intro v hv
  by_cases he : v=T.root
  · subst v; rwa [T.at_root]
  · apply (T.mem_internal _).mpr
    exact fun h => h v ⟨he,rfl⟩

omit [LinearOrder V] in
lemma internal_scope (hroot : ¬T.IsLeaf T.root) (v : V) : T.Scope T.internal v := by
  by_cases h : T.IsLeaf v
  · refine Or.inr ⟨fun hv => (T.mem_internal v).mp hv h,(T.mem_internal _).mpr ?_⟩
    have hvr : v≠T.root := fun he => hroot (he ▸ h)
    exact fun hh => hh v ⟨hvr,rfl⟩
  · exact Or.inl ((T.mem_internal _).mpr h)

omit [LinearOrder V] in
lemma internal_frontier (hroot : ¬T.IsLeaf T.root) (v : V) :
    T.Frontier T.internal v ↔ T.IsLeaf v := by
  constructor
  · intro h
    by_contra hh
    exact h.1 ((T.mem_internal _).mpr hh)
  · intro h
    rcases T.internal_scope hroot v with hv|hv
    · exact False.elim ((T.mem_internal _).mp hv h)
    · exact hv

/-- Every actual polygonally drawn finite tree can be enclosed in a convex disk,
with the leaf stubs left as disjoint exterior polygonal arcs. All untouched raw
leaf-to-leaf drawing pieces remain outside the closed disk. -/
lemma tree_core (hG : T.graph ≤ G) (hroot : ¬T.IsLeaf T.root) :
    ∃ C : DiskCore T.graph {v | T.IsLeaf v},
      ∃ E : ExteriorPorts C.drawing.point P.point {v | T.IsLeaf v} C.disk,
        Disjoint (closure C.disk) (P.carrier {v | T.IsLeaf v}) ∧
        ∀ v, T.IsLeaf v → ∀ z∈E.region v, z∈P.carrier {v | T.IsLeaf v} → z=P.point v := by
  classical
  obtain ⟨H⟩ := T.growth_exists P hG T.internal ((T.mem_internal _).mpr hroot) T.internal_closed
  let i : V → {v // T.Scope T.internal v} := fun v => ⟨v,T.internal_scope hroot v⟩
  have hi : Function.Injective i := fun _ _ h => congrArg Subtype.val h
  have hgraph : ∀ u v, T.graph.Adj u v →
      (SimpleGraph.comap Subtype.val T.graph).Adj (i u) (i v) := fun _ _ h => h
  have hports : ∀ v, T.IsLeaf v → T.Frontier T.internal (i v).val :=
    fun v h => (T.internal_frontier hroot v).mpr h
  obtain ⟨C,E,hD,hp,hE⟩ := H.core.pullback H.stems i hi hgraph hports
  have hout : outside P T.internal=P.carrier {v | T.IsLeaf v} := by
    unfold outside
    congr 1
    ext v
    simp only [mem_ofPred_eq,T.mem_internal,not_not]
  refine ⟨C,E,?_,?_⟩
  · rw [hD,← hout]; exact H.avoid
  · intro v hv z hz hzK
    apply H.contact (i v) (hports v hv) z
    · exact (hE v) ▸ hz
    · rwa [hout]

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set

lemma PolygonallyJoined.exists_path {S : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoined S x y) (hx : x∈S) :
    ∃ p : Path x y, range p ⊆ S := by
  induction h with
  | refl => exact ⟨Path.refl x,by rintro z ⟨t,rfl⟩; exact hx⟩
  | @tail y z h hz ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨p.trans (Path.segment y z),by rw [Path.trans_range,Path.range_segment]; exact union_subset hp hz⟩

namespace DiskCore
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} {B : Set V} (C : DiskCore G B)

lemma carrier_subset (S : Set V) : C.drawing.carrier S ⊆ closure C.disk := by
  intro z hz
  rcases hz with hz|hz
  · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    exact mem_singleton_iff.mp hv ▸ C.point_mem v.val
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hu
    exact C.region_mem _ _ (C.drawing.region_adj hv) hv

end DiskCore
end PlanarL1.Topology

namespace PlanarL1.HeightTree
open Set PlanarL1.Topology Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [LinearOrder V] (T : HeightTree V)

lemma ancestor_plpath (P : PLDrawing T.graph) {u v : V} (h : T.Ancestor u v)
    {S : Set V} (hS : ∀ w, T.Ancestor u w → T.Ancestor w v → w∈S) :
    ∃ p : Path (P.point u) (P.point v), range p ⊆ P.carrier S := by
  induction h with
  | refl => exact ⟨Path.refl _,by rintro z ⟨t,rfl⟩; exact P.point_mem_carrier (hS _ .refl .refl)⟩
  | @tail v w huv hvw ih =>
    obtain ⟨p,hp⟩ := ih (fun a ha hb => hS a ha (hb.tail hvw))
    obtain ⟨q,hq⟩ := (P.region_joined v w (Or.inl hvw)).exists_path (P.region_start v w (Or.inl hvw))
    refine ⟨p.trans q,?_⟩
    rw [Path.trans_range]
    exact union_subset hp (hq.trans (P.region_mem_carrier (hS v huv (.single hvw))
      (hS w (huv.tail hvw) .refl)))

lemma descendants_pljoined (P : PLDrawing T.graph) (a : V) {u v : V}
    (hu : T.Ancestor a u) (hv : T.Ancestor a v) :
    ∃ p : Path (P.point u) (P.point v), range p ⊆ P.carrier {w | T.Ancestor a w} := by
  obtain ⟨p,hp⟩ := T.ancestor_plpath P hu (fun _ h _ => h)
  obtain ⟨q,hq⟩ := T.ancestor_plpath P hv (fun _ h _ => h)
  exact ⟨p.symm.trans q,by rw [Path.trans_range,Path.symm_range]; exact union_subset hp hq⟩

lemma nondescendants_pljoined (P : PLDrawing T.graph) (a : V) {u v : V}
    (hu : ¬T.Ancestor a u) (hv : ¬T.Ancestor a v) :
    ∃ p : Path (P.point u) (P.point v), range p ⊆ P.carrier {w | ¬T.Ancestor a w} := by
  obtain ⟨p,hp⟩ := T.ancestor_plpath P (T.root_ancestor u)
    (S := {w | ¬T.Ancestor a w}) (fun _ _ h ha => hu (ha.trans h))
  obtain ⟨q,hq⟩ := T.ancestor_plpath P (T.root_ancestor v)
    (S := {w | ¬T.Ancestor a w}) (fun _ _ h ha => hv (ha.trans h))
  exact ⟨p.symm.trans q,by rw [Path.trans_range,Path.symm_range]; exact union_subset hp hq⟩

lemma core_prefix_connected {B : Set V} {n : ℕ} (C : DiskCore T.graph B)
    (h : ℂ ≃ₜ ℂ) (hbound : ∀ z∈closure C.disk, ‖h z‖≤1)
    (leaf : Fin n → V) (angle : Fin n → ℝ)
    (hend : ∀ i, h (C.drawing.point (leaf i))=(Circle.exp (angle i) : ℂ))
    (horder : StrictMono angle) (hspan : ∀ i j, angle j-angle i<2*π)
    (a : V) {i j : Fin n} (hi : T.Ancestor a (leaf i)) (hj : T.Ancestor a (leaf j)) :
    (T.prefixGraph leaf a).Reachable i j := by
  apply Columns.consecutive_connected (T.prefixGraph leaf a) {k | T.Ancestor a (leaf k)}
    (fun _ _ hne hc ha hb => ⟨hne,hc,ha,hb⟩) _ hi hj
  intro w x y z hwx hxy hyz hbad
  suffices impossible : ∀ (S U : Set V), Disjoint S U →
      (∃ p : Path (C.drawing.point (leaf w)) (C.drawing.point (leaf y)), range p⊆C.drawing.carrier S) →
      (∃ q : Path (C.drawing.point (leaf x)) (C.drawing.point (leaf z)), range q⊆C.drawing.carrier U) → False by
    rcases hbad with ⟨hw,hx,hy,hz⟩ | ⟨hw,hx,hy,hz⟩
    · exact impossible {v | T.Ancestor a v} {v | ¬T.Ancestor a v}
        disjoint_compl_right (T.descendants_pljoined C.drawing a hw hy)
        (T.nondescendants_pljoined C.drawing a hx hz)
    · exact impossible {v | ¬T.Ancestor a v} {v | T.Ancestor a v}
        disjoint_compl_left (T.nondescendants_pljoined C.drawing a hw hy)
        (T.descendants_pljoined C.drawing a hx hz)
  intro S U hdis ⟨p,hp⟩ ⟨q,hq⟩
  let p' := (p.map h.continuous).cast (hend w).symm (hend y).symm
  let q' := (q.map h.continuous).cast (hend x).symm (hend z).symm
  obtain ⟨s,t,hst⟩ := Topology.disk_cyclic_arcs_meet (angle w) (angle x) (angle y) (angle z)
    (horder hwx) (horder hxy) (horder hyz) (by linarith [hspan w z]) p' q'
    (fun t => hbound _ (C.carrier_subset S (hp (mem_range_self t))))
    (fun t => hbound _ (C.carrier_subset U (hq (mem_range_self t))))
  have he : p s=q t := h.injective hst
  exact disjoint_left.mp (C.drawing.carrier_disjoint hdis) (hp (mem_range_self s))
    (he ▸ hq (mem_range_self t))

lemma layout_of_core [Fintype V] (C : DiskCore T.graph {v | T.IsLeaf v})
    (P : SimpleGraph {v : V // T.IsLeaf v})
    (hheight : ∀ i j, P.Adj i j → T.height i.val=T.height j.val)
    (hmatch : ∀ i j k, P.Adj i j → P.Adj i k → j=k)
    (arc : ∀ i j, P.Adj i j → Path (C.drawing.point i.val) (C.drawing.point j.val))
    (hout : ∀ i j h t, arc i j h t∉C.disk)
    (hdis : ∀ i j h k l h', i≠k → i≠l → j≠k → j≠l →
      Disjoint (range (arc i j h)) (range (arc k l h'))) :
    ∃ (L : T.Layout (Fintype.card {v : V // T.IsLeaf v})),
      ∀ i j, L.pair.Adj i j ↔ P.Adj ⟨L.leaf i,L.isLeaf i⟩ ⟨L.leaf j,L.isLeaf j⟩ := by
  classical
  obtain ⟨h,hi,hcl,hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall C.convex
    (show (interior C.disk).Nonempty by rw [C.isOpen.interior_eq]; exact ⟨C.center,C.center_mem⟩) C.bounded
  have hnorm (v : {v : V // T.IsLeaf v}) : ‖h (C.drawing.point v.val)‖=1 := by
    have hm := mem_image_of_mem h (C.port v.val v.property)
    rw [hfr] at hm
    simpa only [Metric.mem_sphere,dist_zero_right] using hm
  have hbound (z : ℂ) (hz : z∈closure C.disk) : ‖h z‖≤1 := by
    have hm := mem_image_of_mem h hz
    rw [hcl] at hm
    simpa only [Metric.mem_closedBall,dist_zero_right] using hm
  have hexterior (z : ℂ) (hz : z∉C.disk) : 1≤‖h z‖ := by
    by_contra! hn
    have hm : h z∈Metric.ball (0:ℂ) 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hn
    rw [← hi] at hm
    obtain ⟨w,hw,he⟩ := hm
    exact hz (h.injective he ▸ interior_subset hw)
  obtain ⟨e,he,hspan⟩ := Topology.finite_port_order (fun v : {v : V // T.IsLeaf v} => h (C.drawing.point v.val))
    hnorm (h.injective.comp (C.drawing.point_injective.comp Subtype.val_injective))
  let angle (i : Fin (Fintype.card {v : V // T.IsLeaf v})) := Complex.arg (h (C.drawing.point (e i).val))
  have hend i : h (C.drawing.point (e i).val)=(Circle.exp (angle i) : ℂ) :=
    (Topology.circle_exp_arg (hnorm (e i))).symm
  let A : ∀ i j, (SimpleGraph.comap e P).Adj i j →
      Path (Circle.exp (angle i) : ℂ) (Circle.exp (angle j) : ℂ) :=
    fun i j hij => ((arc (e i) (e j) hij).map h.continuous).cast (hend i).symm (hend j).symm
  have hnc : ColumnOrder.Noncrossing (SimpleGraph.comap e P) := by
    apply Topology.noncrossing_of_exterior_arcs _ angle he hspan A
    · intro i j hij t; exact hexterior _ (hout (e i) (e j) hij t)
    · intro i j hij k l hkl hik hil hjk hjl
      rw [disjoint_left]
      rintro z ⟨s,hs⟩ ⟨t,ht⟩
      have hh : h (arc (e i) (e j) hij s)=h (arc (e k) (e l) hkl t) := hs.trans ht.symm
      exact disjoint_left.mp (hdis (e i) (e j) hij (e k) (e l) hkl
        (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
        (mem_range_self s) (h.injective hh ▸ mem_range_self t)
  let L : T.Layout (Fintype.card {v : V // T.IsLeaf v}) := {
    leaf := fun i => (e i).val
    isLeaf := fun i => (e i).property
    injective := Subtype.val_injective.comp e.injective
    covers := fun v hv => ⟨e.symm ⟨v,hv⟩,by simp⟩
    prefix_connected := fun a i j hi hj =>
      T.core_prefix_connected C h hbound _ angle hend he hspan a hi hj
    pair := SimpleGraph.comap e P
    noncrossing := hnc
    paired_height := fun i j hij => hheight (e i) (e j) hij
    matching := fun i j k hij hik => e.injective (hmatch (e i) (e j) (e k) hij hik) }
  exact ⟨L,fun _ _ => Iff.rfl⟩

end PlanarL1.HeightTree




namespace PlanarL1.Topology
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)
  {p : V → ℂ} {B : Set V} {D : Set ℂ} (E : ExteriorPorts p P.point B D)

lemma stemCarrier_disjoint
    (hcontact : ∀ v∈B, ∀ z∈E.region v, z∈P.carrier B → z=P.point v)
    {S U : Set V} (hS : S⊆B) (hU : U⊆B) (hSU : Disjoint S U) :
    Disjoint (stemCarrier P E S) (stemCarrier P E U) := by
  have cross {S U : Set V} (hS : S⊆B) (hU : U⊆B) (hSU : Disjoint S U) :
      Disjoint (P.carrier S) (⋃ v : U, E.region v.val) := by
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨v,hv⟩ := mem_iUnion.mp hz'
    have he := hcontact v.val (hU v.property) z hv (P.carrier_mono hS hz)
    exact disjoint_left.mp hSU (P.point_carrier_iff.mp (he ▸ hz)) v.property
  apply Disjoint.union_left
  · exact Disjoint.union_right (P.carrier_disjoint hSU) (cross hS hU hSU)
  · apply Disjoint.union_right (cross hU hS hSU.symm).symm
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨v,hv⟩ := mem_iUnion.mp hz
    obtain ⟨w,hw⟩ := mem_iUnion.mp hz'
    exact disjoint_left.mp (E.disjoint v.val (hS v.property) w.val (hU w.property)
      (fun he => disjoint_left.mp hSU v.property (he ▸ w.property))) hv hw

end PlanarL1.Topology

namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

/-- The literal planar leaf layout is constructed from a real raw drawing of
its tree and terminal matching. Neither a contour order nor a disk is assumed. -/
lemma layout_of_drawing (P : PLDrawing G) (hG : T.graph ≤ G) (hroot : ¬T.IsLeaf T.root)
    (M : SimpleGraph {v : V // T.IsLeaf v})
    (hMG : ∀ i j, M.Adj i j → G.Adj i.val j.val)
    (hheight : ∀ i j, M.Adj i j → T.height i.val=T.height j.val)
    (hmatch : ∀ i j k, M.Adj i j → M.Adj i k → j=k) :
    ∃ (L : T.Layout (Fintype.card {v : V // T.IsLeaf v})),
      ∀ i j, L.pair.Adj i j ↔ M.Adj ⟨L.leaf i,L.isLeaf i⟩ ⟨L.leaf j,L.isLeaf j⟩ := by
  classical
  obtain ⟨C,E,havoid,hcontact⟩ := T.tree_core P hG hroot
  choose s hs using fun v : {v // T.IsLeaf v} =>
    (E.joined v.val v.property).exists_path (E.start v.val v.property)
  choose r hr using fun i j (h : M.Adj i j) =>
    (P.region_joined i.val j.val (hMG i j h)).exists_path (P.region_start i.val j.val (hMG i j h))
  let A : ∀ i j, M.Adj i j → Path (C.drawing.point i.val) (C.drawing.point j.val) :=
    fun i j h => ((s i).trans (r i j h)).trans (s j).symm
  have hS (i j : {v // T.IsLeaf v}) : ({i.val,j.val} : Set V) ⊆ {v | T.IsLeaf v} := by
    intro v hv
    rcases hv with rfl|hv
    · exact i.property
    · rw [mem_singleton_iff] at hv; exact hv ▸ j.property
  have hArange (i j : {v // T.IsLeaf v}) (h : M.Adj i j) :
      range (A i j h) ⊆ stemCarrier P E {i.val,j.val} := by
    change range (((s i).trans (r i j h)).trans (s j).symm) ⊆ _
    rw [Path.trans_range,Path.trans_range,Path.symm_range]
    refine union_subset (union_subset ?_ ?_) ?_
    · intro z hz; exact Or.inr (mem_iUnion.mpr ⟨⟨i.val,by simp⟩,hs i hz⟩)
    · intro z hz; exact Or.inl (P.region_mem_carrier (by simp) (by simp) (hr i j h hz))
    · intro z hz; exact Or.inr (mem_iUnion.mpr ⟨⟨j.val,by simp⟩,hs j hz⟩)
  have houtside (S : Set V) (hS : S⊆{v | T.IsLeaf v}) (z : ℂ)
      (hz : z∈stemCarrier P E S) : z∉C.disk := by
    intro hzD
    rcases hz with hz|hz
    · exact disjoint_left.mp havoid (subset_closure hzD) (P.carrier_mono hS hz)
    · obtain ⟨v,hv⟩ := mem_iUnion.mp hz
      have he := E.inside v.val (hS v.property) z hv (subset_closure hzD)
      have hf := C.port v.val (hS v.property)
      have hn : C.drawing.point v.val∉interior C.disk := hf.2
      exact hn (by rw [C.isOpen.interior_eq]; exact he ▸ hzD)
  apply T.layout_of_core C M hheight hmatch A
  · intro i j h t; exact houtside _ (hS i j) _ (hArange i j h (mem_range_self t))
  · intro i j h k l h' hik hil hjk hjl
    have hSU : Disjoint ({i.val,j.val} : Set V) {k.val,l.val} := by
      simp only [disjoint_left,mem_insert_iff,mem_singleton_iff]
      intro v hv hv'
      rcases hv with rfl|rfl <;> rcases hv' with he|he
      · exact hik (Subtype.ext he)
      · exact hil (Subtype.ext he)
      · exact hjk (Subtype.ext he)
      · exact hjl (Subtype.ext he)
    exact (stemCarrier_disjoint P E hcontact (hS i j) (hS k l) hSU).mono
      (hArange i j h) (hArange k l h')

end PlanarL1.HeightTree




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PlanarMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology.Drawing.Split
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
  (S : Set (ForwardDart G))

lemma unsplit_adj (d : ForwardDart G) (hd : d∉S) :
    (graph D S).Adj (.inl d.val.fst) (.inl d.val.snd) :=
  ⟨(.inl ⟨d,hd⟩,false),rfl,rfl⟩

lemma first_adj (d : S) : (graph D S).Adj (.inl d.val.val.fst) (.inr (d,0)) :=
  ⟨(.inr (d,0),false),rfl,rfl⟩

lemma last_adj (d : S) : (graph D S).Adj (.inl d.val.val.snd) (.inr (d,1)) :=
  ⟨(.inr (d,2),true),rfl,rfl⟩

lemma middle_adj (d : S) : (graph D S).Adj (.inr (d,0)) (.inr (d,1)) :=
  ⟨(.inr (d,1),false),rfl,rfl⟩

end PlanarL1.Topology.Drawing.Split




namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology PlanarL1.Topology.Drawing
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma original_tree_adj (D : Drawing G) {u v : V}
    (h : (shortestParents hc hs hl o).graph.Adj u v) :
    (drawingGraph hc hs hl o D).Adj (.inl u) (.inl v) := by
  have hg := shortestParents.graph_le hc hs hl o h
  by_cases huv : u<v
  · exact Split.unsplit_adj D (splitSet hc hs hl o) ⟨⟨(u,v),hg⟩,huv⟩ (not_not.mpr h)
  · exact (Split.unsplit_adj D (splitSet hc hs hl o)
      ⟨⟨(v,u),hg.symm⟩,lt_of_le_of_ne (le_of_not_gt huv) hg.ne.symm⟩ (not_not.mpr h.symm)).symm

lemma branch_adj (D : Drawing G) (d : ExtraDart hc hs hl o) :
    (drawingGraph hc hs hl o D).Adj (.inl d.val.fst) (.inr d) := by
  change (Split.graph D (splitSet hc hs hl o)).Adj (.inl d.val.fst) (.inr (splitTip hc hs hl o d))
  by_cases hd : d.val.fst<d.val.snd
  · rw [splitTip,dite_eq_left hd]
    exact Split.first_adj D (splitSet hc hs hl o) ⟨⟨d.val,hd⟩,d.property⟩
  · rw [splitTip,dite_eq_right hd]
    exact Split.last_adj D (splitSet hc hs hl o)
      ⟨⟨d.val.symm,lt_of_le_of_ne (le_of_not_gt hd) d.val.adj.ne.symm⟩,fun h => d.property h.symm⟩

lemma tree_le_drawingGraph (D : Drawing G) :
    (tree hc hs hl o).graph ≤ drawingGraph hc hs hl o D := by
  suffices step : ∀ u v, (tree hc hs hl o).Step u v → (drawingGraph hc hs hl o D).Adj u v by
    intro u v h
    exact h.elim (step u v) (fun h => (step v u h).symm)
  intro u v h
  obtain ⟨hv,rfl⟩ := h
  cases v with
  | inl v =>
    apply original_tree_adj hc hs hl o D
    exact Or.inr ⟨fun he => hv (congrArg Sum.inl he),rfl⟩
  | inr d => exact branch_adj hc hs hl o D d

lemma pair_adj (D : Drawing G) (d : ExtraDart hc hs hl o) :
    (drawingGraph hc hs hl o D).Adj (.inr d) (.inr (ExtraDart.reverse hc hs hl o d)) := by
  change (Split.graph D (splitSet hc hs hl o)).Adj (.inr (splitTip hc hs hl o d))
    (.inr (splitTip hc hs hl o (ExtraDart.reverse hc hs hl o d)))
  unfold splitTip
  by_cases hd : d.val.fst<d.val.snd
  · have hn : ¬(ExtraDart.reverse hc hs hl o d).val.fst<
        (ExtraDart.reverse hc hs hl o d).val.snd := not_lt_of_gt hd
    rw [dite_eq_left hd,dite_eq_right hn]
    exact Split.middle_adj D (splitSet hc hs hl o) ⟨⟨d.val,hd⟩,d.property⟩
  · have hh : (ExtraDart.reverse hc hs hl o d).val.fst<
        (ExtraDart.reverse hc hs hl o d).val.snd := lt_of_le_of_ne (le_of_not_gt hd) d.val.adj.ne.symm
    rw [dite_eq_right hd,dite_eq_left hh]
    exact (Split.middle_adj D (splitSet hc hs hl o)
      ⟨⟨d.val.symm,hh⟩, fun h => d.property h.symm⟩).symm

end PlanarL1.Weighted.EnlargedTree




namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma matchingGraph_height (i j : {v : Node hc hs hl o // (tree hc hs hl o).IsLeaf v})
    (h : (matchingGraph hc hs hl o).Adj i j) :
    (tree hc hs hl o).height i.val=(tree hc hs hl o).height j.val := by
  obtain ⟨d,hi,hj⟩ := h
  rw [hi,hj]
  exact (ExtraDart.tipHeight_reverse hc hs hl o d).symm

lemma matchingGraph_matching (i j k : {v : Node hc hs hl o // (tree hc hs hl o).IsLeaf v})
    (h : (matchingGraph hc hs hl o).Adj i j) (h' : (matchingGraph hc hs hl o).Adj i k) : j=k := by
  obtain ⟨d,hi,hj⟩ := h
  obtain ⟨e,hi',hk⟩ := h'
  have he : d=e := Sum.inr.inj (hi.symm.trans hi')
  subst e
  exact Subtype.ext (hj.trans hk.symm)

lemma layout_of_planar [LinearOrder V] (hp : IsPlanar G)
    (hroot : ¬(tree hc hs hl o).IsLeaf (tree hc hs hl o).root) :
    ∃ n : ℕ, ∃ L : (tree hc hs hl o).Layout n, ExactPairs L := by
  classical
  let : LinearOrder (Node hc hs hl o) := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨D⟩ := drawing_of_planar hp
  obtain ⟨P,_⟩ := (enlargedDrawing hc hs hl o D).polygonal
  obtain ⟨L,hL⟩ := (tree hc hs hl o).layout_of_drawing P (tree_le_drawingGraph hc hs hl o D)
    hroot (matchingGraph hc hs hl o) (by
      rintro i j ⟨d,hi,hj⟩
      rw [hi,hj]
      exact pair_adj hc hs hl o D d)
    (matchingGraph_height hc hs hl o) (matchingGraph_matching hc hs hl o)
  exact ⟨_,L,hL⟩

end PlanarL1.Weighted.EnlargedTree

namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

/-- The source's exact topology-to-column-layout bridge, including a singleton
incidence tree. The contour and the noncrossing switches are constructed, not
assumed. -/
lemma exact_layout_of_planar (hp : IsPlanar G) :
    ∃ n : ℕ, ∃ L : (tree hc hs hl o).Layout n, ExactPairs L := by
  classical
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  by_cases hr : (tree hc hs hl o).IsLeaf (tree hc hs hl o).root
  · refine ⟨1,(tree hc hs hl o).rootLeafLayout hr,?_⟩
    intro i j
    constructor
    · intro h; exact h.elim
    · rintro ⟨d,_,_⟩
      have he := hr.ancestor_eq ((tree hc hs hl o).root_ancestor (.inr d))
      exact False.elim (Sum.inl_ne_inr he)
  · exact layout_of_planar hc hs hl o hp hr

/-- Every literal planar weighted graph is isometric on its original vertices
to the constructed terminal noncrossing column model. -/
lemma column_model_of_planar (hp : IsPlanar G) :
    ∃ n : ℕ, ∃ L : (tree hc hs hl o).Layout n, ExactPairs L ∧
      ∀ u v : V, (L.point (.inl u)).distance (L.point (.inl v))=graphDistance G l u v := by
  obtain ⟨n,L,hL⟩ := exact_layout_of_planar hc hs hl o hp
  exact ⟨n,L,hL,original_distance L hL⟩

end PlanarL1.Weighted.EnlargedTree


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
lemma persistenceCount_pos : 0 < persistenceCount := by
  unfold persistenceCount
  have h1 := sq_nonneg (mainN:ℝ)
  have h2 := sq_nonneg ((1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ):ℝ)
  linarith
lemma exists_goodSpacing : ∃ q : ℕ, GoodSpacing q := by
  obtain ⟨q,hq⟩ := exists_nat_gt (max 2 (max (2000/R) (max (20/persistenceRadius+1)
    (max (80*persistenceSlope+1) (6/successGain+1)))))
  have h2 : (2:ℝ)<q := (le_max_left _ _).trans_lt hq
  have hg : 2000/R<(q:ℝ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hq
  have hr : 20/persistenceRadius+1<(q:ℝ) := (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))).trans_lt hq
  have hs : 80*persistenceSlope+1<(q:ℝ) := (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))).trans_lt hq
  have hb : 6/successGain+1<(q:ℝ) := (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))).trans_lt hq
  have hp : (0:ℝ)<q := by linarith
  have hp' : (0:ℝ)<q-1 := by linarith
  refine ⟨q,h2.le,?_,?_,?_,?_⟩
  · have hh := (div_lt_iff₀ (show (0:ℝ)<R by norm_num [R])).mp hg
    nlinarith
  · apply (div_le_iff₀ hp).mpr
    have hh := (div_lt_iff₀ persistenceRadius_pos).mp (show 20/persistenceRadius<(q:ℝ) by linarith)
    linarith
  · apply (div_le_iff₀ hp').mpr
    linarith
  · apply (div_le_iff₀ hp').mpr
    have hh := (div_lt_iff₀ successGain_pos).mp (show 6/successGain<(q:ℝ)-1 by linarith)
    nlinarith

lemma exists_mesh (N : ℕ) : ∃ m : ℕ, 0 < m ∧ 10000 ≤ m ∧ (N:ℝ)*persistenceCount/m ≤ 1/4 := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 10000 (4*N*persistenceCount))
  have ht : (10000:ℝ) < m := (le_max_left _ _).trans_lt hm
  have hp : 0 < m := by exact_mod_cast (show (0:ℝ) < m by linarith)
  refine ⟨m,hp,?_,?_⟩
  · exact_mod_cast (show (10000:ℝ) ≤ m by linarith)
  · apply (div_le_iff₀ (Nat.cast_pos.mpr hp)).mpr
    have hh := (le_max_right _ _).trans_lt hm
    linarith
end PlanarL1.Parameters

end



section

namespace PlanarL1.Execution
variable {α β γ : Type*}
lemma iterate_add (F : α → Execution α) (E : Execution α) (a b : ℕ) :
    iterate F E (a+b)=iterate F (iterate F E a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change (iterate F E (a+b)).bind F=(iterate F (iterate F E a) b).bind F
    rw [ih]
lemma Holds.iterate {F : α → Execution α} {E : Execution α} {P : ℕ → α → Prop}
    (hE : E.Holds (P 0)) (h : ∀ n x, P n x → (F x).Holds (P (n+1))) (n : ℕ) :
    (iterate F E n).Holds (P n) := by
  induction n with
  | zero => exact hE
  | succ n ih => exact ih.bind F (h n)
lemma prob_iterate_monotone (F : α → Execution α) (E : Execution α) (P : ℕ → α → Prop)
    (h : ∀ n x, P n x → (F x).Holds (P (n+1))) (N : ℕ) :
    E.prob (P 0) ≤ (iterate F E N).prob (P N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hh := conditional_success (iterate F E N) F (P N) (P (N+1)) (p := 1)
      (fun x hx => (h N x hx).prob_eq_one.ge)
    simp only [one_mul] at hh
    exact ih.trans hh
end PlanarL1.Execution

end



section

namespace PlanarL1.Parameters
lemma survivalBudget_zero (Q : ℝ) : survivalBudget Q 0=Q*successGain := by
  unfold survivalBudget
  simp
lemma survivalBudget_succ {Q : ℝ} (hQ : 1 < Q) (t : ℕ) :
    survivalBudget Q (t+1)=Q*(survivalBudget Q t-3) := by
  unfold survivalBudget
  rw [pow_succ]
  have hd : Q-1≠0 := by linarith
  field_simp
  ring
lemma survivalBudget_lower {Q : ℝ} (hQ : GoodSpacing Q) (t : ℕ) :
    Q^(t+1)*successGain/2 ≤ survivalBudget Q t := by
  have hp : 0 < Q := by linarith [hQ.1]
  have hm : 0 < Q-1 := by linarith [hQ.1]
  have hs := mul_le_mul_of_nonneg_left hQ.2.2.2.2 hp.le
  have he : Q*(3/(Q-1))=3*Q/(Q-1) := by ring
  rw [he] at hs
  have ht := mul_le_mul_of_nonneg_left hs (pow_nonneg hp.le t)
  have hr : 0≤3*Q/(Q-1) := by positivity
  unfold survivalBudget
  rw [pow_succ]
  nlinarith
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
lemma run_distances (n : ℕ) : (W.run g hm n).Holds (W.Distances n) :=
  Execution.Holds.iterate (E := .pure W) (P := W.Distances) W.distances_zero
    (fun _ _ h => W.next_distances g hm h) n

lemma run_add (a b : ℕ) : W.run g hm (a+b)=
    Execution.iterate (fun Z : World k V Q => Z.step g.pos g.one g.gap hm) (W.run g hm a) b :=
  Execution.iterate_add _ _ _ _
lemma run_survival_probability {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) (t : ℕ) :
    successChance/2 ≤ (W.run g hm (f+1+t)).prob (fun Z => Z.Successful (survivalBudget Q t) x y) := by
  rw [W.run_add g hm]
  apply le_trans (W.run_success_probability g hm hstart hmesh hmany hlo hhi)
  have hh := Execution.prob_iterate_monotone (fun Z : World k V Q => Z.step g.pos g.one g.gap hm)
    (W.run g hm (f+1)) (fun n Z => Z.Successful (survivalBudget Q n) x y) (by
      intro n Z hZ
      rw [survivalBudget_succ g.gt_one]
      exact Z.step_survives g.pos g.one g.gap hm hZ) t
  simpa only [survivalBudget_zero] using hh
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Parameters
lemma scheduleGain_pos : 0 < scheduleGain := div_pos (mul_pos successChance_pos successGain_pos) (by norm_num)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
lemma averagedCuts_upper (N : ℕ) (x y : V) :
    (W.averagedCuts g hm N).distance x y ≤ 2*(Q^N*W.distance x y) := by
  rw [averagedCuts,FiniteL1.CutFamily.distance_average,← Execution.mean_const (W.run g hm N) (2*(Q^N*W.distance x y))]
  apply Execution.Holds.mean_mono
  apply (W.run_distances g hm N).mono
  intro Z hZ
  exact (Z.cuts_upper x y).trans_eq (by rw [hZ])
lemma averagedCuts_designated {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) (t : ℕ) :
    scheduleGain*(Q^(f+1+t)*W.distance x y) ≤ (W.averagedCuts g hm (f+1+t)).distance x y := by
  have hQpos := g.pos
  have hGain := successGain_pos
  have hChance := successChance_pos
  have hp := W.run_survival_probability g hm hstart hmesh hmany hlo hhi t
  have hb := survivalBudget_lower g t
  have hc : 0 ≤ Q^(t+1)*successGain/2 := by positivity
  have hh := (W.run g hm (f+1+t)).mean_lower_of_event
    (P := fun Z => Z.Successful (survivalBudget Q t) x y)
    (f := fun Z => Z.cuts.distance x y) (c := Q^(t+1)*successGain/2)
    (fun Z => FiniteL1.CutFamily.distance_nonneg _ _ _) (fun Z hZ => hb.trans hZ.cuts)
  have hprod := mul_le_mul_of_nonneg_left hp hc
  rw [averagedCuts,FiniteL1.CutFamily.distance_average]
  apply le_trans ?_ (hprod.trans hh)
  have he : Q^(f+1+t)=Q^(t+1)*Q^f := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  calc
    _ = (Q^(t+1)*successChance*successGain/8)*(Q^f*W.distance x y) := by unfold scheduleGain; ring
    _ ≤ (Q^(t+1)*successChance*successGain/8)*2 :=
      mul_le_mul_of_nonneg_left hhi.le (by positivity)
    _ = _ := by ring
lemma averagedCuts_lower {N f : ℕ} (hf : f<N) {x y : V}
    (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (N:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) :
    scheduleGain*(Q^N*W.distance x y) ≤ (W.averagedCuts g hm N).distance x y := by
  have hfm : (f:ℝ)*persistenceCount/m ≤ 1/4 := by
    apply le_trans ?_ hmesh
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hf.le) persistenceCount_pos.le) (Nat.cast_nonneg m)
  have hh := W.averagedCuts_designated g hm hstart hfm hmany hlo hhi (N-(f+1))
  rwa [Nat.add_sub_of_le (Nat.succ_le_of_lt hf)] at hh
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) {M : Model (k+1)} (A : Ambient M)
variable (v : V → M.Point Set.univ A.root) {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 0 < m)
omit [Fintype V] in
lemma startAt_distance (x y : V) : (startAt (Q := Q) A v hσ).distance x y=σ*dist (v x) (v y) :=
  A.scaleEquiv_dist hσ _ _
omit [Fintype V] in
lemma startAt_coherent (x : V) (ρ : ℝ) : (startAt (Q := Q) A v hσ).Coherent x ρ :=
  initial_coherent _ _ _ _
omit [Fintype V] in
include g hσ in
lemma normalization_cancel (N : ℕ) (c d : ℝ) :
    (Q^N*σ)⁻¹*(c*(Q^N*(σ*d)))=c*d := by
  calc
    _ = ((Q^N*σ)⁻¹*(Q^N*σ))*(c*d) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (mul_pos (pow_pos g.pos N) hσ).ne',one_mul]
lemma normalizedCuts_upper (N : ℕ) (x y : V) :
    (normalizedCuts g A v hσ hm N).distance x y ≤ 2*dist (v x) (v y) := by
  rw [normalizedCuts,FiniteL1.CutFamily.distance_scale]
  have hh := (startAt (Q := Q) A v hσ).averagedCuts_upper g hm N x y
  rw [startAt_distance] at hh
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_pos (pow_pos g.pos N) hσ).le)).trans_eq
    (normalization_cancel g hσ N 2 _)
lemma normalizedCuts_lower {N f : ℕ} (hf : f<N) {x y : V}
    (hmesh : (N:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1≤Q^f*σ*dist (v x) (v y)) (hhi : Q^f*σ*dist (v x) (v y)<2) :
    scheduleGain*dist (v x) (v y) ≤ (normalizedCuts g A v hσ hm N).distance x y := by
  have hh := (startAt (Q := Q) A v hσ).averagedCuts_lower g hm hf
    (startAt_coherent A v hσ x _) hmesh hmany
    (by rwa [startAt_distance,← mul_assoc]) (by rwa [startAt_distance,← mul_assoc])
  rw [startAt_distance] at hh
  have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (mul_pos (pow_pos g.pos N) hσ).le)
  rw [normalization_cancel g hσ] at ht
  simpa only [normalizedCuts,FiniteL1.CutFamily.distance_scale] using ht
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Parameters
lemma first_scale {Q d : ℝ} (hQ : 1<Q) (hsmall : d<1) {T : ℕ} (hT : 1≤Q^T*d) :
    ∃ f : ℕ, f≤T ∧ 1≤Q^f*d ∧ Q^f*d<Q := by
  have hex : ∃ n : ℕ, 1≤Q^n*d := ⟨T,hT⟩
  let f := Nat.find hex
  have hf : 1≤Q^f*d := Nat.find_spec hex
  have hb : f≤T := Nat.find_min' hex hT
  refine ⟨f,hb,hf,?_⟩
  cases he : f with
  | zero => simp only [he,pow_zero,one_mul] at hf; linarith
  | succ n =>
    have hn : n<f := by omega
    have hp := lt_of_not_ge (Nat.find_min hex hn)
    have hh := mul_lt_mul_of_pos_left hp (show 0<Q by linarith)
    rw [pow_succ]
    nlinarith

lemma integer_offset {q : ℕ} {D : ℝ} (hlo : 1≤D) (hhi : D<(q:ℝ)) :
    ∃ i : Fin q, 1≤D/((i.val+1:ℕ):ℝ) ∧ D/((i.val+1:ℕ):ℝ)<2 := by
  let j : ℕ := ⌊D⌋₊
  have hj : 1≤j := by exact Nat.le_floor (by simpa using hlo)
  have hjD : (j:ℝ)≤D := Nat.floor_le (by linarith)
  have hDj : D<(j:ℝ)+1 := Nat.lt_floor_add_one D
  have hjq : j<q := by exact_mod_cast hjD.trans_lt hhi
  have hjp : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  let i : Fin q := ⟨j-1,by omega⟩
  have hi : i.val+1=j := Nat.sub_add_cancel hj
  refine ⟨i,?_,?_⟩
  · rw [hi]
    exact (le_div_iff₀ hjp).mpr (by simpa using hjD)
  · rw [hi]
    apply (div_lt_iff₀ hjp).mpr
    have hjr : (1:ℝ)≤j := by exact_mod_cast hj
    linarith

/-- A finite family of Q offsets covers arbitrary positive distances. Only the
number of iterations and the initial units depend on the finite metric. -/
lemma finite_schedule_cover {V : Type*} [Fintype V] (d : V → V → ℝ)
    (hd : ∀ x y, 0≤d x y) {q : ℕ} (hq : 1<(q:ℝ)) :
    ∃ ε : ℝ, 0<ε ∧ ∃ N : ℕ, ∀ x y, 0<d x y →
      ∃ i : Fin q, ∃ f : ℕ, f<N ∧
        1≤(q:ℝ)^f*(ε/((i.val+1:ℕ):ℝ))*d x y ∧
        (q:ℝ)^f*(ε/((i.val+1:ℕ):ℝ))*d x y<2 := by
  classical
  let B : ℝ := ∑ x, ∑ y, d x y
  have hB : 0≤B := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hd x y))
  have hb (x y : V) : d x y≤B :=
    (Finset.single_le_sum (fun z _ => hd x z) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun w _ => hd z w)) (Finset.mem_univ x))
  let ε : ℝ := 1/(B+1)
  have hε : 0<ε := by unfold ε; positivity
  have hsmall (x y : V) : ε*d x y<1 := by
    change (1/(B+1))*d x y<1
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (div_lt_iff₀ (show 0<B+1 by linarith)).mpr
    linarith [hb x y]
  have hex : ∀ x y, ∃ n : ℕ, 0<d x y → 1≤(q:ℝ)^n*(ε*d x y) := by
    intro x y
    by_cases hp : 0<d x y
    · obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/(ε*d x y)) hq
      refine ⟨n,fun _ => ?_⟩
      exact ((div_lt_iff₀ (mul_pos hε hp)).mp hn).le
    · exact ⟨0,fun hh => (hp hh).elim⟩
  choose bound hbound using hex
  let T : ℕ := ∑ x, ∑ y, bound x y
  have ht (x y : V) : bound x y≤T :=
    (Finset.single_le_sum (fun z _ => Nat.zero_le _) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (f := fun z => ∑ w, bound z w) (fun z _ => Nat.zero_le _) (Finset.mem_univ x))
  refine ⟨ε,hε,T+1,?_⟩
  intro x y hxy
  have hT : 1≤(q:ℝ)^T*(ε*d x y) := (hbound x y hxy).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq.le (ht x y)) (mul_pos hε hxy).le)
  obtain ⟨f,hf,hlo,hhi⟩ := first_scale hq (hsmall x y) hT
  obtain ⟨i,hil,hih⟩ := integer_offset hlo hhi
  refine ⟨i,f,Nat.lt_succ_of_le hf,?_,?_⟩
  · convert hil using 1; ring
  · convert hih using 1; ring
end PlanarL1.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

universe u
namespace PlanarL1.Columns.Model.Ambient
open Parameters
variable {k : ℕ} {V : Type u} [Fintype V] {M : Model (k+1)}
variable {q : ℕ} (g : GoodSpacing q) (A : Ambient M) (v : V → M.Point Set.univ A.root)
include g

/-- The actual finite coupled process produces a cut metric with a universal
lower bound. The finite initial units, mesh and number of steps are selected
from the given vertices; they do not enter the distortion constant. -/
lemma exists_uniform_cuts : ∃ C : FiniteL1.CutFamily V, ∀ x y,
    (scheduleGain/(q:ℝ))*dist (v x) (v y) ≤ C.distance x y ∧
      C.distance x y ≤ 2*dist (v x) (v y) := by
  classical
  obtain ⟨ε,hε,N,hcover⟩ := finite_schedule_cover (fun x y => dist (v x) (v y))
    (fun _ _ => dist_nonneg) g.gt_one
  obtain ⟨m,hm,hmany,hmesh⟩ := exists_mesh N
  let σ : Fin q → ℝ := fun i => ε/((i.val+1:ℕ):ℝ)
  have hσ (i : Fin q) : 0<σ i := div_pos hε (Nat.cast_pos.mpr (Nat.zero_lt_succ _))
  let C : Fin q → FiniteL1.CutFamily V := fun i => World.normalizedCuts g A v (hσ i) hm N
  let D : FiniteL1.CutFamily V := FiniteL1.CutFamily.scale (1/(q:ℝ)) (div_nonneg (by norm_num) g.pos.le)
    (FiniteL1.CutFamily.sum C)
  have hupper (i : Fin q) (x y : V) : (C i).distance x y ≤ 2*dist (v x) (v y) :=
    World.normalizedCuts_upper g A v (hσ i) hm N x y
  have hdistance (x y : V) : D.distance x y=(1/(q:ℝ))*∑ i, (C i).distance x y := by
    rw [FiniteL1.CutFamily.distance_scale,FiniteL1.CutFamily.distance_sum]
  refine ⟨D,fun x y => ⟨?_,?_⟩⟩
  · by_cases hxy : 0<dist (v x) (v y)
    · obtain ⟨i,f,hf,hlo,hhi⟩ := hcover x y hxy
      have hl : scheduleGain*dist (v x) (v y) ≤ (C i).distance x y :=
        World.normalizedCuts_lower g A v (hσ i) hm hf hmesh hmany hlo hhi
      have hs : (C i).distance x y ≤ ∑ j, (C j).distance x y :=
        Finset.single_le_sum (fun j _ => (C j).distance_nonneg x y) (Finset.mem_univ i)
      rw [hdistance]
      have hh := mul_le_mul_of_nonneg_left (hl.trans hs) (div_nonneg (show (0:ℝ)≤1 by norm_num) g.pos.le)
      calc
        _ = (1/(q:ℝ))*(scheduleGain*dist (v x) (v y)) := by ring
        _ ≤ _ := hh
    · have he : dist (v x) (v y)=0 := le_antisymm (le_of_not_gt hxy) dist_nonneg
      rw [he,mul_zero]
      exact D.distance_nonneg x y
  · rw [hdistance]
    calc
      _ ≤ (1/(q:ℝ))*∑ i : Fin q, 2*dist (v x) (v y) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hupper i x y))
          (div_nonneg (by norm_num) g.pos.le)
      _ = 2*dist (v x) (v y) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [← mul_assoc,one_div,inv_mul_cancel₀ g.pos.ne',one_mul]

/-- A finite-dimensional real L1 embedding of vertices of any connected
terminal noncrossing column model, with a constant depending only on q. -/
lemma exists_L1_embedding : ∃ (Ω : Type u) (measurable : MeasurableSpace Ω)
    (μ : @MeasureTheory.Measure Ω measurable)
    (f : V → @MeasureTheory.Lp Ω ℝ measurable _ 1 μ), ∀ x y,
      dist (v x) (v y) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ (2/(scheduleGain/(q:ℝ)))*dist (v x) (v y) := by
  obtain ⟨C,hC⟩ := A.exists_uniform_cuts g v
  let : MeasurableSpace (Set V) := ⊤
  obtain ⟨f,hf⟩ := C.embedding_of_bounds (fun x y => dist (v x) (v y))
    (div_pos scheduleGain_pos g.pos) (fun x y => (hC x y).1) (fun x y => (hC x y).2)
  exact ⟨Set V,⊤,MeasureTheory.Measure.count,f,hf⟩
end PlanarL1.Columns.Model.Ambient

end



section

namespace PlanarL1
open Parameters Columns.Model

/-- Theorem 1.1 of the literal source. The spacing is selected once, before
any graph or length data. Its finite cut embedding is converted to real Lp1.
All geometric realization and process hypotheses are discharged above. -/
theorem planar_graph_metrics_embed_L1_oai : MainStatement := by
  classical
  obtain ⟨q,g⟩ := exists_goodSpacing
  refine ⟨max 1 (2/(scheduleGain/(q:ℝ))),le_max_left _ _,?_⟩
  intro n G length hc hp hs hl
  let o : Fin n := Classical.choice hc.nonempty
  obtain ⟨s,L,hL,hd⟩ := Weighted.EnlargedTree.column_model_of_planar hc hs hl o hp
  cases s with
  | zero => exact (Fin.elim0 (L.column (Weighted.EnlargedTree.tree hc hs hl o).root))
  | succ k =>
    let A := L.ambient
    obtain ⟨Ω,measurable,μ,f,hf⟩ := A.exists_L1_embedding g (fun v => L.point (.inl v))
    refine ⟨Ω,measurable,μ,f,?_⟩
    intro x y
    have he : dist (L.point (.inl x)) (L.point (.inl y))=graphDistance G length x y := hd x y
    have hh := hf x y
    change (L.point (.inl x)).distance (L.point (.inl y)) ≤ ‖f x-f y‖ ∧
      ‖f x-f y‖ ≤ (2/(scheduleGain/(q:ℝ)))*(L.point (.inl x)).distance (L.point (.inl y)) at hh
    rw [hd x y] at hh
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    rw [← he]
    exact dist_nonneg
end PlanarL1


end

end OAI
end

theorem solution : type_of% @OAI.PlanarL1.planar_graph_metrics_embed_L1_oai := @OAI.PlanarL1.planar_graph_metrics_embed_L1_oai
