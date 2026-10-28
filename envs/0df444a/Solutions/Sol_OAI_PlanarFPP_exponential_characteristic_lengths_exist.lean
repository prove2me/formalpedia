-- Prove2me | solution 1 for OAI.PlanarFPP.exponential_characteristic_lengths_exist
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:44:45.373176+00:00
-- url     : https://prove2.me/submissions/b2317190-a100-4472-a421-59d166238ebf

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_exponential_goodSite_path_probability_zero
import Theorems.Thm_OAI_PlanarFPP_exponential_source_connector_test

section
-- module Solutions.OAIS_PlanarFPP.Compat
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

theorem boundaryNext_tail (S : Finset Vertex) (e : SquareSide) :
    (boundaryNext S e).tail = e.head := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;> simp [SquareSide.tail, SquareSide.head, Step.corner,
      Step.left, Step.delta, Prod.mk_add_mk]
  · split <;> cases d <;>
      simp [SquareSide.tail, SquareSide.head, Step.corner, Step.left,
        Step.right, Step.outward, Step.delta, Prod.mk_add_mk]

@[simp] theorem boundaryPerm_tail (S : Finset Vertex) (e : BoundarySide S) :
    (boundaryPerm S e).val.tail = e.val.head := boundaryNext_tail S e.val

theorem boundaryPerm_ne_self (S : Finset Vertex) (e : BoundarySide S) :
    boundaryPerm S e ≠ e := by
  intro h
  have hh := boundaryPerm_tail S e
  rw [h] at hh
  have hz : e.val.2.delta = 0 := by
    have : e.val.tail + e.val.2.delta = e.val.tail + 0 := by
      simpa [SquareSide.head] using hh.symm
    exact add_left_cancel this
  cases hd : e.val.2 <;> simp [hd, Step.delta] at hz

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryWinding
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

theorem SquareSide.opposite_ne_self (e : SquareSide) : e.opposite ≠ e := by
  intro h
  have hh := congrArg Prod.snd h
  cases hd : e.2 <;> simp [opposite, hd, Step.reverse] at hh

theorem square_rayCross_sum (q : Vertex) :
    ∑ d : Step, SquareSide.rayCross (q,d) = if q = 0 then 1 else 0 := by
  have hu : (univ : Finset Step) = {Step.east,Step.west,Step.north,Step.south} := rfl
  rw [hu]
  rcases q with ⟨x,y⟩
  simp [SquareSide.rayCross, Prod.ext_iff]
  split_ifs <;> omega

theorem internalSides_opposite (S : Finset Vertex) (e : SquareSide)
    (he : e ∈ internalSides S) : e.opposite ∈ internalSides S := by
  simp only [internalSides, mem_filter, mem_product, mem_univ, and_true] at he ⊢
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [SquareSide.opposite, Step.outward,
    Step.right, Step.reverse, Step.delta, Prod.mk_add_mk, add_assoc]

theorem internalSides_rayCross_sum (S : Finset Vertex) :
    ∑ e ∈ internalSides S, e.rayCross = 0 := by
  refine sum_involution (fun e _ => e.opposite) ?_ ?_ (internalSides_opposite S) ?_
  · intro e he
    simp
  · intro e he hh
    exact e.opposite_ne_self
  · intro e he
    exact e.opposite_opposite

theorem boundarySides_rayCross_sum (S : Finset Vertex) :
    ∑ e ∈ boundarySides S, e.rayCross = if (0 : Vertex) ∈ S then 1 else 0 := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (S ×ˢ (univ : Finset Step))
    (fun e : SquareSide => e.1 + e.2.outward ∈ S) SquareSide.rayCross
  change (∑ e ∈ internalSides S, e.rayCross) +
    (∑ e ∈ boundarySides S, e.rayCross) = _ at hsplit
  rw [internalSides_rayCross_sum, zero_add] at hsplit
  rw [hsplit, sum_product]
  change (∑ q ∈ S, ∑ d : Step, SquareSide.rayCross (q,d)) = _
  simp_rw [square_rayCross_sum]
  by_cases h0 : (0 : Vertex) ∈ S
  · rw [ite_eq_left h0]
    calc
      _ = (if (0 : Vertex) = 0 then (1 : ℤ) else 0) := by
        apply sum_eq_single 0
        · intro b hb hne
          exact ite_eq_right hne
        · exact fun hh => False.elim (hh h0)
      _ = 1 := ite_eq_left rfl
  · rw [ite_eq_right h0]
    apply sum_eq_zero
    intro q hq
    apply ite_eq_right
    intro hh
    exact h0 (hh ▸ hq)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryCycles
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Equiv

theorem exists_cycle_nonzero_sum {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (w : α → ℤ)
    (hw : ∑ x, w x ≠ 0) :
    ∃ x, ∑ y ∈ (p.toList x).toFinset, w y ≠ 0 := by
  classical
  let := Equiv.Perm.SameCycle.setoid p
  let Q := Quotient (Equiv.Perm.SameCycle.setoid p)
  let : Fintype Q := Fintype.ofFinite Q
  let c : α → Q := Quotient.mk (Equiv.Perm.SameCycle.setoid p)
  have hs := sum_fiberwise (univ : Finset α) c w
  by_contra hn
  push Not at hn
  have hz (q : Q) : ∑ y ∈ univ.filter (fun y => c y = q), w y = 0 := by
    induction q using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ univ.filter (fun y => c y = c x), w y) = 0
      have he : univ.filter (fun y => c y = c x) = (p.toList x).toFinset := by
        ext y
        simp only [mem_filter, mem_univ, true_and, List.mem_toFinset,
          Equiv.Perm.mem_toList_iff, Equiv.Perm.mem_support]
        constructor
        · intro hy
          exact ⟨(Quotient.exact hy : p.SameCycle y x).symm, hp x⟩
        · intro hy
          exact Quotient.sound hy.1.symm
      rw [he]
      exact hn x
  simp_rw [hz] at hs
  exact hw (by simpa using hs.symm)

theorem exists_boundary_cycle (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ x : BoundarySide S,
      let es := (boundaryPerm S).toList x
      es.Nodup ∧ 0 < es.length ∧
      (∀ e ∈ es, ((boundaryPerm S) e).val.tail = e.val.head) ∧
      (∀ e (he : e ∈ es), (es.next e he).val.tail = e.val.head) ∧
      (∑ e ∈ es.toFinset, e.val.rayCross) ≠ 0 := by
  classical
  have hw : ∑ e : BoundarySide S, e.val.rayCross ≠ 0 := by
    have hh := boundarySides_rayCross_sum S
    rw [ite_eq_left h0] at hh
    rw [Finset.sum_coe_sort]
    omega
  obtain ⟨x,hx⟩ := exists_cycle_nonzero_sum (boundaryPerm S)
    (boundaryPerm_ne_self S) (fun e => e.val.rayCross) hw
  refine ⟨x, Equiv.Perm.nodup_toList _ _, ?_, ?_, ?_, hx⟩
  · exact Equiv.Perm.length_toList_pos_of_mem_support _ _
      (Equiv.Perm.mem_support.mpr (boundaryPerm_ne_self S x))
  · intro e he
    exact boundaryPerm_tail S e
  · intro e he
    rw [Equiv.Perm.next_toList_eq_apply]
    exact boundaryPerm_tail S e

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem measurable_pathCost (hτ : ∀ e, Measurable (τ e))
    (p : Vertex) (ds : List Step) :
    Measurable (fun ω => pathCost (fun e => τ e ω) p ds) := by
  induction ds generalizing p with
  | nil => exact measurable_const
  | cons d ds ih => exact (hτ _).add (ih _)

theorem measurableSet_strict_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds < bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_lt (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

theorem measurableSet_bounded_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds ≤ bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_le (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Translation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

theorem shiftEdge_injective (a : Vertex) : Function.Injective (shiftEdge a) := by
  intro e f h
  simpa [shiftEdge, Prod.ext_iff] using h

theorem step_edge_translate (a p : Vertex) (d : Step) :
    d.edge (a+p) = shiftEdge a (d.edge p) := by
  cases d <;> simp [Step.edge, shiftEdge, add_assoc]

theorem pathCost_translate (w : Edge → ℝ) (a p : Vertex) (ds : List Step) :
    pathCost (fun e => w (shiftEdge a e)) p ds = pathCost w (a+p) ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost, step_edge_translate, ih, add_assoc]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.translate (h : ExponentialEnvironment P τ) (a : Vertex) :
    ExponentialEnvironment P (fun e => τ (shiftEdge a e)) where
  probability := h.probability
  measurable := fun _ => h.measurable _
  independent := h.independent.precomp (shiftEdge_injective a)
  marginal := fun _ => h.marginal _

theorem ExponentialEnvironment.jointLaw (h : ExponentialEnvironment P τ) :
    Measure.map (fun ω e => τ e ω) P = exponentialProductLaw := by
  rw [h.independent.map_fun_eq_infinitePi_map h.measurable]
  simp only [h.marginal, exponentialProductLaw]

theorem translated_event_probability (h : ExponentialEnvironment P τ) (a : Vertex)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun e => τ (shiftEdge a e) ω) ∈ A} =
      P {ω | (fun e => τ e ω) ∈ A} := by
  have h1 := (h.translate a).jointLaw
  have h2 := h.jointLaw
  have he := congrArg (fun Q : Measure (Edge → ℝ) => Q A) (h1.trans h2.symm)
  rw [Measure.map_apply (Measurable.of_eval (fun e => h.measurable _)) hA,
    Measure.map_apply (Measurable.of_eval h.measurable) hA] at he
  exact he

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteEdgeEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset

theorem measurable_extendEdgeWeights (S : Finset Edge) : Measurable (extendEdgeWeights S) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ S
  · simpa only [extendEdgeWeights,dite_eq_left he] using (measurable_pi_apply (⟨e,he⟩ : S))
  · simp only [extendEdgeWeights,dite_eq_right he]
    exact measurable_const

theorem DependsOnEdges.restriction_iff {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    extendEdgeWeights S (fun e : S => w e) ∈ A ↔ w ∈ A := by
  apply hA
  intro e he
  simp [extendEdgeWeights,he]

theorem DependsOnEdges.compl {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) : DependsOnEdges Aᶜ S := by
  intro w w' hh
  exact not_congr (hA w w' hh)

theorem dependsOnEdges_biInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, DependsOnEdges (A i) (S i)) :
    DependsOnEdges (⋂ i ∈ t, A i) (t.biUnion S) := by
  classical
  intro w w' hh
  simp only [mem_iInter]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hA i hi w w' (fun e he => hh e (mem_biUnion.mpr ⟨i,hi,he⟩))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem disjoint_edge_events_independent (h : ExponentialEnvironment P τ)
    (A B : Set (Edge → ℝ)) (S T : Finset Edge)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : DependsOnEdges A S) (hBT : DependsOnEdges B T) (hST : Disjoint S T) :
    IndepSet {ω | (fun e => τ e ω) ∈ A} {ω | (fun e => τ e ω) ∈ B} P := by
  let _ := h.probability
  have hf := h.independent.indepFun_finset S T hST h.measurable
  have hs : Measurable (fun ω (e : S) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have ht : Measurable (fun ω (e : T) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have hi := (indepFun_iff_indepSet_preimage hs ht).mp hf
    ((extendEdgeWeights S) ⁻¹' A) ((extendEdgeWeights T) ⁻¹' B)
    (hA.preimage (measurable_extendEdgeWeights S)) (hB.preimage (measurable_extendEdgeWeights T))
  have heA : (fun ω (e : S) => τ e ω) ⁻¹' ((extendEdgeWeights S) ⁻¹' A) =
      {ω | (fun e => τ e ω) ∈ A} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hAS.restriction_iff (fun e => τ e ω)
  have heB : (fun ω (e : T) => τ e ω) ⁻¹' ((extendEdgeWeights T) ⁻¹' B) =
      {ω | (fun e => τ e ω) ∈ B} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hBT.restriction_iff (fun e => τ e ω)
  simpa only [heA,heB] using hi

theorem disjoint_edge_events_inter_probability (h : ExponentialEnvironment P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j))) :
    P {ω | ∀ i ∈ t, (fun e => τ e ω) ∈ A i} =
      ∏ i ∈ t, P {ω | (fun e => τ e ω) ∈ A i} := by
  classical
  let _ := h.probability
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hAt : ∀ i ∈ t, MeasurableSet (A i) := fun i hi => hA i (mem_insert_of_mem hi)
    have hSt : ∀ i ∈ t, DependsOnEdges (A i) (S i) := fun i hi => hAS i (mem_insert_of_mem hi)
    have hd : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)) := by
      intro i hi j hj hij
      exact hdis (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij
    have hdunion : Disjoint (S a) (t.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hi) (by intro he; exact ha (he ▸ hi))
    have hm : MeasurableSet (⋂ i ∈ t, A i) := MeasurableSet.biInter (t.countable_toSet) hAt
    have hi := disjoint_edge_events_independent h (A a) (⋂ i ∈ t, A i) (S a) (t.biUnion S)
      (hA a (mem_insert_self _ _)) hm (hAS a (mem_insert_self _ _))
      (dependsOnEdges_biInter t A S hSt) hdunion
    have hprob := hi.measure_inter_eq_mul
    have he : {ω | ∀ i ∈ insert a t, (fun e => τ e ω) ∈ A i} =
        {ω | (fun e => τ e ω) ∈ A a} ∩ {ω | (fun e => τ e ω) ∈ ⋂ i ∈ t, A i} := by
      ext ω; simp
    rw [he,hprob,Finset.prod_insert ha]
    congr 1
    simpa only [mem_iInter] using ih hAt hSt hd

theorem disjoint_edge_events_iIndepSet (h : ExponentialEnvironment P τ)
    {ι : Type*} (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i, MeasurableSet (A i)) (hAS : ∀ i, DependsOnEdges (A i) (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepSet (fun i => {ω | (fun e => τ e ω) ∈ A i}) P := by
  apply (iIndepSet_iff_meas_biInter (fun i => (hA i).preimage
    (Measurable.of_eval h.measurable))).mpr
  intro t
  simpa only [ofPred_forall,Set.preimage] using disjoint_edge_events_inter_probability h t A S
    (fun i _ => hA i) (fun i _ => hAS i) (fun i _ j _ hij => hdis hij)

theorem disjoint_trials_failure_bound (h : ExponentialEnvironment P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)))
    (p : ℝ)
    (hprob : ∀ i ∈ t, p ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | ∀ i ∈ t, (fun e => τ e ω) ∉ A i} ≤ (1-p)^t.card := by
  classical
  let _ := h.probability
  have he := disjoint_edge_events_inter_probability h t (fun i => (A i)ᶜ) S
    (fun i hi => (hA i hi).compl) (fun i hi => (hAS i hi).compl) hdis
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_prod] at her
  change P.real _ = ∏ i ∈ t, P.real {ω | (fun e => τ e ω) ∉ A i} at her
  simp only [mem_compl_iff] at her
  rw [her]
  calc
    _ ≤ ∏ _i ∈ t, (1-p) := by
      apply Finset.prod_le_prod
      · intro i _; exact measureReal_nonneg
      · intro i hi
        have hm := (hA i hi).preimage (Measurable.of_eval h.measurable)
        have hc := measureReal_compl (μ := P) hm
        simp only [Set.preimage] at hc
        change P.real ({ω | (fun e => τ e ω) ∈ A i}ᶜ) ≤ _
        rw [hc]
        simpa using sub_le_sub_left (hprob i hi) 1
    _ = _ := by simp

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ExponentialTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Real Set MeasureTheory

theorem likelihood_second_moment_integral (ρ : ℝ) (hρ : 1 / 2 < ρ) :
    (∫ x : ℝ in Ioi 0, (exponentialLikelihood ρ x) ^ 2 * exp (-x)) =
      ρ ^ 2 / (2 * ρ - 1) := by
  have hfun : (fun x : ℝ => (exponentialLikelihood ρ x) ^ 2 * exp (-x)) =
      (fun x : ℝ => ρ ^ 2 * exp ((-(2 * ρ - 1)) * x)) := by
    funext x
    unfold exponentialLikelihood
    rw [mul_pow, ← exp_nat_mul, mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, exp_zero, neg_div_neg_eq]
  ring

theorem tilted_rate_second_moment (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    (∫ x : ℝ in Ioi 0, (exponentialLikelihood (1 / (1 - δ)) x) ^ 2 * exp (-x)) =
      1 / (1 - δ ^ 2) := by
  have hden : 0 < 1 - δ := by linarith
  have hrate : 1 / 2 < 1 / (1 - δ) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  rw [likelihood_second_moment_integral _ hrate]
  have hden' : 0 < 1 - δ ^ 2 := by nlinarith
  field_simp [ne_of_gt hden, ne_of_gt hden']
  ring_nf
  field_simp [show 1 + δ ≠ 0 by linarith]
  ring

theorem likelihood_power_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) (M : ℕ) :
    (1 / (1 - δ ^ 2)) ^ M ≤ exp (2 * M * δ ^ 2) := by
  have hden : 0 < 1 - δ ^ 2 := by nlinarith
  have hsmall : 0 ≤ 1 - 2 * δ ^ 2 := by nlinarith
  have hrat : 1 / (1 - δ ^ 2) ≤ 2 * δ ^ 2 + 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg δ) hsmall]
  have he : 1 / (1 - δ ^ 2) ≤ exp (2 * δ ^ 2) :=
    hrat.trans (add_one_le_exp _)
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 / (1 - δ ^ 2) by positivity) he M
  calc
    (1 / (1 - δ ^ 2)) ^ M ≤ exp (2 * δ ^ 2) ^ M := hp
    _ = exp (2 * M * δ ^ 2) := by rw [← exp_nat_mul]; congr 1; ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ExponentialTiltLaw
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem expMeasure_map_scale (α : ℝ) (hα : 0 < α) :
    Measure.map (fun x : ℝ => α*x) (expMeasure 1)=expMeasure (1/α) := by
  have hm : Measurable (fun x : ℝ => α*x) := by fun_prop
  let _ := isProbabilityMeasure_expMeasure (show 0 < 1/α by positivity)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hm measurableSet_Iic]
  have he : (fun y : ℝ => α*y) ⁻¹' Iic x=Iic (x/α) := by
    ext y
    simp only [mem_preimage,mem_Iic]
    rw [le_div_iff₀ hα,mul_comm]
  rw [he,← ofReal_cdf,← ofReal_cdf]
  congr 1
  rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ)<1),cdf_expMeasure_eq (by positivity : 0 < 1/α)]
  have hepos : (0 ≤ x/α) ↔ 0 ≤ x := by rw [le_div_iff₀ hα,zero_mul]
  simp only [hepos]
  simp [div_eq_mul_inv,mul_comm]

theorem exponential_likelihood_density (ρ : ℝ) (_hρ : 0 ≤ ρ) (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exponentialLikelihood ρ x)=exponentialPDF ρ x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold exponentialLikelihood
    simp only [one_mul]
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem expMeasure_withDensity_likelihood (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (expMeasure 1).withDensity (fun x => ENNReal.ofReal (exponentialLikelihood ρ x))=expMeasure ρ := by
  change (volume.withDensity (exponentialPDF 1)).withDensity _=volume.withDensity (exponentialPDF ρ)
  rw [← withDensity_mul volume (by unfold exponentialPDF; fun_prop)
    (by unfold exponentialLikelihood; fun_prop)]
  congr 1
  funext x
  exact exponential_likelihood_density ρ hρ x

theorem exponential_likelihood_square_density (ρ : ℝ) (hρ : 1/2 < ρ) (x : ℝ) :
    exponentialPDF 1 x * (ENNReal.ofReal (exponentialLikelihood ρ x))^2 =
      ENNReal.ofReal (ρ^2/(2*ρ-1))*exponentialPDF (2*ρ-1) x := by
  have hd : 0 < 2*ρ-1 := by linarith
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_pow (by unfold exponentialLikelihood; positivity),
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold exponentialLikelihood
    rw [mul_pow,← Real.exp_nat_mul]
    simp only [one_mul]
    rw [mul_left_comm,← Real.exp_add]
    have he : -x+2*(-(ρ-1)*x)= -((2*ρ-1)*x) := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he]
    have hd' : ρ*2-1 ≠ 0 := by linarith
    field_simp [hd']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_likelihood_second_moment (ρ : ℝ) (hρ : 1/2 < ρ) :
    (∫⁻ x, (ENNReal.ofReal (exponentialLikelihood ρ x))^2 ∂expMeasure 1)=
      ENNReal.ofReal (ρ^2/(2*ρ-1)) := by
  change (∫⁻ x, _ ∂volume.withDensity (exponentialPDF 1))=_
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by unfold exponentialLikelihood; fun_prop)]
  simp only [Pi.mul_apply,exponential_likelihood_square_density ρ hρ]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by linarith : 0 < 2*ρ-1),mul_one]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteTiltLaw
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

theorem probability_pi_lintegral_prod (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ)=∏ i, ∫⁻ y, f i y ∂μ i := by
  have hi : iIndepFun (fun i (x : ι → ℝ) => f i (x i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hh := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i), (measurePreserving_eval μ i).map_eq]

theorem indicator_pi_prod (s : ι → Set ℝ) (f : ι → ℝ → ℝ≥0∞) (x : ι → ℝ) :
    (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · have hh : x ∈ Set.univ.pi s := by simpa using hx
    rw [Set.indicator_of_mem hh]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem (hx i)]
  · obtain ⟨i,hi⟩ := not_forall.mp hx
    have hh : x ∉ Set.univ.pi s := by simpa using (not_forall.mpr ⟨i,hi⟩)
    rw [Set.indicator_of_notMem hh]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem measurable_finiteExponentialLikelihood (ρ : ℝ) :
    Measurable (finiteExponentialLikelihood (ι := ι) ρ) := by
  unfold finiteExponentialLikelihood exponentialLikelihood
  fun_prop

theorem finite_expMeasure_withDensity (ρ : ℝ) (hρ : 0 < ρ) :
    (Measure.pi (fun _ : ι => expMeasure 1)).withDensity (finiteExponentialLikelihood ρ)=
      Measure.pi (fun _ : ι => expMeasure ρ) := by
  let _ := isProbabilityMeasure_expMeasure hρ
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),← lintegral_indicator (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, (Set.univ.pi s).indicator (fun y => ∏ i, ENNReal.ofReal (exponentialLikelihood ρ (y i))) x
    ∂Measure.pi (fun _ : ι => expMeasure 1)) = _
  simp_rw [indicator_pi_prod s (fun _ x => ENNReal.ofReal (exponentialLikelihood ρ x))]
  rw [probability_pi_lintegral_prod _ (fun i => (s i).indicator (fun x => ENNReal.ofReal (exponentialLikelihood ρ x))) (fun i =>
    (by unfold exponentialLikelihood; fun_prop : Measurable (fun x => ENNReal.ofReal (exponentialLikelihood ρ x))).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i),← withDensity_apply _ (hs i),expMeasure_withDensity_likelihood ρ hρ.le]

theorem finite_expMeasure_map_scale (α : ℝ) (hα : 0 < α) :
    (Measure.pi (fun _ : ι => expMeasure 1)).map (fun x i => α*x i)=
      Measure.pi (fun _ : ι => expMeasure (1/α)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun x : ℝ => α*x)).aemeasurable)]
  simp only [expMeasure_map_scale α hα]

theorem finite_exponential_likelihood_second_moment (ρ : ℝ) (hρ : 1/2 < ρ) :
    (∫⁻ x, (finiteExponentialLikelihood (ι := ι) ρ x)^2 ∂Measure.pi (fun _ : ι => expMeasure 1))=
      (ENNReal.ofReal (ρ^2/(2*ρ-1)))^(Fintype.card ι) := by
  simp only [finiteExponentialLikelihood,← Finset.prod_pow]
  rw [probability_pi_lintegral_prod _ (fun _ x => (ENNReal.ofReal (exponentialLikelihood ρ x))^2)
    (fun _ => by unfold exponentialLikelihood; fun_prop)]
  simp only [exponential_likelihood_second_moment ρ hρ,Finset.prod_const,Finset.card_univ]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TiltComparison
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem withDensity_sq_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L : Ω → ℝ≥0∞) (hL : Measurable L)
    (A : Set Ω) (hA : MeasurableSet A) :
    ((P.withDensity L) A)^2 ≤ (∫⁻ x, (L x)^2 ∂P)*P A := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hL.aemeasurable (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) (P.restrict A))
  simp only [Pi.mul_apply,mul_one,ENNReal.rpow_two,one_pow,lintegral_one,
    Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  have hsqrt (x : ℝ≥0∞) : (x^(1/(2 : ℝ)))^2=x := by
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hh2 := pow_le_pow_left' hh 2
  rw [mul_pow,hsqrt,hsqrt] at hh2
  rw [withDensity_apply L hA]
  exact hh2.trans (mul_le_mul' (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl)

variable {ι : Type*} [Fintype ι]

theorem finite_expMeasure_probability_sq_bound (ρ : ℝ) (hρ : 1/2 < ρ)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : ι => expMeasure ρ)).real A ^ 2 ≤
      (ρ^2/(2*ρ-1))^(Fintype.card ι)*(Measure.pi (fun _ : ι => expMeasure 1)).real A := by
  have hh := withDensity_sq_le_second_moment (Measure.pi (fun _ : ι => expMeasure 1))
    (finiteExponentialLikelihood ρ) (measurable_finiteExponentialLikelihood ρ) A hA
  rw [finite_expMeasure_withDensity ρ (by linarith),finite_exponential_likelihood_second_moment ρ hρ] at hh
  have hfin : (ENNReal.ofReal (ρ^2/(2*ρ-1)))^(Fintype.card ι)*
      (Measure.pi (fun _ : ι => expMeasure 1)) A ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hr := ENNReal.toReal_mono hfin hh
  have hc : 0 ≤ ρ^2/(2*ρ-1) := div_nonneg (sq_nonneg ρ) (by linarith)
  simpa only [measureReal_def,ENNReal.toReal_pow,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using hr

theorem finite_scaled_expMeasure_probability_sq_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    ((Measure.pi (fun _ : ι => expMeasure 1)).map (fun x i => (1-δ)*x i)).real A ^ 2 ≤
      (1/(1-δ^2))^(Fintype.card ι)*(Measure.pi (fun _ : ι => expMeasure 1)).real A := by
  have hα : 0 < 1-δ := by linarith
  have hρ : 1/2 < 1/(1-δ) := by
    apply (lt_div_iff₀ hα).mpr
    linarith
  have he : (1/(1-δ))^2/(2*(1/(1-δ))-1)=1/(1-δ^2) := by
    have hi := tilted_rate_second_moment δ hδ hδ'
    rwa [likelihood_second_moment_integral _ hρ] at hi
  rw [finite_expMeasure_map_scale _ hα]
  simpa only [he] using finite_expMeasure_probability_sq_bound (1/(1-δ)) hρ A hA

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteEdgeTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem scaleFiniteEdges_event_iff (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ))
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    scaleFiniteEdges S α w ∈ A ↔ (fun e => α*w e) ∈ A := by
  apply hA
  intro e he
  simp [scaleFiniteEdges,he]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.finiteJointLaw (h : ExponentialEnvironment P τ) (S : Finset Edge) :
    P.map (fun ω (e : S) => τ e ω)=Measure.pi (fun _ : S => expMeasure 1) := by
  have hi := h.independent.precomp (Subtype.val_injective : Function.Injective (fun e : S => (e : Edge)))
  rw [iIndepFun.map_fun_eq_pi_map (fun e : S => (h.measurable e).aemeasurable) hi]
  simp only [h.marginal]

theorem finite_support_event_probability (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | (fun e => τ e ω) ∈ A}=
      (Measure.pi (fun _ : S => expMeasure 1)) ((extendEdgeWeights S) ⁻¹' A) := by
  rw [← h.finiteJointLaw S,Measure.map_apply (Measurable.of_eval (fun e : S => h.measurable e))
    (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  exact (hS.restriction_iff (fun e => τ e ω)).symm

theorem finite_support_scaled_event_probability (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
      ((Measure.pi (fun _ : S => expMeasure 1)).map (fun x e => α*x e))
        ((extendEdgeWeights S) ⁻¹' A) := by
  have hm : Measurable (fun ω (e : S) => α*τ e ω) :=
    Measurable.of_eval (fun e => measurable_const.mul (h.measurable e))
  rw [← h.finiteJointLaw S,Measure.map_map (by fun_prop)
    (Measurable.of_eval (fun e : S => h.measurable e))]
  change P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
    (P.map (fun ω (e : S) => α*τ e ω)) ((extendEdgeWeights S) ⁻¹' A)
  rw [Measure.map_apply hm (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  rw [mem_ofPred_eq,scaleFiniteEdges_event_iff S α A hS]
  exact (hS.restriction_iff (fun e => α*τ e ω)).symm

theorem finite_edge_tilt_probability_sq_bound (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      (1/(1-δ^2))^S.card * P.real {ω | (fun e => τ e ω) ∈ A} := by
  have hh := finite_scaled_expMeasure_probability_sq_bound δ hδ hδ'
    ((extendEdgeWeights S) ⁻¹' A) (hA.preimage (measurable_extendEdgeWeights S))
  unfold Measure.real at *
  rw [finite_support_scaled_event_probability h S (1-δ) A hA hS,
    finite_support_event_probability h S A hA hS]
  simpa only [Fintype.card_coe] using hh

theorem finite_edge_tilt_probability_sq_exp_bound (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      Real.exp (2*S.card*δ^2) * P.real {ω | (fun e => τ e ω) ∈ A} := by
  exact (finite_edge_tilt_probability_sq_bound h S δ hδ hδ' A hA hS).trans
    (mul_le_mul_of_nonneg_right (likelihood_power_bound δ hδ hδ' S.card) measureReal_nonneg)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialModulus
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

theorem latticeBox_card (n : ℕ) : (latticeBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [latticeBox, hi, pow_two]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SquareLoops
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

namespace SquareLoop
variable {m : ℕ}

theorem sum_delta (c : SquareLoop m) : ∑ i, (c.side i).2.delta = 0 := by
  have h := congrArg (fun f : Fin m → Vertex => ∑ i, f i) (funext c.follows)
  simp only [SquareSide.head, sum_add_distrib] at h
  rw [Equiv.sum_comp (finRotate m) (fun i => (c.side i).tail)] at h
  exact add_left_cancel (show (∑ i, (c.side i).tail) + (∑ i, (c.side i).2.delta) =
      (∑ i, (c.side i).tail) + 0 by simpa using h.symm)

theorem upLeft_count (c : SquareLoop m) : m = 2 * c.upLeftIndices.card := by
  have hx := congrArg Prod.fst c.sum_delta
  have hy := congrArg Prod.snd c.sum_delta
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero] at hx hy
  have hd (i : Fin m) : (1 : ℤ) =
      2 * (if (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west then 1 else 0) -
        ((c.side i).2.delta.2 - (c.side i).2.delta.1) := by
    cases h : (c.side i).2 <;> simp [Step.delta]
  have hs := sum_congr (s₁ := (univ : Finset (Fin m))) rfl (fun i _ => hd i)
  simp only [sum_sub_distrib, hx, hy, sub_zero, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hc : (∑ i : Fin m,
      if (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west then (1 : ℤ) else 0) =
      c.upLeftIndices.card := by
    simp [upLeftIndices, sum_boole]
  rw [← mul_sum, hc] at hs
  exact_mod_cast hs

theorem length_le_eight_badSites (c : SquareLoop m) (hc : c.NoRepeatedSides) :
    m ≤ 8*c.badSites.card := by
  have hs : c.upLeftIndices.image c.side ⊆ c.badSites ×ˢ (univ : Finset Step) := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_product.mpr ⟨mem_image.mpr ⟨i,hi,rfl⟩, mem_univ _⟩
  have hn : (c.upLeftIndices.image c.side).card = c.upLeftIndices.card :=
    card_image_of_injective _ hc
  have hcard := card_le_card hs
  rw [hn, card_product] at hcard
  have hfour : (univ : Finset Step).card = 4 := by decide
  rw [hfour] at hcard
  have hh := c.upLeft_count
  omega

end SquareLoop

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ContourEnumeration
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

theorem enclosingLoop_card (n : ℕ) :
    Fintype.card (EnclosingLoop n) ≤ 9*(n+2)^2*4^(n+1) := by
  have hh := Fintype.card_le_of_injective _ (enclosingLoopCode_injective n)
  have hf : Fintype.card Step = 4 := by decide
  simp only [Fintype.card_prod, Fintype.card_coe, latticeBox_card,
    Fintype.card_fun, Fintype.card_fin, hf] at hh
  have hsq : (2*(n+2)+1)^2 ≤ 9*(n+2)^2 := by
    calc
      _ ≤ (3*(n+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  exact hh.trans (Nat.mul_le_mul_right _ hsq)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_OrientedCompactness
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory

theorem orientedSurvival_pred (G : Vertex → Prop) (p : Vertex) (n : ℕ)
    (h : orientedSurvival G p (n+1)) : orientedSurvival G p n := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
    refine ⟨h.1,?_⟩
    rcases h.2 with he | hn
    · exact Or.inl (ih _ he)
    · exact Or.inr (ih _ hn)

theorem orientedSurvival_mono (G : Vertex → Prop) (p : Vertex) {m n : ℕ}
    (hmn : m ≤ n) (h : orientedSurvival G p n) : orientedSurvival G p m := by
  induction n,hmn using Nat.le_induction with
  | base => exact h
  | succ n hmn ih => exact ih (orientedSurvival_pred G p n h)

theorem oriented_surviving_successor (G : Vertex → Prop) (p : Vertex)
    (h : ∀ n, orientedSurvival G p n) :
    (∀ n, orientedSurvival G (p+(1,0)) n) ∨ (∀ n, orientedSurvival G (p+(0,1)) n) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨m,hm⟩,⟨n,hn⟩⟩ := hn
  rcases (h (max m n+1)).2 with he | he
  · exact hm (orientedSurvival_mono G _ (le_max_left _ _) he)
  · exact hn (orientedSurvival_mono G _ (le_max_right _ _) he)

theorem infiniteOrientedPath_iff (G : Vertex → Prop) (p : Vertex) :
    infiniteOrientedPath G p ↔ ∀ n, orientedSurvival G p n := by
  classical
  constructor
  · rintro ⟨z,hz,hstep,hG⟩
    have hh (n m : ℕ) : orientedSurvival G (z m) n := by
      induction n generalizing m with
      | zero => trivial
      | succ n ih =>
        refine ⟨hG m,?_⟩
        have ht := ih (m+1)
        rcases hstep m with he | he
        · exact Or.inl (he ▸ ht)
        · exact Or.inr (he ▸ ht)
    intro n
    simpa [hz] using hh n 0
  · intro h
    let V := {q : Vertex // ∀ n, orientedSurvival G q n}
    have next (q : V) : ∃ r : V, r.val=q.val+(1,0) ∨ r.val=q.val+(0,1) := by
      rcases oriented_surviving_successor G q.val q.property with he | hn
      · exact ⟨⟨q.val+(1,0),he⟩,Or.inl rfl⟩
      · exact ⟨⟨q.val+(0,1),hn⟩,Or.inr rfl⟩
    let step (q : V) : V := (next q).choose
    let z : ℕ → V := Nat.rec ⟨p,h⟩ (fun _ q => step q)
    refine ⟨fun n => (z n).val,rfl,?_,?_⟩
    · intro n
      exact (next (z n)).choose_spec
    · intro n
      exact ((z n).property 1).1

theorem orientedEndpoints_nonempty_iff (G : Vertex → Prop) (p : Vertex) (n : ℕ) :
    (orientedEndpoints G p n).Nonempty ↔ orientedSurvival G p n := by
  classical
  induction n generalizing p with
  | zero => simp [orientedEndpoints,orientedSurvival]
  | succ n ih =>
    by_cases hg : G p <;> simp [orientedEndpoints,orientedSurvival,hg,Finset.union_nonempty,ih]

theorem orientedReachable_finite_of_no_infinite_path (G : Vertex → Prop) (p : Vertex)
    (h : ¬infiniteOrientedPath G p) : (orientedReachable G p).Finite := by
  classical
  rw [infiniteOrientedPath_iff] at h
  push Not at h
  obtain ⟨N,hN⟩ := h
  have hs : orientedReachable G p ⊆ ((Finset.range N).biUnion (orientedEndpoints G p) : Set Vertex) := by
    intro q hq
    obtain ⟨n,hn⟩ := mem_iUnion.mp hq
    have hsurv := (orientedEndpoints_nonempty_iff G p n).mp ⟨q,hn⟩
    have hnN : n < N := by
      by_contra hnN
      exact hN (orientedSurvival_mono G p (by omega) hsurv)
    exact mem_biUnion.mpr ⟨n,mem_range.mpr hnN,hn⟩
  exact (Finset.finite_toSet _).subset hs

theorem orientedReachable_origin (G : Vertex → Prop) (p : Vertex) : p ∈ orientedReachable G p := by
  exact mem_iUnion.mpr ⟨0,by simp [orientedEndpoints]⟩

theorem orientedEndpoints_extend (G : Vertex → Prop) (p q : Vertex) (n : ℕ)
    (hq : q ∈ orientedEndpoints G p n) (hg : G q) :
    q+(1,0) ∈ orientedEndpoints G p (n+1) ∧ q+(0,1) ∈ orientedEndpoints G p (n+1) := by
  classical
  induction n generalizing p with
  | zero =>
    have he : q=p := by simpa [orientedEndpoints] using hq
    subst q
    simp [orientedEndpoints,hg]
  | succ n ih =>
    by_cases hp : G p
    · simp only [orientedEndpoints,ite_eq_left hp,Finset.mem_union] at hq ⊢
      rcases hq with he | hn
      · obtain ⟨h1,h2⟩ := ih _ he
        exact ⟨Or.inl h1,Or.inl h2⟩
      · obtain ⟨h1,h2⟩ := ih _ hn
        exact ⟨Or.inr h1,Or.inr h2⟩
    · simp [orientedEndpoints,hp] at hq

theorem orientedReachable_forward (G : Vertex → Prop) (p q : Vertex)
    (hq : q ∈ orientedReachable G p) (hg : G q) :
    q+(1,0) ∈ orientedReachable G p ∧ q+(0,1) ∈ orientedReachable G p := by
  obtain ⟨n,hn⟩ := mem_iUnion.mp hq
  obtain ⟨h1,h2⟩ := orientedEndpoints_extend G p q n hn hg
  exact ⟨mem_iUnion.mpr ⟨n+1,h1⟩,mem_iUnion.mpr ⟨n+1,h2⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_orientedSurvival (G : Vertex → Set Ω) (hG : ∀ p, MeasurableSet (G p))
    (p : Vertex) (n : ℕ) : MeasurableSet {ω | orientedSurvival (fun v => ω ∈ G v) p n} := by
  induction n generalizing p with
  | zero => simp [orientedSurvival]
  | succ n ih =>
    exact (hG p).inter ((ih (p+(1,0))).union (ih (p+(0,1))))

theorem measurableSet_infiniteOrientedPath (G : Vertex → Set Ω) (hG : ∀ p, MeasurableSet (G p))
    (p : Vertex) : MeasurableSet {ω | infiniteOrientedPath (fun v => ω ∈ G v) p} := by
  simp only [infiniteOrientedPath_iff,ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_orientedSurvival G hG p n)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SeparatedSelection
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set

theorem separated_selection {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ a, R a a) (hsymm : ∀ a b, R a b → R b a)
    (S : Finset α) (d : ℕ)
    (hdegree : ∀ a ∈ S, (S.filter (R a)).card ≤ d) :
    ∃ T : Finset α, T ⊆ S ∧
      Set.Pairwise (↑T : Set α) (fun a b => ¬R a b) ∧ S.card ≤ d*T.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S.Nonempty
    · obtain ⟨a,ha⟩ := hs
      let U := S.filter (fun b => ¬R a b)
      have hu : U ⊆ S := filter_subset _ _
      have hau : a ∉ U := by simp [U,hrefl]
      have hlt : U ⊂ S := ⟨hu,by intro hh; exact hau (hh ha)⟩
      have hdu : ∀ b ∈ U, (U.filter (R b)).card ≤ d := by
        intro b hb
        exact (Finset.card_le_card (filter_subset_filter _ hu)).trans (hdegree b (hu hb))
      obtain ⟨T,hT,hpair,hcard⟩ := ih U hlt hdu
      have hat : a ∉ T := fun hh => hau (hT hh)
      refine ⟨insert a T,?_,?_,?_⟩
      · intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · exact ha
        · exact hu (hT hb)
      · intro b hb c hc hbc
        rcases mem_insert.mp hb with rfl | hbT
        · rcases mem_insert.mp hc with rfl | hcT
          · exact False.elim (hbc rfl)
          · exact (mem_filter.mp (hT hcT)).2
        · rcases mem_insert.mp hc with rfl | hcT
          · intro hr
            exact (mem_filter.mp (hT hbT)).2 (hsymm _ _ hr)
          · exact hpair hbT hcT hbc
      · have hsplit : (S.filter (R a)).card+U.card=S.card := by
          exact card_filter_add_card_filter_not (R a)
        rw [card_insert_of_notMem hat]
        have hd := hdegree a ha
        nlinarith
    · have he : S=∅ := not_nonempty_iff_eq_empty.mp hs
      subst S
      exact ⟨∅,Finset.Subset.rfl,by simp,by simp⟩

theorem latticeNear_refl (k : ℕ) (p : Vertex) : latticeNear k p p := by
  simp [latticeNear]

theorem latticeNear_symm (k : ℕ) (p q : Vertex) : latticeNear k p q ↔ latticeNear k q p := by
  have h0 : p.1-q.1 = -(q.1-p.1) := by omega
  have h1 : p.2-q.2 = -(q.2-p.2) := by omega
  simp only [latticeNear,h0,h1,Int.natAbs_neg]

theorem near_filter_card_le (S : Finset Vertex) (k : ℕ) (p : Vertex) :
    (S.filter (latticeNear k p)).card ≤ (2*k+1)^2 := by
  classical
  have hs : S.filter (latticeNear k p) ⊆ (latticeBox k).image (fun q => p+q) := by
    intro q hq
    obtain ⟨hq0,hq1⟩ := (mem_filter.mp hq).2
    have hmem : q-p ∈ latticeBox k := by
      simp only [latticeBox,mem_product,Finset.mem_Icc,Prod.fst_sub,Prod.snd_sub]
      constructor <;> omega
    exact mem_image.mpr ⟨q-p,hmem,by abel⟩
  exact (Finset.card_le_card hs).trans ((card_image_le).trans_eq (latticeBox_card k))

theorem lattice_separated_selection (S : Finset Vertex) (k : ℕ) :
    ∃ T : Finset Vertex, T ⊆ S ∧
      Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) ∧
      S.card ≤ (2*k+1)^2*T.card := by
  exact separated_selection (latticeNear k) (latticeNear_refl k)
    (fun p q => (latticeNear_symm k p q).mp) S ((2*k+1)^2)
    (fun p _ => near_filter_card_le S k p)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EnclosingContour
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

theorem exists_enclosing_squareLoop (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.NoRepeatedSides ∧ c.winding ≠ 0 ∧ ∀ i, IsBoundarySide S (c.side i) := by
  classical
  obtain ⟨x,hn,hpos,_,hnext,hw⟩ := exists_boundary_cycle S h0
  let es := (boundaryPerm S).toList x
  have hlen : 0 < es.length := hpos
  have : NeZero es.length := ⟨Nat.ne_of_gt hlen⟩
  let c : SquareLoop es.length :=
    { side := fun i => (es.get i).val
      follows := by
        intro i
        have hh := hnext (es.get i) (List.get_mem es i)
        change (es.next es[i.val] (List.get_mem es i)).val.tail = es[i.val].val.head at hh
        rw [List.next_getElem es hn i.val i.isLt] at hh
        simpa only [List.get_eq_getElem, finRotate_apply, Fin.val_add,
          Fin.val_one', Nat.add_mod_mod] using hh }
  refine ⟨es.length,hlen,c,?_,?_,?_⟩
  · exact Subtype.val_injective.comp hn.injective_get
  · change (∑ i : Fin es.length, (es.get i).val.rayCross) ≠ 0
    have hh : (∑ i : Fin es.length, (es.get i).val.rayCross) =
        ∑ e ∈ es.toFinset, e.val.rayCross := by
      rw [List.sum_toFinset _ hn, ← Fin.sum_ofFn]
      have hmap : List.map (fun e : BoundarySide S => e.val.rayCross) (List.ofFn es.get) =
          List.ofFn (fun i => (es.get i).val.rayCross) := List.map_ofFn
      simpa only [List.ofFn_get] using congrArg List.sum hmap.symm
    rw [hh]
    exact hw
  · intro i
    exact (mem_boundarySides S _).mp (es.get i).property

theorem SquareLoop.badSites_bad {m : ℕ} (c : SquareLoop m)
    (S : Finset Vertex) (G : Vertex → Prop)
    (hb : ∀ i, IsBoundarySide S (c.side i))
    (hforward : ∀ q ∈ S, G q → q+(1,0) ∈ S ∧ q+(0,1) ∈ S) :
    ∀ q ∈ c.badSites, ¬G q := by
  intro q hq hg
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
  have hf := hforward _ (hb i).1 hg
  have hout := (hb i).2
  rcases (mem_filter.mp hi).2 with hd | hd
  · exact hout (by simpa [hd,Step.outward,Step.right,Step.delta] using hf.1)
  · exact hout (by simpa [hd,Step.outward,Step.right,Step.delta] using hf.2)

theorem no_infinite_path_enclosing_contour (G : Vertex → Prop) (k : ℕ)
    (h : ¬infiniteOrientedPath G 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.NoRepeatedSides ∧ c.winding ≠ 0 ∧
      (∀ q ∈ c.badSites, ¬G q) ∧
      ∃ T : Finset Vertex, T ⊆ c.badSites ∧
        Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) ∧
        m ≤ 8*(2*k+1)^2*T.card := by
  classical
  let hf := orientedReachable_finite_of_no_infinite_path G 0 h
  let S := hf.toFinset
  have hS (q : Vertex) : q ∈ S ↔ q ∈ orientedReachable G 0 := hf.mem_toFinset
  have h0 : (0 : Vertex) ∈ S := (hS 0).mpr (orientedReachable_origin G 0)
  obtain ⟨m,hm,c,hc,hw,hb⟩ := exists_enclosing_squareLoop S h0
  refine ⟨m,hm,c,hc,hw,?_,?_⟩
  · apply c.badSites_bad S G hb
    intro q hq hg
    have hh := orientedReachable_forward G 0 q ((hS q).mp hq) hg
    exact ⟨(hS _).mpr hh.1,(hS _).mpr hh.2⟩
  · obtain ⟨T,hT,hpair,hcard⟩ := lattice_separated_selection c.badSites k
    refine ⟨T,hT,hpair,?_⟩
    have hh := c.length_le_eight_badSites hc
    nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_OrientedProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem independent_complement_inter {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hi : iIndepSet A P) :
    P {ω | ∀ i, ω ∉ A i} = ∏ i, P (A i)ᶜ := by
  have hh := (iIndepSet_iff_iIndep A P).mp hi
  have hm (i : ι) : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i)ᶜ :=
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton (A i))).compl
  have he := hh.meas_iInter hm
  have heq : {ω | ∀ i, ω ∉ A i} = ⋂ i, (A i)ᶜ := by ext ω; simp
  rw [heq]
  exact he

theorem contour_bad_probability {m : ℕ} (c : SquareLoop m)
    (hc : c.NoRepeatedSides) (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (q : ℝ≥0∞) (hq : q ≤ 1)
    (hbad : ∀ v, P (G v)ᶜ ≤ q^(8*(2*k+1)^2)) :
    P {ω | ∀ v ∈ c.badSites, ω ∉ G v} ≤ q^m := by
  classical
  obtain ⟨T,hT,hpair,hcard⟩ := lattice_separated_selection c.badSites k
  have hlen : m ≤ (8*(2*k+1)^2)*T.card := by
    have hh := c.length_le_eight_badSites hc
    nlinarith
  calc
    _ ≤ P {ω | ∀ v : T, ω ∉ G v.val} := by
      apply measure_mono
      intro ω hω v
      exact hω v.val (hT v.property)
    _ = ∏ v : T, P (G v.val)ᶜ := independent_complement_inter _ (hind T hpair)
    _ ≤ ∏ _v : T, q^(8*(2*k+1)^2) := by
      apply Finset.prod_le_prod'
      intro v hv
      exact hbad v.val
    _ = q^((8*(2*k+1)^2)*T.card) := by simp [← pow_mul]
    _ ≤ q^m := pow_le_pow_right_of_le_one' hq hlen

theorem enclosingLoop_card_geometric (n : ℕ) :
    Fintype.card (EnclosingLoop n) ≤ 9*16^(n+1) := by
  have hp (n : ℕ) : n+2 ≤ 2^(n+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      omega
  have hsq : (n+2)^2 ≤ 4^(n+1) := by
    calc
      _ ≤ (2^(n+1))^2 := Nat.pow_le_pow_left (hp n) 2
      _ = (2^2)^(n+1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm (n+1) 2]
      _ = _ := by norm_num
  calc
    _ ≤ 9*(n+2)^2*4^(n+1) := enclosingLoop_card n
    _ ≤ 9*(4^(n+1))*4^(n+1) := by gcongr
    _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_HighDensityOriented
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] in
theorem no_infinite_path_subset_contours (G : Vertex → Set Ω) :
    {ω | ¬infiniteOrientedPath (fun v => ω ∈ G v) 0} ⊆
      ⋃ n : ℕ, ⋃ c : EnclosingLoop n, badContourEvent G c := by
  intro ω hω
  obtain ⟨m,hm,c,hn,hw,hbad,_⟩ :=
    no_infinite_path_enclosing_contour (fun v => ω ∈ G v) 0 hω
  cases m with
  | zero => omega
  | succ n =>
    exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨c,hw,hn⟩,hbad⟩⟩

omit [IsProbabilityMeasure P] in
theorem bad_contours_fixed_length (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) (n : ℕ) :
    P (⋃ c : EnclosingLoop n, badContourEvent G c) ≤
      9*(1/64 : ℝ≥0∞)^(n+1) := by
  classical
  have hc (c : EnclosingLoop n) : P (badContourEvent G c) ≤ (1/1024 : ℝ≥0∞)^(n+1) :=
    contour_bad_probability c.val c.property.2 G k hind _ (by norm_num) hbad
  have hcard : (Fintype.card (EnclosingLoop n) : ℝ≥0∞) ≤ 9*16^(n+1) := by
    exact_mod_cast enclosingLoop_card_geometric n
  calc
    _ ≤ ∑' c : EnclosingLoop n, P (badContourEvent G c) := measure_iUnion_le _
    _ = ∑ c : EnclosingLoop n, P (badContourEvent G c) := tsum_fintype _
    _ ≤ ∑ _c : EnclosingLoop n, (1/1024 : ℝ≥0∞)^(n+1) := sum_le_sum (fun c _ => hc c)
    _ = (Fintype.card (EnclosingLoop n) : ℝ≥0∞)*(1/1024)^(n+1) := by simp [nsmul_eq_mul]
    _ ≤ (9*16^(n+1))*(1/1024 : ℝ≥0∞)^(n+1) := by simpa only [mul_comm] using mul_le_mul_right hcard ((1/1024 : ℝ≥0∞)^(n+1))
    _ = _ := by
      rw [mul_assoc, ← mul_pow]
      have he : (16 : ℝ≥0∞)*(1/1024) = 1/64 := by
        apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by norm_num) (by norm_num)) (by simp)).mp
        norm_num
      rw [he]

omit [IsProbabilityMeasure P] in

theorem no_infinite_path_probability (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) :
    P {ω | ¬infiniteOrientedPath (fun v => ω ∈ G v) 0} ≤ (1/7 : ℝ≥0∞) := by
  calc
    _ ≤ P (⋃ n : ℕ, ⋃ c : EnclosingLoop n, badContourEvent G c) :=
      measure_mono (no_infinite_path_subset_contours G)
    _ ≤ ∑' n : ℕ, P (⋃ c : EnclosingLoop n, badContourEvent G c) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, 9*(1/64 : ℝ≥0∞)^(n+1) :=
      ENNReal.tsum_le_tsum (bad_contours_fixed_length G k hind hbad)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      have hlt : (1/64 : ℝ≥0∞) < 1 := by norm_num
      have hsub : (1 - 1/64 : ℝ≥0∞) ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hlt)
      apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by norm_num) (by simpa using hsub))) (by simp)).mp
      norm_num [ENNReal.toReal_sub_of_le hlt.le]

theorem high_density_oriented_paths (G : Vertex → Set Ω)
    (hG : ∀ v, MeasurableSet (G v)) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) :
    0 < P {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  have hb := no_infinite_path_probability G k hind hbad
  have hm := measurableSet_infiniteOrientedPath G hG 0
  by_contra hn
  have hz : P {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} = 0 :=
    le_antisymm (le_of_not_gt hn) bot_le
  change P ({ω | infiniteOrientedPath (fun v => ω ∈ G v) 0}ᶜ) ≤ _ at hb
  rw [measure_compl hm (measure_ne_top P _), measure_univ, hz] at hb
  norm_num at hb

theorem high_density_oriented_paths_real_bound (k : ℕ) (G : Vertex → Set Ω)
    (hG : ∀ v, MeasurableSet (G v)) (hi : SeparatedGoodIndependent P G k)
    (hb : ∀ v, P.real (G v)ᶜ ≤ (1/1024 : ℝ)^(8*(2*k+1)^2)) :
    0 < P.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  have hb' (v : Vertex) : P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2) := by
    have hh := ENNReal.ofReal_le_ofReal (hb v)
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)] at hh
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/1024),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1024),
      ENNReal.ofReal_one, ENNReal.ofReal_natCast] using hh
  have hp := high_density_oriented_paths G hG k hi hb'
  exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top P _)

theorem high_density_oriented_paths_uniform (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ (Ω' : Type*) [MeasurableSpace Ω']
      (P' : Measure Ω') [IsProbabilityMeasure P'] (G : Vertex → Set Ω'),
      (∀ v, MeasurableSet (G v)) → SeparatedGoodIndependent P' G k →
      (∀ v, P'.real (G v)ᶜ ≤ ζ) →
      0 < P'.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  refine ⟨(1/1024 : ℝ)^(8*(2*k+1)^2),pow_pos (by norm_num) _,?_⟩
  intro Ω' _ P' _ G hG hi hb
  exact high_density_oriented_paths_real_bound k G hG hi hb

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem internalEdges_card_le (V : Finset Vertex) : (internalEdges V).card ≤ 2*V.card := by
  have h := Finset.card_filter_le (s := V ×ˢ (Finset.univ : Finset Bool)) (fun e => edgeEnd e ∈ V)
  simpa [internalEdges,Nat.mul_comm] using h

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem internalEdges_disjoint {V W : Finset Vertex} (h : Disjoint V W) :
    Disjoint (internalEdges V) (internalEdges W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_internalEdges e V |>.mp he).1
    (mem_internalEdges e W |>.mp hf).1

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem measurableSet_boundedLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (boundedLocalizedEvent V family bound) := by
  simpa only [boundedLocalizedEvent,and_assoc] using
    measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem strictLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (strictLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem boundedLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (boundedLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem strip_vertices_disjoint (V W : Finset Vertex) (b y z R : ℝ)
    (hV : ∀ v ∈ V, |transverse b v-y| ≤ R)
    (hW : ∀ v ∈ W, |transverse b v-z| ≤ R)
    (hsep : 2*R < |y-z|) : Disjoint V W := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have ht := abs_add_le (y-transverse b v) (transverse b v-z)
  rw [sub_add_sub_cancel,abs_sub_comm y (transverse b v)] at ht
  have h1 := hV v hv
  have h2 := hW v hw
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFastGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem centers_close_of_point (a b t R : ℝ)
    (ha : |t-a| ≤ R) (hb : |t-b| ≤ R) : |a-b| ≤ 2*R := by
  have hh := abs_sub_le (t-b) 0 (t-a)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  have he : (t-b)-(t-a)=a-b := by ring
  rw [he] at hh
  linarith

theorem blockRegion_common_indices (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S)
    (v w p : Vertex) (hv : p ∈ blockRegion b A n d σ S v)
    (hw : p ∈ blockRegion b A n d σ S w) :
    |((blockLayer v-blockLayer w : ℤ) : ℝ)| ≤ 2*(A+3) ∧
    |((blockLevel v-blockLevel w : ℤ) : ℝ)| ≤ 8 := by
  have hx := centers_close_of_point _ _ _ _ hv.1 hw.1
  have hy := centers_close_of_point _ _ _ _ hv.2 hw.2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hxx : |(blockX n d v : ℝ)-(blockX n d w : ℝ)| =
      |((blockLayer v-blockLayer w : ℤ) : ℝ)| *((n : ℝ)+d) := by
    simp only [blockX, Int.cast_mul, Int.cast_add, Int.cast_sub]
    rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+d)]
  have hyy : |blockY σ S v-blockY σ S w| =
      |((blockLevel v-blockLevel w : ℤ) : ℝ)| *S := by
    have he : blockY σ S v-blockY σ S w =
        σ*((blockLevel v : ℝ)-(blockLevel w : ℝ))*S := by unfold blockY; ring
    rw [he,abs_mul,abs_mul,hσ,one_mul,abs_of_pos hS,Int.cast_sub]
  rw [hxx] at hx
  rw [hyy] at hy
  constructor
  · nlinarith [mul_nonneg (abs_nonneg (((blockLayer v-blockLayer w : ℤ) : ℝ))) hd']
  · nlinarith

theorem blockRegion_common_near (b A : ℝ) (n d : ℤ) (σ S : ℝ) (k : ℕ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S)
    (hA : 0 ≤ A+3) (hk : 4*(A+3)+8 ≤ k)
    (v w p : Vertex) (hv : p ∈ blockRegion b A n d σ S v)
    (hw : p ∈ blockRegion b A n d σ S w) : latticeNear k v w := by
  obtain ⟨hi,hj⟩ := blockRegion_common_indices b A n d σ S hn hd hσ hS v w p hv hw
  have he1 : ((v.1-w.1 : ℤ) : ℝ) =
      2*((blockLayer v-blockLayer w : ℤ) : ℝ)-((blockLevel v-blockLevel w : ℤ) : ℝ) := by
    simp [blockLayer,blockLevel]; ring
  have he2 : ((v.2-w.2 : ℤ) : ℝ) =
      ((blockLevel v-blockLevel w : ℤ) : ℝ)-((blockLayer v-blockLayer w : ℤ) : ℝ) := by
    simp [blockLayer,blockLevel]; ring
  have hx : |((v.1-w.1 : ℤ) : ℝ)| ≤ k := by
    rw [he1]
    have hh := abs_sub_le (2*((blockLayer v-blockLayer w : ℤ) : ℝ)) 0
      (((blockLevel v-blockLevel w : ℤ) : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hh
    linarith
  have hy : |((v.2-w.2 : ℤ) : ℝ)| ≤ k := by
    rw [he2]
    have hh := abs_sub_le (((blockLevel v-blockLevel w : ℤ) : ℝ)) 0
      (((blockLayer v-blockLayer w : ℤ) : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith
  have hx' : -(k : ℤ) ≤ v.1-w.1 ∧ v.1-w.1 ≤ k := by
    constructor
    · exact_mod_cast (abs_le.mp hx).1
    · exact_mod_cast (abs_le.mp hx).2
  have hy' : -(k : ℤ) ≤ v.2-w.2 ∧ v.2-w.2 ≤ k := by
    constructor
    · exact_mod_cast (abs_le.mp hy).1
    · exact_mod_cast (abs_le.mp hy).2
  dsimp [latticeNear]
  omega

theorem blockRegion_disjoint (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (v w : Vertex) (hvw : ¬latticeNear (⌈4*(A+3)+8⌉₊+1) v w) :
    Disjoint (blockRegion b A n d σ S v) (blockRegion b A n d σ S w) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  apply hvw
  apply blockRegion_common_near b A n d σ S _ hn hd hσ hS (by linarith) _ v w p hp hq
  have hh := Nat.le_ceil (4*(A+3)+8)
  push_cast
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set MeasureTheory Filter
open scoped Topology

theorem measurableSet_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) : MeasurableSet (allPairsRegionEvent V I J bound) := by
  simp only [allPairsRegionEvent,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun q => MeasurableSet.iInter (fun _ =>
      measurableSet_boundedLocalizedEvent V _ _))))

theorem allPairsRegionEvent_depends (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) :
    DependsOnEdges (allPairsRegionEvent V I J bound) (internalEdges V) := by
  intro w w' hh
  simp only [allPairsRegionEvent,mem_ofPred_eq]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  exact boundedLocalizedEvent_depends V _ _ w w' hh

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTrialGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem nearest_integer_error (t : ℝ) : |(⌊t+1/2⌋ : ℝ)-t| ≤ 1/2 := by
  have hlo := Int.floor_le (t+1/2)
  have hhi := Int.lt_floor_add_one (t+1/2)
  apply abs_le.mpr
  constructor <;> linarith

theorem trialTranslate_error (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) :
    |transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)| ≤ 1/2 := by
  have hh := nearest_integer_error (b*X+Y+trialOffset M R s j)
  convert hh using 1
  simp [trialTranslate,transverse]
  congr 1
  ring

theorem trialSpacing_bounds (R s : ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    1 ≤ trialSpacing R s ∧ R*s ≤ trialSpacing R s := by
  have hc := Nat.le_ceil s
  have hn : (1 : ℝ) ≤ (⌈s⌉₊ : ℝ) := by linarith
  unfold trialSpacing
  constructor
  · nlinarith
  · nlinarith

theorem trialOffset_bound (M : ℕ) (R s : ℝ) (j : Fin M)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    |trialOffset M R s j| ≤ 3*M*trialSpacing R s := by
  have hB := (trialSpacing_bounds R s hR hs).1
  have hj : (j.val : ℝ)+1 ≤ M := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have ha : |2*((j.val : ℝ)+1)-(M : ℝ)-1| ≤ M := by
    apply abs_le.mpr
    constructor <;> linarith
  unfold trialOffset
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<3),abs_of_nonneg (show 0 ≤ trialSpacing R s by linarith)]
  nlinarith

theorem trial_strip_in_window (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (p : Vertex) (hp : |transverse b p-transverse b (trialTranslate b X Y M R s j)| ≤ R*s) :
    |transverse b p-Y| ≤ trialWindow M R s/4 := by
  have he := trialTranslate_error b X Y M R s j
  have ho := trialOffset_bound M R s j hR hs
  have hB := trialSpacing_bounds R s hR hs
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast j.pos
  have hh := abs_add_le
    (transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j))
    (trialOffset M R s j)
  have heq : transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)+
      trialOffset M R s j = transverse b (trialTranslate b X Y M R s j)-Y := by ring
  rw [heq] at hh
  have ht := abs_add_le (transverse b p-transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s j)-Y)
  rw [sub_add_sub_cancel] at ht
  unfold trialWindow
  nlinarith [mul_le_mul_of_nonneg_right hM (by linarith : 0 ≤ trialSpacing R s)]

theorem trial_centers_separated (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j l : Fin M) (hjl : j ≠ l) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    2*R*s < |transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l)| := by
  have hB := trialSpacing_bounds R s hR hs
  have he := trialTranslate_error b X Y M R s j
  have hf := trialTranslate_error b X Y M R s l
  have he' := abs_le.mp he
  have hf' := abs_le.mp hf
  have hdiff : trialOffset M R s j-trialOffset M R s l =
      6*((j.val : ℝ)-(l.val : ℝ))*trialSpacing R s := by unfold trialOffset; ring
  have hne : j.val ≠ l.val := fun hh => hjl (Fin.ext hh)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : (j.val : ℝ)+1 ≤ l.val := by exact_mod_cast hlt
    have ha := neg_le_abs (transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l))
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ trialSpacing R s)]
  · have hn : (l.val : ℝ)+1 ≤ j.val := by exact_mod_cast hgt
    have ha := le_abs_self (transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l))
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ trialSpacing R s)]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TiltedRegions
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem block_supported_tests_independent (h : ExponentialEnvironment P τ)
    (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (E : Vertex → Set (Edge → ℝ)) (hE : ∀ v, MeasurableSet (E v))
    (hsupport : ∀ v, DependsOnEdges (E v) (internalEdges (blockVertices b A n d σ S v))) :
    SeparatedGoodIndependent P (fun v => {ω | (fun e => τ e ω) ∈ E v})
      (⌈4*(A+3)+8⌉₊+1) := by
  intro T hT
  apply disjoint_edge_events_iIndepSet h (fun v : T => E v.val)
    (fun v : T => internalEdges (blockVertices b A n d σ S v.val))
    (fun v => hE v.val) (fun v => hsupport v.val)
  intro v w hvw
  apply internalEdges_disjoint
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hsep := hT v.property w.property (fun hh => hvw (Subtype.ext hh))
  exact Set.disjoint_left.mp (blockRegion_disjoint b A n d σ S hn hd hσ hS hA v.val w.val hsep)
    ((mem_blockVertices ..).mp hp) ((mem_blockVertices ..).mp hq)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem trialWindow_scale_bounds (M : ℕ) (hM : 0 < M) (R s : ℝ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    s ≤ trialWindow M R s ∧ trialWindow M R s ≤ (200*M*(R+1))*s := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := Nat.le_ceil s
  have hc' := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
  have hbase : s ≤ (R+1)*(⌈s⌉₊ : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hM' (by positivity : 0 ≤ (R+1)*(⌈s⌉₊ : ℝ))
  have hupper := mul_le_mul_of_nonneg_left (show (⌈s⌉₊ : ℝ) ≤ 2*s by linarith)
    (show 0 ≤ 100*(M : ℝ)*(R+1) by positivity)
  unfold trialWindow trialSpacing
  constructor <;> nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFastEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

theorem measurableSet_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (rareFastEvent b m a A R ε s n t) :=
  measurableSet_strictLocalizedEvent _ _ _

theorem rareFastEvent_depends (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    DependsOnEdges (rareFastEvent b m a A R ε s n t)
      (internalEdges (rareFastVertices b A R s n t)) :=
  strictLocalizedEvent_depends _ _ _

theorem rareFastEvent_translate (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    (fun e => w (shiftEdge t e)) ∈ rareFastEvent b m a A R ε s n 0 ↔
      w ∈ rareFastEvent b m a A R ε s n t := by
  rw [mem_rareFastEvent,mem_rareFastEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m a p ds =
      defect w b m a (t+p) ds := by simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨t+p,ds,by simpa using hp,by simpa [add_assoc] using hq,?_,?_⟩
    · intro i hi
      have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
      change _ ∈ rareFastRegion b A R s n t
      simpa only [rareFastRegion,mem_ofPred_eq,he,sub_zero] using hin i hi
    · rwa [← hc]
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨p-t,ds,by simpa using sub_eq_zero.mpr hp,?_,?_,?_⟩
    · simp only [Prod.fst_add,Prod.fst_sub,Prod.fst_zero] at *
      omega
    · intro i hi
      have he : p-t+displacement (ds.take i)=(p+displacement (ds.take i))-t := by abel
      rw [he]
      simpa [rareFastRegion] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem rareFastEvent_probability_translate (h : ExponentialEnvironment P τ)
    (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} =
      P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0} := by
  have he : {ω | (fun e => τ (shiftEdge t e) ω) ∈ rareFastEvent b m a A R ε s n 0} =
      {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} := by
    ext ω
    exact rareFastEvent_translate b m a A R ε s n t (fun e => τ e ω)
  rw [← he]
  exact translated_event_probability h t _ (measurableSet_rareFastEvent ..)

theorem rareFastTrials_disjoint (b A R s : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    Pairwise (fun j l : Fin M => Disjoint
      (rareFastVertices b A R s n (trialTranslate b X Y M R s j))
      (rareFastVertices b A R s n (trialTranslate b X Y M R s l))) := by
  intro j l hjl
  apply strip_vertices_disjoint _ _ b
    (transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s l)) (R*s)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · simpa only [mul_assoc] using trial_centers_separated b X Y M R s j l hjl hR hs

theorem rareFastTrials_failure_bound (h : ExponentialEnvironment P τ)
    (b m a A R ε s p0 : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0}) :
    P.real {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ rareFastEvent b m a A R ε s n
      (trialTranslate b X Y M R s j)} ≤ (1-p0)^M := by
  have hh := disjoint_trials_failure_bound h (Finset.univ : Finset (Fin M))
    (fun j => rareFastEvent b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun j => internalEdges (rareFastVertices b A R s n (trialTranslate b X Y M R s j)))
    (fun _ _ => measurableSet_rareFastEvent ..) (fun j _ => rareFastEvent_depends b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun _ _ _ _ hij => internalEdges_disjoint (rareFastTrials_disjoint b A R s n X Y M hR hs hij))
    p0 (fun j _ => ?_)
  · simpa using hh
  · unfold Measure.real
    rw [rareFastEvent_probability_translate h]
    exact hp0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GoodSiteEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem internalEdges_mono {V W : Finset Vertex} (h : V ⊆ W) :
    internalEdges V ⊆ internalEdges W := by
  intro e he
  obtain ⟨hp,hq⟩ := (mem_internalEdges e V).mp he
  exact (mem_internalEdges e W).mpr ⟨h hp,h hq⟩

theorem DependsOnEdges.mono {E : Set (Edge → ℝ)} {S T : Finset Edge}
    (h : DependsOnEdges E S) (hst : S ⊆ T) : DependsOnEdges E T := by
  intro w w' hh
  exact h w w' (fun e he => hh e (hst he))

theorem rareFastVertices_subset_block (b A R s σ : ℝ) (n d : ℤ) (v : Vertex)
    (M : ℕ) (j : Fin M) (_hA : 0 ≤ A) (hn : 0 ≤ n) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    rareFastVertices b A R s n
      (trialTranslate b (blockX n d v) (blockY σ (trialWindow M R s) v) M R s j) ⊆
      blockVertices b A n d σ (trialWindow M R s) v := by
  intro p hp
  have hh := (mem_rareFastVertices ..).mp hp
  have htrans : transverse b (p-trialTranslate b (blockX n d v)
      (blockY σ (trialWindow M R s) v) M R s j)=transverse b p-
      transverse b (trialTranslate b (blockX n d v) (blockY σ (trialWindow M R s) v) M R s j) := by
    simp [transverse]; ring
  have hw := trial_strip_in_window b (blockX n d v) (blockY σ (trialWindow M R s) v)
    M R s j hR hs p (by rw [← htrans]; exact hh.2.2)
  have hS : 0 ≤ trialWindow M R s := by
    have := (trialWindow_scale_bounds M j.pos R s hR hs).1
    linarith
  rw [mem_blockVertices]
  refine ⟨abs_le.mpr ⟨?_,?_⟩,by linarith⟩
  · have hl := hh.1
    simp only [Prod.fst_sub,trialTranslate,Int.cast_sub] at hl
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  · have hu := hh.2.1
    simp only [Prod.fst_sub,trialTranslate,Int.cast_sub] at hu
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

theorem connectorVertices_subset_block (b A s σ S : ℝ) (n d : ℤ) (v : Vertex)
    (hA : 0 ≤ A) (hd : 0 ≤ d) (_hs : 0 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    connectorVertices b (blockX n d v+n) d (blockY σ S v) S s ⊆
      blockVertices b A n d σ S v := by
  intro p hp
  have hh := (mem_connectorVertices ..).mp hp
  rw [mem_blockVertices]
  refine ⟨abs_le.mpr ⟨?_,?_⟩,hh.2.2⟩
  all_goals
    have hl := hh.1
    have hu := hh.2.1
    simp only [Int.cast_add] at hl hu
    have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (0 : ℝ) ≤ n := by linarith
    nlinarith

theorem measurableSet_goodSiteEvent (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) :
    MeasurableSet (goodSiteEvent μ b A R ε s plus n d M v) := by
  change MeasurableSet ({w | ∃ j : Fin M, w ∈ siteTrial μ b A R ε s plus n d M v j} ∩
    (siteConnector μ b R ε s plus n d M v 1 ∩ siteConnector μ b R ε s plus n d M v 2))
  apply MeasurableSet.inter
  · simp only [ofPred_exists]
    exact MeasurableSet.iUnion (fun j => measurableSet_rareFastEvent ..)
  · exact (measurableSet_allPairsRegionEvent ..).inter (measurableSet_allPairsRegionEvent ..)

theorem goodSiteEvent_depends (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hR : 0 ≤ R) (hs : 1 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    DependsOnEdges (goodSiteEvent μ b A R ε s plus n d M v)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) := by
  have hn0 : 0 ≤ n := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have ht (j : Fin M) : DependsOnEdges (siteTrial μ b A R ε s plus n d M v j)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) :=
    (rareFastEvent_depends b (μ (direction b)) (extremeSlope μ b plus) A R ε s n _).mono
      (internalEdges_mono (rareFastVertices_subset_block b A R s (contactSign plus) n d v M j hA hn0 hR hs))
  have hc (a : ℝ) : DependsOnEdges (siteConnector μ b R ε s plus n d M v a)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) :=
    (allPairsRegionEvent_depends _ _ _ _).mono
      (internalEdges_mono (connectorVertices_subset_block b A s (contactSign plus)
        (trialWindow M R s) n d v hA hd (by linarith) hn))
  intro w w' hh
  change ((∃ j, w ∈ siteTrial μ b A R ε s plus n d M v j) ∧ _ ∧ _) ↔ _
  exact and_congr (exists_congr (fun j => ht j w w' hh))
    (and_congr (hc 1 w w' hh) (hc 2 w w' hh))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem goodSiteEvent_independent (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hM : 0 < M) (hA : 0 < A) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hs : 1 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    SeparatedGoodIndependent P
      (fun v => {ω | (fun e => τ e ω) ∈ goodSiteEvent μ b A R ε s plus n d M v})
      (⌈4*(A+3)+8⌉₊+1) := by
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have hS : 0 < trialWindow M R s := by
    have := (trialWindow_scale_bounds M hM R s hR hs).1
    linarith
  exact block_supported_tests_independent h b A n d (contactSign plus) (trialWindow M R s)
    hn0 hd (abs_contactSign plus) hS hA _ (fun v => measurableSet_goodSiteEvent ..)
    (fun v => goodSiteEvent_depends μ b A R ε s plus n d M v hA.le hd hR hs hn)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GoodSiteProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem goodSiteEvent_failure_bound (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (b A R ε s p0 : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ) (v : Vertex)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0}) :
    P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n d M v} ≤
      (1-p0)^M + P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 1} +
        P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 2} := by
  let _ := h.probability
  let F := {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ siteTrial μ b A R ε s plus n d M v j}
  let C₁ := {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 1}
  let C₂ := {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n d M v 2}
  have hsub : {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n d M v} ⊆
      (F ∪ C₁) ∪ C₂ := by
    intro ω hh
    simp only [goodSiteEvent,mem_ofPred_eq,not_and_or,not_exists] at hh
    rcases hh with hf | hc | hc
    · exact Or.inl (Or.inl hf)
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hc
  have hf : P.real F ≤ (1-p0)^M := rareFastTrials_failure_bound h b (μ (direction b))
    (extremeSlope μ b plus) A R ε s p0 n (blockX n d v)
    (blockY (contactSign plus) (trialWindow M R s) v) M hR hs hp0
  calc
    _ ≤ P.real ((F ∪ C₁) ∪ C₂) := measureReal_mono hsub
    _ ≤ P.real (F ∪ C₁)+P.real C₂ := measureReal_union_le _ _
    _ ≤ (P.real F+P.real C₁)+P.real C₂ := by linarith [measureReal_union_le (μ := P) F C₁]
    _ ≤ _ := by dsimp [C₁,C₂]; linarith

theorem exponential_goodSiteEvent_failure (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ (n : ℤ) (v : Vertex) (p0 : ℝ),
      p0 ≤ P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0} →
      P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent μ b A R ε s plus n ⌈D0*s⌉ M v} <
        (1-p0)^M+κ := by
  obtain ⟨D0,hD0,hc⟩ := exponential_source_connector_test h μ hμ ht b hb plus M hM R ε hR hε
  refine ⟨D0,hD0,?_⟩
  intro κ hκ
  filter_upwards [hc (κ/2) (by positivity),eventually_ge_atTop (1 : ℝ)] with s hcs hs
  intro n v p0 hp0
  have h1 := hcs (blockX n ⌈D0*s⌉ v+n)
    (blockY (contactSign plus) (trialWindow M R s) v) 1 (by norm_num) (by norm_num)
  have h2 := hcs (blockX n ⌈D0*s⌉ v+n)
    (blockY (contactSign plus) (trialWindow M R s) v) 2 (by norm_num) (by norm_num)
  have hh := goodSiteEvent_failure_bound h μ b A R ε s p0 plus n ⌈D0*s⌉ M v hR hs hp0
  change P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n ⌈D0*s⌉ M v 1} < κ/2 at h1
  change P.real {ω | (fun e => τ e ω) ∉ siteConnector μ b R ε s plus n ⌈D0*s⌉ M v 2} < κ/2 at h2
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFast
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_rareFast_eventually (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (p0 : ℝ) (hp0 : 0 < p0) (hp1 : p0 ≤ 1) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ᶠ s : ℝ in atTop, ∀ n : ℤ,
      (⌈D0*s⌉ : ℝ)+s ≤ n →
      P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0} < p0 := by
  let _ := h.probability
  let k : ℕ := ⌈4*(A+3)+8⌉₊+1
  obtain ⟨ζ,hζ,hpaths⟩ := high_density_oriented_paths_uniform k
  have htM := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1-p0)
    (by linarith : 1-p0 < 1)
  obtain ⟨M,hpow,hM⟩ := ((htM.eventually (gt_mem_nhds (by linarith : 0 < ζ/2))).and
    (eventually_ge_atTop (1 : ℕ))).exists
  have hM0 : 0 < M := by omega
  obtain ⟨D0,hD0,hbad⟩ := exponential_goodSiteEvent_failure h μ hμ ht b A R ε hb plus M hM0 hR hε
  refine ⟨D0,hD0,?_⟩
  filter_upwards [hbad (ζ/2) (by linarith),eventually_ge_atTop (1 : ℝ)] with s hbs hs
  intro n hn
  have hd0 : (0 : ℝ) ≤ (⌈D0*s⌉ : ℤ) := by
    have := Int.le_ceil (D0*s)
    nlinarith
  have hd : 0 ≤ (⌈D0*s⌉ : ℤ) := by exact_mod_cast hd0
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  by_contra hlow
  have hl : p0 ≤ P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0} := le_of_not_gt hlow
  have hg (v : Vertex) : P.real {ω | (fun e => τ e ω) ∉
      goodSiteEvent μ b A R ε s plus n ⌈D0*s⌉ M v} ≤ ζ := by
    have := hbs n v p0 hl
    linarith
  have hi := goodSiteEvent_independent h μ b A R ε s plus n ⌈D0*s⌉ M hM0 hA hd hR hs hn
  have hp := hpaths Ω P
    (fun v => {ω | (fun e => τ e ω) ∈ goodSiteEvent μ b A R ε s plus n ⌈D0*s⌉ M v})
    (fun v => (measurableSet_goodSiteEvent ..).preimage (Measurable.of_eval h.measurable)) hi hg
  have hz := exponential_goodSite_path_probability_zero h μ hμ ht b A R ε s plus n ⌈D0*s⌉ M
    hb hR hε hs hn0 hd hM0
  unfold Measure.real at hp
  simp only [mem_ofPred_eq] at hp
  rw [hz] at hp
  simp at hp

theorem exponential_rareFast_bound (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S K : ℝ, 1 ≤ S ∧ 0 < K ∧ ∀ s : ℝ, S ≤ s → ∀ n : ℤ,
      K*s ≤ n → P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n 0} < κ := by
  let p0 := min κ 1
  have hp0 : 0 < p0 := lt_min hκ (by norm_num)
  obtain ⟨D0,hD0,hh⟩ := exponential_rareFast_eventually h μ hμ ht b A R ε hb hA hR hε plus p0 hp0
    (min_le_right _ _)
  obtain ⟨S,hS⟩ := eventually_atTop.mp hh
  refine ⟨max S 1,D0+2,le_max_right _ _,by linarith,?_⟩
  intro s hs n hn
  have hs1 : 1 ≤ s := (le_max_right _ _).trans hs
  have hc : (⌈D0*s⌉ : ℝ) < D0*s+1 := Int.ceil_lt_add_one _
  exact (hS s ((le_max_left _ _).trans hs) n (by nlinarith)).trans_le (min_le_left _ _)

theorem exponential_rareFast_tendsto {ι : Type*} {l : Filter ι}
    (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (s : ι → ℝ) (n : ι → ℤ)
    (hs : Tendsto s l atTop) (hn : Tendsto (fun i => (n i : ℝ)/s i) l atTop) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε (s i) (n i) 0}) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro κ hκ
    obtain ⟨S,K,hS,_,hh⟩ := exponential_rareFast_bound h μ hμ ht b A R ε hb hA hR hε plus κ hκ
    filter_upwards [hs.eventually (eventually_ge_atTop S),hn.eventually (eventually_ge_atTop K)] with i hsi hni
    apply hh (s i) hsi (n i)
    exact (le_div_iff₀ (by linarith : 0 < s i)).mp hni

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TiltPath
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem pathCost_scale (τ : Edge → ℝ) (α : ℝ) (p : Vertex) (ds : List Step) :
    pathCost (fun e => α * τ e) p ds = α * pathCost τ p ds := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, mul_add]

theorem tilt_crossing_defect (τ : Edge → ℝ) (b m a K lam s n : ℝ)
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hs : 0 < s) (hn : 0 < n)
    (hsmall : lam * s < n) (hgain : K + 16 * |a| + 1 < lam * m)
    (p : Vertex) (ds : List Step)
    (hx : ((displacement ds).1 : ℝ) = n)
    (hr : |transverse b (displacement ds)| ≤ 16 * s)
    (hcheap : pathCost τ p ds < m * n + K * s) :
    defect (fun e => (1 - lam * s / n) * τ e) b m a p ds < -s := by
  have hα : 0 < 1 - lam * s / n := by
    have := (div_lt_one hn).mpr hsmall
    linarith
  have hc := mul_lt_mul_of_pos_left hcheap hα
  have habs : -(a * transverse b (displacement ds)) ≤ 16 * |a| * s := by
    calc
      -(a * transverse b (displacement ds)) ≤ |a * transverse b (displacement ds)| :=
        neg_le_abs _
      _ = |a| * |transverse b (displacement ds)| := abs_mul _ _
      _ ≤ |a| * (16 * s) := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
      _ = 16 * |a| * s := by ring
  have halg : (1 - lam * s / n) * (m * n + K * s) - m * n =
      (K - lam * m) * s - lam * K * s ^ 2 / n := by
    field_simp [ne_of_gt hn]
    ring
  have hnonneg : 0 ≤ lam * K * s ^ 2 / n := by positivity
  have hgain' := mul_lt_mul_of_pos_right hgain hs
  unfold defect support
  rw [pathCost_scale, hx]
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TiltRegionCount
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem int_interval_card_real_le (l u : ℝ) (h : l ≤ u) :
    ((Finset.Icc ⌈l⌉ ⌊u⌋).card : ℝ) ≤ u-l+1 := by
  rw [Int.card_Icc]
  by_cases hh : 0 ≤ ⌊u⌋+1-⌈l⌉
  · have he : ((⌊u⌋+1-⌈l⌉).toNat : ℝ)=((⌊u⌋+1-⌈l⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hh
    rw [he]
    push_cast
    linarith [Int.floor_le u,Int.le_ceil l]
  · have hz : (⌊u⌋+1-⌈l⌉).toNat=0 := Int.toNat_eq_zero.mpr (le_of_not_ge hh)
    rw [hz]
    simp only [Nat.cast_zero]
    linarith

theorem tiltColumn_card (b s : ℝ) (hs : 0 ≤ s) (x : ℤ) :
    ((tiltColumn b s x).card : ℝ) ≤ 16*s+2 := by
  have hh := int_interval_card_real_le (b*x-8*s) (b*x+8*s) (by linarith)
  simpa only [tiltColumn,Finset.card_product,Finset.card_singleton,one_mul] using
    hh.trans (by linarith)

theorem rareFast_tilt_vertices_card (b s : ℝ) (n : ℤ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ((rareFastVertices b 1 8 s n 0).card : ℝ) ≤ (3*(n : ℝ)+1)*(16*s+2) := by
  have hsub : rareFastVertices b 1 8 s n 0 ⊆
      (Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s) := by
    intro p hp
    have hh := (mem_rareFastVertices ..).mp hp
    have hx : -n ≤ p.1 ∧ p.1 ≤ 2*n := by
      constructor
      · have ht : -(n : ℝ) ≤ (p.1 : ℝ) := by simpa using hh.1
        exact_mod_cast ht
      · have := hh.2.1; norm_num only [sub_zero,one_add_one_eq_two] at this
        exact_mod_cast this
    have hy := abs_le.mp hh.2.2
    simp only [sub_zero,transverse] at hy
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,Finset.mem_Icc.mpr hx,?_⟩
    simp only [tiltColumn,Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc,true_and]
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)
  have hcount : ((Finset.Icc (-n) (2*n)).card : ℝ)=3*(n : ℝ)+1 := by
    rw [Int.card_Icc]
    have he : ((2*n+1-(-n)).toNat : ℝ)=((2*n+1-(-n) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ 2*n+1-(-n))
    rw [he]
    push_cast
    ring
  calc
    _ ≤ (((Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (∑ x ∈ Finset.Icc (-n) (2*n), ((tiltColumn b s x).card : ℝ)) := by
      exact_mod_cast (Finset.card_biUnion_le :
        ((Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s)).card ≤ _)
    _ ≤ ∑ _x ∈ Finset.Icc (-n) (2*n), (16*s+2) :=
      Finset.sum_le_sum (fun x _ => tiltColumn_card b s (by linarith) x)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,hcount]

theorem rareFast_tilt_edges_card (b s : ℝ) (n : ℤ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ((internalEdges (rareFastVertices b 1 8 s n 0)).card : ℝ) ≤ 144*(n : ℝ)*s := by
  have hv := rareFast_tilt_vertices_card b s n hs hn
  have he : ((internalEdges (rareFastVertices b 1 8 s n 0)).card : ℝ) ≤
      2*((rareFastVertices b 1 8 s n 0).card : ℝ) := by
    exact_mod_cast internalEdges_card_le (rareFastVertices b 1 8 s n 0)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul (show 3*(n : ℝ)+1 ≤ 4*n by linarith)
    (show 16*s+2 ≤ 18*s by linarith) (by linarith : 0 ≤ 16*s+2)
    (by linarith : 0 ≤ 4*(n : ℝ))
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem crossingEvent_tilt_implication (b m a K lam s : ℝ) (n : ℤ)
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hs : 0 < s) (hn : 0 < n)
    (hsmall : lam*s < n) (hgain : K+16*|a|+1 < lam*m)
    (w : Edge → ℝ) (hw : w ∈ crossingEvent b m K s n 0) :
    scaleFiniteEdges (internalEdges (rareFastVertices b 1 8 s n 0)) (1-lam*s/n) w ∈
      rareFastEvent b m a 1 8 1 s n 0 := by
  rw [scaleFiniteEdges_event_iff _ _ _ (rareFastEvent_depends b m a 1 8 1 s n 0)]
  obtain ⟨p,ds,⟨hp,hq⟩,hin,hcost⟩ := hw
  have hx : ((displacement ds).1 : ℝ)=(n : ℝ) := by
    have he : (displacement ds).1=n := by simpa [Prod.fst_add,hp] using hq
    exact_mod_cast he
  have hstart : p ∈ rareFastRegion b 1 8 s n 0 := by
    have hh := hin 0 (by omega)
    simpa using hh
  have hend : p+displacement ds ∈ rareFastRegion b 1 8 s n 0 := by
    exact (mem_rareFastVertices ..).mp (pathIn_endpoint _ _ _ hin)
  have hr : |transverse b (displacement ds)| ≤ 16*s := by
    have ht := abs_sub (transverse b (p+displacement ds)) (transverse b p)
    simp only [transverse_add,add_sub_cancel_left] at ht
    have h1 := hstart.2.2
    have h2 := hend.2.2
    simp only [sub_zero,transverse_add] at h1 h2
    linarith
  have hd := tilt_crossing_defect w b m a K lam s n hK hlam hs
    (by exact_mod_cast hn) hsmall hgain p ds hx hr hcost
  apply (mem_rareFastEvent ..).mpr
  refine ⟨p,ds,hp,hq,?_,?_⟩
  · intro i hi
    exact (mem_rareFastVertices ..).mp (hin i hi)
  · simpa using hd

theorem source_tilt_exponent_bound (N : ℕ) (lam s n : ℝ)
    (_hs : 0 ≤ s) (hn : 0 < n) (hN : (N : ℝ) ≤ 144*n*s) (hn3 : s^3 ≤ n) :
    2*N*(lam*s/n)^2 ≤ 288*lam^2 := by
  calc
    _ ≤ (2*(144*n*s))*(lam*s/n)^2 := by gcongr
    _ = (288*lam^2)*(s^3/n) := by field_simp; ring
    _ ≤ (288*lam^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one hn).mpr hn3) (by positivity)
    _ = _ := mul_one _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_crossing_tilt_bound (h : ExponentialEnvironment P τ)
    (b m a K lam s : ℝ) (n : ℤ) (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hs : 1 ≤ s) (hn : 1 ≤ n) (hn3 : s^3 ≤ n)
    (hsmall : lam*s/n ≤ 1/2) (hgain : K+16*|a|+1 < lam*m) :
    P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} ^ 2 ≤
      Real.exp (288*lam^2) *
        P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a 1 8 1 s n 0} := by
  let _ := h.probability
  let S := internalEdges (rareFastVertices b 1 8 s n 0)
  let F := rareFastEvent b m a 1 8 1 s n 0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ : 0 ≤ lam*s/n := by positivity
  have hlt : lam*s < n := by
    have hh := (div_le_iff₀ hn0).mp hsmall
    linarith
  have himp : {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} ⊆
      {ω | scaleFiniteEdges S (1-lam*s/n) (fun e => τ e ω) ∈ F} := by
    intro ω hω
    exact crossingEvent_tilt_implication b m a K lam s n hK hlam (by linarith) (by omega) hlt hgain _ hω
  have hprob := measureReal_mono (μ := P) himp
  have hcomp := finite_edge_tilt_probability_sq_exp_bound h S (lam*s/n) hδ hsmall F
    (measurableSet_rareFastEvent ..) (rareFastEvent_depends b m a 1 8 1 s n 0)
  have hexp : Real.exp (2*S.card*(lam*s/n)^2) ≤ Real.exp (288*lam^2) := by
    apply Real.exp_le_exp.mpr
    exact source_tilt_exponent_bound S.card lam s n (by linarith) hn0
      (rareFast_tilt_edges_card b s n hs hn) hn3
  exact (pow_le_pow_left₀ measureReal_nonneg hprob 2).trans
    (hcomp.trans (mul_le_mul_of_nonneg_right hexp measureReal_nonneg))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SourceTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

theorem exponential_crossing_cubic_tendsto {ι : Type*} {l : Filter ι}
    (h : ExponentialEnvironment P τ) (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (ht : IsTimeConstant P τ μ) (b K : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (s : ι → ℝ) (n : ι → ℤ) (hs : Tendsto s l atTop)
    (hn3 : ∀ᶠ i in l, (s i)^3 ≤ n i) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b (μ (direction b)) K (s i) (n i) 0}) l (𝓝 0) := by
  let m := μ (direction b)
  let a := extremeSlope μ b true
  let lam := (K+16*|a|+2)/m
  have hm : 0 < m := norm_direction_pos μ hμ b
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hgain : K+16*|a|+1 < lam*m := by
    dsimp [lam]
    rw [div_mul_cancel₀ _ (ne_of_gt hm)]
    linarith
  have hratio : Tendsto (fun i => (n i : ℝ)/s i) l atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 B)),hn3] with i hsi hni
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hsB : B ≤ s i := (le_max_right _ _).trans hsi
    apply (le_div_iff₀ (by linarith : 0 < s i)).mpr
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    nlinarith [mul_le_mul_of_nonneg_right hsB (by linarith : 0 ≤ s i)]
  have hrare := exponential_rareFast_tendsto h μ hμ ht b 1 8 1 hb (by norm_num) (by norm_num)
    (by norm_num) true s n hs hratio
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le measureReal_nonneg)
  · intro κ hκ
    have hC : 0 < Real.exp (288*lam^2) := Real.exp_pos _
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 (2*lam))),hn3,
      (tendsto_order.1 hrare).2 (κ^2/Real.exp (288*lam^2)) (by positivity)] with i hsi hni hpi
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hslam : 2*lam ≤ s i := (le_max_right _ _).trans hsi
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    have hn1 : (1 : ℝ) ≤ n i := by nlinarith
    have hn1' : 1 ≤ n i := by exact_mod_cast hn1
    have hsmall : lam*s i/(n i : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < n i)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hslam (by linarith : 0 ≤ s i)]
    have hh := exponential_crossing_tilt_bound h b m a K lam (s i) (n i) hK hlam.le hs1 hn1' hni hsmall hgain
    have hh' := (lt_div_iff₀ hC).mp hpi
    nlinarith [measureReal_nonneg (μ := P) (s := {ω | (fun e => τ e ω) ∈ crossingEvent b m K (s i) (n i) 0})]

theorem exponential_source_tilt (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b : ℝ) (hb : |b| ≤ 1) :
    Tendsto (fun k : ℕ => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b (μ (direction b)) (sourceCrossingK μ b) ((2 : ℝ)^k) ((2 : ℤ)^(3*k)) 0})
      atTop (𝓝 0) := by
  apply exponential_crossing_cubic_tendsto h μ hμ ht b (sourceCrossingK μ b) hb
    (by unfold sourceCrossingK; positivity) (fun k : ℕ => (2 : ℝ)^k) (fun k => (2 : ℤ)^(3*k))
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2))
  apply Eventually.of_forall
  intro k
  norm_num only [Int.cast_pow,Int.cast_ofNat]
  rw [← pow_mul,Nat.mul_comm k 3]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CharacteristicLengths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem firstDyadicExponent_spec (p : ℕ → ℝ) (q : ℝ) (h : ∃ j, p j ≤ q) :
    p (firstDyadicExponent p q) ≤ q := by
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_spec h

theorem firstDyadicExponent_le (p : ℕ → ℝ) (q : ℝ) (j : ℕ) (hj : p j ≤ q) :
    firstDyadicExponent p q ≤ j := by
  have h : ∃ j, p j ≤ q := ⟨j,hj⟩
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_min' h hj

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

theorem exponential_characteristic_lengths_exist_oai (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∀ᶠ k : ℕ in atTop,
      characteristicExponent P τ μ b q k ≤ 3*k ∧
      P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) (sourceCrossingK μ b)
        ((2 : ℝ)^k) (characteristicLength P τ μ b q k) 0} ≤ q := by
  filter_upwards [(exponential_source_tilt h μ hμ ht b hb).eventually (gt_mem_nhds hq)] with k hk
  have hh : sourceDyadicCrossingProbability P τ μ b k (3*k) ≤ q := hk.le
  exact ⟨firstDyadicExponent_le _ _ _ hh,firstDyadicExponent_spec _ _ ⟨3*k,hh⟩⟩

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.exponential_characteristic_lengths_exist_oai.{u_1} := @OAI.PlanarFPP.exponential_characteristic_lengths_exist_oai.{u_1}
