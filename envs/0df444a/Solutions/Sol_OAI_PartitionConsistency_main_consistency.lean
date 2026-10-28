-- Prove2me | solution 1 for OAI.PartitionConsistency.main_consistency
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:01:56.46362+00:00
-- url     : https://prove2.me/submissions/9fb4761c-2d12-4026-a60d-698f9b87cb48

import Mathlib
import Definitions.Def_PartitionConsistency
import Definitions.Def_OAIQ5T1002

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_Placements
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements
open Cardinal
universe u
variable {α β : Type u}

/-- An embedding into a larger infinite set can be chosen to cover a prescribed
subset whose cardinality does not exceed that of its domain. -/
theorem embedding_cover [Infinite β] (h : #α < #β) {s : Set β} (hs : #s ≤ #α) :
    ∃ g : α ↪ β, s ⊆ Set.range g := by
  classical
  obtain ⟨k⟩ := hs
  let e : s ≃ Set.range k := Equiv.ofInjective k k.injective
  let f : Set.range k ↪ β := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := extend_embedding h f
  refine ⟨g, ?_⟩
  intro b hb
  refine ⟨k ⟨b, hb⟩, ?_⟩
  simpa [f, e] using hg (e ⟨b, hb⟩)

/-- Complete an existing partial injection and cover a prescribed small subset
at the same time. No value already prescribed is altered. -/
theorem extend_embedding_cover [Infinite β] (h : #α < #β) {s : Set α}
    (f : s ↪ β) {J : Set β} (hJ : #J ≤ #(sᶜ : Set α)) :
    ∃ g : α ↪ β, (∀ x : s, g x = f x) ∧ J ⊆ Set.range g := by
  classical
  have hfr : #(Set.range f) < #β := by
    rw [← Cardinal.mk_congr (Equiv.ofInjective f f.injective)]
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h
  have hcom : #((Set.range f)ᶜ : Set β) = #β :=
    Cardinal.mk_compl_of_infinite _ hfr
  let _ : Infinite ((Set.range f)ᶜ : Set β) :=
    Cardinal.infinite_iff.2 (by rw [hcom]; exact Cardinal.aleph0_le_mk β)
  let K : Set ((Set.range f)ᶜ : Set β) := {b | b.val ∈ J}
  have hK : #K ≤ #(sᶜ : Set α) := by
    have hk : Function.Injective (fun x : K => (⟨x.val.val, x.property⟩ : J)) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : J => z.val) hxy
    exact (Cardinal.mk_le_of_injective hk).trans hJ
  obtain ⟨k, hk⟩ := embedding_cover
    (α := (sᶜ : Set α)) (β := ((Set.range f)ᶜ : Set β))
    (by rw [hcom]; exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h) hK
  let g : α → β := fun a => if ha : a ∈ s then f ⟨a, ha⟩ else k ⟨a, ha⟩
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · simp only [g, dite_eq_left ha, dite_eq_left hb] at hab
      exact congrArg Subtype.val (f.injective hab)
    · simp only [g, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim ((k ⟨b, hb⟩).property ⟨⟨a, ha⟩, hab⟩)
    · simp only [g, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim ((k ⟨a, ha⟩).property ⟨⟨b, hb⟩, hab.symm⟩)
    · simp only [g, dite_eq_right ha, dite_eq_right hb] at hab
      exact congrArg Subtype.val (k.injective (Subtype.ext hab))
  refine ⟨⟨g, hg⟩, (fun x => by simp [g, x.property]), ?_⟩
  intro b hb
  by_cases hbf : b ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hbf
    exact ⟨x.val, by simp [g, x.property]⟩
  · obtain ⟨x, hx⟩ := hk (show (⟨b, hbf⟩ : ((Set.range f)ᶜ : Set β)) ∈ K from hb)
    refine ⟨x.val, ?_⟩
    have hn : x.val ∉ s := x.property
    change (if h : x.val ∈ s then f ⟨x.val, h⟩ else (k x).val) = b
    rw [dite_eq_right hn]
    exact congrArg Subtype.val hx

end SmallPlacements
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_CohenForcing
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace CohenForcing
universe u v
variable {I : Type u} {κ : Type v}

namespace Condition

/-- The Cohen forcing described in the source is countably closed. Unions
suffice; no closure of the diagram forcing or product is asserted. -/
theorem countably_closed (p : ℕ → Condition I κ) (hp : Antitone p) :
    ∃ r : Condition I κ, ∀ n, r ≤ p n := by
  let g := ⋃ n, (p n).graph
  have fun_g : ∀ a b c, (a, b) ∈ g → (a, c) ∈ g → b = c := by
    intro a b c hb hc
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hc
    exact (p (max n m)).functional a b c
      (hp (Nat.le_max_left _ _) hn) (hp (Nat.le_max_right _ _) hm)
  exact ⟨⟨g, fun_g, Set.countable_iUnion (fun n => (p n).countable_graph)⟩,
    fun n z hz => Set.mem_iUnion.2 ⟨n, hz⟩⟩

theorem restrict_eq_of_support_subset (p : Condition I κ) {J : Set I}
    (h : p.support ⊆ J) : restrict p J = p := by
  apply ext
  ext z
  simp only [mem_restrict, and_iff_left_iff_imp]
  intro hz
  exact h ((mem_support p _).2 ⟨z.1.2, z.2, hz⟩)

theorem permute_eq_of_fixes_support (π : Equiv.Perm I) (p : Condition I κ)
    (hπ : ∀ j ∈ p.support, π j = j) : permute π p = p := by
  apply ext
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    have hfix := hπ w.1.1 ((mem_support p _).2 ⟨w.1.2, w.2, hw⟩)
    simpa [hfix] using hw
  · intro z hz
    refine ⟨z, hz, ?_⟩
    have hfix := hπ z.1.1 ((mem_support p _).2 ⟨z.1.2, z.2, hz⟩)
    simp [hfix]

theorem insert_le (p : Condition I κ) (a : I × κ) (b : Bool) (h : a ∉ p.dom) :
    insert p a b h ≤ p := Set.subset_insert _ _

theorem fresh_level [Uncountable κ] (p : Condition I κ) :
    ∃ a : κ, ∀ j : I, (j, a) ∉ p.dom := by
  have hc : (Prod.snd '' p.dom).Countable := p.countable_dom.image _
  have hn : Prod.snd '' p.dom ≠ Set.univ := by
    intro hu
    exact Set.not_countable_univ (hu ▸ hc)
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 hn
  exact ⟨a, fun j hj => ha ⟨(j, a), hj, rfl⟩⟩

/-- Distinct label coordinates can be assigned opposite bits at a fresh level
below every condition. This is the dense separation used for distinct labels. -/
theorem separate_labels [Uncountable κ] (p : Condition I κ) {j k : I} (hjk : j ≠ k) :
    ∃ (q : Condition I κ) (a : κ), q ≤ p ∧
      ((j, a), false) ∈ q.graph ∧ ((k, a), true) ∈ q.graph := by
  obtain ⟨a, ha⟩ := fresh_level p
  let p' := insert p (j, a) false (ha j)
  have hk : (k, a) ∉ p'.dom := by
    rintro h
    obtain ⟨b, hb⟩ := (mem_dom p' _).1 h
    rcases hb with hb | hb
    · exact hjk (congrArg (fun z : (I × κ) × Bool => z.1.1) hb).symm
    · exact ha k ((mem_dom p _).2 ⟨b, hb⟩)
  let q := insert p' (k, a) true hk
  refine ⟨q, a, (insert_le _ _ _ _).trans (insert_le _ _ _ _), ?_, ?_⟩
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert _ _

end Condition
end CohenForcing
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_PlacementExtensions
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements

/-- Only countably many members of a pairwise disjoint family meet a fixed
countable set. This will be applied to the nonroot supports of probe copies. -/
theorem countable_obstructions {I A : Type*} (S : A → Set I) (C : Set I)
    (hS : Pairwise (fun a b => Disjoint (S a) (S b))) (hC : C.Countable) :
    {a | (S a ∩ C).Nonempty}.Countable :=
  Set.countable_ofPred_nonempty_of_disjoint
    (fun _a _b hab => (hS hab).mono Set.inter_subset_left Set.inter_subset_left)
    (fun _ => Set.inter_subset_right) hC

/-- An uncountable family of disjoint nonroot supports always has a member
avoiding any specified countable collection of coordinates. -/
theorem exists_fresh_member {I A : Type*} [Uncountable A] (S : A → Set I)
    (C : Set I) (hS : Pairwise (fun a b => Disjoint (S a) (S b))) (hC : C.Countable) :
    ∃ a, Disjoint (S a) C := by
  have hc := countable_obstructions S C hS hC
  have hn : {a | (S a ∩ C).Nonempty} ≠ Set.univ := by
    intro hu
    exact Set.not_countable_univ (hu ▸ hc)
  obtain ⟨a, ha⟩ := Set.ne_univ_iff_exists_notMem _ |>.1 hn
  exact ⟨a, Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 ha)⟩

end SmallPlacements

namespace CohenForcing.Condition
universe u v w
variable {I : Type u} {κ : Type v} {A : Type w}

/-- Weakening either of two compatible partial functions preserves their
compatibility. Recall that the forcing order is reverse inclusion. -/
theorem Compatible.weaken {p q p' q' : Condition I κ} (h : Compatible p q)
    (hp : p ≤ p') (hq : q ≤ q') : Compatible p' q' :=
  fun a b c hb hc => h a b c (hp hb) (hq hc)

/-- Pairwise independent copies with the same Cohen root give the probe dense
set. Uncountability is sufficient: a test condition has countable support.
No forcing name, generic extension, or choice in a symmetric model is assumed. -/
theorem probeDenseSet_dense [Uncountable A] (J : Set I) (root : Condition I κ)
    (copies : A → Condition I κ) (hroot : ∀ a, (copies a).restrict J = root)
    (hdisj : Pairwise (fun a b => Disjoint ((copies a).support \ J) ((copies b).support \ J))) :
    ForcingQuotient.Dense (probeDenseSet root copies) := by
  intro c
  by_cases hc : Compatible c root
  · obtain ⟨a, ha⟩ := SmallPlacements.exists_fresh_member
      (fun a => (copies a).support \ J) c.support hdisj c.countable_support
    have hr : Compatible (c.restrict J) ((copies a).restrict J) := by
      rw [hroot a]
      exact hc.weaken (le_restrict c J) le_rfl
    have hd : Disjoint (c.support \ J) ((copies a).support \ J) :=
      (ha.mono_right Set.sdiff_subset).symm
    have h := compatible_of_disjoint_off_root c (copies a) J hr hd
    exact ⟨union c (copies a) h, (union_le_left _ _ _),
      Or.inr ⟨a, union_le_right _ _ _⟩⟩
  · exact ⟨c, le_rfl, Or.inl hc⟩

end CohenForcing.Condition
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_Diagrams
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalName _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace DiagramForcing
universe u
variable {M I : Type u}

namespace Diagram

variable [LeftCancelMonoid M]

/-- The distinguished-probe complement bound is exactly what is needed to
extend a diagram through `e` while covering any prescribed `μ` labels.
Source `lem:diagram-amalgamation`, first part. -/
theorem extend_through [Infinite I] (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (p : Diagram M I) {J : Set I} (hJ : Cardinal.mk J ≤ Cardinal.mk M) :
    ∃ r : Diagram M I, sub r e = p ∧ J ⊆ r.range := by
  classical
  let ee : M ≃ Set.range (fun x : M => e * x) :=
    Equiv.ofInjective (fun x => e * x) (fun _ _ h => mul_left_cancel h)
  let f : Set.range (fun x : M => e * x) ↪ I := ee.symm.toEmbedding.trans p.toEmbedding
  obtain ⟨r, hr, hcover⟩ := SmallPlacements.extend_embedding_cover hsize f (by rwa [he])
  refine ⟨⟨r⟩, ?_, hcover⟩
  ext x
  have ht : r (e * x) = p (ee.symm (ee x)) := hr (ee x)
  simpa only [Equiv.symm_apply_apply, sub_apply] using ht

end Diagram

end DiagramForcing
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_ProbeGates
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Probe extension: all gates, conditional joins, and presentation -/

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

theorem Gate.head_ne {w : Word A b} {s : S} {g : M}
    (hg : Gate A b w s g) {z : Word A b} (hz : old A b g ∣ z) :
    head A b z ≠ some s := ((hg z).2 hz).2

/-- An old right multiplier can leave the first-letter block only after
all the intervening letters have been consumed. Thus an exit obtained by
such a multiplier is itself old. -/
theorem append_old_exit_isOld (w : Word A b) {s : S}
    (hs : head A b w = some s) (d : M)
    (hex : head A b (w * old A b d) ≠ some s) :
    ∃ y : M, w * old A b d = old A b y := by
  obtain ⟨w, hw⟩ := w
  induction w generalizing s with
  | old x => cases hs
  | cons t Y ih =>
    have hts : t = s := Option.some.inj hs
    subst t
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hw
    let Y' : Word A b := ⟨Y, hw.1⟩
    have hby : headDiv A b b (Y' * old A b d) :=
      (head_letterAct_ne_iff A b s _).1 hex
    have hYold : ∃ y : M, Y' * old A b d = old A b y := by
      cases heY : Y with
      | old y =>
        have hYeq : Y' = old A b y := Subtype.ext heY
        exact ⟨y * d, congrArg (· * old A b d) hYeq⟩
      | cons t Z =>
        have hYhead : head A b Y' = some t := by change Y.head = some t; rw [heY]; rfl
        have hexY : head A b (Y' * old A b d) ≠ some t := by
          intro hhead
          exact hw.2 ((headDiv_of_same_head A b hYhead hhead).2 hby)
        exact ih hw.1 hYhead hexY
    obtain ⟨y, hy⟩ := hYold
    have hbyold : b ∣ y := by
      change headDiv A b b (old A b y)
      exact hy ▸ hby
    obtain ⟨q, rfl⟩ := hbyold
    refine ⟨A.exit s * q, ?_⟩
    change letterAct A b s (Y' * old A b d) = _
    rw [hy]
    change letterAct A b s (oldAct A b b (old A b q)) = _
    rw [letterAct_oldAct_b]
    rfl

/-- The actual least-old-multiple rule required for the later descending
birth-ordinal argument. -/
theorem Gate.append_old {w : Word A b} {s : S} {g : M}
    (hg : Gate A b w s g) (hs : head A b w = some s) (d : M)
    (hd : old A b g ∣ w * old A b d) :
    ∃ y : M, w * old A b d = old A b y :=
  append_old_exit_isOld A b w hs d (Gate.head_ne A b hg hd)

end Word

end PartitionConsistency.ProbeAlgebra

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_SaturatedMonoids
attribute [-instance] _root_.OAI.PartitionConsistency.ConcreteSystem.instInfiniteCarrierT _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MonoidConstruction.RoundOrdinal.instSuccOrder _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SaturationData -/

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory CategoryTheory.Limits DiagramOrder DiagramForcing
noncomputable section
open scoped Classical

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

/-- The final ideal requirement uses all divisors in the final monoid, not
only those belonging to the scheduling stage. -/
theorem ideal_probes (a b : target M K) (hb : b ≠ 1)
    (U : ConeIdeal (α := LeftDivOrder (target M K)) a) :
    ∃ m : K → target M K, Function.Injective m ∧
      (∀ i, m i * b = a * (target M K).e ∧ ¬ m i ∣ a ∧
        (∀ x : target M K, x ∣ a ∧ x ∣ m i ↔ x ∈ U.carrier) ∧
        ∀ x : target M K, x ∣ a → x ∉ U.carrier →
          ∀ z : target M K, x ∣ z ∧ m i ∣ z ↔ a * (target M K).e ∣ z) ∧
      ∀ i j, i ≠ j → ∀ z : target M K,
        m i ∣ z ∧ m j ∣ z ↔ a * (target M K).e ∣ z := by
  obtain ⟨p,hp₀,hpU,hpinc,hpcof⟩ := U.countable_cofinal_sequence (target M K).margin (target M K).joins
  let path : ProbeAlgebra.Path (target M K) a := ⟨p,hp₀,fun {i j} h => (LeftDivOrder.le_iff_dvd _ _).1 (hpinc h),
    fun i => (LeftDivOrder.le_iff_dvd _ _).1 (U.bounded (hpU i))⟩
  let d : ProbeData (target M K) := ⟨a,b,hb,path⟩
  obtain ⟨m,hminj,hm,hind⟩ := probes M K d
  refine ⟨m,hminj,fun i => ?_,hind⟩
  refine ⟨(hm i).exit,(hm i).not_divides,?_,?_⟩
  · intro x
    rw [(hm i).divisors]
    exact ⟨fun ⟨n,hn⟩ => U.lower ((LeftDivOrder.le_iff_dvd _ _).2 hn) (hpU n),
      fun hx => (hpcof x hx).imp (fun n hn => (LeftDivOrder.le_iff_dvd _ _).1 hn)⟩
  · intro x hxa hxu
    apply (hm i).joins x hxa
    intro hxm
    obtain ⟨n,hn⟩ := ((hm i).divisors x).1 ⟨hxa,hxm⟩
    exact hxu (U.lower ((LeftDivOrder.le_iff_dvd _ _).2 hn) (hpU n))

theorem complement_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ) :
    Cardinal.mk {x : target M K // ¬ (target M K).e ∣ x} = μ := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans (cardinal_le M K hω hpow hM hK.le ⊤)
  · obtain ⟨m,hinj,hm⟩ := complement_probes M K
    rw [← hK]
    exact Cardinal.mk_le_of_injective (f := fun i => (⟨m i,hm i⟩ : {x // ¬ (target M K).e ∣ x}))
      (fun i j h => hinj (congrArg Subtype.val h))

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeHulls
attribute [-instance] _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalName _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## MonoidColimit -/

/-! The directed unions used by the monoid construction retain their
universal property against arbitrary monoid homomorphisms. The stronger
category of conservative height/cost embeddings is not a restriction on
the presentation universal property. -/


/-! ## DirectedPushout -/


/-! ## ConservativeHull -/

/-! Countable conservative submonoids.  This closes an arbitrary countable
set under specified countable dependencies, right factors and joins.  It is
only the hull part of the countable-base rearrangement; it does not identify
the complement presentation with an iterated gate tower. -/
namespace PartitionConsistency.CountableHull
universe u
noncomputable section
open scoped Classical
variable {A : Type u} (s : Set A) (op : A → A → Set A)

theorem countable (hs : s.Countable) (hop : ∀ x y, (op x y).Countable) :
    (carrier s op).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hs
  | succ n hn =>
    exact hn.union (hn.biUnion (fun x _ => hn.biUnion (fun y _ => hop x y)))

end
end PartitionConsistency.CountableHull

namespace PartitionConsistency.DiagramOrder
universe u
noncomputable section
open scoped Classical
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

namespace ConservativeHull

variable (hj : HasConditionalJoins (LeftDivOrder M))
variable (s : Set M) (deps : M → Set M)

omit [IsConical M] in
theorem contains : s ⊆ submonoid s deps :=
  fun _ h => CountableHull.subset_carrier _ _ (Set.mem_insert_of_mem _ h)

omit [IsConical M] in
theorem countable (hs : s.Countable) (hd : ∀ x, (deps x).Countable) :
    (submonoid s deps : Set M).Countable := by
  apply CountableHull.countable _ _ (hs.insert 1)
  intro x y
  exact ((Set.countable_singleton _).insert _ |>.insert _).union (hd x)

omit [IsConical M] in
theorem closed_deps {x : M} (hx : x ∈ submonoid s deps) :
    deps x ⊆ submonoid s deps := by
  intro y hy
  exact CountableHull.closed _ _ hx (submonoid s deps).one_mem (Or.inr hy)

end ConservativeHull
end
end PartitionConsistency.DiagramOrder


/-! ## ConservativeCategory -/

/-! Conservative monoids without height/cost bookkeeping. The original
saturated tower forgets to this category. It is used for rearrangements:
heights are needed for scheduling ideals, but not for old-gate descent. -/

namespace PartitionConsistency.ConservativeMonoids
universe u v w
open DiagramOrder CategoryTheory CategoryTheory.Limits
noncomputable section

attribute [instance] Object.monoid Object.conical

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ConservativeIntersections -/

/-! The intersections used when a presentation is restricted to a countable
hull. This establishes conservation at arbitrary cuts, not just selected cuts. -/


/-! ## Cell -/

/-! The actual countably presented operations, with their conservative
simulations and finite coefficient supports. These are the cells in the
original schedule, forgetting only the height/cost bookkeeping. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramForcing MonoidPushout
noncomputable section

namespace Probe
variable {M N : Object.{u}} (d : Probe M)

theorem parameters_countable : d.parameters.Countable :=
  (Set.toFinite ({d.a,d.b,d.e} : Set M)).countable.union (Set.countable_range _)

end Probe

namespace Merger
variable {M N : Object.{u}} (d : Merger M)

theorem parameters_countable : d.parameters.Countable := by
  have h : d.parameters ⊆ Set.range (fun ij : Fin d.n × Fin d.n =>
      ((d.prescription.start ij.1 ij.2).getD (1,1)).1) ∪
    Set.range (fun ij : Fin d.n × Fin d.n =>
      ((d.prescription.start ij.1 ij.2).getD (1,1)).2) := by
    rintro x ⟨i,j,a,b,hab,hx⟩
    rcases hx with rfl | rfl
    · exact Or.inl ⟨(i,j),by simp only [hab,Option.getD_some]⟩
    · exact Or.inr ⟨(i,j),by simp only [hab,Option.getD_some]⟩
  exact ((Set.countable_range _).union (Set.countable_range _)).mono h

end Merger

namespace Cell
variable {M N : Object.{u}}

theorem parameters_countable (d : Cell M) : d.parameters.Countable := by
  cases d with
  | inl d => exact d.parameters_countable
  | inr d => exact d.parameters_countable

end Cell

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellRestriction -/

/-! Reflecting a scheduled operation to a conservative subobject that
contains its literal countable parameter set. -/


/-! ## CellularTower -/

/-! Cellular towers inside their actual terminal monoid. The countable hull
retains literal generators and finite old coefficients. -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramOrder.ConservativeHull CategoryTheory MonoidPushout
noncomputable section
open scoped Classical

namespace Attachment
variable {T : Object.{u}} {S R : Subobject T} (d : Attachment S R)

theorem parameters_countable : d.parameters.Countable :=
  d.cell.parameters_countable.image _

end Attachment

variable (T : Object.{u}) (J : Type u) [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J]

namespace CellTower
variable {T J} (D : CellTower T J)

omit [WellFoundedLT J]

theorem dependencies_countable (x : T) : (D.dependencies x).Countable := by
  classical
  rw [dependencies]
  split
  · exact ((Attachment.parameters_countable _).union (Set.countable_range _)).union
      (Set.Countable.image (Finset.countable_toSet _) _)
  · exact Set.countable_empty

theorem hull_countable {s : Set T} (hs : s.Countable)
    (hb : ((D.stage ⊥).submonoid : Set T).Countable) :
    ((D.hull s).submonoid : Set T).Countable :=
  ConservativeHull.countable _ _ (hs.union hb) D.dependencies_countable

theorem subset_hull (s : Set T) : s ⊆ (D.hull s).submonoid :=
  fun _ hx => ConservativeHull.contains _ _ (Or.inl hx)

theorem bottom_le_hull (s : Set T) : (D.stage ⊥).submonoid ≤ (D.hull s).submonoid :=
  fun _ hx => ConservativeHull.contains _ _ (Or.inr hx)

theorem hull_closed {s : Set T} {x : T} (hx : x ∈ (D.hull s).submonoid) :
    D.dependencies x ⊆ (D.hull s).submonoid := ConservativeHull.closed_deps _ _ hx

end CellTower
end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellUnion -/

/-! Directed unions of conservative submonoids and of their presentation
pushouts. Every union here is inside the original terminal monoid. -/


/-! ## CellReorder -/

/-! Rearranging the actual tower: a countable dependency-closed submonoid
can be performed first, and every omitted cell can then be appended in its
original order. The construction uses full monoid pushouts at all cuts. -/
namespace PartitionConsistency.ConservativeMonoids.CellTower
universe u
open CategoryTheory DiagramOrder MonoidPushout _root_.OAI.PartitionConsistency.ConservativeMonoids.Subobject
noncomputable section
open scoped Classical
variable {T : Object.{u}} {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J] (D : CellTower T J) (S : Subobject T)

theorem reordered_bottom (hS : D.Closed S) (hbottom : (D.stage ⊥).submonoid ≤ S.submonoid) :
    ((D.reordered S hS).stage ⊥).submonoid = S.submonoid := by
  change (D.future S hS ⊥).submonoid = S.submonoid
  rw [D.future_eq S hS ⊥,sup_eq_right.mpr hbottom]

/-- Every countable set is contained in a countable initial base for a
reordering by the original two kinds of cells. -/
theorem countable_reordering (hbot : ((D.stage ⊥).submonoid : Set T).Countable)
    (s : Set T) (hs : s.Countable) :
    ∃ E : CellTower T J, ((E.stage ⊥).submonoid : Set T).Countable ∧
      s ⊆ (E.stage ⊥).submonoid := by
  let S := D.hull s
  have hS : D.Closed S := fun _ hx => D.hull_closed hx
  refine ⟨D.reordered S hS,?_,?_⟩
  all_goals rw [D.reordered_bottom S hS (D.bottom_le_hull s)]
  · exact D.hull_countable hs hbot
  · exact D.subset_hull s

end
end PartitionConsistency.ConservativeMonoids.CellTower

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingTruth
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.SetForcingNames.SymmetricSystem.instSmallWitnessIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionConsistency.ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

theorem forceFormula_neg (hA : A.Regular) {n} (v : Fin n → N) (p : P) (φ : Formula n) :
    A.ForceFormula v p φ.neg ↔ ∀ q, q ≤ p → ¬ A.ForceFormula v q φ :=
  A.forceFormula_imp hA v p φ .bot

theorem forceFormula_raise (hA : A.Regular) {n} (φ : Formula n) (v : Fin n → N)
    (x : N) (p : P) :
    A.ForceFormula (Fin.snoc v x) p φ.raise ↔ A.ForceFormula v p φ := by
  rw [A.forceFormula_rename hA]
  have h : Fin.snoc v x ∘ Fin.castSucc = v := by funext i; simp
  rw [h]

theorem forceFormula_instantiate (hA : A.Regular) {n} (φ : Formula (n+1))
    (t : Fin n) (v : Fin n → N) (p : P) :
    A.ForceFormula v p (φ.instantiate t) ↔ A.ForceFormula (Fin.snoc v (v t)) p φ := by
  rw [Formula.instantiate, A.forceFormula_rename hA]
  have h : v ∘ Fin.lastCases t id = Fin.snoc v (v t) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [h]

/-- Soundness for the actual classical calculus in forcing semantics. Unlike
the quotient-model argument this needs no countability assumption on the full
collection of names and constructs no generic over all names. -/
theorem forcing_sound (hA : A.Regular) {n} {Γ : Set (Formula n)} {φ : Formula n}
    (h : Derives Γ φ) (v : Fin n → N) (p : P)
    (hΓ : ∀ ψ ∈ Γ, A.ForceFormula v p ψ) : A.ForceFormula v p φ := by
  induction h generalizing p with
  | hyp hp => exact hΓ _ hp
  | weaken hsub _ ih => exact ih v p (fun ψ hψ => hΓ ψ (hsub hψ))
  | impI _ ih =>
    apply (A.forceFormula_imp hA _ _ _ _).mpr
    intro q hqp hq
    exact ih v q (fun ψ hψ => by
      rcases hψ with rfl | hψ
      · exact hq
      · exact A.forceFormula_mono hqp (hΓ _ hψ))
  | impE _ _ ih₁ ih₂ =>
    exact (A.forceFormula_imp hA _ _ _ _).mp (ih₁ v p hΓ) p le_rfl (ih₂ v p hΓ)
  | botE _ ih => exact (ih v p hΓ).elim
  | @classical n Γ φ _ ih =>
    apply A.forceFormula_of_dense hA
    intro q hqp
    by_contra! hn
    have hneg : A.ForceFormula v q φ.neg :=
      (A.forceFormula_neg hA _ _ _).mpr hn
    exact ih v q (fun ψ hψ => by
      rcases hψ with rfl | hψ
      · exact hneg
      · exact A.forceFormula_mono hqp (hΓ _ hψ))
  | conjI _ _ ih₁ ih₂ => exact ⟨ih₁ v p hΓ, ih₂ v p hΓ⟩
  | conjL _ ih => exact (ih v p hΓ).1
  | conjR _ ih => exact (ih v p hΓ).2
  | disjL _ ih =>
    apply (A.forceFormula_disj _ _ _ _).mpr
    intro q hqp
    exact ⟨q, le_rfl, Or.inl (A.forceFormula_mono hqp (ih v p hΓ))⟩
  | disjR _ ih =>
    apply (A.forceFormula_disj _ _ _ _).mpr
    intro q hqp
    exact ⟨q, le_rfl, Or.inr (A.forceFormula_mono hqp (ih v p hΓ))⟩
  | disjE _ _ _ ih₁ ih₂ ih₃ =>
    apply A.forceFormula_of_dense hA
    intro q hqp
    obtain ⟨r, hrq, hr | hr⟩ := (A.forceFormula_disj _ _ _ _).mp (ih₁ v p hΓ) q hqp
    · exact ⟨r, hrq, ih₂ v r (fun ψ hψ => by
        rcases hψ with rfl | hψ
        · exact hr
        · exact A.forceFormula_mono (hrq.trans hqp) (hΓ _ hψ))⟩
    · exact ⟨r, hrq, ih₃ v r (fun ψ hψ => by
        rcases hψ with rfl | hψ
        · exact hr
        · exact A.forceFormula_mono (hrq.trans hqp) (hΓ _ hψ))⟩
  | allI _ ih =>
    apply (A.forceFormula_all hA _ _ _).mpr
    intro x
    apply ih (Fin.snoc v x) p
    rintro ψ ⟨χ, hχ, rfl⟩
    exact (A.forceFormula_raise hA _ _ _ _).mpr (hΓ _ hχ)
  | allE t _ ih =>
    exact (A.forceFormula_instantiate hA _ _ _ _).mpr
      ((A.forceFormula_all hA _ _ _).mp (ih v p hΓ) (v t))
  | exI t _ ih =>
    intro q hqp
    exact ⟨q, le_rfl, v t, A.forceFormula_mono hqp
      ((A.forceFormula_instantiate hA _ _ _ _).mp (ih v p hΓ))⟩
  | exE _ _ ih₁ ih₂ =>
    apply A.forceFormula_of_dense hA
    intro q hqp
    obtain ⟨r, hrq, x, hr⟩ := ih₁ v p hΓ q hqp
    refine ⟨r, hrq, (A.forceFormula_raise hA _ _ _ _).mp (ih₂ (Fin.snoc v x) r ?_)⟩
    intro ψ hψ
    rcases hψ with rfl | hψ
    · exact hr
    · obtain ⟨χ, hχ, rfl⟩ := hψ
      exact (A.forceFormula_raise hA _ _ _ _).mpr
        (A.forceFormula_mono (hrq.trans hqp) (hΓ _ hχ))
  | eqRefl t => exact A.eq_refl p (v t)
  | eqSubst ψ _ _ ih₁ ih₂ =>
    apply (A.forceFormula_instantiate hA _ _ _ _).mpr
    apply (A.forceFormula_tuple_congr ψ _ _ p ?_).mp
      ((A.forceFormula_instantiate hA _ _ _ _).mp (ih₂ v p hΓ))
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using ih₁ v p hΓ
    · simpa using A.eq_refl p (v j)
  | rename r _ ih =>
    apply (A.forceFormula_rename hA _ _ _ _).mpr
    apply ih (v ∘ r) p
    intro ψ hψ
    exact (A.forceFormula_rename hA _ _ _ _).mp (hΓ _ ⟨ψ,hψ,rfl⟩)

/-- A nonempty regular forcing semantics yields ordinary syntactic consistency
for any theory whose axioms are all forced. Neither an externally generic
filter nor a countable class of names is needed. This is not an assertion that
the target axioms are forced in the constructed symmetric system. -/
theorem consistent_of_regular_forcing (hA : A.Regular) [Nonempty N] (p : P)
    {T : Theory} (hT : ∀ φ ∈ T, A.ForceFormula Fin.elim0 p φ) : Consistent T := by
  intro n hcontra
  let v : Fin n → N := fun _ => Classical.choice (inferInstance : Nonempty N)
  apply A.forcing_sound hA hcontra v p
  rintro _ ⟨φ,hφ,rfl⟩
  apply (A.forceFormula_rename hA _ _ _ _).mpr
  have hv : v ∘ (Fin.elim0 : Fin 0 → Fin n) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
  rw [hv]
  exact hT φ hφ

end PartitionConsistency.ForcingQuotient.AtomicData

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricNames
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex _root_.OAI.PartitionConsistency.SetForcingNames.SymmetricSystem.instSmallPowerCandidate _root_.OAI.PartitionConsistency.SetForcingNames.SymmetricSystem.instSmallWitnessIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v w

namespace SymmetricSystem
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Ordinary syntactic consistency follows if *all* axioms of a theory are
forced. This result does not assert the forcing of PP, ACwo, or failure of
Choice. In particular it is not the selected main theorem. -/
theorem consistent_of_forces {T : Theory} (p : P)
    (hT : ∀ φ ∈ T, S.Forces Fin.elim0 p φ) : Consistent T :=
  S.atomic.consistent_of_regular_forcing S.atomic_regular p hT

end SymmetricSystem
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem not_mem_empty (p : P) (σ : S.Name) : ¬ S.atomic.MemF p σ Name.empty := by
  intro h
  obtain ⟨r, _, τ, c, he, _, _⟩ := (S.mem_iff.mp h) p le_rfl
  exact ZFSet.notMem_empty _ he

/-- A local minimal-member witness obtained by genuine well-founded induction
on literal names. No generic filter or external well-foundedness of a model
is used in this lemma. -/
theorem minimal_member (σ ν : S.Name) (p : P) (hmem : S.atomic.MemF p ν σ) :
    ∃ q, q ≤ p ∧ ∃ τ : S.Name, S.atomic.MemF q τ σ ∧
      ∀ ρ : S.Name, ∀ r, r ≤ q → S.atomic.MemF r ρ τ → ¬ S.atomic.MemF r ρ σ := by
  classical
  induction ν using (InvImage.wf (fun ν : S.Name => ν.raw) child_wf).induction generalizing p with
  | h ν ih =>
    by_cases hn : ∃ q, q ≤ p ∧ ∃ ρ : S.Name, S.atomic.MemF q ρ ν ∧ S.atomic.MemF q ρ σ
    · obtain ⟨q, hqp, ρ, hρν, hρσ⟩ := hn
      obtain ⟨r, hrq, χ, c, he, _, heq⟩ := (S.mem_iff.mp hρν) q le_rfl
      have hχσ : S.atomic.MemF r χ σ :=
        (S.atomic.mem_congr heq (S.atomic.eq_refl r σ)).mp (S.atomic.mem_mono hrq hρσ)
      obtain ⟨s, hsr, τ, hτ, hmin⟩ := ih χ ⟨S.code c, he⟩ r hχσ
      exact ⟨s, hsr.trans (hrq.trans hqp), τ, hτ, hmin⟩
    · exact ⟨p, le_rfl, ν, hmem, fun ρ r hr hρν hρσ => hn ⟨r, hr, ρ, hρν, hρσ⟩⟩

/-- The schema's Extensionality instance. -/
theorem forces_extensionality (p : P) : S.Forces Fin.elim0 p SetLanguage.extensionality := by
  simp only [Forces, SetLanguage.extensionality, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal]
  intro σ τ q hqp h
  apply S.eq_of_same_members
  intro ν r hrq
  exact ⟨fun hν => (h ν).1 r hrq hν, fun hν => (h ν).2 r hrq hν⟩

/-- The schema's Empty Set instance. -/
theorem forces_emptySet (p : P) : S.Forces Fin.elim0 p SetLanguage.emptySet := by
  simp only [Forces, SetLanguage.emptySet, SetLanguage.empty,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_neg S.atomic_regular, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro q hqp
  refine ⟨q, le_rfl, Name.empty, ?_⟩
  intro σ r hrq
  exact S.not_mem_empty r σ

/-- The schema's Foundation instance, uniformly at every condition. -/
theorem forces_foundation (p : P) : S.Forces Fin.elim0 p SetLanguage.foundation := by
  simp only [Forces, SetLanguage.foundation, SetLanguage.nonempty,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro σ q hqp hnonempty r hrq
  obtain ⟨s, hsr, ν, hν⟩ := hnonempty r hrq
  obtain ⟨t, hts, τ, hτ, hmin⟩ := S.minimal_member σ ν s hν
  refine ⟨t, hts.trans hsr, τ, hτ, ?_⟩
  intro ρ a hat hρτ b hba hρσ
  exact hmin ρ b (hba.trans hat) (S.atomic.mem_mono hba hρτ) hρσ

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

theorem forceFormula_close (hA : A.Regular) {n} (φ : Formula n) (p : P) :
    A.ForceFormula Fin.elim0 p φ.close ↔ ∀ v : Fin n → N, A.ForceFormula v p φ := by
  induction n with
  | zero =>
    exact ⟨fun h v => Subsingleton.elim (Fin.elim0 : Fin 0 → N) v ▸ h,
      fun h => h Fin.elim0⟩
  | succ n ih =>
    rw [Formula.close, ih]
    simp only [A.forceFormula_all hA]
    constructor
    · intro h v
      have hv : Fin.snoc (fun i => v i.castSucc) (v (Fin.last n)) = v := by
        funext i
        refine Fin.lastCases ?_ (fun _ => ?_) i <;> simp
      exact hv ▸ h _ _
    · exact fun h v x => h (Fin.snoc v x)

end PartitionConsistency.ForcingQuotient.AtomicData

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Every individual instance of full Separation is forced. There is no bound
on the finite syntax, parameters, or ranks in this theorem. -/
theorem forces_separation {n} (φ : Formula (n+1)) (p : P) :
    S.Forces Fin.elim0 p (SetLanguage.separation φ) := by
  unfold SetLanguage.separation
  rw [Forces, S.atomic.forceFormula_close S.atomic_regular]
  simp only [S.atomic.forceFormula_all S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,
    S.atomic.forceFormula_rename S.atomic_regular, Fin.snoc_last, Fin.snoc_castSucc]
  intro v σ q hqp
  refine ⟨q,le_rfl,S.separate σ v φ,?_⟩
  intro ν
  have hv : Fin.snoc (Fin.snoc (Fin.snoc v σ) (S.separate σ v φ)) ν ∘
      Fin.lastCases (Fin.last (n + 2)) (fun i => i.castSucc.castSucc.castSucc) =
        Fin.snoc v ν := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hv]
  exact ⟨fun r _ => (S.mem_separate σ v φ ν r).mp,
    fun r _ => (S.mem_separate σ v φ ν r).mpr⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricSets
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex _root_.OAI.PartitionConsistency.SetForcingNames.SymmetricSystem.instSmallWitnessIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem codeOrder_codes (p q : P) : S.codeOrder (S.code p) (S.code q) ↔ p ≤ q := by
  constructor
  · rintro ⟨p',q',hp,hq,h⟩
    obtain rfl := S.code_injective hp
    obtain rfl := S.code_injective hq
    exact h
  · exact fun h => ⟨p,q,rfl,rfl,h⟩

theorem edge_union (σ ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ σ.union.raw ↔ ∃ (χ : S.Name) (c d : P),
    ZFSet.pair χ.raw (S.code c) ∈ σ.raw ∧
    ZFSet.pair ν.raw (S.code d) ∈ χ.raw ∧ p ≤ c ∧ p ≤ d := by
  change ZFSet.pair ν.raw (S.code p) ∈ unionName S.action.conditions S.codeOrder σ.raw ↔ _
  rw [edge_unionName_iff]
  constructor
  · rintro ⟨χ,c',d',hc,hd,_,hp,hq⟩
    obtain ⟨p',c,hp',rfl,hpc⟩ := hp
    obtain rfl := S.code_injective hp'
    obtain ⟨p',d,hp',rfl,hpd⟩ := hq
    obtain rfl := S.code_injective hp'
    exact ⟨σ.child hc,c,d,hc,hd,hpc,hpd⟩
  · rintro ⟨χ,c,d,hc,hd,hpc,hpd⟩
    exact ⟨χ.raw,S.code c,S.code d,hc,hd,S.code_mem p,
      (S.codeOrder_codes p c).mpr hpc,(S.codeOrder_codes p d).mpr hpd⟩

theorem mem_union (σ ν : S.Name) (p : P) : S.atomic.MemF p ν σ.union ↔
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ χ : S.Name,
      S.atomic.MemF r χ σ ∧ S.atomic.MemF r ν χ := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨χ,a,b,ha,hb,hca,hcb⟩ := (S.edge_union σ τ c).mp he
    refine ⟨r,hrq,χ,S.mem_of_edge ha (hrc.trans hca),?_⟩
    exact (S.atomic.mem_congr heq (S.atomic.eq_refl r χ)).mpr
      (S.mem_of_edge hb (hrc.trans hcb))
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,χ,hχ,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,hτ,hsc,heq⟩ := (S.mem_iff.mp hχ) r le_rfl
    have hντ : S.atomic.MemF s ν τ :=
      (S.atomic.mem_congr (S.atomic.eq_refl s ν) heq).mp (S.atomic.mem_mono hsr hν)
    obtain ⟨t,hts,η,d,hη,htd,heq'⟩ := (S.mem_iff.mp hντ) s le_rfl
    exact ⟨t,hts.trans (hsr.trans hrq),η,t,
      (S.edge_union σ η t).mpr ⟨τ,c,d,hτ,hη,hts.trans hsc,htd⟩,le_rfl,heq'⟩

/-- The Union axiom for arbitrary HS input names. -/
theorem forces_union (p : P) : S.Forces Fin.elim0 p SetLanguage.union := by
  simp only [Forces, SetLanguage.union, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_ex, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro σ q hqp
  refine ⟨q,le_rfl,σ.union,?_⟩
  intro ν
  exact ⟨fun r _ => (S.mem_union σ ν r).mp, fun r _ => (S.mem_union σ ν r).mpr⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The Pairing axiom, with the standard largest-condition name. -/
theorem forces_pairing (p : P) : S.Forces Fin.elim0 p SetLanguage.pairing := by
  simp only [Forces, SetLanguage.pairing, SetLanguage.unorderedPair, Formula.iff,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_disj, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal]
  intro σ τ q hqp
  refine ⟨q,le_rfl,σ.pair τ,?_⟩
  intro ν
  exact ⟨fun r _ => (S.mem_pair σ τ ν r).mp, fun r _ => (S.mem_pair σ τ ν r).mpr⟩

theorem mem_check (x : ZFSet.{u}) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (Name.check x) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y ∈ x, S.atomic.EqF r ν (Name.check y) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,_,heq⟩ := (S.mem_iff.mp h) q hqp
    obtain ⟨y,hy,hτ,_⟩ := edge_checkName_iff.mp he
    have hyτ : Name.check y = τ := Name.ext hτ
    exact ⟨r,hrq,y,hy,hyτ ▸ heq⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,y,hy,heq⟩ := h q hqp
    exact ⟨r,hrq,Name.check y,⊤,edge_checkName_iff.mpr ⟨y,hy,rfl,rfl⟩,le_top,heq⟩

theorem check_mem_of_mem {x y : ZFSet.{u}} (h : y ∈ x) (p : P) :
    S.atomic.MemF p (Name.check y) (Name.check x) :=
  S.mem_of_edge (edge_checkName_iff.mpr ⟨y,h,rfl,rfl⟩) le_top

/-- The check name of a ground successor is its internal successor. -/
theorem check_successor (x : ZFSet.{u}) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (Name.check (insert x x)) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧
        (S.atomic.MemF r ν (Name.check x) ∨ S.atomic.EqF r ν (Name.check x)) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,y,hy,heq⟩ := (S.mem_check _ ν p).mp h q hqp
    rcases ZFSet.mem_insert_iff.mp hy with rfl | hy
    · exact ⟨r,hrq,Or.inr heq⟩
    · exact ⟨r,hrq,Or.inl ((S.atomic.mem_congr heq (S.atomic.eq_refl r (Name.check x))).mpr
        (S.check_mem_of_mem hy r))⟩
  · intro h
    apply (S.mem_check _ ν p).mpr
    intro q hqp
    obtain ⟨r,hrq,hm | he⟩ := h q hqp
    · obtain ⟨s,hsr,y,hy,heq⟩ := (S.mem_check x ν r).mp hm r le_rfl
      exact ⟨s,hsr.trans hrq,y,ZFSet.mem_insert_iff.mpr (Or.inr hy),heq⟩
    · exact ⟨r,hrq,x,ZFSet.mem_insert_iff.mpr (Or.inl rfl),he⟩

/-- The Infinity witness is the literal check-name of the ground natural numbers. -/
theorem forces_infinity (p : P) : S.Forces Fin.elim0 p SetLanguage.infinity := by
  simp only [Forces, SetLanguage.infinity, SetLanguage.empty, SetLanguage.successor,
    S.atomic.forceFormula_rename S.atomic_regular, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_conj, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_disj,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal,
    ForcingQuotient.AtomicData.forceFormula_bot]
  intro q hqp
  refine ⟨q,le_rfl,Name.check ZFSet.omega,?_,?_⟩
  · intro r hrq
    refine ⟨r,le_rfl,Name.check ∅,S.check_mem_of_mem ZFSet.omega_zero r,?_⟩
    intro ν t htr ht
    change S.atomic.MemF t ν (Name.check ∅) at ht
    exact S.not_mem_empty t ν (by simpa only [Name.check_empty] using ht)
  · intro ν r hrq hν t htr
    obtain ⟨s,hst,x,hx,heq⟩ := (S.mem_check ZFSet.omega ν r).mp hν t htr
    refine ⟨s,hst,Name.check (insert x x),S.check_mem_of_mem (ZFSet.omega_succ hx) s,?_⟩
    intro ρ
    constructor
    · intro a has ha b hba
      obtain ⟨c,hcb,hc | hc⟩ := (S.check_successor x ρ a).mp ha b hba
      · exact ⟨c,hcb,Or.inl ((S.atomic.mem_congr (S.atomic.eq_refl c ρ)
          (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq)).mpr hc)⟩
      · exact ⟨c,hcb,Or.inr (S.atomic.eq_trans hc
          (S.atomic.eq_symm (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq)))⟩
    · intro a has ha
      apply (S.check_successor x ρ a).mpr
      intro b hba
      obtain ⟨c,hcb,hc | hc⟩ := ha b hba
      · exact ⟨c,hcb,Or.inl ((S.atomic.mem_congr (S.atomic.eq_refl c ρ)
          (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq)).mp hc)⟩
      · exact ⟨c,hcb,Or.inr (S.atomic.eq_trans hc
          (S.atomic.eq_mono (hcb.trans (hba.trans has)) heq))⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem subset_mono {p q : P} {σ τ : S.Name} (h : q ≤ p) (hsub : S.SubsetF p σ τ) :
    S.SubsetF q σ τ := fun ν r hr => hsub ν r (hr.trans h)

theorem subset_of_dense {p : P} {σ τ : S.Name}
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ S.SubsetF r σ τ) : S.SubsetF p σ τ := by
  intro ν q hqp hν
  apply S.atomic_regular.2 q ν τ
  intro r hrq
  obtain ⟨s,hsr,hs⟩ := h r (hrq.trans hqp)
  exact ⟨s,hsr,hs ν s le_rfl (S.atomic.mem_mono (hsr.trans hrq) hν)⟩

theorem edge_power (σ ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ (S.power σ).raw ↔
      ν.raw ⊆ S.subsetBound σ ∧ S.SubsetF p ν σ := by
  change ZFSet.pair ν.raw (S.code p) ∈
    S.collectRaw (fun i : S.PowerCandidate σ => i.val) (fun i p => S.SubsetF p i.val σ) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,q,hi,hν,hq⟩
    obtain rfl := S.code_injective hq
    have heq : i.val = ν := Name.ext hν
    exact ⟨hν ▸ i.property,heq ▸ hi⟩
  · rintro ⟨hb,hs⟩
    exact ⟨⟨ν,hb⟩,p,hs,rfl,rfl⟩

theorem mem_power (σ ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.power σ) ↔ S.SubsetF p ν σ := by
  constructor
  · intro h
    apply S.subset_of_dense
    intro q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
    have hτ := S.subset_mono hrc ((S.edge_power σ τ c).mp he).2
    exact ⟨r,hrq,(S.subset_congr heq (S.atomic.eq_refl r σ)).mpr hτ⟩
  · intro h
    have heq := S.normalize_eq σ ν h
    have hs : S.SubsetF p (S.normalize σ ν) σ :=
      (S.subset_congr heq (S.atomic.eq_refl p σ)).mp h
    exact (S.atomic.mem_congr heq (S.atomic.eq_refl p (S.power σ))).mpr
      (S.mem_of_edge ((S.edge_power σ (S.normalize σ ν) p).mpr
        ⟨S.normalize_bounded σ ν,hs⟩) le_rfl)

/-- Power Set with quantification over every HS name, including subsets at
arbitrarily high name ranks. -/
theorem forces_powerSet (p : P) : S.Forces Fin.elim0 p SetLanguage.powerSet := by
  simp only [Forces, SetLanguage.powerSet, S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_ex, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem]
  intro σ q hqp
  refine ⟨q,le_rfl,S.power σ,?_⟩
  intro ν
  simp only [S.forces_subset]
  exact ⟨fun r _ => (S.mem_power σ ν r).mp, fun r _ => (S.mem_power σ ν r).mpr⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricChoice
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_relation {n m} (φ : Formula (n+2)) (r : Fin n → Fin m)
    (x y : Fin m) (v : Fin m → S.Name) (p : P) :
    S.Forces v p (SetLanguage.relation φ r x y) ↔ S.RelF (v ∘ r) φ p (v x) (v y) := by
  rw [SetLanguage.relation, Forces, S.atomic.forceFormula_rename S.atomic_regular]
  have h : v ∘ Fin.lastCases y (Fin.lastCases x r) =
      Fin.snoc (Fin.snoc (v ∘ r) (v x)) (v y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Function.comp_def]
  rw [h]

theorem rel_left_congr {n} (v : Fin n → S.Name) (φ : Formula (n+2))
    {p : P} {x x' : S.Name} (y : S.Name) (heq : S.atomic.EqF p x x') :
    S.RelF v φ p x y ↔ S.RelF v φ p x' y := by
  apply S.atomic.forceFormula_tuple_congr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using S.atomic.eq_refl p y
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using heq
    · simpa using S.atomic.eq_refl p (v k)

theorem chosenWitness_spec {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : S.WitnessIndex σ v φ) :
    S.RelF v φ i.val.2 (σ.child i.val.1.property) (S.chosenWitness σ v φ i) :=
  Classical.choose_spec i.property

section SmallGroup
variable [Small.{u} Γ]

theorem witness_in_bound {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : S.WitnessIndex σ v φ) (p : P) :
    S.atomic.MemF p (S.chosenWitness σ v φ i) (S.replacementBound σ v φ) := by
  apply S.mem_of_edge (c := p) ?_ le_rfl
  change ZFSet.pair (S.chosenWitness σ v φ i).raw (S.code p) ∈ S.collectRaw
    (fun z : Γ × S.WitnessIndex σ v φ => z.1 • S.chosenWitness σ v φ z.2) (fun _ _ => True)
  apply (S.edge_collectRaw _ _ _ _).mpr
  exact ⟨(1,i),p,True.intro,by simp,rfl⟩

theorem bounded_local_witness {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : Edges σ.raw) (p : P) (hi : ∃ η, S.RelF v φ p (σ.child i.property) η) :
    ∃ η : S.Name, S.RelF v φ p (σ.child i.property) η ∧
      S.atomic.MemF p η (S.replacementBound σ v φ) := by
  let j : S.WitnessIndex σ v φ := ⟨(i,p),hi⟩
  exact ⟨S.chosenWitness σ v φ j,S.chosenWitness_spec σ v φ j,S.witness_in_bound σ v φ j p⟩

theorem image_in_bound {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    {p : P} (hfunc : S.SingleValuedF σ v φ p) (ν : S.Name) (himage : S.ImageF σ v φ p ν) :
    S.atomic.MemF p ν (S.replacementBound σ v φ) := by
  apply S.atomic_regular.2
  intro q hqp
  obtain ⟨r,hrq,x,hx,hφ⟩ := himage q hqp
  obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := (S.mem_iff.mp hx) r le_rfl
  let i : Edges σ.raw := ⟨(τ.raw,S.code c),he⟩
  have hi : σ.child i.property = τ := Name.ext rfl
  have hφ' : S.RelF v φ s τ ν := (S.rel_left_congr v φ ν heq).mp
    (S.atomic.forceFormula_mono hsr hφ)
  obtain ⟨η,hηφ,hηB⟩ := S.bounded_local_witness σ v φ i s ⟨ν,by simpa only [hi] using hφ'⟩
  rw [hi] at hηφ
  have hνη := hfunc τ ν η s (hsr.trans (hrq.trans hqp)) (S.mem_of_edge he hsc) hφ' hηφ
  exact ⟨s,hsr.trans hrq,(S.atomic.mem_congr hνη
    (S.atomic.eq_refl s (S.replacementBound σ v φ))).mpr hηB⟩

omit [Small.{u} Γ] in
theorem forces_imageFormula {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) (ν : S.Name) (p : P) :
    S.Forces (Fin.snoc (Fin.snoc v σ) ν) p (imageFormula φ) ↔ S.ImageF σ v φ p ν := by
  simp only [Forces, imageFormula, ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_conj, ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_relation, Fin.snoc_last, Fin.snoc_castSucc]
  have h (x : S.Name) : Fin.snoc (Fin.snoc (Fin.snoc v σ) ν) x ∘
      (fun i => i.castSucc.castSucc.castSucc) = v := by funext i; simp
  simp only [h]
  rfl

theorem mem_replacementImage {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) {p : P} (hfunc : S.SingleValuedF σ v φ p) (ν : S.Name) :
    S.atomic.MemF p ν (S.replacementImage σ v φ) ↔ S.ImageF σ v φ p ν := by
  rw [replacementImage, S.mem_separate, S.forces_imageFormula]
  exact ⟨And.right,fun h => ⟨S.image_in_bound σ v φ hfunc ν h,h⟩⟩

omit [Small.{u} Γ] in
theorem singleValued_of_totalFunctional {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) {p : P} (h : S.TotalFunctionalF σ v φ p) :
    S.SingleValuedF σ v φ p := by
  intro x y z q hqp hx hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,η,_,hη⟩ := h x q hqp hx r hrq
  exact ⟨s,hsr,S.atomic.eq_trans (hη y s le_rfl (S.atomic.forceFormula_mono (hsr.trans hrq) hy))
    (S.atomic.eq_symm (hη z s le_rfl (S.atomic.forceFormula_mono (hsr.trans hrq) hz)))⟩

/-- Every full Replacement instance is forced. The bound depends on the
particular domain, formula, and parameter tuple, and not on a prechosen class
of name ranks. -/
theorem forces_replacement {n} (φ : Formula (n+2)) (p : P) :
    S.Forces Fin.elim0 p (SetLanguage.replacement φ) := by
  unfold SetLanguage.replacement
  rw [Forces, S.atomic.forceFormula_close S.atomic_regular]
  simp only [S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular, Formula.iff,
    ForcingQuotient.AtomicData.forceFormula_ex, ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem, ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_relation, Fin.snoc_last, Fin.snoc_castSucc]
  have h3 (v : Fin n → S.Name) (a b c : S.Name) :
      Fin.snoc (Fin.snoc (Fin.snoc v a) b) c ∘ (fun i => i.castSucc.castSucc.castSucc) = v := by
    funext i
    simp
  have h4 (v : Fin n → S.Name) (a b c d : S.Name) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc v a) b) c) d ∘
        (fun i => i.castSucc.castSucc.castSucc.castSucc) = v := by
    funext i
    simp
  simp only [h3,h4]
  intro v σ q hqp h r hrq
  change S.TotalFunctionalF σ v φ q at h
  have hfunc := S.singleValued_of_totalFunctional σ v φ h
  have hf {t : P} (htq : t ≤ q) : S.SingleValuedF σ v φ t :=
    fun x y z a hat => hfunc x y z a (hat.trans htq)
  refine ⟨r,le_rfl,S.replacementImage σ v φ,?_⟩
  intro ν
  exact ⟨fun t htr => (S.mem_replacementImage σ v φ (hf (htr.trans hrq)) ν).mp,
    fun t htr => (S.mem_replacementImage σ v φ (hf (htr.trans hrq)) ν).mpr⟩

end SmallGroup
end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable [Small.{u} Γ] (S : SymmetricSystem.{u} P Γ)

/-- Full ZF in the concrete hereditary-symmetry interpretation. The quantifier
domain is the unbounded class of all HS names. Each schema instance is proved
by its own actual set-name, including unrestricted Separation and Replacement. -/
theorem forces_ZF (p : P) : ∀ φ ∈ SetLanguage.ZF, S.Forces Fin.elim0 p φ := by
  intro φ hφ
  cases hφ with
  | extensionality => exact S.forces_extensionality p
  | emptySet => exact S.forces_emptySet p
  | pairing => exact S.forces_pairing p
  | union => exact S.forces_union p
  | powerSet => exact S.forces_powerSet p
  | infinity => exact S.forces_infinity p
  | foundation => exact S.forces_foundation p
  | separation φ => exact S.forces_separation φ p
  | replacement φ => exact S.forces_replacement φ p

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_EquivariantMixing
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Mixing -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {ι : Type t} [Small.{u} ι]

theorem mix_fixed (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) (g : Γ) (hg : g ∈ H) :
    g • S.mix f a H hH hf ha = S.mix f a H hH hf ha :=
  Subtype.ext (S.collectName_fixed _ _ H (S.mixTest_permute f a H hf ha) g hg)

theorem edge_mix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) (ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ (S.mix f a H hH hf ha).raw ↔
      ∃ i : S.MixEntries f, (f i.1).child i.2.property = ν ∧ S.mixTest f a i p := by
  change ZFSet.pair ν.raw (S.code p) ∈
    S.collectRaw (fun i : S.MixEntries f => (f i.1).child i.2.property) (S.mixTest f a) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,c,hi,hν,hc⟩
    obtain rfl := S.code_injective hc
    exact ⟨i,Name.ext hν,hi⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,p,hR,congrArg Name.raw hi,rfl⟩

/-- The exact regular forcing value of membership in the union mixture. -/
theorem mem_mix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.mix f a H hH hf ha) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : ι, r ≤ a i ∧ S.atomic.MemF r ν (f i) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := S.mem_iff.mp h q hqp
    obtain ⟨i,hi,hia,hit⟩ := (S.edge_mix f a H hH hf ha τ c).mp he
    change S.atomic.MemF c ((f i.1).child i.2.property) (f i.1) at hit
    rw [hi] at hit
    exact ⟨r,hrq,i.1,hrc.trans hia,
      (S.atomic.mem_congr heq (S.atomic.eq_refl r (f i.1))).mpr (S.atomic.mem_mono hrc hit)⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,i,hria,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := S.mem_iff.mp hν r le_rfl
    let j : S.MixEntries f := ⟨i,⟨(τ.raw,S.code c),he⟩⟩
    have hj : (f j.1).child j.2.property = τ := Name.ext rfl
    have ht : S.mixTest f a j s := by
      change s ≤ a i ∧ S.atomic.MemF s ((f i).child he) (f i)
      exact ⟨hsr.trans hria,S.mem_of_edge he hsc⟩
    exact ⟨s,hsr.trans hrq,τ,s,(S.edge_mix f a H hH hf ha τ s).mpr ⟨j,hj,ht⟩,le_rfl,heq⟩

/-- Any coherent family is equal to its mixture below its activation
condition. This applies in particular to antichains, when coherence is vacuous. -/
theorem eq_mix_at (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i)
    (hcoh : ∀ i j p, p ≤ a i → p ≤ a j → S.atomic.EqF p (f i) (f j)) (i : ι) :
    S.atomic.EqF (a i) (S.mix f a H hH hf ha) (f i) := by
  apply S.eq_of_same_members
  intro ν q hqi
  constructor
  · intro h
    apply S.atomic_regular.2 q ν (f i)
    intro r hrq
    obtain ⟨s,hsr,j,hsj,hm⟩ := (S.mem_mix f a H hH hf ha ν q).mp h r hrq
    exact ⟨s,hsr,(S.atomic.mem_congr (S.atomic.eq_refl s ν)
      (hcoh j i s hsj (hsr.trans (hrq.trans hqi)))).mp hm⟩
  · intro h
    apply (S.mem_mix f a H hH hf ha ν q).mpr
    intro r hrq
    exact ⟨r,le_rfl,i,hrq.trans hqi,S.atomic.mem_mono hrq h⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## EquivariantMix -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ProductNames
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalName _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProductSystem -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Each HS name has a literal support of size at most the prescribed bound. -/
theorem name_support (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    ∃ J : Set I, Cardinal.mk J ≤ μ ∧ ∀ π ∈ SupportFilter.Fix J, π • σ = σ := by
  obtain ⟨J,hJ,hfix⟩ := σ.hs.symmetric
  refine ⟨J,hJ,?_⟩
  intro π hπ
  exact Subtype.ext (hfix hπ)

end
end PartitionConsistency.ProductForcing


/-! ## Label -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Check names reflect ground equality at every condition. This uses
well-foundedness of actual sets, and does not presume a generic extension. -/
theorem eq_check_iff (x y : ZFSet.{u}) (p : P) :
    S.atomic.EqF p (Name.check x) (Name.check y) ↔ x = y := by
  suffices h : ∀ x y : ZFSet.{u}, ∀ p : P,
      S.atomic.EqF p (Name.check x) (Name.check y) → x = y from
    ⟨h x y p, fun h => h ▸ S.atomic.eq_refl p (Name.check x)⟩
  intro x
  induction x using ZFSet.mem_wf.induction with
  | h x ih =>
    intro y p he
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      have hm := (S.atomic.mem_congr (S.atomic.eq_refl p (Name.check z)) he).mp
        (S.check_mem_of_mem hz p)
      obtain ⟨r,_,a,ha,he'⟩ := (S.mem_check y (Name.check z) p).mp hm p le_rfl
      exact (ih z hz a r he').symm ▸ ha
    · intro hz
      have hm := (S.atomic.mem_congr (S.atomic.eq_refl p (Name.check z)) he).mpr
        (S.check_mem_of_mem hz p)
      obtain ⟨r,_,a,ha,he'⟩ := (S.mem_check x (Name.check z) p).mp hm p le_rfl
      exact ih a ha z r (S.atomic.eq_symm he') ▸ ha

@[simp] theorem mem_check_check (x y : ZFSet.{u}) (p : P) :
    S.atomic.MemF p (Name.check x) (Name.check y) ↔ x ∈ y := by
  refine ⟨fun h => ?_,fun h => S.check_mem_of_mem h p⟩
  obtain ⟨r,_,z,hz,he⟩ := (S.mem_check y (Name.check x) p).mp h p le_rfl
  rw [(S.eq_check_iff x z r).mp he]
  exact hz

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

theorem bit_mono {p q : Poset M I κ} (h : q ≤ p) {j : I} {α : κ} {b : Bool}
    (hb : Bit p j α b) : Bit q j α b := by
  obtain ⟨p,rfl,hb⟩ := hb
  induction q using WithTop.recTopCoe with
  | top => simp at h
  | coe q =>
    exact (bit_coe q j α b).mpr ((WithTop.coe_le_coe.mp h).1 hb)

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
theorem bit_functional {p : Poset M I κ} {j : I} {α : κ} {b c : Bool}
    (hb : Bit p j α b) (hc : Bit p j α c) : b = c := by
  obtain ⟨q,rfl,hb⟩ := hb
  exact q.1.functional _ _ _ hb ((bit_coe q j α c).mp hc)

/-- Positive bits force their ground indices into the named label. -/
theorem mem_label_of_bit (c : κ → ZFSet.{u}) {j : I} {α : κ} {p : Poset M I κ}
    (hb : Bit p j α true) : (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (Name.check (c α)) (label (M := M) hμ c j) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).mem_of_edge (c := p) ?_ le_rfl
  rw [label_raw]
  exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨α,p,hb,rfl,rfl⟩

/-- The complete local-witness membership characterization of a canonical label. -/
theorem mem_label (c : κ → ZFSet.{u}) (j : I) (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (label (M := M) hμ c j) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ α : κ, Bit r j α true ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν (Name.check (c α)) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,d,he,hrd,heq⟩ := (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mp h q hqp
    rw [label_raw] at he
    obtain ⟨α,d',hα,hτ,hd⟩ := ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mp he
    have hh : Name.check (S := system (M := M) (I := I) (κ := κ) hμ) (c α) = τ := Name.ext hτ
    obtain rfl := (system (M := M) (I := I) (κ := κ) hμ).code_injective hd
    exact ⟨r,hrq,α,bit_mono hrd hα,hh ▸ heq⟩
  · intro h
    apply (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,α,hα,he⟩ := h q hqp
    exact ⟨r,hrq,Name.check (c α),r,
      by rw [label_raw]; exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨α,r,hα,rfl,rfl⟩,le_rfl,he⟩

/-- Negative bits force nonmembership; injectivity here is injectivity of the
ordinary ground-coordinate coding, not an assumed distinctness of labels. -/
theorem not_mem_label_of_bit (c : κ → ZFSet.{u}) (hc : Function.Injective c)
    {j : I} {α : κ} {p : Poset M I κ} (hb : Bit p j α false) :
    ¬ (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (Name.check (c α)) (label (M := M) hμ c j) := by
  intro hm
  obtain ⟨r,hrp,β,hβ,heq⟩ := (mem_label (M := M) hμ c j _ p).mp hm p le_rfl
  have hαβ := hc (((system (M := M) (I := I) (κ := κ) hμ).eq_check_iff (c α) (c β) r).mp heq)
  subst β
  have hbad := bit_functional (bit_mono hrp hb) hβ
  cases hbad

/-- Distinct index coordinates give forced-distinct actual set names, below
every product condition. -/
theorem label_not_equal [Uncountable κ] (c : κ → ZFSet.{u})
    (hc : Function.Injective c) [Nonempty (DiagramForcing.Diagram M I)]
    {j k : I} (hjk : j ≠ k) (p : Poset M I κ) :
    ¬ (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF p (label (M := M) hμ c j) (label (M := M) hμ c k) := by
  intro heq
  suffices hh : ∀ q : Condition M I κ, q ≤ p → False by
    induction p using WithTop.recTopCoe with
    | top => exact hh (⊤,Classical.choice inferInstance) le_top
    | coe p => exact hh p le_rfl
  intro q hqp
  obtain ⟨d,α,hdq,hj,hk⟩ := CohenForcing.Condition.separate_labels q.1 hjk
  let r : Condition M I κ := (d,q.2)
  have hrq : (r : Poset M I κ) ≤ q := WithTop.coe_le_coe.mpr ⟨hdq,le_rfl⟩
  have hej := (system (M := M) (I := I) (κ := κ) hμ).atomic.eq_mono (hrq.trans hqp) heq
  have hm : (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF (r : Poset M I κ) (Name.check (c α)) (label (M := M) hμ c k) :=
    mem_label_of_bit hμ c ((bit_coe r k α true).mpr hk)
  exact not_mem_label_of_bit hμ c hc ((bit_coe r j α false).mpr hj)
    (((system (M := M) (I := I) (κ := κ) hμ).atomic.mem_congr ((system (M := M) (I := I) (κ := κ) hμ).atomic.eq_refl _ _) hej).mpr hm)

theorem label_mem_labelSet (c : κ → ZFSet.{u}) (j : I) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (label (M := M) hμ c j) (labelSet (M := M) (I := I) hμ c) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).mem_of_edge (c := ⊤) ?_ le_top
  rw [labelSet_raw]
  exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨j,⊤,rfl,rfl,rfl⟩

end
end PartitionConsistency.ProductForcing


/-! ## FunctionName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The totality/uniqueness conjunct of the internal set-function sentence. -/
theorem functionOn_total {n} (v : Fin n → S.Name) (p : P) (f d : Fin n)
    (hf : S.Forces v p (SetLanguage.functionOn f d))
    (x : S.Name) {q : P} (hqp : q ≤ p) (hx : S.atomic.MemF q x (v d)) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.App s (v f) x y ∧
      ∀ z : S.Name, ∀ t, t ≤ s → S.App t (v f) x z → S.atomic.EqF t z y := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_edge] at hf
  exact hf.2 x q hqp hx

/-- Forced single-valuedness, with three unrestricted HS names as arguments. -/
theorem functionOn_unique {n} (v : Fin n → S.Name) (p : P) (f d : Fin n)
    (hf : S.Forces v p (SetLanguage.functionOn f d))
    (x y z : S.Name) (hx : S.atomic.MemF p x (v d))
    (hy : S.App p (v f) x y) (hz : S.App p (v f) x z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1 p y z
  intro q hqp
  obtain ⟨r,hrq,a,_,ha⟩ := S.functionOn_total v p f d hf x le_rfl hx q hqp
  exact ⟨r,hrq,S.atomic.eq_trans (ha y r le_rfl (S.app_mono (hrq.trans hqp) hy))
    (S.atomic.eq_symm (ha z r le_rfl (S.app_mono (hrq.trans hqp) hz)))⟩

theorem forces_nonempty {n} (v : Fin n → S.Name) (p : P) (a : Fin n) :
    S.Forces v p (SetLanguage.nonempty a) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, S.atomic.MemF r x (v a) := by
  simp only [Forces,SetLanguage.nonempty,S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_mem]
  rfl

/-- Unpacking a choice function retains exactly the original graph formula. -/
theorem forces_choiceOn {n} (v : Fin n → S.Name) (p : P) (c a : Fin n) :
    S.Forces v p (SetLanguage.choiceOn c a) ↔
      S.Forces ![v c,v a] p (SetLanguage.functionOn 0 1) ∧
      ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v a) →
        ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name,
          S.App s (v c) x y ∧ S.atomic.MemF s y x := by
  simp only [Forces,SetLanguage.choiceOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_edge]
  have hv : v ∘ ![c,a] = ![v c,v a] := by
    funext i
    fin_cases i <;> rfl
  simp [hv,Fin.snoc]

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ChoiceFailure
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalName _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OutsideLabel -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

theorem smul_labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (π : Equiv.Perm I) (hπ : π ∈ SupportFilter.Fix J) :
    π • labelOutside (M := M) hμ c J hJ = labelOutside (M := M) hμ c J hJ := by
  apply Name.ext
  rw [Name.smul_val,labelOutside_raw]
  apply (system (M := M) (I := I) (κ := κ) hμ).collectRaw_move _ _ _ _ π π
  · exact smul_label (M := M) hμ c π
  · intro j p
    apply and_congr (not_congr (SupportFilter.perm_mem_iff hπ j).symm)
    constructor
    · rintro rfl; exact move_top hμ π
    · intro hp
      apply ((system (M := M) (I := I) (κ := κ) hμ).move π).injective
      rw [hp,move_top]

theorem label_mem_labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    {j : I} (hj : j ∉ J) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (label (M := M) hμ c j)
      (labelOutside (M := M) hμ c J hJ) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).mem_of_edge (c := ⊤) ?_ le_top
  rw [labelOutside_raw]
  exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr
    ⟨j,⊤,⟨hj,rfl⟩,rfl,rfl⟩

theorem mem_labelOutside (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (labelOutside (M := M) hμ c J hJ) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j : I, j ∉ J ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν (label (M := M) hμ c j) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,d,he,_,heq⟩ := (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mp h q hqp
    rw [labelOutside_raw] at he
    obtain ⟨j,_,hj,hτ,_⟩ := ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mp he
    have hh : label (M := M) hμ c j = τ := Name.ext hτ
    exact ⟨r,hrq,j,hj.1,hh ▸ heq⟩
  · intro h
    apply (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,j,hj,heq⟩ := h q hqp
    refine ⟨r,hrq,label (M := M) hμ c j,⊤,?_,le_top,heq⟩
    rw [labelOutside_raw]
    exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr
      ⟨j,⊤,⟨hj,rfl⟩,rfl,rfl⟩

theorem labelOutside_subset (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (p : Poset M I κ) : (system (M := M) (I := I) (κ := κ) hμ).SubsetF p
      (labelOutside (M := M) hμ c J hJ) (labelSet (M := M) (I := I) hμ c) := by
  intro ν q hqp hν
  apply (mem_labelSet hμ c ν q).mpr
  intro r hrq
  obtain ⟨s,hsr,j,_,heq⟩ := (mem_labelOutside hμ c J hJ ν q).mp hν r hrq
  exact ⟨s,hsr,j,heq⟩

theorem mem_choiceFailureFamily (c : κ → ZFSet.{u})
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (choiceFailureFamily (M := M) (I := I) hμ c) ↔
      (system (M := M) (I := I) (κ := κ) hμ).SubsetF p ν (labelSet (M := M) (I := I) hμ c) ∧
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ τ, (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF r τ ν := by
  rw [choiceFailureFamily,(system (M := M) (I := I) (κ := κ) hμ).mem_separate,
    (system (M := M) (I := I) (κ := κ) hμ).mem_power,
    (system (M := M) (I := I) (κ := κ) hμ).forces_nonempty]
  rfl

theorem labelOutside_mem_family (c : κ → ZFSet.{u}) (J : Set I) (hJ : Cardinal.mk J ≤ μ)
    (hj : ∃ j : I, j ∉ J) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p (labelOutside (M := M) hμ c J hJ)
      (choiceFailureFamily (M := M) (I := I) hμ c) := by
  apply (mem_choiceFailureFamily hμ c _ p).mpr
  refine ⟨labelOutside_subset hμ c J hJ p,?_⟩
  obtain ⟨j,hj⟩ := hj
  intro q hqp
  exact ⟨q,le_rfl,label (M := M) hμ c j,label_mem_labelOutside hμ c J hJ hj q⟩

end
end PartitionConsistency.ProductForcing


/-! ## Failure -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
theorem Diagram.exists_outside (r : Diagram M I) (hsize : Cardinal.mk M < Cardinal.mk I) :
    ∃ j : I, j ∉ r.range := by
  apply (Set.ne_univ_iff_exists_notMem _).mp
  intro h
  have hc : Cardinal.mk r.range = Cardinal.mk I := by rw [h,Cardinal.mk_univ]
  have hr : Cardinal.mk r.range = Cardinal.mk M := Diagram.cardinal_range r
  exact (ne_of_lt hsize) (hr.symm.trans hc)

/-- No HS graph can choose from all nonempty subsets of the label set.
The proof moves an actual selected label, preserving both the graph's support
and its particular argument, and then amalgamates compatible conditions. -/
theorem not_choiceOn [Infinite M] [Infinite I] [Uncountable κ]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u}) (hc : Function.Injective c)
    (f : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    ¬ (system (M := M) (I := I) (κ := κ) hμ).Forces
      ![f,choiceFailureFamily (M := M) (I := I) hμ c] p (SetLanguage.choiceOn 0 1) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨em⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨em⟩⟩
  intro hchoice
  obtain ⟨hfun,hs⟩ := (S.forces_choiceOn _ _ _ _).mp hchoice
  obtain ⟨J,hJ,hfix⟩ := name_support hμ f
  obtain ⟨p₀,hp₀⟩ := exists_condition_below p
  obtain ⟨r,hr,hcover⟩ := Diagram.extend_through hsize e he p₀.2 (hcard ▸ hJ)
  have hrp : r ≤ p₀.2 := ⟨e,hr⟩
  let q : Condition M I κ := (p₀.1,r)
  have hqp₀ : (q : Poset M I κ) ≤ p₀ := WithTop.coe_le_coe.mpr ⟨le_rfl,hrp⟩
  have hqp : (q : Poset M I κ) ≤ p := hqp₀.trans hp₀
  have hrsize : Cardinal.mk r.range ≤ μ := by rw [Diagram.cardinal_range,hcard]
  let B := labelOutside (M := M) hμ c r.range hrsize
  have hB : ∀ t, S.atomic.MemF t B (choiceFailureFamily (M := M) (I := I) hμ c) :=
    labelOutside_mem_family hμ c r.range hrsize (Diagram.exists_outside r hsize)
  obtain ⟨s,hsq,y,hy,hym⟩ := hs B q hqp (hB q) q le_rfl
  obtain ⟨s',hs's,j,hjr,hyj⟩ := (mem_labelOutside hμ c r.range hrsize y s).mp hym s le_rfl
  have hys' : S.App s' f B (label (M := M) hμ c j) :=
    (S.app_congr (S.atomic.eq_refl s' f) (S.atomic.eq_refl s' B) hyj).mp (S.app_mono hs's hy)
  obtain ⟨t₀,ht₀⟩ := exists_condition_below s'
  obtain ⟨t,ht,htcover⟩ := Diagram.extend_through hsize e he t₀.2
    (J := {j}) (by simpa using (Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk M)))
  let d : Condition M I κ := (t₀.1,t)
  have hdt : (d : Poset M I κ) ≤ t₀ := WithTop.coe_le_coe.mpr ⟨le_rfl,⟨e,ht⟩⟩
  have hdq : (d : Poset M I κ) ≤ q := hdt.trans (ht₀.trans (hs's.trans hsq))
  have htr : t ≤ r := (WithTop.coe_le_coe.mp hdq).2
  have hjt : j ∈ t.range := htcover (Set.mem_singleton j)
  have hdapp : S.App (d : Poset M I κ) f B (label (M := M) hμ c j) :=
    S.app_mono (hdt.trans ht₀) hys'
  obtain ⟨π,hπ,hi,v,hvd,hvπd⟩ := compatible_placement hsize hmerger r t t htr htr t₀.1 t₀.1
    (CohenForcing.Condition.compatible_iff.mpr ⟨_,le_rfl,le_rfl⟩)
  have hπr : π ∈ SupportFilter.Fix r.range := (SupportFilter.mem_Fix _ _).mpr hπ
  have hπf : π • f = f := hfix π ((SupportFilter.mem_Fix _ _).mpr (fun j hj => hπ j (hcover hj)))
  have hπB : π • B = B := smul_labelOutside hμ c r.range hrsize π hπr
  have hπapp : S.App (permute π d : Poset M I κ) f B (label (M := M) hμ c (π j)) := by
    have hh := (S.app_symmetry π (d : Poset M I κ) f B (label (M := M) hμ c j)).mp hdapp
    simpa only [S,move_coe,hπf,hπB,smul_label] using hh
  have hvd' : (v : Poset M I κ) ≤ d := WithTop.coe_le_coe.mpr hvd
  have hvπd' : (v : Poset M I κ) ≤ permute π d := WithTop.coe_le_coe.mpr hvπd
  have hjπ : j ≠ π j := by
    intro hj
    apply hjr
    rw [← hi]
    refine ⟨hjt,?_⟩
    rw [Diagram.range_permute]
    exact ⟨j,hjt,hj.symm⟩
  apply label_not_equal hμ c hc hjπ (v : Poset M I κ)
  exact S.functionOn_unique ![f,choiceFailureFamily (M := M) (I := I) hμ c] v 0 1
    (S.atomic.forceFormula_mono (hvd'.trans (hdq.trans hqp)) hfun) B
    (label (M := M) hμ c j) (label (M := M) hμ c (π j)) (hB v)
    (S.app_mono hvd' hdapp) (S.app_mono hvπd' hπapp)

/-- The family in this counterexample consists of nonempty sets, at every
condition and with arbitrary HS names as potential elements. -/
theorem forces_members_nonempty (c : κ → ZFSet.{u}) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces
      ![choiceFailureFamily (M := M) (I := I) hμ c] p
      (.all ((Formula.mem 1 0).imp (SetLanguage.nonempty 1))) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  change S.atomic.ForceFormula _ p (.all _)
  rw [S.atomic.forceFormula_all S.atomic_regular]
  intro ν
  rw [S.atomic.forceFormula_imp S.atomic_regular]
  intro q hqp hm
  apply (S.forces_nonempty _ q 1).mpr
  exact ((mem_choiceFailureFamily hμ c ν q).mp hm).2

/-- The actual product symmetric system forces the negation of the encoded
first-order Axiom of Choice. No rank bound or countability restriction is
placed on the potential choosing graph. -/
theorem forces_not_AC [Infinite M] [Infinite I] [Uncountable κ]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u}) (hc : Function.Injective c) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces Fin.elim0 p SetLanguage.AC.neg := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  apply (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr
  intro q hqp hAC
  rw [SetLanguage.AC,S.atomic.forceFormula_all S.atomic_regular] at hAC
  have hh := hAC (choiceFailureFamily (M := M) (I := I) hμ c)
  rw [S.atomic.forceFormula_imp S.atomic_regular] at hh
  have hv : Fin.snoc Fin.elim0 (choiceFailureFamily (M := M) (I := I) hμ c) =
      ![choiceFailureFamily (M := M) (I := I) hμ c] := by ext i; fin_cases i; rfl
  rw [hv] at hh
  have hh' := hh q le_rfl (forces_members_nonempty hμ c q)
  obtain ⟨r,hrq,f,hf⟩ := hh' q le_rfl
  apply not_choiceOn hμ hcard hsize hmerger e he c hc f r
  apply (S.forces_choiceOn _ r 0 1).mpr
  exact (S.forces_choiceOn _ r 1 0).mp hf

end
end PartitionConsistency.ProductForcing


/-! ## LocalDecision -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_DiagramPlacements
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalName _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProbePlacement -/

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
noncomputable section
variable {M I : Type u} [LeftCancelMonoid M]

/-- A pointwise isomorphism of small whole diagrams extends to a ground
permutation, fixing any subdiagram at the same position in both. -/
theorem permutation_over_root (hsize : Cardinal.mk M < Cardinal.mk I)
    (s t p : Diagram M I) (b : M) (hs : s.sub b = p) (ht : t.sub b = p) :
    ∃ π : Equiv.Perm I, s.permute π = t ∧ ∀ j ∈ p.range, π j = j := by
  let E : M ≃ s.range := Equiv.ofInjective s s.injective
  let f : s.range ↪ I := E.symm.toEmbedding.trans t.toEmbedding
  obtain ⟨π,hπ⟩ := SmallPlacements.extend_permutation f (by simpa using hsize)
  have hst : s.permute π = t := by
    ext x
    change π (s x) = t x
    have hh := hπ (E x)
    change π (s x) = t (E.symm (E x)) at hh
    simpa only [Equiv.symm_apply_apply] using hh
  refine ⟨π,hst,?_⟩
  rintro j ⟨x,rfl⟩
  have h := congrArg (fun d : Diagram M I => d x)
    ((permute_sub π s b).trans (congrArg (fun d => d.sub b) hst))
  rw [hs,ht] at h
  exact h

end
end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

variable {μ : Cardinal.{u}} {K : Type u} (hμ : Cardinal.aleph0 ≤ μ)

/-- Place an arbitrary-rank witness inside the previously chosen `q`.
Only the existing Cohen condition is strengthened. Uncountably many probes
are used to choose a copy whose nonroot support misses that condition. -/
theorem witness_placement [Uncountable K]
    (hsize : Cardinal.mk M < Cardinal.mk I) (e : M) (hprobes : RootProbes e K)
    {n} (φ : Formula (n+1)) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q s : Diagram M I) (hq : q.sub e = p) (b : M) (hs : s.sub b = p)
    (hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hτ : ∀ π ∈ SupportFilter.Fix s.range, π • τ = τ)
    (d c : CohenForcing.Condition I κ) (hd : d.support ⊆ s.range)
    (hc : CohenForcing.Condition.Compatible c (d.restrict p.range))
    (hf : (system hμ).Forces (Fin.snoc v τ) ((d,s) : Poset M I κ) φ) :
    ∃ a : CohenForcing.Condition I κ, a ≤ c ∧
      ∃ ν : (system (M := M) (I := I) (κ := κ) hμ).Name,
        (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
        (system hμ).Forces (Fin.snoc v ν) ((a,q) : Poset M I κ) φ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hqp : q ≤ p := ⟨e,hq⟩
  by_cases hb : b = 1
  · have hsp : s = p := by simpa only [hb,Diagram.sub_one] using hs
    subst s
    have hd' : d.restrict p.range = d := d.restrict_eq_of_support_subset hd
    rw [hd'] at hc
    obtain ⟨a,hac,had⟩ := CohenForcing.Condition.compatible_iff.mp hc
    refine ⟨a,hac,τ,?_,S.atomic.forceFormula_mono (WithTop.coe_le_coe.mpr ⟨had,hqp⟩) hf⟩
    intro π hπ
    exact hτ π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hqp hj)))
  · obtain ⟨m,hm,hind⟩ := hprobes b hb
    have hroots (i : K) : (q.sub (m i)).sub b = p := by rw [Diagram.sub_sub,hm i,hq]
    choose π hπ hfix using fun i : K =>
      Diagram.permutation_over_root hsize s (q.sub (m i)) p b hs (hroots i)
    have hroot (i : K) : (d.permute (π i)).restrict p.range = d.restrict p.range :=
      CohenForcing.Condition.restrict_permute_of_fixes _ _ (hfix i)
    have hdπ (i : K) : (d.permute (π i)).support ⊆ (q.sub (m i)).range := by
      rw [CohenForcing.Condition.support_permute,← hπ i,Diagram.range_permute]
      exact Set.image_mono hd
    have hdisj : Pairwise (fun i j : K => Disjoint
        ((d.permute (π i)).support \ p.range) ((d.permute (π j)).support \ p.range)) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro k ⟨hki,hkp⟩ ⟨hkj,_⟩
      apply hkp
      have hh := Diagram.range_inter_sub q (m i) (m j) e (hind i j hij)
      rw [hq] at hh
      exact hh ▸ ⟨hdπ i hki,hdπ j hkj⟩
    obtain ⟨i,hi⟩ := SmallPlacements.exists_fresh_member
      (fun i => (d.permute (π i)).support \ p.range) c.support hdisj c.countable_support
    have hcroot : CohenForcing.Condition.Compatible (c.restrict p.range)
        ((d.permute (π i)).restrict p.range) := by
      rw [hroot i]
      exact hc.weaken (c.le_restrict _) le_rfl
    have hci := CohenForcing.Condition.compatible_of_disjoint_off_root c
      (d.permute (π i)) p.range hcroot (hi.mono_right Set.sdiff_subset).symm
    obtain ⟨a,hac,hai⟩ := CohenForcing.Condition.compatible_iff.mp hci
    have hπfix : π i ∈ SupportFilter.Fix p.range := (SupportFilter.mem_Fix _ _).mpr (hfix i)
    have hsup := transported_name_supported hμ s (q.sub (m i)) (π i) (hπ i) τ hτ
    have hvec : (fun k => π i • Fin.snoc v τ k) = Fin.snoc v (π i • τ) := by
      funext k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv _ hπfix]
    have hforce := (S.forces_symmetry (π i) φ (Fin.snoc v τ) ((d,s) : Poset M I κ)).mp hf
    rw [hvec,move_coe] at hforce
    change S.Forces _ (((d.permute (π i)),s.permute (π i)) : Poset M I κ) φ at hforce
    rw [hπ i] at hforce
    refine ⟨a,hac,π i • τ,?_,S.atomic.forceFormula_mono
      (WithTop.coe_le_coe.mpr ⟨hai,⟨m i,rfl⟩⟩) hforce⟩
    intro g hg
    exact hsup g ((SupportFilter.mem_Fix _ _).mpr (fun j hj =>
      (SupportFilter.mem_Fix _ _).mp hg j (q.range_sub_subset (m i) hj)))

/-- Existential witnesses, at any name rank, can all be localized onto the
one diagram `q` chosen before the formula's quantified value. The density
here is in the Cohen coordinate alone. -/
theorem localized_existential [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K)
    {n} (φ : Formula (n+1)) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q : Diagram M I) (hq : q.sub e = p)
    (hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d₀ : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces v ((d₀,p) : Poset M I κ) φ.ex)
    (c : CohenForcing.Condition I κ) (hc : c ≤ d₀) (hcq : c.support ⊆ q.range) :
    ∃ a : CohenForcing.Condition I κ, a ≤ c ∧ a.support ⊆ q.range ∧
      ∃ ν : (system (M := M) (I := I) (κ := κ) hμ).Name,
        (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
        (system hμ).Forces (Fin.snoc v ν) ((a,q) : Poset M I κ) φ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  have hqp : q ≤ p := ⟨e,hq⟩
  obtain ⟨r,hr,τ,hτ⟩ := hf ((c,q) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hc,hqp⟩)
  obtain ⟨r₀,hr₀⟩ := exists_condition_below r
  obtain ⟨J,hJ,hfix⟩ := name_support hμ τ
  obtain ⟨s,hs,hcover⟩ := Diagram.extend_through hsize e he r₀.2 (hcard ▸ hJ)
  have hsr : ((r₀.1,s) : Poset M I κ) ≤ r :=
    (WithTop.coe_le_coe.mpr (show (r₀.1,s) ≤ r₀ from ⟨le_rfl,⟨e,hs⟩⟩)).trans hr₀
  have hsc : ((r₀.1,s) : Poset M I κ) ≤ (c,q) := hsr.trans hr
  have hsp : s ≤ p := (WithTop.coe_le_coe.mp hsc).2.trans hqp
  have hsupτ : ∀ π ∈ SupportFilter.Fix s.range, π • τ = τ := by
    intro π hπ
    exact hfix π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (hcover hj)))
  have hsups : ∀ π ∈ SupportFilter.Fix s.range, ∀ i : Fin (n+1), π • (Fin.snoc v τ : Fin (n+1) → S.Name) i = (Fin.snoc v τ : Fin (n+1) → S.Name) i := by
    intro π hπ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hsupτ π hπ
    · simpa using hv π ((SupportFilter.mem_Fix _ _).mpr
        (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hsp hj))) j
  have hfs := (forces_iff_restrict hμ hsize hmerger φ (Fin.snoc v τ) s hsups r₀.1).mp
    (S.atomic.forceFormula_mono hsr hτ)
  obtain ⟨b,hb⟩ := hsp
  have hroot : CohenForcing.Condition.Compatible c ((r₀.1.restrict s.range).restrict p.range) :=
    CohenForcing.Condition.compatible_iff.mpr ⟨r₀.1,(WithTop.coe_le_coe.mp hsc).1,
      (r₀.1.le_restrict _).trans ((r₀.1.restrict s.range).le_restrict _)⟩
  obtain ⟨a,hac,ν,hν,hfν⟩ := witness_placement hμ hsize e hprobes φ v p q s hq b hb hv τ hsupτ
    (r₀.1.restrict s.range) c (r₀.1.support_restrict_subset _) hroot hfs
  have hvq : ∀ π ∈ SupportFilter.Fix q.range, ∀ i : Fin (n+1), π • (Fin.snoc v ν : Fin (n+1) → S.Name) i = (Fin.snoc v ν : Fin (n+1) → S.Name) i := by
    intro π hπ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hν π hπ
    · simpa using hv π ((SupportFilter.mem_Fix _ _).mpr
        (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hqp hj))) j
  refine ⟨a.restrict q.range,?_,a.support_restrict_subset _,ν,hν,
    (forces_iff_restrict hμ hsize hmerger φ (Fin.snoc v ν) q hvq a).mp hfν⟩
  intro z hz
  exact ⟨hac hz,hcq ((CohenForcing.Condition.mem_support c _).mpr ⟨z.1.2,z.2,hz⟩)⟩

end
end PartitionConsistency.ProductForcing


/-! ## TriplePlacement -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrbitNames
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalName _root_.OAI.PartitionConsistency.ProductForcing.instSmallLocalQuotient _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OrderedPair -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem mem_pair_left (p : P) (σ τ : S.Name) : S.atomic.MemF p σ (σ.pair τ) :=
  (S.mem_pair σ τ σ p).mpr (fun q _ => ⟨q,le_rfl,Or.inl (S.atomic.eq_refl q σ)⟩)

theorem mem_pair_right (p : P) (σ τ : S.Name) : S.atomic.MemF p τ (σ.pair τ) :=
  (S.mem_pair σ τ τ p).mpr (fun q _ => ⟨q,le_rfl,Or.inr (S.atomic.eq_refl q τ)⟩)

theorem mem_singleton (p : P) (σ τ : S.Name) :
    S.atomic.MemF p σ (τ.pair τ) ↔ S.atomic.EqF p σ τ := by
  rw [S.mem_pair]
  constructor
  · intro h
    apply S.atomic_regular.1
    intro q hqp
    obtain ⟨r,hrq,h | h⟩ := h q hqp <;> exact ⟨r,hrq,h⟩
  · intro h q hqp
    exact ⟨q,le_rfl,Or.inl (S.atomic.eq_mono hqp h)⟩

theorem eq_pair_singleton {p : P} {σ τ ν : S.Name}
    (he : S.atomic.EqF p (σ.pair τ) (ν.pair ν)) :
    S.atomic.EqF p σ ν ∧ S.atomic.EqF p τ ν := by
  constructor
  · exact (S.mem_singleton p σ ν).mp
      ((S.atomic.mem_congr (S.atomic.eq_refl p σ) he).mp (S.mem_pair_left p σ τ))
  · exact (S.mem_singleton p τ ν).mp
      ((S.atomic.mem_congr (S.atomic.eq_refl p τ) he).mp (S.mem_pair_right p σ τ))

/-- Cancellation for unordered pairs with a common first entry. -/
theorem eq_pair_cancel_left {p : P} {σ τ ν : S.Name}
    (he : S.atomic.EqF p (σ.pair τ) (σ.pair ν)) : S.atomic.EqF p τ ν := by
  apply S.atomic_regular.1
  intro q hqp
  have hm := (S.atomic.mem_congr (S.atomic.eq_refl p τ) he).mp (S.mem_pair_right p σ τ)
  obtain ⟨r,hrq,h | h⟩ := (S.mem_pair σ ν τ p).mp hm q hqp
  · have hs := S.eq_pair_congr (S.atomic.eq_refl r σ) h
    have h' := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hqp) he)) hs
    exact ⟨r,hrq,S.atomic.eq_trans h (S.atomic.eq_symm (S.eq_pair_singleton h').2)⟩
  · exact ⟨r,hrq,h⟩

/-- Injectivity of ordered-pair names is a forcing theorem, not an assumption
on the name quotient. -/
theorem eq_opair_iff {p : P} {σ σ' τ τ' : S.Name} :
    S.atomic.EqF p (σ.opair τ) (σ'.opair τ') ↔
      S.atomic.EqF p σ σ' ∧ S.atomic.EqF p τ τ' := by
  constructor
  · intro he
    have hσ : S.atomic.EqF p σ σ' := by
      apply S.atomic_regular.1
      intro q hqp
      have hm := (S.atomic.mem_congr (S.atomic.eq_refl p (σ.pair σ)) he).mp
        (S.mem_pair_left p (σ.pair σ) (σ.pair τ))
      obtain ⟨r,hrq,h | h⟩ := (S.mem_pair (σ'.pair σ') (σ'.pair τ') (σ.pair σ) p).mp hm q hqp
      · exact ⟨r,hrq,(S.eq_pair_singleton h).1⟩
      · exact ⟨r,hrq,S.atomic.eq_symm (S.eq_pair_singleton (S.atomic.eq_symm h)).1⟩
    refine ⟨hσ,?_⟩
    have h := S.atomic.eq_trans (S.atomic.eq_symm (S.eq_opair_congr hσ (S.atomic.eq_refl p τ))) he
    have h' := S.eq_pair_cancel_left h
    exact S.eq_pair_cancel_left h'
  · rintro ⟨hσ,hτ⟩
    exact S.eq_opair_congr hσ hτ

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Orbit -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The forcing membership value of an arbitrary collected family. The
index type, not the ranks of its entries, is required to be small. -/
theorem mem_collect {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (R : ι → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (permutes : ∀ g ∈ H, ∀ i p, R i p → ∃ j,
      f j = g • f i ∧ R j (S.move g p)) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.collect f R H hH permutes) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i a, R i a ∧ r ≤ a ∧ S.atomic.EqF r ν (f i) := by
  constructor
  · intro hm q hqp
    obtain ⟨r,hrq,τ,a,he,hra,heq⟩ := S.mem_iff.mp hm q hqp
    obtain ⟨i,b,hR,hτ,hba⟩ := (S.edge_collectRaw f R τ.raw (S.code a)).mp he
    obtain rfl := S.code_injective hba
    exact ⟨r,hrq,i,b,hR,hra,(Name.ext hτ : f i = τ) ▸ heq⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,i,a,hR,hra,heq⟩ := h q hqp
    exact ⟨r,hrq,f i,a,(S.edge_collectRaw f R _ _).mpr ⟨i,a,hR,rfl,rfl⟩,hra,heq⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
variable {M I : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- Compatible diagrams with the same center agree pointwise. This is the
functional feature of diagram forcing used by the name-orbit presentation. -/
theorem eq_of_compatible_centers {r p q : Diagram M I}
    (hrp : r ≤ p) (hrq : r ≤ q) (hcenter : p 1 = q 1) : p = q := by
  obtain ⟨a,rfl⟩ := hrp
  obtain ⟨b,rfl⟩ := hrq
  have hab : a = b := r.injective (by simpa only [sub_apply,mul_one] using hcenter)
  rw [hab]

end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Complete local-witness description of the partial graph, including the
moved diagram that authorizes a contributed pair. -/
theorem mem_orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF t ν (orbitGraph hμ c σ p) ↔
      ∀ q, q ≤ t → ∃ r, r ≤ q ∧ ∃ π : Equiv.Perm I,
        r ≤ (((⊤ : CohenForcing.Condition I κ),p.permute π) : Poset M I κ) ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν ((label (M := M) hμ c (π (p 1))).opair (π • σ)) := by
  rw [orbitGraph,(system (M := M) (I := I) (κ := κ) hμ).mem_collect]
  simp only [exists_eq_left]

/-- Application is computed by actual contributed input-output pairs. -/
theorem app_orbitGraph (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (x y : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x y ↔
      ∀ q, q ≤ t → ∃ r, r ≤ q ∧ ∃ π : Equiv.Perm I,
        r ≤ (((⊤ : CohenForcing.Condition I κ),p.permute π) : Poset M I κ) ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r x (label (M := M) hμ c (π (p 1))) ∧
        (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r y (π • σ) := by
  rw [(system (M := M) (I := I) (κ := κ) hμ).app_iff_mem_opair,mem_orbitGraph]
  simp only [(system (M := M) (I := I) (κ := κ) hμ).eq_opair_iff]

/-- The identity copy maps the label at the supporting diagram's center to
the original arbitrary-rank name. -/
theorem orbitGraph_app_self (c : κ → ZFSet.{u})
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I) :
    (system (M := M) (I := I) (κ := κ) hμ).App (((⊤ : CohenForcing.Condition I κ),p) : Poset M I κ) (orbitGraph hμ c σ p)
      (label (M := M) hμ c (p 1)) σ := by
  apply (app_orbitGraph hμ c σ p _ _ _).mpr
  intro q hq
  refine ⟨q,le_rfl,1,?_,?_,?_⟩
  · simpa only [Diagram.permute_one] using hq
  · exact (system (M := M) (I := I) (κ := κ) hμ).atomic.eq_refl q _
  · simpa only [one_smul] using (system (M := M) (I := I) (κ := κ) hμ).atomic.eq_refl q σ

/-- The graph is forced single-valued. Its two contributing diagrams are
compared only below a common condition, never by moving a fixed generic. -/
theorem orbitGraph_unique [Uncountable κ] (c : κ → ZFSet.{u})
    (hc : Function.Injective c)
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ)
    (x y z : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hy : (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x y)
    (hz : (system (M := M) (I := I) (κ := κ) hμ).App t (orbitGraph hμ c σ p) x z) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF t y z := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  apply S.atomic_regular.1
  intro q hq
  obtain ⟨r,hrq,π,hrπ,hxπ,hyπ⟩ := (app_orbitGraph hμ c σ p x y t).mp hy q hq
  obtain ⟨s,hsr,ρ,hsρ,hxρ,hzρ⟩ := (app_orbitGraph hμ c σ p x z t).mp hz r (hrq.trans hq)
  have heq := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hsr hxπ)) hxρ
  have hcenter : π (p 1) = ρ (p 1) := by
    by_contra hn
    exact label_not_equal hμ c hc hn s heq
  obtain ⟨s₀,hs₀⟩ := exists_condition_below s
  have hsp : s₀.2 ≤ p.permute π := (WithTop.coe_le_coe.mp (hs₀.trans (hsr.trans hrπ))).2
  have hsq : s₀.2 ≤ p.permute ρ := (WithTop.coe_le_coe.mp (hs₀.trans hsρ)).2
  have hp := Diagram.eq_of_compatible_centers hsp hsq hcenter
  have hn := smul_name_eq_of_diagram_eq hμ σ p hσ π ρ hp
  refine ⟨s,hsr.trans hrq,?_⟩
  rw [hn] at hyπ
  exact S.atomic.eq_trans (S.atomic.eq_mono hsr hyπ) (S.atomic.eq_symm hzρ)

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_LocalRecords
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Record -/


/-! The ground record calculation for local quotients. These results count
literal witnesses of local representation by a covariant family of names.
They do not assume that every normalized subset is such a class, or assert
that every local E-class has a witness without the forcing argument. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
variable {A I κ : Type u}

/-- The recorded partial function determines the original supported Cohen
condition up to the specified coordinate permutation. -/
theorem permute_eq_of_pullback_eq (r s : A ↪ I) (π : Equiv.Perm I)
    (hπ : ∀ x, π (r x) = s x) (d c : Condition I κ)
    (hd : d.support ⊆ Set.range r) (hc : c.support ⊆ Set.range s)
    (h : d.pullback r = c.pullback s) : d.permute π = c := by
  have hrecord (x : A) (k : κ) (b : Bool) :
      ((r x,k),b) ∈ d.graph ↔ ((s x,k),b) ∈ c.graph := by
    change ((x,k),b) ∈ (d.pullback r).graph ↔ ((x,k),b) ∈ (c.pullback s).graph
    rw [h]
  apply ext
  ext z
  constructor
  · intro hz
    have hmem := (mem_permute π d z).mp hz
    obtain ⟨x,hx⟩ := hd ((mem_support d _).mpr ⟨z.1.2,z.2,hmem⟩)
    have he : s x = z.1.1 := (hπ x).symm.trans ((congrArg π hx).trans (π.apply_symm_apply _))
    have hh := (hrecord x z.1.2 z.2).mp (hx ▸ hmem)
    simpa only [he] using hh
  · intro hz
    obtain ⟨x,hx⟩ := hc ((mem_support c _).mpr ⟨z.1.2,z.2,hz⟩)
    apply (mem_permute π d z).mpr
    have he : r x = π.symm z.1.1 := by
      apply π.injective
      rw [hπ,hx,π.apply_symm_apply]
    have hh := (hrecord x z.1.2 z.2).mpr (hx ▸ hz)
    simpa only [he] using hh

/-- A countable graph can be enumerated after adjoining `none`, including
when the condition is empty. -/
private theorem graph_code (d : Condition I κ) :
    ∃ f : ℕ → Option ((I × κ) × Bool),
      Set.range f = Set.insert none (Option.some '' d.graph) := by
  obtain ⟨f,hf⟩ := ((d.countable_graph.image Option.some).insert none).exists_eq_range
    (Set.insert_nonempty _ _)
  exact ⟨f,hf.symm⟩

/-- There are at most μ countable Cohen conditions on a space of size at
most μ when μ is a fixed point of countable exponentiation. -/
theorem cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hμ : μ ^ Cardinal.aleph0 = μ) (hI : Cardinal.mk I ≤ μ)
    (hκ : Cardinal.mk κ ≤ μ) : Cardinal.mk (Condition I κ) ≤ μ := by
  let f (d : Condition I κ) := (graph_code d).choose
  have hf : Function.Injective f := by
    intro d c h
    apply ext
    have he : Set.insert none (Option.some '' d.graph) =
        Set.insert none (Option.some '' c.graph) :=
      ((graph_code d).choose_spec.symm.trans (congrArg Set.range h)).trans
        (graph_code c).choose_spec
    ext z
    have hz := Set.ext_iff.mp he (some z)
    change (some z = none ∨ ∃ x ∈ d.graph, some x = some z) ↔
      (some z = none ∨ ∃ x ∈ c.graph, some x = some z) at hz
    simpa only [Option.some_ne_none,Option.some.injEq,exists_eq_right,false_or] using hz
  have hbool : Cardinal.lift.{u} (Cardinal.mk Bool) ≤ μ := by
    rw [Cardinal.mk_bool,Cardinal.lift_ofNat]
    exact Cardinal.natCast_le_aleph0.trans hω
  have hop : Cardinal.mk (Option ((I × κ) × Bool)) ≤ μ := by
    simp only [Cardinal.mk_option,Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_uzero]
    exact (add_le_add
      ((mul_le_mul' ((mul_le_mul' hI hκ).trans_eq (Cardinal.mul_eq_self hω)) hbool).trans_eq
        (Cardinal.mul_eq_self hω)) (Cardinal.one_le_aleph0.trans hω)).trans_eq
          (Cardinal.add_eq_self hω)
  calc
    Cardinal.mk (Condition I κ) ≤ Cardinal.mk (ℕ → Option ((I × κ) × Bool)) :=
      Cardinal.mk_le_of_injective hf
    _ = Cardinal.mk (Option ((I × κ) × Bool)) ^ Cardinal.aleph0 := by simp
    _ ≤ μ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hop
    _ = μ := hμ

end
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

namespace LocalWitness
variable {hμ} {F : GenericFilter (CohenForcing.Condition I κ)} {r : Diagram M I}
variable {C : I → (system (M := M) hμ).Name}

/-- Equal records identify the *actual* local quotient values. This proof
uses only name symmetry and reflection to the root, not an action on an
already evaluated extension. -/
theorem equal_of_record_eq [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (hC : ∀ π ∈ SupportFilter.Fix r.range, ∀ j, π • C j = C (π j))
    {τ σ : LocalName hμ c r} (w : LocalWitness hμ F r C τ) (z : LocalWitness hμ F r C σ)
    (hrecord : w.record = z.record) : LocalQuotient.ofName F τ = LocalQuotient.ofName F σ := by
  have hb : w.rootIndex = z.rootIndex := congrArg Prod.fst hrecord
  have hx : w.labelIndex = z.labelIndex := congrArg (fun t => t.2.1) hrecord
  have hd : w.condition.pullback w.diagram.toEmbedding =
      z.condition.pullback z.diagram.toEmbedding := congrArg (fun t => t.2.2) hrecord
  obtain ⟨π,hπ,hfix⟩ := Diagram.permutation_over_root hsize w.diagram z.diagram r w.rootIndex
    w.root (by rw [hb]; exact z.root)
  have hπval : ∀ x, π (w.diagram x) = z.diagram x := fun x =>
    congrArg (fun t : Diagram M I => t x) hπ
  have hdπ : w.condition.permute π = z.condition :=
    CohenForcing.Condition.permute_eq_of_pullback_eq _ _ π hπval
      w.condition z.condition w.supported z.supported hd
  have hπfix : π ∈ SupportFilter.Fix r.range := (SupportFilter.mem_Fix _ _).mpr hfix
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hm := (S.eq_symmetry π ((w.condition,w.diagram) : Poset M I κ)
    τ.name (C (w.diagram w.labelIndex))).mp w.represents
  have hplaced : S.atomic.EqF ((z.condition,z.diagram) : Poset M I κ)
      τ.name (C (z.diagram z.labelIndex)) := by
    dsimp only [S] at hm
    rw [move_coe] at hm
    simpa only [permute,hdπ,hπ,τ.fixed π hπfix,hC π hπfix,hπval,hx] using hm
  have heq := S.atomic.eq_trans hplaced (S.atomic.eq_symm z.represents)
  apply (LocalQuotient.ofName_eq F τ σ).mpr
  refine ⟨z.condition.restrict r.range,F.lower (z.condition.le_restrict _) z.mem,?_⟩
  have hsup : ∀ π ∈ SupportFilter.Fix r.range, ∀ i : Fin 2,
      π • (![τ.name,σ.name] : Fin 2 → S.Name) i = ![τ.name,σ.name] i := by
    intro π hπ i
    fin_cases i
    · exact τ.fixed π hπ
    · exact σ.fixed π hπ
  exact forces_at_supporting_root hμ hsize hmerger (.equal 0 1) ![τ.name,σ.name]
    r z.diagram ⟨z.rootIndex,z.root⟩ hsup z.condition (by
      simpa only [Forces,AtomicData.forceFormula_equal,Matrix.cons_val_zero,
        Matrix.cons_val_one] using heq)

end LocalWitness

end
end PartitionConsistency.ProductForcing


/-! ## Class -/


namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem mem_relationClass (A E x y : S.Name) (p : P) :
    S.atomic.MemF p y (S.relationClass A E x) ↔
      S.atomic.MemF p y A ∧ S.App p E x y := by
  rw [relationClass,S.mem_separate,S.forces_edge]
  rfl

theorem relationClass_congr {p : P} {A A' E E' x x' : S.Name}
    (hA : S.atomic.EqF p A A') (hE : S.atomic.EqF p E E')
    (hx : S.atomic.EqF p x x') :
    S.atomic.EqF p (S.relationClass A E x) (S.relationClass A' E' x') := by
  apply S.eq_of_same_members
  intro y q hqp
  rw [S.mem_relationClass,S.mem_relationClass]
  exact and_congr (S.atomic.mem_congr (S.atomic.eq_refl q y) (S.atomic.eq_mono hqp hA))
    (S.app_congr (S.atomic.eq_mono hqp hE) (S.atomic.eq_mono hqp hx) (S.atomic.eq_refl q y))

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_classOf {n} (v : Fin n → S.Name) (p : P) (τ A E x : Fin n) :
    S.Forces v p (SetLanguage.classOf τ A E x) ↔
      S.atomic.EqF p (v τ) (S.relationClass (v A) (v E) (v x)) := by
  simp only [Forces,SetLanguage.classOf,SetLanguage.classOfFormula,Formula.iff,
    S.atomic.forceFormula_rename S.atomic_regular,S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_edge]
  constructor
  · intro h
    apply S.eq_of_same_members
    intro y q hqp
    rw [S.mem_relationClass]
    exact ⟨(h y).1 q hqp,(h y).2 q hqp⟩
  · intro he y
    constructor
    · intro q hqp hy
      exact (S.mem_relationClass _ _ _ y q).mp
        ((S.atomic.mem_congr (S.atomic.eq_refl q y) (S.atomic.eq_mono hqp he)).mp hy)
    · intro q hqp hy
      exact (S.atomic.mem_congr (S.atomic.eq_refl q y) (S.atomic.eq_mono hqp he)).mpr
        ((S.mem_relationClass _ _ _ y q).mpr hy)

theorem forces_isClass {n} (v : Fin n → S.Name) (p : P) (τ A E : Fin n) :
    S.Forces v p (SetLanguage.isClass τ A E) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name,
        S.atomic.MemF r x (v A) ∧
        S.atomic.EqF r (v τ) (S.relationClass (v A) (v E) x) := by
  change S.atomic.ForceFormula v p _ ↔ _
  rw [SetLanguage.isClass,S.atomic.forceFormula_rename S.atomic_regular,
    SetLanguage.isClassFormula,ForcingQuotient.AtomicData.forceFormula_ex]
  simp only [ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,forces_classOf,Fin.snoc]
  rfl

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

theorem forces_localLabelClass_isClass (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (j : I) (hj : j ∈ r.range)
    (p : Poset M I κ) :
    (system hμ).Forces ![(localLabelClass hμ c r E hE j hj).name,labelSet hμ c,E] p
      (SetLanguage.isClass 0 1 2) := by
  apply ((system hμ).forces_isClass _ _ _ _ _).mpr
  intro q hqp
  exact ⟨q,le_rfl,label hμ c j,label_mem_labelSet hμ c j q,(system hμ).atomic.eq_refl _ _⟩

end
end PartitionConsistency.ProductForcing


/-! ## Availability -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_AvailableRecords
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer_normal _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Eligible -/


namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

theorem classRepresentationSet_denseBelow [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e*x))ᶜ : Set M) = Cardinal.mk M)
    (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r)
    (d₀ : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d₀,r) : Poset M I κ)
      (SetLanguage.isClass 0 1 2)) :
    ∀ d, d ≤ d₀ → ∃ a, a ≤ d ∧ a ∈ classRepresentationSet hμ c r E τ := by
  intro d hdd
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨t,ht,x,hx,heq⟩ := (S.forces_isClass _ _ _ _ _).mp hf
    ((d,r) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hdd,le_rfl⟩)
  obtain ⟨s,hst,j,hxj⟩ := (mem_labelSet hμ c x t).mp hx t le_rfl
  let : Nonempty (Diagram M I) := ⟨r⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  have hear := (WithTop.coe_le_coe.mp ((has.trans hst).trans ht))
  have hU : Cardinal.mk ↥(a.1.support ∪ {j}) ≤ Cardinal.mk M := by
    apply (Cardinal.mk_union_le _ _).trans
    have hω := Cardinal.aleph0_le_mk M
    apply (add_le_add (a.1.cardinal_support.trans hω) ?_).trans_eq (Cardinal.add_eq_self hω)
    simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hω
  obtain ⟨b,hb,hcover⟩ := Diagram.extend_through hsize e he a.2 hU
  have hba : b ≤ a.2 := ⟨e,hb⟩
  have hlt : ((a.1,b) : Poset M I κ) ≤ t :=
    ((WithTop.coe_le_coe.mpr (show (a.1,b) ≤ a from ⟨le_rfl,hba⟩)).trans has).trans hst
  have hls : ((a.1,b) : Poset M I κ) ≤ s :=
    (WithTop.coe_le_coe.mpr (show (a.1,b) ≤ a from ⟨le_rfl,hba⟩)).trans has
  refine ⟨a.1,hear.1,b,hba.trans hear.2,fun k hk => hcover (Or.inl hk),j,
    hcover (Or.inr (Set.mem_singleton j)),?_⟩
  exact S.atomic.eq_trans (S.atomic.eq_mono hlt heq)
    (S.relationClass_congr (S.atomic.eq_refl _ _) (S.atomic.eq_refl _ _)
      (S.atomic.eq_mono hls hxj))

end
end PartitionConsistency.ProductForcing


/-! ## ActualAvailability -/


/-! ## Contraction -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ConcreteSystem
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConcreteSystem.instNonemptyκ _root_.OAI.PartitionConsistency.ConcreteSystem.instUncountableK _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallChainCode _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CardinalParameters -/


/-! ## Instance -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
noncomputable section

theorem complement_cardinal :
    Cardinal.mk ((Set.range (fun x : T => T.e * x))ᶜ : Set T) = Cardinal.mk T := by
  have hh : (Set.range (fun x : T => T.e * x))ᶜ = {x : T | ¬ T.e ∣ x} := by
    ext x
    simp only [Set.mem_compl_iff,Set.mem_range,Set.mem_ofPred_eq,dvd_def]
    simp only [eq_comm]
  rw [hh,cardinal_T]
  exact Saturation.complement_cardinal Base.object K aleph_one_le_μ μ_countable_power
    base_cardinal_le cardinal_K

theorem forces_ZF (p : P) : ∀ φ ∈ SetLanguage.ZF, S.Forces Fin.elim0 p φ := S.forces_ZF p

theorem forces_not_AC (p : P) : S.Forces Fin.elim0 p SetLanguage.AC.neg :=
  ProductForcing.forces_not_AC aleph0_le_μ cardinal_T size_lt finiteMergers T.e
    complement_cardinal (posetCode κ) (posetCode_injective κ) p

end
end PartitionConsistency.ConcreteSystem


/-! ## LabelFiber -/

namespace PartitionConsistency.MonoidConstruction.Saturation
universe u
open DiagramOrder DiagramForcing LocalDiagramSystem
noncomputable section
variable (M : Object.{u}) (K : Type u) [Nonempty K]

/-- The source's exact label-fiber count in the actual executed saturated
monoid. All ideals at all final vertices are covered. No count of symbolic
E-classes is postulated here. -/
theorem labelFiber_cardinal {μ : Cardinal.{u}} (hω : Cardinal.aleph 1 ≤ μ)
    (hpow : μ ^ Cardinal.aleph0 = μ) (hM : Cardinal.mk M ≤ μ) (hK : Cardinal.mk K = μ)
    {I : Type u} {q : Diagram (target M K) I} (w : Vertex q) :
    Cardinal.mk ((labelSystem (M := target M K) (I := I)).vertexFiber w) = μ := by
  apply le_antisymm
  · have hh := Cardinal.mk_subtype_le (fun x : w.diagram.range =>
        (labelSystem (M := target M K) (I := I)).availability w.diagram w.index x = w.ideal)
    exact hh.trans_eq ((Diagram.cardinal_range w.diagram).trans (target_cardinal M K hω hpow hM hK))
  · obtain ⟨m,hinj,hm,_⟩ := ideal_probes M K w.index (target M K).e (target M K).e_ne_one w.ideal
    rw [← hK]
    exact Cardinal.mk_le_of_injective (labelFiberEmbedding w m hinj (fun i => (hm i).2.2.1)).injective

end
end PartitionConsistency.MonoidConstruction.Saturation


/-! ## Stabilizer -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section

namespace Chain
variable {v : Vertex q} (C : Chain v)

/-- The name-independent label set is fixed pointwise by every tail fixer. -/
theorem tailFixer_fixes_labels (hj : HasConditionalJoins (LeftDivOrder M))
    (k : C.tailFixer hj) (j : I) (hjv : j ∈ labelFiberSet v) : k.val.val.val j = j := by
  obtain ⟨i,hi⟩ := k.property
  apply hi
  apply labelFiberSet_subset (C.vertex i)
  rwa [← labelFiberSet_common hj (C.common i)]

end Chain
end
end PartitionConsistency.LocalDiagramSystem.Vertex

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_TailGraphs
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## TailCode -/

/-! Codes for actual symbolic classes along a component chain.  The
representing relation ignores a finite prefix and is covariant under each
eventual pointwise fixer, with the *same* code at the moved Cohen filter. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

namespace ChainCode
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

variable {hμ c hcard hsize hmerger hj E hE C}

/-- Every glued class has a code of genuine local name representatives. This
is a set-sized countable choice in the ambient ordinary computation; it is
not yet a claim that an external filter is generic. -/
theorem exists_representing_code (F : GenericFilter (CohenForcing.Condition I κ))
    (b : (D[F]).Glued hj v) :
    ∃ a : ChainCode hμ c C, Represents hμ c hcard hsize hmerger hj E hE C F a b := by
  have hex (i : ℕ) : ∃ τ : LocalName hμ c (C.vertex i).diagram,
      At hμ c hcard hsize hmerger hj E hE F (C.vertex i) τ.name b := by
    obtain ⟨x,hx⟩ := (D[F]).toGlued_surjective hj v (C.vertex i) (C.common i) b
    obtain ⟨σ,hσ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ F (C.vertex i).diagram) x.val.val
    exact ⟨σ,C.common i,x,σ,rfl,hσ,hx⟩
  choose a ha using hex
  exact ⟨a,0,fun i _ => ha i⟩

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## Graph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Exact Cartesian membership, including the assertion that every member
is an actual ordered pair. All witnesses remain HS names. -/
theorem mem_cartesianName (X Y ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.cartesianName X Y) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x y : S.Name,
        S.atomic.MemF r x X ∧ S.atomic.MemF r y Y ∧ S.atomic.EqF r ν (x.opair y) := by
  rw [cartesianName,S.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,i,a,hi,hra,he⟩ := h q hqp
    exact ⟨r,hrq,X.child i.1.property,Y.child i.2.property,
      S.atomic.mem_mono hra hi.1,S.atomic.mem_mono hra hi.2,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,y,hx,hy,he⟩ := h q hqp
    obtain ⟨s,hsr,σ,a,ha,hsa,hxσ⟩ := S.mem_iff.mp hx r le_rfl
    obtain ⟨t,hts,τ,b,hb,htb,hyτ⟩ := S.mem_iff.mp hy s hsr
    let i : S.ProductEntries X Y := (⟨(σ.raw,S.code a),ha⟩,⟨(τ.raw,S.code b),hb⟩)
    have hσ : X.child i.1.property = σ := Name.ext rfl
    have hτ : Y.child i.2.property = τ := Name.ext rfl
    refine ⟨t,hts.trans (hsr.trans hrq),i,t,?_,le_rfl,?_⟩
    · change S.atomic.MemF t (X.child i.1.property) X ∧
        S.atomic.MemF t (Y.child i.2.property) Y
      rw [hσ,hτ]
      exact ⟨S.mem_of_edge ha (hts.trans hsa),S.mem_of_edge hb htb⟩
    · change S.atomic.EqF t ν ((X.child i.1.property).opair (Y.child i.2.property))
      rw [hσ,hτ]
      exact S.atomic.eq_trans (S.atomic.eq_mono (hts.trans hsr) he)
        (S.eq_opair_congr (S.atomic.eq_mono hts hxσ) hyτ)

/-- The Cartesian name has precisely the usual membership value on pairs. -/
theorem opair_mem_cartesianName (X Y x y : S.Name) (p : P) :
    S.atomic.MemF p (x.opair y) (S.cartesianName X Y) ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y := by
  rw [S.mem_cartesianName]
  constructor
  · intro h
    have hd q (hqp : q ≤ p) : ∃ r, r ≤ q ∧ S.atomic.MemF r x X ∧ S.atomic.MemF r y Y := by
      obtain ⟨r,hrq,a,b,ha,hb,he⟩ := h q hqp
      obtain ⟨hxa,hyb⟩ := S.eq_opair_iff.mp he
      exact ⟨r,hrq,(S.atomic.mem_congr hxa (S.atomic.eq_refl r X)).mpr ha,
        (S.atomic.mem_congr hyb (S.atomic.eq_refl r Y)).mpr hb⟩
    exact ⟨S.atomic_regular.2 _ _ _ (fun q hqp => (hd q hqp).imp (fun r hr => ⟨hr.1,hr.2.1⟩)),
      S.atomic_regular.2 _ _ _ (fun q hqp => (hd q hqp).imp (fun r hr => ⟨hr.1,hr.2.2⟩))⟩
  · rintro ⟨hx,hy⟩ q hqp
    exact ⟨q,le_rfl,x,y,S.atomic.mem_mono hqp hx,S.atomic.mem_mono hqp hy,S.atomic.eq_refl q _⟩

omit [OrderTop P] in
/-- Unpacking an internal map leaves its full set-function conjunct intact. -/
theorem forces_mapsTo {n} (v : Fin n → S.Name) (p : P) (f a b : Fin n) :
    S.Forces v p (SetLanguage.mapsTo f a b) ↔
      S.Forces ![v f,v a] p (SetLanguage.functionOn 0 1) ∧
      ∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v a) →
        ∀ r, r ≤ q → S.App r (v f) x y → S.atomic.MemF r y (v b) := by
  simp only [Forces,SetLanguage.mapsTo,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_edge]
  have hv : (v ∘ ![f,a,b]) ∘ ![0,1] = ![v f,v a] ∘ ![0,1] := by
    funext i
    fin_cases i <;> rfl
  simp only [SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,hv]
  rfl

omit [OrderTop P] in
/-- Unpacking the graph-surjection sentence keeps all witnesses internal. -/
theorem forces_surjection {n} (v : Fin n → S.Name) (p : P) (f a b : Fin n) :
    S.Forces v p (SetLanguage.surjection f a b) ↔
      S.Forces ![v f,v a,v b] p (SetLanguage.mapsTo 0 1 2) ∧
      ∀ y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q y (v b) →
        ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x : S.Name,
          S.atomic.MemF s x (v a) ∧ S.App s (v f) x y := by
  simp only [Forces,SetLanguage.surjection,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_mem,S.forces_edge]
  have hv : (v ∘ ![f,a,b]) ∘ ![0,1,2] = ![v f,v a,v b] ∘ ![0,1,2] := by
    funext i
    fin_cases i <;> rfl
  simp only [SetLanguage.mapsTo,S.atomic.forceFormula_rename S.atomic_regular,hv]
  rfl

namespace BinaryRelation
variable {S} (R : S.BinaryRelation)
variable (X Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hX : ∀ g ∈ H, g • X = X) (hY : ∀ g ∈ H, g • Y = Y)
variable (hR : ∀ g ∈ H, ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))

theorem mem_graph (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (R.graph X Y H hH hX hY hR) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x y : S.Name,
        S.atomic.MemF r x X ∧ S.atomic.MemF r y Y ∧ R.holds r x y ∧
          S.atomic.EqF r ν (x.opair y) := by
  rw [graph,S.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,i,a,hi,hra,he⟩ := h q hqp
    exact ⟨r,hrq,X.child i.1.property,Y.child i.2.property,
      S.atomic.mem_mono hra hi.1.1,S.atomic.mem_mono hra hi.1.2,R.mono hra hi.2,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,y,hx,hy,hRxy,he⟩ := h q hqp
    obtain ⟨s,hsr,σ,a,ha,hsa,hxσ⟩ := S.mem_iff.mp hx r le_rfl
    obtain ⟨t,hts,τ,b,hb,htb,hyτ⟩ := S.mem_iff.mp hy s hsr
    let i : S.ProductEntries X Y := (⟨(σ.raw,S.code a),ha⟩,⟨(τ.raw,S.code b),hb⟩)
    have hσ : X.child i.1.property = σ := Name.ext rfl
    have hτ : Y.child i.2.property = τ := Name.ext rfl
    refine ⟨t,hts.trans (hsr.trans hrq),i,t,?_,le_rfl,?_⟩
    · change (S.atomic.MemF t (X.child i.1.property) X ∧
        S.atomic.MemF t (Y.child i.2.property) Y) ∧
        R.holds t (X.child i.1.property) (Y.child i.2.property)
      rw [hσ,hτ]
      exact ⟨⟨S.mem_of_edge ha (hts.trans hsa),S.mem_of_edge hb htb⟩,
        (R.congr (S.atomic.eq_mono hts hxσ) hyτ).mp (R.mono (hts.trans hsr) hRxy)⟩
    · change S.atomic.EqF t ν ((X.child i.1.property).opair (Y.child i.2.property))
      rw [hσ,hτ]
      exact S.atomic.eq_trans (S.atomic.eq_mono (hts.trans hsr) he)
        (S.eq_opair_congr (S.atomic.eq_mono hts hxσ) hyτ)

/-- Every application of this internal graph is exactly a related bounded
pair. No external function is substituted for an internal set graph. -/
theorem app_graph (x y : S.Name) (p : P) :
    S.App p (R.graph X Y H hH hX hY hR) x y ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ R.holds p x y := by
  rw [S.app_iff_mem_opair,R.mem_graph X Y H hH hX hY hR]
  constructor
  · intro h
    have hd q (hqp : q ≤ p) : ∃ r, r ≤ q ∧
        S.atomic.MemF r x X ∧ S.atomic.MemF r y Y ∧ R.holds r x y := by
      obtain ⟨r,hrq,a,b,ha,hb,hRab,he⟩ := h q hqp
      obtain ⟨hxa,hyb⟩ := S.eq_opair_iff.mp he
      exact ⟨r,hrq,(S.atomic.mem_congr hxa (S.atomic.eq_refl r X)).mpr ha,
        (S.atomic.mem_congr hyb (S.atomic.eq_refl r Y)).mpr hb,(R.congr hxa hyb).mpr hRab⟩
    refine ⟨S.atomic_regular.2 _ _ _ ?_,S.atomic_regular.2 _ _ _ ?_,R.regular ?_⟩
    · intro q hqp
      obtain ⟨r,hrq,hx,_,_⟩ := hd q hqp
      exact ⟨r,hrq,hx⟩
    · intro q hqp
      obtain ⟨r,hrq,_,hy,_⟩ := hd q hqp
      exact ⟨r,hrq,hy⟩
    · intro q hqp
      obtain ⟨r,hrq,_,_,hRxy⟩ := hd q hqp
      exact ⟨r,hrq,hRxy⟩
  · rintro ⟨hx,hy,hRxy⟩ q hqp
    exact ⟨q,le_rfl,x,y,S.atomic.mem_mono hqp hx,S.atomic.mem_mono hqp hy,
      R.mono hqp hRxy,S.atomic.eq_refl q _⟩

/-- Totality and uniqueness produce the internal function formula, including
its prohibition of non-pairs and out-of-domain graph entries. -/
theorem graph_functionOn (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z) :
    S.Forces ![R.graph X Y H hH hX hY hR,X] p (SetLanguage.functionOn 0 1) := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_orderedPair,S.forces_edge]
  constructor
  · intro ν q hqp hm r hrq
    obtain ⟨s,hsr,x,y,hx,_,_,he⟩ := (R.mem_graph X Y H hH hX hY hR ν q).mp hm r hrq
    refine ⟨s,hsr,x,?_⟩
    intro t hts
    exact ⟨t,le_rfl,y,S.atomic.mem_mono hts hx,S.atomic.eq_mono hts he⟩
  · intro x q hqp hx r hrq
    obtain ⟨s,hsr,y,hy,hRxy⟩ := htotal x q hqp hx r hrq
    refine ⟨s,hsr,y,(R.app_graph X Y H hH hX hY hR x y s).mpr
      ⟨S.atomic.mem_mono (hsr.trans hrq) hx,hy,hRxy⟩,?_⟩
    intro z t hts ha
    exact hone t (hts.trans (hsr.trans (hrq.trans hqp))) x z y
      ((R.app_graph X Y H hH hX hY hR x z t).mp ha).2.2 (R.mono hts hRxy)

/-- The same actual graph takes all its values in the specified codomain. -/

theorem graph_mapsTo (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z) :
    S.Forces ![R.graph X Y H hH hX hY hR,X,Y] p (SetLanguage.mapsTo 0 1 2) := by
  rw [S.forces_mapsTo]
  constructor
  · exact R.graph_functionOn X Y H hH hX hY hR p htotal hone
  · intro x y q _ _ r _ ha
    exact ((R.app_graph X Y H hH hX hY hR x y r).mp ha).2.1

/-- Dense local inverse witnesses give an internal surjection, not an
externally indexed family of maps. -/

theorem graph_surjection (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z)
    (honto : ∀ y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q y Y →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x : S.Name, S.atomic.MemF s x X ∧ R.holds s x y) :
    S.Forces ![R.graph X Y H hH hX hY hR,X,Y] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  constructor
  · exact R.graph_mapsTo X Y H hH hX hY hR p htotal hone
  · intro y q hqp hy r hrq
    obtain ⟨s,hsr,x,hx,hRxy⟩ := honto y q hqp hy r hrq
    exact ⟨s,hsr,x,hx,(R.app_graph X Y H hH hX hY hR x y s).mpr
      ⟨hx,S.atomic.mem_mono (hsr.trans hrq) hy,hRxy⟩⟩

end BinaryRelation
end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GraphFusion
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## IndexedGraph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The complete membership value of the graph. -/
theorem mem_indexedGraph (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.indexedGraph X f H hH hfix) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : X,
        S.atomic.EqF r ν ((Name.check x.val).opair (f x)) := by
  constructor
  · intro hm q hqp
    obtain ⟨r,hrq,τ,c,he,_,heq⟩ := S.mem_iff.mp hm q hqp
    obtain ⟨x,d,_,hτ,_⟩ := (S.edge_collectRaw
      (fun x : X => (Name.check x.val).opair (f x)) (fun _ _ => True) τ.raw (S.code c)).mp he
    exact ⟨r,hrq,x,(Name.ext hτ : (Name.check x.val).opair (f x) = τ) ▸ heq⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,x,heq⟩ := h q hqp
    refine ⟨r,hrq,(Name.check x.val).opair (f x),⊤,?_,le_top,heq⟩
    exact (S.edge_collectRaw (fun x : X => (Name.check x.val).opair (f x))
      (fun _ _ => True) _ _).mpr ⟨x,⊤,trivial,rfl,rfl⟩

/-- Every value asserted by the graph is one of its prescribed values, with
both the input and output transported by forced equality. -/
theorem app_indexedGraph (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (x y : S.Name) (p : P) :
    S.App p (S.indexedGraph X f H hH hfix) x y ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
        S.atomic.EqF r x (Name.check i.val) ∧ S.atomic.EqF r y (f i) := by
  rw [S.app_iff_mem_opair,S.mem_indexedGraph]
  simp only [S.eq_opair_iff]

theorem indexedGraph_app_at (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (i : X) (p : P) :
    S.App p (S.indexedGraph X f H hH hfix) (Name.check i.val) (f i) :=
  (S.app_indexedGraph X f H hH hfix _ _ p).mpr
    (fun q _ => ⟨q,le_rfl,i,S.atomic.eq_refl _ _,S.atomic.eq_refl _ _⟩)

/-- The ground-indexed name-family graph satisfies the unmodified internal
set-function formula. This includes the assertion that it has no junk entries. -/
theorem indexedGraph_functionOn (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) (p : P) :
    S.Forces ![S.indexedGraph X f H hH hfix,Name.check X] p (SetLanguage.functionOn 0 1) := by
  simp only [Forces,SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_orderedPair,S.forces_edge]
  constructor
  · intro ν q hqp hm r hrq
    obtain ⟨s,hsr,i,heq⟩ := (S.mem_indexedGraph X f H hH hfix ν q).mp hm r hrq
    refine ⟨s,hsr,Name.check i.val,?_⟩
    intro t hts
    exact ⟨t,le_rfl,f i,S.check_mem_of_mem i.property t,S.atomic.eq_mono hts heq⟩
  · intro ν q hqp hm r hrq
    obtain ⟨s,hsr,x,hx,heq⟩ := (S.mem_check X ν q).mp hm r hrq
    let i : X := ⟨x,hx⟩
    refine ⟨s,hsr,f i,?_,?_⟩
    · exact (S.app_congr (S.atomic.eq_refl s _) heq (S.atomic.eq_refl s (f i))).mpr
        (S.indexedGraph_app_at X f H hH hfix i s)
    · intro z t hts ha
      apply S.atomic_regular.1
      intro a hat
      obtain ⟨b,hba,j,hj,hz⟩ := (S.app_indexedGraph X f H hH hfix ν z t).mp ha a hat
      have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val b).mp
        (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hba.trans (hat.trans hts)) heq)) hj))
      exact ⟨b,hba,hij.symm ▸ hz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CheckGraph -/

/-! Literal ground graphs and their check names.  These lemmas keep the
internal set-function formula, including its no-junk-entries conjunct. -/


/-! ## Fusion -/

/-! Countable ground-sequence preservation by fusion at a fixed supporting
root. The diagram forcing is not asserted to be countably closed. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u v
noncomputable section
open scoped Classical
variable {I κ : Type u}

/-- Every countable family of downward-persistent dense requirements below
a Cohen condition can be met by one condition, by actual countable closure. -/
theorem countable_fusion {A : Type v} [Countable A]
    (d : Condition I κ) (R : A → Condition I κ → Prop)
    (hmono : ∀ i q r, r ≤ q → R i q → R i r)
    (hdense : ∀ i q, q ≤ d → ∃ r, r ≤ q ∧ R i r) :
    ∃ r, r ≤ d ∧ ∀ i, R i r := by
  let : Encodable A := Encodable.ofCountable A
  let step (n : ℕ) (q : Set.Iic d) : Set.Iic d :=
    match Encodable.decode (α := A) n with
    | none => q
    | some i => ⟨(hdense i q.val q.property).choose,
        (hdense i q.val q.property).choose_spec.1.trans q.property⟩
  have hstep (n : ℕ) (q : Set.Iic d) : (step n q).val ≤ q.val := by
    dsimp only [step]
    cases Encodable.decode (α := A) n with
    | none => exact le_rfl
    | some i => exact (hdense i q.val q.property).choose_spec.1
  have hreq (i : A) (q : Set.Iic d) : R i (step (Encodable.encode i) q).val := by
    dsimp only [step]
    rw [Encodable.encodek]
    exact (hdense i q.val q.property).choose_spec.2
  let seq : ℕ → Set.Iic d := fun n => Nat.rec (⟨d,show d ≤ d from le_rfl⟩ : Set.Iic d) (fun n q => step n q) n
  have hseq : Antitone (fun n => (seq n).val) :=
    antitone_nat_of_succ_le (fun n => hstep n (seq n))
  obtain ⟨r,hr⟩ := countably_closed (fun n => (seq n).val) hseq
  refine ⟨r,hr 0,fun i => ?_⟩
  exact hmono i (seq (Encodable.encode i+1)).val r (hr (Encodable.encode i + 1)) (hreq i (seq (Encodable.encode i)))

end
end PartitionConsistency.CohenForcing.Condition


/-! ## StableIdeal -/

/-! Dense stabilization of the actual availability ideals. This is a
condition-by-condition form of the countable-closure argument: it involves
no filter asserted to meet an unbounded collection of ambient dense sets. -/
namespace PartitionConsistency.DiagramOrder.HeightCost
universe u v
noncomputable section
open scoped Classical
variable {α : Type u} [PartialOrder α] (H : HeightCost α)
variable {P : Type v} [Preorder P]

include H in
/-- A monotone system of directed bounded ideals in a height-and-cost order
is locally constant on a dense set in any countably closed forcing. The
heights of possible future elements are approximated during a descending
construction. Positive costs exclude every still-missing element at its
countable lower bound. -/
theorem dense_stable_ideal (hclosed : ∀ f : ℕ → P, Antitone f → ∃ p, ∀ n, p ≤ f n)
    (hj : HasConditionalJoins α) {a : α} (U : P → ConeIdeal a)
    (hmono : ∀ {p q : P}, q ≤ p → (U p).carrier ⊆ (U q).carrier) (p : P) :
    ∃ q, q ≤ p ∧ ∀ r, r ≤ q → U r = U q := by
  let V (q : P) : Set α := {x | ∃ r, r ≤ q ∧ x ∈ (U r).carrier}
  let s (q : P) : ℝ := sSup (H.height '' V q)
  have hv (q : P) : (V q).Nonempty := by
    obtain ⟨x,hx⟩ := (U q).nonempty
    exact ⟨x,q,le_rfl,hx⟩
  have hb (q : P) : BddAbove (H.height '' V q) := by
    refine ⟨1,?_⟩
    rintro _ ⟨x,_,rfl⟩
    exact (H.height_lt_one x).le
  have hstep (n : ℕ) (q : P) :
      ∃ r, r ≤ q ∧ ∃ x ∈ (U r).carrier, s q - 1 / (n+1 : ℝ) < H.height x := by
    have hpos : (0 : ℝ) < 1 / (n+1 : ℝ) := by positivity
    have hs : s q - 1 / (n+1 : ℝ) < s q := by linarith
    obtain ⟨_,⟨x,⟨r,hr,hx⟩,rfl⟩,h⟩ :=
      (lt_csSup_iff (hb q) ((hv q).image H.height)).mp hs
    exact ⟨r,hr,x,hx,h⟩
  choose next hnext x hx happrox using hstep
  let f : ℕ → P := Nat.rec p (fun n q => next n q)
  have hf : Antitone f := antitone_nat_of_succ_le (fun n => hnext n (f n))
  obtain ⟨q,hq⟩ := hclosed f hf
  refine ⟨q,hq 0,fun r hr => ?_⟩
  apply ConeIdeal.ext
  apply Set.Subset.antisymm _ (hmono hr)
  intro d hd
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (H.cost_pos d)
  let z := x n (f n)
  have hzq : z ∈ (U q).carrier := hmono (hq (n+1)) (hx n (f n))
  have hzr : z ∈ (U r).carrier := hmono hr hzq
  by_contra hbad
  have hdz : ¬ d ≤ z := fun h => hbad ((U q).lower h hzq)
  obtain ⟨w,hw,hzw,hdw⟩ := (U r).directed hj z hzr d hd
  have hzw' : z < w := lt_of_le_not_ge hzw (fun h => hdz (hdw.trans h))
  have hcost := H.point_margin hzw' hdw hdz
  have hupper : H.height w ≤ s (f n) :=
    le_csSup (hb (f n)) ⟨w,⟨r,hr.trans (hq n),hw⟩,rfl⟩
  have happ : s (f n) - 1 / (n+1 : ℝ) < H.height z := happrox n (f n)
  linarith

end
end PartitionConsistency.DiagramOrder.HeightCost

namespace PartitionConsistency.ForcingQuotient
universe u
variable {P : Type u} [Preorder P]

theorem AtomicData.eqG_principal {N : Type*} (A : AtomicData P N) (p : P) (σ τ : N) :
    A.EqG (principalFilter p) σ τ ↔ A.EqF p σ τ := by
  constructor
  · rintro ⟨q,hq,heq⟩
    exact A.eq_mono hq heq
  · intro h
    exact ⟨p,le_rfl,h⟩

end PartitionConsistency.ForcingQuotient


/-! ## StableAvailability -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ)
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)

theorem mem_localAvailability (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) (n : LeftDivOrder M) :
    n ∈ (localAvailability hμ c hcard hsize hmerger F r a τ).carrier ↔
      n ≤ a ∧ ∃ d : CohenForcing.Condition I κ, d ∈ F ∧ ForcedAvailable hμ c d r τ n := by
  change (n ≤ a ∧ ∃ x : LocalQuotient (c := c) hμ F (r.sub n),
    LocalQuotient.restrict F (r.self_le_sub n) x = LocalQuotient.ofName F τ) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨σ,rfl⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ F (r.sub n)) x
    obtain ⟨d,hd,he⟩ := (LocalQuotient.ofName_eq F (σ.restrict (r.self_le_sub n)) τ).mp hx
    exact ⟨d,hd,σ,he⟩
  · rintro ⟨d,hd,σ,he⟩
    refine ⟨LocalQuotient.ofName F σ,?_⟩
    exact (LocalQuotient.ofName_eq F (σ.restrict (r.self_le_sub n)) τ).mpr ⟨d,hd,he⟩

theorem mem_forcedAvailability (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (a : M) (τ : LocalName hμ c r) (n : LeftDivOrder M) :
    n ∈ (forcedAvailability hμ c hcard hsize hmerger d r a τ).carrier ↔
      n ≤ a ∧ ForcedAvailable hμ c d r τ n := by
  rw [forcedAvailability,mem_localAvailability]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨s,hs,σ,he⟩
    exact ⟨σ,(system hμ).atomic.eq_mono
      (p := ((s,r) : Poset M I κ)) (q := ((d,r) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨hs,le_rfl⟩) he⟩
  · intro h
    exact ⟨d,show d ≤ d from le_rfl,h⟩

omit [Infinite M] [Infinite I] in
theorem ForcedAvailable.mono {d e : CohenForcing.Condition I κ} (hed : e ≤ d)
    {r : Diagram M I} {τ : LocalName hμ c r} {n : M}
    (h : ForcedAvailable hμ c d r τ n) : ForcedAvailable hμ c e r τ n := by
  obtain ⟨σ,hσ⟩ := h
  exact ⟨σ,(system hμ).atomic.eq_mono
    (p := ((d,r) : Poset M I κ)) (q := ((e,r) : Poset M I κ))
    (WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩) hσ⟩

theorem forcedAvailability_mono {d e : CohenForcing.Condition I κ} (hed : e ≤ d)
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) :
    (forcedAvailability hμ c hcard hsize hmerger d r a τ).carrier ⊆
      (forcedAvailability hμ c hcard hsize hmerger e r a τ).carrier := by
  intro n hn
  rw [mem_forcedAvailability] at hn ⊢
  exact ⟨hn.1,ForcedAvailable.mono hμ c hed hn.2⟩

/-- Forced equality identifies the two actual ideals, not just their
cardinalities. -/
theorem forcedAvailability_congr (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (a : M) (τ σ : LocalName hμ c r)
    (heq : (system hμ).atomic.EqF ((d,r) : Poset M I κ) τ.name σ.name) :
    forcedAvailability hμ c hcard hsize hmerger d r a τ =
      forcedAvailability hμ c hcard hsize hmerger d r a σ := by
  apply ConeIdeal.ext
  ext n
  rw [mem_forcedAvailability,mem_forcedAvailability]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨ν,hν⟩
    exact ⟨ν,(system hμ).atomic.eq_trans hν heq⟩
  · rintro ⟨ν,hν⟩
    exact ⟨ν,(system hμ).atomic.eq_trans hν ((system hμ).atomic.eq_symm heq)⟩

/-- The set of available subdiagrams of every local name can be made
permanently constant by strengthening only its Cohen coordinate. -/
theorem forcedAvailability_dense_stable (H : HeightCost (LeftDivOrder M))
    (hj : HasConditionalJoins (LeftDivOrder M)) (d : CohenForcing.Condition I κ)
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) :
    ∃ e, e ≤ d ∧ ∀ f, f ≤ e →
      forcedAvailability hμ c hcard hsize hmerger f r a τ =
        forcedAvailability hμ c hcard hsize hmerger e r a τ :=
  H.dense_stable_ideal CohenForcing.Condition.countably_closed hj
    (fun s => forcedAvailability hμ c hcard hsize hmerger s r a τ)
    (fun h => forcedAvailability_mono hμ c hcard hsize hmerger h r a τ) d

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_PersistentCodes
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeSelection -/

/-! Least-code selection at the level of forcing conditions. No generic
filter, regular ultrafilter, or selection of values in another universe is
assumed. The equivalence relation has a monotone truth value, and working
codes persist under refinement. -/
namespace PartitionConsistency.ConditionCodeSelection
universe u v
noncomputable section
variable {P : Type u} [Preorder P] {A : Type v}
variable (W : P → A → Prop) (E : P → A → A → Prop)

variable (wmono : ∀ {p q a}, q ≤ p → W p a → W q a)
variable (emono : ∀ {p q a b}, q ≤ p → E p a b → E q a b)
variable (erefl : ∀ p a, E p a a)
variable (esymm : ∀ {p a b}, E p a b → E p b a)
variable (etrans : ∀ {p a b c}, E p a b → E p b c → E p a c)

include wmono in
theorem selected_mono {a : A} {p q : P} (hqp : q ≤ p)
    (h : Selected W E a p) : Selected W E a q :=
  ⟨wmono hqp h.1,fun r hr => h.2 r (hr.trans hqp)⟩

include esymm in
/-- Two persistent least codes agreeing at a condition are literally equal,
not merely equivalent. -/
theorem selected_unique {a b : A} {p : P}
    (ha : Selected W E a p) (hb : Selected W E b p) (hab : E p a b) : a = b := by
  rcases (trichotomous_of WellOrderingRel a b) with h | h | h
  · exact False.elim (hb.2 p le_rfl a h ⟨ha.1,esymm hab⟩)
  · exact h
  · exact False.elim (ha.2 p le_rfl b h ⟨hb.1,hab⟩)

include wmono emono erefl etrans in
/-- Every working code densely admits a selected representative. The
minimum is taken over the set of codes which can agree *somewhere below*
the starting condition; minimality therefore survives every refinement. -/
theorem dense_selected (p : P) (a : A) (ha : W p a) :
    ∃ q, q ≤ p ∧ ∃ b, Selected W E b q ∧ E q a b := by
  let B : Set A := {b | ∃ q, q ≤ p ∧ W q b ∧ E q a b}
  have hB : B.Nonempty := ⟨a,p,le_rfl,wmono le_rfl ha,erefl p a⟩
  let b := WellOrderingRel.isWellOrder.wf.min B hB
  obtain ⟨q,hqp,hb,hab⟩ := WellOrderingRel.isWellOrder.wf.min_mem B hB
  refine ⟨q,hqp,b,⟨hb,?_⟩,hab⟩
  intro r hrq c hcb hc
  apply WellOrderingRel.isWellOrder.wf.not_lt_min B
    (show c ∈ B from ⟨r,hrq.trans hqp,hc.1,etrans (emono hrq hab) hc.2⟩)
  exact hcb

end
end PartitionConsistency.ConditionCodeSelection


/-! ## PrincipalCode -/

/-! The least-code construction without an ambient fully generic filter.
The names and glued quotient values are the actual ones from the local
symbolic system. The principal filter at a condition is used only as a
convenient quotient notation for equality forced by that condition. -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

variable {hμ c hcard hsize hmerger hj E hE C}

theorem works_mono {d e : CohenForcing.Condition I κ} {a : ChainCode hμ c C}
    (hed : e ≤ d) (ha : Works hμ c hcard hsize hmerger hj E hE C d a) :
    Works hμ c hcard hsize hmerger hj E hE C e a :=
  fun f hfe => ha f (hfe.trans hed)

omit [Infinite M] [Infinite I] in
theorem same_refl (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C) :
    Same hμ c C d a a := ⟨0,fun i _ => (localAtomic hμ (C.vertex i).diagram).eq_refl d _⟩

omit [Infinite M] [Infinite I] in
theorem same_symm {d : CohenForcing.Condition I κ} {a b : ChainCode hμ c C}
    (h : Same hμ c C d a b) : Same hμ c C d b a := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => (localAtomic hμ (C.vertex i).diagram).eq_symm (hN i hi)⟩

omit [Infinite M] [Infinite I] in
theorem same_trans {d : CohenForcing.Condition I κ} {a b f : ChainCode hμ c C}
    (h : Same hμ c C d a b) (h' : Same hμ c C d b f) : Same hμ c C d a f := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := h'
  exact ⟨max N L,fun i hi => (localAtomic hμ (C.vertex i).diagram).eq_trans
    (hN i ((le_max_left _ _).trans hi)) (hL i ((le_max_right _ _).trans hi))⟩

omit [Infinite M] [Infinite I] in
theorem same_mono {d e : CohenForcing.Condition I κ} {a b : ChainCode hμ c C}
    (hed : e ≤ d) (h : Same hμ c C d a b) : Same hμ c C e a b := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => (localAtomic hμ (C.vertex i).diagram).eq_mono hed (hN i hi)⟩

variable (hμ c hcard hsize hmerger hj E hE C)

theorem selected_mono {a : ChainCode hμ c C} {d e : CohenForcing.Condition I κ}
    (hed : e ≤ d) (ha : Selected hμ c hcard hsize hmerger hj E hE C a d) :
    Selected hμ c hcard hsize hmerger hj E hE C a e :=
  ConditionCodeSelection.selected_mono
    (Works hμ c hcard hsize hmerger hj E hE C) (Same hμ c C)
    (fun h ha => works_mono h ha) hed ha

theorem selected_unique {a b : ChainCode hμ c C} {d : CohenForcing.Condition I κ}
    (ha : Selected hμ c hcard hsize hmerger hj E hE C a d)
    (hb : Selected hμ c hcard hsize hmerger hj E hE C b d)
    (hab : Same hμ c C d a b) : a = b :=
  ConditionCodeSelection.selected_unique
    (Works hμ c hcard hsize hmerger hj E hE C) (Same hμ c C)
    (fun h => same_symm h) ha hb hab

theorem dense_selected (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a) :
    ∃ e, e ≤ d ∧ ∃ b, Selected hμ c hcard hsize hmerger hj E hE C b e ∧ Same hμ c C e a b :=
  ConditionCodeSelection.dense_selected
    (Works hμ c hcard hsize hmerger hj E hE C) (Same hμ c C)
    (fun h hw => works_mono h hw)
    (fun h he => same_mono h he) same_refl (fun h h' => same_trans h h') d a ha

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## PersistentCode -/

/-! Stable availability gives actual working ground codes, persistently at
every refinement. This supplies the density input for least-code ranks,
without a countable family of external fully generic filters. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- Eligibility adds no restriction to the availability witnesses below a
supporting root: a representative of an eligible class is itself eligible,
by local decision. -/
theorem eligibleSystem_availability_eq (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (a : M) (ha : r.sub a = q) (x : (D[F]).Obj r) :
    (D[F]).availability r a x =
      (allLocalSystem (c := c) hμ hcard hsize hmerger F).availability r a x.val := by
  apply ConeIdeal.ext
  ext n
  change (n ≤ (show LeftDivOrder M from a) ∧ ∃ y : (D[F]).Obj (r.sub n),
      (D[F]).restrict (r.self_le_sub n) y = x) ↔
    n ≤ (show LeftDivOrder M from a) ∧ ∃ y : LocalQuotient (c := c) hμ F (r.sub n),
      LocalQuotient.restrict F (r.self_le_sub n) y = x.val
  apply and_congr_right
  intro hn
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y.val,congrArg Subtype.val hy⟩
  · rintro ⟨y,hy⟩
    have hrq : r.sub n ≤ q := ha ▸ r.sub_mono hn
    have hey : Eligible hμ c F (r.sub n) E y :=
      (eligible_restrict_iff hμ c hsize hmerger F E (r.self_le_sub n)
        (supported_mono hμ hrq E hE) y).mp (hy.symm ▸ x.property.2)
    exact ⟨⟨y,hrq,hey⟩,Subtype.ext hy⟩

/-- For any chosen name, the actual exact-fiber predicate in a principal
quotient agrees with eligibility and its computed forced availability. -/
theorem exists_fiber_principal (d : CohenForcing.Condition I κ) (v : Vertex q)
    (τ : LocalName hμ c v.diagram)
    (hel : (system hμ).Forces ![τ.name,labelSet hμ c,E]
      ((d,v.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2))
    (hU : forcedAvailability hμ c hcard hsize hmerger d v.diagram v.index τ = v.ideal) :
    ∃ x : (D[principalFilter d]).vertexFiber v,
      LocalQuotient.ofName (principalFilter d) τ = x.val.val := by
  let x : (D[principalFilter d]).Obj v.diagram :=
    ⟨LocalQuotient.ofName (principalFilter d) τ,⟨v.index,v.root⟩,d,(mem_principalFilter d d).mpr le_rfl,hel⟩
  refine ⟨⟨x,?_⟩,rfl⟩
  rw [eligibleSystem_availability_eq hμ c hcard hsize hmerger E hE
    (principalFilter d) v.diagram v.index v.root x]
  exact hU

namespace ChainCode
variable (hj : HasConditionalJoins (LeftDivOrder M)) {v : Vertex q} (C : Vertex.Chain v)

/-- An explicit eligible name with permanently constant ideal at the root
has a code which works at EVERY refinement of the condition. At each chain
vertex the code's entry remains the exact same ground normalized name. -/
theorem exists_working_code_of_stable (d : CohenForcing.Condition I κ)
    (τ : LocalName hμ c v.diagram)
    (hel : (system hμ).Forces ![τ.name,labelSet hμ c,E]
      ((d,v.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2))
    (hstable : ∀ e, e ≤ d →
      forcedAvailability hμ c hcard hsize hmerger e v.diagram v.index τ = v.ideal) :
    ∃ a : ChainCode hμ c C,
      Works hμ c hcard hsize hmerger hj E hE C d a ∧
      ∀ i, (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) (a i).name τ.name := by
  have hex (e : CohenForcing.Condition I κ) (hed : e ≤ d) :
      ∃ x : (D[principalFilter e]).vertexFiber v,
        LocalQuotient.ofName (principalFilter e) τ = x.val.val := by
    exact exists_fiber_principal hμ c hcard hsize hmerger E hE e v τ
      ((system hμ).atomic.forceFormula_mono
        (WithTop.coe_le_coe.mpr (show (e,v.diagram) ≤ (d,v.diagram) from ⟨hed,le_rfl⟩)) hel)
      (hstable e hed)
  obtain ⟨x,hx⟩ := hex d le_rfl
  have harr (i : ℕ) : Nonempty (v.Arrow (C.vertex i)) := by
    simpa only [C.first] using C.increasing 0 i (Nat.zero_le i)
  let f (i : ℕ) : v.Arrow (C.vertex i) := (harr i).some
  let hdiag (i : ℕ) : v.diagram ≤ (C.vertex i).diagram := ⟨(f i).index,(f i).diagram⟩
  have hcodes (i : ℕ) : ∃ σ : LocalName hμ c (C.vertex i).diagram,
      (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) σ.name τ.name := by
    obtain ⟨y,hy⟩ := (D[principalFilter d]).arrowMap_bijective hj (f i) |>.2 x
    obtain ⟨σ,hσ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ
      (principalFilter d) (C.vertex i).diagram) y.val.val
    refine ⟨σ,?_⟩
    apply ((localAtomic hμ v.diagram).eqG_principal d σ.name τ.name).mp
    apply (LocalQuotient.ofName_eq (principalFilter d) (σ.restrict (hdiag i)) τ).mp
    calc
      LocalQuotient.ofName (principalFilter d) (σ.restrict (hdiag i)) =
          LocalQuotient.restrict (principalFilter d) (hdiag i) y.val.val := congrArg (LocalQuotient.restrict (principalFilter d) (hdiag i)) hσ
      _ = x.val.val := congrArg (fun z : (D[principalFilter d]).vertexFiber v => z.val.val) hy
      _ = LocalQuotient.ofName (principalFilter d) τ := hx.symm
  choose a ha using hcodes
  refine ⟨a,?_,ha⟩
  intro e hed
  obtain ⟨x',hx'⟩ := hex e hed
  refine ⟨(D[principalFilter e]).toGlued hj v v (Vertex.Common.refl v) x',0,fun i _ => ?_⟩
  obtain ⟨y,hy⟩ := (D[principalFilter e]).arrowMap_bijective hj (f i) |>.2 x'
  have heq : LocalQuotient.ofName (principalFilter e) (a i) = y.val.val := by
    apply LocalQuotient.restrict_injective (principalFilter e) hsize hmerger (hdiag i)
    have ht : LocalQuotient.ofName (principalFilter e) ((a i).restrict (hdiag i)) =
        LocalQuotient.ofName (principalFilter e) τ := by
      apply (LocalQuotient.ofName_eq (principalFilter e) _ _).mpr
      apply ((localAtomic hμ v.diagram).eqG_principal e _ _).mpr
      exact (system hμ).atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (e,v.diagram) ≤ (d,v.diagram) from ⟨hed,le_rfl⟩)) (ha i)
    exact ht.trans (hx'.trans
      (congrArg (fun z : (D[principalFilter e]).vertexFiber v => z.val.val) hy).symm)
  refine ⟨C.common i,y,a i,rfl,heq,?_⟩
  rw [← (D[principalFilter e]).toGlued_arrow hj v v (C.vertex i)
    (Vertex.Common.refl v) (C.common i) (f i) y,hy]

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## OrdinalName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem transF_mono {p q : P} {σ : S.Name} (h : q ≤ p) (ht : S.TransF p σ) :
    S.TransF q σ := fun τ ν r hr => ht τ ν r (hr.trans h)

theorem transF_congr {p : P} {σ τ : S.Name} (he : S.atomic.EqF p σ τ) :
    S.TransF p σ ↔ S.TransF p τ := by
  have forward {σ τ : S.Name} (he : S.atomic.EqF p σ τ) (h : S.TransF p σ) :
      S.TransF p τ := by
    intro ν χ q hqp hν hχ
    have hem := S.atomic.eq_mono hqp he
    exact (S.atomic.mem_congr (S.atomic.eq_refl q χ) hem).mp
      (h ν χ q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν) hem).mpr hν) hχ)
  exact ⟨forward he,forward (S.atomic.eq_symm he)⟩

theorem ordF_mono {p q : P} {σ : S.Name} (h : q ≤ p) (ho : S.OrdF p σ) :
    S.OrdF q σ := ⟨S.transF_mono h ho.1,fun τ r hr => ho.2 τ r (hr.trans h)⟩

theorem ordF_mem {p : P} {σ τ : S.Name} (ho : S.OrdF p σ)
    (hm : S.atomic.MemF p τ σ) : S.OrdF p τ := by
  refine ⟨ho.2 τ p le_rfl hm,?_⟩
  intro ν q hqp hν
  exact ho.2 ν q hqp (ho.1 τ ν q hqp (S.atomic.mem_mono hqp hm) hν)

theorem forces_transitiveSet {n} (v : Fin n → S.Name) (p : P) (x : Fin n) :
    S.Forces v p (SetLanguage.transitiveSet x) ↔ S.TransF p (v x) := by
  simp only [Forces,SetLanguage.transitiveSet,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_mem]
  constructor
  · intro h τ ν q hqp hτ hν
    exact h τ ν q hqp hτ q le_rfl hν
  · intro h τ ν q hqp hτ r hrq hν
    exact h τ ν r (hrq.trans hqp) (S.atomic.mem_mono hrq hτ) hν

/-- The literal ordinal sentence implies the semantic hereditary transitivity
used in the rank induction. Internal well-foundedness is not confused with
external well-foundedness of a model. -/
theorem ordF_of_forces_ordinal {n} (v : Fin n → S.Name) (p : P) (x : Fin n)
    (ho : S.Forces v p (SetLanguage.ordinal x)) : S.OrdF p (v x) := by
  have ht : S.Forces v p (SetLanguage.transitiveSet x) := ho.1
  have hl : S.Forces v p (SetLanguage.membershipLinear x) := ho.2.1
  have ht' := (S.forces_transitiveSet v p x).mp ht
  refine ⟨ht',?_⟩
  intro τ q hqp hτ ν χ r hrq hν hχ
  simp only [Forces,SetLanguage.membershipLinear,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem] at hl
  have hτ' := S.atomic.mem_mono hrq hτ
  have hν' := ht' τ ν r (hrq.trans hqp) hτ' hν
  have hχ' := ht' ν χ r (hrq.trans hqp) hν' hχ
  exact hl.2.1 χ ν τ r (hrq.trans hqp) hχ' r le_rfl hν' r le_rfl hτ' r le_rfl ⟨hχ,hν⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Ordinal preservation for unrestricted HS names. A condition forcing a
transitive set of transitive sets has an extension deciding it to be a ground
ordinal. The quantitative bound is proved by induction on literal name rank. -/
theorem ordF_eq_check_le (σ : S.Name) (p : P) (ho : S.OrdF p σ) :
    ∃ q, q ≤ p ∧ ∃ β : Ordinal.{u}, β ≤ σ.raw.rank ∧
      S.atomic.EqF q σ (Name.check β.toZFSet) := by
  classical
  induction σ using (InvImage.wf (fun σ : S.Name => σ.raw) child_wf).induction generalizing p with
  | h σ ih =>
    have hbounded : ∀ (ν : S.Name) (q : P), q ≤ p → S.atomic.MemF q ν σ →
        S.atomic.MemF q ν (Name.check σ.raw.rank.toZFSet) := by
      intro ν q hqp hm
      apply (S.mem_check _ ν q).mpr
      intro r hrq
      obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := (S.mem_iff.mp hm) r hrq
      have hτσ : S.atomic.MemF s τ σ := S.mem_of_edge he hsc
      obtain ⟨t,hts,β,hβ,hτ⟩ := ih τ ⟨S.code c,he⟩ s
        (S.ordF_mem (S.ordF_mono (hsr.trans (hrq.trans hqp)) ho) hτσ)
      exact ⟨t,hts.trans hsr,β.toZFSet,
        Ordinal.toZFSet_mem_toZFSet_iff.mpr
          (hβ.trans_lt (Child.rank_lt ⟨S.code c,he⟩)),
        S.atomic.eq_trans (S.atomic.eq_mono hts heq) hτ⟩
    have hmiss : ¬ S.atomic.MemF p (Name.check σ.raw.rank.toZFSet) σ := by
      intro hm
      exact ZFSet.mem_irrefl _ ((S.mem_check_check _ _ p).mp
        (hbounded _ p le_rfl hm))
    obtain ⟨α,hα,hmin⟩ := Ordinal.lt_wf.has_min
      {α : Ordinal.{u} | ¬ S.atomic.MemF p (Name.check α.toZFSet) σ} ⟨σ.raw.rank,hmiss⟩
    have hαle : α ≤ σ.raw.rank := le_of_not_gt (hmin _ hmiss)
    have hbelow : ∀ β < α, S.atomic.MemF p (Name.check β.toZFSet) σ := by
      intro β hβ
      by_contra hn
      exact hmin β hn hβ
    have hneg : ∃ q, q ≤ p ∧ ∀ r, r ≤ q →
        ¬ S.atomic.MemF r (Name.check α.toZFSet) σ := by
      by_contra hn
      push Not at hn
      exact hα (S.atomic_regular.2 p (Name.check α.toZFSet) σ hn)
    obtain ⟨q,hqp,hneg⟩ := hneg
    refine ⟨q,hqp,α,hαle,S.eq_of_same_members ?_⟩
    intro ν r hrq
    constructor
    · intro hm
      apply (S.mem_check _ ν r).mpr
      intro s hsr
      obtain ⟨t,hts,y,hy,hey⟩ := (S.mem_check _ ν r).mp
        (hbounded ν r (hrq.trans hqp) hm) s hsr
      obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      have hβσ : S.atomic.MemF t (Name.check β.toZFSet) σ :=
        (S.atomic.mem_congr hey (S.atomic.eq_refl t σ)).mp
          (S.atomic.mem_mono (hts.trans hsr) hm)
      have hβα : β < α := by
        by_contra hn
        rcases (not_lt.mp hn).eq_or_lt with h | h
        · exact hneg t (hts.trans (hsr.trans hrq)) (h.symm ▸ hβσ)
        · exact hneg t (hts.trans (hsr.trans hrq))
            (ho.1 (Name.check β.toZFSet) (Name.check α.toZFSet) t
              (hts.trans (hsr.trans (hrq.trans hqp))) hβσ
              (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr h) t))
      exact ⟨t,hts,β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hβα,hey⟩
    · intro hm
      apply S.atomic_regular.2
      intro s hsr
      obtain ⟨t,hts,y,hy,hey⟩ := (S.mem_check _ ν r).mp hm s hsr
      obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
      exact ⟨t,hts,(S.atomic.mem_congr hey (S.atomic.eq_refl t σ)).mpr
        (S.atomic.mem_mono (hts.trans (hsr.trans (hrq.trans hqp))) (hbelow β hβ))⟩

/-- Dense decision of any name satisfying the actual ordinal formula. This
applies at arbitrary rank, not merely to normalized subset names. -/
theorem forces_ordinal_decide {n} (v : Fin n → S.Name) (p : P) (x : Fin n)
    (ho : S.Forces v p (SetLanguage.ordinal x)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ β : Ordinal.{u},
      S.atomic.EqF r (v x) (Name.check β.toZFSet) := by
  intro q hqp
  obtain ⟨r,hrq,β,_,he⟩ := S.ordF_eq_check_le (v x) q
    (S.ordF_mono hqp (S.ordF_of_forces_ordinal v p x ho))
  exact ⟨r,hrq,β,he⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalCodes
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instIsWellOrderIndexLt _root_.OAI.PartitionConsistency.ProductForcing.ChainCode.instLinearOrderIndex _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OrdinalSelection -/

/-! A wellordered subset selected by forcing conditions has an actual
ordinal name for its order type and names for the ranks of its elements.
This construction uses ordinary set names, not evaluated ambient generics.
The pointwise invariance of each selection predicate gives literal fixation
of every rank name. -/
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hR : ∀ g ∈ H, ∀ x p, R x p → R x (S.move g p))

namespace FixedName
variable {S H}

omit [OrderTop P] in
theorem mem_collect {A : Type u} (f : A → S.FixedName H) (Q : A → P → Prop)
    (hQ : ∀ g ∈ H, ∀ a p, Q a p → Q a (S.move g p)) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (collect hH f Q hQ).val ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a c, Q a c ∧ r ≤ c ∧
        S.atomic.EqF r ν (f a).val :=
  S.mem_collect (fun a => (f a).val) Q H hH
    (fun g hg a p ha => ⟨a,((f a).property g hg).symm,hQ g hg a p ha⟩) ν p

end FixedName

omit [OrderTop P] in
theorem selectedRank_fixed (a : X) (g : Γ) (hg : g ∈ H) :
    g • S.selectedRank R H hH hR a = S.selectedRank R H hH hR a :=
  (S.selectedRankFixed R H hH hR a).property g hg

omit [OrderTop P] in
theorem selectionType_fixed (g : Γ) (hg : g ∈ H) :
    g • S.selectionType R H hH hR = S.selectionType R H hH hR :=
  (FixedName.collect hH (fun a => S.selectedRankFixed R H hH hR a) R hR).property g hg

omit [OrderTop P] in
theorem selectedRankFixed_eq (a : X) : S.selectedRankFixed R H hH hR a =
    FixedName.collect hH (fun b : {b : X // b < a} => S.selectedRankFixed R H hH hR b.val)
      (fun b p => R b.val p) (fun g hg b p => hR g hg b.val p) := by
  unfold selectedRankFixed
  rw [WellFounded.fix_eq]

omit [OrderTop P] in
/-- Membership is densely witnessed by a selected smaller ground code. -/
theorem mem_selectedRank (a : X) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.selectedRank R H hH hR a) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ b, b < a ∧ ∃ c,
        R b c ∧ r ≤ c ∧ S.atomic.EqF r ν (S.selectedRank R H hH hR b) := by
  change S.atomic.MemF p ν (S.selectedRankFixed R H hH hR a).val ↔ _
  rw [S.selectedRankFixed_eq,FixedName.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,b,c,hb,hrc,he⟩ := h q hqp
    exact ⟨r,hrq,b.val,b.property,c,hb,hrc,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,b,hba,c,hb,hrc,he⟩ := h q hqp
    exact ⟨r,hrq,⟨b,hba⟩,c,hb,hrc,he⟩

omit [OrderTop P] in
theorem mem_selectionType (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.selectionType R H hH hR) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a c,
        R a c ∧ r ≤ c ∧ S.atomic.EqF r ν (S.selectedRank R H hH hR a) :=
  FixedName.mem_collect hH _ _ _ _ _

omit [OrderTop P] in
/-- Ranks of selected elements belong to the selected order type. -/
theorem selectedRank_mem_selectionType (a : X) (p : P) (ha : R a p) :
    S.atomic.MemF p (S.selectedRank R H hH hR a) (S.selectionType R H hH hR) := by
  apply (S.mem_selectionType R H hH hR _ p).mpr
  exact fun q hqp => ⟨q,le_rfl,a,p,ha,hqp,S.atomic.eq_refl q _⟩

omit [OrderTop P] in
theorem selectedRank_mem_selectedRank {a b : X} (hab : a < b) (p : P) (ha : R a p) :
    S.atomic.MemF p (S.selectedRank R H hH hR a) (S.selectedRank R H hH hR b) := by
  apply (S.mem_selectedRank R H hH hR b _ p).mpr
  exact fun q hqp => ⟨q,le_rfl,a,hab,p,ha,hqp,S.atomic.eq_refl q _⟩

omit [OrderTop P] in
/-- Taking a longer initial segment can only add members. -/
theorem selectedRank_subset {a b : X} (hab : a ≤ b) (p : P) :
    S.SubsetF p (S.selectedRank R H hH hR a) (S.selectedRank R H hH hR b) := by
  intro ν q _ hm
  apply (S.mem_selectedRank R H hH hR b ν q).mpr
  intro r hrq
  obtain ⟨s,hsr,c,hca,d,hc,hsd,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hm r hrq
  exact ⟨s,hsr,c,hca.trans_le hab,d,hc,hsd,he⟩

omit [OrderTop P] in
theorem selectedRank_subset_selectionType (a : X) (p : P) :
    S.SubsetF p (S.selectedRank R H hH hR a) (S.selectionType R H hH hR) := by
  intro ν q _ hm
  apply (S.mem_selectionType R H hH hR ν q).mpr
  intro r hrq
  obtain ⟨s,hsr,b,_,d,hb,hsd,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hm r hrq
  exact ⟨s,hsr,b,d,hb,hsd,he⟩

omit [OrderTop P] in
/-- The recursively defined ranks really are transitive sets. -/
theorem transF_selectedRank (a : X) (p : P) :
    S.TransF p (S.selectedRank R H hH hR a) := by
  intro ν χ q _ hν hχ
  apply S.atomic_regular.2
  intro r hrq
  obtain ⟨s,hsr,b,hba,d,_,_,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hν r hrq
  have hm := (S.atomic.mem_congr (S.atomic.eq_refl s χ) he).mp
    (S.atomic.mem_mono (hsr.trans hrq) hχ)
  exact ⟨s,hsr,S.selectedRank_subset R H hH hR hba.le s χ s le_rfl hm⟩

omit [OrderTop P] in
theorem transF_selectionType (p : P) : S.TransF p (S.selectionType R H hH hR) := by
  intro ν χ q _ hν hχ
  apply S.atomic_regular.2
  intro r hrq
  obtain ⟨s,hsr,b,d,_,_,he⟩ := (S.mem_selectionType R H hH hR ν q).mp hν r hrq
  have hm := (S.atomic.mem_congr (S.atomic.eq_refl s χ) he).mp
    (S.atomic.mem_mono (hsr.trans hrq) hχ)
  exact ⟨s,hsr,S.selectedRank_subset_selectionType R H hH hR b s χ s le_rfl hm⟩

omit [OrderTop P] in
/-- A member of any selected rank is itself transitive. -/
theorem ordF_selectedRank (a : X) (p : P) :
    S.OrdF p (S.selectedRank R H hH hR a) := by
  refine ⟨S.transF_selectedRank R H hH hR a p,?_⟩
  intro ν q _ hν χ ψ r hrq hχ hψ
  apply S.atomic_regular.2
  intro s hsr
  obtain ⟨t,hts,b,_,d,_,_,he⟩ := (S.mem_selectedRank R H hH hR a ν q).mp hν s (hsr.trans hrq)
  have ht := (S.transF_congr he).mpr (S.transF_selectedRank R H hH hR b t)
  exact ⟨t,hts,ht χ ψ t le_rfl (S.atomic.mem_mono (hts.trans hsr) hχ)
    (S.atomic.mem_mono (hts.trans hsr) hψ)⟩

omit [OrderTop P] in
theorem ordF_selectionType (p : P) : S.OrdF p (S.selectionType R H hH hR) := by
  refine ⟨S.transF_selectionType R H hH hR p,?_⟩
  intro ν q _ hν χ ψ r hrq hχ hψ
  apply S.atomic_regular.2
  intro s hsr
  obtain ⟨t,hts,b,d,_,_,he⟩ := (S.mem_selectionType R H hH hR ν q).mp hν s (hsr.trans hrq)
  have ht := (S.transF_congr he).mpr (S.transF_selectedRank R H hH hR b t)
  exact ⟨t,hts,ht χ ψ t le_rfl (S.atomic.mem_mono (hts.trans hsr) hχ)
    (S.atomic.mem_mono (hts.trans hsr) hψ)⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SelectedRank -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hR : ∀ g ∈ H, ∀ x p, R x p → R x (S.move g p))

/-- No ordinal name can be forced to belong to itself. Ordinal decision
reduces this to irreflexivity in the genuine von Neumann ordinals. -/
theorem ordF_not_mem_self (σ : S.Name) (p : P) (ho : S.OrdF p σ) :
    ¬ S.atomic.MemF p σ σ := by
  intro hm
  obtain ⟨q,hqp,β,_,he⟩ := S.ordF_eq_check_le σ p ho
  have hh := (S.atomic.mem_congr he he).mp (S.atomic.mem_mono hqp hm)
  exact ZFSet.mem_irrefl _ ((S.mem_check_check _ _ q).mp hh)

/-- Distinct selected codes have distinct ordinal ranks, at every condition
where both are selected. This is an internal forcing assertion about the
actual ordinal names, not an assertion about an evaluated proxy order. -/
theorem selectedRank_eq_iff (a b : X) (p : P) (ha : R a p) (hb : R b p) :
    S.atomic.EqF p (S.selectedRank R H hH hR a) (S.selectedRank R H hH hR b) ↔ a = b := by
  constructor
  · intro he
    rcases lt_trichotomy a b with hab | hab | hab
    · have hm := S.selectedRank_mem_selectedRank R H hH hR hab p ha
      exact False.elim (S.ordF_not_mem_self _ p (S.ordF_selectedRank R H hH hR a p)
        ((S.atomic.mem_congr (S.atomic.eq_refl p _) (S.atomic.eq_symm he)).mp hm))
    · exact hab
    · have hm := S.selectedRank_mem_selectedRank R H hH hR hab p hb
      exact False.elim (S.ordF_not_mem_self _ p (S.ordF_selectedRank R H hH hR b p)
        ((S.atomic.mem_congr (S.atomic.eq_refl p _) he).mp hm))
  · rintro rfl
    exact S.atomic.eq_refl p _

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CohenSelection -/

/-! The ordinal coding of a condition-defined wellorder can be carried out
inside the product symmetric system itself. Its rank names have the given
tail support. Reflection to a supporting diagram permits all ordinal
decisions to be made by strengthening just the Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable [Infinite M] [Infinite I]
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
include hsize hmerger

/-- Reflection to the root, retaining the full Cohen condition. -/
theorem forces_at_root {n} (φ : Formula n)
    (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (r t : Diagram M I) (htr : t ≤ r)
    (hsup : ∀ π ∈ SupportFilter.Fix r.range, ∀ i, π • v i = v i)
    (d : CohenForcing.Condition I κ)
    (h : (system (M := M) (I := I) (κ := κ) hμ).Forces v ((d,t) : Poset M I κ) φ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces v ((d,r) : Poset M I κ) φ :=
  (system (M := M) (I := I) (κ := κ) hμ).atomic.forceFormula_mono
    (WithTop.coe_le_coe.mpr (show (d,r) ≤ (d.restrict r.range,r) from ⟨d.le_restrict _,le_rfl⟩))
    (forces_at_supporting_root hμ hsize hmerger φ v r t htr hsup d h)

theorem eq_at_root (τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (r t : Diagram M I) (htr : t ≤ r)
    (hτ : ∀ π ∈ SupportFilter.Fix r.range, π • τ = τ)
    (hσ : ∀ π ∈ SupportFilter.Fix r.range, π • σ = σ)
    (d : CohenForcing.Condition I κ)
    (h : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,t) : Poset M I κ) τ σ) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ) τ σ := by
  have hh := forces_at_root hμ hsize hmerger (.equal 0 1) ![τ,σ] r t htr
    (by intro π hπ i; fin_cases i; exact hτ π hπ; exact hσ π hπ) d (by
      simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
        Matrix.cons_val_one] using h)
  simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
    Matrix.cons_val_one] using hh

/-- Every supported ordinal name can be decided by the Cohen coordinate
alone while the supporting root stays fixed. -/
theorem ordinal_decide_at_root (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (r : Diagram M I) (hτ : ∀ π ∈ SupportFilter.Fix r.range, π • τ = τ)
    (d : CohenForcing.Condition I κ)
    (ho : (system (M := M) (I := I) (κ := κ) hμ).OrdF ((d,r) : Poset M I κ) τ) :
    ∃ e, e ≤ d ∧ ∃ β : Ordinal.{u}, β ≤ τ.raw.rank ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) τ (Name.check β.toZFSet) := by
  let : Nonempty (Diagram M I) := ⟨r⟩
  obtain ⟨s,hs,β,hβ,he⟩ := (system (M := M) (I := I) (κ := κ) hμ).ordF_eq_check_le τ ((d,r) : Poset M I κ) ho
  obtain ⟨t,ht⟩ := exists_condition_below s
  have htd : t ≤ (d,r) := WithTop.coe_le_coe.mp (ht.trans hs)
  exact ⟨t.1,htd.1,β,hβ,eq_at_root hμ hsize hmerger τ (Name.check β.toZFSet) r t.2 htd.2
    hτ (fun π _ => Name.smul_check (system (M := M) (I := I) (κ := κ) hμ) π _) t.1 ((system (M := M) (I := I) (κ := κ) hμ).atomic.eq_mono ht he)⟩

omit hsize hmerger

namespace CohenSelection
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → CohenForcing.Condition I κ → Prop)
variable (H : Subgroup (Equiv.Perm I)) (hH : H ∈ (system (M := M) (I := I) (κ := κ) hμ).filter)
variable (hR : ∀ π ∈ H, ∀ a d, R a d → R a (d.permute π))

omit [Infinite M] [Infinite I] in
theorem rank_fixed (a : X) (π : Equiv.Perm I) (hπ : π ∈ H) :
    π • rank hμ R H hH hR a = rank hμ R H hH hR a :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank_fixed _ _ _ _ a π hπ

omit [Infinite M] [Infinite I] in
theorem orderType_fixed (π : Equiv.Perm I) (hπ : π ∈ H) :
    π • orderType hμ R H hH hR = orderType hμ R H hH hR :=
  (system (M := M) (I := I) (κ := κ) hμ).selectionType_fixed _ _ _ _ π hπ

variable (r : Diagram M I) (hroot : SupportFilter.Fix r.range ≤ H)

include hsize hmerger hroot in
theorem orderType_decide (d : CohenForcing.Condition I κ) :
    ∃ e, e ≤ d ∧ ∃ θ : Ordinal.{u}, θ ≤ (orderType hμ R H hH hR).raw.rank ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) (orderType hμ R H hH hR) (Name.check θ.toZFSet) :=
  ordinal_decide_at_root hμ hsize hmerger _ r
    (fun π hπ => orderType_fixed hμ R H hH hR π (hroot hπ)) d
    ((system (M := M) (I := I) (κ := κ) hμ).ordF_selectionType _ _ _ _ _)

omit [Infinite M] [Infinite I] in
theorem rank_eq_iff (a b : X) (d : CohenForcing.Condition I κ) (ha : R a d) (hb : R b d) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ)
      (rank hμ R H hH hR a) (rank hμ R H hH hR b) ↔ a = b :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank_eq_iff _ _ _ _ a b _
    ((lift_coe R a d r).mpr ha) ((lift_coe R b d r).mpr hb)

omit [Infinite M] [Infinite I] in
theorem rank_mem (a : X) (d : CohenForcing.Condition I κ) (ha : R a d) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF ((d,r) : Poset M I κ)
      (rank hμ R H hH hR a) (orderType hμ R H hH hR) :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank_mem_selectionType _ _ _ _ a _ ((lift_coe R a d r).mpr ha)

include hsize hmerger hroot in
/-- Ranks are decided without changing the chosen root diagram. -/
theorem rank_decide (a : X) (d : CohenForcing.Condition I κ) (ha : R a d) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ)
      (orderType hμ R H hH hR) (Name.check θ.toZFSet)) :
    ∃ e, e ≤ d ∧ ∃ β : Set.Iio θ,
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) (rank hμ R H hH hR a) (Name.check β.val.toZFSet) := by
  obtain ⟨e,hed,β,_,hb⟩ := ordinal_decide_at_root hμ hsize hmerger (rank hμ R H hH hR a) r
    (fun π hπ => rank_fixed hμ R H hH hR a π (hroot hπ)) d
    ((system (M := M) (I := I) (κ := κ) hμ).ordF_selectedRank _ _ _ _ a _)
  have hle : ((e,r) : Poset M I κ) ≤ ((d,r) : Poset M I κ) := WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩
  have hm := (system (M := M) (I := I) (κ := κ) hμ).atomic.mem_mono hle (rank_mem hμ R H hH hR r a d ha)
  have hm' := ((system (M := M) (I := I) (κ := κ) hμ).atomic.mem_congr hb ((system (M := M) (I := I) (κ := κ) hμ).atomic.eq_mono hle hθ)).mp hm
  exact ⟨e,hed,⟨β,Ordinal.toZFSet_mem_toZFSet_iff.mp
    (((system (M := M) (I := I) (κ := κ) hμ).mem_check_check _ _ ((e,r) : Poset M I κ)).mp hm')⟩,hb⟩

include hsize hmerger hroot in
/-- Every member of a decided order type is densely the rank of a selected
code. Extraction uses actual collection-name entries. -/
theorem member_rank (hmono : ∀ {a d e}, e ≤ d → R a d → R a e)
    (d : CohenForcing.Condition I κ) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,r) : Poset M I κ)
      (orderType hμ R H hH hR) (Name.check θ.toZFSet)) (β : Set.Iio θ) :
    ∃ e, e ≤ d ∧ ∃ a, R a e ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,r) : Poset M I κ) (rank hμ R H hH hR a) (Name.check β.val.toZFSet) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨r⟩
  have hm : S.atomic.MemF ((d,r) : Poset M I κ) (Name.check β.val.toZFSet)
      (orderType hμ R H hH hR) :=
    (S.atomic.mem_congr (S.atomic.eq_refl _ _) (S.atomic.eq_symm hθ)).mp
      (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr β.property) _)
  obtain ⟨s,hs,a,c,ha,hsc,hea⟩ :=
    (S.mem_selectionType _ _ _ _ _ ((d,r) : Poset M I κ)).mp hm ((d,r) : Poset M I κ) le_rfl
  obtain ⟨f,t,hc,ha⟩ := ha
  obtain ⟨u,hu⟩ := exists_condition_below s
  have hud : u ≤ (d,r) := WithTop.coe_le_coe.mp (hu.trans hs)
  have huf : u ≤ (f,t) := WithTop.coe_le_coe.mp (hc ▸ hu.trans hsc)
  refine ⟨u.1,hud.1,a,hmono huf.1 ha,?_⟩
  exact eq_at_root hμ hsize hmerger _ _ r u.2 hud.2
    (fun π hπ => rank_fixed hμ R H hH hR a π (hroot hπ))
    (fun π _ => Name.smul_check (system (M := M) (I := I) (κ := κ) hμ) π _) u.1
    (S.atomic.eq_symm (S.atomic.eq_mono hu hea))

end CohenSelection
end
end PartitionConsistency.ProductForcing


/-! ## CodeRoot -/

/-! Connecting the persistent ground codes to literal root-supported names.
The comparison of two codes is equivalent to forced equality of any of their
root representatives. No generic evaluator is presumed in this step. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

variable {hμ c C}

omit [Infinite M] [Infinite I] in
theorem rooted_mono {a : ChainCode hμ c C} {d e : CohenForcing.Condition I κ}
    {τ : LocalName hμ c v.diagram} (hed : e ≤ d) (h : Rooted hμ c C a d τ) :
    Rooted hμ c C a e τ := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => (system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (e,v.diagram) ≤ (d,v.diagram) from ⟨hed,le_rfl⟩)) (hN i hi)⟩

include hsize hmerger in
/-- All root representatives induce exactly the same code equivalence. -/
theorem rooted_eq_iff_same {a b : ChainCode hμ c C} {d : CohenForcing.Condition I κ}
    {τ σ : LocalName hμ c v.diagram} (ha : Rooted hμ c C a d τ) (hb : Rooted hμ c C b d σ) :
    (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) τ.name σ.name ↔ Same hμ c C d a b := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hb
  have hr (i : ℕ) : v.diagram ≤ (C.vertex i).diagram := by
    obtain ⟨f⟩ := C.increasing 0 i (Nat.zero_le i)
    have h : (C.vertex 0).diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
    simpa only [C.first] using h
  have he (i : ℕ) (hn : N ≤ i) (hl : L ≤ i) :
      (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) τ.name σ.name ↔
        (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name := by
    constructor
    · intro h
      exact eq_at_root hμ hsize hmerger _ _ (C.vertex i).diagram v.diagram (hr i)
        (a i).fixed (b i).fixed d
        ((system hμ).atomic.eq_trans (hN i hn) ((system hμ).atomic.eq_trans h
          ((system hμ).atomic.eq_symm (hL i hl))))
    · intro h
      have h' := (system hμ).atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (d,v.diagram) ≤ (d,(C.vertex i).diagram) from ⟨le_rfl,hr i⟩)) h
      exact (system hμ).atomic.eq_trans ((system hμ).atomic.eq_symm (hN i hn))
        ((system hμ).atomic.eq_trans h' (hL i hl))
  constructor
  · intro h
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)
      ((le_max_right _ _).trans hi)).mp h⟩
  · rintro ⟨K,hK⟩
    exact (he (max (max N L) K) ((le_max_left N L).trans (le_max_left _ _))
      ((le_max_right N L).trans (le_max_left _ _))).mpr (hK _ (le_max_right _ _))

variable (hμ c C)

/-- Every persistent code has an eligible normalized name at its root.
The proof uses the genuine bijective local restriction maps. -/
theorem working_rooted (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a) :
    ∃ τ : LocalName hμ c v.diagram,
      (system hμ).Forces ![τ.name,labelSet hμ c,E]
        ((d,v.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2) ∧
      Rooted hμ c C a d τ := by
  obtain ⟨b,N,hN⟩ := ha d le_rfl
  obtain ⟨x,hx⟩ := (D[principalFilter d]).toGlued_surjective hj v v (Vertex.Common.refl v) b
  obtain ⟨τ,hτ⟩ := Quotient.mk'_surjective (s := localSetoid (c := c) hμ
    (principalFilter d) v.diagram) x.val.val
  change LocalQuotient.ofName (principalFilter d) τ = x.val.val at hτ
  have hel : EligibleName hμ c (principalFilter d) v.diagram E τ := by
    apply (eligible_ofName hμ c (principalFilter d) v.diagram E τ).mp
    rw [hτ]
    exact x.val.property.2
  obtain ⟨e,he,hel⟩ := hel
  refine ⟨τ,(system hμ).atomic.forceFormula_mono
    (WithTop.coe_le_coe.mpr (show (d,v.diagram) ≤ (e,v.diagram) from
      ⟨(mem_principalFilter d e).mp he,le_rfl⟩)) hel,N,?_⟩
  intro i hi
  obtain ⟨hw,y,σ,hσ,hy,hb⟩ := hN i hi
  have hσ' : σ = a i := LocalName.ext hσ
  subst σ
  have harr : Nonempty (v.Arrow (C.vertex i)) := by
    simpa only [C.first] using C.increasing 0 i (Nat.zero_le i)
  let f := harr.some
  have hf : v.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  have hexy : (D[principalFilter d]).arrowMap hj f y = x := by
    apply (D[principalFilter d]).toGlued_injective hj v v (Vertex.Common.refl v)
    rw [(D[principalFilter d]).toGlued_arrow hj v v (C.vertex i)
      (Vertex.Common.refl v) hw f y,hb,hx]
  apply ((localAtomic hμ v.diagram).eqG_principal d _ _).mp
  apply (LocalQuotient.ofName_eq (principalFilter d) ((a i).restrict hf) τ).mp
  calc
    LocalQuotient.ofName (principalFilter d) ((a i).restrict hf) =
        LocalQuotient.restrict (principalFilter d) hf y.val.val :=
      congrArg (LocalQuotient.restrict (principalFilter d) hf) hy
    _ = x.val.val := congrArg (fun z : (D[principalFilter d]).vertexFiber v => z.val.val) hexy
    _ = LocalQuotient.ofName (principalFilter d) τ := hτ.symm

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## OrderAssignment -/

/-! Enumeration using one fixed, bounded table of bijections with ordinals.
This is the order-theoretic part of the preliminary component assignment.
The table is chosen once and never depends on the wellordered set being
enumerated. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_CodeLinks
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeOrdinal -/

/-! Actual ordinal names for the persistent least-code ordering on a single
component. All names have the initial diagram as a support. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

theorem isSelected_mono {a : Index hμ c C} {d e : CohenForcing.Condition I κ}
    (hed : e ≤ d) (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d) :
    IsSelected hμ c hcard hsize hmerger hj E hE C a e :=
  selected_mono hμ c hcard hsize hmerger hj E hE C hed ha

theorem ordinalType_decide (d : CohenForcing.Condition I κ) :
    ∃ e, e ≤ d ∧ ∃ θ : Ordinal.{u}, θ ≤ (ordinalType hμ c hcard hsize hmerger hj E hE C).raw.rank ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet) :=
  CohenSelection.orderType_decide hμ hsize hmerger _ _ _ _ v.diagram (root_le_tailGroup hj C) d

theorem ordinalRank_eq_iff (a b : Index hμ c C) (d : CohenForcing.Condition I κ)
    (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d)
    (hb : IsSelected hμ c hcard hsize hmerger hj E hE C b d) :
    (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalRank hμ c hcard hsize hmerger hj E hE C a)
      (ordinalRank hμ c hcard hsize hmerger hj E hE C b) ↔ a = b :=
  CohenSelection.rank_eq_iff hμ _ _ _ _ v.diagram a b d ha hb

theorem ordinalRank_decide (a : Index hμ c C) (d : CohenForcing.Condition I κ)
    (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet)) :
    ∃ e, e ≤ d ∧ ∃ β : Set.Iio θ,
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hj E hE C a) (Name.check β.val.toZFSet) :=
  CohenSelection.rank_decide hμ hsize hmerger _ _ _ _ v.diagram
    (root_le_tailGroup hj C) a d ha θ hθ

theorem member_ordinalRank (d : CohenForcing.Condition I κ) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet)) (β : Set.Iio θ) :
    ∃ e, e ≤ d ∧ ∃ a : Index hμ c C,
      IsSelected hμ c hcard hsize hmerger hj E hE C a e ∧
      (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hj E hE C a) (Name.check β.val.toZFSet) :=
  CohenSelection.member_rank hμ hsize hmerger
    (IsSelected hμ c hcard hsize hmerger hj E hE C)
    (tailGroup hj C) (tailGroup_supported hμ hcard hj C)
    (isSelected_covariance hμ c hcard hsize hmerger hj E hE C) v.diagram
    (root_le_tailGroup hj C) (fun h ha => isSelected_mono hμ c hcard hsize hmerger hj E hE C h ha)
    d θ hθ β

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## CodeLink -/

/-! Eventual code links at arbitrary vertices, rather than only at the
chosen first vertex. This is the local forcing form of the canonical
identifications in one component. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

variable {hμ c C}

omit [Infinite M] [Infinite I] in
theorem links_mono {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a : ChainCode hμ c C}
    (hed : e ≤ d) (h : Links hμ c C d w τ a) : Links hμ c C e w τ a := by
  obtain ⟨N,hN⟩ := h
  exact ⟨N,fun i hi => ⟨(hN i hi).1,(system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (e,w.diagram) ≤ (d,w.diagram) from ⟨hed,le_rfl⟩))
    (hN i hi).2⟩⟩

omit [Infinite M] [Infinite I] in
theorem links_same {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a b : ChainCode hμ c C}
    (h : Links hμ c C d w τ a) (hs : Same hμ c C d a b) : Links hμ c C d w τ b := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := hs
  refine ⟨max N L,fun i hi => ?_⟩
  obtain ⟨hf,he⟩ := hN i ((le_max_left _ _).trans hi)
  obtain ⟨f⟩ := hf
  refine ⟨⟨f⟩,(system hμ).atomic.eq_trans ?_ he⟩
  exact (system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (d,(C.vertex i).diagram) from
      ⟨le_rfl,⟨f.index,f.diagram⟩⟩))
    ((system hμ).atomic.eq_symm (hL i ((le_max_right _ _).trans hi)))

include hsize hmerger in
/-- The common code comparison is exactly forced equality, at any one
vertex at which both codes have linked representatives. -/
theorem links_eq_iff_same {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a b : ChainCode hμ c C}
    (ha : Links hμ c C d w τ a) (hb : Links hμ c C d w σ b) :
    (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ Same hμ c C d a b := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hb
  have he (i : ℕ) (hn : N ≤ i) (hl : L ≤ i) :
      (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔
        (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name := by
    obtain ⟨f⟩ := (hN i hn).1
    have hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
    constructor
    · intro h
      exact eq_at_root hμ hsize hmerger _ _ (C.vertex i).diagram w.diagram hf
        (a i).fixed (b i).fixed d
        ((system hμ).atomic.eq_trans (hN i hn).2 ((system hμ).atomic.eq_trans h
          ((system hμ).atomic.eq_symm (hL i hl).2)))
    · intro h
      have h' := (system hμ).atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (d,(C.vertex i).diagram) from ⟨le_rfl,hf⟩)) h
      exact (system hμ).atomic.eq_trans ((system hμ).atomic.eq_symm (hN i hn).2)
        ((system hμ).atomic.eq_trans h' (hL i hl).2)
  constructor
  · intro h
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)
      ((le_max_right _ _).trans hi)).mp h⟩
  · rintro ⟨K,hK⟩
    exact (he (max (max N L) K) ((le_max_left N L).trans (le_max_left _ _))
      ((le_max_right N L).trans (le_max_left _ _))).mpr (hK _ (le_max_right _ _))

variable (hμ c C)

/-- A representation in a principal quotient implies actual forced code
links. There is no genericity assumption on that principal quotient. -/
theorem links_of_represents_at (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (b : (D[principalFilter d]).Glued hj v)
    (ha : Represents hμ c hcard hsize hmerger hj E hE C (principalFilter d) a b)
    (w : Vertex q) (τ : LocalName hμ c w.diagram)
    (hτ : At hμ c hcard hsize hmerger hj E hE (principalFilter d) w τ.name b) :
    Links hμ c C d w τ.name a := by
  obtain ⟨hw,x,ρ,hρ,hx,hb⟩ := hτ
  have hρ' : ρ = τ := LocalName.ext hρ
  subst ρ
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := C.cofinal w hw
  refine ⟨max N L,fun i hi => ?_⟩
  let f : w.Arrow (C.vertex i) := hL.some.comp (C.increasing L i ((le_max_right _ _).trans hi)).some
  have hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  obtain ⟨hwi,y,σ,hσ,hy,hbi⟩ := hN i ((le_max_left _ _).trans hi)
  have hσ' : σ = a i := LocalName.ext hσ
  subst σ
  have hexy : (D[principalFilter d]).arrowMap hj f y = x := by
    apply (D[principalFilter d]).toGlued_injective hj v w hw
    rw [(D[principalFilter d]).toGlued_arrow hj v w (C.vertex i) hw hwi f y,hbi,hb]
  refine ⟨⟨f⟩,?_⟩
  apply ((localAtomic hμ w.diagram).eqG_principal d _ _).mp
  apply (LocalQuotient.ofName_eq (principalFilter d) ((a i).restrict hf) τ).mp
  calc
    LocalQuotient.ofName (principalFilter d) ((a i).restrict hf) =
        LocalQuotient.restrict (principalFilter d) hf y.val.val :=
      congrArg (LocalQuotient.restrict (principalFilter d) hf) hy
    _ = x.val.val := congrArg (fun z : (D[principalFilter d]).vertexFiber w => z.val.val) hexy
    _ = LocalQuotient.ofName (principalFilter d) τ := hx.symm

/-- A linked local name is in the exact fiber, not merely eligible. The
bijective contraction maps certify the exact ideal. -/
theorem at_of_represents_links (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (b : (D[principalFilter d]).Glued hj v)
    (ha : Represents hμ c hcard hsize hmerger hj E hE C (principalFilter d) a b)
    (w : Vertex q) (τ : LocalName hμ c w.diagram) (hτ : Links hμ c C d w τ.name a) :
    At hμ c hcard hsize hmerger hj E hE (principalFilter d) w τ.name b := by
  have hw := links_common hτ
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hτ
  let i := max N L
  obtain ⟨hwi,y,σ,hσ,hy,hbi⟩ := hN i (le_max_left _ _)
  have hσ' : σ = a i := LocalName.ext hσ
  subst σ
  obtain ⟨⟨f⟩,he⟩ := hL i (le_max_right _ _)
  have hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  refine ⟨hw,(D[principalFilter d]).arrowMap hj f y,τ,rfl,?_,?_⟩
  · have het : LocalQuotient.ofName (principalFilter d) ((a i).restrict hf) =
        LocalQuotient.ofName (principalFilter d) τ :=
      (LocalQuotient.ofName_eq (principalFilter d) _ _).mpr
        (((localAtomic hμ w.diagram).eqG_principal d _ _).mpr he)
    exact het.symm.trans (congrArg (LocalQuotient.restrict (principalFilter d) hf) hy)
  · exact ((D[principalFilter d]).toGlued_arrow hj v w (C.vertex i) hw hwi f y).trans hbi

/-- Extraction of the actual stable ideal from a persistent working code
and a literal name linked to it at w. -/
theorem links_stable (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a)
    (w : Vertex q) (τ : LocalName hμ c w.diagram) (hτ : Links hμ c C d w τ.name a) :
    (system hμ).Forces ![τ.name,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)
        (SetLanguage.isClass 0 1 2) ∧
      ∀ e, e ≤ d → forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index τ = w.ideal := by
  have hat (e : CohenForcing.Condition I κ) (hed : e ≤ d) :
      ∃ x : (D[principalFilter e]).vertexFiber w,
        LocalQuotient.ofName (principalFilter e) τ = x.val.val := by
    obtain ⟨b,hb⟩ := ha e hed
    obtain ⟨_,x,σ,hσ,hx,_⟩ := at_of_represents_links hμ c hcard hsize hmerger hj E hE C
      e a b hb w τ (links_mono hed hτ)
    have he : σ = τ := LocalName.ext hσ
    exact ⟨x,he ▸ hx⟩
  constructor
  · obtain ⟨x,hx⟩ := hat d le_rfl
    have he : EligibleName hμ c (principalFilter d) w.diagram E τ := by
      apply (eligible_ofName hμ c (principalFilter d) w.diagram E τ).mp
      rw [hx]
      exact x.val.property.2
    obtain ⟨e,he,hel⟩ := he
    exact (system hμ).atomic.forceFormula_mono
      (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (e,w.diagram) from
        ⟨(mem_principalFilter d e).mp he,le_rfl⟩)) hel
  · intro e hed
    obtain ⟨x,hx⟩ := hat e hed
    have hi := x.property
    rw [eligibleSystem_availability_eq hμ c hcard hsize hmerger E hE
      (principalFilter e) w.diagram w.index w.root x.val] at hi
    change (allLocalSystem (c := c) hμ hcard hsize hmerger (principalFilter e)).availability
      w.diagram w.index (LocalQuotient.ofName (principalFilter e) τ) = w.ideal
    rw [hx]
    exact hi

/-- Stable exact membership at any vertex in the component gives a code
which works at every stronger Cohen condition and remains linked there. -/
theorem exists_linked_working_of_stable (d : CohenForcing.Condition I κ)
    (w : Vertex q) (hw : Vertex.Common v w) (τ : LocalName hμ c w.diagram)
    (hel : (system hμ).Forces ![τ.name,labelSet hμ c,E]
      ((d,w.diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2))
    (hstable : ∀ e, e ≤ d →
      forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index τ = w.ideal) :
    ∃ a : ChainCode hμ c C, Works hμ c hcard hsize hmerger hj E hE C d a ∧
      Links hμ c C d w τ.name a := by
  have hex (e : CohenForcing.Condition I κ) (hed : e ≤ d) :
      ∃ x : (D[principalFilter e]).vertexFiber w,
        LocalQuotient.ofName (principalFilter e) τ = x.val.val :=
    exists_fiber_principal hμ c hcard hsize hmerger E hE e w τ
      ((system hμ).atomic.forceFormula_mono
        (WithTop.coe_le_coe.mpr (show (e,w.diagram) ≤ (d,w.diagram) from ⟨hed,le_rfl⟩)) hel)
      (hstable e hed)
  obtain ⟨x,hx⟩ := hex d le_rfl
  let b := (D[principalFilter d]).toGlued hj v w hw x
  obtain ⟨a,ha⟩ := exists_representing_code (C := C) (principalFilter d) b
  have hl := links_of_represents_at hμ c hcard hsize hmerger hj E hE C d a b ha w τ
    ⟨hw,x,τ,rfl,hx,rfl⟩
  refine ⟨a,?_,hl⟩
  intro e hed
  obtain ⟨x',hx'⟩ := hex e hed
  obtain ⟨N,hN⟩ := links_mono hed hl
  refine ⟨(D[principalFilter e]).toGlued hj v w hw x',N,fun i hi => ?_⟩
  obtain ⟨⟨f⟩,he⟩ := hN i hi
  let hf : w.diagram ≤ (C.vertex i).diagram := ⟨f.index,f.diagram⟩
  obtain ⟨y,hy⟩ := (D[principalFilter e]).arrowMap_bijective hj f |>.2 x'
  have heq : LocalQuotient.ofName (principalFilter e) (a i) = y.val.val := by
    apply LocalQuotient.restrict_injective (principalFilter e) hsize hmerger hf
    have ht : LocalQuotient.ofName (principalFilter e) ((a i).restrict hf) =
        LocalQuotient.ofName (principalFilter e) τ :=
      (LocalQuotient.ofName_eq (principalFilter e) _ _).mpr
        (((localAtomic hμ w.diagram).eqG_principal e _ _).mpr he)
    exact ht.trans (hx'.trans
      (congrArg (fun z : (D[principalFilter e]).vertexFiber w => z.val.val) hy).symm)
  refine ⟨C.common i,y,a i,rfl,heq,?_⟩
  rw [← (D[principalFilter e]).toGlued_arrow hj v w (C.vertex i) hw (C.common i) f y,hy]

omit [Infinite M] [Infinite I] in
/-- Restriction along an actual contraction preserves the literal linked
representative. Both the condition and the code remain unchanged. -/
theorem links_restrict (d : CohenForcing.Condition I κ) {w z : Vertex q}
    (f : w.Arrow z) (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (a : ChainCode hμ c C) (h : Links hμ c C d z τ a) :
    Links hμ c C d w τ a := by
  obtain ⟨N,hN⟩ := h
  refine ⟨N,fun i hi => ?_⟩
  obtain ⟨⟨g⟩,he⟩ := hN i hi
  exact ⟨⟨f.comp g⟩,(system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (d,w.diagram) ≤ (d,z.diagram) from
      ⟨le_rfl,⟨f.index,f.diagram⟩⟩)) he⟩

/-- A working code has a normalized representative at EVERY vertex in its
component; this is not restricted to the first vertex of the chosen chain. -/
theorem working_linked (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a)
    (w : Vertex q) (hw : Vertex.Common v w) :
    ∃ τ : LocalName hμ c w.diagram, Links hμ c C d w τ.name a := by
  obtain ⟨b,hb⟩ := ha d le_rfl
  obtain ⟨x,hx⟩ := (D[principalFilter d]).toGlued_surjective hj v w hw b
  obtain ⟨τ,hτ⟩ := Quotient.mk'_surjective
    (s := localSetoid (c := c) hμ (principalFilter d) w.diagram) x.val.val
  exact ⟨τ,links_of_represents_at hμ c hcard hsize hmerger hj E hE C d a b hb w τ
    ⟨hw,x,τ,rfl,hτ,hx⟩⟩

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_UniformNames
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## UniformFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
theorem uniformRange_fixed {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (g : Γ) (hg : g ∈ H) :
    g • S.uniformRange f H hH hfix = S.uniformRange f H hH hfix :=
  Subtype.ext (S.collectName_fixed _ _ H
    (fun g hg i _ _ => ⟨i,(hfix g hg i).symm,trivial⟩) g hg)

omit [OrderTop P] in
theorem mem_uniformRange {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (x : S.Name) (p : P) :
    S.atomic.MemF p x (S.uniformRange f H hH hfix) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, S.atomic.EqF r x (f i) := by
  rw [uniformRange,S.mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,i,_,_,_,he⟩ := h q hqp
    exact ⟨r,hrq,i,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,i,he⟩ := h q hqp
    exact ⟨r,hrq,i,r,trivial,le_rfl,he⟩

omit [OrderTop P] in
/-- The injection sentence, with its full maps-to conjunct retained. -/
theorem forces_injection {n} (v : Fin n → S.Name) (p : P) (f a b : Fin n) :
    S.Forces v p (SetLanguage.injection f a b) ↔
      S.Forces ![v f,v a,v b] p (SetLanguage.mapsTo 0 1 2) ∧
      ∀ x y z : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v a) →
        ∀ r, r ≤ q → S.atomic.MemF r y (v a) → ∀ s, s ≤ r →
          S.App s (v f) x z ∧ S.App s (v f) y z → S.atomic.EqF s x y := by
  simp only [Forces,SetLanguage.injection,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    ForcingQuotient.AtomicData.forceFormula_equal,S.forces_edge]
  have hv : (v ∘ ![f,a,b]) ∘ ![0,1,2] = ![v f,v a,v b] ∘ ![0,1,2] := by
    funext i
    fin_cases i <;> rfl
  simp only [SetLanguage.mapsTo,S.atomic.forceFormula_rename S.atomic_regular,hv]
  rfl

/-- A bounded functional relation which is also one-to-one gives an actual
internal injection graph. -/
theorem BinaryRelation.graph_injection (R : S.BinaryRelation)
    (X Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hX : ∀ g ∈ H, g • X = X) (hY : ∀ g ∈ H, g • Y = Y)
    (hR : ∀ g ∈ H, ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))
    (p : P)
    (htotal : ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ R.holds s x y)
    (hone : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x y → R.holds q x z →
      S.atomic.EqF q y z)
    (hinj : ∀ q, q ≤ p → ∀ x y z : S.Name, R.holds q x z → R.holds q y z →
      S.atomic.EqF q x y) :
    S.Forces ![R.graph X Y H hH hX hY hR,X,Y] p (SetLanguage.injection 0 1 2) := by
  rw [S.forces_injection]
  refine ⟨R.graph_mapsTo X Y H hH hX hY hR p htotal hone,?_⟩
  rintro x y z q hqp _ r hrq _ s hsr ⟨hx,hy⟩
  exact hinj s (hsr.trans (hrq.trans hqp)) x y z
    ((R.app_graph X Y H hH hX hY hR x z s).mp hx).2.2
    ((R.app_graph X Y H hH hX hY hR y z s).mp hy).2.2

namespace UniformInverse
variable {S}
variable (X : ZFSet.{u}) (f : X → S.Name)

omit [OrderTop P] in
theorem least_mono {p q : P} {x : S.Name} {i : X}
    (h : q ≤ p) (hi : LeastValue X f p x i) : LeastValue X f q x i :=
  ⟨S.atomic.eq_mono h hi.1,fun j hj r hr => hi.2 j hj r (hr.trans h)⟩

omit [OrderTop P] in
theorem least_unique {p : P} {x : S.Name} {i j : X}
    (hi : LeastValue X f p x i) (hj : LeastValue X f p x j) : i = j := by
  rcases trichotomous_of WellOrderingRel i j with h | h | h
  · exact (hj.2 i h p le_rfl hi.1).elim
  · exact h
  · exact (hi.2 j h p le_rfl hj.1).elim

theorem relation_one {p : P} {x y z : S.Name}
    (hy : (relation X f).holds p x y) (hz : (relation X f).holds p x z) :
    S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,i,hyi,hi⟩ := hy q hqp
  obtain ⟨s,hsr,j,hzj,hj⟩ := hz r (hrq.trans hqp)
  have hij := least_unique X f (least_mono X f hsr hi) hj
  subst j
  exact ⟨s,hsr.trans hrq,S.atomic.eq_trans (S.atomic.eq_mono hsr hyi) (S.atomic.eq_symm hzj)⟩

theorem relation_inj {p : P} {x y z : S.Name}
    (hx : (relation X f).holds p x z) (hy : (relation X f).holds p y z) :
    S.atomic.EqF p x y := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,i,hzi,hi⟩ := hx q hqp
  obtain ⟨s,hsr,j,hzj,hj⟩ := hy r (hrq.trans hqp)
  have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val s).mp
    (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hsr hzi)) hzj))
  subst j
  exact ⟨s,hsr.trans hrq,S.atomic.eq_trans (S.atomic.eq_mono hsr hi.1) (S.atomic.eq_symm hj.1)⟩

/-- Least indices are dense below every condition forcing membership in
this range. Minimality is proved using the ground wellorder; no choice
function in the symmetric extension or completeness of a filter is assumed. -/
theorem relation_total (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (x : S.Name) (p : P)
    (hm : S.atomic.MemF p x (S.uniformRange f H hH hfix)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name,
      S.atomic.MemF r y (Name.check X) ∧ (relation X f).holds r x y := by
  intro q hqp
  have hne : {i : X | ∃ r, r ≤ q ∧ S.atomic.EqF r x (f i)}.Nonempty := by
    obtain ⟨r,hrq,i,he⟩ := (S.mem_uniformRange f H hH hfix x p).mp hm q hqp
    exact ⟨i,r,hrq,he⟩
  obtain ⟨i,⟨r,hrq,hi⟩,hmin⟩ := WellOrderingRel.isWellOrder.wf.has_min _ hne
  have hl : LeastValue X f r x i := by
    refine ⟨hi,?_⟩
    intro j hj s hsr he
    exact hmin j ⟨s,hsr.trans hrq,he⟩ hj
  exact ⟨r,hrq,Name.check i.val,S.check_mem_of_mem i.property r,
    fun s hsr => ⟨s,le_rfl,i,S.atomic.eq_refl s _,least_mono X f hsr hl⟩⟩

end UniformInverse

theorem uniformSubsetInverse_injection (X : ZFSet.{u}) (f : X → S.Name) (Y : S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (hY : ∀ g ∈ H, g • Y = Y) (p : P)
    (hsub : S.SubsetF p Y (S.uniformRange f H hH hfix)) :
    S.Forces ![S.uniformSubsetInverse X f Y H hH hfix hY,Y,Name.check X]
      p (SetLanguage.injection 0 1 2) := by
  apply (UniformInverse.relation X f).graph_injection
  · intro x q hqp hx
    exact UniformInverse.relation_total X f H hH hfix x q (hsub x q hqp hx)
  · intro q _ x y z
    exact UniformInverse.relation_one X f
  · intro q _ x y z
    exact UniformInverse.relation_inj X f

/-- If a set cannot be injected into the index set, then densely it has an
element outside this evaluation list. Nonmembership in the list is forced
below the witness condition, rather than just presently undecided. -/
theorem outside_uniformRange (X : ZFSet.{u}) (f : X → S.Name) (Y : S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (hY : ∀ g ∈ H, g • Y = Y) (p : P)
    (hno : ∀ q, q ≤ p → ∀ J : S.Name,
      ¬ S.Forces ![J,Y,Name.check X] q (SetLanguage.injection 0 1 2)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, S.atomic.MemF r y Y ∧
      ∀ s, s ≤ r → ¬ S.atomic.MemF s y (S.uniformRange f H hH hfix) := by
  intro q hqp
  have hsub : ¬ S.SubsetF q Y (S.uniformRange f H hH hfix) := by
    intro h
    exact hno q hqp _ (S.uniformSubsetInverse_injection X f Y H hH hfix hY q h)
  change ¬ (∀ y r, r ≤ q → S.atomic.MemF r y Y →
    S.atomic.MemF r y (S.uniformRange f H hH hfix)) at hsub
  push Not at hsub
  obtain ⟨y,r,hrq,hy,hout⟩ := hsub
  have hstrong : ∃ s, s ≤ r ∧ ∀ t, t ≤ s →
      ¬ S.atomic.MemF t y (S.uniformRange f H hH hfix) := by
    by_contra hn
    push Not at hn
    exact hout (S.atomic_regular.2 _ _ _ hn)
  obtain ⟨s,hsr,hs⟩ := hstrong
  exact ⟨s,hsr.trans hrq,y,S.atomic.mem_mono hsr hy,hs⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CheckOrdinal -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Members of a checked ordinal are locally checked smaller ordinals. -/
theorem mem_checkOrdinal (α : Ordinal.{u}) (x : S.Name) (p : P) :
    S.atomic.MemF p x (Name.check α.toZFSet) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ β : Ordinal.{u}, β < α ∧
        S.atomic.EqF r x (Name.check β.toZFSet) := by
  rw [S.mem_check]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,y,hy,he⟩ := h q hqp
    obtain ⟨β,hβ,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
    exact ⟨r,hrq,β,hβ,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,β,hβ,he⟩ := h q hqp
    exact ⟨r,hrq,β.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hβ,he⟩

/-- Transitivity of a ground ordinal survives arbitrary set symmetric
forcing. Quantified members here are all HS names, not just check names. -/
theorem transF_checkOrdinal (α : Ordinal.{u}) (p : P) :
    S.TransF p (Name.check α.toZFSet) := by
  intro x y q _ hx hy
  apply S.atomic_regular.2
  intro r hrq
  obtain ⟨s,hsr,β,hβ,he⟩ := (S.mem_checkOrdinal α x q).mp hx r hrq
  have hm : S.atomic.MemF s y (Name.check β.toZFSet) :=
    (S.atomic.mem_congr (S.atomic.eq_refl s y) he).mp (S.atomic.mem_mono (hsr.trans hrq) hy)
  obtain ⟨t,hts,γ,hγ,he'⟩ := (S.mem_checkOrdinal β y s).mp hm s le_rfl
  exact ⟨t,hts.trans hsr,(S.atomic.mem_congr he' (S.atomic.eq_refl t _)).mpr
    (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr (hγ.trans hβ)) t)⟩

/-- Each member of a check ordinal is forced to be transitive as well. -/
theorem ordF_checkOrdinal (α : Ordinal.{u}) (p : P) :
    S.OrdF p (Name.check α.toZFSet) := by
  refine ⟨S.transF_checkOrdinal α p,?_⟩
  intro x q _ hx y z r hrq hy hz
  apply S.atomic_regular.2
  intro s hsr
  obtain ⟨t,hts,β,_,he⟩ := (S.mem_checkOrdinal α x q).mp hx s (hsr.trans hrq)
  have ht : S.TransF t x := (S.transF_congr he).mpr (S.transF_checkOrdinal β t)
  exact ⟨t,hts,ht y z t le_rfl (S.atomic.mem_mono (hts.trans hsr) hy)
    (S.atomic.mem_mono (hts.trans hsr) hz)⟩

omit [OrderTop P] in
/-- Internal membership well-foundedness follows from the proved name-rank
Foundation argument, and holds for every set of the symmetric model. -/
theorem forces_membershipWellFounded {n} (v : Fin n → S.Name) (p : P) (a : Fin n) :
    S.Forces v p (SetLanguage.membershipWellFounded a) := by
  simp only [Forces,SetLanguage.membershipWellFounded,
    S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_mem]
  intro x q _ hx r hrq
  obtain ⟨s,hsr,y,hy⟩ := (S.forces_nonempty _ q 1).mp hx.2 r hrq
  obtain ⟨t,hts,z,hz,hmin⟩ := S.minimal_member x y s hy
  refine ⟨t,hts.trans hsr,z,hz,?_⟩
  intro b u hut hbx v hvu hbz
  exact hmin b v (hvu.trans hut) hbz (S.atomic.mem_mono hvu hbx)

/-- An actual checked ordinal satisfies the exact ordinal formula used by
`ACwo`. Neither external well-foundedness of a model nor a weakened proxy
for that formula is used. -/
theorem forces_checkOrdinal (α : Ordinal.{u}) (p : P) :
    S.Forces ![Name.check α.toZFSet] p (SetLanguage.ordinal 0) := by
  refine ⟨(S.forces_transitiveSet _ p 0).mpr (S.transF_checkOrdinal α p),?_,
    S.forces_membershipWellFounded _ p 0⟩
  change S.Forces ![Name.check α.toZFSet] p (SetLanguage.membershipLinear 0)
  simp only [Forces,SetLanguage.membershipLinear,
    S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_mem]
  refine ⟨?_,?_,?_⟩
  · intro x q _ hx r hrq hself
    obtain ⟨s,hsr,β,_,he⟩ := (S.mem_checkOrdinal α x r).mp
      (S.atomic.mem_mono hrq hx) r le_rfl
    have h := (S.atomic.mem_congr he he).mp (S.atomic.mem_mono hsr hself)
    exact ZFSet.mem_irrefl β.toZFSet ((S.mem_check_check _ _ s).mp h)
  · intro x y z q hqp hx r hrq hy s hsr hz t hts hxy
    have ht := (S.ordF_checkOrdinal α p).2 z s (hsr.trans (hrq.trans hqp)) hz
    exact ht y x t hts hxy.2 hxy.1
  · intro x y q _ hx r hrq hy
    apply (S.atomic.forceFormula_disj _ _ _ _).mpr
    intro s hsr
    obtain ⟨t,hts,β,_,hxβ⟩ := (S.mem_checkOrdinal α x q).mp hx s (hsr.trans hrq)
    obtain ⟨u,hut,γ,_,hyγ⟩ := (S.mem_checkOrdinal α y r).mp hy t (hts.trans hsr)
    refine ⟨u,hut.trans hts,?_⟩
    have hxβ := S.atomic.eq_mono hut hxβ
    rcases lt_trichotomy β γ with h | h | h
    · right
      apply (S.atomic.forceFormula_disj _ _ _ _).mpr
      intro v hvu
      exact ⟨v,le_rfl,Or.inl (S.atomic.mem_mono hvu
        ((S.atomic.mem_congr hxβ hyγ).mpr
          (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr h) u)))⟩
    · left
      change S.atomic.EqF u x y
      subst γ
      exact S.atomic.eq_trans hxβ (S.atomic.eq_symm hyγ)
    · right
      apply (S.atomic.forceFormula_disj _ _ _ _).mpr
      intro v hvu
      exact ⟨v,le_rfl,Or.inr (S.atomic.mem_mono hvu
        ((S.atomic.mem_congr hyγ hxβ).mpr
          (S.check_mem_of_mem (Ordinal.toZFSet_mem_toZFSet_iff.mpr h) u)))⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_RelationCalculus
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small _root_.OAI.PartitionConsistency.ProductForcing.instSmallPresentationIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## RelationTools -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

namespace UnaryRelation
variable {S} (R : S.UnaryRelation)
variable (X : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hX : ∀ g ∈ H, g • X = X)
variable (hR : ∀ g ∈ H, ∀ p x, R.holds p x → R.holds (S.move g p) (g • x))

omit [OrderTop P] in
theorem mem_select (x : S.Name) (p : P) :
    S.atomic.MemF p x (R.select X H hH hX hR) ↔
      S.atomic.MemF p x X ∧ R.holds p x := by
  rw [select,S.mem_collect]
  constructor
  · intro h
    have hd q (hqp : q ≤ p) : ∃ r, r ≤ q ∧ S.atomic.MemF r x X ∧ R.holds r x := by
      obtain ⟨r,hrq,i,a,hi,hra,he⟩ := h q hqp
      exact ⟨r,hrq,(S.atomic.mem_congr he (S.atomic.eq_refl r _)).mpr
        (S.atomic.mem_mono hra hi.1),(R.congr he).mpr (R.mono hra hi.2)⟩
    exact ⟨S.atomic_regular.2 _ _ _ (fun q hqp => (hd q hqp).imp
      (fun r hr => ⟨hr.1,hr.2.1⟩)),R.regular (fun q hqp => (hd q hqp).imp
      (fun r hr => ⟨hr.1,hr.2.2⟩))⟩
  · rintro ⟨hx,hR⟩ q hqp
    obtain ⟨r,hrq,σ,a,ha,hra,he⟩ := S.mem_iff.mp hx q hqp
    let i : Edges X.raw := ⟨(σ.raw,S.code a),ha⟩
    have hi : X.child i.property = σ := Name.ext rfl
    refine ⟨r,hrq,i,r,?_,le_rfl,?_⟩
    · change S.atomic.MemF r (X.child i.property) X ∧ R.holds r (X.child i.property)
      rw [hi]
      exact ⟨S.mem_of_edge ha hra,(R.congr he).mp (R.mono (hrq.trans hqp) hR)⟩
    · simpa only [hi] using he

end UnaryRelation

omit [OrderTop P]

/-- Convenient semantic consequences of the full internal function formulas. -/
theorem mapsTo_function {f X Y : S.Name} {p : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![f,X] p (SetLanguage.functionOn 0 1) := (S.forces_mapsTo _ _ _ _ _).mp h |>.1

theorem mapsTo_value {f X Y x y : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) (hxy : S.App q f x y) : S.atomic.MemF q y Y :=
  (S.forces_mapsTo _ _ _ _ _).mp h |>.2 x y q hq hx q le_rfl hxy

theorem mapsTo_total {f X Y x : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ S.App s f x y := by
  intro r hrq
  obtain ⟨s,hsr,y,hy,_⟩ := S.functionOn_total ![f,X] p 0 1 (S.mapsTo_function h) x hq hx r hrq
  exact ⟨s,hsr,y,S.mapsTo_value h (hsr.trans (hrq.trans hq))
    (S.atomic.mem_mono (hsr.trans hrq) hx) hy,hy⟩

theorem mapsTo_unique {f X Y x y z : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) (hy : S.App q f x y) (hz : S.App q f x z) :
    S.atomic.EqF q y z :=
  S.functionOn_unique ![f,X] q 0 1
    (S.atomic.forceFormula_mono hq (S.mapsTo_function h)) x y z hx hy hz

theorem surjection_mapsTo {f X Y : S.Name} {p : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2) := (S.forces_surjection _ _ _ _ _).mp h |>.1

theorem surjection_onto {f X Y y : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2)) (hq : q ≤ p)
    (hy : S.atomic.MemF q y Y) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x : S.Name, S.atomic.MemF s x X ∧ S.App s f x y :=
  (S.forces_surjection _ _ _ _ _).mp h |>.2 y q hq hy

theorem injection_mapsTo {f X Y : S.Name} {p : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2) := (S.forces_injection _ _ _ _ _).mp h |>.1

theorem injection_one {f X Y x y z : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) (hy : S.atomic.MemF q y X)
    (hxz : S.App q f x z) (hyz : S.App q f y z) : S.atomic.EqF q x y :=
  (S.forces_injection _ _ _ _ _).mp h |>.2 x y z q hq hx q le_rfl hy q le_rfl ⟨hxz,hyz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## MapCalculus -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem app_compositionGraph (f g X Y Z x z : S.Name) (p : P) :
    S.App p (S.compositionGraph f g X Y Z) x z ↔
      (S.compositionRelation f g X Y Z).holds p x z := by
  unfold compositionGraph
  erw [BinaryRelation.app_graph]
  constructor
  · exact fun h => h.2.2
  · intro h
    refine ⟨S.atomic_regular.2 _ _ _ ?_,S.atomic_regular.2 _ _ _ ?_,h⟩
    · intro q hq
      obtain ⟨r,hrq,y,hh,_⟩ := h q hq
      exact ⟨r,hrq,hh.1⟩
    · intro q hq
      obtain ⟨r,hrq,y,_,hh⟩ := h q hq
      exact ⟨r,hrq,hh.2.1⟩

theorem compositionRelation_one (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ x y z : S.Name,
      (S.compositionRelation f g X Y Z).holds q x y →
      (S.compositionRelation f g X Y Z).holds q x z → S.atomic.EqF q y z := by
  intro q hq x y z hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay⟩ := hy r hrq
  obtain ⟨t,hts,b,hb,hbz⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have hab := S.mapsTo_unique hf htp (S.atomic.mem_mono hts ha.1)
    (S.app_mono hts ha.2.2) hb.2.2
  have hay' := (S.app_congr (S.atomic.eq_refl t g) hab (S.atomic.eq_refl t y)).mp
    (S.app_mono hts hay.2.2)
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hg htp hb.2.1 hay' hbz.2.2⟩

theorem compositionGraph_mapsTo (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![S.compositionGraph f g X Y Z,X,Z] p (SetLanguage.mapsTo 0 1 2) := by
  unfold compositionGraph
  apply BinaryRelation.graph_mapsTo
  · intro x q hq hx r hrq
    obtain ⟨s,hsr,y,hy,hxy⟩ := S.mapsTo_total hf hq hx r hrq
    obtain ⟨t,hts,z,hz,hyz⟩ := S.mapsTo_total hg (hsr.trans (hrq.trans hq)) hy s le_rfl
    refine ⟨t,hts.trans hsr,z,hz,fun a hat => ⟨a,le_rfl,y,?_,?_⟩⟩
    · exact ⟨S.atomic.mem_mono (hat.trans (hts.trans (hsr.trans hrq))) hx,
        S.atomic.mem_mono (hat.trans hts) hy,S.app_mono (hat.trans hts) hxy⟩
    · exact ⟨S.atomic.mem_mono (hat.trans hts) hy,S.atomic.mem_mono hat hz,S.app_mono hat hyz⟩
  · exact S.compositionRelation_one f g X Y Z p hf hg

theorem compositionGraph_surjection (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![S.compositionGraph f g X Y Z,X,Z] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  refine ⟨S.compositionGraph_mapsTo f g X Y Z p (S.surjection_mapsTo hf) (S.surjection_mapsTo hg),?_⟩
  intro z q hq hz r hrq
  obtain ⟨s,hsr,y,hy,hyz⟩ := S.surjection_onto hg hq hz r hrq
  obtain ⟨t,hts,x,hx,hxy⟩ := S.surjection_onto hf (hsr.trans (hrq.trans hq)) hy s le_rfl
  refine ⟨t,hts.trans hsr,x,hx,(S.app_compositionGraph f g X Y Z x z t).mpr ?_⟩
  intro a hat
  exact ⟨a,le_rfl,y,⟨S.atomic.mem_mono hat hx,S.atomic.mem_mono (hat.trans hts) hy,S.app_mono hat hxy⟩,
    ⟨S.atomic.mem_mono (hat.trans hts) hy,S.atomic.mem_mono (hat.trans (hts.trans (hsr.trans hrq))) hz,
      S.app_mono (hat.trans hts) hyz⟩⟩

theorem compositionGraph_injection (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![S.compositionGraph f g X Y Z,X,Z] p (SetLanguage.injection 0 1 2) := by
  rw [S.forces_injection]
  refine ⟨S.compositionGraph_mapsTo f g X Y Z p (S.injection_mapsTo hf) (S.injection_mapsTo hg),?_⟩
  rintro x y z q hq _ r hrq _ s hsr ⟨hx,hy⟩
  apply S.atomic_regular.1
  intro t hts
  obtain ⟨a,hat,b,hb,hbz⟩ := (S.app_compositionGraph f g X Y Z x z s).mp hx t hts
  obtain ⟨c,hca,d,hd,hdz⟩ := (S.app_compositionGraph f g X Y Z y z s).mp hy a (hat.trans hts)
  have hcp := hca.trans (hat.trans (hts.trans (hsr.trans (hrq.trans hq))))
  have hbd := S.injection_one hg hcp (S.atomic.mem_mono hca hb.2.1) hd.2.1
    (S.app_mono hca hbz.2.2) hdz.2.2
  have hxd := (S.app_congr (S.atomic.eq_refl c f) (S.atomic.eq_refl c x) hbd).mp
    (S.app_mono hca hb.2.2)
  exact ⟨c,hca.trans hat,S.injection_one hf hcp (S.atomic.mem_mono hca hb.1) hd.1 hxd hd.2.2⟩

theorem app_inverseGraph (f X Y x y : S.Name) (p : P) :
    S.App p (S.inverseGraph f X Y) y x ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ S.App p f x y := by
  unfold inverseGraph
  erw [BinaryRelation.app_graph]
  change (_ ∧ _ ∧ (_ ∧ _ ∧ _)) ↔ _
  tauto

theorem inverseGraph_injection (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hi : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![S.inverseGraph f X Y,Y,X] p (SetLanguage.injection 0 1 2) := by
  unfold inverseGraph
  apply BinaryRelation.graph_injection
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf hq hy r hrq
    exact ⟨s,hsr,x,hx,hx,S.atomic.mem_mono (hsr.trans hrq) hy,hxy⟩
  · intro q hq y x z hx hz
    exact S.injection_one hi hq hx.1 hz.1 hx.2.2 hz.2.2
  · intro q hq x y z hx hy
    exact S.mapsTo_unique (S.surjection_mapsTo hf) hq hx.1 hx.2.2 hy.2.2

theorem inverseGraph_surjection (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hi : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![S.inverseGraph f X Y,Y,X] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  refine ⟨S.injection_mapsTo (S.inverseGraph_injection f X Y p hf hi),?_⟩
  intro x q hq hx r hrq
  obtain ⟨s,hsr,y,hy,hxy⟩ := S.mapsTo_total (S.surjection_mapsTo hf) hq hx r hrq
  exact ⟨s,hsr,y,hy,(S.app_inverseGraph f X Y x y s).mpr
    ⟨S.atomic.mem_mono (hsr.trans hrq) hx,hy,hxy⟩⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalPresentation
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Completion -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
/-- An exact description of the default relation's Boolean disjunction.
The fallback is used only when every possible bounded graph value is ruled out. -/
theorem defaultRelation_iff (f X x₀ a y : S.Name) (p : P) :
    (S.defaultRelation f X x₀).holds p a y ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧
        ((S.App r f a y ∧ S.atomic.MemF r y X) ∨
          (S.NoValue f X r a ∧ S.atomic.EqF r y x₀)) := by
  simp only [defaultRelation,BinaryRelation.ofFormula,defaultFormula,Forces,
    ForcingQuotient.AtomicData.forceFormula_disj,ForcingQuotient.AtomicData.forceFormula_conj,
    ForcingQuotient.AtomicData.forceFormula_ex,S.atomic.forceFormula_neg S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_mem,ForcingQuotient.AtomicData.forceFormula_equal,
    S.forces_edge]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,hr | hr⟩ := h q hqp
    · exact ⟨r,hrq,Or.inl hr⟩
    · refine ⟨r,hrq,Or.inr ⟨?_,hr.2⟩⟩
      intro t htr z ha hz
      apply hr.1 t htr
      intro b hbt
      exact ⟨b,le_rfl,z,S.app_mono hbt ha,S.atomic.mem_mono hbt hz⟩
  · intro h q hqp
    obtain ⟨r,hrq,hr | hr⟩ := h q hqp
    · exact ⟨r,hrq,Or.inl hr⟩
    · refine ⟨r,hrq,Or.inr ⟨?_,hr.2⟩⟩
      intro t htr hh
      obtain ⟨b,hbt,z,ha,hz⟩ := hh t le_rfl
      exact hr.1 b (hbt.trans htr) z ha hz

omit [OrderTop P] in
theorem defaultRelation_of_app {f X x₀ a y : S.Name} {p : P}
    (ha : S.App p f a y) (hy : S.atomic.MemF p y X) :
    (S.defaultRelation f X x₀).holds p a y := by
  apply (S.defaultRelation_iff f X x₀ a y p).mpr
  intro q hqp
  exact ⟨q,le_rfl,Or.inl ⟨S.app_mono hqp ha,S.atomic.mem_mono hqp hy⟩⟩

omit [OrderTop P] in
/-- The default construction is densely total, with values actually in `X`,
whenever the default belongs to `X`. -/
theorem defaultRelation_total (f X x₀ a : S.Name) {p : P} (hx₀ : S.atomic.MemF p x₀ X) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name,
      S.atomic.MemF r y X ∧ (S.defaultRelation f X x₀).holds r a y := by
  intro q hqp
  by_cases hh : ∃ r, r ≤ q ∧ ∃ y : S.Name, S.App r f a y ∧ S.atomic.MemF r y X
  · obtain ⟨r,hrq,y,ha,hy⟩ := hh
    exact ⟨r,hrq,y,hy,S.defaultRelation_of_app ha hy⟩
  · refine ⟨q,le_rfl,x₀,S.atomic.mem_mono hqp hx₀,?_⟩
    apply (S.defaultRelation_iff f X x₀ a x₀ q).mpr
    intro r hrq
    refine ⟨r,le_rfl,Or.inr ⟨?_,S.atomic.eq_refl r x₀⟩⟩
    intro t htr y ha hy
    exact hh ⟨t,htr.trans hrq,y,ha,hy⟩

omit [OrderTop P] in
/-- Completing a genuinely single-valued partial graph preserves uniqueness. -/
theorem defaultRelation_unique (f X x₀ : S.Name)
    (hf : ∀ p, ∀ a y z : S.Name, S.App p f a y → S.App p f a z → S.atomic.EqF p y z)
    (p : P) (a y z : S.Name) (hy : (S.defaultRelation f X x₀).holds p a y)
    (hz : (S.defaultRelation f X x₀).holds p a z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,hr⟩ := (S.defaultRelation_iff f X x₀ a y p).mp hy q hqp
  obtain ⟨s,hsr,hs⟩ := (S.defaultRelation_iff f X x₀ a z p).mp hz r (hrq.trans hqp)
  refine ⟨s,hsr.trans hrq,?_⟩
  rcases hr with ⟨hr,hyX⟩ | ⟨hr,hy₀⟩ <;> rcases hs with ⟨hs,hzX⟩ | ⟨hs,hz₀⟩
  · exact hf s a y z (S.app_mono hsr hr) hs
  · exact (hs s le_rfl y (S.app_mono hsr hr) (S.atomic.mem_mono hsr hyX)).elim
  · exact (hr s hsr z hs hzX).elim
  · exact S.atomic.eq_trans (S.atomic.eq_mono hsr hy₀) (S.atomic.eq_symm hz₀)

theorem completionRelation_at (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name)
    (i : O) (a y : S.Name) (p : P) (h : (S.defaultRelation (f i) X x₀).holds p a y) :
    (S.completionRelation O f X x₀).holds p (a.opair (Name.check i.val)) y :=
  fun q hqp => ⟨q,le_rfl,i,a,S.atomic.eq_refl q _,(S.defaultRelation _ X x₀).mono hqp h⟩

/-- Uniqueness for a family of partial functions survives both completion and
packaging into one Cartesian-domain graph. -/
theorem completionRelation_unique (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name)
    (hf : ∀ i p, ∀ a y z : S.Name, S.App p (f i) a y → S.App p (f i) a z →
      S.atomic.EqF p y z) (p : P) (x y z : S.Name)
    (hy : (S.completionRelation O f X x₀).holds p x y)
    (hz : (S.completionRelation O f X x₀).holds p x z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hqp
  obtain ⟨r,hrq,i,a,ha,hy⟩ := hy q hqp
  obtain ⟨s,hsr,j,b,hb,hz⟩ := hz r (hrq.trans hqp)
  have hh := S.eq_opair_iff.mp (S.atomic.eq_trans
    (S.atomic.eq_symm (S.atomic.eq_mono hsr ha)) hb)
  have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val s).mp hh.2)
  subst j
  refine ⟨s,hsr.trans hrq,?_⟩
  apply S.defaultRelation_unique (f i) X x₀ (hf i) s b y z
  · exact ((S.defaultRelation (f i) X x₀).congr hh.1 (S.atomic.eq_refl s y)).mp
      ((S.defaultRelation (f i) X x₀).mono hsr hy)
  · exact hz

/-- The completed relation is total on the literal product name. -/
theorem completionRelation_total (O : ZFSet.{u}) (f : O → S.Name) (A X x₀ : S.Name)
    {p : P} (hx₀ : S.atomic.MemF p x₀ X) (x : S.Name) {q : P} (hqp : q ≤ p)
    (hx : S.atomic.MemF q x (S.cartesianName A (Name.check O))) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name,
      S.atomic.MemF s y X ∧ (S.completionRelation O f X x₀).holds s x y := by
  intro r hrq
  obtain ⟨s,hsr,a,b,_,hb,hx⟩ := (S.mem_cartesianName A (Name.check O) x q).mp hx r hrq
  obtain ⟨t,hts,i,hi,hbi⟩ := (S.mem_check O b s).mp hb s le_rfl
  let i' : O := ⟨i,hi⟩
  obtain ⟨v,hvt,y,hy,hf⟩ := S.defaultRelation_total (f i') X x₀ a
    (S.atomic.mem_mono (hts.trans (hsr.trans (hrq.trans hqp))) hx₀) t le_rfl
  refine ⟨v,hvt.trans (hts.trans hsr),y,hy,?_⟩
  have hx' := S.atomic.eq_trans (S.atomic.eq_mono (hvt.trans hts) hx)
    (S.eq_opair_congr (S.atomic.eq_refl v a) (S.atomic.eq_mono hvt hbi))
  exact ((S.completionRelation O f X x₀).congr hx' (S.atomic.eq_refl v y)).mpr
    (S.completionRelation_at O f X x₀ i' a y v hf)

/-- A densely covering family of invariant partial functions yields an actual
internal surjection from `A × O` onto `X`. All graph and domain names have been
constructed; the family and its covering property are explicit inputs here. -/
theorem completionGraph_surjection (O : ZFSet.{u}) (f : O → S.Name) (A X x₀ : S.Name)
    (hinv : ∀ g : Γ, ∀ i, g • f i = f i)
    (hf : ∀ i p, ∀ a y z : S.Name, S.App p (f i) a y → S.App p (f i) a z →
      S.atomic.EqF p y z) (p : P) (hx₀ : S.atomic.MemF p x₀ X)
    (hcover : ∀ y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q y X →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ i : O, ∃ a : S.Name,
        S.atomic.MemF s a A ∧ S.App s (f i) a y) :
    S.Forces ![S.completionGraph O f A X x₀ hinv,S.cartesianName A (Name.check O),X]
      p (SetLanguage.surjection 0 1 2) := by
  unfold completionGraph
  refine BinaryRelation.graph_surjection (S.completionRelation O f X x₀)
    (S.cartesianName A (Name.check O)) X
    (S.productSupport A X ⊓ MulAction.stabilizer Γ x₀.val)
    (S.normal.2.2.1 _ _ (S.productSupport_mem A X) x₀.hs.symmetric)
    (fun g hg => S.cartesianName_fixed A (Name.check O) g (Subtype.ext hg.1.1) (Name.smul_check S g O))
    (fun _ hg => Subtype.ext hg.1.2)
    (fun g hg p x y h => S.completionRelation_symmetry O f X x₀ g (hinv g)
      (Subtype.ext hg.1.2) (Subtype.ext hg.2) p x y h) p ?_ ?_ ?_
  · exact fun x q hqp hx => S.completionRelation_total O f A X x₀ hx₀ x hqp hx
  · exact fun q _ x y z => S.completionRelation_unique O f X x₀ hf q x y z
  · intro y q hqp hy r hrq
    obtain ⟨s,hsr,i,a,ha,hf⟩ := hcover y q hqp hy r hrq
    refine ⟨s,hsr,a.opair (Name.check i.val),?_,?_⟩
    · exact (S.opair_mem_cartesianName A (Name.check O) a (Name.check i.val) s).mpr
        ⟨ha,S.check_mem_of_mem i.property s⟩
    · exact S.completionRelation_at O f X x₀ i a y s
        (S.defaultRelation_of_app hf (S.atomic.mem_mono (hsr.trans hrq) hy))

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Presentation -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Single-valuedness uses genuine label separation and the support recorded
in the index. It is proved uniformly for all records. -/
theorem presentationPartial_unique [Uncountable κ] (c : κ → ZFSet.{u})
    (hc : Function.Injective c)
    (X : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (i : PresentationIndex hμ X) (p : Poset M I κ)
    (a y z : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hy : (system hμ).App p (presentationPartial hμ c X i) a y)
    (hz : (system hμ).App p (presentationPartial hμ c X i) a z) :
    (system hμ).atomic.EqF p y z :=
  orbitGraph_unique hμ c hc _ _ i.property a y z p hy hz

/-- Every member is densely reached by one of the presentation's partial
functions. The supporting diagram is chosen below the condition witnessing
membership, rather than presumed to belong to a generic filter. -/
theorem presentationPartial_cover [Infinite I]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u})
    (X y : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hy : (system hμ).atomic.MemF t y X) :
    ∀ q, q ≤ t → ∃ r, r ≤ q ∧ ∃ i : PresentationIndex hμ X,
      ∃ a : (system (M := M) (I := I) (κ := κ) hμ).Name,
        (system hμ).atomic.MemF r a (labelSet (M := M) (I := I) hμ c) ∧
        (system hμ).App r (presentationPartial hμ c X i) a y := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨emb⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨emb⟩⟩
  intro q hqt
  obtain ⟨r,hrq,σ,b,hσ,hrb,hyσ⟩ := S.mem_iff.mp hy q hqt
  let j : Edges X.raw := ⟨(σ.raw,S.code b),hσ⟩
  have hj : X.child j.property = σ := Name.ext rfl
  obtain ⟨J,hJ,hfix⟩ := name_support hμ σ
  obtain ⟨d,hdr⟩ := exists_condition_below r
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through hsize e he d.2 (by rwa [hcard])
  have hs : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ := by
    intro g hg
    exact hfix g ((SupportFilter.mem_Fix _ _).mpr (fun z hz =>
      (SupportFilter.mem_Fix _ _).mp hg z (hcover hz)))
  let i : PresentationIndex hμ X := ⟨(j,p),by simpa only [hj] using hs⟩
  let s : Poset M I κ := (d.1,p)
  have hsd : s ≤ (d : Poset M I κ) := WithTop.coe_le_coe.mpr ⟨le_rfl,⟨e,hp⟩⟩
  have hsr := hsd.trans hdr
  have ha := S.app_mono (WithTop.coe_le_coe.mpr (show (d.1,p) ≤ ((⊤ : CohenForcing.Condition I κ),p) from
      ⟨le_top,le_rfl⟩)) (orbitGraph_app_self hμ c σ p)
  have hi : presentationPartial hμ c X i = orbitGraph hμ c σ p := by
    change orbitGraph hμ c (X.child j.property) p = _
    rw [hj]
  refine ⟨s,hsr.trans hrq,i,label (M := M) hμ c (p 1),label_mem_labelSet hμ c _ s,?_⟩
  rw [hi]
  exact (S.app_congr (S.atomic.eq_refl s _) (S.atomic.eq_refl s _)
    (S.atomic.eq_symm (S.atomic.eq_mono hsr hyσ))).mp ha

/-- The unrestricted-rank presentation theorem. Given a single member of `X`
at a condition, this constructs an actual internal graph forced to surject
from the Cartesian product of the invariant label set with a ground ordinal.
There is no inaccessible cardinal, name-rank bound, or assumed coverage. -/
theorem ordinal_presentation [Infinite I] [Uncountable κ]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (c : κ → ZFSet.{u}) (hc : Function.Injective c)
    (X x₀ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ)
    (hx₀ : (system hμ).atomic.MemF p x₀ X) :
    ∃ η : Ordinal.{u}, ∃ f : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (system hμ).Forces ![f,(system (M := M) (I := I) (κ := κ) hμ).cartesianName
        (labelSet (M := M) (I := I) hμ c) (Name.check η.toZFSet),X]
          p (SetLanguage.surjection 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨η,⟨ε⟩⟩ := exists_ordinal_equiv (PresentationIndex hμ X)
  let f : η.toZFSet → S.Name := fun i => presentationPartial hμ c X (ε i)
  have hinv : ∀ g : Equiv.Perm I, ∀ i, g • f i = f i :=
    fun g i => smul_presentationPartial hμ c X (ε i) g
  have hfun : ∀ i r, ∀ a y z : S.Name, S.App r (f i) a y → S.App r (f i) a z →
      S.atomic.EqF r y z := fun i r a y z => presentationPartial_unique hμ c hc X (ε i) r a y z
  refine ⟨η,S.completionGraph η.toZFSet f (labelSet (M := M) (I := I) hμ c) X x₀ hinv,?_⟩
  apply S.completionGraph_surjection η.toZFSet f _ X x₀ hinv hfun p hx₀
  intro y q _ hy r hrq
  obtain ⟨s,hsr,i,a,ha,hf⟩ := presentationPartial_cover hμ hcard hsize e he c X y q hy r hrq
  refine ⟨s,hsr,ε.symm i,a,ha,?_⟩
  simpa only [f,Equiv.apply_symm_apply] using hf

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ClassFibers
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## LocalList -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
theorem forces_wellorderable {n} (v : Fin n → S.Name) (p : P) (a : Fin n) :
    S.Forces v p (SetLanguage.wellorderable a) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ η : S.Name,
        S.Forces ![η] r (SetLanguage.ordinal 0) ∧
        (∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ J : S.Name,
          S.Forces ![J,v a,η] t (SetLanguage.injection 0 1 2)) := by
  simp only [Forces,SetLanguage.wellorderable,SetLanguage.wellorderableFormula,
    S.atomic.forceFormula_rename S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_ex,ForcingQuotient.AtomicData.forceFormula_conj]
  have hordinal (η : S.Name) (r : P) :
      S.Forces (Fin.snoc (v ∘ ![a]) η) r (SetLanguage.ordinal 1) ↔
      S.Forces ![η] r (SetLanguage.ordinal 0) := by
    simp only [Forces,SetLanguage.ordinal,SetLanguage.transitiveSet,
      SetLanguage.membershipLinear,SetLanguage.membershipWellFounded,
      S.atomic.forceFormula_rename S.atomic_regular,
      ForcingQuotient.AtomicData.forceFormula_conj]
    have hv : (Fin.snoc (v ∘ ![a]) η) ∘ ![1] = ![η] ∘ ![0] := by
      funext i
      fin_cases i
      rfl
    rw [hv]
  have hinjection (η J : S.Name) (t : P) :
      S.Forces (Fin.snoc (Fin.snoc (v ∘ ![a]) η) J) t (SetLanguage.injection 2 0 1) ↔
      S.Forces ![J,v a,η] t (SetLanguage.injection 0 1 2) := by
    simp only [Forces,SetLanguage.injection,S.atomic.forceFormula_rename S.atomic_regular]
    have hv : (Fin.snoc (Fin.snoc (v ∘ ![a]) η) J) ∘ ![2,0,1] =
        ![J,v a,η] ∘ ![0,1,2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  simpa only [Forces] using (show (∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ η : S.Name,
      S.Forces (Fin.snoc (v ∘ ![a]) η) r (SetLanguage.ordinal 1) ∧
      (∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ J : S.Name,
        S.Forces (Fin.snoc (Fin.snoc (v ∘ ![a]) η) J) t (SetLanguage.injection 2 0 1))) ↔ _ from by
    simp only [hordinal,hinjection])

/-- Injecting a set into a checked ordinal is enough for the genuine
wellorderability formula. No ordinal preservation assumption is used. -/
theorem wellorderable_of_check_injection (Y J : S.Name) (α : Ordinal.{u}) (p : P)
    (h : S.Forces ![J,Y,Name.check α.toZFSet] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![Y] p (SetLanguage.wellorderable 0) := by
  rw [S.forces_wellorderable]
  intro q hqp
  exact ⟨q,le_rfl,Name.check α.toZFSet,S.forces_checkOrdinal α q,
    fun r hrq => ⟨r,le_rfl,J,S.atomic.forceFormula_mono (hrq.trans hqp) h⟩⟩

theorem no_check_injection_of_not_wellorderable (Y : S.Name) (p : P)
    (h : S.Forces ![Y] p (SetLanguage.wellorderable 0).neg) (α : Ordinal.{u}) :
    ∀ q, q ≤ p → ∀ J : S.Name,
      ¬ S.Forces ![J,Y,Name.check α.toZFSet] q (SetLanguage.injection 0 1 2) := by
  intro q hqp J hj
  exact (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mp h q hqp
    (S.wellorderable_of_check_injection Y J α q hj)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

theorem mem_quotientName (E y : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Poset M I κ) :
    (system hμ).atomic.MemF p y (quotientName hμ c E) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j : I,
        (system hμ).atomic.EqF r y (labelClass hμ c E j) := by
  rw [quotientName,(system hμ).mem_collect]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,j,_,_,_,he⟩ := h q hqp
    exact ⟨r,hrq,j,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,j,he⟩ := h q hqp
    exact ⟨r,hrq,j,r,trivial,le_rfl,he⟩

/-- Membership is exactly the first-order class predicate, not a quotient
surrogate supplied with the desired comparison property. -/
theorem mem_quotientName_iff_isClass
    (E y : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system hμ).atomic.MemF p y (quotientName hμ c E) ↔
      (system hμ).Forces ![y,labelSet hμ c,E] p (SetLanguage.isClass 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  rw [mem_quotientName,S.forces_isClass]
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,j,he⟩ := h q hqp
    exact ⟨r,hrq,label hμ c j,label_mem_labelSet hμ c j r,he⟩
  · intro h q hqp
    obtain ⟨r,hrq,x,hx,he⟩ := h q hqp
    obtain ⟨s,hsr,j,hxj⟩ := (mem_labelSet hμ c x r).mp hx r le_rfl
    exact ⟨s,hsr.trans hrq,j,S.atomic.eq_trans (S.atomic.eq_mono hsr he)
      (S.relationClass_congr (S.atomic.eq_refl s _) (S.atomic.eq_refl s _) hxj)⟩

theorem localList_fixed (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (π : Equiv.Perm I) (hπ : π ∈ SupportFilter.Fix r.range) :
    π • localList hμ c hcard r = localList hμ c hcard r := by
  unfold localList
  exact (system (M := M) (I := I) (κ := κ) hμ).uniformRange_fixed (ι := (localListOrdinal hμ c r).toZFSet)
    (localListEntry hμ c r) (SupportFilter.Fix r.range)
    (localList_support (κ := κ) hμ hcard r) (localListEntry_fixed hμ c r) π hπ

theorem mem_localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (y : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Poset M I κ) :
    (system hμ).atomic.MemF p y (localList hμ c hcard r) ↔
      ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ ν : LocalName hμ c r,
        (system hμ).atomic.EqF s y ν.name := by
  unfold localList
  rw [(system (M := M) (I := I) (κ := κ) hμ).mem_uniformRange]
  constructor
  · intro h q hqp
    obtain ⟨s,hsq,i,he⟩ := h q hqp
    exact ⟨s,hsq,localListEquiv hμ c r i,he⟩
  · intro h q hqp
    obtain ⟨s,hsq,ν,he⟩ := h q hqp
    obtain ⟨i,rfl⟩ := (localListEquiv hμ c r).surjective ν
    exact ⟨s,hsq,i,he⟩

theorem localName_mem_localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (ν : LocalName hμ c r) (p : Poset M I κ) :
    (system hμ).atomic.MemF p ν.name (localList hμ c hcard r) :=
  (mem_localList hμ c hcard r ν.name p).mpr
    (fun q _ => ⟨q,le_rfl,ν,(system hμ).atomic.eq_refl q ν.name⟩)

/-- Nonwellorderability supplies densely an actual E-class outside every
value on the local evaluation list. Nonmembership persists below the chosen
condition; it is not just a failure to decide membership. -/
theorem outside_localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (p : Poset M I κ)
    (hno : (system hμ).Forces ![quotientName hμ c E] p (SetLanguage.wellorderable 0).neg) :
    ∀ q, q ≤ p → ∃ s, s ≤ q ∧ ∃ y : (system hμ).Name,
      (system hμ).atomic.MemF s y (quotientName hμ c E) ∧
      ∀ t, t ≤ s → ¬ (system hμ).atomic.MemF t y (localList hμ c hcard r) := by
  apply (system (M := M) (I := I) (κ := κ) hμ).outside_uniformRange
    (localListOrdinal hμ c r).toZFSet (localListEntry hμ c r)
    (quotientName hμ c E) (SupportFilter.Fix r.range)
    (localList_support (κ := κ) hμ hcard r) (localListEntry_fixed hμ c r)
    (fun π hπ => quotientName_fixed hμ c E π (hE π hπ)) p
  exact (system (M := M) (I := I) (κ := κ) hμ).no_check_injection_of_not_wellorderable
    _ p hno (localListOrdinal hμ c r)

end
end PartitionConsistency.ProductForcing


/-! ## OutsideClass -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- This is a local dense-set theorem derived from nonwellorderability, not
an additional assumption that the unavailable class exists. -/
theorem outsideClassSet_denseBelow [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e*x))ᶜ : Set M) = Cardinal.mk M)
    (p : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix p.range, π • E = E)
    (d₀ : CohenForcing.Condition I κ)
    (hno : (system hμ).Forces ![quotientName hμ c E] ((d₀,p) : Poset M I κ)
      (SetLanguage.wellorderable 0).neg) :
    ∀ d, d ≤ d₀ → ∃ a, a ≤ d ∧ a ∈ outsideClassSet hμ c hcard p E := by
  intro d hdd
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨s,hs,y,hy,hout⟩ := outside_localList hμ c hcard p E hE _ hno
    ((d,p) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hdd,le_rfl⟩)
  obtain ⟨u,hus,j,hyj⟩ := (mem_quotientName hμ c E y s).mp hy s le_rfl
  let : Nonempty (Diagram M I) := ⟨p⟩
  obtain ⟨a,hau⟩ := exists_condition_below u
  have hap := WithTop.coe_le_coe.mp ((hau.trans hus).trans hs)
  have hU : Cardinal.mk ↥(a.1.support ∪ {j}) ≤ Cardinal.mk M := by
    apply (Cardinal.mk_union_le _ _).trans
    have hω := Cardinal.aleph0_le_mk M
    apply (add_le_add (a.1.cardinal_support.trans hω) ?_).trans_eq (Cardinal.add_eq_self hω)
    simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hω
  obtain ⟨t,hta,hcover⟩ := Diagram.extend_through hsize e he a.2 hU
  have hta' : t ≤ a.2 := ⟨e,hta⟩
  have htu : ((a.1,t) : Poset M I κ) ≤ u :=
    (WithTop.coe_le_coe.mpr (show (a.1,t) ≤ a from ⟨le_rfl,hta'⟩)).trans hau
  have hts := htu.trans hus
  have hjt : j ∈ t.range := hcover (Or.inr (Set.mem_singleton j))
  have hnot : ∀ z : Poset M I κ, z ≤ (a.1,t) →
      ¬ S.atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard p) := by
    intro z hzt hz
    apply hout z (hzt.trans hts)
    exact (S.atomic.mem_congr (S.atomic.eq_mono (hzt.trans htu) hyj)
      (S.atomic.eq_refl z _)).mpr hz
  obtain ⟨b,hb⟩ := hta'.trans hap.2
  have hbn : b ≠ 1 := by
    intro h
    have htp : t = p := by simpa only [h,Diagram.sub_one] using hb
    have hjp : j ∈ p.range := htp ▸ hjt
    exact hnot (a.1,t) le_rfl
      (localName_mem_localList hμ c hcard p (localLabelClass hμ c p E hE j hjp) (a.1,t))
  exact ⟨a.1,hap.1,t,b,hb,hbn,fun k hk => hcover (Or.inl hk),j,hjt,hnot⟩

end
end PartitionConsistency.ProductForcing


/-! ## ClassFiber -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- A class outside the full evaluation list cannot be the inclusion of
any local quotient element at that root. Only membership of its witnessing
condition in the filter is used here. -/
theorem outsideLocal_not_image (hcard : Cardinal.mk M ≤ μ)
    (F : GenericFilter (CohenForcing.Condition I κ)) (p s : Diagram M I)
    (hsp : s ≤ p) (d : CohenForcing.Condition I κ) (hd : d ∈ F)
    (σ : LocalName hμ c s) (hout : OutsideLocal hμ c hcard p s d σ)
    (x : LocalQuotient (c := c) hμ F p) :
    LocalQuotient.restrict F hsp x ≠ LocalQuotient.ofName F σ := by
  induction x using Quotient.inductionOn with
  | h τ =>
    intro he
    obtain ⟨a,ha,heq⟩ := (LocalQuotient.ofName_eq F (τ.restrict hsp) σ).mp he
    obtain ⟨b,hb,hbd,hba⟩ := F.directed _ hd _ ha
    have hσ : (system hμ).atomic.EqF ((OrderDual.ofDual b,s) : Poset M I κ)
        σ.name τ.name := (system hμ).atomic.eq_symm
      ((system hμ).atomic.eq_mono
        (p := ((OrderDual.ofDual a,s) : Poset M I κ))
        (q := ((OrderDual.ofDual b,s) : Poset M I κ))
        (WithTop.coe_le_coe.mpr ⟨hba,le_rfl⟩) heq)
    apply hout (OrderDual.ofDual b,s) (WithTop.coe_le_coe.mpr ⟨hbd,le_rfl⟩)
    exact ((system hμ).atomic.mem_congr hσ ((system hμ).atomic.eq_refl _ _)).mpr
      (localName_mem_localList hμ c hcard p τ (OrderDual.ofDual b,s))

/-- Support descent over an exact intersection prevents an outside class
from equaling any element supported by the other diagram. -/
theorem outsideLocal_not_equal [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (d : CohenForcing.Condition I κ) (hd : d ∈ F) (σ : LocalName hμ c s₀)
    (hout : OutsideLocal hμ c hcard p s₀ d σ)
    (y : LocalQuotient (c := c) hμ F s₁) :
    LocalQuotient.restrict F hv₀ (LocalQuotient.ofName F σ) ≠
      LocalQuotient.restrict F hv₁ y := by
  intro he
  obtain ⟨x,hx,_⟩ := LocalQuotient.intersection F hcard hsize hmerger
    p s₀ s₁ v hs₀ hs₁ hinter hv₀ hv₁ (LocalQuotient.ofName F σ) y he
  exact outsideLocal_not_image hμ c hcard F p s₀ hs₀ d hd σ hout x hx

/-- The exact profile for a class on one probe. The positive availability
comes from retaining the name on larger ranges; the negative test is the
actual support-descent contradiction, not a multiplicity assumption. -/
theorem classFromLocal_profile [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q r p : Diagram M I) (a e m b : M) (hqa : r.sub a = q)
    (hp : r.sub (a*e) = p) (hmb : m*b = a*e)
    (U : ConeIdeal (show LeftDivOrder M from a))
    (hm : ∀ n : M, n ∣ a ∧ n ∣ m ↔ n ∈ U.carrier)
    (hinter : ∀ n : M, n ∣ a → n ∉ U.carrier →
      ∀ z : M, n ∣ z ∧ m ∣ z ↔ a*e ∣ z)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (σ : LocalName hμ c (r.sub m)) (hσ : EligibleName hμ c F (r.sub m) E σ)
    (d : CohenForcing.Condition I κ) (hd : d ∈ F)
    (hout : OutsideLocal hμ c hcard p (r.sub m) d σ) :
    (eligibleSystem hμ c hcard hsize hmerger F q E hE).availability r a
      (classFromLocal hμ c hcard hsize hmerger F q r (r.sub m)
        ⟨a,hqa⟩ (r.self_le_sub m) E hE σ hσ) = U := by
  let D := eligibleSystem hμ c hcard hsize hmerger F q E hE
  let x := classFromLocal hμ c hcard hsize hmerger F q r (r.sub m)
    ⟨a,hqa⟩ (r.self_le_sub m) E hE σ hσ
  have hmp : r.sub m ≤ p := ⟨b,by rw [Diagram.sub_sub,hmb,hp]⟩
  apply ConeIdeal.ext
  ext n
  change (n ≤ a ∧ D.Available r x n) ↔ n ∈ U.carrier
  constructor
  · rintro ⟨hna,y,hy⟩
    by_contra hnu
    have hnp : r.sub n ≤ p := by
      rw [← hp]
      exact r.sub_mono (hna.trans (LeftDivOrder.le_mul_right a e))
    have hi : (r.sub m).range ∩ (r.sub n).range = p.range := by
      rw [Set.inter_comm,← hp]
      exact r.range_inter_sub n m (a*e) (hinter n ((LeftDivOrder.le_iff_dvd _ _).mp hna) hnu)
    apply outsideLocal_not_equal hμ c hcard hsize hmerger F p (r.sub m) (r.sub n) r
      hmp hnp hi (r.self_le_sub _) (r.self_le_sub _) d hd σ hout y.val
    exact (congrArg Subtype.val hy).symm
  · intro hnu
    have hh := (hm n).mpr hnu
    have hna : n ≤ (a : LeftDivOrder M) := (LeftDivOrder.le_iff_dvd _ _).mpr hh.1
    have hnm : n ≤ (m : LeftDivOrder M) := (LeftDivOrder.le_iff_dvd _ _).mpr hh.2
    have hnq : r.sub n ≤ q := hqa ▸ r.sub_mono hna
    let y := classFromLocal hμ c hcard hsize hmerger F q (r.sub n) (r.sub m)
      hnq (r.sub_mono hnm) E hE σ hσ
    refine ⟨hna,y,?_⟩
    apply Subtype.ext
    exact LocalQuotient.restrict_restrict F (r.sub_mono hnm) (r.self_le_sub n)
      (LocalQuotient.ofName F σ)

/-- Transport the actual outside label-class witness to all copies of its
diagram over p. The names remain normalized names in the stated local sets,
and their exclusions are forced at the transported conditions. -/
theorem outsideClass_copies (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (p r : Diagram M I) (a e b : M)
    (hp : r.sub (a*e) = p) {K : Type u} (m : K → M) (hm : ∀ i, m i*b = a*e)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix p.range, π • E = E)
    (t : Diagram M I) (ht : t.sub b = p)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : Poset M I κ, z ≤ (d,t) →
      ¬ (system hμ).atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard p)) :
    ∃ (d' : K → CohenForcing.Condition I κ) (σ : ∀ i, LocalName hμ c (r.sub (m i))),
      (∀ i, (d' i).support ⊆ (r.sub (m i)).range) ∧
      (∀ i, (d' i).restrict p.range = d.restrict p.range) ∧
      (∀ i z, (system hμ).Forces ![(σ i).name,labelSet hμ c,E] z (SetLanguage.isClass 0 1 2)) ∧
      ∀ i, OutsideLocal hμ c hcard p (r.sub (m i)) (d' i) (σ i) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hroots (i : K) : (r.sub (m i)).sub b = p := by rw [Diagram.sub_sub,hm i,hp]
  choose π hπ hfix using fun i : K =>
    Diagram.permutation_over_root hsize t (r.sub (m i)) p b ht (hroots i)
  have hip (i : K) : r.sub (m i) ≤ p := ⟨b,hroots i⟩
  have jmem (i : K) : π i j ∈ (r.sub (m i)).range := by
    rw [← hπ i,Diagram.range_permute]
    exact Set.mem_image_of_mem (π i) hj
  let σ (i : K) := localLabelClass hμ c (r.sub (m i)) E
    (supported_mono hμ (hip i) E hE) (π i j) (jmem i)
  refine ⟨fun i => d.permute (π i),σ,?_,?_,?_,?_⟩
  · intro i
    rw [CohenForcing.Condition.support_permute,← hπ i,Diagram.range_permute]
    exact Set.image_mono hd
  · intro i
    exact CohenForcing.Condition.restrict_permute_of_fixes _ _ (hfix i)
  · intro i z
    exact forces_localLabelClass_isClass hμ c _ E _ _ _ z
  · intro i z hz hzmem
    have hπp : π i ∈ SupportFilter.Fix p.range := (SupportFilter.mem_Fix _ _).mpr (hfix i)
    have he : π i • E = E := hE _ hπp
    have hn : π i • labelClass hμ c E j = (σ i).name := by
      change π i • labelClass hμ c E j = labelClass hμ c E (π i j)
      rw [labelClass_move,he]
    have hl : π i • localList hμ c hcard p = localList hμ c hcard p :=
      localList_fixed hμ c hcard p (π i) hπp
    have hmove : S.move (π i) ((d,t) : Poset M I κ) = (d.permute (π i),r.sub (m i)) := by
      rw [move_coe]
      change ((d.permute (π i),t.permute (π i)) : Poset M I κ) = _
      rw [hπ i]
    apply hout ((S.move (π i)).symm z)
    · apply (S.move (π i)).le_iff_le.mp
      rw [OrderIso.apply_symm_apply,hmove]
      exact hz
    · apply (S.mem_symmetry (π i) ((S.move (π i)).symm z) _ _).mpr
      rw [OrderIso.apply_symm_apply,hn,hl]
      exact hzmem

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalChoice
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConcreteSystem.instNonemptyκ _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.System.fiberSmall _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_glued_small _root_.OAI.PartitionConsistency.ProductForcing.eligibleSystem_obj_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Antichain -/

namespace PartitionConsistency.ForcingQuotient
universe u
noncomputable section
variable {P : Type u} [Preorder P]

/-- Every set of forcing conditions has a maximal incompatible subfamily.
The conclusion is predensity in that set; no cardinal chain condition is used. -/
theorem maximal_antichain (D : Set P) :
    ∃ A : Set P, A ⊆ D ∧
      (∀ p ∈ A, ∀ q ∈ A, ∀ r, r ≤ p → r ≤ q → p = q) ∧
      ∀ d ∈ D, ∃ a ∈ A, ∃ r, r ≤ d ∧ r ≤ a := by
  classical
  let C : Set (Set P) := {A | A ⊆ D ∧
    ∀ p ∈ A, ∀ q ∈ A, ∀ r, r ≤ p → r ≤ q → p = q}
  obtain ⟨A,hA,hmax⟩ := zorn_subset C (by
    intro c hc hchain
    refine ⟨⋃₀ c,⟨?_,?_⟩,fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro p ⟨B,hB,hpB⟩
      exact (hc hB).1 hpB
    · rintro p ⟨B,hB,hpB⟩ q ⟨C,hC,hqC⟩ r hrp hrq
      rcases hchain.total hB hC with hBC | hCB
      · exact (hc hC).2 p (hBC hpB) q hqC r hrp hrq
      · exact (hc hB).2 p hpB q (hCB hqC) r hrp hrq)
  refine ⟨A,hA.1,hA.2,?_⟩
  intro d hd
  by_contra hn
  have hdA : d ∉ A := by
    intro h
    exact hn ⟨d,h,d,le_rfl,le_rfl⟩
  have hi : insert d A ∈ C := by
    refine ⟨Set.insert_subset hd hA.1,?_⟩
    intro p hp q hq r hrp hrq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact False.elim (hn ⟨q,hq,r,hrp,hrq⟩)
    · exact False.elim (hn ⟨p,hp,r,hrq,hrp⟩)
    · exact hA.2 p hp q hq r hrp hrq
  exact hdA (hmax hi (Set.subset_insert _ _) (Set.mem_insert _ _))

end
end PartitionConsistency.ForcingQuotient


/-! ## Maximum -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ K : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The local maximum principle furnished by root probes. Unlike the ordinary
maximum principle, the conclusion has a specified literal supporting diagram,
chosen before the witness. The name is a mixture over a Cohen antichain. -/
theorem localized_maximum [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K)
    {n} (φ : Formula (n+1)) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q : Diagram M I) (hq : q.sub e = p)
    (hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ q.range)
    (hf : (system hμ).Forces v ((d₀,p) : Poset M I κ) φ.ex) :
    ∃ ν : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      (system hμ).Forces (Fin.snoc v ν) ((d₀,q) : Poset M I κ) φ := by
  classical
  let S := system (M := M) (I := I) (κ := κ) hμ
  have : Nonempty (Diagram M I) := ⟨p⟩
  let D : Set (CohenForcing.Condition I κ) := {a | a ≤ d₀ ∧ a.support ⊆ q.range ∧
    ∃ ν : S.Name, (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      S.Forces (Fin.snoc v ν) ((a,q) : Poset M I κ) φ}
  obtain ⟨A,hAD,hanti,hpred⟩ := ForcingQuotient.maximal_antichain D
  have hchoose : ∀ a : A, ∃ ν : S.Name,
      (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      S.Forces (Fin.snoc v ν) ((a.val,q) : Poset M I κ) φ :=
    fun a => (hAD a.property).2.2
  choose f hfix hforce using hchoose
  let act : A → Poset M I κ := fun a => ((a.val,q) : Condition M I κ)
  let H := SupportFilter.Fix q.range
  have hH : H ∈ S.filter := ⟨q.range,by rw [Diagram.cardinal_range,hcard],le_rfl⟩
  have hact : ∀ π ∈ H, ∀ a, S.move π (act a) = act a := by
    intro π hπ a
    have hfixπ := (SupportFilter.mem_Fix _ _).mp hπ
    change S.move π ((a.val,q) : Poset M I κ) = ((a.val,q) : Poset M I κ)
    rw [move_coe]
    apply congrArg WithTop.some
    apply Prod.ext
    · exact CohenForcing.Condition.permute_eq_of_fixes_support π a.val
        (fun j hj => hfixπ j ((hAD a.property).2.1 hj))
    · exact Diagram.permute_eq_of_fixes_range π q hfixπ
  have hcoh : ∀ i j r, r ≤ act i → r ≤ act j → S.atomic.EqF r (f i) (f j) := by
    intro i j r hri hrj
    obtain ⟨r₀,hr₀⟩ := exists_condition_below r
    have hij : i = j := Subtype.ext (hanti _ i.property _ j.property r₀.1
      (WithTop.coe_le_coe.mp (hr₀.trans hri)).1
      (WithTop.coe_le_coe.mp (hr₀.trans hrj)).1)
    subst j
    exact S.atomic.eq_refl _ _
  let ν := S.mix f act H hH (fun π hπ a => hfix a π hπ) hact
  refine ⟨ν,S.mix_fixed f act H hH _ hact,?_⟩
  apply S.atomic.forceFormula_of_dense S.atomic_regular
  intro t ht
  obtain ⟨t₀,ht₀⟩ := exists_condition_below t
  have htd : t₀.1 ≤ d₀ := (WithTop.coe_le_coe.mp (ht₀.trans ht)).1
  have htq : t₀.2 ≤ q := (WithTop.coe_le_coe.mp (ht₀.trans ht)).2
  let c := t₀.1.restrict q.range
  have hcd : c ≤ d₀ := by
    intro z hz
    exact ⟨htd hz,hd₀ ((CohenForcing.Condition.mem_support _ _).mpr ⟨z.1.2,z.2,hz⟩)⟩
  obtain ⟨d,hdc,hds,νd,hfixd,hforced⟩ := localized_existential hμ hcard hsize hmerger e he hprobes
    φ v p q hq hv d₀ hf c hcd (t₀.1.support_restrict_subset _)
  have hdD : d ∈ D := ⟨hdc.trans hcd,hds,νd,hfixd,hforced⟩
  obtain ⟨a,ha,b,hbd,hba⟩ := hpred d hdD
  let b' := b.restrict q.range
  have hbc : b' ≤ c := by
    intro z hz
    exact ⟨hbd (hdc hz),hz.2⟩
  have hba' : b' ≤ a := by
    intro z hz
    exact ⟨hba hz,(hAD ha).2.1 ((CohenForcing.Condition.mem_support _ _).mpr ⟨z.1.2,z.2,hz⟩)⟩
  have htcomp : CohenForcing.Condition.Compatible t₀.1 b' := by
    intro z x y hx hy
    exact b'.functional z x y (hbc ⟨hx,hy.2⟩) hy
  obtain ⟨s,hst,hsb⟩ := CohenForcing.Condition.compatible_iff.mp htcomp
  let a' : A := ⟨a,ha⟩
  have hsa : ((s,t₀.2) : Poset M I κ) ≤ act a' :=
    WithTop.coe_le_coe.mpr ⟨hsb.trans hba',htq⟩
  have heq := S.atomic.eq_mono hsa (S.eq_mix_at f act H hH (fun π hπ a => hfix a π hπ) hact hcoh a')
  refine ⟨((s,t₀.2) : Poset M I κ),
    (WithTop.coe_le_coe.mpr (show (s,t₀.2) ≤ t₀ from ⟨hst,le_rfl⟩)).trans ht₀,?_⟩
  exact (S.forces_snoc_congr φ v heq).mpr (S.atomic.forceFormula_mono hsa (hforce a'))

end
end PartitionConsistency.ProductForcing


/-! ## ChoiceFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_nonemptyFamily {n} (v : Fin n → S.Name) (p : P) (F d : Fin n) :
    S.Forces v p (SetLanguage.nonemptyFamily F d) ↔
      S.Forces ![v F,v d] p (SetLanguage.functionOn 0 1) ∧
      ∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v d) →
        ∀ r, r ≤ q → S.App r (v F) x y →
          ∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ z : S.Name, S.atomic.MemF t z y := by
  simp only [Forces,SetLanguage.nonemptyFamily,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_edge,S.forces_nonempty]
  have hv : v ∘ ![F,d] = ![v F,v d] := by
    ext i
    fin_cases i <;> rfl
  simp [hv,Fin.snoc]

theorem forces_choiceForFamily {n} (v : Fin n → S.Name) (p : P) (c d F : Fin n) :
    S.Forces v p (SetLanguage.choiceForFamily c d F) ↔
      S.Forces ![v c,v d] p (SetLanguage.functionOn 0 1) ∧
      ∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v d) →
        ∀ r, r ≤ q → S.App r (v F) x y →
          ∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ z : S.Name,
            S.App t (v c) x z ∧ S.atomic.MemF t z y := by
  simp only [Forces,SetLanguage.choiceForFamily,S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular,S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    ForcingQuotient.AtomicData.forceFormula_ex,S.forces_edge]
  have hv : v ∘ ![c,d,F] = ![v c,v d,v F] := by
    ext i
    fin_cases i <;> rfl
  have hfun : S.atomic.ForceFormula ![v c,v d,v F] p (SetLanguage.functionOn 0 1) ↔
      S.atomic.ForceFormula ![v c,v d] p (SetLanguage.functionOn 0 1) := by
    simp only [SetLanguage.functionOn,S.atomic.forceFormula_rename S.atomic_regular]
    have hc : ![v c,v d,v F] ∘ ![0,1] = ![v c,v d] ∘ ![0,1] := by
      ext i
      fin_cases i <;> rfl
    rw [hc]
  simpa [hv,Fin.snoc,Fin.castPred,Fin.castLT] using
    and_congr hfun (Iff.rfl :
      (∀ x y : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x (v d) →
        ∀ r, r ≤ q → S.App r (v F) x y →
          ∀ s, s ≤ r → ∃ t, t ≤ s ∧ ∃ z : S.Name,
            S.App t (v c) x z ∧ S.atomic.MemF t z y) ↔ _)

theorem forces_familyMember (F x z : S.Name) (p : P) :
    S.Forces ![F,x,z] p SetLanguage.familyMember ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name,
        S.App r F x y ∧ S.atomic.MemF r z y := by
  simp only [Forces,SetLanguage.familyMember,ForcingQuotient.AtomicData.forceFormula_ex,
    ForcingQuotient.AtomicData.forceFormula_conj,ForcingQuotient.AtomicData.forceFormula_mem,
    S.forces_edge]
  rfl

/-- A member of the domain of a forced nonempty family has a possible
choice value. Both the family's set value and the member are internal names. -/
theorem nonemptyFamily_member {n} (v : Fin n → S.Name) (p : P) (F d : Fin n)
    (hf : S.Forces v p (SetLanguage.nonemptyFamily F d)) (x : S.Name)
    (hx : S.atomic.MemF p x (v d)) :
    S.Forces ![v F,x] p SetLanguage.familyMember.ex := by
  obtain ⟨hfun,hne⟩ := (S.forces_nonemptyFamily v p F d).mp hf
  intro q hqp
  obtain ⟨r,hrq,y,ha,_⟩ := S.functionOn_total ![v F,v d] p 0 1 hfun x le_rfl hx q hqp
  obtain ⟨s,hsr,z,hz⟩ := hne x y p le_rfl hx r (hrq.trans hqp) ha r le_rfl
  refine ⟨s,hsr.trans hrq,z,?_⟩
  have hvec : Fin.snoc ![v F,x] z = ![v F,x,z] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  exact (S.forces_familyMember _ _ _ _).mpr (fun t hts =>
    ⟨t,le_rfl,y,S.app_mono (hts.trans hsr) ha,S.atomic.mem_mono hts hz⟩)

/-- Once the family's value at an index is specified, a selected member
belongs to that value. This uses single-valuedness of the actual graph. -/
theorem familyMember_mem {n} (v : Fin n → S.Name) (p : P) (F d : Fin n)
    (hfun : S.Forces v p (SetLanguage.functionOn F d)) (x y z : S.Name)
    (hx : S.atomic.MemF p x (v d)) (ha : S.App p (v F) x y)
    (hz : S.Forces ![v F,x,z] p SetLanguage.familyMember) : S.atomic.MemF p z y := by
  apply S.atomic_regular.2
  intro q hqp
  obtain ⟨r,hrq,t,hat,hzt⟩ := (S.forces_familyMember _ _ _ _).mp hz q hqp
  have he := S.functionOn_unique v r F d (S.atomic.forceFormula_mono (hrq.trans hqp) hfun)
    x t y (S.atomic.mem_mono (hrq.trans hqp) hx) hat (S.app_mono (hrq.trans hqp) ha)
  exact ⟨r,hrq,(S.atomic.mem_congr (S.atomic.eq_refl r z) he).mp hzt⟩

/-- The ordinary first-order ACwo sentence follows from dense internal
choice graphs. This is only a logical unpacking, with the ordinal and all
family hypotheses unchanged. -/
theorem forces_ACwo_of_dense
    (h : ∀ (p : P) (η F : S.Name),
      S.Forces ![η] p (SetLanguage.ordinal 0) →
      S.Forces ![F,η] p (SetLanguage.nonemptyFamily 0 1) →
      ∃ q, q ≤ p ∧ ∃ c : S.Name,
        S.Forces ![c,η,F] q (SetLanguage.choiceForFamily 0 1 2)) (p : P) :
    S.Forces Fin.elim0 p SetLanguage.ACwo := by
  change S.atomic.ForceFormula Fin.elim0 p SetLanguage.ACwo
  rw [SetLanguage.ACwo,S.atomic.forceFormula_all S.atomic_regular]
  intro η
  have hη : Fin.snoc (Fin.elim0 : Fin 0 → S.Name) η = ![η] := by
    ext i
    fin_cases i
    rfl
  rw [hη]
  rw [S.atomic.forceFormula_imp S.atomic_regular]
  intro q hqp ho
  rw [S.atomic.forceFormula_all S.atomic_regular]
  intro F
  have hF : Fin.snoc ![η] F = ![η,F] := by
    ext i
    fin_cases i <;> rfl
  rw [hF]
  rw [S.atomic.forceFormula_imp S.atomic_regular]
  intro r hrq hf
  have hf' : S.Forces ![F,η] r (SetLanguage.nonemptyFamily 0 1) :=
    (S.forces_nonemptyFamily ![F,η] r 0 1).mpr
      ((S.forces_nonemptyFamily ![η,F] r 1 0).mp hf)
  intro s hsr
  obtain ⟨t,hts,c,hc⟩ := h s η F (S.atomic.forceFormula_mono (hsr.trans hrq) ho)
    (S.atomic.forceFormula_mono hsr hf')
  refine ⟨t,hts,c,?_⟩
  have hcvec : Fin.snoc ![η,F] c = ![η,F,c] := by
    ext i
    fin_cases i <;> rfl
  rw [hcvec]
  exact (S.forces_choiceForFamily ![η,F,c] t 2 0 1).mpr
    ((S.forces_choiceForFamily ![c,η,F] t 0 1 2).mp hc)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Uniformly supported local choices yield an actual internal set function,
not an external function substituted for the conclusion of ACwo. -/
theorem indexedGraph_choiceForFamily (X : ZFSet.{u}) (F : S.Name)
    (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (p : P)
    (hfun : S.Forces ![F,Name.check X] p (SetLanguage.functionOn 0 1))
    (hf : ∀ i : X, S.Forces ![F,Name.check i.val,f i] p SetLanguage.familyMember) :
    S.Forces ![S.indexedGraph X f H hH hfix,Name.check X,F] p
      (SetLanguage.choiceForFamily 0 1 2) := by
  apply (S.forces_choiceForFamily _ _ _ _ _).mpr
  refine ⟨S.indexedGraph_functionOn X f H hH hfix p,?_⟩
  intro x y q hqp hx r hrq ha s hsr
  obtain ⟨t,hts,i,hi,heq⟩ := (S.mem_check X x q).mp hx s (hsr.trans hrq)
  let j : X := ⟨i,hi⟩
  have hap : S.App t F (Name.check i) y :=
    (S.app_congr (S.atomic.eq_refl t F) heq (S.atomic.eq_refl t y)).mp
      (S.app_mono (hts.trans hsr) ha)
  have hm := S.familyMember_mem ![F,Name.check X] t 0 1
    (S.atomic.forceFormula_mono (hts.trans (hsr.trans (hrq.trans hqp))) hfun)
    (Name.check i) y (f j) (S.check_mem_of_mem hi t) hap
    (S.atomic.forceFormula_mono (hts.trans (hsr.trans (hrq.trans hqp))) (hf j))
  refine ⟨t,hts,f j,?_,hm⟩
  exact (S.app_congr (S.atomic.eq_refl t _) heq (S.atomic.eq_refl t _)).mpr
    (S.indexedGraph_app_at X f H hH hfix j t)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## ACwo -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ K : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- One previously chosen extension of the supporting diagram supports all
choices from a ground-indexed family, at arbitrary name ranks. The result is
an internal graph; the uniform maximum principle only constructs its name. -/
theorem ground_family_choice [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K) (X : ZFSet.{u})
    (F : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q : Diagram M I) (hq : q.sub e = p)
    (hF : ∀ π ∈ SupportFilter.Fix p.range, π • F = F)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ q.range)
    (hf : (system hμ).Forces ![F,Name.check X] ((d₀,p) : Poset M I κ)
      (SetLanguage.nonemptyFamily 0 1)) :
    ∃ c : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (system hμ).Forces ![c,Name.check X,F] ((d₀,q) : Poset M I κ)
        (SetLanguage.choiceForFamily 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hw (i : X) : ∃ ν : S.Name,
      (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
      S.Forces ![F,Name.check i.val,ν] ((d₀,q) : Poset M I κ) SetLanguage.familyMember := by
    have hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ j : Fin 2,
        π • (![F,Name.check i.val] : Fin 2 → S.Name) j = ![F,Name.check i.val] j := by
      intro π hπ j
      fin_cases j
      · exact hF π hπ
      · exact Name.smul_check S π _
    have hm := S.nonemptyFamily_member ![F,Name.check X] ((d₀,p) : Poset M I κ) 0 1 hf
      (Name.check i.val) (S.check_mem_of_mem i.property _)
    obtain ⟨ν,hν,hforce⟩ := localized_maximum hμ hcard hsize hmerger e he hprobes
      SetLanguage.familyMember ![F,Name.check i.val] p q hq hv d₀ hd₀ hm
    refine ⟨ν,hν,?_⟩
    have hvec : Fin.snoc ![F,Name.check i.val] ν = ![F,Name.check i.val,ν] := by
      ext j
      fin_cases j <;> rfl
    rwa [hvec] at hforce
  choose f hfix hforce using hw
  let H := SupportFilter.Fix q.range
  have hH : H ∈ S.filter := ⟨q.range,by rw [Diagram.cardinal_range,hcard],le_rfl⟩
  have hf' := (S.forces_nonemptyFamily ![F,Name.check X] ((d₀,p) : Poset M I κ) 0 1).mp hf
  exact ⟨S.indexedGraph X f H hH (fun π hπ i => hfix i π hπ),
    S.indexedGraph_choiceForFamily X F f H hH (fun π hπ i => hfix i π hπ) _
      (S.atomic.forceFormula_mono (p := ((d₀,p) : Poset M I κ)) (q := ((d₀,q) : Poset M I κ))
        (WithTop.coe_le_coe.mpr ⟨le_rfl,⟨e,hq⟩⟩) hf'.1) hforce⟩

/-- An arbitrary starting condition for a ground-indexed nonempty family
can be strengthened to force a choice graph. The family's support and the
Cohen condition are both put in the root before using probes. -/
theorem ground_family_choice_dense [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K) (X : ZFSet.{u})
    (F : (system (M := M) (I := I) (κ := κ) hμ).Name) (t : Poset M I κ)
    (hf : (system hμ).Forces ![F,Name.check X] t (SetLanguage.nonemptyFamily 0 1)) :
    ∃ s, s ≤ t ∧ ∃ c : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (system hμ).Forces ![c,Name.check X,F] s (SetLanguage.choiceForFamily 0 1 2) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨emb⟩ := (Cardinal.le_def M I).mp hsize.le
  let : Nonempty (Diagram M I) := ⟨⟨emb⟩⟩
  obtain ⟨d,hdt⟩ := exists_condition_below t
  obtain ⟨J,hJ,hfix⟩ := name_support hμ F
  have hU : Cardinal.mk ↥(J ∪ d.1.support) ≤ Cardinal.mk M := by
    rw [hcard]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (d.1.cardinal_support.trans hμ)).trans_eq (Cardinal.add_eq_self hμ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through hsize e he d.2 hU
  have hpd : ((d.1,p) : Poset M I κ) ≤ t :=
    (WithTop.coe_le_coe.mpr (show (d.1,p) ≤ d from ⟨le_rfl,⟨e,hp⟩⟩)).trans hdt
  obtain ⟨q,hq,_⟩ := Diagram.extend_through hsize e he p (J := ∅) (by simp)
  have hqp : q ≤ p := ⟨e,hq⟩
  obtain ⟨c,hc⟩ := ground_family_choice hμ hcard hsize hmerger e he hprobes X F p q hq
    (fun π hπ => hfix π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (hcover (Or.inl hj)))))
    d.1 (fun j hj => Diagram.range_antitone hqp (hcover (Or.inr hj)))
    (S.atomic.forceFormula_mono hpd hf)
  exact ⟨(d.1,q),(WithTop.coe_le_coe.mpr (show (d.1,q) ≤ (d.1,p) from ⟨le_rfl,hqp⟩)).trans hpd,c,hc⟩

/-- Choice for every internal ordinal-indexed family, without a rank cutoff.
Ordinal preservation first decides the index set to a ground ordinal, after
which one uniformly supported internal choice graph is constructed. -/
theorem forces_ACwo [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K) (p : Poset M I κ) :
    (system (M := M) (I := I) (κ := κ) hμ).Forces Fin.elim0 p SetLanguage.ACwo := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  apply S.forces_ACwo_of_dense
  intro s η F ho hf'
  obtain ⟨t,hts,β,hη⟩ := S.forces_ordinal_decide ![η] s 0 ho s le_rfl
  have hf' := S.atomic.forceFormula_mono hts hf'
  have hchange : S.Forces ![F,Name.check β.toZFSet] t (SetLanguage.nonemptyFamily 0 1) := by
    apply (S.atomic.forceFormula_tuple_congr (p := t) (φ := SetLanguage.nonemptyFamily 0 1)
      (v := ![F,η]) (w := ![F,Name.check β.toZFSet]) ?_).mp hf'
    intro i
    fin_cases i
    · exact S.atomic.eq_refl t F
    · exact hη
  obtain ⟨a,hat,c,hc⟩ := ground_family_choice_dense hμ hcard hsize hmerger e he hprobes
    β.toZFSet F t hchange
  have hc' : S.Forces ![c,η,F] a (SetLanguage.choiceForFamily 0 1 2) := by
    apply (S.atomic.forceFormula_tuple_congr (p := a) (φ := SetLanguage.choiceForFamily 0 1 2)
      (v := ![c,Name.check β.toZFSet,F]) (w := ![c,η,F]) ?_).mp hc
    intro i
    fin_cases i
    · exact S.atomic.eq_refl a c
    · exact S.atomic.eq_symm (S.atomic.eq_mono hat hη)
    · exact S.atomic.eq_refl a F
  exact ⟨a,hat.trans hts,c,hc'⟩

end
end PartitionConsistency.ProductForcing

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
noncomputable section

/-- The probes used by ordinal choice are actually present in the saturated
monoid. This is an instance of the executed requests with `a=1`. -/
theorem rootProbes : ProductForcing.RootProbes T.e K := by
  intro b hb
  let d : ProbeData T :=
    ⟨1,b,hb,⟨fun _ => 1,rfl,fun _ => dvd_refl _,fun _ => dvd_refl _⟩⟩
  obtain ⟨m,_,hm,hi⟩ := Saturation.probes Base.object K d
  refine ⟨m,fun i => (hm i).exit.trans (one_mul _),?_⟩
  intro i j hij z
  have hh := hi i j hij z
  change m i ∣ z ∧ m j ∣ z ↔ (1 : T) * T.e ∣ z at hh
  simpa only [one_mul] using! hh

/-- No additional cardinal or support principle is assumed here. -/
theorem forces_ACwo (p : P) : S.Forces Fin.elim0 p SetLanguage.ACwo :=
  ProductForcing.forces_ACwo aleph0_le_μ cardinal_T size_lt finiteMergers T.e
    complement_cardinal rootProbes p

end
end PartitionConsistency.ConcreteSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_QuotientActions
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SaturatedFibers -/

namespace PartitionConsistency.MonoidConstruction.Saturation
universe u
open DiagramOrder DiagramForcing LocalDiagramSystem
noncomputable section
variable (M : Object.{u}) (K : Type u) [Nonempty K] [Infinite K]

/-- Reindex the actual saturated probes into independently hit rows. This
uses infinitude of the prescribed multiplicity, not a new saturation step. -/
theorem square_ideal_probes (a b : target M K) (hb : b ≠ 1)
    (U : ConeIdeal (α := LeftDivOrder (target M K)) a) :
    ∃ m : K × K → target M K, Function.Injective m ∧
      (∀ i, m i * b = a * (target M K).e ∧ ¬ m i ∣ a ∧
        (∀ x : target M K, x ∣ a ∧ x ∣ m i ↔ x ∈ U.carrier) ∧
        ∀ x : target M K, x ∣ a → x ∉ U.carrier →
          ∀ z : target M K, x ∣ z ∧ m i ∣ z ↔ a * (target M K).e ∣ z) ∧
      ∀ i j, i ≠ j → ∀ z : target M K,
        m i ∣ z ∧ m j ∣ z ↔ a * (target M K).e ∣ z := by
  have hs : Cardinal.mk (K × K) = Cardinal.mk K := by
    rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.mul_eq_self (Cardinal.aleph0_le_mk K)]
  obtain ⟨h⟩ := Cardinal.eq.mp hs
  obtain ⟨m,hinj,hm,hi⟩ := ideal_probes M K a b hb U
  exact ⟨m ∘ h,hinj.comp h.injective,fun i => hm (h i),
    fun i j hij => hi (h i) (h j) (fun he => hij (h.injective he))⟩

end
end PartitionConsistency.MonoidConstruction.Saturation


/-! ## Preliminary -/

/-! A preliminary assignment on the genuine symbolic component with tail
covariance. Exact cardinality at an intermediate filter is an explicit
input here; the issued dense requirements needed to obtain it are in
`SaturatedFibersWork`. No existence of a filter generic over every ambient
set is assumed or asserted. -/


/-! ## ComponentAction -/

/-! The actual symbolic fibers carry transport between moved Cohen filters.
On the total space this is a genuine group action. The individual interpreted
universes are not being treated as if they carried this action internally. -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramForcing DiagramOrder
noncomputable section
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

namespace Vertex
variable {q : Diagram M I} (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q)

theorem Chain.tailFixer_fixes_label (C : Chain v) (k : C.tailFixer hj) (j : labelFiberSet v) :
    k.val • j = j :=
  Subtype.ext (C.tailFixer_fixes_labels hj k j.val j.property)

end Vertex
end
end PartitionConsistency.LocalDiagramSystem


/-! ## CodeCovariance -/

/-! Covariance on actual forcing conditions. The code order is held fixed,
whereas both the Cohen condition and the local supporting vertex move. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

omit [Infinite M] [Infinite I] in
/-- Every one of the shrinking chain diagrams supports the ordinal names,
not just the first diagram. -/
theorem chainFix_le_tailGroup (i : ℕ) :
    SupportFilter.Fix (C.vertex i).diagram.range ≤ tailGroup hj C := by
  intro π hπ
  have hr : (C.vertex i).diagram ≤ q := ⟨(C.vertex i).index,(C.vertex i).root⟩
  have hπq : π ∈ Vertex.RootGroup q := by
    apply (SupportFilter.mem_Fix _ _).mpr
    intro j hj
    exact (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hr hj)
  let g : Vertex.RootGroup q := ⟨π,hπq⟩
  have hg (j : I) (hj : j ∈ (C.vertex i).diagram.range) : g.val j = j :=
    (SupportFilter.mem_Fix _ _).mp hπ j hj
  let k : Vertex.componentStabilizer hj v := ⟨g,C.fixes_mem_stabilizer hj g i hg⟩
  exact (tailGroup_mem hj C π).mpr ⟨⟨k,i,hg⟩,rfl⟩

omit [Infinite M] [Infinite I] in
/-- The same code is linked to the transported name at the moved vertex.
It is not necessary for the permutation to fix the original root. -/
theorem links_permute (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (w : Vertex q) (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (a : ChainCode hμ c C) (h : Links hμ c C d w τ a) :
    Links hμ c C (d.permute k.val.val.val) (k.val.val • w) (k.val.val.val • τ) a := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨L,hL⟩ := tail_fixed hμ c hj C k
  refine ⟨max N L,fun i hi => ?_⟩
  obtain ⟨⟨f⟩,he⟩ := hN i ((le_max_left _ _).trans hi)
  obtain ⟨hv,hn⟩ := hL i ((le_max_right _ _).trans hi)
  refine ⟨?_,?_⟩
  · simpa only [hv] using (show Nonempty ((k.val.val • w).Arrow (k.val.val • C.vertex i)) from
      ⟨f.move k.val.val⟩)
  · simpa only [hn (a i),move_coe,permute,Vertex.smul_diagram] using
      ((system hμ).eq_symmetry k.val.val.val ((d,w.diagram) : Poset M I κ) (a i).name τ).mp he

include c hsize hmerger in
/-- Local decision reflects a tail-invariant equality back from the moved
root. This is the needed covariance of ordinal VALUES, not just names. -/
theorem tail_eq_permute (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (τ σ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hτ : ∀ π ∈ tailGroup hj C, π • τ = τ)
    (hσ : ∀ π ∈ tailGroup hj C, π • σ = σ)
    (he : (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) τ σ) :
    (system hμ).atomic.EqF ((d.permute k.val.val.val,v.diagram) : Poset M I κ) τ σ := by
  obtain ⟨N,hN⟩ := tail_fixed hμ c hj C k
  have hk : k.val.val.val ∈ tailGroup hj C := (tailGroup_mem hj C _).mpr ⟨k,rfl⟩
  have hm : (system hμ).atomic.EqF
      ((d.permute k.val.val.val,(k.val.val • v).diagram) : Poset M I κ) τ σ := by
    simpa only [hτ _ hk,hσ _ hk,move_coe,permute,Vertex.smul_diagram] using
      ((system hμ).eq_symmetry k.val.val.val ((d,v.diagram) : Poset M I κ) τ σ).mp he
  have hf : Nonempty (v.Arrow (C.vertex N)) := by
    simpa only [C.first] using C.increasing 0 N (Nat.zero_le _)
  have hfm : Nonempty ((k.val.val • v).Arrow (C.vertex N)) := by
    simpa only [(hN N le_rfl).1] using
      (show Nonempty ((k.val.val • v).Arrow (k.val.val • C.vertex N)) from ⟨hf.some.move k.val.val⟩)
  have ht := eq_at_root hμ hsize hmerger τ σ (C.vertex N).diagram
    (k.val.val • v).diagram ⟨hfm.some.index,hfm.some.diagram⟩
    (fun π hπ => hτ π (chainFix_le_tailGroup hj C N hπ))
    (fun π hπ => hσ π (chainFix_le_tailGroup hj C N hπ)) (d.permute k.val.val.val) hm
  exact (system hμ).atomic.eq_mono
    (WithTop.coe_le_coe.mpr (show (d.permute k.val.val.val,v.diagram) ≤
      (d.permute k.val.val.val,(C.vertex N).diagram) from
        ⟨le_rfl,⟨hf.some.index,hf.some.diagram⟩⟩)) ht

/-- Both ordinal name constructions are literally fixed by the tail group. -/
theorem ordinalRank_fixed (a : Index hμ c C) (π : Equiv.Perm I) (hπ : π ∈ tailGroup hj C) :
    π • ordinalRank hμ c hcard hsize hmerger hj E hE C a =
      ordinalRank hμ c hcard hsize hmerger hj E hE C a :=
  CohenSelection.rank_fixed hμ _ _ _ _ a π hπ

theorem ordinalType_fixed (π : Equiv.Perm I) (hπ : π ∈ tailGroup hj C) :
    π • ordinalType hμ c hcard hsize hmerger hj E hE C =
      ordinalType hμ c hcard hsize hmerger hj E hE C :=
  CohenSelection.orderType_fixed hμ _ _ _ _ π hπ

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GermSelectors
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## PreAssignment -/

/-! The preliminary component assignment, as a persistent relation on actual
forcing conditions and actual HS names. The ordinal table is fixed once,
and the names for ranks/order types are computed from the persistent least
codes rather than from arbitrary principal-filter wellorders. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "ordT" => ordinalType hμ c hcard hsize hmerger hj E hE C
local notation "ordR" => ordinalRank hμ c hcard hsize hmerger hj E hE C
local notation "Sel" => IsSelected hμ c hcard hsize hmerger hj E hE C
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

variable {hμ c hcard hsize hmerger hj E hE C}

theorem preliminary_mono {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name} (hed : e ≤ d)
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  have hh : ((e,v.diagram) : Poset M I κ) ≤ (d,v.diagram) :=
    WithTop.coe_le_coe.mpr ⟨hed,le_rfl⟩
  exact ⟨θ,hb,hc,a,isSelected_mono hμ c hcard hsize hmerger hj E hE C hed ha,
    (S).atomic.eq_mono hh ht,(S).atomic.eq_mono hh hr,links_mono hed hl⟩

omit [Infinite M] [Infinite I] in
/-- This equality concerns actual forced ordinal values. It is independent
of the enumeration's arbitrary but once-for-all ground choices. -/
private theorem ordinal_value_unique (d : CohenForcing.Condition I κ) (τ : (S).Name)
    {θ ψ : Ordinal.{u}}
    (hθ : (S).atomic.EqF ((d,v.diagram) : Poset M I κ) τ (Name.check θ.toZFSet))
    (hψ : (S).atomic.EqF ((d,v.diagram) : Poset M I κ) τ (Name.check ψ.toZFSet)) : θ = ψ := by
  apply Ordinal.toZFSet_injective
  exact ((S).eq_check_iff _ _ ((d,v.diagram) : Poset M I κ)).mp
    ((S).atomic.eq_trans ((S).atomic.eq_symm hθ) hψ)

/-- Injectivity and single-valuedness together: two assigned values are
forced equal at the local vertex if and only if their ground labels agree. -/
theorem preliminary_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j k : labelFiberSet v} {τ σ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ)
    (h' : Preliminary hμ c hcard hsize hmerger hj E hE C d w k σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = k := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  obtain ⟨ψ,hb',hc',b,hbsel,ht',hr',hl'⟩ := h'
  have heθ := ordinal_value_unique d ordT ht ht'
  subst ψ
  constructor
  · intro he
    have hs := (links_eq_iff_same hsize hmerger hl hl').mp he
    have hab : a = b := (code hμ c C).injective
      (selected_unique hμ c hcard hsize hmerger hj E hE C ha hbsel hs)
    subst b
    have hij := ordinal_value_unique d (ordR a) hr hr'
    exact (OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C)
      θ hb hc).injective (Subtype.ext hij)
  · rintro rfl
    have heq : (S).atomic.EqF ((d,v.diagram) : Poset M I κ) (ordR a) (ordR b) :=
      (S).atomic.eq_trans hr ((S).atomic.eq_symm hr')
    have hab := (ordinalRank_eq_iff hμ c hcard hsize hmerger hj E hE C a b d ha hbsel).mp heq
    subst b
    exact (links_eq_iff_same hsize hmerger hl hl').mpr (same_refl d _)

variable (hμ c hcard hsize hmerger hj E hE C)

/-- Every assigned local representative is eligible and keeps exactly the
vertex's availability ideal at every stronger Cohen condition. -/
theorem preliminary_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : LocalName hμ c w.diagram}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    (S).Forces ![τ.name,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)
      (SetLanguage.isClass 0 1 2) ∧
    ∀ e, e ≤ d → forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index τ = w.ideal := by
  obtain ⟨_,_,_,a,ha,_,_,hl⟩ := h
  exact links_stable hμ c hcard hsize hmerger hj E hE C d (code hμ c C a) ha.1 w τ hl

/-- Restrictions are the canonical identifications in the component. -/
theorem preliminary_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : labelFiberSet v} {τ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d z j τ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  exact ⟨θ,hb,hc,a,ha,ht,hr,links_restrict hμ c C d f τ _ hl⟩

/-- The equation for every member of the tail group, including its moved
Cohen condition and moved vertex. Ground code order is unchanged. -/
theorem preliminary_permute (g : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (w : Vertex q) (j : labelFiberSet v) (τ : (S).Name)
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Preliminary hμ c hcard hsize hmerger hj E hE C (d.permute g.val.val.val)
      (g.val.val • w) j (g.val.val.val • τ) := by
  obtain ⟨θ,hb,hc,a,ha,ht,hr,hl⟩ := h
  have hg : g.val.val.val ∈ tailGroup hj C := (tailGroup_mem hj C _).mpr ⟨g,rfl⟩
  refine ⟨θ,hb,hc,a,isSelected_covariance hμ c hcard hsize hmerger hj E hE C _ hg a d ha,?_,?_,
    links_permute hμ c hj C g d w τ _ hl⟩
  · exact tail_eq_permute hμ c hsize hmerger hj C g d _ _
      (ordinalType_fixed hμ c hcard hsize hmerger hj E hE C)
      (fun π _ => Name.smul_check S π _) ht
  · exact tail_eq_permute hμ c hsize hmerger hj C g d _ _
      (ordinalRank_fixed hμ c hcard hsize hmerger hj E hE C a)
      (fun π _ => Name.smul_check S π _) hr

/-- Dense totality at an arbitrary vertex of the component. -/
theorem preliminary_total (d : CohenForcing.Condition I κ)
    (hcount : OrdinalCount hμ c hcard hsize hmerger hj E hE C d)
    (w : Vertex q) (hw : Vertex.Common v w) (j : labelFiberSet v) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      Preliminary hμ c hcard hsize hmerger hj E hE C e w j τ.name := by
  obtain ⟨e,hed,θ,hb,ht⟩ := ordinalType_decide hμ c hcard hsize hmerger hj E hE C d
  have hc := hcount e hed θ ht
  let β := OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C) θ hb hc j
  obtain ⟨f,hfe,a,ha,hr⟩ := member_ordinalRank hμ c hcard hsize hmerger hj E hE C e θ ht β
  obtain ⟨τ,hτ⟩ := working_linked hμ c hcard hsize hmerger hj E hE C f (code hμ c C a) ha.1 w hw
  refine ⟨f,hfe.trans hed,τ,θ,hb,hc,a,ha,?_,hr,hτ⟩
  exact (S).atomic.eq_mono (WithTop.coe_le_coe.mpr (show (f,v.diagram) ≤ (e,v.diagram) from
    ⟨hfe,le_rfl⟩)) ht

/-- Dense surjectivity onto every persistent linked class, before any
selector or coset representative is chosen. -/
theorem preliminary_onto (d : CohenForcing.Condition I κ)
    (hcount : OrdinalCount hμ c hcard hsize hmerger hj E hE C d)
    (w : Vertex q) (τ : (S).Name) (a : ChainCode hμ c C)
    (ha : Works hμ c hcard hsize hmerger hj E hE C d a)
    (hl : Links hμ c C d w τ a) :
    ∃ e, e ≤ d ∧ ∃ j : labelFiberSet v,
      Preliminary hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨e,hed,b,hb,hab⟩ := dense_selected hμ c hcard hsize hmerger hj E hE C d a ha
  let ib := (code hμ c C).symm b
  have hb' : Sel ib e := by simpa only [ib,Equiv.apply_symm_apply,IsSelected] using hb
  have hl' : Links hμ c C e w τ (code hμ c C ib) := by
    simpa only [ib,Equiv.apply_symm_apply] using links_same (links_mono hed hl) hab
  obtain ⟨f,hfe,θ,hθ,ht⟩ := ordinalType_decide hμ c hcard hsize hmerger hj E hE C e
  have hc := hcount f (hfe.trans hed) θ ht
  have hbf := isSelected_mono hμ c hcard hsize hmerger hj E hE C hfe hb'
  obtain ⟨g,hgf,β,hr⟩ := ordinalRank_decide hμ c hcard hsize hmerger hj E hE C ib f hbf θ ht
  let j := (OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C) θ hθ hc).symm β
  refine ⟨g,hgf.trans (hfe.trans hed),j,θ,hθ,hc,ib,
    isSelected_mono hμ c hcard hsize hmerger hj E hE C hgf hbf,?_,?_,
    links_mono (hgf.trans hfe) hl'⟩
  · exact (S).atomic.eq_mono (WithTop.coe_le_coe.mpr (show (g,v.diagram) ≤ (f,v.diagram) from
      ⟨hgf,le_rfl⟩)) ht
  · simpa only [j,Equiv.apply_symm_apply] using hr

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## Germ -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u t
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I} {v : Vertex q}
noncomputable section
variable (C : Chain v)

theorem index_transition (i j : ℕ) (f : Arrow (C.vertex i) (C.vertex j)) :
    C.index i * f.index = C.index j := by
  exact congrArg Arrow.index (Subsingleton.elim ((C.fromRoot i).comp f) (C.fromRoot j))

theorem alignments_nonempty (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) : (C.Alignments hj π).Nonempty := by
  have ht : Common v ((π⁻¹).val • v) := (π⁻¹).property
  obtain ⟨i,⟨f⟩⟩ := C.cofinal _ ht
  have g : Arrow v (π.val • C.vertex i) := by
    simpa only [Subgroup.coe_inv,smul_inv_smul] using f.move π.val
  exact ⟨(i,g.index),g,rfl⟩

/-- Each alignment index is bounded by an original chain index. -/
theorem alignment_bounded (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) {p : ℕ × M} (hp : p ∈ C.Alignments hj π) :
    ∃ N, p.2 ∣ C.index N := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨N,⟨g⟩⟩ := C.cofinal _ (Common.of_arrow f)
  have hh := congrArg Arrow.index (Subsingleton.elim (f.comp g) (C.fromRoot N))
  exact ⟨N,g.index,by simpa only [Arrow.comp,fromRoot_index,hf] using hh.symm⟩

/-- Arbitrary cofinal advances are admissible replacements in the precise
sense required by finite old-gate descent. -/
theorem alignment_replacement (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) {p : ℕ × M} (hp : p ∈ C.Alignments hj π) (N : ℕ) :
    ∃ l' d, (l',p.2*d) ∈ C.Alignments hj π ∧ p.1 ≤ l' ∧
      C.index p.1*d = C.index l' ∧ C.index N ∣ p.2*d := by
  obtain ⟨f,hf⟩ := hp
  have ht : Common v ((π⁻¹).val • C.vertex N) :=
    common_moved hj v (π⁻¹) (C.common N)
  obtain ⟨k,⟨g⟩⟩ := C.cofinal _ ht
  let l' := max p.1 k
  let d := (C.increasing p.1 l' (le_max_left _ _)).some
  let e := (C.increasing k l' (le_max_right _ _)).some
  have g' : Arrow (C.vertex N) (π.val • C.vertex l') := by
    simpa only [Subgroup.coe_inv,smul_inv_smul] using (g.comp e).move π.val
  let f' := f.comp (d.move π.val)
  refine ⟨l',d.index,⟨f',by change f.index*d.index = p.2*d.index; rw [hf]⟩,
    le_max_left _ _,C.index_transition _ _ d,g'.index,?_⟩
  have hh := congrArg Arrow.index (Subsingleton.elim ((C.fromRoot N).comp g') f')
  simpa only [Arrow.comp,Arrow.move,fromRoot_index,hf,f'] using hh.symm

/-- Having the same alignment identifies the two actual quotient cosets.
This is independent of any choice of a descent path. -/
theorem coset_eq_of_alignment (hj : HasConditionalJoins (LeftDivOrder M))
    (π σ : componentStabilizer hj v) {p : ℕ × M}
    (hπ : p ∈ C.Alignments hj π) (hσ : p ∈ C.Alignments hj σ) :
    (QuotientGroup.mk' (C.tailFixer hj) π) = QuotientGroup.mk' (C.tailFixer hj) σ := by
  apply QuotientGroup.eq.mpr
  obtain ⟨f,hf⟩ := hπ
  obtain ⟨g,hg⟩ := hσ
  refine ⟨p.1,?_⟩
  rintro j ⟨x,rfl⟩
  have hdiag : (C.vertex p.1).diagram.permute π.val.val =
      (C.vertex p.1).diagram.permute σ.val.val := by
    rw [← smul_diagram,← smul_diagram,← f.diagram,← g.diagram,hf,hg]
  have hh := congrArg (fun r : Diagram M I => r x) hdiag
  change π.val.val.symm (σ.val.val ((C.vertex p.1).diagram x)) = (C.vertex p.1).diagram x
  change π.val.val ((C.vertex p.1).diagram x) = σ.val.val ((C.vertex p.1).diagram x) at hh
  rw [← hh,Equiv.symm_apply_apply]

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain


/-! ## Selector -/

/-! A combinatorial coset-selector argument. The existence of a countable-base
tower and symmetric names for its assignments are established separately. -/

namespace PartitionConsistency.TailSelector
universe u v w
noncomputable section
open scoped Classical

theorem eventualMk_eq_iff {A : Type*} (f g : ℕ → A) :
    eventualMk f = eventualMk g ↔ ∃ N, ∀ n, N ≤ n → f n = g n :=
  Quotient.eq

namespace TailData
variable {G : Type u} {I : Type v} [Group G] [MulAction G I] (D : TailData G I)

theorem detector_mem (δ : D.Nonidentity) (n : ℕ) : D.detector δ n ∈ D.tail n :=
  (D.detector_exists δ n).choose_spec.1

theorem detector_moved (δ : D.Nonidentity) (n : ℕ) :
    δ.val.out • D.detector δ n ≠ D.detector δ n :=
  (D.detector_exists δ n).choose_spec.2

theorem detector_fixed_eventually {k : G} (hk : k ∈ D.K) (δ : D.Nonidentity) :
    ∃ N, ∀ n, N ≤ n → k • D.detector δ n = D.detector δ n := by
  obtain ⟨N,hN⟩ := (D.mem_iff k).mp hk
  exact ⟨N,fun n hn => hN _ (D.antitone hn (D.detector_mem δ n))⟩

variable {κ : Type w} [LinearOrder κ]

theorem rawPattern_congr (R : I → κ → Bool) (α : κ) {g h : G}
    (he : (g : D.Cosets) = (h : D.Cosets)) :
    D.rawPattern R α g = D.rawPattern R α h := by
  funext δ
  obtain ⟨N,hN⟩ := D.detector_fixed_eventually (QuotientGroup.eq.mp he) δ
  apply (eventualMk_eq_iff _ _).mpr
  refine ⟨N,fun n hn => ?_⟩
  have hs : g • D.detector δ n = h • D.detector δ n := by
    have hh := congrArg (fun i : I => g • i) (hN n hn)
    simpa only [← mul_smul,mul_inv_cancel_left] using hh.symm
  rw [hs]

@[simp] theorem pattern_mk (R : I → κ → Bool) (α : κ) (g : G) :
    D.pattern R α (g : D.Cosets) = D.rawPattern R α g :=
  D.rawPattern_congr R α (QuotientGroup.out_eq' _)

/-- The actual pattern objects, not just their cardinalities, are identical
under left multiplication in the quotient and transport of rows. -/
theorem pattern_covariance (σ : G) (R : I → κ → Bool) (α : κ) (c : D.Cosets) :
    D.pattern (moveRows σ R) α ((σ : D.Cosets) * c) = D.pattern R α c := by
  induction c using Quotient.inductionOn with
  | h g => rw [← QuotientGroup.mk_mul,D.pattern_mk,D.pattern_mk,D.rawPattern_moveRows]

/-- Distinct cosets are detected at every sufficiently late position of one
of the fixed detector sequences. -/
theorem detector_separates (g h : G) (hne : (g : D.Cosets) ≠ (h : D.Cosets)) :
    ∃ δ : D.Nonidentity, ∃ N, ∀ n, N ≤ n →
      g • D.detector δ n ≠ h • D.detector δ n := by
  let δ : D.Nonidentity := ⟨((g⁻¹*h : G) : D.Cosets),by
    intro he
    exact hne (QuotientGroup.eq.mpr ((QuotientGroup.eq_one_iff _).mp he))⟩
  have he : (δ.val.out : D.Cosets) = ((g⁻¹*h : G) : D.Cosets) :=
    QuotientGroup.out_eq' δ.val
  obtain ⟨N,hN⟩ := D.detector_fixed_eventually (QuotientGroup.eq.mp he) δ
  refine ⟨δ,N,fun n hn heq => ?_⟩
  have hh : (g⁻¹*h) • D.detector δ n = δ.val.out • D.detector δ n := by
    have hh := congrArg (fun i : I => δ.val.out • i) (hN n hn)
    simpa only [← mul_smul,mul_inv_cancel_left] using hh
  have hh' := congrArg (fun i : I => g⁻¹ • i) heq
  rw [inv_smul_smul,← mul_smul,hh] at hh'
  exact D.detector_moved δ n hh'.symm

variable [WellFoundedLT κ]

theorem leastBound_distinguishes (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α)) :
    Function.Injective (D.pattern R (D.leastBound R h)) :=
  wellFounded_lt.min_mem _ h

omit [WellFoundedLT κ] in
theorem distinguishes_moveRows_iff (σ : G) (R : I → κ → Bool) (α : κ) :
    Function.Injective (D.pattern (moveRows σ R) α) ↔ Function.Injective (D.pattern R α) := by
  constructor
  · intro hinj c e he
    apply mul_left_cancel (a := (σ : D.Cosets))
    apply hinj
    simpa only [D.pattern_covariance] using he
  · intro hinj c e he
    have hc := D.pattern_covariance σ R α ((σ : D.Cosets)⁻¹*c)
    have he' := D.pattern_covariance σ R α ((σ : D.Cosets)⁻¹*e)
    simp only [mul_inv_cancel_left] at hc he'
    have hh := hinj (hc.symm.trans (he.trans he'))
    exact mul_left_cancel hh

theorem leastBound_covariance (σ : G) (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α))
    (h' : ∃ α, Function.Injective (D.pattern (moveRows σ R) α)) :
    D.leastBound (moveRows σ R) h' = D.leastBound R h := by
  have hs : {α | Function.Injective (D.pattern (moveRows σ R) α)} =
      {α | Function.Injective (D.pattern R α)} := by
    ext α
    exact D.distinguishes_moveRows_iff σ R α
  unfold leastBound
  congr 1

omit [WellFoundedLT κ] in
theorem bestCoset_minimal (R : I → κ → Bool) (α : κ) (c : D.Cosets) :
    ¬ WellOrderingRel (D.pattern R α c) (D.pattern R α (D.bestCoset R α)) :=
  (InvImage.wf (D.pattern R α) WellOrderingRel.isWellOrder.wf).not_lt_min
    Set.univ (Set.mem_univ c)

omit [WellFoundedLT κ] in
theorem bestCoset_covariance (σ : G) (R : I → κ → Bool) (α : κ)
    (hα : Function.Injective (D.pattern R α)) :
    D.bestCoset (moveRows σ R) α = (σ : D.Cosets) * D.bestCoset R α := by
  let c := D.bestCoset (moveRows σ R) α
  let e := D.bestCoset R α
  have hc : D.pattern (moveRows σ R) α c = D.pattern R α ((σ : D.Cosets)⁻¹*c) := by
    simpa only [mul_inv_cancel_left] using D.pattern_covariance σ R α ((σ : D.Cosets)⁻¹*c)
  have hmin : ¬ WellOrderingRel (D.pattern R α e) (D.pattern R α ((σ : D.Cosets)⁻¹*c)) := by
    have hh := D.bestCoset_minimal (moveRows σ R) α ((σ : D.Cosets)*e)
    rwa [D.pattern_covariance,hc] at hh
  have hmin' := D.bestCoset_minimal R α ((σ : D.Cosets)⁻¹*c)
  have heq : D.pattern R α ((σ : D.Cosets)⁻¹*c) = D.pattern R α e := by
    rcases trichotomous_of WellOrderingRel (D.pattern R α ((σ : D.Cosets)⁻¹*c))
      (D.pattern R α e) with hlt | heq | hgt
    · exact (hmin' hlt).elim
    · exact heq
    · exact (hmin hgt).elim
  have hh := congrArg (fun d : D.Cosets => (σ : D.Cosets)*d) (hα heq)
  simpa only [mul_inv_cancel_left,c,e] using hh

/-- Source equation (coset-selector-covariance), proved with the actual row
objects on both sides, including invariance of the least distinguishing bound. -/
theorem selector_covariance (σ : G) (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α))
    (h' : ∃ α, Function.Injective (D.pattern (moveRows σ R) α)) :
    D.selector (moveRows σ R) h' = (σ : D.Cosets) * D.selector R h := by
  unfold selector
  rw [D.leastBound_covariance σ R h h']
  exact D.bestCoset_covariance σ R _ (D.leastBound_distinguishes R h)

end TailData
end
end PartitionConsistency.TailSelector

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_StableSelectors
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ConditionSelector -/

/-! The countable-germ selector as a genuine condition-by-condition recipe.
There is no total family of generic rows in the ambient universe in this
construction.  A countable condition suffices to decide each selection, and
the decisions are both persistent and covariant. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

theorem rows_of_mem (p : Condition I κ) (i : I) (a : κ) (b : Bool)
    (h : ((i,a),b) ∈ p.graph) : p.rows i a = b := by
  cases b
  · have hn : ((i,a),true) ∉ p.graph := fun ht => Bool.false_ne_true (p.functional _ _ _ h ht)
    simp [rows,hn]
  · simp [rows,h]

theorem rows_eq_of_le {p q : Condition I κ} (hqp : q ≤ p) {i : I} {a : κ}
    (ha : (i,a) ∈ p.dom) : q.rows i a = p.rows i a := by
  obtain ⟨b,hb⟩ := (p.mem_dom _).mp ha
  exact (q.rows_of_mem i a b (hqp hb)).trans (p.rows_of_mem i a b hb).symm

theorem dom_mono {p q : Condition I κ} (hqp : q ≤ p) : p.dom ⊆ q.dom := by
  intro a ha
  obtain ⟨b,hb⟩ := (p.mem_dom _).mp ha
  exact (q.mem_dom _).mpr ⟨b,hqp hb⟩

theorem fill_le (p : Condition I κ) (A : Set (I × κ)) (hA : A.Countable) :
    p.fill A hA ≤ p := fun _ h => Or.inl h

theorem subset_dom_fill (p : Condition I κ) (A : Set (I × κ)) (hA : A.Countable) :
    A ⊆ (p.fill A hA).dom := by
  intro a ha
  by_cases h : a ∈ p.dom
  · exact dom_mono (p.fill_le A hA) h
  · exact ((p.fill A hA).mem_dom a).mpr ⟨false,Or.inr ⟨ha,h,rfl⟩⟩

end
end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.TailSelector.TailData
universe u
noncomputable section
open scoped Classical
open CohenForcing
variable {G I κ : Type u} [Group G] [MulAction G I] (D : TailData G I)
variable [LinearOrder κ]

/-- Eventually the canonical representative of a coset acts just like any
other representative on each detector sequence. -/
theorem representative_eventually (g : G) (δ : D.Nonidentity) :
    ∃ N, ∀ n, N ≤ n → (g : D.Cosets).out • D.detector δ n = g • D.detector δ n := by
  obtain ⟨N,hN⟩ := D.detector_fixed_eventually
    (QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : D.Cosets))) δ
  refine ⟨N,fun n hn => ?_⟩
  have h := congrArg (fun i : I => (g : D.Cosets).out • i) (hN n hn)
  simpa only [← mul_smul,mul_inv_cancel_left] using h.symm

theorem Complete.mono {p q : Condition I κ} {α : κ} (h : D.Complete p α) (hqp : q ≤ p) :
    D.Complete q α := by
  intro g δ
  obtain ⟨N,hN⟩ := h g δ
  exact ⟨N,fun n hn b => Condition.dom_mono hqp (hN n hn b)⟩

theorem Complete.downward {p : Condition I κ} {α β : κ}
    (h : D.Complete p α) (hβα : β ≤ α) : D.Complete p β := by
  intro g δ
  obtain ⟨N,hN⟩ := h g δ
  exact ⟨N,fun n hn b => hN n hn ⟨b.val,b.property.trans_le hβα⟩⟩

/-- Assigned bounded patterns cannot be altered by an extension. -/
theorem Complete.pattern_eq {p q : Condition I κ} {α : κ}
    (h : D.Complete p α) (hqp : q ≤ p) : D.pattern q.rows α = D.pattern p.rows α := by
  funext c δ
  apply (eventualMk_eq_iff _ _).mpr
  obtain ⟨N,hN⟩ := h c.out δ
  refine ⟨N,fun n hn => funext (fun b => ?_)⟩
  exact Condition.rows_eq_of_le hqp (hN n hn b)

theorem Complete.permute {p : Condition I κ} {α : κ}
    (h : D.Complete p α) (σ : G) : D.Complete (p.permute (MulAction.toPerm σ)) α := by
  intro g δ
  obtain ⟨N,hN⟩ := h (σ⁻¹*g) δ
  refine ⟨N,fun n hn b => ?_⟩
  obtain ⟨a,ha⟩ := (p.mem_dom _).mp (hN n hn b)
  apply ((p.permute (MulAction.toPerm σ)).mem_dom _).mpr
  refine ⟨a,?_⟩
  simpa only [Condition.mem_permute,Condition.coordinatePerm_symm_apply,
    MulAction.toPerm_symm_apply,mul_smul] using ha

omit [LinearOrder κ] in
theorem rows_permute (σ : G) (p : Condition I κ) :
    (p.permute (MulAction.toPerm σ)).rows = moveRows σ p.rows := by
  funext i a
  simpa only [moveRows,MulAction.toPerm_symm_apply] using
    Condition.rows_permute (MulAction.toPerm σ) p i a

theorem Good.mono {p q : Condition I κ} (h : D.Good p) (hqp : q ≤ p) : D.Good q := by
  obtain ⟨α,hc,hi⟩ := h
  refine ⟨α,hc.mono D hqp,?_⟩
  rwa [hc.pattern_eq D hqp]

theorem Good.permute [WellFoundedLT κ] {p : Condition I κ} (h : D.Good p) (σ : G) :
    D.Good (p.permute (MulAction.toPerm σ)) := by
  obtain ⟨α,hc,hi⟩ := h
  refine ⟨α,hc.permute D σ,?_⟩
  rw [rows_permute]
  exact (D.distinguishes_moveRows_iff σ p.rows α).mpr hi

theorem detectorSites_countable [Countable D.Cosets] : D.detectorSites.Countable :=
  Set.countable_range _

theorem detectorSite_mem (c : D.Cosets) (δ : D.Nonidentity) (n : ℕ) :
    c.out • D.detector δ n ∈ D.detectorSites := ⟨(c,δ,n),rfl⟩

theorem complete_of_covered {p : Condition I κ} {α : κ}
    (h : D.detectorSites ×ˢ Set.Iio α ⊆ p.dom) : D.Complete p α := by
  intro g δ
  obtain ⟨N,hN⟩ := D.representative_eventually g δ
  refine ⟨N,fun n hn b => ?_⟩
  rw [← hN n hn]
  exact h ⟨D.detectorSite_mem (g : D.Cosets) δ n,b.property⟩

private theorem bounded_countable [Nonempty κ]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    {A : Type u} [Countable A] (f : A → κ) : ∃ α, ∀ a, f a < α := by
  let : Encodable A := Encodable.ofCountable A
  let g : ℕ → κ := fun n => (Encodable.decode (α := A) n).elim
    (Classical.choice ‹Nonempty κ›) f
  obtain ⟨α,hα⟩ := hbound g
  refine ⟨α,fun a => ?_⟩
  simpa only [g,Encodable.encodek,Option.elim_some] using hα (Encodable.encode a)

/-- In one countable extension all relevant unequal detector sites acquire
opposite bits below a common countable bound. This argument does not assume
that the ambient universe already contains distinct rows on all of I. -/
theorem good_dense [Nonempty κ] [Uncountable κ] [Countable D.Cosets]
    (hbound : ∀ f : ℕ → κ, ∃ α, ∀ n, f n < α)
    (hcount : ∀ α : κ, (Set.Iio α).Countable) (p : Condition I κ) :
    ∃ q, q ≤ p ∧ D.Good q := by
  let J := D.detectorSites
  let : Countable J := D.detectorSites_countable.to_subtype
  let A := {z : J × J // z.1 ≠ z.2}
  let R (z : A) (q : Condition I κ) :=
    ∃ a : κ, ((z.val.1.val,a),false) ∈ q.graph ∧ ((z.val.2.val,a),true) ∈ q.graph
  have hdense : ∀ z q, q ≤ p → ∃ r, r ≤ q ∧ R z r := by
    intro z q _
    have hne : z.val.1.val ≠ z.val.2.val := fun h => z.property (Subtype.ext h)
    obtain ⟨r,a,hr,hx,hy⟩ := q.separate_labels hne
    exact ⟨r,hr,a,hx,hy⟩
  obtain ⟨q,hqp,hq⟩ := Condition.countable_fusion p R
    (fun z q r hr ⟨a,hx,hy⟩ => ⟨a,hr hx,hr hy⟩) hdense
  choose bit hfalse htrue using hq
  obtain ⟨α,hα⟩ := bounded_countable hbound bit
  let B := J ×ˢ Set.Iio α
  have hB : B.Countable := D.detectorSites_countable.prod (hcount α)
  let r := q.fill B hB
  have hrq : r ≤ q := q.fill_le B hB
  refine ⟨r,hrq.trans hqp,α,D.complete_of_covered (q.subset_dom_fill B hB),?_⟩
  intro c e he
  by_contra hne
  have hne' : (c.out : D.Cosets) ≠ (e.out : D.Cosets) := by
    simpa only [QuotientGroup.out_eq'] using hne
  obtain ⟨δ,N,hN⟩ := D.detector_separates c.out e.out hne'
  obtain ⟨M,hM⟩ := (eventualMk_eq_iff _ _).mp (congrFun he δ)
  let x : J := ⟨c.out • D.detector δ (N+M),D.detectorSite_mem c δ (N+M)⟩
  let y : J := ⟨e.out • D.detector δ (N+M),D.detectorSite_mem e δ (N+M)⟩
  let z : A := ⟨(x,y),fun h => hN (N+M) (Nat.le_add_right _ _) (congrArg Subtype.val h)⟩
  have hh := congrFun (hM (N+M) (Nat.le_add_left _ _)) (⟨bit z,hα z⟩ : Set.Iio α)
  have hx : r.rows x.val (bit z) = false := r.rows_of_mem _ _ _ (hrq (hfalse z))
  have hy : r.rows y.val (bit z) = true := r.rows_of_mem _ _ _ (hrq (htrue z))
  exact Bool.false_ne_true (hx.symm.trans (hh.trans hy))

variable [WellFoundedLT κ]

theorem leastBound_le (R : I → κ → Bool)
    (h : ∃ α, Function.Injective (D.pattern R α)) (α : κ)
    (hα : Function.Injective (D.pattern R α)) : D.leastBound R h ≤ α :=
  not_lt.mp (wellFounded_lt.not_lt_min _ hα)

theorem Good.complete_least {p : Condition I κ} (h : D.Good p) :
    D.Complete p (D.leastBound p.rows ⟨h.choose,h.choose_spec.2⟩) :=
  h.choose_spec.1.downward D (D.leastBound_le _ _ _ h.choose_spec.2)

/-- The first distinguishing bound is persistent, not an artifact of how
undefined rows were filled. -/
theorem leastBound_extension {p q : Condition I κ} (hp : D.Good p) (hq : D.Good q)
    (hqp : q ≤ p) :
    D.leastBound q.rows ⟨hq.choose,hq.choose_spec.2⟩ =
      D.leastBound p.rows ⟨hp.choose,hp.choose_spec.2⟩ := by
  let α := D.leastBound p.rows ⟨hp.choose,hp.choose_spec.2⟩
  let β := D.leastBound q.rows ⟨hq.choose,hq.choose_spec.2⟩
  have hc : D.Complete p α := hp.complete_least D
  have hi : Function.Injective (D.pattern q.rows α) := by
    rw [hc.pattern_eq D hqp]
    exact D.leastBound_distinguishes _ _
  have hβα : β ≤ α := D.leastBound_le _ _ _ hi
  have hi' : Function.Injective (D.pattern p.rows β) := by
    rw [← (hc.downward D hβα).pattern_eq D hqp]
    exact D.leastBound_distinguishes _ _
  exact le_antisymm hβα (D.leastBound_le _ _ _ hi')

omit [WellFoundedLT κ] in
theorem bestCoset_congr (R R' : I → κ → Bool) (α : κ)
    (h : D.pattern R α = D.pattern R' α) : D.bestCoset R α = D.bestCoset R' α := by
  unfold bestCoset
  congr 1
  rw [h]

/-- Every stronger condition makes the same coset decision. -/
theorem conditionSelector_extension {p q : Condition I κ} (hp : D.Good p) (hq : D.Good q)
    (hqp : q ≤ p) : D.conditionSelector q hq = D.conditionSelector p hp := by
  unfold conditionSelector selector
  rw [D.leastBound_extension hp hq hqp]
  exact D.bestCoset_congr _ _ _ ((hp.complete_least D).pattern_eq D hqp)

/-- Genuine covariance of the persistent decision made by a Cohen condition. -/
theorem conditionSelector_permute (p : Condition I κ) (hp : D.Good p) (σ : G)
    (hq : D.Good (p.permute (MulAction.toPerm σ))) :
    D.conditionSelector (p.permute (MulAction.toPerm σ)) hq =
      (σ : D.Cosets) * D.conditionSelector p hp := by
  unfold conditionSelector
  have hrow := rows_permute σ p
  have he : ∃ α, Function.Injective (D.pattern (moveRows σ p.rows) α) := by
    simpa only [hrow] using (show ∃ α, Function.Injective
      (D.pattern (p.permute (MulAction.toPerm σ)).rows α) from ⟨hq.choose,hq.choose_spec.2⟩)
  have hh := D.selector_covariance σ p.rows ⟨hp.choose,hp.choose_spec.2⟩ he
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [hrow]

theorem Selected.mono {p q : Condition I κ} {c : D.Cosets}
    (h : D.Selected p c) (hqp : q ≤ p) : D.Selected q c := by
  obtain ⟨hp,rfl⟩ := h
  exact ⟨hp.mono D hqp,D.conditionSelector_extension hp (hp.mono D hqp) hqp⟩

theorem selected_unique {p : Condition I κ} {c e : D.Cosets}
    (hc : D.Selected p c) (he : D.Selected p e) : c = e := by
  obtain ⟨hp,rfl⟩ := hc
  obtain ⟨hq,rfl⟩ := he
  rfl

theorem Selected.permute {p : Condition I κ} {c : D.Cosets}
    (h : D.Selected p c) (σ : G) :
    D.Selected (p.permute (MulAction.toPerm σ)) ((σ : D.Cosets)*c) := by
  obtain ⟨hp,rfl⟩ := h
  exact ⟨hp.permute D σ,D.conditionSelector_permute p hp σ _⟩

end
end PartitionConsistency.TailSelector.TailData


/-! ## CosetPredicate -/

/-! Coset transport for predicates on the total space of computations.
The inverse moves every argument, in particular the actual Cohen condition. -/

namespace PartitionConsistency.CosetPredicate
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
noncomputable section

theorem shift_mul (g h : G) (R : X → Prop) :
    shift (g*h) R = shift g (shift h R) := by
  funext x
  simp only [shift, mul_inv_rev, mul_smul]

theorem shift_at_moved (g : G) (R : X → Prop) (x : X) :
    shift g R (g • x) = R x := by
  simp only [shift, inv_smul_smul]

theorem shift_eq (K : Subgroup G) (R : X → Prop) (hR : Invariant K R)
    {g h : G} (he : (g : G ⧸ K) = h) : shift g R = shift h R := by
  have hk : g⁻¹*h ∈ K := QuotientGroup.eq.mp he
  have hi : shift (g⁻¹*h) R = R := by
    funext x
    exact propext (hR _ (K.inv_mem hk) x)
  calc
    shift g R = shift g (shift (g⁻¹*h) R) := by rw [hi]
    _ = shift (g*(g⁻¹*h)) R := (shift_mul _ _ _).symm
    _ = shift h R := by rw [mul_inv_cancel_left]

end
end PartitionConsistency.CosetPredicate


/-! ## Corrected -/

/-! A component assignment on actual conditions: select a residual coset,
compute at the inverse-moved condition, then transport every argument back.
The quotient operation uses proved tail invariance, not an arbitrary choice
of a bijection. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.componentStabilizer hj v
local notation "K" => C.tailFixer hj

theorem preliminaryPoint_move (k : K) (x : AssignmentPoint (κ := κ) hμ (v := v))
    (hx : preliminaryPoint hμ c hcard hsize hmerger hj E hE C x) :
    preliminaryPoint hμ c hcard hsize hmerger hj E hE C (k.val • x) := by
  obtain ⟨d,w,j,τ⟩ := x
  change Preliminary hμ c hcard hsize hmerger hj E hE C
    (d.permute k.val.val.val) (k.val.val • w) (k.val • j) (k.val.val.val • τ)
  rw [Vertex.Chain.tailFixer_fixes_label hj v C k j]
  exact preliminary_permute hμ c hcard hsize hmerger hj E hE C k d w j τ hx

theorem preliminaryPoint_invariant : CosetPredicate.Invariant K
    (preliminaryPoint hμ c hcard hsize hmerger hj E hE C) := by
  intro k hk x
  constructor
  · intro h
    have hh := preliminaryPoint_move hμ c hcard hsize hmerger hj E hE C ⟨k⁻¹,(K).inv_mem hk⟩ (k • x) h
    simpa only [inv_smul_smul] using hh
  · exact preliminaryPoint_move hμ c hcard hsize hmerger hj E hE C ⟨k,hk⟩ x

variable [LinearOrder κ] [WellFoundedLT κ]

/-- Independence of the representative of the selected coset. -/
theorem corrected_selected {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name} (g : G)
    (hg : (C.tailData hj).Selected d (g : G ⧸ K)) :
    Corrected hμ c hcard hsize hmerger hj E hE C d w j τ ↔
      Preliminary hμ c hcard hsize hmerger hj E hE C
        (g⁻¹ • d) (g⁻¹ • w) (g⁻¹ • j) (g⁻¹ • τ) := by
  constructor
  · rintro ⟨k,hk,h⟩
    have he : (k : G ⧸ K) = g := (C.tailData hj).selected_unique hk hg
    have hs := CosetPredicate.shift_eq K
      (preliminaryPoint hμ c hcard hsize hmerger hj E hE C)
      (preliminaryPoint_invariant hμ c hcard hsize hmerger hj E hE C) he
    rw [hs] at h
    exact h
  · intro h
    exact ⟨g,hg,h⟩

variable {hμ c hcard hsize hmerger hj E hE C}

theorem corrected_mono {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name} (hed : e ≤ d)
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Corrected hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨g,hg,h⟩ := h
  refine ⟨g,hg.mono _ hed,?_⟩
  exact preliminary_mono ((CohenForcing.Condition.permuteOrderIso g.val.val⁻¹).monotone hed) h

variable (hμ)

omit [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ] in
/-- Equality transport at a moved vertex, with the moved Cohen coordinate. -/
theorem root_eq_symmetry (g : Vertex.RootGroup q) (d : CohenForcing.Condition I κ)
    (w : Vertex q) (τ σ : (S).Name) :
    (S).atomic.EqF ((g • d,(g • w).diagram) : Poset M I κ) (g • τ) (g • σ) ↔
      (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ := by
  change (S).atomic.EqF ((d.permute g.val,w.diagram.permute g.val) : Poset M I κ)
      (g.val • τ) (g.val • σ) ↔ _
  simpa only [move_coe,permute] using
    ((S).eq_symmetry g.val ((d,w.diagram) : Poset M I κ) τ σ).symm

variable {hμ}

variable (hμ c hcard hsize hmerger hj E hE C)

/-- Both injectivity and single-valuedness survive coset correction. -/
theorem corrected_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j k : labelFiberSet v} {τ σ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ)
    (h' : Corrected hμ c hcard hsize hmerger hj E hE C d w k σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = k := by
  obtain ⟨g,hg,h⟩ := h
  have hh := (corrected_selected hμ c hcard hsize hmerger hj E hE C g hg).mp h'
  rw [← root_eq_symmetry hμ g.val⁻¹ d w τ σ]
  exact (preliminary_eq_iff h hh).trans (MulAction.injective g⁻¹).eq_iff

/-- Covariance under every element of the entire component stabilizer. -/
theorem corrected_permute (g : G) (d : CohenForcing.Condition I κ) (w : Vertex q)
    (j : labelFiberSet v) (τ : (S).Name)
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Corrected hμ c hcard hsize hmerger hj E hE C
      (g • d) (g • w) (g • j) (g • τ) := by
  obtain ⟨k,hk,h⟩ := h
  refine ⟨g*k,?_,?_⟩
  · have hg : MulAction.toPerm g = g.val.val := by ext; rfl
    change (C.tailData hj).Selected (d.permute g.val.val) _
    rw [QuotientGroup.mk_mul]
    have hh := hk.permute (C.tailData hj) g
    rw [hg] at hh
    exact hh
  · change CosetPredicate.shift (g*k)
      (preliminaryPoint hμ c hcard hsize hmerger hj E hE C)
      (g • (d,w,j,τ))
    rw [CosetPredicate.shift_mul,CosetPredicate.shift_at_moved]
    exact h

/-- Pullback along a contraction retains precisely the same representative. -/
theorem corrected_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : labelFiberSet v} {τ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d z j τ) :
    Corrected hμ c hcard hsize hmerger hj E hE C d w j τ := by
  obtain ⟨g,hg,h⟩ := h
  exact ⟨g,hg,preliminary_restrict hμ c hcard hsize hmerger hj E hE C (f.move g.val⁻¹) h⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## StableTransport -/

/-! Coordinate transport for the permanently decided availability ideal.
This is used both for coset correction and for moving between component
orbits. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

omit [Infinite M] [Infinite I] in
/-- Moving the entire local equality test also moves its normalized witness. -/
theorem forcedAvailable_permute_iff (π : Equiv.Perm I)
    (d : CohenForcing.Condition I κ) (r : Diagram M I) (τ : LocalName hμ c r) (n : M) :
    ForcedAvailable hμ c (d.permute π) (r.permute π) (τ.transport hμ π) n ↔
      ForcedAvailable hμ c d r τ n := by
  constructor
  · rintro ⟨σ,he⟩
    let ρ := σ.rebase hμ c (Diagram.permute_sub π r n).symm
    obtain ⟨ν,hν⟩ := (LocalName.transportEquiv hμ c π (r.sub n)).surjective ρ
    have hname : π • ν.name = σ.name := congrArg LocalName.name hν
    refine ⟨ν,?_⟩
    apply ((S).eq_symmetry π ((d,r) : Poset M I κ) ν.name τ.name).mpr
    simpa only [move_coe,permute,hname,LocalName.transport_name] using he
  · rintro ⟨σ,he⟩
    refine ⟨(σ.transport hμ π).rebase hμ c (Diagram.permute_sub π r n),?_⟩
    simpa only [move_coe,permute,LocalName.rebase_name,LocalName.transport_name] using
      ((S).eq_symmetry π ((d,r) : Poset M I κ) σ.name τ.name).mp he

/-- The actual ideal is preserved, not merely its cardinality. -/
theorem forcedAvailability_permute (π : Equiv.Perm I)
    (d : CohenForcing.Condition I κ) (r : Diagram M I) (a : M) (τ : LocalName hμ c r) :
    forcedAvailability hμ c hcard hsize hmerger (d.permute π) (r.permute π) a
        (τ.transport hμ π) = forcedAvailability hμ c hcard hsize hmerger d r a τ := by
  apply ConeIdeal.ext
  ext n
  erw [mem_forcedAvailability,mem_forcedAvailability,forcedAvailable_permute_iff]

variable {q : Diagram M I}

/-- This permutation is allowed to move the component as well as its chain. -/
theorem stableAt_permute (E : (S).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (g : Vertex.RootGroup q) (d : CohenForcing.Condition I κ) (w : Vertex q) (τ : (S).Name)
    (h : StableAt hμ c hcard hsize hmerger E d w τ) :
    StableAt hμ c hcard hsize hmerger E (g • d) (g • w) (g • τ) := by
  obtain ⟨ρ,rfl,hel,hs⟩ := h
  refine ⟨ρ.transport hμ g.val,rfl,?_,?_⟩
  · change (S).Forces ![g.val • ρ.name,labelSet hμ c,E]
      ((d.permute g.val,w.diagram.permute g.val) : Poset M I κ) (SetLanguage.isClass 0 1 2)
    have hv : (fun i => g.val • (![ρ.name,labelSet hμ c,E] : Fin 3 → (S).Name) i) =
        ![g.val • ρ.name,labelSet hμ c,E] := by
      funext i
      fin_cases i
      · rfl
      · exact smul_labelSet hμ c g.val
      · exact hE g.val g.property
    simpa only [move_coe,permute,hv] using
      ((S).forces_symmetry g.val (SetLanguage.isClass 0 1 2)
        ![ρ.name,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)).mp hel
  · change ∀ e, e ≤ d.permute g.val → forcedAvailability hμ c hcard hsize hmerger e
        (w.diagram.permute g.val) w.index (ρ.transport hμ g.val) = w.ideal
    intro e he
    have hed : e.permute g.val⁻¹ ≤ d := by
      have hh := (CohenForcing.Condition.permuteOrderIso g.val⁻¹).monotone he
      change e.permute g.val⁻¹ ≤ (d.permute g.val).permute g.val⁻¹ at hh
      simpa only [CohenForcing.Condition.permute_inv_permute] using hh
    have hh := forcedAvailability_permute hμ c hcard hsize hmerger g.val
      (e.permute g.val⁻¹) w.diagram w.index ρ
    simpa only [CohenForcing.Condition.permute_permute_inv] using hh.trans (hs _ hed)

theorem stableAt_permute_iff (E : (S).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (g : Vertex.RootGroup q) (d : CohenForcing.Condition I κ) (w : Vertex q) (τ : (S).Name) :
    StableAt hμ c hcard hsize hmerger E (g • d) (g • w) (g • τ) ↔
      StableAt hμ c hcard hsize hmerger E d w τ := by
  constructor
  · intro h
    have hh := stableAt_permute hμ c hcard hsize hmerger E hE g⁻¹ (g • d) (g • w) (g • τ) h
    simpa only [inv_smul_smul] using hh
  · exact stableAt_permute hμ c hcard hsize hmerger E hE g d w τ

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrbitAssignments
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CorrectedDensity -/

/-! Exactness and the two density directions for the coset-corrected
assignment. Selector density and ordinal counts are discharged for the
concrete system in the following construction. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.componentStabilizer hj v
local notation "K" => C.tailFixer hj

/-- A corrected assignment has the actual permanent ideal at its vertex. -/
theorem corrected_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : LocalName hμ c w.diagram}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    StableAt hμ c hcard hsize hmerger E d w τ.name := by
  obtain ⟨g,hg,h⟩ := h
  have hp := preliminary_stable hμ c hcard hsize hmerger hj E hE C
    (d := g⁻¹ • d) (w := g.val⁻¹ • w) (j := g⁻¹ • j)
    (τ := τ.transport hμ g.val.val⁻¹) h
  have hs : StableAt hμ c hcard hsize hmerger E (g⁻¹ • d) (g.val⁻¹ • w) (g⁻¹ • τ.name) :=
    ⟨τ.transport hμ g.val.val⁻¹,rfl,hp.1,hp.2⟩
  exact (stableAt_permute_iff hμ c hcard hsize hmerger E hE g.val⁻¹ d w τ.name).mp hs

variable {hμ c hcard hsize hmerger hj E hE C}

omit [LinearOrder κ] [WellFoundedLT κ] in
theorem ordinalCount_mono {d e : CohenForcing.Condition I κ} (hed : e ≤ d)
    (h : OrdinalCount hμ c hcard hsize hmerger hj E hE C d) :
    OrdinalCount hμ c hcard hsize hmerger hj E hE C e :=
  fun f hfe θ hθ => h f (hfe.trans hed) θ hθ

variable (hμ c hcard hsize hmerger hj E hE C)

omit [Infinite M] [Infinite I] in
private theorem selected_exists (d : CohenForcing.Condition I κ)
    (hd : (C.tailData hj).Good d) :
    ∃ g : G, (C.tailData hj).Selected d (g : G ⧸ K) := by
  let g := ((C.tailData hj).conditionSelector d hd).out
  exact ⟨g,hd,(QuotientGroup.out_eq' _).symm⟩

/-- Dense totality, with both the ordinal computations and the selector
made at the actual moved condition. -/
theorem corrected_total (d : CohenForcing.Condition I κ)
    (hsel : ∀ d : CohenForcing.Condition I κ, ∃ e, e ≤ d ∧ (C.tailData hj).Good e)
    (hcount : ∀ g : G, OrdinalCount hμ c hcard hsize hmerger hj E hE C (g⁻¹ • d))
    (w : Vertex q) (hw : Vertex.Common v w) (j : labelFiberSet v) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      Corrected hμ c hcard hsize hmerger hj E hE C e w j τ.name := by
  obtain ⟨e,hed,he⟩ := hsel d
  obtain ⟨g,hg⟩ := selected_exists hj C e he
  have hged : g⁻¹ • e ≤ g⁻¹ • d :=
    (CohenForcing.Condition.permuteOrderIso g.val.val⁻¹).monotone hed
  obtain ⟨f,hfe,τ,hτ⟩ := preliminary_total hμ c hcard hsize hmerger hj E hE C (g⁻¹ • e)
    (ordinalCount_mono hged (hcount g)) (g⁻¹ • w) (Vertex.common_moved hj v g⁻¹ hw) (g⁻¹ • j)
  have hgf : g • f ≤ e := by
    have h := (CohenForcing.Condition.permuteOrderIso g.val.val).monotone hfe
    change g • f ≤ g • (g⁻¹ • e) at h
    simpa only [smul_inv_smul] using h
  let σ : LocalName hμ c w.diagram := (τ.transport hμ g.val.val).rebase hμ c
    (by
      change (g.val • (g.val⁻¹ • w)).diagram = w.diagram
      exact congrArg Vertex.diagram (smul_inv_smul g.val w))
  refine ⟨g • f,hgf.trans hed,σ,?_⟩
  apply (corrected_selected hμ c hcard hsize hmerger hj E hE C g (hg.mono _ hgf)).mpr
  change Preliminary hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • (g • f)) (g⁻¹ • w) (g⁻¹ • j) (g⁻¹ • (g • τ.name))
  simpa only [inv_smul_smul] using hτ

/-- Dense surjectivity onto every actual, permanently available local class. -/
theorem corrected_onto (d : CohenForcing.Condition I κ)
    (hsel : ∀ d : CohenForcing.Condition I κ, ∃ e, e ≤ d ∧ (C.tailData hj).Good e)
    (hcount : ∀ g : G, OrdinalCount hμ c hcard hsize hmerger hj E hE C (g⁻¹ • d))
    (w : Vertex q) (hw : Vertex.Common v w) (τ : (S).Name)
    (hs : StableAt hμ c hcard hsize hmerger E d w τ) :
    ∃ e, e ≤ d ∧ ∃ j : labelFiberSet v,
      Corrected hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨e,hed,he⟩ := hsel d
  obtain ⟨g,hg⟩ := selected_exists hj C e he
  obtain ⟨ρ,hρ,hel,hstable⟩ :=
    stableAt_permute hμ c hcard hsize hmerger E hE g.val⁻¹ d w τ hs
  have hged : g⁻¹ • e ≤ g⁻¹ • d :=
    (CohenForcing.Condition.permuteOrderIso g.val.val⁻¹).monotone hed
  have hhel : (S).Forces ![ρ.name,labelSet hμ c,E]
      ((g⁻¹ • e,(g⁻¹ • w).diagram) : Poset M I κ) (SetLanguage.isClass 0 1 2) := by
    rw [hρ]
    exact (S).atomic.forceFormula_mono (WithTop.coe_le_coe.mpr
      (show (g⁻¹ • e,(g⁻¹ • w).diagram) ≤ (g⁻¹ • d,(g⁻¹ • w).diagram) from ⟨hged,le_rfl⟩)) hel
  obtain ⟨a,ha,hl⟩ := exists_linked_working_of_stable hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • e) (g⁻¹ • w) (Vertex.common_moved hj v g⁻¹ hw) ρ hhel
    (fun f hfe => hstable f (hfe.trans hged))
  rw [hρ] at hl
  obtain ⟨f,hfe,j,hj⟩ := preliminary_onto hμ c hcard hsize hmerger hj E hE C (g⁻¹ • e)
    (ordinalCount_mono hged (hcount g)) (g⁻¹ • w) (g⁻¹ • τ) a ha hl
  have hgf : g • f ≤ e := by
    have h := (CohenForcing.Condition.permuteOrderIso g.val.val).monotone hfe
    change g • f ≤ g • (g⁻¹ • e) at h
    simpa only [smul_inv_smul] using h
  refine ⟨g • f,hgf.trans hed,g • j,?_⟩
  apply (corrected_selected hμ c hcard hsize hmerger _ E hE C g (hg.mono _ hgf)).mpr
  simpa only [inv_smul_smul] using hj

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## ComponentOrbit -/

/-! Orbits of actual contraction components, under the group fixing the
root diagram. Representatives and chains are chosen only once per orbit. -/
namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section
variable (hj : HasConditionalJoins (LeftDivOrder M))

theorem orbit_rep (a : ComponentOrbit (q := q) hj) : orbit hj (orbitRep hj a) = a :=
  Quotient.out_eq a

theorem orbit_eq {v w : Vertex q} : orbit hj v = orbit hj w ↔ OrbitRel hj v w :=
  Quotient.eq

end
end PartitionConsistency.LocalDiagramSystem.Vertex


/-! ## AllComponent -/

/-! Transport of the corrected assignment to an entire orbit of components.
The only ambiguity is the actual component stabilizer, whose covariance has
already been proved with the inverse-moved Cohen condition. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.RootGroup q

variable {hμ c hcard hsize hmerger hj E hE C}

theorem orbitAssignment_orbit {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) :
    Vertex.OrbitRel hj v w := by
  obtain ⟨g,k,_,h⟩ := h
  exact ⟨g⁻¹,corrected_common h⟩

theorem orbitAssignment_mono {d e : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (hed : e ≤ d) (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C e w j τ := by
  obtain ⟨g,k,hk,h⟩ := h
  exact ⟨g,k,hk,corrected_mono ((CohenForcing.Condition.permuteOrderIso g.val⁻¹).monotone hed) h⟩

variable (hμ c hcard hsize hmerger hj E hE C)

theorem orbitAssignment_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d z j τ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ := by
  obtain ⟨g,k,hk,h⟩ := h
  exact ⟨g,k,hk,corrected_restrict hμ c hcard hsize hmerger hj E hE C (f.move g⁻¹) h⟩

theorem orbitAssignment_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ.name) :
    StableAt hμ c hcard hsize hmerger E d w τ.name := by
  obtain ⟨g,k,_,h⟩ := h
  have hs := corrected_stable hμ c hcard hsize hmerger hj E hE C
    (d := g⁻¹ • d) (w := g⁻¹ • w) (τ := τ.transport hμ g.val⁻¹) h
  exact (stableAt_permute_iff hμ c hcard hsize hmerger E hE g⁻¹ d w τ.name).mp hs

omit [Infinite M] [Infinite I] in
/-- Two transports to the same component differ by the full stabilizer. -/
theorem component_difference (g s : G) (w : Vertex q)
    (hg : Vertex.Common v (g⁻¹ • w)) (hs : Vertex.Common v (s⁻¹ • w)) :
    g⁻¹*s ∈ Vertex.componentStabilizer hj v := by
  have hh : Vertex.Common ((g⁻¹*s) • v) (g⁻¹ • w) := by
    simpa only [mul_smul,smul_inv_smul] using hs.move (g⁻¹*s)
  exact hg.trans hj hh.symm

/-- The transport is unambiguous even when its two witnesses use unrelated
coordinate permutations. Both injectivity and single-valuedness are retained. -/
theorem orbitAssignment_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q} {j j' : I} {τ σ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ)
    (h' : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j' σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = j' := by
  obtain ⟨g,k,hk,h⟩ := h
  obtain ⟨s,l,hl,h'⟩ := h'
  let a : Vertex.componentStabilizer hj v :=
    ⟨g⁻¹*s,component_difference hj g s w (corrected_common h) (corrected_common h')⟩
  have hm := corrected_permute hμ c hcard hsize hmerger hj E hE C a
    (s⁻¹ • d) (s⁻¹ • w) l (s⁻¹ • σ) h'
  have hm' : Corrected hμ c hcard hsize hmerger hj E hE C
      (g⁻¹ • d) (g⁻¹ • w) (a • l) (g⁻¹ • σ) := by
    change Corrected hμ c hcard hsize hmerger hj E hE C
      ((g⁻¹*s) • (s⁻¹ • d)) ((g⁻¹*s) • (s⁻¹ • w)) (a • l) ((g⁻¹*s) • (s⁻¹ • σ)) at hm
    simpa only [mul_smul,smul_inv_smul] using hm
  rw [← root_eq_symmetry hμ g⁻¹ d w τ σ,corrected_eq_iff hμ c hcard hsize hmerger hj E hE C h hm']
  constructor
  · intro he
    have hv := congrArg (fun x : labelFiberSet v => g • x.val) he
    change g • k.val = g • ((g⁻¹*s) • l.val) at hv
    simpa only [mul_smul,smul_inv_smul,hk,hl] using hv
  · intro he
    apply Subtype.ext
    change k.val = (g⁻¹*s) • l.val
    apply (MulAction.injective g)
    simpa only [mul_smul,smul_inv_smul,hk,hl] using he

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## OrbitDensity -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.RootGroup q

/-- Totality after transporting to any component in the orbit. -/
theorem orbitAssignment_total_at (d : CohenForcing.Condition I κ) (w : Vertex q) (g : G)
    (hw : Vertex.Common v (g⁻¹ • w))
    (hsel : ∀ e : CohenForcing.Condition I κ, ∃ f, f ≤ e ∧ (C.tailData hj).Good f)
    (hcount : ∀ a : Vertex.componentStabilizer hj v,
      OrdinalCount hμ c hcard hsize hmerger hj E hE C (a⁻¹ • (g⁻¹ • d)))
    (j : I) (hjw : j ∈ labelFiberSet w) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      OrbitAssignment hμ c hcard hsize hmerger hj E hE C e w j τ.name := by
  have hk : (g⁻¹ • j) ∈ labelFiberSet v := by
    rw [labelFiberSet_common hj hw]
    exact (labelFiberSet_permute g⁻¹ w j).mp hjw
  let k : labelFiberSet v := ⟨g⁻¹ • j,hk⟩
  obtain ⟨f,hfd,τ,hτ⟩ := corrected_total hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • d) hsel hcount (g⁻¹ • w) hw k
  have hgf : g • f ≤ d := by
    have hh := (CohenForcing.Condition.permuteOrderIso g.val).monotone hfd
    change g • f ≤ g • (g⁻¹ • d) at hh
    simpa only [smul_inv_smul] using hh
  let σ : LocalName hμ c w.diagram := (τ.transport hμ g.val).rebase hμ c
    (by
      change (g • (g⁻¹ • w)).diagram = w.diagram
      exact congrArg Vertex.diagram (smul_inv_smul g w))
  refine ⟨g • f,hgf,σ,g,k,by exact smul_inv_smul g j,?_⟩
  change Corrected hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • (g • f)) (g⁻¹ • w) k (g⁻¹ • (g • τ.name))
  simpa only [inv_smul_smul] using hτ

/-- Surjectivity after orbital transport, still only onto an actual local
class with its permanent availability ideal. -/
theorem orbitAssignment_onto_at (d : CohenForcing.Condition I κ) (w : Vertex q) (g : G)
    (hw : Vertex.Common v (g⁻¹ • w))
    (hsel : ∀ e : CohenForcing.Condition I κ, ∃ f, f ≤ e ∧ (C.tailData hj).Good f)
    (hcount : ∀ a : Vertex.componentStabilizer hj v,
      OrdinalCount hμ c hcard hsize hmerger hj E hE C (a⁻¹ • (g⁻¹ • d)))
    (τ : (S).Name) (hs : StableAt hμ c hcard hsize hmerger E d w τ) :
    ∃ e, e ≤ d ∧ ∃ j : I,
      OrbitAssignment hμ c hcard hsize hmerger hj E hE C e w j τ := by
  have hs' := stableAt_permute hμ c hcard hsize hmerger E hE g⁻¹ d w τ hs
  obtain ⟨f,hfd,k,hk⟩ := corrected_onto hμ c hcard hsize hmerger hj E hE C
    (g⁻¹ • d) hsel hcount (g⁻¹ • w) hw (g⁻¹ • τ) hs'
  have hgf : g • f ≤ d := by
    have hh := (CohenForcing.Condition.permuteOrderIso g.val).monotone hfd
    change g • f ≤ g • (g⁻¹ • d) at hh
    simpa only [smul_inv_smul] using hh
  refine ⟨g • f,hgf,g • k.val,g,k,rfl,?_⟩
  simpa only [inv_smul_smul] using hk

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## GlobalAssignment -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

variable {hμ c hcard hsize hmerger hj H E hE}

theorem assigned_mono {d e : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (he : e ≤ d) (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ) :
    Assigned hμ c hcard hsize hmerger hj H E hE e w j τ := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_mono he ha⟩

variable (hμ c hcard hsize hmerger hj H E hE)

theorem assigned_restrict {d : CohenForcing.Condition I κ} {w z : Vertex q}
    (f : w.Arrow z) {j : I} {τ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d z j τ) :
    Assigned hμ c hcard hsize hmerger hj H E hE d w j τ := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_restrict hμ c hcard hsize hmerger hj E hE _ f ha⟩

theorem assigned_stable {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name) :
    StableAt hμ c hcard hsize hmerger E d w τ.name := by
  obtain ⟨a,ha⟩ := h
  exact orbitAssignment_stable hμ c hcard hsize hmerger hj E hE _ ha

private theorem orbitAssignment_index (a : Vertex.ComponentOrbit (q := q) hj)
    {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) d w j τ) :
    a = Vertex.orbit hj w := by
  rw [← Vertex.orbit_rep hj a,Vertex.orbit_eq]
  exact orbitAssignment_orbit h

theorem assigned_eq_iff {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j k : I} {τ σ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ)
    (h' : Assigned hμ c hcard hsize hmerger hj H E hE d w k σ) :
    (S).atomic.EqF ((d,w.diagram) : Poset M I κ) τ σ ↔ j = k := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  have hab := (orbitAssignment_index hμ c hcard hsize hmerger hj H E hE a ha).trans
    (orbitAssignment_index hμ c hcard hsize hmerger hj H E hE b hb).symm
  subst b
  exact orbitAssignment_eq_iff hμ c hcard hsize hmerger hj E hE _ ha hb

/-- Uniform count and selector hypotheses give totality on every vertex;
there is no orbit omitted from the chosen graph. -/
theorem assigned_total (d : CohenForcing.Condition I κ)
    (hsel : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ e : CohenForcing.Condition I κ,
      ∃ f, f ≤ e ∧ ((Vertex.orbitChain hj H a).tailData hj).Good f)
    (hcount : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ g : Vertex.RootGroup q,
      OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) (g • d))
    (w : Vertex q) (j : I) (hjw : j ∈ labelFiberSet w) :
    ∃ e, e ≤ d ∧ ∃ τ : LocalName hμ c w.diagram,
      Assigned hμ c hcard hsize hmerger hj H E hE e w j τ.name := by
  let a := Vertex.orbit hj w
  have hrel : Vertex.OrbitRel hj (Vertex.orbitRep hj a) w :=
    (Vertex.orbit_eq hj).mp (Vertex.orbit_rep hj a)
  obtain ⟨g,hg⟩ := hrel
  obtain ⟨e,hed,τ,hτ⟩ := orbitAssignment_total_at hμ c hcard hsize hmerger hj E hE
    (Vertex.orbitChain hj H a) d w g⁻¹ (by simpa only [inv_inv] using hg) (hsel a)
    (fun s => by
      change OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a)
        (s.val⁻¹ • ((g⁻¹)⁻¹ • d))
      simpa only [mul_smul,inv_inv] using hcount a (s.val⁻¹ * g)) j hjw
  exact ⟨e,hed,τ,a,hτ⟩

theorem assigned_onto (d : CohenForcing.Condition I κ)
    (hsel : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ e : CohenForcing.Condition I κ,
      ∃ f, f ≤ e ∧ ((Vertex.orbitChain hj H a).tailData hj).Good f)
    (hcount : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ g : Vertex.RootGroup q,
      OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) (g • d))
    (w : Vertex q) (τ : (S).Name) (hs : StableAt hμ c hcard hsize hmerger E d w τ) :
    ∃ e, e ≤ d ∧ ∃ j : I, Assigned hμ c hcard hsize hmerger hj H E hE e w j τ := by
  let a := Vertex.orbit hj w
  have hrel : Vertex.OrbitRel hj (Vertex.orbitRep hj a) w :=
    (Vertex.orbit_eq hj).mp (Vertex.orbit_rep hj a)
  obtain ⟨g,hg⟩ := hrel
  obtain ⟨e,hed,j,hj⟩ := orbitAssignment_onto_at hμ c hcard hsize hmerger hj E hE
    (Vertex.orbitChain hj H a) d w g⁻¹ (by simpa only [inv_inv] using hg) (hsel a)
    (fun s => by
      change OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a)
        (s.val⁻¹ • ((g⁻¹)⁻¹ • d))
      simpa only [mul_smul,inv_inv] using hcount a (s.val⁻¹ * g)) τ hs
  exact ⟨e,hed,j,a,hj⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## AssignmentCompatibility -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
noncomputable section

theorem labelVertex_mem {q : Diagram M I} (r : Diagram M I) (a : M) (ha : r.sub a = q)
    (j : I) (hj : j ∈ r.range) : j ∈ labelFiberSet (labelVertex r a ha j hj) :=
  ⟨⟨⟨j,hj⟩,rfl⟩,rfl⟩

/-- Enlarging a diagram induces the unique contraction carrying the
exact label fiber back to its original vertex. -/
theorem labelVertex_arrow {q : Diagram M I} (r : Diagram M I) (a : M) (ha : r.sub a = q)
    (w : Vertex q) (hrw : r ≤ w.diagram) (j : I) (hj : j ∈ labelFiberSet w) :
    Nonempty ((labelVertex r a ha j (Diagram.range_antitone hrw (labelFiberSet_subset w hj))).Arrow w) := by
  obtain ⟨x,hx⟩ := hj
  subst j
  obtain ⟨n,hn⟩ := hrw
  have hna : n*w.index = a := by
    apply Diagram.index_unique (r := r)
    rw [← Diagram.sub_sub,hn,w.root,ha]
  refine ⟨⟨n,?_,hn,?_⟩⟩
  · change (show LeftDivOrder M from n) ≤ a ∧ _
    refine ⟨⟨w.index,hna⟩,?_⟩
    rw [label_available_iff,hn]
    exact x.val.property
  · intro t
    have ht := Set.ext_iff.mp (congrArg ConeIdeal.carrier x.property) t
    change t ∈ w.ideal.carrier ↔ _
    rw [← ht]
    change (t ≤ (show LeftDivOrder M from w.index) ∧ _) ↔
      ((show LeftDivOrder M from n)*t ≤ a ∧ _)
    erw [label_available_iff,label_available_iff,← hna,LeftDivOrder.mul_le_mul_left_iff]
    erw [← Diagram.sub_sub,hn]

end
end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

theorem assigned_ideal {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name) :
    forcedAvailability hμ c hcard hsize hmerger d w.diagram w.index τ = w.ideal := by
  obtain ⟨ρ,he,_,hs⟩ := assigned_stable hμ c hcard hsize hmerger hj H E hE h
  have he' : ρ = τ := LocalName.ext he
  subst ρ
  exact hs d le_rfl

/-- Passing to a stronger diagram uses the actual label availability ideal,
so no arbitrary identification between enlarged fibers is made. -/
theorem assigned_at_extension {d e : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name)
    (he : e ≤ d) (r : Diagram M I) (a : M) (ha : r.sub a = q) (hrw : r ≤ w.diagram) :
    Assigned hμ c hcard hsize hmerger hj H E hE e
      (labelVertex r a ha j (Diagram.range_antitone hrw (labelFiberSet_subset w (assigned_label h))))
      j (τ.restrict hrw).name := by
  obtain ⟨f⟩ := labelVertex_arrow r a ha w hrw j (assigned_label h)
  exact assigned_restrict hμ c hcard hsize hmerger hj H E hE f (assigned_mono he h)

/-- Compatible graph entries with the same literal label always have the
same value, even if they were computed at different diagrams and components. -/
theorem assigned_compatible_one {d e f : CohenForcing.Condition I κ} {w z : Vertex q}
    {j : I} {τ : LocalName hμ c w.diagram} {σ : LocalName hμ c z.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name)
    (h' : Assigned hμ c hcard hsize hmerger hj H E hE e z j σ.name)
    (hfd : f ≤ d) (hfe : f ≤ e) (r : Diagram M I) (hrw : r ≤ w.diagram) (hrz : r ≤ z.diagram) :
    (S).atomic.EqF ((f,r) : Poset M I κ) τ.name σ.name := by
  obtain ⟨a,ha⟩ := hrw.trans (show w.diagram ≤ q from ⟨w.index,w.root⟩)
  have h₁ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h hfd r a ha hrw
  have h₂ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h' hfe r a ha hrz
  exact (assigned_eq_iff hμ c hcard hsize hmerger hj H E hE h₁ h₂).mpr rfl

/-- Equal values at a common extension have equal permanent availability
ideals, hence lie in one and the same fiber and have equal labels. -/
theorem assigned_compatible_inj {d e f : CohenForcing.Condition I κ} {w z : Vertex q}
    {j k : I} {τ : LocalName hμ c w.diagram} {σ : LocalName hμ c z.diagram}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name)
    (h' : Assigned hμ c hcard hsize hmerger hj H E hE e z k σ.name)
    (hfd : f ≤ d) (hfe : f ≤ e) (r : Diagram M I) (hrw : r ≤ w.diagram) (hrz : r ≤ z.diagram)
    (heq : (S).atomic.EqF ((f,r) : Poset M I κ) τ.name σ.name) : j = k := by
  obtain ⟨a,ha⟩ := hrw.trans (show w.diagram ≤ q from ⟨w.index,w.root⟩)
  let w₁ := labelVertex r a ha j (Diagram.range_antitone hrw (labelFiberSet_subset w (assigned_label h)))
  let w₂ := labelVertex r a ha k (Diagram.range_antitone hrz (labelFiberSet_subset z (assigned_label h')))
  have h₁ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h hfd r a ha hrw
  have h₂ := assigned_at_extension hμ c hcard hsize hmerger hj H E hE h' hfe r a ha hrz
  have hU : w₁.ideal = w₂.ideal :=
    (assigned_ideal hμ c hcard hsize hmerger hj H E hE (τ := τ.restrict hrw) h₁).symm.trans
      ((forcedAvailability_congr hμ c hcard hsize hmerger f r a (τ.restrict hrw) (σ.restrict hrz) heq).trans
        (assigned_ideal hμ c hcard hsize hmerger hj H E hE (τ := σ.restrict hrz) h₂))
  have hw : w₁ = w₂ := by
    change (⟨r,a,ha,w₁.ideal⟩ : Vertex q) = ⟨r,a,ha,w₂.ideal⟩
    rw [hU]
  change Assigned hμ c hcard hsize hmerger hj H E hE f w₂ k σ.name at h₂
  rw [← hw] at h₂
  exact (assigned_eq_iff hμ c hcard hsize hmerger hj H E hE h₁ h₂).mp heq

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_AssignedGraphs
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## AssignedGraph -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

theorem graphWitness_mono {p r : Poset M I κ} {x y : (S).Name} (hr : r ≤ p)
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    GraphWitness hμ c hcard hsize hmerger hj H E hE r x y := by
  obtain ⟨d,w,j,τ,hp,ha,hx,hy⟩ := h
  exact ⟨d,w,j,τ,hr.trans hp,ha,(S).atomic.eq_mono hr hx,(S).atomic.eq_mono hr hy⟩

theorem graphWitness_holds {p : Poset M I κ} {x y : (S).Name}
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x y :=
  fun r hr => ⟨r,le_rfl,graphWitness_mono hμ c hcard hsize hmerger hj H E hE hr h⟩

/-- Each literal entry really has its value in the quotient set. -/
theorem graphWitness_bounds {p : Poset M I κ} {x y : (S).Name}
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    (S).atomic.MemF p x (labelSet hμ c) ∧ (S).atomic.MemF p y (quotientName hμ c E) := by
  obtain ⟨d,w,j,τ,hp,ha,hx,hy⟩ := h
  obtain ⟨_,_,hclass,_⟩ := assigned_stable hμ c hcard hsize hmerger hj H E hE ha
  exact ⟨((S).atomic.mem_congr hx ((S).atomic.eq_refl p _)).mpr (label_mem_labelSet hμ c j p),
    ((S).atomic.mem_congr hy ((S).atomic.eq_refl p _)).mpr
      ((S).atomic.mem_mono hp ((mem_quotientName_iff_isClass hμ c E τ.name _).mpr hclass))⟩

/-- Single-valuedness is proved at common extensions of actual diagram
entries; no common preassigned component is assumed. -/
theorem graphRelation_one [Uncountable κ] (hc : Function.Injective c)
    {p : Poset M I κ} {x y z : (S).Name}
    (h : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x y)
    (h' : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x z) :
    (S).atomic.EqF p y z := by
  let : Nonempty (Diagram M I) := ⟨q⟩
  apply (S).atomic_regular.1
  intro r hr
  obtain ⟨s,hs,d,w,j,τ,hsp,ha,hxj,hyτ⟩ := h r hr
  obtain ⟨t,ht,e,v,k,σ,htp,hb,hxk,hzσ⟩ := h' s (hs.trans hr)
  obtain ⟨a,hat⟩ := exists_condition_below t
  have haj := WithTop.coe_le_coe.mp (hat.trans (ht.trans hsp))
  have hak := WithTop.coe_le_coe.mp (hat.trans htp)
  have hjk : j = k := by
    by_contra hn
    exact label_not_equal hμ c hc hn (a : Poset M I κ)
      ((S).atomic.eq_trans ((S).atomic.eq_symm ((S).atomic.eq_mono (hat.trans ht) hxj))
        ((S).atomic.eq_mono hat hxk))
  subst k
  have heq := assigned_compatible_one hμ c hcard hsize hmerger hj H E hE ha hb
    haj.1 hak.1 a.2 haj.2 hak.2
  exact ⟨a,(hat.trans ht).trans hs,(S).atomic.eq_trans
    ((S).atomic.eq_mono (hat.trans ht) hyτ)
    ((S).atomic.eq_trans heq ((S).atomic.eq_symm ((S).atomic.eq_mono hat hzσ)))⟩

/-- Equal graph values have equal labels, even before the cardinality
conditions used to prove totality have been imposed. -/
theorem graphRelation_inj {p : Poset M I κ} {x y z : (S).Name}
    (h : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x z)
    (h' : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p y z) :
    (S).atomic.EqF p x y := by
  let : Nonempty (Diagram M I) := ⟨q⟩
  apply (S).atomic_regular.1
  intro r hr
  obtain ⟨s,hs,d,w,j,τ,hsp,ha,hxj,hzτ⟩ := h r hr
  obtain ⟨t,ht,e,v,k,σ,htp,hb,hyk,hzσ⟩ := h' s (hs.trans hr)
  obtain ⟨a,hat⟩ := exists_condition_below t
  have haj := WithTop.coe_le_coe.mp (hat.trans (ht.trans hsp))
  have hak := WithTop.coe_le_coe.mp (hat.trans htp)
  have heq := (S).atomic.eq_trans
    ((S).atomic.eq_symm ((S).atomic.eq_mono (hat.trans ht) hzτ)) ((S).atomic.eq_mono hat hzσ)
  have hjk := assigned_compatible_inj hμ c hcard hsize hmerger hj H E hE ha hb
    haj.1 hak.1 a.2 haj.2 hak.2 heq
  subst k
  exact ⟨a,(hat.trans ht).trans hs,(S).atomic.eq_trans
    ((S).atomic.eq_mono (hat.trans ht) hxj) ((S).atomic.eq_symm ((S).atomic.eq_mono hat hyk))⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## GraphDensity -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
variable (e₀ : M)
variable (hcomp : Cardinal.mk ((Set.range (fun x : M => e₀*x))ᶜ : Set M) = Cardinal.mk M)
variable (d₀ : CohenForcing.Condition I κ)
variable (hsel : ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ e : CohenForcing.Condition I κ,
  ∃ f, f ≤ e ∧ ((Vertex.orbitChain hj H a).tailData hj).Good f)
variable (hcount : ∀ d : CohenForcing.Condition I κ, d ≤ d₀ →
  ∀ a : Vertex.ComponentOrbit (q := q) hj, ∀ g : Vertex.RootGroup q,
    OrdinalCount hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) (g • d))

include e₀ hcomp hsel hcount

/-- All label coordinates can be covered by strengthened diagrams. Thus
dense local totality gives totality of the one actual graph. -/
theorem graphRelation_total (x : (S).Name) (p : Poset M I κ)
    (hp : p ≤ (d₀,q)) (hx : (S).atomic.MemF p x (labelSet hμ c)) :
    ∀ r, r ≤ p → ∃ s, s ≤ r ∧ ∃ y : (S).Name,
      (S).atomic.MemF s y (quotientName hμ c E) ∧
      (graphRelation hμ c hcard hsize hmerger hj H E hE).holds s x y := by
  intro r hr
  obtain ⟨s,hs,j,hxj⟩ := (mem_labelSet hμ c x p).mp hx r hr
  let : Nonempty (Diagram M I) := ⟨q⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  have ha := WithTop.coe_le_coe.mp ((has.trans hs).trans (hr.trans hp))
  have hsizej : Cardinal.mk ({j} : Set I) ≤ Cardinal.mk M := by
    simpa only [Cardinal.mk_singleton] using
      Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk M)
  obtain ⟨t,hta,hjt⟩ := Diagram.extend_through hsize e₀ hcomp a.2 hsizej
  have ht : t ≤ a.2 := ⟨e₀,hta⟩
  obtain ⟨b,hb⟩ := ht.trans ha.2
  let w := labelVertex t b hb j (hjt (Set.mem_singleton j))
  obtain ⟨d,hda,τ,hA⟩ := assigned_total hμ c hcard hsize hmerger hj H E hE a.1 hsel
    (hcount a.1 ha.1) w j (labelVertex_mem t b hb j (hjt (Set.mem_singleton j)))
  have hds : ((d,t) : Poset M I κ) ≤ s := (WithTop.coe_le_coe.mpr (show (d,t) ≤ a from ⟨hda,ht⟩)).trans has
  have hw : GraphWitness hμ c hcard hsize hmerger hj H E hE (d,t) x τ.name :=
    ⟨d,w,j,τ,le_rfl,hA,(S).atomic.eq_mono hds hxj,(S).atomic.eq_refl _ _⟩
  exact ⟨(d,t),hds.trans hs,τ.name,
    (graphWitness_bounds hμ c hcard hsize hmerger hj H E hE hw).2,
    graphWitness_holds hμ c hcard hsize hmerger hj H E hE hw⟩

/-- Every actual quotient member is locally a canonical class of some label.
After placing that label in a diagram and stabilizing availability, the
onto assertion for its exact fiber supplies a graph preimage. -/
theorem graphRelation_onto (y : (S).Name) (p : Poset M I κ)
    (hp : p ≤ (d₀,q)) (hy : (S).atomic.MemF p y (quotientName hμ c E)) :
    ∀ r, r ≤ p → ∃ s, s ≤ r ∧ ∃ x : (S).Name,
      (S).atomic.MemF s x (labelSet hμ c) ∧
      (graphRelation hμ c hcard hsize hmerger hj H E hE).holds s x y := by
  intro r hr
  obtain ⟨s,hs,j,hyj⟩ := (mem_quotientName hμ c E y p).mp hy r hr
  let : Nonempty (Diagram M I) := ⟨q⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  have ha := WithTop.coe_le_coe.mp ((has.trans hs).trans (hr.trans hp))
  have hsizej : Cardinal.mk ({j} : Set I) ≤ Cardinal.mk M := by
    simpa only [Cardinal.mk_singleton] using
      Cardinal.one_le_aleph0.trans (Cardinal.aleph0_le_mk M)
  obtain ⟨t,hta,hjt⟩ := Diagram.extend_through hsize e₀ hcomp a.2 hsizej
  have ht : t ≤ a.2 := ⟨e₀,hta⟩
  obtain ⟨b,hb⟩ := ht.trans ha.2
  have hEt := supported_mono hμ (ht.trans ha.2) E hE
  let τ := localLabelClass hμ c t E hEt j (hjt (Set.mem_singleton j))
  obtain ⟨d,hda,hstable⟩ := forcedAvailability_dense_stable hμ c hcard hsize hmerger H hj
    a.1 t b τ
  let w : Vertex q := ⟨t,b,hb,forcedAvailability hμ c hcard hsize hmerger d t b τ⟩
  have hτ : StableAt hμ c hcard hsize hmerger E d w τ.name :=
    ⟨τ,rfl,forces_localLabelClass_isClass hμ c t E hEt j (hjt (Set.mem_singleton j)) (d,t),hstable⟩
  obtain ⟨f,hfd,k,hA⟩ := assigned_onto hμ c hcard hsize hmerger hj H E hE d hsel
    (hcount d (hda.trans ha.1)) w τ.name hτ
  have hfs : ((f,t) : Poset M I κ) ≤ s :=
    (WithTop.coe_le_coe.mpr (show (f,t) ≤ a from ⟨hfd.trans hda,ht⟩)).trans has
  have hw : GraphWitness hμ c hcard hsize hmerger hj H E hE (f,t) (label hμ c k) y :=
    ⟨f,w,k,τ,le_rfl,hA,(S).atomic.eq_refl _ _,(S).atomic.eq_mono hfs hyj⟩
  exact ⟨(f,t),hfs.trans hs,label hμ c k,label_mem_labelSet hμ c k ((f,t) : Poset M I κ),
    graphWitness_holds hμ c hcard hsize hmerger hj H E hE hw⟩

/-- Under the explicitly stated dense count and selector facts the actual
HS graph is a bijection. These facts are discharged for the concrete monoid
and forcing in the construction, rather than being model axioms. -/
theorem assignmentGraph_bijection [Uncountable κ] (hc : Function.Injective c) :
    (S).Forces ![assignmentGraph hμ c hcard hsize hmerger hj H E hE,
      labelSet hμ c,quotientName hμ c E] ((d₀,q) : Poset M I κ)
      ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  apply And.intro
  · apply (graphRelation hμ c hcard hsize hmerger hj H E hE).graph_surjection
    · exact graphRelation_total hμ c hcard hsize hmerger hj H E hE e₀ hcomp d₀ hsel hcount
    · intro p _ x y z
      exact graphRelation_one hμ c hcard hsize hmerger hj H E hE hc
    · exact graphRelation_onto hμ c hcard hsize hmerger hj H E hE e₀ hcomp d₀ hsel hcount
  · apply (graphRelation hμ c hcard hsize hmerger hj H E hE).graph_injection
    · exact graphRelation_total hμ c hcard hsize hmerger hj H E hE e₀ hcomp d₀ hsel hcount
    · intro p _ x y z
      exact graphRelation_one hμ c hcard hsize hmerger hj H E hE hc
    · intro p _ x y z
      exact graphRelation_inj hμ c hcard hsize hmerger hj H E hE

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## CountableHull -/

/-! Small hulls for countably-ary operations, used for the chain condition of
countable Cohen forcing. The construction is a genuine well-founded term
algebra; no elementary-submodel or large-cardinal assumption is needed. -/
namespace PartitionConsistency.CountableHull
universe u
noncomputable section
open scoped Classical
variable {A X : Type u}

/-- Closure under any small family of countably-ary operations has size at
most a fixed point of countable exponentiation. -/
theorem exists_closed {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpower : μ ^ Cardinal.aleph0 = μ) (hA : Cardinal.mk A ≤ μ)
    (base : X) (op : A → (ℕ → X) → X) :
    ∃ S : Set X, Cardinal.mk S ≤ μ ∧ base ∈ S ∧
      ∀ a f, (∀ n, f n ∈ S) → op a f ∈ S := by
  have hlabels : Cardinal.mk (Option A) ≤ μ := by
    simpa only [Cardinal.mk_option] using
      (add_le_add hA (Cardinal.one_le_aleph0.trans hω)).trans_eq (Cardinal.add_eq_self hω)
  have harity (a : Option A) : Cardinal.mk (Arity a) ≤ Cardinal.aleph0 := by
    cases a <;> simp [Arity]
  have htree : Cardinal.mk (WType (@Arity A)) ≤ μ := by
    apply WType.cardinalMk_le_of_le
    calc
      Cardinal.sum (fun a : Option A => μ ^ Cardinal.mk (Arity a)) ≤
          Cardinal.sum (fun _ : Option A => μ) := by
        apply Cardinal.sum_le_sum
        intro a
        exact (Cardinal.power_le_power_left (ne_of_gt (Cardinal.aleph0_pos.trans_le hω)) (harity a)).trans_eq hpower
      _ = Cardinal.mk (Option A) * μ := by simp
      _ ≤ μ * μ := mul_le_mul' hlabels le_rfl
      _ = μ := Cardinal.mul_eq_self hω
  refine ⟨Set.range (evaluate base op),?_,?_,?_⟩
  · exact Cardinal.mk_range_le.trans htree
  · exact ⟨WType.mk none PEmpty.elim,rfl⟩
  · intro a f hf
    choose t ht using hf
    exact ⟨WType.mk (some a) (fun n => t n.down),by
      change op a (fun n => evaluate base op (t n)) = op a f
      exact congrArg (op a) (funext ht)⟩

end
end PartitionConsistency.CountableHull


/-! ## CohenChain -/

/-! Chain condition for the actual countable Cohen conditions. The small
hull is a well-founded term algebra, so this proof adds no hypothesis about
an elementary submodel or a delta-system. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

private theorem code_range (d : Condition I κ) :
    Set.range (code d) = Set.insert none (Option.some '' d.graph) :=
  (exists_code d).choose_spec

private theorem enriched_graph_injective : Function.Injective
    (fun d : Condition I κ => Set.insert none (Option.some '' d.graph)) := by
  intro d e h
  apply ext
  ext z
  have hz := Set.ext_iff.mp h (some z)
  change (some z = none ∨ ∃ x ∈ d.graph, some x = some z) ↔
    (some z = none ∨ ∃ x ∈ e.graph, some x = some z) at hz
  simpa only [Option.some_ne_none,Option.some.injEq,exists_eq_right,false_or] using hz

private theorem code_injective : Function.Injective (code (I := I) (κ := κ)) := by
  intro d e h
  apply enriched_graph_injective
  dsimp only
  rw [← code_range,← code_range,h]

private theorem decode_code (d : Condition I κ) : decode (code d) = d := by
  have h : ∃ e : Condition I κ,
      Set.range (code d) = Set.insert none (Option.some '' e.graph) := ⟨d,code_range d⟩
  rw [decode,dite_eq_left h]
  exact enriched_graph_injective (h.choose_spec.symm.trans (code_range d))

private theorem compatibleChoice_spec (A : Set (Condition I κ)) (d : Condition I κ)
    (h : ∃ e ∈ A, Compatible d e) :
    compatibleChoice A d ∈ A ∧ Compatible d (compatibleChoice A d) := by
  rw [compatibleChoice,dite_eq_left h]
  exact h.choose_spec

/-- Every pairwise incompatible set of countable binary conditions has size
at most any infinite fixed point of countable exponentiation. In particular
the forcing is `(2^ℵ₀)⁺`-c.c., irrespective of its coordinate set. -/
theorem antichain_cardinal_le {μ : Cardinal.{u}} (hω : Cardinal.aleph0 ≤ μ)
    (hpower : μ ^ Cardinal.aleph0 = μ) (A : Set (Condition I κ))
    (hA : ∀ p ∈ A, ∀ q ∈ A, Compatible p q → p = q) : Cardinal.mk A ≤ μ := by
  let op (a : ULift.{u} (Bool × ℕ)) (f : ℕ → Option ((I × κ) × Bool)) :=
    if a.down.1 then code (compatibleChoice A (decode f)) a.down.2 else flip (f a.down.2)
  have hops : Cardinal.mk (ULift.{u} (Bool × ℕ)) ≤ μ := by
    simpa only [Cardinal.mk_uLift,Cardinal.mk_prod,Cardinal.mk_bool,Cardinal.mk_nat,
      Cardinal.lift_aleph0,Cardinal.lift_id,Cardinal.ofNat_mul_aleph0] using hω
  obtain ⟨S,hS,hnone,hclosed⟩ :=
    CountableHull.exists_closed hω hpower hops (none : Option ((I × κ) × Bool)) op
  have hflip (z : Option ((I × κ) × Bool)) (hz : z ∈ S) : flip z ∈ S :=
    hclosed ⟨(false,0)⟩ (fun _ => z) (fun _ => hz)
  have hbits (a : I × κ) (b c : Bool) (h : some (a,b) ∈ S) : some (a,c) ∈ S := by
    cases b <;> cases c
    · exact h
    · exact hflip _ h
    · exact hflip _ h
    · exact h
  have hcode {d : Condition I κ} (hs : ∀ z ∈ d.graph, some z ∈ S) :
      ∀ n, code d n ∈ S := by
    intro n
    have hn := Set.range_subset_iff.mp (show Set.range (code d) ⊆ S by
      rw [code_range]
      exact Set.insert_subset hnone (by rintro _ ⟨z,hz,rfl⟩; exact hs z hz)) n
    exact hn
  have hin (p : Condition I κ) (hp : p ∈ A) : ∀ z ∈ p.graph, some z ∈ S := by
    let d := restrictedGraph p S
    have hd : Compatible d p := fun a b c hb hc => p.functional a b c hb.1 hc
    have hb := compatibleChoice_spec A d ⟨p,hp,hd⟩
    let b := compatibleChoice A d
    have hbS (n : ℕ) : code b n ∈ S := by
      have hh := hclosed ⟨(true,n)⟩ (code d) (hcode (fun z hz => hz.2))
      simpa [op,decode_code,b] using hh
    have hbgraph (z : (I × κ) × Bool) (hz : z ∈ b.graph) : some z ∈ S := by
      have hr : some z ∈ Set.range (code b) := by
        rw [code_range]
        exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hz)
      obtain ⟨n,hn⟩ := hr
      exact hn ▸ hbS n
    have hbp : Compatible p b := by
      intro a x y hx hy
      apply hb.2 a x y ⟨hx,?_⟩ hy
      exact hbits a y x (hbgraph _ hy)
    have he : p = b := hA p hp b hb.1 hbp
    exact he ▸ hbgraph
  let pack (p : A) : ℕ → S := fun n => ⟨code p.val n,hcode (hin p.val p.property) n⟩
  have hpack : Function.Injective pack := by
    intro p q h
    apply Subtype.ext
    apply code_injective
    exact funext (fun n => congrArg Subtype.val (congrFun h n))
  calc
    Cardinal.mk A ≤ Cardinal.mk (ℕ → S) := Cardinal.mk_le_of_injective hpack
    _ = Cardinal.mk S ^ Cardinal.aleph0 := by simp
    _ ≤ μ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hS
    _ = μ := hpower

/-- The source chain condition, with its precise successor-continuum bound. -/
theorem antichain_continuum (A : Set (Condition I κ))
    (hA : ∀ p ∈ A, ∀ q ∈ A, Compatible p q → p = q) :
    Cardinal.mk A ≤ Cardinal.continuum :=
  antichain_cardinal_le Cardinal.aleph0_le_continuum Cardinal.continuum_power_aleph0 A hA

end
end PartitionConsistency.CohenForcing.Condition


/-! ## ChainPreservation -/

/-! Cardinal preservation from the actual chain condition. The statements
below concern the internal set-graph surjection sentence and arbitrary name
ranks. No existence of an ambient fully generic filter is used. -/
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v
noncomputable section
open ForcingQuotient
variable {P : Type u} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
/-- A separating family of conditions injects into an antichain. -/
theorem ChainBound.cardinal_le {ν : Cardinal.{u}} (hcc : ChainBound (P := P) ν)
    {X : Type u} (c : X → P)
    (hc : ∀ x y, Compatible (c x) (c y) → x = y) : Cardinal.mk X ≤ ν := by
  have hinj : Function.Injective c := by
    intro x y he
    exact hc x y ⟨c x,le_rfl,he ▸ le_rfl⟩
  let pack : X → Set.range c := fun x => ⟨c x,⟨x,rfl⟩⟩
  have hp : Function.Injective pack := fun x y he => hinj (congrArg Subtype.val he)
  apply (Cardinal.mk_le_of_injective hp).trans
  exact hcc _ (by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ h
    exact congrArg c (hc x y h))

omit [OrderTop P] in
/-- Counting an indexed relation whose witnesses with compatible conditions
and equal records must have the same value. -/
theorem ChainBound.cardinal_le_mul {ν : Cardinal.{u}} (hcc : ChainBound (P := P) ν)
    {A B : Type u} (R : P → A → B → Prop)
    (total : ∀ b, ∃ a p, R p a b)
    (single : ∀ a b b' p q, R p a b → R q a b' → Compatible p q → b = b') :
    Cardinal.mk B ≤ Cardinal.mk A * ν := by
  let V (a : A) := {b : B // ∃ p, R p a b}
  have hV (a : A) : Cardinal.mk (V a) ≤ ν := by
    let c : V a → P := fun b => b.property.choose
    apply hcc.cardinal_le c
    intro b b' hc
    apply Subtype.ext
    exact single a b.val b'.val (c b) (c b') b.property.choose_spec b'.property.choose_spec hc
  let pack : B → Σ a : A, V a := fun b => ⟨(total b).choose,⟨b,(total b).choose_spec⟩⟩
  have hi : Function.Injective pack := by
    intro b b' he
    exact congrArg (fun t : Σ a : A, V a => t.2.val) he
  calc
    Cardinal.mk B ≤ Cardinal.mk (Σ a : A, V a) := Cardinal.mk_le_of_injective hi
    _ = Cardinal.sum (fun a : A => Cardinal.mk (V a)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : A => ν) := Cardinal.sum_le_sum _ _ hV
    _ = Cardinal.mk A * ν := by simp

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_CodeCardinals
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeCardinal -/

/-! The upper bound for the actual name for the persistent code order type.
Its possible ordinal values are bounded by literal representation records
and the proved chain condition of the countable Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

namespace ChainCode
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

/-- Every decided value of the literal ordinal-type name has ground
cardinality at most μ. Neither genericity nor a supply of representatives
is an assumption: the needed records are obtained by density. -/
theorem ordinalType_cardinal_le (hpower : μ ^ Cardinal.aleph0 = μ)
    (hκ : Cardinal.mk κ ≤ μ) (b : M)
    (hb : Cardinal.mk ((Set.range (fun x : M => b*x))ᶜ : Set M) = Cardinal.mk M)
    (d : CohenForcing.Condition I κ) (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hj E hE C) (Name.check θ.toZFSet)) :
    θ.card ≤ μ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let toIio : θ.ToType ≃ Set.Iio θ := Ordinal.ToType.mk.toEquiv.symm
  let R (e : CohenForcing.Condition I κ) (rec : LocalRecord (M := M) (κ := κ))
      (β : θ.ToType) : Prop :=
    ∃ a : Index hμ c C, ∃ τ : LocalName hμ c v.diagram,
      IsSelected hμ c hcard hsize hmerger hj E hE C a e ∧
      Rooted hμ c C (code hμ c C a) e τ ∧
      S.atomic.EqF ((e,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hj E hE C a) (Name.check (toIio β).val.toZFSet) ∧
      ∃ w : LocalWitness hμ (principalFilter e) v.diagram (labelClass hμ c E) τ, w.record = rec
  have total (β : θ.ToType) : ∃ rec e, R e rec β := by
    obtain ⟨e,hed,a,ha,hea⟩ := member_ordinalRank hμ c hcard hsize hmerger hj E hE C d θ hθ (toIio β)
    obtain ⟨τ,hτ,hrooted⟩ := working_rooted hμ c hcard hsize hmerger hj E hE C e (code hμ c C a) ha.1
    obtain ⟨f,hfe,t,⟨m,hm⟩,hs,j,⟨x,rfl⟩,heq⟩ :=
      classRepresentationSet_denseBelow hμ c hsize b hb v.diagram E τ e hτ e le_rfl
    let w : LocalWitness hμ (principalFilter f) v.diagram (labelClass hμ c E) τ :=
      ⟨t,m,hm,x,f,(mem_principalFilter _ _).mpr le_rfl,hs,heq⟩
    refine ⟨w.record,f,a,τ,isSelected_mono hμ c hcard hsize hmerger hj E hE C hfe ha,
      rooted_mono hfe hrooted,?_,w,rfl⟩
    exact S.atomic.eq_mono
      (WithTop.coe_le_coe.mpr (show (f,v.diagram) ≤ (e,v.diagram) from ⟨hfe,le_rfl⟩)) hea
  have single (rec : LocalRecord (M := M) (κ := κ)) (β γ : θ.ToType)
      (p p' : CohenForcing.Condition I κ) (hp : R p rec β) (hp' : R p' rec γ)
      (hcompat : ForcingQuotient.Compatible p p') : β = γ := by
    obtain ⟨a,τ,ha,hta,hea,w,hw⟩ := hp
    obtain ⟨a',σ,ha',htb,heb,w',hw'⟩ := hp'
    obtain ⟨f,hfp,hfp'⟩ := hcompat
    have heq : LocalQuotient.ofName (principalFilter f) τ = LocalQuotient.ofName (principalFilter f) σ :=
      LocalWitness.equal_of_record_eq hsize hmerger
        (by
          intro π hπ j
          rw [labelClass_move,supported_mono hμ ⟨v.index,v.root⟩ E hE π hπ])
        (w.below hfp) (w'.below hfp') (hw.trans hw'.symm)
    have hτσ : S.atomic.EqF ((f,v.diagram) : Poset M I κ) τ.name σ.name :=
      ((localAtomic hμ v.diagram).eqG_principal f _ _).mp
        ((LocalQuotient.ofName_eq (principalFilter f) τ σ).mp heq)
    have hs : Same hμ c C f (code hμ c C a) (code hμ c C a') :=
      (rooted_eq_iff_same hsize hmerger (rooted_mono hfp hta) (rooted_mono hfp' htb)).mp hτσ
    have haa : a = a' := (code hμ c C).injective
      (selected_unique hμ c hcard hsize hmerger hj E hE C
        (isSelected_mono hμ c hcard hsize hmerger hj E hE C hfp ha)
        (isSelected_mono hμ c hcard hsize hmerger hj E hE C hfp' ha') hs)
    subst a'
    have hle : ((f,v.diagram) : Poset M I κ) ≤ ((p,v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hfp,le_rfl⟩
    have hle' : ((f,v.diagram) : Poset M I κ) ≤ ((p',v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hfp',le_rfl⟩
    apply toIio.injective
    apply Subtype.ext
    apply Ordinal.toZFSet_injective
    exact (S.eq_check_iff _ _ ((f,v.diagram) : Poset M I κ)).mp
      (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hle hea)) (S.atomic.eq_mono hle' heb))
  have hcc : ChainBound (P := CohenForcing.Condition I κ) μ := by
    intro A hA
    exact CohenForcing.Condition.antichain_cardinal_le hμ hpower A (by
      intro p hp q hq hc
      exact hA p hp q hq (CohenForcing.Condition.compatible_iff.mp hc))
  have hrec : Cardinal.mk (LocalRecord (M := M) (κ := κ)) ≤ μ := by
    change Cardinal.mk (M × M × CohenForcing.Condition M κ) ≤ μ
    simp only [Cardinal.mk_prod,Cardinal.lift_id]
    exact (mul_le_mul' hcard
      ((mul_le_mul' hcard (CohenForcing.Condition.cardinal_le hμ hpower hcard hκ)).trans_eq
        (Cardinal.mul_eq_self hμ))).trans_eq (Cardinal.mul_eq_self hμ)
  calc
    θ.card = Cardinal.mk θ.ToType := (Cardinal.mk_toType θ).symm
    _ ≤ Cardinal.mk (LocalRecord (M := M) (κ := κ)) * μ := hcc.cardinal_le_mul R total single
    _ ≤ μ * μ := mul_le_mul' hrec le_rfl
    _ = μ := Cardinal.mul_eq_self hμ

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## CodeLower -/

/-! The lower bound for the actual persistent-code ordinal. Independent
probe rows give distinct ranks whenever their witnessing conditions are
compatible. The countable Cohen chain bound then gives the cardinal estimate,
without postulating a filter meeting an ambient uncountable family. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hjoin : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable {v : Vertex q} (C : Vertex.Chain v)

omit [Infinite M] [Infinite I] in
/-- Changing a code within its forced equivalence class preserves its
root representative. Equality is reflected along the actual chain arrows. -/
theorem rooted_of_same {a b : ChainCode hμ c C} {d : CohenForcing.Condition I κ}
    {τ : LocalName hμ c v.diagram} (ha : Rooted hμ c C a d τ) (hs : Same hμ c C d a b) :
    Rooted hμ c C b d τ := by
  obtain ⟨N,hN⟩ := ha
  obtain ⟨L,hL⟩ := hs
  refine ⟨max N L,?_⟩
  intro i hi
  have hr : v.diagram ≤ (C.vertex i).diagram := by
    obtain ⟨f⟩ := C.increasing 0 i (Nat.zero_le i)
    simpa only [C.first] using (show (C.vertex 0).diagram ≤ (C.vertex i).diagram from ⟨f.index,f.diagram⟩)
  exact (system hμ).atomic.eq_trans
    ((system hμ).atomic.eq_symm ((system hμ).atomic.eq_mono
      (WithTop.coe_le_coe.mpr (show (d,v.diagram) ≤ (d,(C.vertex i).diagram) from ⟨le_rfl,hr⟩))
      (hL i ((le_max_right _ _).trans hi)))) (hN i ((le_max_left _ _).trans hi))

/-- For every probe row one can force a selected representative and its
ordinal rank. Equal possible ranks in compatible conditions force two probe
classes equal, contrary to the outside-list assertion and exact intersection. -/
theorem ordinalType_lower_count (e b : M) {K : Type u} [Uncountable K]
    (m : K × K → M) (hmb : ∀ i, m i*b = v.index*e)
    (hm : ∀ i (n : M), n ∣ v.index ∧ n ∣ m i ↔ n ∈ v.ideal.carrier)
    (hinter : ∀ i (n : M), n ∣ v.index → n ∉ v.ideal.carrier →
      ∀ z : M, n ∣ z ∧ m i ∣ z ↔ v.index*e ∣ z)
    (hind : ∀ i j, i ≠ j → ∀ z : M, m i ∣ z ∧ m j ∣ z ↔ v.index*e ∣ z)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub e).range, π • E = E)
    (t : Diagram M I) (ht : t.sub b = q.sub e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : Poset M I κ, z ≤ (d₀,t) →
      ¬ (system hμ).atomic.MemF z (labelClass hμ c E j) (localList hμ c hcard (q.sub e)))
    (d : CohenForcing.Condition I κ) (hd : d ≤ d₀.restrict (q.sub e).range)
    (θ : Ordinal.{u})
    (hθ : (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF ((d,v.diagram) : Poset M I κ)
      (ordinalType hμ c hcard hsize hmerger hjoin E
        (supported_mono hμ (q.self_le_sub e) E hE) C) (Name.check θ.toZFSet)) :
    Cardinal.mk K ≤ θ.card * Cardinal.continuum := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let hEq := supported_mono hμ (q.self_le_sub e) E hE
  let toIio : θ.ToType ≃ Set.Iio θ := Ordinal.ToType.mk.toEquiv.symm
  have hp : v.diagram.sub (v.index*e) = q.sub e := by rw [← Diagram.sub_sub,v.root]
  obtain ⟨d',σ,hs,hroot,hσ,hout'⟩ := outsideClass_copies hμ c hcard hsize
    (q.sub e) v.diagram v.index e b hp m hmb E hE t ht d₀ hd₀ j hj hout
  let τ (i : K × K) : LocalName hμ c v.diagram :=
    (σ i).restrict (v.diagram.self_le_sub (m i))
  have hdisj : Pairwise (fun i k : K × K => Disjoint
      ((d' i).support \ (q.sub e).range) ((d' k).support \ (q.sub e).range)) := by
    intro i k hik
    rw [Set.disjoint_left]
    rintro z ⟨hzi,hzp⟩ ⟨hzk,_⟩
    apply hzp
    have hi := v.diagram.range_inter_sub (m i) (m k) (v.index*e) (hind i k hik)
    rw [hp] at hi
    exact hi ▸ ⟨hs i hzi,hs k hzk⟩
  have hits (i : K) : ∃ f, f ≤ d ∧ ∃ k : K, f ≤ d' (i,k) := by
    let D := CohenForcing.Condition.probeDenseSet
      (d₀.restrict (q.sub e).range) (fun k : K => d' (i,k))
    have hD : Dense D := CohenForcing.Condition.probeDenseSet_dense (q.sub e).range
      (d₀.restrict (q.sub e).range) (fun k : K => d' (i,k)) (fun k => hroot (i,k))
      (fun x y hxy => hdisj (fun he => hxy (congrArg Prod.snd he)))
    obtain ⟨f,hfd,hf⟩ := hD d
    rcases hf with hf | hf
    · exact (hf (CohenForcing.Condition.compatible_iff.mpr ⟨f,le_rfl,hfd.trans hd⟩)).elim
    · exact ⟨f,hfd,hf⟩
  have hel (i : K × K) (f : CohenForcing.Condition I κ) :
      S.Forces ![(τ i).name,labelSet hμ c,E] ((f,v.diagram) : Poset M I κ)
        (SetLanguage.isClass 0 1 2) := hσ i _
  have stable (i : K × K) (f : CohenForcing.Condition I κ) (hfi : f ≤ d' i) :
      forcedAvailability hμ c hcard hsize hmerger f v.diagram v.index (τ i) = v.ideal := by
    let F := principalFilter f
    have hi : d' i ∈ F := (mem_principalFilter _ _).mpr hfi
    have hσi : EligibleName hμ c F (v.diagram.sub (m i)) E (σ i) :=
      ⟨f,(mem_principalFilter _ _).mpr le_rfl,hσ i _⟩
    have hh := classFromLocal_profile hμ c hcard hsize hmerger F q v.diagram (q.sub e)
      v.index e (m i) b v.root hp (hmb i) v.ideal (hm i) (hinter i) E hEq
      (σ i) hσi (d' i) hi (hout' i)
    rw [eligibleSystem_availability_eq hμ c hcard hsize hmerger E hEq F
      v.diagram v.index v.root] at hh
    exact hh
  let R (f : CohenForcing.Condition I κ) (β : θ.ToType) (i : K) : Prop :=
    ∃ k : K, f ≤ d' (i,k) ∧ ∃ a : Index hμ c C,
      IsSelected hμ c hcard hsize hmerger hjoin E hEq C a f ∧
      Rooted hμ c C (code hμ c C a) f (τ (i,k)) ∧
      S.atomic.EqF ((f,v.diagram) : Poset M I κ)
        (ordinalRank hμ c hcard hsize hmerger hjoin E hEq C a) (Name.check (toIio β).val.toZFSet)
  have total (i : K) : ∃ β f, R f β i := by
    obtain ⟨f,hfd,k,hfk⟩ := hits i
    obtain ⟨a,ha,hτa⟩ := exists_working_code_of_stable hμ c hcard hsize hmerger E hEq hjoin C f
      (τ (i,k)) (hel (i,k) f) (fun g hgf => stable (i,k) g (hgf.trans hfk))
    obtain ⟨g,hgf,a',ha',hsame⟩ := dense_selected hμ c hcard hsize hmerger hjoin E hEq C f a ha
    let smallA : Index hμ c C := (code hμ c C).symm a'
    have hsmallA : IsSelected hμ c hcard hsize hmerger hjoin E hEq C smallA g := by
      simpa only [IsSelected,smallA,Equiv.apply_symm_apply] using ha'
    have hgθ : S.atomic.EqF ((g,v.diagram) : Poset M I κ)
        (ordinalType hμ c hcard hsize hmerger hjoin E hEq C) (Name.check θ.toZFSet) :=
      S.atomic.eq_mono
        (WithTop.coe_le_coe.mpr (show (g,v.diagram) ≤ (d,v.diagram) from ⟨hgf.trans hfd,le_rfl⟩)) hθ
    obtain ⟨z,hzg,β,hzβ⟩ := ordinalRank_decide hμ c hcard hsize hmerger hjoin E hEq C
      smallA g hsmallA θ hgθ
    refine ⟨toIio.symm β,z,k,(hzg.trans hgf).trans hfk,smallA,
      isSelected_mono hμ c hcard hsize hmerger hjoin E hEq C hzg hsmallA,?_,?_⟩
    · have har : Rooted hμ c C a f (τ (i,k)) := ⟨0,fun n _ => hτa n⟩
      have hbr := rooted_of_same hμ c C (rooted_mono hgf har) hsame
      simpa only [smallA,Equiv.apply_symm_apply] using rooted_mono hzg hbr
    · simpa only [Equiv.apply_symm_apply] using hzβ
  have single (β : θ.ToType) (i i' : K) (f g : CohenForcing.Condition I κ)
      (hf : R f β i) (hg : R g β i') (hfg : ForcingQuotient.Compatible f g) : i = i' := by
    obtain ⟨k,hfk,a,ha,hτa,heβ⟩ := hf
    obtain ⟨k',hgk,a',ha',hτb,heβ'⟩ := hg
    obtain ⟨z,hzf,hzg⟩ := hfg
    have hle : ((z,v.diagram) : Poset M I κ) ≤ ((f,v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hzf,le_rfl⟩
    have hle' : ((z,v.diagram) : Poset M I κ) ≤ ((g,v.diagram) : Poset M I κ) :=
      WithTop.coe_le_coe.mpr ⟨hzg,le_rfl⟩
    have hab : a = a' := (ordinalRank_eq_iff hμ c hcard hsize hmerger hjoin E hEq C a a' z
      (isSelected_mono hμ c hcard hsize hmerger hjoin E hEq C hzf ha)
      (isSelected_mono hμ c hcard hsize hmerger hjoin E hEq C hzg ha')).mp
        (S.atomic.eq_trans (S.atomic.eq_mono hle heβ) (S.atomic.eq_symm (S.atomic.eq_mono hle' heβ')))
    subst a'
    have heq : S.atomic.EqF ((z,v.diagram) : Poset M I κ) (τ (i,k)).name (τ (i',k')).name :=
      (rooted_eq_iff_same hsize hmerger (rooted_mono hzf hτa) (rooted_mono hzg hτb)).mpr
        (same_refl z _)
    by_contra hii
    have hneq : (i,k) ≠ (i',k') := fun h => hii (congrArg Prod.fst h)
    have hip (l : K × K) : v.diagram.sub (m l) ≤ q.sub e :=
      ⟨b,by rw [Diagram.sub_sub,hmb l,hp]⟩
    have hi : (v.diagram.sub (m (i,k))).range ∩ (v.diagram.sub (m (i',k'))).range = (q.sub e).range := by
      rw [← hp]
      exact v.diagram.range_inter_sub _ _ _ (hind _ _ hneq)
    apply outsideLocal_not_equal hμ c hcard hsize hmerger (principalFilter z) (q.sub e)
      (v.diagram.sub (m (i,k))) (v.diagram.sub (m (i',k'))) v.diagram
      (hip (i,k)) (hip (i',k')) hi (v.diagram.self_le_sub _) (v.diagram.self_le_sub _)
      (d' (i,k)) ((mem_principalFilter _ _).mpr (hzf.trans hfk)) (σ (i,k)) (hout' (i,k))
      (LocalQuotient.ofName (principalFilter z) (σ (i',k')))
    exact (LocalQuotient.ofName_eq (principalFilter z) (τ (i,k)) (τ (i',k'))).mpr
      (((localAtomic hμ v.diagram).eqG_principal z _ _).mpr heq)
  have hcc : ChainBound (P := CohenForcing.Condition I κ) Cardinal.continuum := by
    intro A hA
    exact CohenForcing.Condition.antichain_continuum A (by
      intro p hp q hq hc
      exact hA p hp q hq (CohenForcing.Condition.compatible_iff.mp hc))
  simpa only [Cardinal.mk_toType] using hcc.cardinal_le_mul R total single

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ConcreteQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellDescent -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder
noncomputable section

namespace Cell
variable {M : Object.{u}} (d : Cell M)

/-- The old-input gate rule for the literal cells. A merger has no new old
divisors; a probe's first-letter gate consumes all letters on an old input. -/
theorem descent_gate (w : d.extension) (hw : ∀ x, d.inclusion x ≠ w)
    (hb : ∃ y, w ∣ d.inclusion y) :
    ∃ g : M, w ∣ d.inclusion g ∧ (∀ y, w ∣ d.inclusion y → g ∣ y) ∧
      ∀ x, d.inclusion g ∣ w * d.inclusion x → ∃ y, w * d.inclusion x = d.inclusion y := by
  cases d with
  | inl d =>
    let A := d.path.alphabet d.e_ne_one
    change ProbeAlgebra.Word A d.b at w
    change ∀ x, ProbeAlgebra.Word.old A d.b x ≠ w at hw
    change ∃ y, w ∣ ProbeAlgebra.Word.old A d.b y at hb
    change ∃ g : M, w ∣ ProbeAlgebra.Word.old A d.b g ∧
      (∀ y, w ∣ ProbeAlgebra.Word.old A d.b y → g ∣ y) ∧
      ∀ x, ProbeAlgebra.Word.old A d.b g ∣ w * ProbeAlgebra.Word.old A d.b x →
        ∃ y, w * ProbeAlgebra.Word.old A d.b x = ProbeAlgebra.Word.old A d.b y
    obtain ⟨y,hy⟩ := hb
    cases hs : ProbeAlgebra.Word.head A d.b w with
    | none =>
      obtain ⟨x,hx⟩ := (ProbeAlgebra.Word.head_eq_none_iff A d.b w).mp hs
      exact (hw x hx.symm).elim
    | some s =>
      obtain ⟨g,hg⟩ := ProbeAlgebra.Word.exists_gate_of_exit A d.b
        (d.path.oldIntersections d.e_ne_one d.b M.joins) w hs hy (by intro h; cases h)
      exact ⟨g,ProbeAlgebra.Word.Gate.dvd A d.b hg,
        fun y hy => (ProbeAlgebra.Word.Gate.dvd_old_iff A d.b hg y).mp hy,
        fun x hx => ProbeAlgebra.Word.Gate.append_old A d.b hg hs x hx⟩
  | inr d =>
    obtain ⟨y,z,hz⟩ := hb
    obtain ⟨x,_,hx,_,_⟩ := MergerAlgebra.Word.factors_of_old hz.symm
    exact (hw x hx.symm).elim

end Cell
namespace Attachment
variable {T : Object.{u}} {S R : Subobject T} (d : Attachment S R)

include d in
/-- The same gate statement holds in the final monoid, by conservation of
divisibility, including for final right factors not yet present at this cut. -/
theorem gateStep : OldGateStep S.submonoid R.submonoid := by
  intro w hw hn hb
  let w₀ := d.equiv.symm (⟨w,hw⟩ : R.object)
  have hew : d.embedding w₀ = w := congrArg Subtype.val (d.equiv.apply_symm_apply ⟨w,hw⟩)
  have hnew : ∀ x, d.cell.inclusion x ≠ w₀ := by
    intro x hx
    apply hn
    have hh := congrArg d.embedding hx
    rw [d.embedding_old,hew] at hh
    exact hh ▸ x.property
  have hbound : ∃ y, w₀ ∣ d.cell.inclusion y := by
    obtain ⟨y,hy,hwy⟩ := hb
    refine ⟨⟨y,hy⟩,(d.embedding.conservative.dvd_iff _ _).mp ?_⟩
    erw [hew,d.embedding_old]
    exact hwy
  obtain ⟨g,hg,hleast,hinput⟩ := d.cell.descent_gate w₀ hnew hbound
  refine ⟨g.val,g.property,?_,?_,?_⟩
  · simpa only [hew,d.embedding_old] using d.embedding.map_dvd hg
  · intro y hy hwy
    have hh : w₀ ∣ d.cell.inclusion (⟨y,hy⟩ : S.object) :=
      (d.embedding.conservative.dvd_iff _ _).mp (by
        erw [d.embedding_old,hew]
        exact hwy)
    exact S.inclusion.map_dvd (hleast _ hh)
  · intro x hx hgd
    have hh : d.cell.inclusion g ∣ w₀ * d.cell.inclusion (⟨x,hx⟩ : S.object) :=
      (d.embedding.conservative.dvd_iff _ _).mp (by
        erw [d.embedding.map_mul,d.embedding_old,d.embedding_old,hew]
        exact hgd)
    obtain ⟨y,hy⟩ := hinput _ hh
    have hh := congrArg d.embedding hy
    erw [d.embedding.map_mul,d.embedding_old,d.embedding_old,hew] at hh
    exact hh.symm ▸ y.property

end Attachment

namespace CellTower
variable {T : Object.{u}} {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J] (D : CellTower T J) (n : ℕ → T) (A : Set (ℕ × T))

/-- Finite old-gate descent in a rearranged literal cell tower. Right factors
between base indices belong to the base by its conservative closure. -/
theorem finite_descent
    (hn : ∀ i, n i ∈ (D.stage ⊥).submonoid)
    (hbound : ∀ p ∈ A, ∃ N, p.2 ∣ n N)
    (hreplace : ∀ p ∈ A, ∀ N, ∃ l' d,
      (l',p.2*d) ∈ A ∧ p.1 ≤ l' ∧ n p.1*d = n l' ∧ n N ∣ p.2*d)
    (α : J) (p : ℕ × T) (hp : p ∈ A) (hα : p.2 ∈ (D.stage α).submonoid) :
    ∃ q ∈ A, q.2 ∈ (D.stage ⊥).submonoid ∧ Relation.ReflTransGen (Replaces n A) p q := by
  induction α using SuccOrder.limitRecOn generalizing p with
  | isMin α hmin => exact ⟨p,hp,hmin.eq_bot ▸ hα,Relation.ReflTransGen.refl⟩
  | succ α hne ih =>
    by_cases ho : p.2 ∈ (D.stage α).submonoid
    · exact ih p hp ho
    rcases D.step α with he | hcell
    · exact (ho (he ▸ hα)).elim
    · obtain ⟨N,hN⟩ := hbound p hp
      have hnN : n N ∈ (D.stage α).submonoid := D.mono bot_le (hn N)
      obtain ⟨g,_,_,hleast,hgate⟩ := hcell.some.gateStep p.2 hα ho ⟨n N,hnN,hN⟩
      obtain ⟨l',d,hA',hll',hd,hNd⟩ := hreplace p hp N
      have hdo : d ∈ (D.stage α).submonoid := D.mono bot_le (by
        rw [← ConservativeHull.factor_eq _ _ d hd]
        exact (D.stage ⊥).factors _ (hn _) _ (hn _))
      have hnew : p.2*d ∈ (D.stage α).submonoid := hgate d hdo ((hleast _ hnN hN).trans hNd)
      obtain ⟨q,hqA,hq0,hpath⟩ := ih (l',p.2*d) hA' hnew
      exact ⟨q,hqA,hq0,(Relation.ReflTransGen.single (show Replaces n A p (l',p.2*d) from
        ⟨hp,hA',hll',d,hd,rfl⟩)).trans hpath⟩
  | isSuccLimit α hlim ih =>
    obtain ⟨β,hβα,hmem⟩ := D.continuous α hlim p.2 hα
    exact ih β hβα p hp hmem

theorem finite_descent_terminal
    (hn : ∀ i, n i ∈ (D.stage ⊥).submonoid)
    (hbound : ∀ p ∈ A, ∃ N, p.2 ∣ n N)
    (hreplace : ∀ p ∈ A, ∀ N, ∃ l' d,
      (l',p.2*d) ∈ A ∧ p.1 ≤ l' ∧ n p.1*d = n l' ∧ n N ∣ p.2*d)
    (p : ℕ × T) (hp : p ∈ A) :
    ∃ q ∈ A, q.2 ∈ (D.stage ⊥).submonoid ∧ Relation.ReflTransGen (Replaces n A) p q := by
  apply D.finite_descent n A hn hbound hreplace ⊤ p hp
  rw [D.terminal]
  trivial

end CellTower
end
end PartitionConsistency.ConservativeMonoids


/-! ## GermActual -/

namespace PartitionConsistency.MonoidConstruction.Saturation
universe u
open ConservativeMonoids DiagramOrder
noncomputable section
variable (M : MonoidConstruction.Object.{u}) (K : Type u) [Nonempty K]

/-- The fully executed construction still begins with the given countable
base; flattening only inserts identity cuts between rounds. -/
theorem cells_bottom_countable [Countable M] :
    (((cells M K).stage ⊥).submonoid : Set (forgetMargins.obj (target M K))).Countable := by
  change ((blockStage M K (⊥ : RoundOrdinal) ⊥).submonoid : Set (forgetMargins.obj (target M K))).Countable
  rw [blockStage_base]
  let : Countable ((tower M K).obj ⊥) := (isoEquiv (botIso M K)).injective.countable
  exact Set.countable_range (fromStage M K ⊥)

end
end PartitionConsistency.MonoidConstruction.Saturation

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u
open DiagramOrder DiagramForcing ConservativeMonoids
noncomputable section
variable {M : Object.{u}} {I : Type u} {q : Diagram M I} {v : Vertex q}
variable (C : Chain v) {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J]

/-- Finite gate descent, now applied in a literal rearrangement of the
constructed monoid, bounds the actual germs by countably many alignments. -/
theorem countable_quotient_of_cells (D : CellTower M J)
    (hbot : ((D.stage ⊥).submonoid : Set M).Countable) :
    Countable (componentStabilizer M.joins v ⧸ C.tailFixer M.joins) := by
  obtain ⟨E,hbase,hn⟩ := D.countable_reordering hbot (Set.range C.index) (Set.countable_range _)
  have halign : ∀ π : componentStabilizer M.joins v,
      ∃ p : ℕ × (E.stage ⊥).submonoid, (p.1,p.2.val) ∈ C.Alignments M.joins π := by
    intro π
    obtain ⟨p,hp⟩ := C.alignments_nonempty M.joins π
    obtain ⟨a,ha,hmem,_⟩ := E.finite_descent_terminal C.index (C.Alignments M.joins π)
      (fun i => hn (Set.mem_range_self i))
      (fun p hp => C.alignment_bounded M.joins π hp)
      (fun p hp N => C.alignment_replacement M.joins π hp N) p hp
    exact ⟨(a.1,⟨a.2,hmem⟩),ha⟩
  let chooseCode (c : componentStabilizer M.joins v ⧸ C.tailFixer M.joins) :
      ℕ × (E.stage ⊥).submonoid := (halign c.out).choose
  have hcode (c : componentStabilizer M.joins v ⧸ C.tailFixer M.joins) :
      ((chooseCode c).1,(chooseCode c).2.val) ∈ C.Alignments M.joins c.out :=
    (halign c.out).choose_spec
  have hinj : Function.Injective chooseCode := by
    intro c e he
    have hc := hcode c
    rw [he] at hc
    have hh := C.coset_eq_of_alignment M.joins c.out e.out hc (hcode e)
    simpa only [QuotientGroup.mk'_apply,Quotient.out_eq] using hh
  let : Countable (E.stage ⊥).submonoid := hbase.to_subtype
  exact hinj.countable

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction LocalDiagramSystem
noncomputable section

/-- Countable germs for every local component in the actual final monoid;
no rearrangement, countable-base, or gate assumptions remain. -/
theorem countable_germs {q : DiagramForcing.Diagram T I} {v : Vertex q}
    (C : Vertex.Chain v) :
    Countable (Vertex.componentStabilizer T.joins v ⧸ C.tailFixer T.joins) := by
  let : Countable Base.object := show Countable (Multiplicative ℕ) from inferInstance
  exact LocalDiagramSystem.Vertex.Chain.countable_quotient_of_cells
    (M := ConservativeMonoids.forgetMargins.obj T) C (Saturation.cells Base.object K)
    (Saturation.cells_bottom_countable Base.object K)

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteSelector -/

/-! The selector for the actual saturated monoid and the prescribed Cohen
length. This supplies all countability/regularity hypotheses from the
construction, rather than leaving them as properties of an abstract action. -/
namespace PartitionConsistency.ConcreteSystem
open CardinalParameters DiagramForcing LocalDiagramSystem TailSelector
noncomputable section

theorem κ_countable_bound (f : ℕ → κ) : ∃ a : κ, ∀ n, f n < a :=
  CardinalParameters.countable_bound Cardinal.isRegular_aleph_one
    Cardinal.aleph0_lt_aleph_one f

theorem κ_initial_countable (a : κ) : (Set.Iio a).Countable := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  simpa only [κ,Cardinal.mk_toType,Cardinal.card_ord] using
    Cardinal.mk_Iio_lt a (by simp [κ])

variable {q : Diagram T I} {v : Vertex q} (C : Vertex.Chain v)

/-- Each actual component chain has a dense set of conditions at which the
least distinguishing-bound construction selects one of its countably many
residual symmetries. -/
theorem component_selector_dense (p : CohenForcing.Condition I κ) :
    ∃ r, r ≤ p ∧ (C.tailData T.joins).Good r := by
  let : Countable (C.tailData T.joins).Cosets := countable_germs C
  exact (C.tailData T.joins).good_dense κ_countable_bound κ_initial_countable p

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteCode -/

/-! The exact cardinality of the *actual ordinal name* for the persistent
least-code ordering in the executed concrete construction. No assertion of
genericity over an uncountable collection of ambient sets is used. -/
namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem SetForcingNames.SymmetricSystem
noncomputable section

/-- Every possible order type has cardinality exactly the label-fiber
cardinal. The hypotheses are just the outside-list condition at which the
quotient construction is made, and a stronger initial Cohen condition. -/
theorem code_ordinalType_cardinal {q : Diagram T I} {v : Vertex q} (C : Vertex.Chain v)
    (b : T) (hb : b ≠ 1) (E : S.Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d₀,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e)))
    (d : CohenForcing.Condition I κ) (hd : d ≤ d₀.restrict (q.sub T.e).range)
    (θ : Ordinal)
    (hθ : S.atomic.EqF ((d,v.diagram) : P)
      (ChainCode.ordinalType aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers
        T.joins E (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) C)
      (Name.check θ.toZFSet)) : θ.card = μ := by
  apply le_antisymm
  · exact ChainCode.ordinalType_cardinal_le aleph0_le_μ (posetCode κ) cardinal_T.le
      size_lt finiteMergers T.joins E
      (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) C μ_countable_power
      (cardinal_κ ▸ aleph_one_le_μ) T.e complement_cardinal d θ hθ
  · obtain ⟨m,_,hm,hi⟩ := Saturation.square_ideal_probes Base.object K v.index b hb v.ideal
    have hl := ChainCode.ordinalType_lower_count aleph0_le_μ (posetCode κ) cardinal_T.le
      size_lt finiteMergers T.joins C T.e b m (fun i => (hm i).1)
      (fun i => (hm i).2.2.1) (fun i => (hm i).2.2.2) hi E hE t ht d₀ hd₀ j hj hout d hd θ hθ
    rw [cardinal_K] at hl
    by_contra hn
    have hs : θ.card ≤ Cardinal.continuum := Order.lt_succ_iff.mp (lt_of_not_ge hn)
    have hc : μ ≤ Cardinal.continuum := hl.trans
      ((mul_le_mul' hs le_rfl).trans_eq (Cardinal.mul_eq_self Cardinal.aleph0_le_continuum))
    exact (Order.lt_succ Cardinal.continuum).not_ge hc

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcretePreAssignment -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem SetForcingNames.SymmetricSystem
noncomputable section

/-- The literal common label subset has the advertised cardinality, not
merely an abstract isomorphic fiber. -/
theorem labelFiberSet_cardinal {q : Diagram T I} (v : Vertex q) :
    Cardinal.mk (labelFiberSet v) = μ := by
  let f : (labelSystem (M := T) (I := I)).vertexFiber v → I := fun x => x.val.val
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have he : (labelSystem (M := T) (I := I)).vertexFiber v ≃ labelFiberSet v :=
    Equiv.ofInjective f hf
  rw [← Cardinal.mk_congr he]
  exact Saturation.labelFiber_cardinal Base.object K aleph_one_le_μ μ_countable_power
    (by change Cardinal.mk (Multiplicative ℕ) ≤ μ; simpa using aleph0_le_μ) cardinal_K v

/-- The count needed for assigning the preliminary ranks is supplied by the
executed construction and the outside-list condition. -/
theorem preliminary_ordinalCount {q : Diagram T I} {v : Vertex q} (C : Vertex.Chain v)
    (b : T) (hb : b ≠ 1) (E : S.Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d₀,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e)))
    (d : CohenForcing.Condition I κ) (hd : d ≤ d₀.restrict (q.sub T.e).range) :
    ChainCode.OrdinalCount aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers
      T.joins E (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) C d := by
  intro e hed θ he
  rw [labelFiberSet_cardinal v]
  exact code_ordinalType_cardinal C b hb E hE t ht d₀ hd₀ j hj hout e (hed.trans hd) θ he

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteQuotient -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem SetForcingNames.SymmetricSystem
noncomputable section

/-- All count and selector hypotheses of the equivariant assignment are
satisfied by the executed construction. The condition used for the graph
retains exactly the Cohen information in the smaller root. -/
theorem quotient_bijection_above (q : Diagram T I) (b : T) (hb : b ≠ 1) (E : S.Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d₀,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e))) :
    ∃ f : S.Name, S.Forces ![f,labelSet aleph0_le_μ (posetCode κ),
      quotientName aleph0_le_μ (posetCode κ) E] ((d₀.restrict (q.sub T.e).range,q) : P)
      ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  let dbase := d₀.restrict (q.sub T.e).range
  have hroot := supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE
  refine ⟨ChainCode.assignmentGraph aleph0_le_μ (posetCode κ) cardinal_T.le size_lt
    finiteMergers T.joins T.margin E hroot,?_⟩
  apply ChainCode.assignmentGraph_bijection aleph0_le_μ (posetCode κ) cardinal_T.le size_lt
    finiteMergers T.joins T.margin E hroot T.e complement_cardinal dbase
    (fun a d => component_selector_dense (Vertex.orbitChain T.joins T.margin a) d)
    (fun d hd a g => ?_) (posetCode_injective κ)
  apply preliminary_ordinalCount (Vertex.orbitChain T.joins T.margin a)
    b hb E hE t ht d₀ hd₀ j hj hout
  have hfix : dbase.permute g.val = dbase :=
    CohenForcing.Condition.permute_eq_of_fixes_support g.val dbase (fun k hk =>
      (SupportFilter.mem_Fix _ _).mp g.property k
        (Diagram.range_antitone (q.self_le_sub T.e) (d₀.support_restrict_subset _ hk)))
  change d.permute g.val ≤ dbase
  rw [← hfix]
  exact (CohenForcing.Condition.permuteOrderIso g.val).monotone hd

/-- Densely below every condition which forces a quotient to be nonwellorderable,
there is an actual supported graph bijecting the label set with that quotient.
There is no inaccessible-cardinal or quotient-classification premise. -/
theorem nonwellorderable_quotient_bijection (E : S.Name) (s : P)
    (hno : S.Forces ![quotientName aleph0_le_μ (posetCode κ) E] s
      (SetLanguage.wellorderable 0).neg) :
    ∃ r, r ≤ s ∧ ∃ f : S.Name,
      S.Forces ![f,labelSet aleph0_le_μ (posetCode κ),
        quotientName aleph0_le_μ (posetCode κ) E] r
        ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  obtain ⟨emb⟩ := (Cardinal.le_def T I).mp size_lt.le
  let : Nonempty (Diagram T I) := ⟨⟨emb⟩⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  obtain ⟨J,hJ,hfix⟩ := name_support aleph0_le_μ E
  have hU : Cardinal.mk ↥(J ∪ a.1.support) ≤ Cardinal.mk T := by
    rw [cardinal_T]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (a.1.cardinal_support.trans aleph0_le_μ)).trans_eq
        (Cardinal.add_eq_self aleph0_le_μ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through size_lt T.e complement_cardinal a.2 hU
  have hpa : p ≤ a.2 := ⟨T.e,hp⟩
  have hps : ((a.1,p) : P) ≤ s :=
    (WithTop.coe_le_coe.mpr (show (a.1,p) ≤ a from ⟨le_rfl,hpa⟩)).trans has
  have hEp : ∀ π ∈ SupportFilter.Fix p.range, π • E = E := by
    intro π hπ
    exact hfix π ((SupportFilter.mem_Fix _ _).mpr (fun k hk =>
      (SupportFilter.mem_Fix _ _).mp hπ k (hcover (Or.inl hk))))
  obtain ⟨d,hd,t,b,hb,hbn,hdt,j,hjt,hout⟩ := outsideClassSet_denseBelow
    aleph0_le_μ (posetCode κ) cardinal_T.le size_lt T.e complement_cardinal p E hEp a.1
      (S.atomic.forceFormula_mono hps hno) a.1 le_rfl
  obtain ⟨q,hq,_⟩ := Diagram.extend_through size_lt T.e complement_cardinal p
    (J := ∅) (by simp)
  have hroot : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E := by
    rwa [hq]
  obtain ⟨f,hf⟩ := quotient_bijection_above q b hbn E hroot t (hb.trans hq.symm)
    d hdt j hjt (by simpa only [S,hq] using hout)
  have hr : d.restrict (q.sub T.e).range ≤ a.1 := by
    intro z hz
    exact ⟨hd hz,by
      rw [hq]
      exact hcover (Or.inr ((CohenForcing.Condition.mem_support _ _).mpr
        ⟨z.1.2,z.2,hz⟩))⟩
  exact ⟨(d.restrict (q.sub T.e).range,q),
    (WithTop.coe_le_coe.mpr (show (d.restrict (q.sub T.e).range,q) ≤ (a.1,p)
      from ⟨hr,⟨T.e,hq⟩⟩)).trans hps,f,hf⟩

end
end PartitionConsistency.ConcreteSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_UniformImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## KernelImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem app_kernelGraph (h A B a b : S.Name) (p : P) :
    S.App p (S.kernelGraph h A B) a b ↔ (S.kernelRelation h A B).holds p a b := by
  unfold kernelGraph
  erw [BinaryRelation.app_graph]
  constructor
  · exact fun hi => hi.2.2
  · intro hi
    refine ⟨S.atomic_regular.2 _ _ _ ?_,S.atomic_regular.2 _ _ _ ?_,hi⟩
    · intro q hq
      obtain ⟨r,hrq,y,ha,_⟩ := hi q hq
      exact ⟨r,hrq,ha.1⟩
    · intro q hq
      obtain ⟨r,hrq,y,_,hb⟩ := hi q hq
      exact ⟨r,hrq,hb.1⟩

/-- Kernel membership says exactly equality of the actual function values;
no representatives of classes have been chosen. -/
theorem app_kernelGraph_value {h A B a y : S.Name} {p q : P}
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (ha : S.atomic.MemF q a A) (hay : S.App q h a y) (b : S.Name) :
    S.App q (S.kernelGraph h A B) a b ↔ S.atomic.MemF q b A ∧ S.App q h b y := by
  rw [S.app_kernelGraph]
  constructor
  · intro hi
    have hd r (hrq : r ≤ q) : ∃ s, s ≤ r ∧ S.atomic.MemF s b A ∧ S.App s h b y := by
      obtain ⟨s,hsr,z,has,hbs⟩ := hi r hrq
      have hzy := S.mapsTo_unique hf (hsr.trans (hrq.trans hq)) has.1 has.2.2
        (S.app_mono (hsr.trans hrq) hay)
      exact ⟨s,hsr,hbs.1,(S.app_congr (S.atomic.eq_refl s h) (S.atomic.eq_refl s b) hzy).mp hbs.2.2⟩
    exact ⟨S.atomic_regular.2 _ _ _ (fun r hr => (hd r hr).imp (fun s hs => ⟨hs.1,hs.2.1⟩)),
      (S.appRelation h).regular (fun r hr => (hd r hr).imp (fun s hs => ⟨hs.1,hs.2.2⟩))⟩
  · rintro ⟨hb,hby⟩ r hrq
    have hy := S.mapsTo_value hf hq ha hay
    exact ⟨r,le_rfl,y,⟨S.atomic.mem_mono hrq ha,S.atomic.mem_mono hrq hy,S.app_mono hrq hay⟩,
      ⟨S.atomic.mem_mono hrq hb,S.atomic.mem_mono hrq hy,S.app_mono hrq hby⟩⟩

theorem kernel_class_same_value {h A B a b y : S.Name} {p q : P}
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (ha : S.atomic.MemF q a A) (hb : S.atomic.MemF q b A)
    (hay : S.App q h a y) (hby : S.App q h b y) :
    S.atomic.EqF q (S.relationClass A (S.kernelGraph h A B) a)
      (S.relationClass A (S.kernelGraph h A B) b) := by
  apply S.eq_of_same_members
  intro x r hrq
  rw [S.mem_relationClass,S.mem_relationClass,
    S.app_kernelGraph_value hf (hrq.trans hq) (S.atomic.mem_mono hrq ha) (S.app_mono hrq hay),
    S.app_kernelGraph_value hf (hrq.trans hq) (S.atomic.mem_mono hrq hb) (S.app_mono hrq hby)]

theorem imageClassRelation_one (h A B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ y C D : S.Name,
      (S.imageClassRelation h A B).holds q y C →
      (S.imageClassRelation h A B).holds q y D → S.atomic.EqF q C D := by
  intro q hq y C D hC hD
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay,hCa⟩ := hC r hrq
  obtain ⟨t,hts,b,hb,hby,hDb⟩ := hD s (hsr.trans hrq)
  have hc := S.kernel_class_same_value hf (hts.trans (hsr.trans (hrq.trans hq)))
    (S.atomic.mem_mono hts ha) hb (S.app_mono hts hay) hby
  exact ⟨t,hts.trans hsr,S.atomic.eq_trans (S.atomic.eq_mono hts hCa)
    (S.atomic.eq_trans hc (S.atomic.eq_symm hDb))⟩

theorem imageClassRelation_inj (h A B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ y z C : S.Name,
      (S.imageClassRelation h A B).holds q y C →
      (S.imageClassRelation h A B).holds q z C → S.atomic.EqF q y z := by
  intro q hq y z C hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay,hCa⟩ := hy r hrq
  obtain ⟨t,hts,b,hb,hbz,hCb⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have ham := S.atomic.mem_mono hts ha
  have haym := S.app_mono hts hay
  have haa : S.atomic.MemF t a (S.relationClass A (S.kernelGraph h A B) a) :=
    (S.mem_relationClass _ _ _ _ _).mpr ⟨ham,
      (S.app_kernelGraph_value hf htp ham haym a).mpr ⟨ham,haym⟩⟩
  have heab := S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hts hCa)) hCb
  have hab := (S.mem_relationClass _ _ _ _ _).mp
    ((S.atomic.mem_congr (S.atomic.eq_refl t a) heab).mp haa)
  have haz := ((S.app_kernelGraph_value hf htp hb hbz a).mp hab.2).2
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp ham haym haz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

theorem mem_imageQuotient (h B C : S.Name) (p : P) :
    S.atomic.MemF p C (imageQuotient h B) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ a : S.Name,
        S.atomic.MemF r a A ∧ S.atomic.EqF r C (S.relationClass A (S.kernelGraph h A B) a) := by
  change (system aleph0_le_μ).atomic.MemF p C (quotientName _ _ _) ↔ _
  erw [mem_quotientName_iff_isClass]
  exact S.forces_isClass ![C,A,S.kernelGraph h A B] p 0 1 2

theorem app_imageQuotientGraph (h B y C : S.Name) (p : P) :
    S.App p (imageQuotientGraph h B) y C ↔
      S.atomic.MemF p y B ∧ S.atomic.MemF p C (imageQuotient h B) ∧
        (S.imageClassRelation h A B).holds p y C := by
  exact BinaryRelation.app_graph _ _ _ _ _ _ _ _ _ _ _

theorem imageQuotientGraph_mapsTo (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![imageQuotientGraph h B,B,imageQuotient h B] p (SetLanguage.mapsTo 0 1 2) := by
  unfold imageQuotientGraph
  apply BinaryRelation.graph_mapsTo
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,a,ha,hay⟩ := S.surjection_onto hf hq hy r hrq
    refine ⟨s,hsr,S.relationClass A (S.kernelGraph h A B) a,?_,?_⟩
    · exact (mem_imageQuotient _ _ _ _).mpr (fun t hts =>
        ⟨t,le_rfl,a,S.atomic.mem_mono hts ha,S.atomic.eq_refl t _⟩)
    · exact fun t hts => ⟨t,le_rfl,a,S.atomic.mem_mono hts ha,S.app_mono hts hay,S.atomic.eq_refl t _⟩
  · exact S.imageClassRelation_one h A B p (S.surjection_mapsTo hf)

theorem imageQuotientGraph_injection (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![imageQuotientGraph h B,B,imageQuotient h B] p (SetLanguage.injection 0 1 2) := by
  rw [S.forces_injection]
  refine ⟨imageQuotientGraph_mapsTo h B p hf,?_⟩
  rintro x y z q hq _ r hrq _ s hsr ⟨hx,hy⟩
  have hx := (app_imageQuotientGraph h B x z s).mp hx
  have hy := (app_imageQuotientGraph h B y z s).mp hy
  exact S.imageClassRelation_inj h A B p (S.surjection_mapsTo hf) s
    (hsr.trans (hrq.trans hq)) x y z hx.2.2 hy.2.2

theorem imageQuotientGraph_surjection (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![imageQuotientGraph h B,B,imageQuotient h B] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  refine ⟨imageQuotientGraph_mapsTo h B p hf,?_⟩
  intro C q hq hC r hrq
  obtain ⟨s,hsr,a,ha,he⟩ := (mem_imageQuotient h B C q).mp hC r hrq
  obtain ⟨t,hts,y,hy,hay⟩ := S.mapsTo_total (S.surjection_mapsTo hf) (hsr.trans (hrq.trans hq)) ha s le_rfl
  refine ⟨t,hts.trans hsr,y,hy,?_⟩
  apply (app_imageQuotientGraph h B y C t).mpr
  refine ⟨hy,S.atomic.mem_mono (hts.trans (hsr.trans hrq)) hC,?_⟩
  exact fun b hbt => ⟨b,le_rfl,a,S.atomic.mem_mono (hbt.trans hts) ha,
    S.app_mono hbt hay,S.atomic.eq_mono (hbt.trans hts) he⟩

/-- Every nonwellorderable image of A is now bijective to A. This is
obtained from the actual kernel quotient and its representative-free graph. -/
theorem nonwellorderable_image_bijection (h B : S.Name) (p : P)
    (hf : S.Forces ![h,A,B] p (SetLanguage.surjection 0 1 2))
    (hno : S.Forces ![B] p (SetLanguage.wellorderable 0).neg) :
    ∃ q, q ≤ p ∧ ∃ f : S.Name,
      S.Forces ![f,A,B] q ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  have hQ : S.Forces ![imageQuotient h B] p (SetLanguage.wellorderable 0).neg := by
    apply (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr
    intro q hq hwo
    obtain ⟨r,hrq,η,hη,hinj⟩ := (S.forces_wellorderable _ _ _).mp hwo q le_rfl
    obtain ⟨s,hsr,J,hJ⟩ := hinj r le_rfl
    have hB : S.Forces ![B] s (SetLanguage.wellorderable 0) := by
      rw [S.forces_wellorderable]
      intro t hts
      refine ⟨t,le_rfl,η,S.atomic.forceFormula_mono (hts.trans hsr) hη,?_⟩
      intro a hat
      refine ⟨a,le_rfl,S.compositionGraph (imageQuotientGraph h B) J B (imageQuotient h B) η,?_⟩
      exact S.compositionGraph_injection _ _ _ _ _ a
        (S.atomic.forceFormula_mono (hat.trans (hts.trans (hsr.trans (hrq.trans hq))))
          (imageQuotientGraph_injection h B p hf))
        (S.atomic.forceFormula_mono (hat.trans hts) hJ)
    exact (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mp hno s (hsr.trans (hrq.trans hq)) hB
  obtain ⟨q,hq,f,hf'⟩ := nonwellorderable_quotient_bijection (S.kernelGraph h A B) p hQ
  have hh := S.atomic.forceFormula_mono hq hf
  have hfi := (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mp hf'
  let J := S.inverseGraph (imageQuotientGraph h B) B (imageQuotient h B)
  have hJs := S.inverseGraph_surjection _ _ _ q (imageQuotientGraph_surjection h B q hh)
    (imageQuotientGraph_injection h B q hh)
  have hJi := S.inverseGraph_injection _ _ _ q (imageQuotientGraph_surjection h B q hh)
    (imageQuotientGraph_injection h B q hh)
  refine ⟨q,hq,S.compositionGraph f J A (imageQuotient h B) B,?_⟩
  apply (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mpr
  exact ⟨S.compositionGraph_surjection _ _ _ _ _ q hfi.1 hJs,
    S.compositionGraph_injection _ _ _ _ _ q hfi.2 hJi⟩

end
end PartitionConsistency.ConcreteSystem


/-! ## UniformMaximum -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- Simultaneous use of the localized maximum principle. The same larger
root is chosen before any witnesses, hence all the witnesses have one common
support, even for a ground family of arbitrarily large small cardinality. -/
theorem uniform_maximum_dense {ι : Sort*} {n} (φ : Formula (n+1))
    (v : ι → Fin n → S.Name) (H : Subgroup (Equiv.Perm I)) (hH : H ∈ S.filter)
    (hv : ∀ g ∈ H, ∀ i k, g • v i k = v i k)
    (t : P) (hf : ∀ i, S.Forces (v i) t φ.ex) :
    ∃ r, r ≤ t ∧ ∃ G : Subgroup (Equiv.Perm I), G ∈ S.filter ∧
      ∃ f : ι → S.Name, (∀ g ∈ G, ∀ i, g • f i = f i) ∧
        ∀ i, S.Forces (Fin.snoc (v i) (f i)) r φ := by
  obtain ⟨emb⟩ := (Cardinal.le_def T I).mp size_lt.le
  let : Nonempty (Diagram T I) := ⟨⟨emb⟩⟩
  obtain ⟨a,hat⟩ := exists_condition_below t
  obtain ⟨J,hJ,hJH⟩ := hH
  have hU : Cardinal.mk ↥(J ∪ a.1.support) ≤ Cardinal.mk T := by
    rw [cardinal_T]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (a.1.cardinal_support.trans aleph0_le_μ)).trans_eq
        (Cardinal.add_eq_self aleph0_le_μ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through size_lt T.e complement_cardinal a.2 hU
  have hpa : ((a.1,p) : P) ≤ t :=
    (WithTop.coe_le_coe.mpr (show (a.1,p) ≤ a from ⟨le_rfl,⟨T.e,hp⟩⟩)).trans hat
  obtain ⟨q,hq,_⟩ := Diagram.extend_through size_lt T.e complement_cardinal p
    (J := ∅) (by simp)
  have hqp : q ≤ p := ⟨T.e,hq⟩
  have hc : a.1.support ⊆ q.range := fun k hk => Diagram.range_antitone hqp (hcover (Or.inr hk))
  have hvec : ∀ g ∈ SupportFilter.Fix p.range, ∀ i k, g • v i k = v i k := by
    intro g hg
    exact hv g (hJH ((SupportFilter.mem_Fix _ _).mpr (fun k hk =>
      (SupportFilter.mem_Fix _ _).mp hg k (hcover (Or.inl hk)))))
  have hchoice : ∀ i, ∃ f : S.Name, (∀ g ∈ SupportFilter.Fix q.range, g • f = f) ∧
      S.Forces (Fin.snoc (v i) f) ((a.1,q) : P) φ := by
    intro i
    exact localized_maximum aleph0_le_μ cardinal_T size_lt finiteMergers T.e complement_cardinal
      rootProbes φ (v i) p q hq (fun g hg k => hvec g hg i k) a.1 hc
      (S.atomic.forceFormula_mono hpa (hf i))
  choose f hfix hforce using hchoice
  exact ⟨(a.1,q),(WithTop.coe_le_coe.mpr (show (a.1,q) ≤ (a.1,p) from ⟨le_rfl,hqp⟩)).trans hpa,
    SupportFilter.Fix q.range,⟨q.range,by rw [Diagram.cardinal_range,cardinal_T],le_rfl⟩,
    f,fun g hg i => hfix i g hg,hforce⟩

end
end PartitionConsistency.ConcreteSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrderedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## LeastOccurrence -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace LeastOccurrence
variable (X : ZFSet.{u}) (R : X → S.UnaryRelation)

omit [OrderTop P] in
theorem unique {p : P} {x : S.Name} {i j : X} (hi : At X R p x i) (hj : At X R p x j) : i = j := by
  rcases trichotomous_of WellOrderingRel i j with hh | hh | hh
  · exact (hj.2 i hh p le_rfl hi.1).elim
  · exact hh
  · exact (hi.2 j hh p le_rfl hj.1).elim

omit [OrderTop P] in
/-- Minimal compatible occurrence exists densely. -/
theorem dense (x : S.Name) (p : P)
    (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, At X R r x i := by
  intro q hq
  have hne : {i | ∃ r, r ≤ q ∧ (R i).holds r x}.Nonempty := by
    obtain ⟨r,hrq,i,hi⟩ := h q hq
    exact ⟨i,r,hrq,hi⟩
  obtain ⟨i,⟨r,hrq,hi⟩,hmin⟩ := WellOrderingRel.isWellOrder.wf.has_min _ hne
  exact ⟨r,hrq,i,hi,fun j hj s hsr hs => hmin j ⟨s,hsr.trans hrq,hs⟩ hj⟩

theorem relation_one {p : P} {x y z : S.Name}
    (hy : (relation X R).holds p x y) (hz : (relation X R).holds p x z) : S.atomic.EqF p y z := by
  apply S.atomic_regular.1
  intro q hq
  obtain ⟨r,hrq,i,hyi,hi⟩ := hy q hq
  obtain ⟨s,hsr,j,hzj,hj⟩ := hz r (hrq.trans hq)
  have hij := unique X R (mono X R hsr hi) hj
  subst j
  exact ⟨s,hsr.trans hrq,S.atomic.eq_trans (S.atomic.eq_mono hsr hyi) (S.atomic.eq_symm hzj)⟩

theorem relation_inj (p : P)
    (hone : ∀ i q, q ≤ p → ∀ x y, (R i).holds q x → (R i).holds q y → S.atomic.EqF q x y) :
    ∀ q, q ≤ p → ∀ x y z, (relation X R).holds q x z →
      (relation X R).holds q y z → S.atomic.EqF q x y := by
  intro q hq x y z hx hy
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,i,hzi,hi⟩ := hx r hrq
  obtain ⟨t,hts,j,hzj,hj⟩ := hy s (hsr.trans hrq)
  have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val t).mp
    (S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hts hzi)) hzj))
  subst j
  exact ⟨t,hts.trans hsr,hone i t (hts.trans (hsr.trans (hrq.trans hq))) x y
    ((R i).mono hts hi.1) hj.1⟩

theorem relation_move (H : Subgroup Γ)
    (hR : ∀ g ∈ H, ∀ i p x, (R i).holds p x → (R i).holds (S.move g p) (g • x))
    (g : Γ) (hg : g ∈ H) (p : P) (x y : S.Name) (h : (relation X R).holds p x y) :
    (relation X R).holds (S.move g p) (g • x) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,i,he,hi⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,?_,move X R H hR g hg hi⟩
  simpa only [Name.smul_check] using (S.eq_symmetry g r y (Name.check i.val)).mp he

/-- Every family of regular occurrences covering a set and with at most one
value at each index supplies an internal injection into the ground index set. -/
theorem exists_injection (Y : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hY : ∀ g ∈ H, g • Y = Y)
    (hR : ∀ g ∈ H, ∀ i p x, (R i).holds p x → (R i).holds (S.move g p) (g • x))
    (p : P)
    (hcover : ∀ x q, q ≤ p → S.atomic.MemF q x Y →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ i, (R i).holds s x)
    (hone : ∀ i q, q ≤ p → ∀ x y, (R i).holds q x → (R i).holds q y → S.atomic.EqF q x y) :
    ∃ f : S.Name, S.Forces ![f,Y,Name.check X] p (SetLanguage.injection 0 1 2) := by
  refine ⟨(relation X R).graph Y (Name.check X) H hH hY (fun g _ => Name.smul_check S g X)
    (relation_move X R H hR),?_⟩
  apply BinaryRelation.graph_injection
  · intro x q hq hx r hrq
    obtain ⟨s,hsr,i,hi⟩ := dense X R x q (hcover x q hq hx) r hrq
    exact ⟨s,hsr,Name.check i.val,S.check_mem_of_mem i.property s,
      fun t hts => ⟨t,le_rfl,i,S.atomic.eq_refl t _,mono X R hts hi⟩⟩
  · intro q _ x y z
    exact relation_one X R
  · exact relation_inj X R p hone

end LeastOccurrence
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## WellorderedImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Dense presentation of a wellorderability witness by a ground ordinal. -/
theorem wellorderable_check_dense (X : S.Name) (p : P)
    (h : S.Forces ![X] p (SetLanguage.wellorderable 0)) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ β : Ordinal.{u}, ∃ J : S.Name,
      S.Forces ![J,X,Name.check β.toZFSet] r (SetLanguage.injection 0 1 2) := by
  intro q hq
  obtain ⟨r,hrq,η,ho,hj⟩ := (S.forces_wellorderable _ _ _).mp h q hq
  obtain ⟨s,hsr,β,he⟩ := S.forces_ordinal_decide ![η] r 0 ho r le_rfl
  obtain ⟨t,hts,J,hJ⟩ := hj s hsr
  refine ⟨t,hts.trans (hsr.trans hrq),β,J,?_⟩
  apply (S.atomic.forceFormula_tuple_congr (p := t) (φ := SetLanguage.injection 0 1 2)
    (v := ![J,X,η]) (w := ![J,X,Name.check β.toZFSet]) ?_).mp hJ
  intro k
  fin_cases k
  · exact S.atomic.eq_refl t J
  · exact S.atomic.eq_refl t X
  · exact S.atomic.eq_mono hts he

theorem indexedImage_move (f J X Y : S.Name) (Ξ : ZFSet.{u}) (g : Γ)
    (hf : g • f = f) (hJ : g • J = J) (hX : g • X = X) (hY : g • Y = Y)
    (i : Ξ) (p : P) (y : S.Name) (h : (S.indexedImage f J X Y Ξ i).holds p y) :
    (S.indexedImage f J X Y Ξ i).holds (S.move g p) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,x,hx,hy⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • x,?_,
    S.boundedApp_move f X Y g hf hX hY r x y hy⟩
  change (S.boundedApp J X (Name.check Ξ)).holds (S.move g r) (g • x) (Name.check i.val)
  simpa only [Name.smul_check] using
    S.boundedApp_move J X (Name.check Ξ) g hJ hX (Name.smul_check S g Ξ) r x (Name.check i.val) hx

theorem indexedImage_one (f J X Y : S.Name) (Ξ : ZFSet.{u}) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hJ : S.Forces ![J,X,Name.check Ξ] p (SetLanguage.injection 0 1 2)) :
    ∀ i q, q ≤ p → ∀ y z, (S.indexedImage f J X Y Ξ i).holds q y →
      (S.indexedImage f J X Y Ξ i).holds q z → S.atomic.EqF q y z := by
  intro i q hq y z hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,x,hx,hxy⟩ := hy r hrq
  obtain ⟨t,hts,a,ha,haz⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have hxa := S.injection_one hJ htp (S.atomic.mem_mono hts hx.1) ha.1
    (S.app_mono hts hx.2.2) ha.2.2
  have hay := (S.app_congr (S.atomic.eq_refl t f) hxa (S.atomic.eq_refl t y)).mp
    (S.app_mono hts hxy.2.2)
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp ha.1 hay haz.2.2⟩

theorem indexedImage_cover (f J X Y : S.Name) (Ξ : ZFSet.{u}) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hJ : S.Forces ![J,X,Name.check Ξ] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ y q, q ≤ p → S.atomic.MemF q y Y →
      ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ i, (S.indexedImage f J X Y Ξ i).holds s y := by
  intro y q hq hy r hrq
  obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf hq hy r hrq
  obtain ⟨t,hts,j,hj,hxj⟩ := S.mapsTo_total hJ (hsr.trans (hrq.trans hq)) hx s le_rfl
  obtain ⟨a,hat,i,hi,hji⟩ := (S.mem_check Ξ j t).mp hj t le_rfl
  refine ⟨a,hat.trans (hts.trans hsr),⟨i,hi⟩,?_⟩
  intro b hba
  have hbs := hba.trans (hat.trans hts)
  refine ⟨b,le_rfl,x,?_,?_⟩
  · exact ⟨S.atomic.mem_mono hbs hx,S.check_mem_of_mem hi b,
      (S.app_congr (S.atomic.eq_refl b J) (S.atomic.eq_refl b x) (S.atomic.eq_mono hba hji)).mp
        (S.app_mono (hba.trans hat) hxj)⟩
  · exact ⟨S.atomic.mem_mono hbs hx,S.atomic.mem_mono (hbs.trans (hsr.trans hrq)) hy,
      S.app_mono hbs hxy⟩

/-- Images of wellorderable sets are wellorderable, by least preimages, not
by a use of Choice. -/
theorem wellorderable_image (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hX : S.Forces ![X] p (SetLanguage.wellorderable 0)) :
    S.Forces ![Y] p (SetLanguage.wellorderable 0) := by
  apply S.atomic.forceFormula_of_dense S.atomic_regular
  intro q hq
  obtain ⟨r,hrq,β,J,hJ⟩ := S.wellorderable_check_dense X p hX q hq
  let H := S.tupleStabilizer ![f,J,X,Y]
  have hR : ∀ g ∈ H, ∀ i p y, (S.indexedImage f J X Y β.toZFSet i).holds p y →
      (S.indexedImage f J X Y β.toZFSet i).holds (S.move g p) (g • y) := by
    intro g hg
    exact S.indexedImage_move f J X Y β.toZFSet g
      ((S.mem_tupleStabilizer _ g).mp hg 0) ((S.mem_tupleStabilizer _ g).mp hg 1)
      ((S.mem_tupleStabilizer _ g).mp hg 2) ((S.mem_tupleStabilizer _ g).mp hg 3)
  have hfr := S.atomic.forceFormula_mono (hrq.trans hq) hf
  obtain ⟨K,hK⟩ := LeastOccurrence.exists_injection β.toZFSet
    (S.indexedImage f J X Y β.toZFSet) Y H (S.tupleStabilizer_mem _)
      (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 3) hR r
      (S.indexedImage_cover f J X Y β.toZFSet r hfr (S.injection_mapsTo hJ))
      (S.indexedImage_one f J X Y β.toZFSet r (S.surjection_mapsTo hfr) hJ)
  exact ⟨r,hrq,S.wellorderable_of_check_injection Y K β r hK⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## RelationFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w i
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace BinaryRelation

omit [OrderTop P] in
theorem familyUnion_move {ι : Sort i} (R : ι → S.BinaryRelation) (g : Γ)
    (hR : ∀ i p x y, (R i).holds p x y → (R i).holds (S.move g p) (g • x) (g • y))
    (p : P) (x y : S.Name) (h : (familyUnion R).holds p x y) :
    (familyUnion R).holds (S.move g p) (g • x) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,i,hi⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  exact ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,hR i r x y hi⟩

end BinaryRelation

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## WellorderedSection -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
theorem forces_indexedSection (f X Y J i x : S.Name) (p : P) :
    S.Forces ![f,X,Y,J,i,x] p SetLanguage.indexedSection ↔
      ∀ y q, q ≤ p → S.atomic.MemF q y Y →
        ∀ r, r ≤ q → S.App r J y i → S.atomic.MemF r x X ∧ S.App r f x y := by
  simp only [Forces,SetLanguage.indexedSection,S.atomic.forceFormula_all S.atomic_regular,
    S.atomic.forceFormula_imp S.atomic_regular,ForcingQuotient.AtomicData.forceFormula_mem,
    ForcingQuotient.AtomicData.forceFormula_conj,S.forces_edge]
  rfl

omit [OrderTop P] in
/-- One fiber can be chosen without any simultaneous use of choice; an
unoccupied ordinal index imposes no requirement on the selected name. -/
theorem indexedSection_exists (f X Y J O i : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hJ : S.Forces ![J,Y,O] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![f,X,Y,J,i] p SetLanguage.indexedSection.ex := by
  intro q hq
  by_cases h : ∃ r, r ≤ q ∧ ∃ y, S.atomic.MemF r y Y ∧ S.App r J y i
  · obtain ⟨r,hrq,y,hy,hyi⟩ := h
    obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf (hrq.trans hq) hy r le_rfl
    refine ⟨s,hsr.trans hrq,x,?_⟩
    have hv : Fin.snoc ![f,X,Y,J,i] x = ![f,X,Y,J,i,x] := by
      ext k
      fin_cases k <;> rfl
    rw [hv]
    apply (S.forces_indexedSection _ _ _ _ _ _ _).mpr
    intro z t hts hz a hat hzi
    have hay := S.atomic.mem_mono (hat.trans (hts.trans hsr)) hy
    have haz := S.atomic.mem_mono hat hz
    have hzy := S.injection_one hJ (hat.trans (hts.trans (hsr.trans (hrq.trans hq)))) haz hay hzi
      (S.app_mono (hat.trans (hts.trans hsr)) hyi)
    exact ⟨S.atomic.mem_mono (hat.trans hts) hx,
      (S.app_congr (S.atomic.eq_refl a f) (S.atomic.eq_refl a x) hzy).mpr
        (S.app_mono (hat.trans hts) hxy)⟩
  · refine ⟨q,le_rfl,Name.empty,?_⟩
    have hv : Fin.snoc ![f,X,Y,J,i] (Name.empty : S.Name) = ![f,X,Y,J,i,Name.empty] := by
      ext k
      fin_cases k <;> rfl
    rw [hv]
    apply (S.forces_indexedSection _ _ _ _ _ _ _).mpr
    intro y r hrq hy s hsr hji
    exact (h ⟨s,hsr.trans hrq,y,S.atomic.mem_mono hsr hy,hji⟩).elim

theorem sectionPart_move (J Y i x : S.Name) (g : Γ)
    (hJ : g • J = J) (hY : g • Y = Y) (hi : g • i = i) (hx : g • x = x)
    (p : P) (y z : S.Name) (h : (S.sectionPart J Y i x).holds p y z) :
    (S.sectionPart J Y i x).holds (S.move g p) (g • y) (g • z) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [hY] using (S.mem_symmetry g p y Y).mp h.1
  · simpa only [hJ,hi] using (S.app_symmetry g p J y i).mp h.2.1
  · simpa only [hx] using (S.eq_symmetry g p z x).mp h.2.2

/-- A uniformly supported collection of local preimages gives one internal
injection, including its totality and its absence of extraneous graph entries. -/
theorem section_injection_of_uniform (f X Y J : S.Name) (Ξ : ZFSet.{u}) (c : Ξ → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hX : ∀ g ∈ H, g • X = X)
    (hY : ∀ g ∈ H, g • Y = Y) (hJ : ∀ g ∈ H, g • J = J)
    (hc : ∀ g ∈ H, ∀ i, g • c i = c i) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hj : S.Forces ![J,Y,Name.check Ξ] p (SetLanguage.mapsTo 0 1 2))
    (hs : ∀ i y q, q ≤ p → S.atomic.MemF q y Y → S.App q J y (Name.check i.val) →
      S.atomic.MemF q (c i) X ∧ S.App q f (c i) y) :
    ∃ K : S.Name, S.Forces ![K,Y,X] p (SetLanguage.injection 0 1 2) := by
  let R := BinaryRelation.familyUnion (fun i : Ξ => S.sectionPart J Y (Name.check i.val) (c i))
  have hR : ∀ g ∈ H, ∀ t y z, R.holds t y z → R.holds (S.move g t) (g • y) (g • z) := by
    intro g hg
    exact BinaryRelation.familyUnion_move _ g (fun i => S.sectionPart_move J Y (Name.check i.val)
      (c i) g (hJ g hg) (hY g hg) (Name.smul_check S g i.val) (hc g hg i))
  refine ⟨R.graph Y X H hH hY hX hR,?_⟩
  apply BinaryRelation.graph_injection
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,i,hi,hyi⟩ := S.mapsTo_total hj hq hy r hrq
    obtain ⟨t,hts,a,ha,hia⟩ := (S.mem_check Ξ i s).mp hi s le_rfl
    have hty := S.atomic.mem_mono (hts.trans (hsr.trans hrq)) hy
    have hyai := (S.app_congr (S.atomic.eq_refl t J) (S.atomic.eq_refl t y) hia).mp
      (S.app_mono hts hyi)
    have hval := hs ⟨a,ha⟩ y t (hts.trans (hsr.trans (hrq.trans hq))) hty hyai
    refine ⟨t,hts.trans hsr,c ⟨a,ha⟩,hval.1,?_⟩
    intro b hbt
    exact ⟨b,le_rfl,⟨a,ha⟩,S.atomic.mem_mono hbt hty,S.app_mono hbt hyai,S.atomic.eq_refl b _⟩
  · intro q hq y x z hx hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hy,hyi,hxi⟩ := hx r hrq
    obtain ⟨t,hts,j,_,hyj,hzj⟩ := hz s (hsr.trans hrq)
    have he := S.mapsTo_unique hj (hts.trans (hsr.trans (hrq.trans hq)))
      (S.atomic.mem_mono hts hy) (S.app_mono hts hyi) hyj
    have hij : i = j := Subtype.ext ((S.eq_check_iff i.val j.val t).mp he)
    subst j
    exact ⟨t,hts.trans hsr,S.atomic.eq_trans (S.atomic.eq_mono hts hxi) (S.atomic.eq_symm hzj)⟩
  · intro q hq y z x hy hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hys,hyi,hxi⟩ := hy r hrq
    obtain ⟨t,hts,j,hzt,hzj,hxj⟩ := hz s (hsr.trans hrq)
    have htp := hts.trans (hsr.trans (hrq.trans hq))
    have hy' := hs i y t htp (S.atomic.mem_mono hts hys) (S.app_mono hts hyi)
    have hz' := hs j z t htp hzt hzj
    have hxy := (S.app_congr (S.atomic.eq_refl t f) (S.atomic.eq_mono hts hxi)
      (S.atomic.eq_refl t y)).mpr hy'.2
    have hxz := (S.app_congr (S.atomic.eq_refl t f) hxj (S.atomic.eq_refl t z)).mpr hz'.2
    have hxX := (S.atomic.mem_congr hxj (S.atomic.eq_refl t X)).mpr hz'.1
    exact ⟨t,hts.trans hsr,S.mapsTo_unique hf htp hxX hxy hxz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- In the concrete system, surjections onto a wellorderable target admit
sections densely. The common support is chosen before any fiber values. -/
theorem wellorderable_target_injection (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hY : S.Forces ![Y] p (SetLanguage.wellorderable 0)) :
    ∃ q, q ≤ p ∧ ∃ K : S.Name, S.Forces ![K,Y,X] q (SetLanguage.injection 0 1 2) := by
  obtain ⟨r,hrp,β,J,hJ⟩ := S.wellorderable_check_dense Y p hY p le_rfl
  let H := S.tupleStabilizer ![f,X,Y,J]
  let v : β.toZFSet → Fin 5 → S.Name := fun i => ![f,X,Y,J,Name.check i.val]
  have hv : ∀ g ∈ H, ∀ i k, g • v i k = v i k := by
    intro g hg i k
    fin_cases k
    · exact (S.mem_tupleStabilizer _ g).mp hg 0
    · exact (S.mem_tupleStabilizer _ g).mp hg 1
    · exact (S.mem_tupleStabilizer _ g).mp hg 2
    · exact (S.mem_tupleStabilizer _ g).mp hg 3
    · exact Name.smul_check S g i.val
  obtain ⟨s,hsr,G,hG,c,hc,hchoices⟩ := uniform_maximum_dense SetLanguage.indexedSection v H
    (S.tupleStabilizer_mem _) hv r (fun i => S.indexedSection_exists f X Y J
      (Name.check β.toZFSet) (Name.check i.val) r (S.atomic.forceFormula_mono hrp hf) hJ)
  obtain ⟨K,hK⟩ := S.section_injection_of_uniform f X Y J β.toZFSet c (H ⊓ G)
    (S.normal.2.2.1 _ _ (S.tupleStabilizer_mem _) hG)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg.1 1)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg.1 2)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg.1 3)
    (fun g hg => hc g hg.2) s (S.surjection_mapsTo (S.atomic.forceFormula_mono (hsr.trans hrp) hf))
    (S.injection_mapsTo (S.atomic.forceFormula_mono hsr hJ)) (by
      intro i y t hts hy hji
      have hi := hchoices i
      have hv : Fin.snoc (v i) (c i) = ![f,X,Y,J,Name.check i.val,c i] := by
        ext k
        fin_cases k <;> rfl
      rw [hv] at hi
      exact (S.forces_indexedSection _ _ _ _ _ _ _).mp hi y t hts hy t le_rfl hji)
  exact ⟨s,hsr.trans hrp,K,hK⟩

end
end PartitionConsistency.ConcreteSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_SliceGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SubsetImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
/-- Local version of uniqueness for the default completion, using only the
forced function property on its stated domain. -/
theorem defaultRelation_unique_on (f A B D d : S.Name) (p : P)
    (hf : S.Forces ![f,A,B] p (SetLanguage.mapsTo 0 1 2)) {q : P} (hq : q ≤ p)
    (a y z : S.Name) (ha : S.atomic.MemF q a A)
    (hy : (S.defaultRelation f D d).holds q a y) (hz : (S.defaultRelation f D d).holds q a z) :
    S.atomic.EqF q y z := by
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,hs⟩ := (S.defaultRelation_iff f D d a y q).mp hy r hrq
  obtain ⟨t,hts,ht⟩ := (S.defaultRelation_iff f D d a z q).mp hz s (hsr.trans hrq)
  refine ⟨t,hts.trans hsr,?_⟩
  rcases hs with ⟨hs,hyD⟩ | ⟨hs,hy₀⟩ <;> rcases ht with ⟨ht,hzD⟩ | ⟨ht,hz₀⟩
  · exact S.mapsTo_unique hf (hts.trans (hsr.trans (hrq.trans hq)))
      (S.atomic.mem_mono (hts.trans (hsr.trans hrq)) ha) (S.app_mono hts hs) ht
  · exact (ht t le_rfl y (S.app_mono hts hs) (S.atomic.mem_mono hts hyD)).elim
  · exact (hs t hts z ht hzD).elim
  · exact S.atomic.eq_trans (S.atomic.eq_mono hts hy₀) (S.atomic.eq_symm hz₀)

/-- Every single nonempty subset of a surjective image is itself a surjective
image. The one default is explicitly given; no family of defaults is chosen. -/
theorem subset_image_surjection (f A B D d : S.Name) (p : P)
    (hf : S.Forces ![f,A,B] p (SetLanguage.surjection 0 1 2))
    (hD : S.SubsetF p D B) (hd : S.atomic.MemF p d D) :
    S.Forces ![S.subsetImageGraph f A D d,A,D] p (SetLanguage.surjection 0 1 2) := by
  unfold subsetImageGraph
  apply BinaryRelation.graph_surjection
  · intro a q hq ha r hrq
    obtain ⟨s,hsr,y,hy,hR⟩ := S.defaultRelation_total f D d a (S.atomic.mem_mono hq hd) r hrq
    exact ⟨s,hsr,y,hy,S.atomic.mem_mono (hsr.trans hrq) ha,hy,hR⟩
  · intro q hq a y z hy hz
    exact S.defaultRelation_unique_on f A B D d p (S.surjection_mapsTo hf) hq a y z
      hy.1 hy.2.2 hz.2.2
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,a,ha,hay⟩ := S.surjection_onto hf hq (hD y q hq hy) r hrq
    have hsD := S.atomic.mem_mono (hsr.trans hrq) hy
    exact ⟨s,hsr,a,ha,ha,hsD,S.defaultRelation_of_app hay hsD⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceRelations -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace SliceData
variable (D : SliceData S)

theorem mem_B (i : D.O) (x : S.Name) (p : P) :
    S.atomic.MemF p x (D.B i) ↔ (D.slice i).image.holds p x := by
  rw [B,UnaryRelation.mem_select]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨S.atomic_regular.2 _ _ _ ?_,h⟩
    intro q hq
    obtain ⟨r,hrq,a,ha⟩ := h q hq
    exact ⟨r,hrq,ha.2.1⟩

theorem B_subset (i : D.O) (p : P) : S.SubsetF p (D.B i) D.X := by
  intro x q _ hx
  exact ((UnaryRelation.mem_select _ _ _ _ _ _ x q).mp hx).1

theorem mem_Ypart (i : D.O) (y : S.Name) (p : P) :
    S.atomic.MemF p y (D.Ypart i) ↔
      S.atomic.MemF p y D.Y ∧ LeastOccurrence.At D.O D.occurrence p y i :=
  UnaryRelation.mem_select _ _ _ _ _ _ y p

theorem Ypart_disjoint {i j : D.O} {p : P} {y : S.Name}
    (hi : S.atomic.MemF p y (D.Ypart i)) (hj : S.atomic.MemF p y (D.Ypart j)) : i = j :=
  LeastOccurrence.unique D.O D.occurrence ((D.mem_Ypart i y p).mp hi).2
    ((D.mem_Ypart j y p).mp hj).2

theorem fix_Spart (g : Γ) (hg : g ∈ D.support) (i : D.O) : g • D.Spart i = D.Spart i :=
  UnaryRelation.select_fixed _ _ _ _ _ _ g hg

theorem mem_Spart (i : D.O) (x : S.Name) (p : P) :
    S.atomic.MemF p x (D.Spart i) ↔ S.atomic.MemF p x (D.B i) ∧ (D.preimage i).holds p x :=
  UnaryRelation.mem_select _ _ _ _ _ _ x p

theorem Spart_subset_B (i : D.O) (p : P) : S.SubsetF p (D.Spart i) (D.B i) :=
  fun x q _ hx => ((D.mem_Spart i x q).mp hx).1

theorem Spart_subset (i : D.O) (p : P) : S.SubsetF p (D.Spart i) D.X :=
  fun x q hq hx => D.B_subset i p x q hq (D.Spart_subset_B i p x q hq hx)

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceGeometry -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace SliceData
variable (D : SliceData S)

/-- Each Cartesian slice surjects onto its actual image. -/
theorem sliceGraph_surjection (i : D.O) (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![D.sliceGraph i,D.A,D.B i] p (SetLanguage.surjection 0 1 2) := by
  unfold sliceGraph
  apply BinaryRelation.graph_surjection
  · intro a q hq ha r hrq
    have hab := (S.opair_mem_cartesianName D.A (Name.check D.O) a (Name.check i.val) q).mpr
      ⟨ha,S.check_mem_of_mem i.property q⟩
    obtain ⟨s,hsr,x,hx,hax⟩ := S.mapsTo_total hs hq hab r hrq
    have hR : (D.slice i).holds s a x := ⟨S.atomic.mem_mono (hsr.trans hrq) ha,hx,hax⟩
    exact ⟨s,hsr,x,(D.mem_B i x s).mpr (fun t hts => ⟨t,le_rfl,a,(D.slice i).mono hts hR⟩),hR⟩
  · intro q hq a x y hx hy
    exact S.mapsTo_unique hs hq
      ((S.opair_mem_cartesianName D.A (Name.check D.O) a (Name.check i.val) q).mpr
        ⟨hx.1,S.check_mem_of_mem i.property q⟩) hx.2.2 hy.2.2
  · intro x q _ hx r hrq
    obtain ⟨s,hsr,a,ha⟩ := (D.mem_B i x q).mp hx r hrq
    exact ⟨s,hsr,a,ha.1,ha⟩

theorem partGraph_surjection (i : D.O) (p : P)
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![D.partGraph i,D.Spart i,D.Ypart i] p (SetLanguage.surjection 0 1 2) := by
  unfold partGraph restrictionGraph
  apply BinaryRelation.graph_surjection
  · intro x q hq hx r hrq
    obtain ⟨s,hsr,y,hxB,hy,hxy⟩ := ((D.mem_Spart i x q).mp hx).2 r hrq
    have hxS := S.atomic.mem_mono (hsr.trans hrq) hx
    exact ⟨s,hsr,y,hy,hxS,hy,hxy⟩
  · intro q hq x y z hy hz
    exact S.mapsTo_unique hf hq (D.Spart_subset i p x q hq hy.1) hy.2.2 hz.2.2
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,x,hxB,hyY,hxy⟩ := ((D.mem_Ypart i y q).mp hy).2.1 r hrq
    have hy' := S.atomic.mem_mono (hsr.trans hrq) hy
    have hxS : S.atomic.MemF s x (D.Spart i) := (D.mem_Spart i x s).mpr
      ⟨hxB,fun t hts => ⟨t,le_rfl,y,S.atomic.mem_mono hts hxB,S.atomic.mem_mono hts hy',
        S.app_mono hts hxy⟩⟩
    exact ⟨s,hsr,x,hxS,hxS,hy',hxy⟩

/-- The source pieces need not cover X, but they are pairwise disjoint. -/
theorem Spart_disjoint (p : P)
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.mapsTo 0 1 2))
    {i j : D.O} {q : P} (hq : q ≤ p) {x : S.Name}
    (hi : S.atomic.MemF q x (D.Spart i)) (hj : S.atomic.MemF q x (D.Spart j)) : i = j := by
  obtain ⟨r,hrq,y,hxB,hy,hxy⟩ := ((D.mem_Spart i x q).mp hi).2 q le_rfl
  obtain ⟨s,hsr,z,_,hz,hxz⟩ := ((D.mem_Spart j x q).mp hj).2 r hrq
  have hxX := D.B_subset i p x s (hsr.trans (hrq.trans hq)) (S.atomic.mem_mono hsr hxB)
  have he := S.mapsTo_unique hf (hsr.trans (hrq.trans hq)) hxX (S.app_mono hsr hxy) hxz
  exact D.Ypart_disjoint ((S.atomic.mem_congr he (S.atomic.eq_refl s (D.Ypart i))).mp
    (S.atomic.mem_mono hsr hy)) hz

/-- All target values occur in some slice, densely with an actual ground
index. No choice of slice indices is made. -/
theorem occurrence_cover (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2))
    (y : S.Name) {q : P} (hq : q ≤ p) (hy : S.atomic.MemF q y D.Y) :
    ∀ r, r ≤ q → ∃ t, t ≤ r ∧ ∃ i : D.O, (D.occurrence i).holds t y := by
  intro r hrq
  obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf hq hy r hrq
  obtain ⟨t,hts,z,hz,hzx⟩ := S.surjection_onto hs (hsr.trans (hrq.trans hq)) hx s le_rfl
  obtain ⟨b,hbt,a,j,ha,hj,hzaj⟩ := (S.mem_cartesianName D.A (Name.check D.O) z t).mp hz t le_rfl
  obtain ⟨c,hcb,k,hk,hjk⟩ := (S.mem_check D.O j b).mp hj b le_rfl
  let i : D.O := ⟨k,hk⟩
  have hzai := S.atomic.eq_trans (S.atomic.eq_mono hcb hzaj)
    (S.eq_opair_congr (S.atomic.eq_refl c a) hjk)
  have hax := (S.app_congr (S.atomic.eq_refl c D.s) hzai (S.atomic.eq_refl c x)).mp
    (S.app_mono (hcb.trans hbt) hzx)
  have hslice : (D.slice i).holds c a x :=
    ⟨S.atomic.mem_mono hcb ha,S.atomic.mem_mono (hcb.trans (hbt.trans hts)) hx,hax⟩
  have hxB := (D.mem_B i x c).mpr (fun d hdc => ⟨d,le_rfl,a,(D.slice i).mono hdc hslice⟩)
  refine ⟨c,hcb.trans (hbt.trans (hts.trans hsr)),i,?_⟩
  intro d hdc
  exact ⟨d,le_rfl,x,S.atomic.mem_mono hdc hxB,
    S.atomic.mem_mono (hdc.trans (hcb.trans (hbt.trans (hts.trans (hsr.trans hrq))))) hy,
    S.app_mono (hdc.trans (hcb.trans (hbt.trans hts))) hxy⟩

/-- Taking the least occurrence partitions the whole target. -/
theorem Ypart_cover (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2))
    (y : S.Name) {q : P} (hq : q ≤ p) (hy : S.atomic.MemF q y D.Y) :
    ∀ r, r ≤ q → ∃ t, t ≤ r ∧ ∃ i : D.O, S.atomic.MemF t y (D.Ypart i) := by
  intro r hrq
  obtain ⟨t,htr,i,hi⟩ := LeastOccurrence.dense D.O D.occurrence y q
    (D.occurrence_cover p hs hf y hq hy) r hrq
  exact ⟨t,htr,i,(D.mem_Ypart i y t).mpr ⟨S.atomic.mem_mono (htr.trans hrq) hy,hi⟩⟩

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_SliceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SliceAssembly -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- An empty domain has an internal injection into any set. -/
theorem empty_domain_injection (X Y : S.Name) (p : P)
    (hX : ∀ x q, q ≤ p → ¬ S.atomic.MemF q x X) :
    ∃ j : S.Name, S.Forces ![j,X,Y] p (SetLanguage.injection 0 1 2) := by
  let H := S.tupleStabilizer ![X,Y]
  refine ⟨S.falseRelation.graph X Y H (S.tupleStabilizer_mem _)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 0)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1) (fun _ _ _ _ _ h => h.elim),?_⟩
  apply BinaryRelation.graph_injection
  · intro x q hq hx
    exact (hX x q hq hx).elim
  · intro q hq x y z h
    exact h.elim
  · intro q hq x y z h
    exact h.elim

theorem empty_domain_wellorderable (X : S.Name) (p : P)
    (hX : ∀ x q, q ≤ p → ¬ S.atomic.MemF q x X) :
    S.Forces ![X] p (SetLanguage.wellorderable 0) := by
  obtain ⟨j,hj⟩ := S.empty_domain_injection X (Name.check (0 : Ordinal.{u}).toZFSet) p hX
  exact S.wellorderable_of_check_injection X j 0 p hj

/-- Nonwellorderability alone supplies a member densely. This selects only
one member below one condition, never a family of default members. -/
theorem nonwellorderable_member_dense (X : S.Name) (p : P)
    (hX : S.Forces ![X] p (SetLanguage.wellorderable 0).neg) :
    ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, S.atomic.MemF r x X := by
  intro q hq
  by_contra h
  have he : ∀ x r, r ≤ q → ¬ S.atomic.MemF r x X := fun x r hr hx => h ⟨r,hr,x,hx⟩
  exact (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mp hX q hq
    (S.empty_domain_wellorderable X q he)

namespace SliceData
variable {S} (D : SliceData S)

/-- A uniformly supported family of candidate injections is assembled into
one graph. Totality uses the target partition, while one-to-one-ness uses the
disjoint source pieces. No assertion that these source pieces cover X is made. -/
theorem assemble (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2))
    (c : D.O → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter) (hHD : H ≤ D.support)
    (hc : ∀ g ∈ H, ∀ i, g • c i = c i)
    (hj : ∀ i, S.Forces ![c i,D.Ypart i,D.Spart i] p (SetLanguage.injection 0 1 2)) :
    ∃ j : S.Name, S.Forces ![j,D.Y,D.X] p (SetLanguage.injection 0 1 2) := by
  let R := BinaryRelation.familyUnion (fun i => S.boundedApp (c i) (D.Ypart i) (D.Spart i))
  have hR : ∀ g ∈ H, ∀ t y x, R.holds t y x → R.holds (S.move g t) (g • y) (g • x) := by
    intro g hg
    exact BinaryRelation.familyUnion_move _ g (fun i => S.boundedApp_move _ _ _ g
      (hc g hg i) (D.fix_Ypart g (hHD hg) i) (D.fix_Spart g (hHD hg) i))
  refine ⟨R.graph D.Y D.X H hH (fun _ hg => D.fix_Y (hHD hg))
    (fun _ hg => D.fix_X (hHD hg)) hR,?_⟩
  apply BinaryRelation.graph_injection
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,i,hyi⟩ := D.Ypart_cover p hs hf y hq hy r hrq
    obtain ⟨t,hts,x,hxi,hyx⟩ := S.mapsTo_total (S.injection_mapsTo (hj i))
      (hsr.trans (hrq.trans hq)) hyi s le_rfl
    exact ⟨t,hts.trans hsr,x,D.Spart_subset i p x t (hts.trans (hsr.trans (hrq.trans hq))) hxi,
      fun b hbt => ⟨b,le_rfl,i,S.atomic.mem_mono (hbt.trans hts) hyi,
        S.atomic.mem_mono hbt hxi,S.app_mono hbt hyx⟩⟩
  · intro q hq y x z hx hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hyi,hxi,hyx⟩ := hx r hrq
    obtain ⟨t,hts,k,hyk,hzk,hyz⟩ := hz s (hsr.trans hrq)
    have hik := D.Ypart_disjoint (S.atomic.mem_mono hts hyi) hyk
    subst k
    exact ⟨t,hts.trans hsr,S.mapsTo_unique (S.injection_mapsTo (hj i))
      (hts.trans (hsr.trans (hrq.trans hq))) hyk (S.app_mono hts hyx) hyz⟩
  · intro q hq y z x hy hz
    apply S.atomic_regular.1
    intro r hrq
    obtain ⟨s,hsr,i,hyi,hxi,hyx⟩ := hy r hrq
    obtain ⟨t,hts,k,hzk,hxk,hzx⟩ := hz s (hsr.trans hrq)
    have htp := hts.trans (hsr.trans (hrq.trans hq))
    have hik := D.Spart_disjoint p (S.surjection_mapsTo hf) htp (S.atomic.mem_mono hts hxi) hxk
    subst k
    exact ⟨t,hts.trans hsr,S.injection_one (hj i) htp (S.atomic.mem_mono hts hyi) hzk
      (S.app_mono hts hyx) hzx⟩

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceCandidates -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- Pointwise existence of a candidate. The wellorderable case uses ordinal
choice for the fibers of this one slice. In the other case two classified
images of A give a reverse injection; it need not be a section of f. -/
theorem slice_candidate (D : SliceData S) (hA : D.A = A) (i : D.O) (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2)) :
    ∃ q, q ≤ p ∧ ∃ j : S.Name,
      S.Forces ![j,D.Ypart i,D.Spart i] q (SetLanguage.injection 0 1 2) := by
  have hpart := D.partGraph_surjection i p (S.surjection_mapsTo hf)
  by_cases hwo : ∃ q, q ≤ p ∧ S.Forces ![D.Ypart i] q (SetLanguage.wellorderable 0)
  · obtain ⟨q,hqp,hwo⟩ := hwo
    obtain ⟨r,hrq,j,hj⟩ := wellorderable_target_injection (D.partGraph i) (D.Spart i) (D.Ypart i)
      q (S.atomic.forceFormula_mono hqp hpart) hwo
    exact ⟨r,hrq.trans hqp,j,hj⟩
  · have hYn : S.Forces ![D.Ypart i] p (SetLanguage.wellorderable 0).neg :=
      (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr (fun q hq hh => hwo ⟨q,hq,hh⟩)
    have hSn : S.Forces ![D.Spart i] p (SetLanguage.wellorderable 0).neg := by
      apply (S.atomic.forceFormula_neg S.atomic_regular _ _ _).mpr
      intro q hq hh
      exact hwo ⟨q,hq,S.wellorderable_image (D.partGraph i) (D.Spart i) (D.Ypart i) q
        (S.atomic.forceFormula_mono hq hpart) hh⟩
    obtain ⟨q,hqp,d,hd⟩ := S.nonwellorderable_member_dense (D.Spart i) p hSn p le_rfl
    have hB : S.Forces ![D.sliceGraph i,A,D.B i] q (SetLanguage.surjection 0 1 2) := by
      rw [← hA]
      exact D.sliceGraph_surjection i q (S.surjection_mapsTo (S.atomic.forceFormula_mono hqp hs))
    let aS := S.subsetImageGraph (D.sliceGraph i) A (D.Spart i) d
    have has : S.Forces ![aS,A,D.Spart i] q (SetLanguage.surjection 0 1 2) :=
      S.subset_image_surjection (D.sliceGraph i) A (D.B i) (D.Spart i) d q hB (D.Spart_subset_B i q) hd
    let aY := S.compositionGraph aS (D.partGraph i) A (D.Spart i) (D.Ypart i)
    have hay : S.Forces ![aY,A,D.Ypart i] q (SetLanguage.surjection 0 1 2) :=
      S.compositionGraph_surjection _ _ _ _ _ q has (S.atomic.forceFormula_mono hqp hpart)
    obtain ⟨r,hrq,kS,hkS⟩ := nonwellorderable_image_bijection aS (D.Spart i) q has
      (S.atomic.forceFormula_mono hqp hSn)
    obtain ⟨t,htr,kY,hkY⟩ := nonwellorderable_image_bijection aY (D.Ypart i) r
      (S.atomic.forceFormula_mono hrq hay) (S.atomic.forceFormula_mono (hrq.trans hqp) hYn)
    have hkS := (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mp
      (S.atomic.forceFormula_mono htr hkS)
    have hkY := (ForcingQuotient.AtomicData.forceFormula_conj _ _ _ _ _).mp hkY
    have hi := S.inverseGraph_injection kY A (D.Ypart i) t hkY.1 hkY.2
    exact ⟨t,htr.trans (hrq.trans hqp),
      S.compositionGraph (S.inverseGraph kY A (D.Ypart i)) kS (D.Ypart i) A (D.Spart i),
      S.compositionGraph_injection _ _ _ _ _ t hi hkS.2⟩

/-- Choose the already defined slice injections with one common support and
assemble them. There is no simultaneous selection of auxiliary wellorderings,
defaults, or quotient bijections in the pointwise argument. -/
theorem presentation_reverse_injection (D : SliceData S) (hA : D.A = A) (p : P)
    (hs : S.Forces ![D.s,S.cartesianName D.A (Name.check D.O),D.X] p (SetLanguage.surjection 0 1 2))
    (hf : S.Forces ![D.f,D.X,D.Y] p (SetLanguage.surjection 0 1 2)) :
    ∃ q, q ≤ p ∧ ∃ j : S.Name, S.Forces ![j,D.Y,D.X] q (SetLanguage.injection 0 1 2) := by
  let v : D.O → Fin 2 → S.Name := fun i => ![D.Ypart i,D.Spart i]
  have hv : ∀ g ∈ D.support, ∀ i k, g • v i k = v i k := by
    intro g hg i k
    fin_cases k
    · exact D.fix_Ypart g hg i
    · exact D.fix_Spart g hg i
  have hex : ∀ i, S.Forces (v i) p (SetLanguage.injection 2 0 1).ex := by
    intro i q hqp
    obtain ⟨r,hrq,j,hj⟩ := slice_candidate D hA i q
      (S.atomic.forceFormula_mono hqp hs) (S.atomic.forceFormula_mono hqp hf)
    refine ⟨r,hrq,j,?_⟩
    have he : Fin.snoc (v i) j = ![D.Ypart i,D.Spart i,j] := by
      ext k
      fin_cases k <;> rfl
    rw [he]
    exact (S.forces_injection _ r 2 0 1).mpr ((S.forces_injection _ r 0 1 2).mp hj)
  obtain ⟨q,hqp,H,hH,c,hc,hj⟩ := uniform_maximum_dense (SetLanguage.injection 2 0 1) v
    D.support D.support_mem hv p hex
  obtain ⟨j,hj⟩ := D.assemble q (S.atomic.forceFormula_mono hqp hs) (S.atomic.forceFormula_mono hqp hf)
    c (D.support ⊓ H) (S.normal.2.2.1 _ _ D.support_mem hH) inf_le_left
    (fun g hg => hc g hg.2) (by
      intro i
      have hi := hj i
      have he : Fin.snoc (v i) (c i) = ![D.Ypart i,D.Spart i,c i] := by
        ext k
        fin_cases k <;> rfl
      rw [he] at hi
      exact (S.forces_injection _ q 0 1 2).mpr ((S.forces_injection _ q 2 0 1).mp hi))
  exact ⟨q,hqp,j,hj⟩

end
end PartitionConsistency.ConcreteSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## PartitionPrinciple -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
/-- Purely logical conversion of reverse-injection witnesses to the full
Partition Principle sentence. Its quantifiers range over all HS names. -/
theorem forces_PP_of_dense
    (h : ∀ (p : P) (f X Y : S.Name),
      S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2) →
      ∃ q, q ≤ p ∧ ∃ j : S.Name, S.Forces ![j,Y,X] q (SetLanguage.injection 0 1 2))
    (p : P) : S.Forces Fin.elim0 p SetLanguage.PP := by
  change S.atomic.ForceFormula Fin.elim0 p SetLanguage.PP
  rw [SetLanguage.PP,S.atomic.forceFormula_all S.atomic_regular]
  intro X
  have hX : Fin.snoc (Fin.elim0 : Fin 0 → S.Name) X = ![X] := by
    ext k
    fin_cases k; rfl
  rw [hX,S.atomic.forceFormula_all S.atomic_regular]
  intro Y
  have hY : Fin.snoc ![X] Y = ![X,Y] := by
    ext k
    fin_cases k <;> rfl
  rw [hY,S.atomic.forceFormula_imp S.atomic_regular]
  intro q hqp hf r hrq
  obtain ⟨s,hsr,f,hf⟩ := hf r hrq
  have hv : Fin.snoc ![X,Y] f = ![X,Y,f] := by
    ext k
    fin_cases k <;> rfl
  rw [hv] at hf
  have hf' : S.Forces ![f,X,Y] s (SetLanguage.surjection 0 1 2) :=
    (S.forces_surjection _ s 0 1 2).mpr ((S.forces_surjection _ s 2 0 1).mp hf)
  obtain ⟨t,hts,j,hj⟩ := h s f X Y hf'
  refine ⟨t,hts.trans hsr,j,?_⟩
  have hvj : Fin.snoc ![X,Y] j = ![X,Y,j] := by
    ext k
    fin_cases k <;> rfl
  rw [hvj]
  exact (S.forces_injection _ t 2 1 0).mpr ((S.forces_injection _ t 0 1 2).mp hj)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- All-set reduction for the constructed system, including the empty-set
case. The presentation and subsequent choices are made at arbitrary ranks. -/
theorem reverse_injection_dense (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2)) :
    ∃ q, q ≤ p ∧ ∃ j : S.Name, S.Forces ![j,Y,X] q (SetLanguage.injection 0 1 2) := by
  by_cases hne : ∃ q, q ≤ p ∧ ∃ x : S.Name, S.atomic.MemF q x X
  · obtain ⟨q,hqp,x,hx⟩ := hne
    obtain ⟨η,s,hs⟩ := ordinal_presentation aleph0_le_μ cardinal_T size_lt T.e complement_cardinal
      (posetCode κ) (posetCode_injective κ) X x q hx
    let D : SliceData S := ⟨s,f,A,X,Y,η.toZFSet⟩
    obtain ⟨r,hrq,j,hj⟩ := presentation_reverse_injection D rfl q hs (S.atomic.forceFormula_mono hqp hf)
    exact ⟨r,hrq.trans hqp,j,hj⟩
  · have he : ∀ y q, q ≤ p → ¬ S.atomic.MemF q y Y := by
      intro y q hqp hy
      obtain ⟨r,hrq,x,hx,_⟩ := S.surjection_onto hf hqp hy q le_rfl
      exact hne ⟨r,hrq.trans hqp,x,hx⟩
    obtain ⟨j,hj⟩ := S.empty_domain_injection Y X p he
    exact ⟨p,le_rfl,j,hj⟩

/-- The Partition Principle for arbitrary internal sets and surjections. -/
theorem forces_PP (p : P) : S.Forces Fin.elim0 p SetLanguage.PP :=
  S.forces_PP_of_dense (fun p f X Y => reverse_injection_dense f X Y p) p

/-- The actual symmetric forcing interpretation supplies every axiom of the
full target theory, with no inaccessible-cardinal or model-existence premise. -/
theorem forces_target (p : P) : ∀ φ ∈ SetLanguage.targetTheory, S.Forces Fin.elim0 p φ := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact forces_ZF p φ hφ
  · rcases hφ with rfl | rfl | rfl | hfalse
    · exact forces_PP p
    · exact forces_ACwo p
    · exact forces_not_AC p

/-- Soundness of the nontrivial regular forcing interpretation rules out an
ordinary finite first-order proof of contradiction from the target theory. -/
theorem consistent_target : Consistent SetLanguage.targetTheory :=
  S.consistent_of_forces (⊤ : P) (forces_target ⊤)

end
end PartitionConsistency.ConcreteSystem

namespace PartitionConsistency
/-- Relative consistency for pure first-order set theories, with syntactic
consistency and no transitive-ground or inaccessible-cardinal hypothesis. -/





theorem main_consistency_oai :
    Consistent SetLanguage.ZF → Consistent SetLanguage.targetTheory := by
  intro _
  exact ConcreteSystem.consistent_target
end PartitionConsistency

end OAI
end

theorem solution : type_of% @OAI.PartitionConsistency.main_consistency_oai := @OAI.PartitionConsistency.main_consistency_oai
