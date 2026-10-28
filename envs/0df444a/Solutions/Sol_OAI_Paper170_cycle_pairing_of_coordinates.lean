-- Prove2me | solution 1 for OAI.Paper170.cycle_pairing_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:42:50.709173+00:00
-- url     : https://prove2.me/submissions/a27cdc78-3144-4af5-a98a-6ed687206281

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_CompleteCrossing
import Definitions.Def_OAIQ4Cc002
import Theorems.Thm_OAI_Paper170Geometry_TruncatedSpokeCoordinates_exists_cycle_block_radius
import Theorems.Thm_OAI_Paper170Geometry_TruncatedSpokeCoordinates_exists_passage_pairing_radius

section
-- module Solutions.OAIQ4_Cc.CompleteCrossing_CycleSpace
attribute [-instance] _root_.OAI.Paper170Geometry.incidentEdgesFintype _root_.OAI.Paper170Geometry.instFintypeOrientedDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cycle-space spanning, flows, simple cycles, and oriented darts. -/

section

/-! Linear properties of actual oriented simple cycles. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} {G : Graph V E}
namespace SimpleCycle

theorem follows_next (C : SimpleCycle G) (i : Fin C.length) :
    (G.src (C.edge i)=C.vertex i ∧ G.dst (C.edge i)=C.vertex (C.next i)) ∨
      (G.dst (C.edge i)=C.vertex i ∧ G.src (C.edge i)=C.vertex (C.next i)) := C.follows i

theorem next_eq_finRotate (C : SimpleCycle G) : C.next = finRotate C.length := by
  funext i
  apply Fin.ext
  have hL : 1 < C.length := by have := C.three_le; omega
  simp [next, finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt hL]

theorem next_val (C : SimpleCycle G) (i : Fin C.length) :
    (C.next i).val = if i.val+1<C.length then i.val+1 else 0 := by
  change (i.val+1)%C.length = _
  by_cases h : i.val+1<C.length
  · simp [h, Nat.mod_eq_of_lt h]
  · have he : i.val+1=C.length := by omega
    simp [he]

theorem next_ne_self (C : SimpleCycle G) (i : Fin C.length) : C.next i≠i := by
  intro h
  have he := congrArg Fin.val h
  rw [next_val] at he
  have := C.three_le
  split_ifs at he <;> omega

theorem next_next_ne_self (C : SimpleCycle G) (i : Fin C.length) : C.next (C.next i)≠i := by
  intro h
  have he := congrArg Fin.val h
  simp only [next_val] at he
  have := C.three_le
  split_ifs at he <;> omega

theorem edge_injective (C : SimpleCycle G) : Function.Injective C.edge := by
  intro i j hij
  have hi := C.follows_next i
  have hj := C.follows_next j
  rw [hij] at hi
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact C.vertex_injective (hi.1.symm.trans hj.1)
  · have h1 := C.vertex_injective (hi.1.symm.trans hj.2)
    have h2 := C.vertex_injective (hi.2.symm.trans hj.1)
    exact False.elim (C.next_next_ne_self j (by rw [← h1,h2]))
  · have h1 := C.vertex_injective (hi.1.symm.trans hj.2)
    have h2 := C.vertex_injective (hi.2.symm.trans hj.1)
    exact False.elim (C.next_next_ne_self j (by rw [← h1,h2]))
  · exact C.vertex_injective (hi.1.symm.trans hj.1)

theorem edgeChain_at_edge (C : SimpleCycle G) (i : Fin C.length) :
    C.edgeChain (C.edge i) = if G.src (C.edge i)=C.vertex i then 1 else -1 := by
  classical
  simp only [edgeChain, C.edge_injective.eq_iff]
  simp

theorem edgeChain_at_edge_ne_zero (C : SimpleCycle G) (i : Fin C.length) :
    C.edgeChain (C.edge i) ≠ 0 := by
  rw [edgeChain_at_edge]
  split_ifs <;> norm_num

theorem edgeChain_eq_zero_of_not_mem_range (C : SimpleCycle G) {e : E}
    (he : e∉Set.range C.edge) : C.edgeChain e=0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  rw [ite_eq_right (fun h => he ⟨i,h⟩)]

theorem edgeChain_support (C : SimpleCycle G) (e : E) :
    C.edgeChain e≠0 ↔ e∈Set.range C.edge := by
  constructor
  · exact fun h => Classical.byContradiction (fun he => h (C.edgeChain_eq_zero_of_not_mem_range he))
  · rintro ⟨i,rfl⟩
    exact C.edgeChain_at_edge_ne_zero i

theorem signed_boundary_step (C : SimpleCycle G) (i : Fin C.length) (v : V) :
    (if G.src (C.edge i)=C.vertex i then (1:ℝ) else -1) *
      ((if G.dst (C.edge i)=v then 1 else 0)-(if G.src (C.edge i)=v then 1 else 0)) =
    (if C.vertex (C.next i)=v then 1 else 0)-(if C.vertex i=v then 1 else 0) := by
  classical
  rcases C.follows_next i with h | h
  · simp [h.1,h.2]
  · have hn : C.vertex (C.next i)≠C.vertex i := fun h => C.next_ne_self i (C.vertex_injective h)
    simp only [h.1,h.2,ite_eq_right hn]
    ring

theorem boundary_edgeChain [Fintype E] (C : SimpleCycle G) (v : V) : boundary G C.edgeChain v=0 := by
  classical
  unfold boundary edgeChain
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi (i : Fin C.length) :
      (∑e, (if C.edge i=e then (if G.src e=C.vertex i then (1:ℝ) else -1) else 0) *
        ((if G.dst e=v then 1 else 0)-(if G.src e=v then 1 else 0))) =
      (if C.vertex (C.next i)=v then 1 else 0)-(if C.vertex i=v then 1 else 0) := by
    rw [Finset.sum_eq_single (C.edge i)]
    · simpa using C.signed_boundary_step i v
    · intro e _ he
      simp [Ne.symm he]
    · simp
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, next_eq_finRotate]
  exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate C.length)
    (fun i => if C.vertex i=v then (1:ℝ) else 0))

end SimpleCycle
end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

omit [Fintype V] in
lemma flowEdge_spec (z : E → ℝ) (hz : ∀ v, boundary G z v = 0) (v : FlowVertex G z) :
    ((G.src (flowEdge G z hz v) = v.val ∧ G.dst (flowEdge G z hz v) = (flowNext G z hz v).val ∧ 0 < z (flowEdge G z hz v)) ∨
    (G.dst (flowEdge G z hz v) = v.val ∧ G.src (flowEdge G z hz v) = (flowNext G z hz v).val ∧ z (flowEdge G z hz v) < 0)) :=
  (flow_successor_exists G z hz v).choose_spec.choose_spec

omit [Fintype V] [Fintype E] in
lemma flowArc_irrefl (z : E → ℝ) (v : V) (e : E) : ¬ ((G.src e = v ∧ G.dst e = v ∧ 0 < z e) ∨
    (G.dst e = v ∧ G.src e = v ∧ z e < 0)) := by
  rintro (⟨hs, hd, _⟩ | ⟨hd, hs, _⟩) <;> exact G.loopless e (hs.trans hd.symm)

omit [Fintype V] [Fintype E] in
lemma flowArc_not_reverse (z : E → ℝ) (v w : V) (e f : E)
    (he : ((G.src e = v ∧ G.dst e = w ∧ 0 < z e) ∨
    (G.dst e = v ∧ G.src e = w ∧ z e < 0))) (hf : ((G.src f = w ∧ G.dst f = v ∧ 0 < z f) ∨
    (G.dst f = w ∧ G.src f = v ∧ z f < 0))) : False := by
  have hef : e = f := by
    apply G.simple e f
    rcases he with ⟨he1, he2, _⟩ | ⟨he1, he2, _⟩ <;>
      rcases hf with ⟨hf1, hf2, _⟩ | ⟨hf1, hf2, _⟩
    · exact Or.inr ⟨he1.trans hf2.symm, he2.trans hf1.symm⟩
    · exact Or.inl ⟨he1.trans hf2.symm, he2.trans hf1.symm⟩
    · exact Or.inl ⟨he2.trans hf1.symm, he1.trans hf2.symm⟩
    · exact Or.inr ⟨he2.trans hf1.symm, he1.trans hf2.symm⟩
  subst f
  rcases he with ⟨he1, he2, hp⟩ | ⟨he1, he2, hp⟩ <;>
    rcases hf with ⟨hf1, hf2, hq⟩ | ⟨hf1, hf2, hq⟩
  · exact G.loopless e (he1.trans hf2.symm)
  · linarith
  · linarith
  · exact G.loopless e (hf2.trans he1.symm)

lemma exists_positive_period {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    ∃ a, 0 < Function.minimalPeriod f a := by
  let x : α := Classical.arbitrary α
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => f^[i] x)
  have helper {m n : ℕ} (hmn : m < n) (h : f^[m] x = f^[n] x) :
      ∃ a, 0 < Function.minimalPeriod f a := by
    have hperiod : Function.IsPeriodicPt f (n - m) (f^[m] x) := by
      change f^[n-m] (f^[m] x) = f^[m] x
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmn.le]
      exact h.symm
    exact ⟨f^[m] x, hperiod.minimalPeriod_pos (Nat.sub_pos_of_lt hmn)⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact helper hlt heq
  · exact helper hlt heq.symm

end Paper170

end
end

section

/-! Support reduction spans the real kernel of the graph boundary map by simple cycles. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} [Fintype E] (G : Graph V E)

theorem mem_chainSupport (z : E → ℝ) (e : E) : e∈chainSupport z ↔ z e≠0 := by
  simp [chainSupport]

theorem simple_cycles_balanced (z : E → ℝ)
    (hz : z∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain))) :
    ∀v, boundary G z v=0 := by
  have hle : Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) ≤
      LinearMap.ker (boundaryLinear G) := by
    rw [Submodule.span_le]
    rintro _ ⟨C,rfl⟩
    exact funext C.boundary_edgeChain
  exact fun v => congrFun (hle hz) v

theorem simple_cycles_span_of_supported_cycle
    (hex : ∀z : E → ℝ, (∀v, boundary G z v=0) → z≠0 →
      ∃C : SimpleCycle G, ∀i, z (C.edge i)≠0) (z : E → ℝ) :
    (∀v, boundary G z v=0) ↔ z∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) := by
  constructor
  · intro hz
    suffices h : ∀m (w : E → ℝ), (chainSupport w).card=m → (∀v, boundary G w v=0) →
        w∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) from
      h _ z rfl hz
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro w hm hw
      by_cases hw0 : w=0
      · simp [hw0]
      obtain ⟨C,hC⟩ := hex w hw hw0
      let i : Fin C.length := ⟨0,by have := C.three_le; omega⟩
      let e := C.edge i
      have hc : C.edgeChain e≠0 := C.edgeChain_at_edge_ne_zero i
      let a := w e / C.edgeChain e
      let w' := w-a • C.edgeChain
      have hw' : ∀v, boundary G w' v=0 := by
        have hmapw : boundaryLinear G w=0 := funext hw
        have hmapC : boundaryLinear G C.edgeChain=0 := funext C.boundary_edgeChain
        have hmap : boundaryLinear G w'=0 := by
          simp only [w',map_sub,map_smul,hmapw,hmapC,smul_zero,sub_self]
        exact fun v => congrFun hmap v
      have he0 : w' e=0 := by
        change w e-(w e/C.edgeChain e)*C.edgeChain e=0
        rw [div_mul_cancel₀ _ hc,sub_self]
      have hsub : chainSupport w' ⊆ chainSupport w := by
        intro f hf
        rw [mem_chainSupport] at hf ⊢
        by_contra hwf
        have hCf : C.edgeChain f=0 := by
          by_contra hh
          obtain ⟨j,hj⟩ := (C.edgeChain_support f).mp hh
          exact hC j (hj ▸ hwf)
        apply hf
        change w f-a*C.edgeChain f=0
        rw [hwf,hCf,mul_zero,sub_self]
      have hproper : chainSupport w' ⊂ chainSupport w := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub,?_⟩
        intro heq
        have hew : e∈chainSupport w := (mem_chainSupport w e).mpr (hC i)
        rw [← heq,mem_chainSupport] at hew
        exact hew he0
      have hcard : (chainSupport w').card < m := by
        rw [← hm]
        exact Finset.card_lt_card hproper
      have hind := ih _ hcard w' rfl hw'
      have hchain : C.edgeChain∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) :=
        Submodule.subset_span ⟨C,rfl⟩
      have hsum := (Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain))).add_mem
        hind ((Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain))).smul_mem a hchain)
      simpa only [w',sub_add_cancel] using hsum
  · exact simple_cycles_balanced G z

end Paper170

end
end

section

noncomputable section
open scoped Classical
namespace Paper170

variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

omit [Fintype V] in
lemma flow_period_three (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (a : FlowVertex G z) (hp : 0 < Function.minimalPeriod (flowNext G z hz) a) :
    3 ≤ Function.minimalPeriod (flowNext G z hz) a := by
  let f := flowNext G z hz
  have hone : Function.minimalPeriod f a ≠ 1 := by
    intro h
    have heq : f a = a := by
      simpa [h] using (Function.iterate_minimalPeriod (f := f) (x := a))
    have hs := flowEdge_spec G z hz a
    change ((G.src (flowEdge G z hz a) = a.val ∧ G.dst (flowEdge G z hz a) = (f a).val ∧ 0 < z (flowEdge G z hz a)) ∨
      (G.dst (flowEdge G z hz a) = a.val ∧ G.src (flowEdge G z hz a) = (f a).val ∧ z (flowEdge G z hz a) < 0)) at hs
    rw [heq] at hs
    exact flowArc_irrefl G z a.val _ hs
  have htwo : Function.minimalPeriod f a ≠ 2 := by
    intro h
    have heq : f (f a) = a := by
      simpa [h, Function.iterate_succ_apply'] using
        (Function.iterate_minimalPeriod (f := f) (x := a))
    have hs := flowEdge_spec G z hz (f a)
    change ((G.src (flowEdge G z hz (f a)) = (f a).val ∧ G.dst (flowEdge G z hz (f a)) = (f (f a)).val ∧ 0 < z (flowEdge G z hz (f a))) ∨
      (G.dst (flowEdge G z hz (f a)) = (f a).val ∧ G.src (flowEdge G z hz (f a)) = (f (f a)).val ∧ z (flowEdge G z hz (f a)) < 0)) at hs
    rw [heq] at hs
    exact flowArc_not_reverse G z a.val (f a).val _ _ (flowEdge_spec G z hz a) hs
  change 0 < Function.minimalPeriod f a at hp
  change 3 ≤ Function.minimalPeriod f a
  omega

theorem exists_supported_simple_cycle (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (hne : z ≠ 0) : ∃ C : SimpleCycle G, ∀ i, z (C.edge i) ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  have hnonempty : Nonempty (FlowVertex G z) := by
    rcases lt_or_gt_of_ne he with h | h
    · exact ⟨⟨G.dst e, e, Or.inr ⟨rfl, h⟩⟩⟩
    · exact ⟨⟨G.src e, e, Or.inl ⟨rfl, h⟩⟩⟩
  let := hnonempty
  let f := flowNext G z hz
  obtain ⟨a, ha⟩ := exists_positive_period f
  let n := Function.minimalPeriod f a
  have hn : 3 ≤ n := flow_period_three G z hz a ha
  have hstep (i : Fin n) :
      f^[((i.val + 1) % n)] a = f (f^[i.val] a) := by
    rw [Function.iterate_mod_minimalPeriod_eq]
    exact Function.iterate_succ_apply' _ _ _
  let C : SimpleCycle G :=
    { length := n
      three_le := hn
      vertex := fun i => (f^[i.val] a).val
      vertex_injective := by
        intro i j hij
        apply Fin.ext
        exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt (Subtype.ext hij)
      edge := fun i => flowEdge G z hz (f^[i.val] a)
      follows := by
        intro i
        change (G.src (flowEdge G z hz (f^[i.val] a)) = (f^[i.val] a).val ∧
          G.dst (flowEdge G z hz (f^[i.val] a)) = (f^[((i.val + 1) % n)] a).val) ∨
          (G.dst (flowEdge G z hz (f^[i.val] a)) = (f^[i.val] a).val ∧
          G.src (flowEdge G z hz (f^[i.val] a)) = (f^[((i.val + 1) % n)] a).val)
        rw [hstep]
        rcases flowEdge_spec G z hz (f^[i.val] a) with ⟨hs, hd, _⟩ | ⟨hd, hs, _⟩
        · exact Or.inl ⟨hs, hd⟩
        · exact Or.inr ⟨hd, hs⟩ }
  refine ⟨C, ?_⟩
  intro i
  rcases flowEdge_spec G z hz (f^[i.val] a) with ⟨_, _, hp⟩ | ⟨_, _, hn⟩
  · exact ne_of_gt hp
  · exact ne_of_lt hn

end Paper170

end
end

section

/-! A frozen simple cycle gives a periodic sequence of actual oriented edge traversals. -/
noncomputable section
open scoped Classical
namespace Paper170.SimpleCycle
open Paper170Geometry
variable {V E : Type} {G : Graph V E}

theorem dart_fst (C : SimpleCycle G) (i : Fin C.length) : (C.dart i).fst = C.vertex i := by
  rcases C.follows_next i with h | h
  · simp [dart,OrientedDart.fst,h.1]
  · have hn : G.src (C.edge i) ≠ C.vertex i := by
      rw [h.2]
      exact fun he => C.next_ne_self i (C.vertex_injective he)
    simp [dart,OrientedDart.fst,hn,h.1]

theorem dart_snd (C : SimpleCycle G) (i : Fin C.length) : (C.dart i).snd = C.vertex (C.next i) := by
  rcases C.follows_next i with h | h
  · simp [dart,OrientedDart.snd,h.1,h.2]
  · have hn : G.src (C.edge i) ≠ C.vertex i := by
      rw [h.2]
      exact fun he => C.next_ne_self i (C.vertex_injective he)
    simpa only [dart,OrientedDart.snd,decide_eq_true_eq,ite_eq_right hn] using h.2

theorem dart_edge (C : SimpleCycle G) (i : Fin C.length) : (C.dart i).edge = C.edge i := rfl

theorem dart_sign (C : SimpleCycle G) (i : Fin C.length) :
    dartSign (C.dart i) = if G.src (C.edge i)=C.vertex i then 1 else -1 := by
  simp [dart,dartSign]

theorem modIndex_succ (C : SimpleCycle G) (i : ℕ) : C.modIndex (i+1)=C.next (C.modIndex i) := by
  apply Fin.ext
  simp [modIndex,next,Nat.add_mod]

theorem modIndex_period (C : SimpleCycle G) : C.modIndex C.length=C.modIndex 0 := by
  apply Fin.ext
  simp [modIndex]

theorem cyclicDart_seam (C : SimpleCycle G) (i : ℕ) :
    (C.cyclicDart i).snd = (C.cyclicDart (i+1)).fst := by
  simp only [cyclicDart,dart_snd,dart_fst,modIndex_succ]

theorem cyclicDart_period (C : SimpleCycle G) : C.cyclicDart C.length = C.cyclicDart 0 := by
  rw [cyclicDart,cyclicDart,modIndex_period]

theorem cyclicDart_next_edge_ne (C : SimpleCycle G) (i : ℕ) :
    (C.cyclicDart (i+1)).edge ≠ (C.cyclicDart i).edge := by
  simp only [cyclicDart,dart_edge,modIndex_succ]
  exact fun he => C.next_ne_self _ (C.edge_injective he)

end Paper170.SimpleCycle

end
end

section

/-! The real cycle space of an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170
variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

theorem simple_cycles_span (z : E → ℝ) :
    (∀v, boundary G z v=0) ↔
      z∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) :=
  simple_cycles_span_of_supported_cycle G (exists_supported_simple_cycle G) z

end Paper170

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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygonIntersection_swap (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection w v m n = -polygonIntersection v w n m := by
  unfold polygonIntersection
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        -segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact segmentCrossingSign_swap _ _ _ _
    _ = _ := by simp only [Finset.sum_neg_distrib]

theorem telescoping_real_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i-f (i+1))) = f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    ring

theorem polygon_cone_cancellation (v : ℕ → Plane) (n : ℕ) (hv : v n = v 0)
    (o c d : Plane) :
    (∑ i ∈ Finset.range n, triangleSegmentIntersection o (v i) (v (i+1)) c d) =
      ∑ i ∈ Finset.range n, segmentCrossingSign (v i) (v (i+1)) c d := by
  unfold triangleSegmentIntersection
  have hrev : ∀ i, segmentCrossingSign (v (i+1)) o c d = -segmentCrossingSign o (v (i+1)) c d :=
    fun i => segmentCrossingSign_reverse_left o (v (i+1)) c d
  simp only [hrev, Finset.sum_add_distrib]
  have htele := telescoping_real_sum (fun i => segmentCrossingSign o (v i) c d) n
  rw [hv,sub_self] at htele
  rw [Finset.sum_sub_distrib] at htele
  rw [Finset.sum_neg_distrib]
  linarith

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

theorem eventually_segmentCrossingSign_of_proper (a b c d : Plane)
    (h : SegmentsCrossProperly a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b),
      segmentCrossingSign ab.1 ab.2 c d = segmentCrossingSign a b c d := by
  have hD : Continuous (fun ab : Plane × Plane => det2 (ab.2-ab.1) (d-c)) := by
    dsimp [det2]
    fun_prop
  have hF : ContinuousAt (fun ab : Plane × Plane => firstIntersectionParameter ab.1 ab.2 c d) (a,b) := by
    apply ContinuousAt.div
    · dsimp [det2]
      fun_prop
    · exact hD.continuousAt
    · exact h.1
  have hS : ContinuousAt (fun ab : Plane × Plane => secondIntersectionParameter ab.1 ab.2 c d) (a,b) := by
    apply ContinuousAt.div
    · dsimp [det2]
      fun_prop
    · exact hD.continuousAt
    · exact h.1
  obtain ⟨ht,hu⟩ := (segmentsCrossProperly_iff_parameters a b c d h.1).mp h
  have ht' := hF.eventually (isOpen_Ioo.mem_nhds ht)
  have hu' := hS.eventually (isOpen_Ioo.mem_nhds hu)
  by_cases hpos : 0 < det2 (b-a) (d-c)
  · have hd' : ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), 0 < det2 (ab.2-ab.1) (d-c) :=
      continuousAt_const.eventually_lt hD.continuousAt hpos
    filter_upwards [ht',hu',hd'] with ab ht hu hd
    have hc := (segmentsCrossProperly_iff_parameters ab.1 ab.2 c d (ne_of_gt hd)).mpr ⟨ht,hu⟩
    simp [segmentCrossingSign,h,hc,hpos,hd]
  · have hneg : det2 (b-a) (d-c) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) h.1
    have hd' : ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), det2 (ab.2-ab.1) (d-c) < 0 :=
      hD.continuousAt.eventually_lt continuousAt_const hneg
    filter_upwards [ht',hu',hd'] with ab ht hu hd
    have hc := (segmentsCrossProperly_iff_parameters ab.1 ab.2 c d (ne_of_lt hd)).mpr ⟨ht,hu⟩
    simp [segmentCrossingSign,h,hc,hpos,not_lt.mpr hd.le]

theorem eventually_segmentCrossingSign (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b),
      segmentCrossingSign ab.1 ab.2 c d = segmentCrossingSign a b c d := by
  by_cases hc : SegmentsCrossProperly a b c d
  · exact eventually_segmentCrossingSign_of_proper a b c d hc
  · have hn : ¬ ClosedSegmentsMeet a b c d := by
      rintro ⟨t,ht,u,hu,he⟩
      obtain ⟨hd,ht',hu'⟩ := h t ht u hu he
      exact hc ⟨hd,t,ht',u,hu',he⟩
    have hevent := (isClosed_closedSegmentsMeet c d).isOpen_compl.mem_nhds
      (show (a,b) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d}ᶜ from hn)
    filter_upwards [hevent] with ab hab
    have hn' : ¬ SegmentsCrossProperly ab.1 ab.2 c d :=
      fun hx => hab (closedSegmentsMeet_of_proper _ _ _ _ hx)
    simp [segmentCrossingSign,hc,hn']

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical BigOperators

theorem exists_polygon_intersection_stability_radius (v w : ℕ → Plane) (n m : ℕ)
    (h : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v' : ℕ → Plane,
      (∀ i : Fin (n+1), dist (v' i.val) (v i.val) < ε) →
      polygonIntersection v' w n m = polygonIntersection v w n m := by
  have hh : ∀ ij : Fin n × Fin m, ∃ ε : ℝ, 0 < ε ∧
      ∀ ab : Plane × Plane, dist ab (v ij.1.val,v (ij.1.val+1)) < ε →
        segmentCrossingSign ab.1 ab.2 (w ij.2.val) (w (ij.2.val+1)) =
          segmentCrossingSign (v ij.1.val) (v (ij.1.val+1)) (w ij.2.val) (w (ij.2.val+1)) := by
    intro ij
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentCrossingSign _ _ _ _ (h ij.1 ij.2))
    exact ⟨ε,hε,fun ab hab => he hab⟩
  choose radius hpos hstable using hh
  obtain ⟨ε,hε,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun ij _ => hpos ij)
  refine ⟨ε,hε,?_⟩
  intro v' hv'
  unfold polygonIntersection
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hin := Finset.mem_range.mp hi
  have hjm := Finset.mem_range.mp hj
  let ii : Fin n := ⟨i,hin⟩
  let jj : Fin m := ⟨j,hjm⟩
  apply hstable (ii,jj) (v' i,v' (i+1))
  rw [Prod.dist_eq]
  exact (max_lt (hv' ⟨i,by omega⟩) (hv' ⟨i+1,by omega⟩)).trans (hbound (ii,jj) (Finset.mem_univ _))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TransversalityStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem segmentPairTransverse_of_proper (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    SegmentPairTransverse a b c d := by
  obtain ⟨hn,t₀,ht₀,u₀,hu₀,he₀⟩ := h
  intro t ht u hu he
  obtain ⟨rfl,rfl⟩ := segment_intersection_parameters_unique a b c d hn t u t₀ u₀ he he₀
  exact ⟨hn,ht₀,hu₀⟩

theorem segmentPairTransverse_swap (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    SegmentPairTransverse c d a b := by
  intro t ht u hu he
  obtain ⟨hn,hu',ht'⟩ := h u hu t ht he.symm
  refine ⟨?_,ht',hu'⟩
  rw [det2_swap]
  exact neg_ne_zero.mpr hn

theorem eventually_segmentPairTransverse (a b c d : Plane) (h : SegmentPairTransverse a b c d) :
    ∀ᶠ ab : Plane × Plane in 𝓝 (a,b), SegmentPairTransverse ab.1 ab.2 c d := by
  by_cases hc : SegmentsCrossProperly a b c d
  · have hsign : segmentCrossingSign a b c d ≠ 0 := by
      unfold segmentCrossingSign
      rw [ite_eq_left hc]
      split_ifs <;> norm_num
    filter_upwards [eventually_segmentCrossingSign_of_proper a b c d hc] with ab hab
    apply segmentPairTransverse_of_proper
    by_contra hn
    have hz : segmentCrossingSign ab.1 ab.2 c d = 0 := by simp [segmentCrossingSign,hn]
    exact hsign (hab.symm.trans hz)
  · have hn : ¬ ClosedSegmentsMeet a b c d := by
      rintro ⟨t,ht,u,hu,he⟩
      obtain ⟨hd,ht',hu'⟩ := h t ht u hu he
      exact hc ⟨hd,t,ht',u,hu',he⟩
    have hevent := (isClosed_closedSegmentsMeet c d).isOpen_compl.mem_nhds
      (show (a,b) ∈ {ab : Plane × Plane | ClosedSegmentsMeet ab.1 ab.2 c d}ᶜ from hn)
    filter_upwards [hevent] with ab hab
    intro t ht u hu he
    exact False.elim (hab ⟨t,ht,u,hu,he⟩)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonTransversalityStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem exists_polygon_transversality_radius (v w : ℕ → Plane) (n m : ℕ)
    (h : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v' : ℕ → Plane,
      (∀ i : Fin (n+1), dist (v' i.val) (v i.val) < ε) →
      (∀ i : Fin n, ∀ j : Fin m,
        SegmentPairTransverse (v' i.val) (v' (i.val+1)) (w j.val) (w (j.val+1))) ∧
      polygonIntersection v' w n m = polygonIntersection v w n m := by
  have hh : ∀ ij : Fin n × Fin m, ∃ ε : ℝ, 0 < ε ∧
      ∀ ab : Plane × Plane, dist ab (v ij.1.val,v (ij.1.val+1)) < ε →
        SegmentPairTransverse ab.1 ab.2 (w ij.2.val) (w (ij.2.val+1)) := by
    intro ij
    obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
      (eventually_segmentPairTransverse _ _ _ _ (h ij.1 ij.2))
    exact ⟨ε,hε,fun ab hab => he hab⟩
  choose radius hpos hstable using hh
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun ij _ => hpos ij)
  obtain ⟨η,hη,hcount⟩ := exists_polygon_intersection_stability_radius v w n m h
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro v' hv'
  constructor
  · intro i j
    apply hstable (i,j) (v' i.val,v' (i.val+1))
    rw [Prod.dist_eq]
    have h₀ := (hv' ⟨i.val,by omega⟩).trans_le (min_le_left δ η)
    have h₁ := (hv' ⟨i.val+1,by omega⟩).trans_le (min_le_left δ η)
    exact (max_lt h₀ h₁).trans (hbound (i,j) (Finset.mem_univ _))
  · exact hcount v' (fun i => (hv' i).trans_le (min_le_right δ η))

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
-- module Solutions.OAIQ4_Cc.Crossing_GenericPointExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_generic_point_extension {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (p : ι → Plane) (q : ν → Plane) (a v : κ → Plane)
    (hv : ∀ k, v k ≠ 0) (hpq : ∀ i j, q j ≠ p i)
    (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Plane, dist x z < ε ∧
      (∀ i, x ≠ p i) ∧ (∀ j, q j ≠ x) ∧
      (∀ k, det2 (x-a k) (v k) ≠ 0) ∧
      (∀ i k, det2 (x-p i) (v k) ≠ 0) ∧
      (∀ i j, orient2 (p i) x (q j) ≠ 0) := by
  let J := κ ⊕ (ν ⊕ (ι ⊕ ((ι × κ) ⊕ (ι × ν))))
  let base : J → Plane
    | .inl k => a k
    | .inr (.inl j) => q j
    | .inr (.inr (.inl i)) => p i
    | .inr (.inr (.inr (.inl (i,_)))) => p i
    | .inr (.inr (.inr (.inr (i,_)))) => p i
  let direction : J → Plane
    | .inl k => v k
    | .inr (.inl _) => (1,0)
    | .inr (.inr (.inl _)) => (1,0)
    | .inr (.inr (.inr (.inl (_,k)))) => v k
    | .inr (.inr (.inr (.inr (i,j)))) => q j-p i
  have hd : ∀ k, direction k ≠ 0 := by
    rintro (k|(j|(i|(⟨i,k⟩|⟨i,j⟩))))
    · exact hv k
    · norm_num [direction]
    · norm_num [direction]
    · exact hv k
    · exact sub_ne_zero.mpr (hpq i j)
  obtain ⟨x,hx,havoid⟩ := exists_near_avoiding_lines base direction hd z ε hε
  refine ⟨x,hx,?_,?_,?_,?_,?_⟩
  · intro i heq
    have hh := havoid (.inr (.inr (.inl i)))
    simp [base,direction,heq,det2] at hh
  · intro j heq
    have hh := havoid (.inr (.inl j))
    simp [base,direction,← heq,det2] at hh
  · intro k
    exact havoid (.inl k)
  · intro i k
    exact havoid (.inr (.inr (.inr (.inl (i,k)))))
  · intro i j
    exact havoid (.inr (.inr (.inr (.inr (i,j)))))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_StepEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem sum_stepEvent (n : ℕ) (r lo hi : Fin n → ℝ) (hr : StrictMono r)
    (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, stepEvent r lo hi i) =
      (∏ i, stepAt (r i) (lo i) (hi i) 1) - ∏ i, stepAt (r i) (lo i) (hi i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let rt := fun i : Fin n => r i.succ
    let lt := fun i : Fin n => lo i.succ
    let ht := fun i : Fin n => hi i.succ
    have hrt : StrictMono rt := hr.comp (fun _ _ h => Fin.succ_lt_succ_iff.mpr h)
    have hind := ih rt lt ht hrt (fun i => h0 i.succ) (fun i => h1 i.succ)
    have hfirst : ∀ i : Fin n, r 0 < r i.succ := fun i => hr (Fin.succ_pos i)
    have hhead : stepEvent r lo hi 0 =
        if 0 < r 0 ∧ r 0 < 1 then (hi 0-lo 0) * ∏ i : Fin n, lt i else 0 := by
      unfold stepEvent
      rw [Fin.prod_univ_succ]
      simp only [ite_true,one_mul,Fin.succ_ne_zero,ite_false]
      congr 1
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_left (hfirst i)
    have htail : ∀ i : Fin n, stepEvent r lo hi i.succ = hi 0 * stepEvent rt lt ht i := by
      intro i
      unfold stepEvent
      rw [Fin.prod_univ_succ]
      simp only [(Fin.succ_ne_zero i).symm,ite_false,Fin.succ_inj]
      rw [show stepAt (r 0) (lo 0) (hi 0) (r i.succ) = hi 0 from ite_eq_right (not_lt.mpr (hfirst i).le)]
      change (if 0 < rt i ∧ rt i < 1 then (ht i-lt i) *
        (hi 0 * ∏ j, if j=i then 1 else stepAt (rt j) (lt j) (ht j) (rt i)) else 0) = _
      split_ifs <;> ring
    rw [Fin.sum_univ_succ,hhead]
    simp_rw [htail]
    rw [← Finset.mul_sum,hind,Fin.prod_univ_succ,Fin.prod_univ_succ]
    rcases lt_or_gt_of_ne (h0 0) with hrneg | hrpos
    · have hn1 : ¬ 1 < r 0 := by linarith
      have hn0 : ¬ 0 < r 0 := by linarith
      simp only [hn0,false_and,ite_false,stepAt,hn1]
      ring
    · rcases lt_or_gt_of_ne (h1 0) with hrlt | hrgt
      · have hn1 : ¬ 1 < r 0 := by linarith
        have ht0 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 0) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrpos.trans (hfirst i))
        rw [ht0]
        simp only [hrpos,hrlt,and_self,ite_true,stepAt,hn1,ite_false]
        ring
      · have ht0 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 0) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrpos.trans (hfirst i))
        have ht1 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 1) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrgt.trans (hfirst i))
        rw [ht0,ht1]
        simp [stepAt,hrpos,hrgt,not_lt.mpr hrgt.le]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_AffineSideEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem sideAfter_sub_before (b : ℝ) : sideAfter b-sideBefore b = slopeSign b := by
  unfold sideAfter sideBefore slopeSign
  split_ifs <;> norm_num

theorem positiveIndicator_factor (b r t : ℝ) (hb : b ≠ 0) (ht : t ≠ r) :
    positiveIndicator (b*(t-r)) = stepAt r (sideBefore b) (sideAfter b) t := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · by_cases htr : t < r
    · have hprod := mul_pos_of_neg_of_neg hb (sub_neg.mpr htr)
      simp [positiveIndicator,stepAt,sideBefore,htr,hprod,not_lt.mpr hb.le]
    · have hrt : r<t := lt_of_le_of_ne (le_of_not_gt htr) ht.symm
      have hprod := mul_neg_of_neg_of_pos hb (sub_pos.mpr hrt)
      simp [positiveIndicator,stepAt,sideAfter,htr,not_lt.mpr hprod.le,not_lt.mpr hb.le]
  · by_cases htr : t < r
    · have hprod := mul_neg_of_pos_of_neg hb (sub_neg.mpr htr)
      simp [positiveIndicator,stepAt,sideBefore,htr,not_lt.mpr hprod.le,hb]
    · have hrt : r<t := lt_of_le_of_ne (le_of_not_gt htr) ht.symm
      have hprod := mul_pos hb (sub_pos.mpr hrt)
      simp [positiveIndicator,stepAt,sideAfter,htr,hprod,hb]

theorem sum_affine_side_events (n : ℕ) (r b : Fin n → ℝ)
    (hr : StrictMono r) (hb : ∀ i, b i ≠ 0) (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, if 0 < r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0) =
      (∏ i, positiveIndicator (b i*(1-r i))) - ∏ i, positiveIndicator (b i*(0-r i)) := by
  have hh := sum_stepEvent n r (fun i => sideBefore (b i)) (fun i => sideAfter (b i)) hr h0 h1
  have he : ∀ i : Fin n, stepEvent r (fun i => sideBefore (b i)) (fun i => sideAfter (b i)) i =
      if 0 < r i ∧ r i<1 then slopeSign (b i) *
        (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0 := by
    intro i
    unfold stepEvent
    rw [sideAfter_sub_before]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · rw [ite_eq_right hji,ite_eq_right hji]
      exact (positiveIndicator_factor (b j) (r j) (r i) (hb j) (hr.injective.ne (Ne.symm hji))).symm
  simp_rw [he] at hh
  rw [hh]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact (positiveIndicator_factor (b i) (r i) 1 (hb i) (h1 i).symm).symm
  · apply Finset.prod_congr rfl
    intro i hi
    exact (positiveIndicator_factor (b i) (r i) 0 (hb i) (h0 i).symm).symm

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_SortedSideEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem exists_sorted_permutation (n : ℕ) (r : Fin n → ℝ) (hr : Function.Injective r) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (r ∘ e) := by
  let e := @Fintype.orderIsoFinOfCardEq (Fin n) (LinearOrder.lift' r hr)
    inferInstance n (Fintype.card_fin n)
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  exact @OrderIso.strictMono (Fin n) (Fin n) inferInstance
    (LinearOrder.lift' r hr).toPreorder e i j hij

theorem sum_affine_side_events_unordered (n : ℕ) (r b : Fin n → ℝ)
    (hr : Function.Injective r) (hb : ∀ i, b i ≠ 0) (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, if 0 < r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0) =
      (∏ i, positiveIndicator (b i*(1-r i))) - ∏ i, positiveIndicator (b i*(0-r i)) := by
  obtain ⟨e,he⟩ := exists_sorted_permutation n r hr
  have h := sum_affine_side_events n (r ∘ e) (b ∘ e) he
    (fun i => hb (e i)) (fun i => h0 (e i)) (fun i => h1 (e i))
  simp only [Function.comp_apply] at h
  have hprod : ∀ i, (∏ j : Fin n, if j=i then (1 : ℝ) else
      positiveIndicator (b (e j)*(r (e i)-r (e j)))) =
      ∏ j : Fin n, if j=e i then 1 else positiveIndicator (b j*(r (e i)-r j)) := by
    intro i
    rw [← Equiv.prod_comp e (fun j => if j=e i then (1 : ℝ) else positiveIndicator (b j*(r (e i)-r j)))]
    simp only [e.injective.eq_iff]
  simp_rw [hprod] at h
  rw [Equiv.sum_comp e (fun i => if 0 < r i ∧ r i<1 then slopeSign (b i) *
      (∏ j, if j=i then 1 else positiveIndicator (b j*(r i-r j))) else 0),
    Equiv.prod_comp e (fun i => positiveIndicator (b i*(1-r i))),
    Equiv.prod_comp e (fun i => positiveIndicator (b i*(0-r i)))] at h
  exact h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TriangleSideEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Classical

theorem triangle_side_at_first_edge (a b c : Plane) (t : ℝ) :
    orient2 b c (segmentPoint a b t) = (1-t)*orient2 a b c := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem triangle_other_side_at_first_edge (a b c : Plane) (t : ℝ) :
    orient2 c a (segmentPoint a b t) = t*orient2 a b c := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem triangle_edge_side_tests (a b c d e : Plane)
    (harea : 0 < orient2 a b c) (hn : det2 (b-a) (e-d) ≠ 0) :
    (0 < orient2 b c (segmentPoint d e (secondIntersectionParameter a b d e)) ↔
      firstIntersectionParameter a b d e < 1) ∧
    (0 < orient2 c a (segmentPoint d e (secondIntersectionParameter a b d e)) ↔
      0 < firstIntersectionParameter a b d e) := by
  rw [← intersection_parameters_eq a b d e hn,
    triangle_side_at_first_edge, triangle_other_side_at_first_edge]
  constructor
  · rw [mul_pos_iff_of_pos_right harea]
    constructor <;> intro h <;> linarith
  · exact mul_pos_iff_of_pos_right harea

theorem segmentCrossingSign_triangle_event (a b c d e : Plane)
    (harea : 0 < orient2 a b c) (hn : det2 (b-a) (e-d) ≠ 0) :
    segmentCrossingSign a b d e =
      if 0 < secondIntersectionParameter a b d e ∧ secondIntersectionParameter a b d e < 1 then
        slopeSign (det2 (b-a) (e-d)) *
          (positiveIndicator (orient2 b c (segmentPoint d e (secondIntersectionParameter a b d e))) *
           positiveIndicator (orient2 c a (segmentPoint d e (secondIntersectionParameter a b d e))))
      else 0 := by
  obtain ⟨hleft,hright⟩ := triangle_edge_side_tests a b c d e harea hn
  rw [segmentCrossingSign, segmentsCrossProperly_iff_parameters a b d e hn]
  simp only [Set.mem_Ioo,positiveIndicator,hleft,hright]
  by_cases hu : 0 < secondIntersectionParameter a b d e ∧ secondIntersectionParameter a b d e < 1
  · by_cases ht0 : 0 < firstIntersectionParameter a b d e <;>
      by_cases ht1 : firstIntersectionParameter a b d e < 1 <;>
      simp [hu,ht0,ht1,slopeSign]
  · simp [hu]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TriangleEntryExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

theorem triangle_area_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem affine_side_factor (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) (t : ℝ) :
    orient2 a b (segmentPoint c d t) =
      det2 (b-a) (d-c) * (t-secondIntersectionParameter a b c d) := by
  rw [orient2_segment]
  change (1-t)*orient2 a b c+t*orient2 a b d =
    det2 (b-a) (d-c)*(t-(-orient2 a b c / det2 (b-a) (d-c)))
  field_simp
  linear_combination t * (orient2_difference a b c d)

theorem triangle_segment_entry_exit (a b c d e : Plane)
    (harea : 0 < orient2 a b c)
    (hn : ∀ i : Fin 3, det2 (triangleEnd a b c i-triangleStart a b c i) (e-d) ≠ 0)
    (hr : Function.Injective (fun i : Fin 3 =>
      secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e))
    (h0 : ∀ i : Fin 3, secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e ≠ 0)
    (h1 : ∀ i : Fin 3, secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e ≠ 1) :
    triangleSegmentIntersection a b c d e = triangleIndicator a b c e-triangleIndicator a b c d := by
  let r := fun i : Fin 3 => secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e
  let b' := fun i : Fin 3 => det2 (triangleEnd a b c i-triangleStart a b c i) (e-d)
  have hf (i : Fin 3) (t : ℝ) : b' i*(t-r i) =
      orient2 (triangleStart a b c i) (triangleEnd a b c i) (segmentPoint d e t) :=
    (affine_side_factor _ _ d e (hn i) t).symm
  have hc1 : 0 < orient2 b c a := by rwa [triangle_area_cycle]
  have hc2 : 0 < orient2 c a b := by rwa [triangle_area_cycle,triangle_area_cycle]
  have hs (i : Fin 3) :
      segmentCrossingSign (triangleStart a b c i) (triangleEnd a b c i) d e =
        if 0 < r i ∧ r i<1 then slopeSign (b' i) *
          (∏ j : Fin 3, if j=i then 1 else positiveIndicator
            (orient2 (triangleStart a b c j) (triangleEnd a b c j) (segmentPoint d e (r i)))) else 0 := by
    fin_cases i
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ] using
        segmentCrossingSign_triangle_event a b c d e harea (hn 0)
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ,mul_comm] using
        segmentCrossingSign_triangle_event b c a d e hc1 (hn 1)
    · simpa [r,b',triangleStart,triangleEnd,Fin.prod_univ_succ] using
        segmentCrossingSign_triangle_event c a b d e hc2 (hn 2)
  have h := sum_affine_side_events_unordered 3 r b' hr hn h0 h1
  simp_rw [hf] at h
  simp only [segmentPoint_one,segmentPoint_zero] at h
  calc
    triangleSegmentIntersection a b c d e =
        ∑ i : Fin 3, segmentCrossingSign (triangleStart a b c i) (triangleEnd a b c i) d e := by
      simp [triangleSegmentIntersection,triangleStart,triangleEnd,Fin.sum_univ_succ]
      ring
    _ = _ := by simpa only [hs,triangleIndicator] using h

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TriangleTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem triangle_consecutive_roots_ne (a b c d e : Plane)
    (ha : orient2 a b c ≠ 0) (h₀ : det2 (b-a) (e-d) ≠ 0)
    (h₁ : det2 (c-b) (e-d) ≠ 0) (hb : orient2 d e b ≠ 0) :
    secondIntersectionParameter a b d e ≠ secondIntersectionParameter b c d e := by
  intro heq
  have hz : orient2 b c (segmentPoint a b (firstIntersectionParameter a b d e)) = 0 := by
    rw [intersection_parameters_eq a b d e h₀,heq,
      ← intersection_parameters_eq b c d e h₁,orient2_self_segment]
  rw [triangle_side_at_first_edge] at hz
  have ht : firstIntersectionParameter a b d e = 1 := by
    have := (mul_eq_zero.mp hz).resolve_right ha
    linarith
  have hp := intersection_parameters_eq a b d e h₀
  rw [ht,segmentPoint_one] at hp
  apply hb
  rw [hp,orient2_self_segment]

theorem second_parameter_ne_zero (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (hc : orient2 a b c ≠ 0) :
    secondIntersectionParameter a b c d ≠ 0 := by
  intro h
  have hh := affine_side_factor a b c d hn 0
  rw [h,segmentPoint_zero] at hh
  apply hc
  simpa using hh

theorem second_parameter_ne_one (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (hd : orient2 a b d ≠ 0) :
    secondIntersectionParameter a b c d ≠ 1 := by
  intro h
  have hh := affine_side_factor a b c d hn 1
  rw [h,segmentPoint_one] at hh
  apply hd
  simpa using hh

theorem triangle_roots_injective (a b c d e : Plane) (ha : orient2 a b c ≠ 0)
    (h : TriangleSegmentPosition a b c d e) :
    Function.Injective (fun i : Fin 3 =>
      secondIntersectionParameter (triangleStart a b c i) (triangleEnd a b c i) d e) := by
  have h₀ := triangle_consecutive_roots_ne a b c d e ha (h.1 0) (h.1 1) (h.2.1 1)
  have ha₁ : orient2 b c a ≠ 0 := by rwa [triangle_area_cycle]
  have ha₂ : orient2 c a b ≠ 0 := by rwa [triangle_area_cycle,triangle_area_cycle]
  have h₁ := triangle_consecutive_roots_ne b c a d e ha₁ (h.1 1) (h.1 2) (h.2.1 2)
  have h₂ := triangle_consecutive_roots_ne c a b d e ha₂ (h.1 2) (h.1 0) (h.2.1 0)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [triangleStart,triangleEnd]

theorem triangle_segment_entry_exit_of_position (a b c d e : Plane)
    (ha : 0 < orient2 a b c) (h : TriangleSegmentPosition a b c d e) :
    triangleSegmentIntersection a b c d e = triangleIndicator a b c e-triangleIndicator a b c d := by
  exact triangle_segment_entry_exit a b c d e ha h.1
    (triangle_roots_injective a b c d e (ne_of_gt ha) h)
    (fun i => second_parameter_ne_zero _ _ _ _ (h.1 i) (h.2.2 i).1)
    (fun i => second_parameter_ne_one _ _ _ _ (h.1 i) (h.2.2 i).2)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TriangleOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators Classical

theorem orient2_reverse_edge (a b c : Plane) : orient2 b a c = -orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem det2_reverse_edge (a b c d : Plane) : det2 (a-b) (d-c) = -det2 (b-a) (d-c) := by
  dsimp [det2]
  ring

theorem triangle_position_reverse (a b c d e : Plane)
    (h : TriangleSegmentPosition a b c d e) : TriangleSegmentPosition a c b d e := by
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    · change det2 (c-a) (e-d) ≠ 0
      rw [det2_reverse_edge c a d e]
      exact neg_ne_zero.mpr (h.1 2)
    · change det2 (b-c) (e-d) ≠ 0
      rw [det2_reverse_edge b c d e]
      exact neg_ne_zero.mpr (h.1 1)
    · change det2 (a-b) (e-d) ≠ 0
      rw [det2_reverse_edge a b d e]
      exact neg_ne_zero.mpr (h.1 0)
  · intro i
    fin_cases i
    · exact h.2.1 0
    · exact h.2.1 2
    · exact h.2.1 1
  · intro i
    fin_cases i
    · change orient2 a c d ≠ 0 ∧ orient2 a c e ≠ 0
      rw [orient2_reverse_edge c a d,orient2_reverse_edge c a e]
      exact ⟨neg_ne_zero.mpr (h.2.2 2).1,neg_ne_zero.mpr (h.2.2 2).2⟩
    · change orient2 c b d ≠ 0 ∧ orient2 c b e ≠ 0
      rw [orient2_reverse_edge b c d,orient2_reverse_edge b c e]
      exact ⟨neg_ne_zero.mpr (h.2.2 1).1,neg_ne_zero.mpr (h.2.2 1).2⟩
    · change orient2 b a d ≠ 0 ∧ orient2 b a e ≠ 0
      rw [orient2_reverse_edge a b d,orient2_reverse_edge a b e]
      exact ⟨neg_ne_zero.mpr (h.2.2 0).1,neg_ne_zero.mpr (h.2.2 0).2⟩

theorem triangle_intersection_reverse (a b c d e : Plane) :
    triangleSegmentIntersection a c b d e = -triangleSegmentIntersection a b c d e := by
  unfold triangleSegmentIntersection
  rw [segmentCrossingSign_reverse_left c a d e,
    segmentCrossingSign_reverse_left b c d e,segmentCrossingSign_reverse_left a b d e]
  ring

theorem oriented_triangle_entry_exit (a b c d e : Plane) (ha : orient2 a b c ≠ 0)
    (h : TriangleSegmentPosition a b c d e) :
    triangleSegmentIntersection a b c d e =
      orientedTriangleIndicator a b c e-orientedTriangleIndicator a b c d := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hac : 0 < orient2 a c b := by
      rw [triangle_area_cycle b a c,orient2_reverse_edge]
      exact neg_pos.mpr ha
    have hh := triangle_segment_entry_exit_of_position a c b d e hac (triangle_position_reverse a b c d e h)
    rw [triangle_intersection_reverse] at hh
    simp only [orientedTriangleIndicator,not_lt.mpr ha.le,ite_false]
    linarith
  · simpa only [orientedTriangleIndicator,ha,ite_true] using triangle_segment_entry_exit_of_position a b c d e ha h

theorem triangle_closed_walk_intersection_zero (a b c : Plane) (ha : orient2 a b c ≠ 0)
    (w : ℕ → Plane) (m : ℕ) (hw : w m = w 0)
    (h : ∀ j ∈ Finset.range m, TriangleSegmentPosition a b c (w j) (w (j+1))) :
    (∑ j ∈ Finset.range m, triangleSegmentIntersection a b c (w j) (w (j+1))) = 0 := by
  have hs := telescoping_real_sum (fun j => orientedTriangleIndicator a b c (w j)) m
  rw [hw,sub_self,Finset.sum_sub_distrib] at hs
  calc
    _ = ∑ j ∈ Finset.range m,
        (orientedTriangleIndicator a b c (w (j+1))-orientedTriangleIndicator a b c (w j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact oriented_triangle_entry_exit a b c _ _ ha (h j hj)
    _ = 0 := by rw [Finset.sum_sub_distrib]; linarith

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GenericPointFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_generic_point_family {κ ν : Type*} [Fintype κ] [Fintype ν]
    (q : ν → Plane) (a v : κ → Plane) (hv : ∀ k, v k ≠ 0)
    (n : ℕ) (z : Fin n → Plane) (ε : Fin n → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ p : Fin n → Plane, (∀ i, dist (p i) (z i) < ε i) ∧ Function.Injective p ∧
      (∀ i j, q j ≠ p i) ∧
      (∀ i k, det2 (p i-a k) (v k) ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ k, det2 (p j-p i) (v k) ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ l, orient2 (p i) (p j) (q l) ≠ 0) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_,?_,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨p,hp,hinj,hpq,hline,hpar,hcorn⟩ :=
      ih (fun i => z i.succ) (fun i => ε i.succ) (fun i => hε i.succ)
    obtain ⟨x,hx,hxp,hxq,hxl,hxpar,hxcorn⟩ :=
      exists_generic_point_extension p q a v hv hpq (z 0) (ε 0) (hε 0)
    refine ⟨Fin.cons x p,?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hx
      · exact hp i
    · apply Fin.cons_injective_of_injective _ hinj
      rintro ⟨i,hi⟩
      exact hxp i hi.symm
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hxq
      · exact hpq i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hxl
      · exact hline i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ k
          change det2 (p j-x) (v k) ≠ 0
          have hh : det2 (p j-x) (v k) = -det2 (x-p j) (v k) := by
            dsimp [det2]
            ring
          rw [hh]
          exact neg_ne_zero.mpr (hxpar j k)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ k
          exact hxpar i k
        · intro hij k
          exact hpar i j (fun h => hij (congrArg Fin.succ h)) k
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact False.elim (h rfl)
        · intro _ l
          change orient2 x (p j) (q l) ≠ 0
          rw [orient2_reverse_edge]
          exact neg_ne_zero.mpr (hxcorn j l)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ l
          exact hxcorn i l
        · intro hij l
          exact hcorn i j (fun h => hij (congrArg Fin.succ h)) l

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ConeIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygon_intersection_zero_of_cone (v w : ℕ → Plane) (n m : ℕ)
    (hv : v n = v 0) (hw : w m = w 0) (o : Plane)
    (ha : ∀ i ∈ Finset.range n, orient2 o (v i) (v (i+1)) ≠ 0)
    (hp : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range m,
      TriangleSegmentPosition o (v i) (v (i+1)) (w j) (w (j+1))) :
    polygonIntersection v w n m = 0 := by
  unfold polygonIntersection
  calc
    _ = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
        segmentCrossingSign (v i) (v (i+1)) (w j) (w (j+1)) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
        triangleSegmentIntersection o (v i) (v (i+1)) (w j) (w (j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (polygon_cone_cancellation v n hv o _ _).symm
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        triangleSegmentIntersection o (v i) (v (i+1)) (w j) (w (j+1)) := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact triangle_closed_walk_intersection_zero o _ _ (ha i hi) w m hw (hp i hi)

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FiniteConePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_polygon_cone_point (v w : ℕ → Plane) (n m : ℕ)
    (hv : ∀ i : Fin n, v (i.val+1) ≠ v i.val)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (hvw : ∀ i : Fin (n+1), ∀ j : Fin (m+1), w j.val ≠ v i.val) :
    ∃ o : Plane,
      (∀ i : Fin n, orient2 o (v i.val) (v (i.val+1)) ≠ 0) ∧
      (∀ j : Fin m, orient2 (w j.val) (w (j.val+1)) o ≠ 0) ∧
      (∀ i : Fin (n+1), ∀ j : Fin m, det2 (v i.val-o) (w (j.val+1)-w j.val) ≠ 0) ∧
      (∀ i : Fin (n+1), ∀ j : Fin (m+1), orient2 o (v i.val) (w j.val) ≠ 0) := by
  let ι := (Fin n ⊕ Fin m) ⊕ ((Fin (n+1) × Fin m) ⊕ (Fin (n+1) × Fin (m+1)))
  let base : ι → Plane
    | .inl (.inl i) => v i.val
    | .inl (.inr j) => w j.val
    | .inr (.inl (i,_)) => v i.val
    | .inr (.inr (i,_)) => v i.val
  let direction : ι → Plane
    | .inl (.inl i) => v (i.val+1)-v i.val
    | .inl (.inr j) => w (j.val+1)-w j.val
    | .inr (.inl (_,j)) => w (j.val+1)-w j.val
    | .inr (.inr (i,j)) => w j.val-v i.val
  have hd : ∀ k, direction k ≠ 0 := by
    rintro ((i|j)|(⟨i,j⟩|⟨i,j⟩))
    · exact sub_ne_zero.mpr (hv i)
    · exact sub_ne_zero.mpr (hw j)
    · exact sub_ne_zero.mpr (hw j)
    · exact sub_ne_zero.mpr (hvw i j)
  obtain ⟨o,_,ho⟩ := exists_near_avoiding_lines base direction hd (0 : Plane) 1 (by norm_num)
  refine ⟨o,?_,?_,?_,?_⟩
  · intro i
    rw [← triangle_area_cycle o (v i.val) (v (i.val+1))]
    change det2 (v (i.val+1)-v i.val) (o-v i.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inl (.inl i)))
  · intro j
    change det2 (w (j.val+1)-w j.val) (o-w j.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inl (.inr j)))
  · intro i j
    rw [det2_reverse_edge (v i.val) o (w j.val) (w (j.val+1))]
    exact neg_ne_zero.mpr (ho (.inr (.inl (i,j))))
  · intro i j
    rw [← triangle_area_cycle o (v i.val) (w j.val)]
    change det2 (w j.val-v i.val) (o-v i.val) ≠ 0
    rw [det2_swap]
    exact neg_ne_zero.mpr (ho (.inr (.inr (i,j))))

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GenericPolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem polygon_intersection_zero_in_line_position (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n = v 0) (hd : w m = w 0)
    (hv : ∀ i : Fin n, v (i.val+1) ≠ v i.val)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (hvw : ∀ i : Fin (n+1), ∀ j : Fin (m+1), w j.val ≠ v i.val)
    (hp : PolygonLinePosition v w n m) : polygonIntersection v w n m = 0 := by
  obtain ⟨o,ha,hb,hpar,hcorn⟩ := exists_polygon_cone_point v w n m hv hw hvw
  apply polygon_intersection_zero_of_cone v w n m hc hd o
  · intro i hi
    exact ha ⟨i,Finset.mem_range.mp hi⟩
  · intro i hi j hj
    have hin := Finset.mem_range.mp hi
    have hjm := Finset.mem_range.mp hj
    let ii : Fin n := ⟨i,Finset.mem_range.mp hi⟩
    let jj : Fin m := ⟨j,Finset.mem_range.mp hj⟩
    let i₀ : Fin (n+1) := ⟨i,by omega⟩
    let i₁ : Fin (n+1) := ⟨i+1,by omega⟩
    let j₀ : Fin (m+1) := ⟨j,by omega⟩
    let j₁ : Fin (m+1) := ⟨j+1,by omega⟩
    refine ⟨?_,?_,?_⟩
    · intro k
      fin_cases k
      · exact hpar i₀ jj
      · exact hp.1 ii jj
      · change det2 (o-v (i+1)) (w (j+1)-w j) ≠ 0
        rw [det2_reverse_edge o (v (i+1)) (w j) (w (j+1))]
        exact neg_ne_zero.mpr (hpar i₁ jj)
    · intro k
      fin_cases k
      · exact hb jj
      · exact hp.2.1 i₀ jj
      · exact hp.2.1 i₁ jj
    · intro k
      fin_cases k
      · exact ⟨hcorn i₀ j₀,hcorn i₀ j₁⟩
      · exact ⟨hp.2.2 ii j₀,hp.2.2 ii j₁⟩
      · change orient2 (v (i+1)) o (w j) ≠ 0 ∧ orient2 (v (i+1)) o (w (j+1)) ≠ 0
        rw [orient2_reverse_edge o _ _,orient2_reverse_edge o _ _]
        exact ⟨neg_ne_zero.mpr (hcorn i₁ j₀),neg_ne_zero.mpr (hcorn i₁ j₁)⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PeriodicPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem cyclicIndex_of_lt (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i<n) :
    cyclicIndex n hn i = ⟨i,hi⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hi

theorem cyclicIndex_period (n : ℕ) (hn : 0 < n) : cyclicIndex n hn n = cyclicIndex n hn 0 := by
  apply Fin.ext
  simp [cyclicIndex]

theorem periodicPolygon_closed (n : ℕ) (hn : 0 < n) (p : Fin n → Plane) :
    periodicPolygon n hn p n = periodicPolygon n hn p 0 := by
  exact congrArg p (cyclicIndex_period n hn)

theorem cyclicIndex_succ_ne (n : ℕ) (hn : 1 < n) (i : Fin n) :
    cyclicIndex n (by omega) (i.val+1) ≠ cyclicIndex n (by omega) i.val := by
  intro h
  have he := congrArg Fin.val h
  change (i.val+1)%n = i.val%n at he
  rw [Nat.mod_eq_of_lt i.isLt] at he
  by_cases hh : i.val+1=n
  · rw [hh,Nat.mod_self] at he
    omega
  · have hlt : i.val+1<n := by omega
    rw [Nat.mod_eq_of_lt hlt] at he
    omega

theorem periodicPolygon_near (n : ℕ) (hn : 0 < n) (v : ℕ → Plane) (hv : v n=v 0)
    (p : Fin n → Plane) (ε : ℝ) (hp : ∀ i, dist (p i) (v i.val) < ε) :
    ∀ i : Fin (n+1), dist (periodicPolygon n hn p i.val) (v i.val) < ε := by
  intro i
  by_cases hi : i.val<n
  · simpa only [periodicPolygon,cyclicIndex_of_lt n hn i.val hi] using hp ⟨i.val,hi⟩
  · have hin : i.val=n := by omega
    rw [hin,periodicPolygon_closed,hv]
    simpa only [periodicPolygon,cyclicIndex_of_lt n hn 0 hn] using hp ⟨0,hn⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TransversePolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentCrossingSign_self_left (a c d : Plane) : segmentCrossingSign a a c d = 0 := by
  simp [segmentCrossingSign,SegmentsCrossProperly,det2]

theorem polygon_intersection_zero_transverse (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n=v 0) (hd : w m=w 0)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (ht : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    polygonIntersection v w n m = 0 := by
  by_cases hn : 1<n
  · have hn0 : 0<n := by omega
    obtain ⟨ε,hε,hstable⟩ := exists_polygon_intersection_stability_radius v w n m ht
    obtain ⟨p,hnear,hinj,hpq,hline,hpar,hcorn⟩ := exists_generic_point_family
      (fun j : Fin (m+1) => w j.val) (fun j : Fin m => w j.val)
      (fun j : Fin m => w (j.val+1)-w j.val) (fun j => sub_ne_zero.mpr (hw j))
      n (fun i => v i.val) (fun _ => ε) (fun _ => hε)
    let v' := periodicPolygon n hn0 p
    have hclose : v' n=v' 0 := periodicPolygon_closed n hn0 p
    have hv' (i : Fin n) : v' (i.val+1) ≠ v' i.val :=
      hinj.ne (cyclicIndex_succ_ne n hn i)
    have hpoint (i : Fin (n+1)) (j : Fin (m+1)) : w j.val ≠ v' i.val := hpq _ j
    have hposition : PolygonLinePosition v' w n m := by
      refine ⟨?_,?_,?_⟩
      · intro i j
        exact hpar _ _ (Ne.symm (cyclicIndex_succ_ne n hn i)) j
      · intro i j
        change det2 (w (j.val+1)-w j.val) (p (cyclicIndex n hn0 i.val)-w j.val) ≠ 0
        rw [det2_swap]
        exact neg_ne_zero.mpr (hline _ j)
      · intro i j
        exact hcorn _ _ (Ne.symm (cyclicIndex_succ_ne n hn i)) j
    have hzero := polygon_intersection_zero_in_line_position v' w n m hclose hd hv' hw hpoint hposition
    have heq := hstable v' (periodicPolygon_near n hn0 v hc p ε hnear)
    rwa [heq] at hzero
  · have hn' : n=0 ∨ n=1 := by omega
    rcases hn' with rfl | rfl
    · simp [polygonIntersection]
    · simp only [polygonIntersection,Finset.sum_range_one]
      rw [hc]
      simp only [segmentCrossingSign_self_left,Finset.sum_const_zero]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ClosedPolygonIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closed_polygon_intersection_zero (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n=v 0) (hd : w m=w 0)
    (ht : ∀ i : Fin n, ∀ j : Fin m,
      SegmentPairTransverse (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1))) :
    polygonIntersection v w n m = 0 := by
  by_cases hm : 1 < m
  · have hm0 : 0 < m := by omega
    have hswap (j : Fin m) (i : Fin n) :
        SegmentPairTransverse (w j.val) (w (j.val+1)) (v i.val) (v (i.val+1)) :=
      segmentPairTransverse_swap _ _ _ _ (ht i j)
    obtain ⟨ε,hε,hstable⟩ := exists_polygon_transversality_radius w v m n hswap
    obtain ⟨p,hnear,hinj,_⟩ := exists_generic_point_family
      (fun i : Fin 0 => (Fin.elim0 i : Plane)) (fun i : Fin 0 => (Fin.elim0 i : Plane))
      (fun i : Fin 0 => (Fin.elim0 i : Plane)) (fun i => Fin.elim0 i)
      m (fun i => w i.val) (fun _ => ε) (fun _ => hε)
    let w' := periodicPolygon m hm0 p
    have hclose : w' m=w' 0 := periodicPolygon_closed m hm0 p
    have hw' (j : Fin m) : w' (j.val+1) ≠ w' j.val := hinj.ne (cyclicIndex_succ_ne m hm j)
    obtain ⟨htrans,heq⟩ := hstable w' (periodicPolygon_near m hm0 w hd p ε hnear)
    have hzero := polygon_intersection_zero_transverse v w' n m hc hclose hw'
      (fun i j => segmentPairTransverse_swap _ _ _ _ (htrans j i))
    have hrev := polygonIntersection_swap v w' n m
    rw [hzero,neg_zero,heq] at hrev
    rw [polygonIntersection_swap v w n m] at hrev
    exact neg_eq_zero.mp hrev
  · have hm' : m=0 ∨ m=1 := by omega
    rcases hm' with rfl | rfl
    · simp [polygonIntersection]
    · have hz : polygonIntersection w v 1 n = 0 := by
        simp only [polygonIntersection,Finset.sum_range_one]
        rw [hd]
        simp only [segmentCrossingSign_self_left,Finset.sum_const_zero]
      rw [polygonIntersection_swap v w n 1] at hz
      exact neg_eq_zero.mp hz

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
-- module Solutions.OAIQ4_Cc.Crossing_PolygonComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem polygonIntersection_join_left (v w z : ℕ → Plane) (n m k : ℕ) (h : v n=w 0) :
    polygonIntersection (joinedSequence v w n) z (n+m) k =
      polygonIntersection v z n k+polygonIntersection w z m k := by
  unfold polygonIntersection
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [joinedSequence_left v w n h i (by omega),joinedSequence_left v w n h (i+1) (by omega)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [joinedSequence_right,show n+i+1=n+(i+1) by omega,joinedSequence_right]

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

theorem PolygonalParametrization.direction_ne_zero {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : ℕ) (hi : i < P.pieces) : P.vertices (i+1) - P.vertices i ≠ 0 :=
  (toZarankiewiczParametrization P).direction_ne_zero hγ i hi

end Paper170

end
end

section

noncomputable section
open Set Zarankiewicz
open scoped BigOperators
namespace Paper170Geometry

theorem sum_eq_sum_of_unique_match {A B : Type} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) (R : A → B → Prop)
    (hf : ∀a, f a≠0 → ∃!b, g b≠0 ∧ R a b)
    (hg : ∀b, g b≠0 → ∃!a, f a≠0 ∧ R a b)
    (heq : ∀a b, f a≠0 → g b≠0 → R a b → f a=g b) :
    ∑a, f a = ∑b, g b := by
  classical
  have hrow (a : A) : f a = ∑b : B, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0 := by
    by_cases ha : f a=0
    · simp [ha]
    · obtain ⟨b, hb, hu⟩ := hf a ha
      symm
      rw [Finset.sum_eq_single b]
      · rw [ite_eq_left ⟨ha, hb.1, hb.2⟩]
      · intro c _ hcb
        have hn : ¬(f a≠0 ∧ g c≠0 ∧ R a c) := fun h => hcb (hu c h.2)
        simp only [ite_eq_right hn]
      · simp
  have hcol (b : B) : (∑a : A, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0) = g b := by
    by_cases hb : g b=0
    · simp [hb]
    · obtain ⟨a, ha, hu⟩ := hg b hb
      rw [Finset.sum_eq_single a]
      · rw [ite_eq_left ⟨ha.1,hb,ha.2⟩]
        exact heq a b ha.1 hb ha.2
      · intro c _ hca
        have hn : ¬(f c≠0 ∧ g b≠0 ∧ R c b) := fun h => hca (hu c ⟨h.1,h.2.2⟩)
        simp only [ite_eq_right hn]
      · simp
  calc
    ∑a, f a = ∑a, ∑b, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0 :=
      Finset.sum_congr rfl (fun a _ => hrow a)
    _ = ∑b, ∑a, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0 := Finset.sum_comm
    _ = ∑b, g b := Finset.sum_congr rfl (fun b _ => hcol b)

theorem segmentCrossingSign_ne_zero_iff (a b c d : Plane) :
    segmentCrossingSign a b c d ≠ 0 ↔ SegmentsCrossProperly a b c d := by
  unfold segmentCrossingSign
  split_ifs <;> simp_all

theorem meeting_of_mem_openSegments (a b c d x : Plane)
    (hx : x∈openSegmentTrace a b) (hy : x∈openSegmentTrace c d) :
    ∃s∈Ioo (0:ℝ) 1, ∃t∈Ioo (0:ℝ) 1, segmentPoint a b s=segmentPoint c d t := by
  obtain ⟨s,hs,hsx⟩ := hx
  obtain ⟨t,ht,htx⟩ := hy
  exact ⟨s,hs,t,ht,hsx.trans htx.symm⟩

theorem openSegments_inter_subsingleton (a b c d : Plane) (hdet : det2 (b-a) (d-c)≠0) :
    (openSegmentTrace a b ∩ openSegmentTrace c d).Subsingleton := by
  rintro x ⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩ y ⟨⟨u,hu,huy⟩,⟨v,hv,hvy⟩⟩
  have he := segment_intersection_parameters_unique a b c d hdet s t u v
    (hsx.trans htx.symm) (huy.trans hvy.symm)
  exact hsx.symm.trans ((congrArg (segmentPoint a b) he.1).trans huy)

theorem segmentCrossingSign_eq_of_pos_directions
    (a b c d a' b' c' d' x : Plane) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (he : b-a=r • (b'-a')) (hf : d-c=s • (d'-c'))
    (hxa : x∈openSegmentTrace a b) (hxc : x∈openSegmentTrace c d)
    (hxa' : x∈openSegmentTrace a' b') (hxc' : x∈openSegmentTrace c' d') :
    segmentCrossingSign a b c d = segmentCrossingSign a' b' c' d' := by
  have hm := meeting_of_mem_openSegments a b c d x hxa hxc
  have hm' := meeting_of_mem_openSegments a' b' c' d' x hxa' hxc'
  simp only [segmentCrossingSign, SegmentsCrossProperly, hm, hm', and_true,
    he, hf, det2_smul_left, det2_smul_right, ne_eq, mul_eq_zero,
    ne_of_gt hr, ne_of_gt hs, false_or, mul_pos_iff_of_pos_left hr,
    mul_pos_iff_of_pos_left hs]

theorem polygonIntersection_eq_fin_sum (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection v w n m = ∑i : Fin n, ∑j : Fin m,
      segmentCrossingSign (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1)) := by
  unfold polygonIntersection
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]

end Paper170Geometry

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

/-- Interior overlap is sufficient for the positive direction comparison. -/
theorem path_segments_direction_of_mem {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η)
    (a₀ a₁ b₀ b₁ : unitInterval) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (A B C D : Plane)
    (hγseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val)
    (hηseg : ∀t, η (intervalSegment b₀ b₁ t) = Paper170.segmentPoint C D t.val)
    (x : Plane) (hx : x ∈ openSegmentTrace A B) (hy : x ∈ openSegmentTrace C D) :
    ∃ r : ℝ, 0 < r ∧ D-C = r • (B-A) := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, hqx⟩ := hy
  exact path_segments_direction γ η hγ hη hrange a₀ a₁ b₀ b₁ ha hb A B C D
    hγseg hηseg ⟨p, hp.1.le, hp.2.le⟩ ⟨q, hq.1.le, hq.2.le⟩ hp.2 hq.2
    (hpx.trans hqx.symm)

end Paper170

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
-- module Solutions.OAIQ4_Cc.Crossing_SegmentAffineForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem segmentPoint_start_form (a b : Plane) (t : ℝ) :
    segmentPoint a b t = a+t • (b-a) := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

end Zarankiewicz

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

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry

/-- A point away from the subdivision knots lies strictly inside one piece. -/
theorem parametrization_knot_interval {a b : Paper170.Plane} {γ : Path a b}
    (P : Paper170.PolygonalParametrization γ) (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) (hne : ∀i, t ≠ P.knot i) :
    ∃i : Fin P.pieces, P.knot i.castSucc < t ∧ t < P.knot i.succ := by
  classical
  have hex : ∃i, t < P.knot i := ⟨Fin.last P.pieces, by simpa only [P.last] using ht.2⟩
  let j := Fin.find (fun i => t < P.knot i) hex
  have hj : t < P.knot j := Fin.find_spec hex
  have hj0 : j ≠ 0 := by
    intro he
    rw [he, P.first] at hj
    exact (lt_asymm ht.1 hj)
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hj0
  refine ⟨i, ?_, by simpa only [hi] using hj⟩
  have hm : ¬t < P.knot i.castSucc := Fin.find_min hex (by change i.castSucc < j; rw [← hi]; exact Fin.castSucc_lt_succ)
  exact lt_of_le_of_ne (le_of_not_gt hm) (hne i.castSucc).symm

/-- The open part of a subdivided path is exactly its open segment. -/
theorem parametrization_open_piece {a b : Paper170.Plane} {γ : Path a b}
    (P : Paper170.PolygonalParametrization γ) (i : Fin P.pieces) :
    γ '' Ioo (P.knot i.castSucc) (P.knot i.succ) =
      openSegmentTrace (P.vertices i.val) (P.vertices (i.val+1)) := by
  have hab := P.increasing (Fin.castSucc_lt_succ (i := i))
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu⟩ := intervalSegment_surjective_interval _ _ hab t ⟨ht.1.le, ht.2.le⟩
    have hu0 : 0 < (u : ℝ) := by
      by_contra hn
      have hue : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) u.property.1)
      have he : P.knot i.castSucc = t := by simpa [hue, intervalSegment] using hu
      exact ht.1.ne he
    have hu1 : (u : ℝ) < 1 := by
      by_contra hn
      have hue : u = 1 := Subtype.ext (le_antisymm u.property.2 (le_of_not_gt hn))
      have he : P.knot i.succ = t := by simpa [hue, intervalSegment] using hu
      exact ht.2.ne he.symm
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    exact ((Paper170.toZarankiewiczParametrization P).segment_formula i u).symm.trans
      (congrArg γ hu)
  · rintro ⟨s, hs, rfl⟩
    let u : unitInterval := ⟨s, hs.1.le, hs.2.le⟩
    refine ⟨intervalSegment (P.knot i.castSucc) (P.knot i.succ) u,
      intervalSegment_strict_between _ _ u hab hs, ?_⟩
    exact (Paper170.toZarankiewiczParametrization P).segment_formula i u

/-- An injective polygonal path is locally a straight segment away from its knots. -/
theorem locallyStraightAt_of_not_knot {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (P : Paper170.PolygonalParametrization (D.edge e)) (t : unitInterval)
    (ht : t ∈ Ioo (0 : unitInterval) 1) (hne : ∀i, t ≠ P.knot i) :
    LocallyStraightAt D e (D.edge e t) := by
  obtain ⟨i, hti⟩ := parametrization_knot_interval P t ht hne
  have hem := (D.edge e).continuous.isClosedEmbedding (D.edge_injective e)
  obtain ⟨U, hU, heq⟩ := hem.isInducing.isOpen_iff.mp
    (isOpen_Ioo : IsOpen (Ioo (P.knot i.castSucc) (P.knot i.succ)))
  have hpiece := parametrization_open_piece P i
  have hsub : Ioo (P.knot i.castSucc) (P.knot i.succ) ⊆ Ioo (0 : unitInterval) 1 := by
    intro s hs
    exact ⟨lt_of_le_of_lt (P.knot i.castSucc).property.1 hs.1,
      lt_of_lt_of_le hs.2 (P.knot i.succ).property.2⟩
  refine ⟨P.vertices i.val, P.vertices (i.val+1), ?_, ?_, U, hU, ?_, ?_⟩
  · exact fun he => P.direction_ne_zero (D.edge_injective e) i.val i.isLt (sub_eq_zero.mpr he.symm)
  · rw [← hpiece]
    exact ⟨t, hti, rfl⟩
  · change t ∈ (D.edge e) ⁻¹' U
    rw [heq]
    exact hti
  · intro z hz
    rw [← hpiece]
    constructor
    · rintro ⟨s, _, rfl⟩
      refine ⟨s, ?_, rfl⟩
      rw [← heq]
      exact hz
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hsub hs, rfl⟩

theorem normalized_locallyStraight {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (N : Paper170.NormalizedDrawing graph) : LocallyStraightCrossings N.toAdmissibleDrawing := by
  refine ⟨?_⟩
  intro e f hef x hxe hxf
  have hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing := ⟨e, f, hef, hxe, hxf⟩
  have hlocal (g : Edge) (hg : x ∈ Paper170.edgeInterior N.toContinuousDrawing g) :
      LocallyStraightAt N.toContinuousDrawing g x := by
    obtain ⟨t, ht, rfl⟩ := hg
    apply locallyStraightAt_of_not_knot N.toContinuousDrawing g (N.polygonal g) t ht
    intro i he
    exact N.crossings_not_knots g i (he ▸ hx)
  exact ⟨hlocal e hxe, hlocal f hxf⟩

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
open scoped Topology
namespace Paper170Geometry

/-- A crossing chart makes the local intersection a single point. -/
theorem properCrossing_locally_unique (A B : Set Paper170.Plane) (x : Paper170.Plane)
    (h : Paper170.ProperCrossing A B x) :
    ∃U : Set Paper170.Plane, IsOpen U ∧ x ∈ U ∧
      ∀y ∈ U, y ∈ A → y ∈ B → y = x := by
  obtain ⟨chart, hx, hz, hA, hB⟩ := h.chart_exists
  refine ⟨chart.source, chart.open_source, hx, ?_⟩
  intro y hy hyA hyB
  have hyA' := (chart_image_mem_iff chart A {z | z.2=0} hA y hy).mp hyA
  have hyB' := (chart_image_mem_iff chart B {z | z.1=0} hB y hy).mp hyB
  apply chart.injOn hy hx
  rw [hz]
  exact Prod.ext hyB' hyA'

/-- Two straight segments meeting locally only once have independent directions. -/
theorem local_segment_directions_ne_zero (a b c d x : Plane)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hxab : x ∈ openSegmentTrace a b) (hxcd : x ∈ openSegmentTrace c d)
    (U : Set Plane) (hU : IsOpen U) (hxU : x ∈ U)
    (hunique : ∀y ∈ U, y ∈ openSegmentTrace a b → y ∈ openSegmentTrace c d → y=x) :
    det2 (b-a) (d-c) ≠ 0 := by
  intro hdet
  obtain ⟨s, hs, hsx⟩ := hxab
  obtain ⟨t, ht, htx⟩ := hxcd
  let k := dot2 (b-a) (d-c) / squaredLength (b-a)
  have hparallel : d-c = k • (b-a) := vector_parallel_of_det_zero _ _ (sub_ne_zero.mpr hab.symm) hdet
  let f : ℝ → Plane := fun r => x + r • (d-c)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f 0 = x := by simp [f]
  have hevent : ∀ᶠr : ℝ in 𝓝 0,
      f r ∈ U ∧ s+r*k ∈ Ioo (0:ℝ) 1 ∧ t+r ∈ Ioo (0:ℝ) 1 := by
    have h₁ := hf.continuousAt.eventually (show U ∈ 𝓝 (f 0) by simpa only [hf0] using hU.mem_nhds hxU)
    have h₂ : ∀ᶠr : ℝ in 𝓝 0, s+r*k ∈ Ioo (0:ℝ) 1 := by
      have hc : Continuous (fun r : ℝ => s+r*k) := by fun_prop
      apply hc.continuousAt.eventually
      change Ioo (0:ℝ) 1 ∈ 𝓝 (s+0*k)
      simpa only [zero_mul, add_zero] using (isOpen_Ioo.mem_nhds hs)
    have h₃ : ∀ᶠr : ℝ in 𝓝 0, t+r ∈ Ioo (0:ℝ) 1 := by
      have hc : Continuous (fun r : ℝ => t+r) := by fun_prop
      apply hc.continuousAt.eventually
      change Ioo (0:ℝ) 1 ∈ 𝓝 (t+0)
      simpa only [add_zero] using (isOpen_Ioo.mem_nhds ht)
    filter_upwards [h₁, h₂, h₃] with r h₁ h₂ h₃ using ⟨h₁,h₂,h₃⟩
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hevent
  have he : dist (ε/2) (0:ℝ) < ε := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  obtain ⟨hfU, hs', ht'⟩ := hsmall he
  have habf : segmentPoint a b (s+(ε/2)*k) = f (ε/2) := by
    dsimp [f]
    rw [segmentPoint_start_form, show x = a+s • (b-a) from hsx.symm.trans (segmentPoint_start_form a b s)]
    rw [hparallel, smul_smul, add_smul]
    abel
  have hcdf : segmentPoint c d (t+ε/2) = f (ε/2) := by
    dsimp [f]
    rw [segmentPoint_start_form, show x = c+t • (d-c) from htx.symm.trans (segmentPoint_start_form c d t)]
    rw [add_smul]
    abel
  have hfx : f (ε/2) = x := hunique _ hfU ⟨_,hs',habf⟩ ⟨_,ht',hcdf⟩
  have hzero : (ε/2) • (d-c) = 0 := by simpa only [f, add_eq_left] using hfx
  exact (smul_eq_zero.mp hzero).elim (ne_of_gt (by positivity)) (sub_ne_zero.mpr hcd.symm)

/-- Local straightness and the actual crossing charts imply transversality. -/
theorem locallyTransverse_of_locallyStraight {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (D : Paper170.AdmissibleDrawing graph) (h : LocallyStraightCrossings D) :
    LocallyTransverseCrossings D := by
  refine ⟨?_⟩
  intro e f hef x hxe hxf
  obtain ⟨he,hf⟩ := h.at_crossing e f hef x hxe hxf
  obtain ⟨a,b,hab,hxab,U,hU,hxU,hAU⟩ := he.exists_line
  obtain ⟨c,d,hcd,hxcd,V,hV,hxV,hBV⟩ := hf.exists_line
  obtain ⟨W,hW,hxW,hunique⟩ := properCrossing_locally_unique _ _ x (D.crossings_proper e f hef x hxe hxf)
  have hdet : det2 (b-a) (d-c) ≠ 0 := by
    apply local_segment_directions_ne_zero a b c d x hab hcd hxab hxcd (U∩V∩W)
      ((hU.inter hV).inter hW) ⟨⟨hxU,hxV⟩,hxW⟩
    intro y hy hyA hyB
    exact hunique y hy.2 ((hAU y hy.1.1).mpr hyA) ((hBV y hy.1.2).mpr hyB)
  exact ⟨a,b,c,d,hdet,hxab,hxcd,U∩V,hU.inter hV,⟨hxU,hxV⟩,
    fun y hy => hAU y hy.1,fun y hy => hBV y hy.2⟩

theorem normalized_locallyTransverse {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
    (N : Paper170.NormalizedDrawing graph) : LocallyTransverseCrossings N.toAdmissibleDrawing :=
  locallyTransverse_of_locallyStraight N.toAdmissibleDrawing (normalized_locallyStraight N)

end Paper170Geometry

end
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

end Paper170Geometry

end
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

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedTraceDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem center_segment_in_disk (o p : Plane) (r : ℝ) (hp : squaredLength (p-o)=r^2) :
    segment ℝ o p ⊆ closedRoundDisk o r := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  have he : squaredLength (segmentPoint o p t.val-o)=t.val^2*squaredLength (p-o) := by
    dsimp [segmentPoint,squaredLength]
    ring
  have ht2 : t.val^2 ≤ 1 := by nlinarith [t.property.1,t.property.2]
  have hh := mul_le_mul_of_nonneg_right ht2 (sq_nonneg r)
  change squaredLength (x-o) ≤ r^2
  have ht' : segmentPoint o p t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  rw [← ht',he,hp]
  simpa only [one_mul] using hh

end Zarankiewicz

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
-- module Solutions.OAIQ4_Cc.Crossing_TruncatedSegmentTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segment_parameter_strict_of_avoids_endpoints (a b x : Plane) (S : Set Plane)
    (hx : x ∈ S) (ha : a ∉ S) (hb : b ∉ S) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (he : segmentPoint a b t=x) : t ∈ Set.Ioo (0 : ℝ) 1 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h,segmentPoint_zero] at he
    exact ha (he.symm ▸ hx)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h,segmentPoint_one] at he
    exact hb (he.symm ▸ hx)
  exact ⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩

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

theorem minimum_piece_crossing_open (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (x : Plane) (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing)
    (hseg : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    x ∈ openSegmentTrace (P.vertices i) (P.vertices (i+1)) := by
  rw [← Path.range_segment] at hseg
  obtain ⟨t,ht⟩ := hseg
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp only [Path.source] at ht
    exact minimum_vertices_not_crossing D hstraight e P hmin i (by omega) (ht.symm ▸ hx)
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    simp only [Path.target] at ht
    exact minimum_vertices_not_crossing D hstraight e P hmin (i+1) (by omega) (ht.symm ▸ hx)
  refine ⟨t.val,⟨?_,?_⟩,?_⟩
  · exact lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
  · simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

end Paper170Geometry

end
end

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
theorem drawing_edge_trace_decomposition (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    Set.range (D.edge e)=
      segment ℝ (D.vertex ((graph.src e))) (P.startPort r) ∪
        Set.range (polygonalArcPath (P.truncatedVertices r) P.pieces) ∪
        segment ℝ (P.endPort r) (D.vertex ((graph.dst e))) := by
  have hp := drawing_chain_pieces_pos D e P
  have hs : segment ℝ (D.vertex ((graph.src e))) (P.startPort r) ⊆ Set.range (D.edge e) := by
    have hx := openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment (P.vertices 0) (P.vertices 1) r hr hfirst)
    have hh := ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hx).trans (P.inside 0 hp)
    simpa only [PolygonalChain.startPort,P.first] using hh
  have ht : segment ℝ (P.endPort r) (D.vertex ((graph.dst e))) ⊆ Set.range (D.edge e) := by
    have hlen : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
      rwa [squaredLength_sub_comm]
    have hx := openSegmentTrace_subset_segment _ _
      (openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hlen))
    have hinside := P.inside (P.pieces-1) (by omega)
    rw [show P.pieces-1+1=P.pieces by omega] at hinside
    have hh := ((convex_segment (𝕜 := ℝ) _ _).segment_subset hx (right_mem_segment ℝ _ _)).trans hinside
    simpa only [PolygonalChain.endPort,P.last] using hh
  let T := P.truncated hp r hr hfirst hlast
  let G := ((Path.segment (D.vertex ((graph.src e))) (P.startPort r)).trans T.path).trans
    (Path.segment (P.endPort r) (D.vertex ((graph.dst e))))
  have hG : Set.range G ⊆ Set.range (D.edge e) := by
    dsimp [G]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset (Set.union_subset hs T.path_range_subset) ht
  have he := path_range_eq_of_subset (D.edge e) G (D.edge_injective e) hG
  calc
    Set.range (D.edge e) = Set.range G := he.symm
    _ = _ := by
      dsimp [G]
      rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
      rfl

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
theorem crossing_mem_truncated_edge (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : Edge) (x : Plane) (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing)
    (hxe : x ∈ Paper170.edgeInterior D.toContinuousDrawing e) :
    x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) := by
  have hh := edgeInterior_subset_range D.toContinuousDrawing e hxe
  rw [drawing_edge_trace_decomposition D.toContinuousDrawing e (P e) r hr (hshort e).1 (hshort e).2] at hh
  rcases hh with (hs | hm) | ht
  · have hmem := center_segment_in_disk (D.vertex ((graph.src e))) ((P e).startPort r) r
      (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r) hs
    exact False.elim (Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.src e))) hmem hx)
  · exact hm
  · have ht' : x ∈ segment ℝ (D.vertex ((graph.dst e))) ((P e).endPort r) := by
      simpa only [segment_symm ℝ ((P e).endPort r) (D.vertex ((graph.dst e)))] using ht
    have hmem := center_segment_in_disk (D.vertex ((graph.dst e))) ((P e).endPort r) r
      (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r) ht'
    exact False.elim (Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.dst e))) hmem hx)

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
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem truncated_vertices_not_crossing (D : Paper170.AdmissibleDrawing graph)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : Edge) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (P e).truncatedVertices r i ∉ Paper170.crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [(P e).truncatedVertices_first]
    intro hx
    have hc := (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.src e))) hc hx
  by_cases hn : i=(P e).pieces
  · subst i
    rw [(P e).truncatedVertices_last (drawing_chain_pieces_pos D.toContinuousDrawing e (P e))]
    intro hx
    have hc := (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.dst e))) hc hx
  · simp only [PolygonalChain.truncatedVertices,ite_eq_right h0,ite_eq_right hn]
    exact minimum_vertices_not_crossing D hstraight e (P e) (hmin e) i hi

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

theorem vertices_not_crossing [Fintype Vertex] {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (e : Edge) (i : ℕ) (hi : i ≤ V.pieces e) : V.vertices e i ∉ Paper170.crossingPoints D.toContinuousDrawing :=
  truncated_vertices_not_crossing D hnorm hstraight V.chain V.minimal V.radius V.piece_clearance e i hi

end Paper170Geometry.VertexTruncation

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

theorem signedIntersection_self (e : Edge) : V.signedIntersection e e=0 := by
  simp [signedIntersection]

end Paper170Geometry.VertexTruncation

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}

theorem intersection_join_left (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection (P.join Q).vertices w (P.join Q).pieces k=
      polygonIntersection P.vertices w P.pieces k+polygonIntersection Q.vertices w Q.pieces k :=
  polygonIntersection_join_left _ _ _ _ _ _ (P.last.trans Q.first.symm)

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolygonalChainTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O T : Set Plane} {a b c d e : Plane}

theorem transverse_swap (P : PolygonalChain O a b) (Q : PolygonalChain T d e)
    (h : P.Transverse Q) : Q.Transverse P :=
  fun j i => segmentPairTransverse_swap _ _ _ _ (h i j)

theorem transverse_join_left (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (hP : P.Transverse R) (hQ : Q.Transverse R) :
    (P.join Q).Transverse R := by
  intro i j
  change SegmentPairTransverse (joinedSequence P.vertices Q.vertices P.pieces i.val)
    (joinedSequence P.vertices Q.vertices P.pieces (i.val+1)) _ _
  have hi : i.val<P.pieces+Q.pieces := i.isLt
  by_cases hip : i.val<P.pieces
  · rw [joinedSequence_left _ _ _ (P.last.trans Q.first.symm) i.val hip.le,
      joinedSequence_left _ _ _ (P.last.trans Q.first.symm) (i.val+1) (by omega)]
    exact hP ⟨i.val,hip⟩ j
  · have he : i.val=P.pieces+(i.val-P.pieces) := by omega
    have he' : i.val+1=P.pieces+(i.val-P.pieces+1) := by omega
    have h₀ : joinedSequence P.vertices Q.vertices P.pieces i.val=Q.vertices (i.val-P.pieces) := by
      conv_lhs => rw [he]
      exact joinedSequence_right _ _ _ _
    have h₁ : joinedSequence P.vertices Q.vertices P.pieces (i.val+1)=Q.vertices (i.val-P.pieces+1) := by
      rw [he',joinedSequence_right]
    rw [h₀,h₁]
    exact hQ ⟨i.val-P.pieces,by omega⟩ j

theorem closed_intersection_zero (P : PolygonalChain O a a) (Q : PolygonalChain T d d)
    (h : P.Transverse Q) : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=0 :=
  closed_polygon_intersection_zero _ _ _ _ (P.last.trans P.first.symm) (Q.last.trans Q.first.symm) h

end Zarankiewicz.PolygonalChain

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_FinitePolygonalComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

theorem finitePolygonalChain_intersection_left (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (w : ℕ → Plane) (k n : ℕ) :
    polygonIntersection (finitePolygonalChain O v h0 P n).vertices w (finitePolygonalChain O v h0 P n).pieces k=
      ∑ i ∈ Finset.range n, polygonIntersection (P i).vertices w (P i).pieces k := by
  induction n with
  | zero => simp [finitePolygonalChain,PolygonalChain.point,polygonIntersection]
  | succ n ih =>
    change polygonIntersection ((finitePolygonalChain O v h0 P n).join (P n)).vertices w
      ((finitePolygonalChain O v h0 P n).join (P n)).pieces k=_
    rw [PolygonalChain.intersection_join_left,ih,Finset.sum_range_succ]

theorem finitePolygonalChain_intersection_right (O : Set Plane) (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (w : ℕ → Plane) (k n : ℕ) :
    polygonIntersection w (finitePolygonalChain O v h0 P n).vertices k (finitePolygonalChain O v h0 P n).pieces=
      ∑ i ∈ Finset.range n, polygonIntersection w (P i).vertices k (P i).pieces := by
  rw [polygonIntersection_swap,finitePolygonalChain_intersection_left]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (polygonIntersection_swap _ _ _ _).symm

theorem finitePolygonalChain_transverse_left {O T : Set Plane} (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) {a b : Plane} (Q : PolygonalChain T a b)
    (n : ℕ) (h : ∀ i, i<n → (P i).Transverse Q) : (finitePolygonalChain O v h0 P n).Transverse Q := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    exact (finitePolygonalChain O v h0 P n).transverse_join_left (P n) Q
      (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem finitePolygonalChain_transverse_right {O T : Set Plane} (v : ℕ → Plane) (h0 : v 0 ∈ O)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) {a b : Plane} (Q : PolygonalChain T a b)
    (n : ℕ) (h : ∀ i, i<n → Q.Transverse (P i)) : Q.Transverse (finitePolygonalChain O v h0 P n) :=
  (finitePolygonalChain O v h0 P n).transverse_swap Q
    (finitePolygonalChain_transverse_left v h0 P Q n (fun i hi => Q.transverse_swap (P i) (h i hi)))

theorem finitePolygonalChain_intersection_double {O T : Set Plane}
    (v w : ℕ → Plane) (hv : v 0 ∈ O) (hw : w 0 ∈ T)
    (P : ∀ i, PolygonalChain O (v i) (v (i+1))) (Q : ∀ j, PolygonalChain T (w j) (w (j+1)))
    (n k : ℕ) :
    polygonIntersection (finitePolygonalChain O v hv P n).vertices (finitePolygonalChain T w hw Q k).vertices
      (finitePolygonalChain O v hv P n).pieces (finitePolygonalChain T w hw Q k).pieces =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k, polygonIntersection (P i).vertices (Q j).vertices (P i).pieces (Q j).pieces := by
  rw [finitePolygonalChain_intersection_left]
  apply Finset.sum_congr rfl
  intro i hi
  exact finitePolygonalChain_intersection_right _ _ _ _ _ _ _

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

/-! Fixed vertex half-order kernels on actual incident edge flags. -/
noncomputable section
open Zarankiewicz
open scoped Classical
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem incidentCast_refl {j : Vertex} (e : IncidentEdges graph j) :
    incidentCast (rfl : j=j) e=e := Subtype.ext rfl

theorem incidentFlag_cast {j k : Vertex} (h : j=k) (e : IncidentEdges graph j) :
    (⟨k,incidentCast h e⟩ : IncidentFlag graph)=⟨j,e⟩ := by
  subst k
  rw [incidentCast_refl]

theorem dartPassageNext_flag (d : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (i : ℕ) :
    (⟨(d i).snd,dartPassageNext d hd i⟩ : IncidentFlag graph)=dartSourceFlag (d (i+1)) :=
  incidentFlag_cast (hd i).symm _

namespace TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem vertexChordPairing_flags (j k : Vertex)
    (a b : IncidentEdges graph j) (c d : IncidentEdges graph k) :
    C.vertexChordPairing j k a b c d=
      C.flagPairing ⟨j,a⟩ ⟨k,c⟩-C.flagPairing ⟨j,a⟩ ⟨k,d⟩-
        C.flagPairing ⟨j,b⟩ ⟨k,c⟩+C.flagPairing ⟨j,b⟩ ⟨k,d⟩ := by
  by_cases h : k=j
  · subst k
    simp only [vertexChordPairing,flagPairing,dite_eq_left rfl,incidentCast_refl,chordEndpointPairing,dite_true]
    ring
  · simp only [vertexChordPairing,flagPairing,dite_eq_right h,sub_zero,add_zero]

theorem passagePairing_flags (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ) :
    C.passagePairing d f hd hf i j=
      C.flagPairing (dartTargetFlag (d i)) (dartTargetFlag (f j))-
        C.flagPairing (dartTargetFlag (d i)) (dartSourceFlag (f (j+1)))-
        C.flagPairing (dartSourceFlag (d (i+1))) (dartTargetFlag (f j))+
        C.flagPairing (dartSourceFlag (d (i+1))) (dartSourceFlag (f (j+1))) := by
  rw [passagePairing,C.vertexChordPairing_flags,dartPassageNext_flag,dartPassageNext_flag]
  rfl

theorem dart_endpoint_pairing (a b : OrientedDart graph) :
    C.flagPairing (dartTargetFlag a) (dartTargetFlag b)-
      C.flagPairing (dartTargetFlag a) (dartSourceFlag b)-
      C.flagPairing (dartSourceFlag a) (dartTargetFlag b)+
      C.flagPairing (dartSourceFlag a) (dartSourceFlag b)=
        dartSign a*dartSign b*C.edgeEndpointPairing a.edge b.edge := by
  rcases a with ⟨e,a⟩
  rcases b with ⟨f,b⟩
  cases a <;> cases b <;>
    simp [dartSign,edgeEndpointPairing,forwardDart,dartSourceFlag,dartTargetFlag,
      dartSourceIncident,dartTargetIncident,OrientedDart.fst,OrientedDart.snd]
  all_goals ring

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_CyclicSumArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open scoped BigOperators

theorem sum_range_cycle_succ {A : Type*} [AddCommGroup A] (f : ℕ → A) (N : ℕ)
    (hN : f N=f 0) : (∑ i ∈ Finset.range N, f (i+1))=∑ i ∈ Finset.range N, f i := by
  apply add_right_cancel (b := f 0)
  calc
    _ = ∑ i ∈ Finset.range (N+1), f i := (Finset.sum_range_succ' f N).symm
    _ = _ := by rw [Finset.sum_range_succ,hN]

theorem double_sum_cycle_shift_right {A B : Type*} (d : ℕ → A) (f : ℕ → B)
    (N K : ℕ) (hK : f K=f 0) (H : A → B → ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f (j+1)))=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f j) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_range_cycle_succ (fun j => H (d i) (f j)) K (congrArg (H (d i)) hK)

theorem double_sum_cycle_shift_left {A B : Type*} (d : ℕ → A) (f : ℕ → B)
    (N K : ℕ) (hN : d N=d 0) (H : A → B → ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d (i+1)) (f j))=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, H (d i) (f j) :=
  sum_range_cycle_succ (fun i => ∑ j ∈ Finset.range K, H (d i) (f j)) N
    (congrArg (fun a => ∑ j ∈ Finset.range K, H a (f j)) hN)

end Zarankiewicz

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

/-! The global sum is derived from the actual closed polygonal curves and every one of their traversals. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_closed_cycle_intersection_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → OrientedDart graph)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
        (N K : ℕ), d N=d 0 → f K=f 0 →
        (∀ i, i < N → OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i)) →
        (∀ j, j < K → OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j)) →
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        (dartSign (d i)*dartSign (f j)*
          V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))+
            C.passageIntersection d f hd hf i j ε)=0 := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cycle_block_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro ε hε hs d f hd hf N K hN hK hdi hfj
  let P := V.dartCycleChain d hd N hN
  let Q := C.shiftedCycleChain f hf K hK ε
  have hblocks (i j : ℕ) (hi : i < N) (hj : j < K) :=
    hh ε hε hs d f hd hf i j (hdi i hi) (hfj j hj)
  have hT : P.Transverse Q := by
    change (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).Transverse
      (finitePolygonalChain Set.univ (C.shiftedCycleVertex f ε) (Set.mem_univ _) (C.shiftedCycleBlock f hf ε) K)
    apply finitePolygonalChain_transverse_left
    intro i hi
    apply finitePolygonalChain_transverse_right
    intro j hj
    exact (hblocks i j hi hj).1
  have hzero := P.closed_intersection_zero Q hT
  have hsplit : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces :=
    finitePolygonalChain_intersection_double _ _ _ _ _ _ _ _
  rw [hsplit] at hzero
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hblocks i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)).2.symm
    _ = 0 := hzero

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Two actual physical shifts give the global averaged identity, with no restriction on shared edges between cycles. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge] {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem closed_cycle_averaged_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i))
    (hfj : ∀ j, j < K → OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      (dartSign (d i)*dartSign (f j)*
        V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))+
          C.passagePairing d f hd hf i j)=0 := by
  obtain ⟨δ₀,hδ₀,hglobal⟩ := C.exists_closed_cycle_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,hlocal⟩ := C.exists_passage_pairing_radius hnorm
  let t := min δ₀ δ₁/2
  have ht : 0 < t := half_pos (lt_min hδ₀ hδ₁)
  have htmin : t < min δ₀ δ₁ := half_lt_self (lt_min hδ₀ hδ₁)
  have ht₀ : t < δ₀ := htmin.trans_le (min_le_left _ _)
  have ht₁ : t < δ₁ := htmin.trans_le (min_le_right _ _)
  have hzplus := hglobal t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  have hzminus := hglobal (-t) (neg_ne_zero.mpr (ne_of_gt ht))
    (by simpa only [abs_neg,abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  let E : ℕ → ℕ → ℝ := fun i j => dartSign (d i)*dartSign (f j)*
    V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        ((E i j+C.passageIntersection d f hd hf i j t)+
          (E i j+C.passageIntersection d f hd hf i j (-t)))/2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hlocal t ht ht₁ d f hd hf i j (hdi i (Finset.mem_range.mp hi)) (hfj j (Finset.mem_range.mp hj))]
      dsimp only [E]
      ring
    _ = ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j t))+
        (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j (-t))))/2 := by
      simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.sum_mul,add_mul]
    _ = 0 := by rw [hzplus,hzminus]; norm_num

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Every local passage endpoint is counted once at the corresponding graph-edge endpoint. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem passage_sum_eq_endpoint_sum (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, C.passagePairing d f hd hf i j)=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        dartSign (d i)*dartSign (f j)*
          C.edgeEndpointPairing (OrientedDart.edge (d i)) (OrientedDart.edge (f j)) := by
  have hTS := double_sum_cycle_shift_right d f N K hK
    (fun a b => C.flagPairing (dartTargetFlag a) (dartSourceFlag b))
  have hST := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartTargetFlag b))
  have hSS₀ := double_sum_cycle_shift_right (fun i => d (i+1)) f N K hK
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  have hSS₁ := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  simp_rw [C.passagePairing_flags,← C.dart_endpoint_pairing]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hTS,hST,hSS₀,hSS₁]

theorem closed_cycle_matrix_sum [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i))
    (hfj : ∀ j, j < K → OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      dartSign (d i)*dartSign (f j)*
        C.cycleIntersectionMatrix (OrientedDart.edge (d i)) (OrientedDart.edge (f j))=0 := by
  have hh := C.closed_cycle_averaged_sum hnorm hstraight htrans d f hd hf N K hN hK hdi hfj
  simp only [Finset.sum_add_distrib] at hh
  rw [C.passage_sum_eq_endpoint_sum d f hd hf N K hN hK] at hh
  simpa only [cycleIntersectionMatrix,mul_add,Finset.sum_add_distrib] using hh

end Paper170Geometry.TruncatedSpokeCoordinates

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

theorem normalized_crossing_unique_piece (N : Paper170.NormalizedDrawing graph)
    (e : Edge) (x : Plane) (hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing)
    (hxe : x ∈ Paper170.edgeInterior N.toContinuousDrawing e) :
    ∃!i : Fin (N.polygonal e).pieces,
      x ∈ openSegmentTrace ((N.polygonal e).vertices i.val) ((N.polygonal e).vertices (i.val+1)) := by
  obtain ⟨t, ht, rfl⟩ := hxe
  have hn (i : Fin ((N.polygonal e).pieces+1)) : t ≠ (N.polygonal e).knot i := by
    intro he
    exact N.crossings_not_knots e i (he ▸ hx)
  obtain ⟨i, hi⟩ := parametrization_knot_interval (N.polygonal e) t ht hn
  have hmem : N.edge e t ∈ openSegmentTrace ((N.polygonal e).vertices i.val)
      ((N.polygonal e).vertices (i.val+1)) := by
    rw [← parametrization_open_piece]
    exact ⟨t,hi,rfl⟩
  refine ⟨i,hmem,?_⟩
  intro j hj
  rw [← parametrization_open_piece] at hj
  obtain ⟨s,hs,he⟩ := hj
  have hst : s=t := N.edge_injective e he
  subst s
  apply le_antisymm
  · by_contra h
    have hij : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact lt_of_not_ge h
    exact hi.2.not_ge (((N.polygonal e).increasing.monotone hij).trans hs.1.le)
  · by_contra h
    have hji : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact lt_of_not_ge h
    exact hs.2.not_ge (((N.polygonal e).increasing.monotone hji).trans hi.1.le)

theorem openSegmentTrace_of_mem_segment_avoiding (a b x : Plane) (S : Set Plane)
    (hx : x∈S) (ha : a∉S) (hb : b∉S) (hseg : x∈segment ℝ a b) :
    x∈openSegmentTrace a b := by
  rw [← Path.range_segment] at hseg
  obtain ⟨t,ht⟩ := hseg
  have he : segmentPoint a b t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  exact ⟨t.val,segment_parameter_strict_of_avoids_endpoints a b x S hx ha hb t.val t.property he,he⟩

theorem minimum_crossing_piece_unique [Fintype Vertex] (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing)
    (i j : Fin (V.chain e).pieces)
    (hi : x∈segment ℝ ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)))
    (hj : x∈segment ℝ ((V.chain e).vertices j.val) ((V.chain e).vertices (j.val+1))) : i=j := by
  suffices hh : ∀ i j : Fin (V.chain e).pieces, i<j →
      x∈segment ℝ ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)) →
      x∈segment ℝ ((V.chain e).vertices j.val) ((V.chain e).vertices (j.val+1)) → False by
    rcases lt_trichotomy i j with h | h | h
    · exact (hh i j h hi hj).elim
    · exact h
    · exact (hh j i h hj hi).elim
  intro i j hij hi hj
  by_cases he : j.val=i.val+1
  · have hj' : x∈segment ℝ ((V.chain e).vertices (i.val+1)) ((V.chain e).vertices (i.val+2)) := by
      simpa only [he, Nat.add_assoc] using hj
    have hxv := (V.chain e).minimum_adjacent_intersection (V.minimal e) i.val (by omega) hi hj'
    exact minimum_vertices_not_crossing N.toAdmissibleDrawing (normalized_locallyStraight N)
      e (V.chain e) (V.minimal e) (i.val+1) (by omega) (hxv ▸ hx)
  · exact Set.disjoint_left.mp ((V.chain e).minimum_nonadjacent_disjoint (V.minimal e)
      i.val j.val (by change i.val<j.val at hij; omega) j.isLt) hi hj

theorem truncated_crossing_unique_piece [Fintype Vertex] (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing)
    (hxe : x ∈ Paper170.edgeInterior N.toContinuousDrawing e) :
    ∃!i : Fin (V.pieces e), x∈openSegmentTrace (V.vertices e i.val) (V.vertices e (i.val+1)) := by
  have hxr := crossing_mem_truncated_edge N.toAdmissibleDrawing (normalized_noAdjacent N)
    V.chain V.minimal V.radius V.radius_pos V.weak_short V.piece_clearance e x hx hxe
  obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (V.vertices e) (V.pieces e)
    (V.pieces_pos e) x hxr
  have hm : x∈openSegmentTrace (V.vertices e i) (V.vertices e (i+1)) :=
    openSegmentTrace_of_mem_segment_avoiding _ _ x (Paper170.crossingPoints N.toContinuousDrawing) hx
      (V.vertices_not_crossing (normalized_noAdjacent N) (normalized_locallyStraight N) e i (by omega))
      (V.vertices_not_crossing (normalized_noAdjacent N) (normalized_locallyStraight N) e (i+1) (by omega)) hxi
  refine ⟨⟨i,hi⟩,hm,?_⟩
  intro j hj
  apply minimum_crossing_piece_unique N V e x hx
  · exact (V.chain e).truncated_piece_subset V.radius V.radius_pos (V.weak_short e).1
      (V.weak_short e).2 j.val j.isLt (openSegmentTrace_subset_segment _ _ hj)
  · exact (V.chain e).truncated_piece_subset V.radius V.radius_pos (V.weak_short e).1
      (V.weak_short e).2 i hi hxi

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
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

/-- At an actual crossing, the truncated chain and original subdivision point in the same direction. -/
theorem truncated_direction_pos_mul_original (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge)
    (i : Fin (V.pieces e)) (k : Fin (N.polygonal e).pieces) (x : Plane)
    (hx : x∈Paper170.crossingPoints N.toContinuousDrawing)
    (hxi : x∈openSegmentTrace (V.vertices e i.val) (V.vertices e (i.val+1)))
    (hxk : x∈openSegmentTrace ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1))) :
    ∃r : ℝ, 0 < r ∧ V.vertices e (i.val+1)-V.vertices e i.val =
      r • ((N.polygonal e).vertices (k.val+1)-(N.polygonal e).vertices k.val) := by
  have hfull := (V.chain e).truncated_piece_subset V.radius V.radius_pos
    (V.weak_short e).1 (V.weak_short e).2 i.val i.isLt (openSegmentTrace_subset_segment _ _ hxi)
  have hxfull := minimum_piece_crossing_open N.toAdmissibleDrawing (normalized_locallyStraight N)
    e (V.chain e) (V.minimal e) i.val i.isLt x hx hfull
  obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval (V.chain e).vertices
    (V.chain e).pieces i.val i.isLt
  have hend : N.vertex (graph.src e) ≠ N.vertex (graph.dst e) :=
    fun he => graph.loopless e (N.vertex_injective he)
  have hγseg : ∀t : unitInterval,
      N.edge e (intervalSegment ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) t) =
      Paper170.segmentPoint ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1)) t.val :=
    (Paper170.toZarankiewiczParametrization (N.polygonal e)).segment_formula k
  have hηseg : ∀t : unitInterval, (V.chain e).path (intervalSegment a b t) =
      Paper170.segmentPoint ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)) t.val := hseg
  obtain ⟨r,hr,he⟩ := Paper170.path_segments_direction_of_mem (N.edge e) (V.chain e).path
    (N.edge_injective e) ((V.chain e).minimum_path_injective hend (V.minimal e))
    (drawing_chain_range_eq N.toContinuousDrawing e (V.chain e)).symm
    ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) a b
    ((N.polygonal e).increasing Fin.castSucc_lt_succ) hab
    ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1))
    ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)) hγseg hηseg x hxk hxfull
  refine ⟨(V.chain e).truncatedScale V.radius i.val * r,
    mul_pos ((V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 i.val) hr, ?_⟩
  change trackDirection ((V.chain e).truncatedVertices V.radius) i.val = _
  rw [(V.chain e).truncated_direction V.radius i.val i.isLt]
  change (V.chain e).truncatedScale V.radius i.val •
    ((V.chain e).vertices (i.val+1)-(V.chain e).vertices i.val) = _
  rw [he,smul_smul]

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
open scoped BigOperators
namespace Paper170Geometry
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

/-- The only remaining geometric input is equality of the local oriented crossing signs. -/
theorem signedIntersection_eq_of_matching_signs (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e f : Edge) (hef : e≠f)
    (hmatch : ∀ (i : Fin (V.pieces e)) (j : Fin (V.pieces f))
      (k : Fin (N.polygonal e).pieces) (l : Fin (N.polygonal f).pieces) (x : Plane),
      x∈openSegmentTrace (V.vertices e i.val) (V.vertices e (i.val+1)) →
      x∈openSegmentTrace (V.vertices f j.val) (V.vertices f (j.val+1)) →
      x∈openSegmentTrace ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1)) →
      x∈openSegmentTrace ((N.polygonal f).vertices l.val) ((N.polygonal f).vertices (l.val+1)) →
      segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
        (V.vertices f j.val) (V.vertices f (j.val+1)) =
      segmentCrossingSign ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1))
        ((N.polygonal f).vertices l.val) ((N.polygonal f).vertices (l.val+1))) :
    V.signedIntersection e f=Paper170.interiorIntersection N e f := by
  classical
  let A := Fin (V.pieces e) × Fin (V.pieces f)
  let B := Fin (N.polygonal e).pieces × Fin (N.polygonal f).pieces
  let F : A → ℝ := fun a => segmentCrossingSign
    (V.vertices e a.1.val) (V.vertices e (a.1.val+1))
    (V.vertices f a.2.val) (V.vertices f (a.2.val+1))
  let G : B → ℝ := fun b => segmentCrossingSign
    ((N.polygonal e).vertices b.1.val) ((N.polygonal e).vertices (b.1.val+1))
    ((N.polygonal f).vertices b.2.val) ((N.polygonal f).vertices (b.2.val+1))
  let R : A → B → Prop := fun a b => ∃x : Plane,
    x∈openSegmentTrace (V.vertices e a.1.val) (V.vertices e (a.1.val+1)) ∧
    x∈openSegmentTrace (V.vertices f a.2.val) (V.vertices f (a.2.val+1)) ∧
    x∈openSegmentTrace ((N.polygonal e).vertices b.1.val) ((N.polygonal e).vertices (b.1.val+1)) ∧
    x∈openSegmentTrace ((N.polygonal f).vertices b.2.val) ((N.polygonal f).vertices (b.2.val+1))
  have hsame (a : A) (b : B) (h : R a b) : F a=G b := by
    obtain ⟨x,hx₁,hx₂,hx₃,hx₄⟩ := h
    exact hmatch a.1 a.2 b.1 b.2 x hx₁ hx₂ hx₃ hx₄
  have hF : ∀a, F a≠0 → ∃!b, G b≠0 ∧ R a b := by
    intro a ha
    have hproper := (segmentCrossingSign_ne_zero_iff _ _ _ _).mp ha
    obtain ⟨s,hs,t,ht,he⟩ := hproper.2
    let x := segmentPoint (V.vertices e a.1.val) (V.vertices e (a.1.val+1)) s
    have hx₁ : x∈openSegmentTrace (V.vertices e a.1.val) (V.vertices e (a.1.val+1)) := ⟨s,hs,rfl⟩
    have hx₂ : x∈openSegmentTrace (V.vertices f a.2.val) (V.vertices f (a.2.val+1)) := ⟨t,ht,he.symm⟩
    have hxe := V.range_subset_edgeInterior e (V.piece_subset_range e a.1.val a.1.isLt
      (openSegmentTrace_subset_segment _ _ hx₁))
    have hxf := V.range_subset_edgeInterior f (V.piece_subset_range f a.2.val a.2.isLt
      (openSegmentTrace_subset_segment _ _ hx₂))
    have hx : x∈Paper170.crossingPoints N.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
    obtain ⟨i,hi,hu⟩ := normalized_crossing_unique_piece N e x hx hxe
    obtain ⟨j,hj,hv⟩ := normalized_crossing_unique_piece N f x hx hxf
    have hR : R a (i,j) := ⟨x,hx₁,hx₂,hi,hj⟩
    refine ⟨(i,j),⟨?_,hR⟩,?_⟩
    · rwa [← hsame a (i,j) hR]
    · rintro b ⟨_,y,hy₁,hy₂,hy₃,hy₄⟩
      have hyx : y=x := openSegments_inter_subsingleton _ _ _ _ hproper.1 ⟨hy₁,hy₂⟩ ⟨hx₁,hx₂⟩
      subst y
      exact Prod.ext (hu b.1 hy₃) (hv b.2 hy₄)
  have hG : ∀b, G b≠0 → ∃!a, F a≠0 ∧ R a b := by
    intro b hb
    have hproper := (segmentCrossingSign_ne_zero_iff _ _ _ _).mp hb
    obtain ⟨s,hs,t,ht,he⟩ := hproper.2
    let x := segmentPoint ((N.polygonal e).vertices b.1.val) ((N.polygonal e).vertices (b.1.val+1)) s
    have hx₃ : x∈openSegmentTrace ((N.polygonal e).vertices b.1.val)
        ((N.polygonal e).vertices (b.1.val+1)) := ⟨s,hs,rfl⟩
    have hx₄ : x∈openSegmentTrace ((N.polygonal f).vertices b.2.val)
        ((N.polygonal f).vertices (b.2.val+1)) := ⟨t,ht,he.symm⟩
    have hxe : x∈Paper170.edgeInterior N.toContinuousDrawing e :=
      (N.polygonal e).segment_mem_interior N.toContinuousDrawing e b.1 s hs
    have hxf : x∈Paper170.edgeInterior N.toContinuousDrawing f := by
      rw [show x=segmentPoint ((N.polygonal f).vertices b.2.val)
        ((N.polygonal f).vertices (b.2.val+1)) t from he]
      exact (N.polygonal f).segment_mem_interior N.toContinuousDrawing f b.2 t ht
    have hx : x∈Paper170.crossingPoints N.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
    obtain ⟨i,hi,hu⟩ := truncated_crossing_unique_piece N V e x hx hxe
    obtain ⟨j,hj,hv⟩ := truncated_crossing_unique_piece N V f x hx hxf
    have hR : R (i,j) b := ⟨x,hi,hj,hx₃,hx₄⟩
    refine ⟨(i,j),⟨?_,hR⟩,?_⟩
    · rwa [hsame (i,j) b hR]
    · rintro a ⟨_,y,hy₁,hy₂,hy₃,hy₄⟩
      have hyx : y=x := openSegments_inter_subsingleton _ _ _ _ hproper.1 ⟨hy₃,hy₄⟩ ⟨hx₃,hx₄⟩
      subst y
      exact Prod.ext (hu a.1 hy₁) (hv a.2 hy₂)
  have hsum : ∑a, F a = ∑b, G b :=
    sum_eq_sum_of_unique_match F G R hF hG (fun a b _ _ h => hsame a b h)
  rw [VertexTruncation.signedIntersection,ite_eq_right hef,Paper170.interiorIntersection,ite_eq_right hef]
  dsimp only [A,B,F,G] at hsum
  simp only [Fintype.sum_prod_type] at hsum
  simp only [Paper170.segmentIntersection_eq_segmentCrossingSign]
  change polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) =
    polygonIntersection (N.polygonal e).vertices (N.polygonal f).vertices
      (N.polygonal e).pieces (N.polygonal f).pieces
  simpa only [polygonIntersection_eq_fin_sum] using hsum

end Paper170Geometry

end
end

section

/-! The cycle engine computes the signed intersection of the original, arbitrary
normalized subdivision, independently of the minimal-chain presentation. -/
noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry.VertexTruncation
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

theorem signedIntersection_eq_interiorIntersection (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e f : Edge) :
    V.signedIntersection e f = Paper170.interiorIntersection N e f := by
  classical
  by_cases hef : e=f
  · subst f
    rw [V.signedIntersection_self]
    simp [Paper170.interiorIntersection]
  · apply signedIntersection_eq_of_matching_signs N V e f hef
    intro i j k l x hxi hxj hxk hxl
    have hxe := V.range_subset_edgeInterior e (V.piece_subset_range e i.val i.isLt
      (openSegmentTrace_subset_segment _ _ hxi))
    have hxf := V.range_subset_edgeInterior f (V.piece_subset_range f j.val j.isLt
      (openSegmentTrace_subset_segment _ _ hxj))
    have hx : x∈Paper170.crossingPoints N.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
    obtain ⟨r,hr,he⟩ := truncated_direction_pos_mul_original N V e i k x hx hxi hxk
    obtain ⟨s,hs,hf⟩ := truncated_direction_pos_mul_original N V f j l x hx hxj hxl
    exact segmentCrossingSign_eq_of_pos_directions _ _ _ _ _ _ _ _ x r s hr hs he hf hxi hxj hxk hxl

end Paper170Geometry.VertexTruncation

end
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

/-! The directed complete-graph chains and the chosen unoriented edge representatives agree. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E A : Type} [Fintype E] [Fintype A]

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

end Paper170

end
end

section

/-! A bilinear edge pairing is determined on real cycles by oriented simple cycles. -/
noncomputable section
open scoped BigOperators
namespace Paper170
variable {V E : Type} [Fintype E]

theorem edgePairing_add_left (J : E → E → ℝ) (x y z : E → ℝ) :
    edgePairing J (x+y) z = edgePairing J x z + edgePairing J y z := by
  simp [edgePairing,add_mul,Finset.sum_add_distrib]

theorem edgePairing_add_right (J : E → E → ℝ) (x y z : E → ℝ) :
    edgePairing J x (y+z) = edgePairing J x y + edgePairing J x z := by
  simp [edgePairing,mul_add,add_mul,Finset.sum_add_distrib]

theorem edgePairing_smul_left (J : E → E → ℝ) (c : ℝ) (x y : E → ℝ) :
    edgePairing J (c•x) y = c*edgePairing J x y :=
  edgePairing_mul_left J c x y

theorem edgePairing_smul_right (J : E → E → ℝ) (c : ℝ) (x y : E → ℝ) :
    edgePairing J x (c•y) = c*edgePairing J x y :=
  edgePairing_mul_right J c x y

theorem edgePairing_eq_zero_of_simple_cycles [Fintype V] (G : Graph V E)
    (J : E → E → ℝ)
    (hcycles : ∀ C C' : SimpleCycle G, edgePairing J C.edgeChain C'.edgeChain = 0)
    (z z' : E → ℝ) (hz : ∀ v, boundary G z v = 0) (hz' : ∀ v, boundary G z' v = 0) :
    edgePairing J z z' = 0 := by
  have hy := (simple_cycles_span G z').mp hz'
  have hright (C : SimpleCycle G) : edgePairing J C.edgeChain z' = 0 := by
    clear hz'
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨C',rfl⟩ := hy
      exact hcycles C C'
    | zero => simp [edgePairing]
    | add x y _ _ hx hy => rw [edgePairing_add_right,hx,hy,add_zero]
    | smul c x _ hx => rw [edgePairing_smul_right,hx,mul_zero]
  have hx := (simple_cycles_span G z).mp hz
  clear hz
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C,rfl⟩ := hx
    exact hright C
  | zero => simp [edgePairing]
  | add x y _ _ hx hy => rw [edgePairing_add_left,hx,hy,add_zero]
  | smul c x _ hx => rw [edgePairing_smul_left,hx,mul_zero]

end Paper170

end
end

section

/-! Traversal sums of a simple cycle agree with the frozen edge-chain bilinear pairing. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
open Paper170Geometry
variable {V E : Type} {G : Graph V E}

namespace SimpleCycle

theorem cyclicDart_coe (C : SimpleCycle G) (i : Fin C.length) : C.cyclicDart i = C.dart i := by
  exact congrArg C.dart (Fin.ext (Nat.mod_eq_of_lt i.isLt))

theorem edgeChain_eq_dart_sum (C : SimpleCycle G) :
    C.edgeChain = fun e => ∑ i, dartSign (C.dart i) * (Pi.single (C.edge i) (1 : ℝ) : E → ℝ) e := by
  funext e
  unfold edgeChain
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : C.edge i = e
  · subst e
    simp [dart_sign]
  · simp [h]

end SimpleCycle

variable [Fintype E]

theorem edgePairing_single_single (J : E → E → ℝ) (e f : E) (a b : ℝ) :
    edgePairing J (Pi.single e a) (Pi.single f b) = a*b*J e f := by
  simp [edgePairing,Pi.single_apply]

theorem edgePairing_simple_cycles (J : E → E → ℝ) (C C' : SimpleCycle G) :
    edgePairing J C.edgeChain C'.edgeChain =
      ∑ i, ∑ j, dartSign (C.dart i) * dartSign (C'.dart j) * J (C.edge i) (C'.edge j) := by
  rw [C.edgeChain_eq_dart_sum,C'.edgeChain_eq_dart_sum]
  simp_rw [edgePairing_sum_left,edgePairing_sum_right,edgePairing_mul_left,
    edgePairing_mul_right,edgePairing_single_single]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem edgePairing_simple_cycles_range (J : E → E → ℝ) (C C' : SimpleCycle G) :
    edgePairing J C.edgeChain C'.edgeChain =
      ∑ i ∈ Finset.range C.length, ∑ j ∈ Finset.range C'.length,
        dartSign (C.cyclicDart i) * dartSign (C'.cyclicDart j) *
          J (C.cyclicDart i).edge (C'.cyclicDart j).edge := by
  rw [edgePairing_simple_cycles]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [SimpleCycle.cyclicDart_coe,SimpleCycle.dart_edge]

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

/-! Actual vertex-coordinate orders give the frozen signed endpoint contribution. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {Vertex Edge : Type} {graph : Graph Vertex Edge}

theorem endpointSign_eq_sub_indicators (v : Vertex) (e : Edge) :
    endpointSign graph v e =
      (if graph.src e=v then 1 else 0) - (if graph.dst e=v then 1 else 0) := by
  by_cases hs : graph.src e=v
  · have ht : graph.dst e≠v := fun h => graph.loopless e (hs.trans h.symm)
    simp [endpointSign,hs,ht]
  · by_cases ht : graph.dst e=v <;> simp [endpointSign,hs,ht]

theorem sum_endpointSign [Fintype Vertex] (e : Edge) (f : Vertex → ℝ) :
    (∑v, endpointSign graph v e * f v) = f (graph.src e)-f (graph.dst e) := by
  simp [endpointSign_eq_sub_indicators,sub_mul,ite_mul,Finset.sum_sub_distrib]

end Paper170

namespace Paper170Geometry.TruncatedSpokeCoordinates
open Zarankiewicz
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}
  {N : Paper170.NormalizedDrawing graph} {V : VertexTruncation N.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V) (O : Paper170.SpokeOrders N)

omit [Fintype Vertex] in
theorem flagPairing_eq_spokeComparison
    (hnode : ∀v (e f : IncidentEdges graph v),
      orderSign (C.node v e) (C.node v f) = Paper170.spokeComparison O v e.val f.val)
    (a b : IncidentFlag graph) : C.flagPairing a b =
      if b.1=a.1 then Paper170.spokeComparison O a.1 a.2.val b.2.val / 2 else 0 := by
  unfold flagPairing
  split_ifs with h
  · rw [hnode]
    rfl
  · rfl

theorem edgeEndpointPairing_eq_signed_sum
    (hnode : ∀v (e f : IncidentEdges graph v),
      orderSign (C.node v e) (C.node v f) = Paper170.spokeComparison O v e.val f.val)
    (e f : Edge) : C.edgeEndpointPairing e f =
      (1/2 : ℝ) * ∑v, Paper170.endpointSign graph v e * Paper170.endpointSign graph v f *
        Paper170.spokeComparison O v e f := by
  have hsum := Paper170.sum_endpointSign (graph := graph) e
    (fun v => Paper170.endpointSign graph v f * Paper170.spokeComparison O v e f)
  simp only [← mul_assoc] at hsum
  rw [hsum]
  unfold edgeEndpointPairing
  rw [C.flagPairing_eq_spokeComparison O hnode,C.flagPairing_eq_spokeComparison O hnode,
    C.flagPairing_eq_spokeComparison O hnode,C.flagPairing_eq_spokeComparison O hnode]
  simp only [dartSourceFlag,dartTargetFlag,dartSourceIncident,dartTargetIncident,
    forwardDart,OrientedDart.fst,OrientedDart.snd,Paper170.endpointSign_eq_sub_indicators]
  split_ifs <;> ring

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! The geometric closed-polygon calculation annihilates the real graph cycle space. -/
noncomputable section
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Paper170.Graph Vertex Edge} {D : Paper170.AdmissibleDrawing graph}
  {V : VertexTruncation D.toContinuousDrawing} (C : TruncatedSpokeCoordinates V)

theorem cycleMatrix_pairing_zero (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (z z' : Edge → ℝ) (hz : ∀v, Paper170.boundary graph z v = 0)
    (hz' : ∀v, Paper170.boundary graph z' v = 0) :
    Paper170.edgePairing C.cycleIntersectionMatrix z z' = 0 := by
  apply Paper170.edgePairing_eq_zero_of_simple_cycles graph C.cycleIntersectionMatrix ?_ z z' hz hz'
  intro P Q
  rw [Paper170.edgePairing_simple_cycles_range]
  exact C.closed_cycle_matrix_sum hnorm hstraight htrans P.cyclicDart Q.cyclicDart
    P.cyclicDart_seam Q.cyclicDart_seam P.length Q.length P.cyclicDart_period Q.cyclicDart_period
    (fun i _ => P.cyclicDart_next_edge_ne i) (fun j _ => Q.cyclicDart_next_edge_ne j)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Reconstruction of the frozen cycle pairing from faithful local coordinates. -/
noncomputable section
namespace Paper170
open Paper170Geometry
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Graph Vertex Edge}

theorem cycle_pairing_of_coordinates_oai (N : NormalizedDrawing graph) (O : SpokeOrders N)
    (V : VertexTruncation N.toContinuousDrawing) (C : TruncatedSpokeCoordinates V)
    (hnode : ∀v (e f : IncidentEdges graph v),
      Zarankiewicz.orderSign (C.node v e) (C.node v f) = spokeComparison O v e.val f.val)
    (z z' : Edge → ℝ) (hz : ∀v, boundary graph z v = 0) (hz' : ∀v, boundary graph z' v = 0) :
    edgePairing (cycleIntersection O) z z' = 0 := by
  have hmatrix : C.cycleIntersectionMatrix = cycleIntersection O := by
    funext e f
    unfold TruncatedSpokeCoordinates.cycleIntersectionMatrix cycleIntersection
    rw [VertexTruncation.signedIntersection_eq_interiorIntersection N V,
      C.edgeEndpointPairing_eq_signed_sum O hnode]
  rw [← hmatrix]
  exact C.cycleMatrix_pairing_zero (normalized_noAdjacent N) (normalized_locallyStraight N)
    (normalized_locallyTransverse N) z z' hz hz'

end Paper170

end
end

end OAI
end

theorem solution : type_of% @OAI.Paper170.cycle_pairing_of_coordinates_oai := @OAI.Paper170.cycle_pairing_of_coordinates_oai
