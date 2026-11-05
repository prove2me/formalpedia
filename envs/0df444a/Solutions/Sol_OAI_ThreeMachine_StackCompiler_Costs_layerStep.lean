-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.layerStep
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:42:42.315737+00:00
-- url     : https://prove2.me/submissions/ecf0e914-d9c4-43bc-9798-002786816943

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_advanceLast
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_solveMarks

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false


section
-- module DynamicProgram
namespace OAI

section

namespace ThreeMachine.Algorithm
open Structure

namespace Block
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

omit [Fintype J] [DecidableEq J] in
theorem valid_empty : (empty : Block J).Valid r ∅ := by
  let b : FullBlock r (↑(∅ : Finset J) : Set J) :=
    { length := 0
      time := fun _ => 0
      bounds := by simp
      capacity := by simp
      respects := by simp
      size := by simp }
  exact ⟨b, rfl, rfl⟩

omit [DecidableEq J] in
theorem valid_triple {Z : Finset J} (hc : Z.card = 3)
    (ha : ∀ x ∈ Z, ∀ y ∈ Z, ¬r x y) : (triple : Block J).Valid r Z :=
  ⟨FullBlock.triple ⟨Z,hc⟩ ha, rfl, rfl⟩

theorem valid_append {U V : Finset J} {s t : Block J}
    (hs : s.Valid r U) (ht : t.Valid r V) (hd : Disjoint U V)
    (hb : ∀ x ∈ V, ∀ y ∈ U, ¬r x y) : (append U s t).Valid r (U ∪ V) := by
  obtain ⟨s', hsl, hst⟩ := hs
  obtain ⟨t', htl, htt⟩ := ht
  have hd' : Disjoint (U : Set J) (V : Set J) := Finset.disjoint_coe.mpr hd
  let b := s'.append t' hd' hb
  let c : FullBlock r (↑(U ∪ V) : Set J) :=
    { length := b.length, time := b.time
      bounds := fun x hx => b.bounds x (by simpa using hx)
      capacity := fun k => by simpa using b.capacity k
      respects := fun x hx y hy hxy => b.respects x (by simpa using hx) y (by simpa using hy) hxy
      size := by simpa using b.size }
  refine ⟨c, ?_, ?_⟩
  · change s'.length + t'.length = s.length + t.length
    rw [hsl, htl]
  · funext x
    by_cases hx : x ∈ U <;> simp [c, b, FullBlock.append, append, hx, hsl, hst, htt]

omit [Fintype J] [DecidableEq J] in
theorem Valid.of_eq {U V : Finset J} {s : Block J} (h : s.Valid r U) (he : U = V) :
    s.Valid r V := he ▸ h

end Block

namespace State
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

omit [Fintype J] in
theorem Compatible.left_subset {W : Finset J} {u : State J} (h : u.Compatible r W) :
    u.left ⊆ W := by
  rw [← h.1]
  exact fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem valid_advance {W : Finset J} {u v : State J} {s t : Block J}
    (hu : u.Compatible r W) (hv : v.Compatible r W) (hs : s.Valid r u.left)
    (hsub : u.upto ⊆ v.left) (ht : t.Valid r (v.left \ u.upto)) :
    (u.advance s t).Valid r v.left := by
  have hs' := Block.valid_append hs
    (Block.valid_triple hu.2.2.2.2.1 hu.2.2.2.2.2.1) hu.2.1 hu.2.2.2.2.2.2.1
  have hd : Disjoint u.upto (v.left \ u.upto) :=
    Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have hb : ∀ x ∈ v.left \ u.upto, ∀ y ∈ u.upto, ¬r x y := by
    intro x hx y hy
    have hxr : x ∈ u.right := by
      have hxW := hv.left_subset (Finset.mem_sdiff.mp hx).1
      rw [← hu.1] at hxW
      rcases Finset.mem_union.mp hxW with hp | hr
      · exact ((Finset.mem_sdiff.mp hx).2 hp).elim
      · exact hr
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hu.2.2.2.2.2.2.2.1 x hxr y hy
    · exact hu.2.2.2.2.2.2.2.2 x hxr y hy
  have he : u.upto ∪ (v.left \ u.upto) = v.left := Finset.union_sdiff_of_subset hsub
  exact (Block.valid_append hs' ht hd hb).of_eq he

theorem valid_finish {W : Finset J} {u : State J} {s t : Block J}
    (hu : u.Compatible r W) (hs : s.Valid r u.left) (ht : t.Valid r u.right) :
    (u.finish s t).Valid r W := by
  have hs' := Block.valid_append hs
    (Block.valid_triple hu.2.2.2.2.1 hu.2.2.2.2.2.1) hu.2.1 hu.2.2.2.2.2.2.1
  have hd : Disjoint u.upto u.right := Finset.disjoint_union_left.mpr ⟨hu.2.2.1,hu.2.2.2.1⟩
  have hb : ∀ x ∈ u.right, ∀ y ∈ u.upto, ¬r x y := by
    intro x hx y hy
    exact (Finset.mem_union.mp hy).elim
      (hu.2.2.2.2.2.2.2.1 x hx y) (hu.2.2.2.2.2.2.2.2 x hx y)
  exact (Block.valid_append hs' ht hd hb).of_eq hu.1

end State
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm

theorem lookup_mem {K V : Type} [DecidableEq K] {tab : List (K × V)} {k : K} {v : V}
    (h : lookup tab k = some v) : (k,v) ∈ tab := by
  induction tab with
  | nil => simp [lookup] at h
  | cons a xs ih =>
    simp only [lookup] at h
    split_ifs at h with he
    · subst k
      have he' : a.2 = v := Option.some.inj h
      rw [← he']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem firstResult_some {K V : Type} {f : K → Option V} {ks : List K} {v : V}
    (h : firstResult f ks = some v) : ∃ k ∈ ks, f k = some v := by
  induction ks with
  | nil => simp [firstResult] at h
  | cons k ks ih =>
    cases hf : f k with
    | none =>
      obtain ⟨k',hk',he⟩ := ih (by simpa only [firstResult, hf] using h)
      exact ⟨k', List.mem_cons_of_mem _ hk',he⟩
    | some u =>
      have he : u = v := Option.some.inj (by simpa only [firstResult, hf] using h)
      exact ⟨k,List.mem_cons_self,he ▸ hf⟩

theorem mem_tableOf {K V : Type} (ks : List K) (f : K → Option V) (k : K) (v : V) :
    (k,v) ∈ tableOf ks f ↔ k ∈ ks ∧ f k = some v := by
  rw [tableOf,List.mem_filterMap]
  constructor
  · rintro ⟨a,ha,he⟩
    cases hf : f a with
    | none => simp [hf] at he
    | some b =>
      have hab : (a,b) = (k,v) := Option.some.inj (by simpa [hf] using he)
      cases hab
      exact ⟨ha,hf⟩
  · rintro ⟨hk,hv⟩
    exact ⟨k,hk, by simp [hv]⟩

namespace Walk
variable {K : Type} {r : K → K → Prop}

end Walk
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
section DynamicProgram
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

theorem states_compatible {family triples : List (Finset J)} {W : Finset J} {u : State J}
    (h : u ∈ states r family triples W) : u.Compatible r W := by
  exact of_decide_eq_true (List.mem_filter.mp h).2

omit [DecidableRel r] in
theorem markings_good {tab : List (Finset J × Block J)} {sts : List (State J)} {W : Finset J}
    (htab : TableGood r tab) (hsts : ∀ u ∈ sts, u.Compatible r W) (k : ℕ) :
    MarksGood r W (markings tab sts k) := by
  induction k with
  | zero =>
    intro u s h
    obtain ⟨hu, hs⟩ := (mem_tableOf sts _ u s).mp h
    exact ⟨hsts u hu, htab _ _ (lookup_mem hs)⟩
  | succ k ih =>
    intro v s h
    obtain ⟨hv, hs⟩ := (mem_tableOf sts _ v s).mp h
    refine ⟨hsts v hv, ?_⟩
    cases he : lookup (markings tab sts k) v with
    | some b =>
      have hb : b = s := Option.some.inj (by simpa only [he] using hs)
      exact hb ▸ (ih v b (lookup_mem he)).2
    | none =>
      obtain ⟨⟨u,b⟩, hu, hh⟩ := firstResult_some (by simpa only [he] using hs)
      simp only [tryAdvance] at hh
      split_ifs at hh with hsub
      · cases hg : lookup tab (v.left \ u.upto) with
        | none => simp [hg] at hh
        | some t =>
          have hes : u.advance b t = s := Option.some.inj (by simpa [hg] using hh)
          exact hes ▸ State.valid_advance (ih u b hu).1 (hsts v hv)
            (ih u b hu).2 hsub (htab _ _ (lookup_mem hg))

theorem solve_good {tab : List (Finset J × Block J)} (htab : TableGood r tab)
    (family triples : List (Finset J)) {W : Finset J} {s : Block J}
    (h : solve r tab family triples W = some s) : s.Valid r W := by
  simp only [solve] at h
  split_ifs at h with he
  · subst W
    have hs : Block.empty = s := Option.some.inj h
    exact hs ▸ Block.valid_empty
  · obtain ⟨⟨u,b⟩,hu,hs⟩ := firstResult_some h
    have hg := markings_good r htab (fun v hv => states_compatible r hv) (Fintype.card J) u b hu
    cases ht : lookup tab u.right with
    | none => simp [ht] at hs
    | some t =>
      have hes : u.finish b t = s := Option.some.inj (by simpa [ht] using hs)
      exact hes ▸ State.valid_finish hg.1 hg.2 (htab _ _ (lookup_mem ht))

end DynamicProgram
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
open scoped Classical
section EraseSplits
variable {J A : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}
    {atoms : A → Set J} {W : Set J}

end EraseSplits

section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]
    (atoms : A → Set J) (family triples : List (Finset J))
    (hfamily : ∀ F, Described atoms F 10000 → F.toFinset ∈ family)
    (htriples : ∀ Z : Triple J, Z.val ∈ triples)

end Completeness
end ThreeMachine.Algorithm

end

end OAI
end

section
-- module UniformRoutines
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26

section

namespace ThreeMachine.StackCompiler
variable {α : Type u1} {β : Type u2} [Coding α] [Coding β]

theorem length_le_volume (xs : List α) : xs.length ≤ volume xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [volume_cons,List.length_cons]; omega

namespace Realizer
variable {F : α × β → β}

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Realizer
variable {α : Type u3} {β : Type u4} {γ : Type u5} [Coding α] [Coding β] [Coding γ]

end ThreeMachine.StackCompiler.Realizer

namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u9} {α : I → Type u10} {β : I → Type u11} {γ : I → Type u12} {δ : I → Type u13}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)] [∀ i, Coding (δ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}

end Uniform

namespace Realizer
variable {α : Type u14} {β : Type u15} [Coding α] [Coding β] {f : α → β}

end Realizer

end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer
variable {α : Type u17} [Coding α]

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u18} {α : I → Type u19} {β : I → Type u20} {γ : I → Type u21}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u22} {α : I → Type u23} {β : I → Type u24} {γ : I → Type u25}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

end ThreeMachine.StackCompiler.Uniform

end

end OAI
end

section
-- module ScheduleRoutines
namespace OAI

universe u1 u2 u3 u4

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Uniform

variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Uniform

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Realizer

end Realizer

namespace Uniform

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Uniform

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.Algorithm
open Structure

namespace Block

theorem bounded_empty {J : Type} : (empty : Block J).Bounded := fun _ => le_rfl

theorem bounded_triple {J : Type} : (triple : Block J).Bounded := fun _ => le_rfl

theorem Bounded.append {J : Type} [DecidableEq J] {s t : Block J}
    (hs : s.Bounded) (ht : t.Bounded) (W : Finset J) : (append W s t).Bounded := by
  intro x
  change (if x ∈ W then s.time x else s.length+t.time x) ≤ s.length+t.length
  split_ifs
  · exact (hs x).trans (Nat.le_add_right _ _)
  · exact Nat.add_le_add_left (ht x) _

theorem Valid.length_le {n : ℕ} {r : Fin n → Fin n → Prop} {W : Finset (Fin n)}
    {s : Block (Fin n)} (hs : s.Valid r W) : s.length ≤ n := by
  obtain ⟨b,hbl,_⟩ := hs
  have h := b.size
  rw [Set.ncard_coe_finset,hbl] at h
  have hc := Finset.card_le_univ W
  simp only [Fintype.card_fin] at hc
  omega

end Block

namespace State
variable {J : Type} [DecidableEq J]

theorem bounded_advance (u : State J) {s t : Block J} (hs : s.Bounded) (ht : t.Bounded) :
    (u.advance s t).Bounded := (hs.append Block.bounded_triple u.left).append ht u.upto

theorem bounded_finish (u : State J) {s t : Block J} (hs : s.Bounded) (ht : t.Bounded) :
    (u.finish s t).Bounded := u.bounded_advance hs ht

end State

section Bounded
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

omit [Fintype J] in
theorem tryAdvance_bounded {tab : List (Finset J × Block J)} (htab : TableBounded tab)
    (u : State J) (v : State J) {b s : Block J} (hb : b.Bounded)
    (h : tryAdvance tab (u,b) v = some s) : s.Bounded := by
  simp only [tryAdvance] at h
  split_ifs at h
  · cases hg : lookup tab (v.left \ u.upto) with
    | none => simp [hg] at h
    | some t =>
      have he : u.advance b t = s := Option.some.inj (by simpa [hg] using h)
      exact he ▸ u.bounded_advance hb (htab _ _ (lookup_mem hg))

omit [Fintype J] [DecidableRel r] in
theorem markings_bounded {tab : List (Finset J × Block J)} {sts : List (State J)}
    (htab : TableBounded tab) (k : ℕ) : MarksBounded (markings tab sts k) := by
  induction k with
  | zero =>
    intro u s h
    obtain ⟨_,hs⟩ := (mem_tableOf sts _ u s).mp h
    exact htab _ _ (lookup_mem hs)
  | succ k ih =>
    intro v s h
    obtain ⟨_,hs⟩ := (mem_tableOf sts _ v s).mp h
    cases he : lookup (markings tab sts k) v with
    | some b =>
      have hb : b = s := Option.some.inj (by simpa only [he] using hs)
      exact hb ▸ ih v b (lookup_mem he)
    | none =>
      obtain ⟨⟨u,b⟩,hu,hh⟩ := firstResult_some (by simpa only [he] using hs)
      exact tryAdvance_bounded htab u v (ih u b hu) hh

theorem solve_bounded {tab : List (Finset J × Block J)} (htab : TableBounded tab)
    (family triples : List (Finset J)) {W : Finset J} {s : Block J}
    (h : solve r tab family triples W = some s) : s.Bounded := by
  simp only [solve] at h
  split_ifs at h
  · cases Option.some.inj h
    exact Block.bounded_empty
  · obtain ⟨⟨u,b⟩,hu,hs⟩ := firstResult_some h
    have hg := markings_bounded htab (Fintype.card J) u b hu
    cases ht : lookup tab u.right with
    | none => simp [ht] at hs
    | some t =>
      have he : u.finish b t = s := Option.some.inj (by simpa [ht] using hs)
      exact he ▸ u.bounded_finish hg (htab _ _ (lookup_mem ht))

end Bounded

end ThreeMachine.Algorithm

end

end OAI
end

section
-- module CostBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38 u39 u40

section

namespace ThreeMachine.StackCompiler

theorem volume_sublist {α : Type u5} [Coding α] {as bs : List α} (h : as.Sublist bs) :
    volume as ≤ volume bs := by
  induction h with
  | slnil => rfl
  | @cons a as bs h ih => simp only [volume_cons]; omega
  | @cons_cons a as bs h ih => simp only [volume_cons]; omega

theorem volume_filter_le {α : Type u6} [Coding α] (p : α → Bool) (xs : List α) :
    volume (xs.filter p) ≤ volume xs := volume_sublist (List.filter_sublist)

theorem volume_function_le {α : Type u9} [Coding α] {n : ℕ} (f : Fin n → α) (V : ℕ)
    (h : ∀ v, volume (f v) ≤ V) : volume f ≤ 1+n*(V+1) := by
  change volume (List.ofFn f) ≤ _
  have hv := volume_list_le (List.ofFn f) V (by
    intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; exact h i)
  simpa only [List.length_ofFn,Nat.add_comm] using hv

namespace Realizer
variable {α : Type u10} {β : Type u11} [Coding α] [Coding β] {f : α × β → β}

end Realizer

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
variable {f : ∀ i, α i × β i → β i}

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer

end Realizer

namespace Uniform
variable {I : Type u16} {α : I → Type u17} {β : I → Type u18}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_test_le (p : ∀ i, α i → Bool) (h : ∀ i x, (enc x).nonempty = p i x)
    (i : I) (x : α i) : (test p h).time i x ≤ 10000*(volume x+1) :=
  Realizer.time_test_le (p i) (h i) x

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

namespace Majorized
variable {I : Type u22} {J : Type u23} {f g h s t : I → ℕ}

end Majorized
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u25} {α : I → Type u26} {β : I → Type u27} {γ : I → Type u28}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_some_le (i : I) (x : α i) : some.time i x ≤ 100*(volume x+1) := by
  change volume x+2+2+20*(volume x+volume x+1+1) ≤ _
  omega

theorem foldTime_cons (i : I) (xs ys : List (α i)) :
    Realizer.foldTime ((cons : Uniform (fun i (x : α i × List (α i)) => x.1 :: x.2)).specialize i) ys xs ≤
      100*xs.length*(volume xs+volume ys+1)+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have hh := ih (a :: ys)
    change volume (a,ys)+2+Realizer.foldTime _ (a :: ys) xs+
      20*(volume (a :: xs)+volume ys+volume (a :: ys)+1) ≤ _
    simp only [volume_pair,volume_cons,List.length_cons] at hh ⊢
    nlinarith [volume_pos a,volume_pos xs,volume_pos ys]

theorem time_consFold (i : I) (xs ys : List (α i)) :
    cons.fold.time i (xs,ys) ≤ 200*(xs.length+1)*(volume xs+volume ys+1) := by
  have h := foldTime_cons i xs ys
  rw [time_fold]
  simp only [volume_pair]
  nlinarith

theorem foldTime_flatten (i : I) (xs : List (List (α i))) (ys : List (α i)) :
    Realizer.foldTime ((cons.fold : Uniform (fun i (x : List (α i) × List (α i)) =>
      x.1.foldl (fun b a => a :: b) x.2)).specialize i) ys xs ≤
      1000*(xs.length+xs.flatten.length)*(volume xs+volume ys+1)+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,List.flatten_nil,Nat.zero_add,Nat.mul_zero,Nat.zero_mul]; rfl
  | cons a xs ih =>
    have hh := ih (a.reverse ++ ys)
    have ht := time_consFold i a ys
    have hv := volume_append a.reverse ys
    rw [volume_reverse] at hv
    simp only [Realizer.foldTime,Realizer.fold_cons_eq]
    change cons.fold.time i (a,ys)+Realizer.foldTime _ (a.reverse ++ ys) xs+
      20*(volume (a :: xs)+volume ys+volume (a.reverse ++ ys)+1) ≤ _
    simp only [volume_cons,List.length_cons,List.flatten_cons,List.length_append] at hh ht ⊢
    nlinarith [volume_pos a,volume_pos xs,volume_pos ys]

theorem time_flatten (i : I) (xs : List (List (α i))) :
    flatten.time i xs ≤ 10000*(xs.length+xs.flatten.length+1)*(volume xs+1) := by
  have hf := foldTime_flatten i xs []
  have hr := time_reverse i xs.flatten.reverse
  simp only [volume_nil,List.length_reverse,volume_reverse] at hf hr
  have hv : volume xs.flatten ≤ volume xs := by rw [volume_flatten]; omega
  simp only [flatten,time_congr,time_comp,time_pair,time_id,time_nil,time_fold,
    Function.comp_apply,flatten_fold_eq,List.append_nil,volume_pair,volume_nil,volume_reverse]
  nlinarith [volume_pos xs,volume_pos xs.flatten]

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u29} {α : I → Type u30} {β : I → Type u31} {γ : I → Type u32}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_filterBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (a : α i) (e : γ i) (ys : List (α i)) :
    (filterBody P).time i (a,(e,ys)) ≤ P.time i (a,e)+
      10000*(volume a+volume e+volume ys+1) := by
  have ht := time_ite_le ((fst.pair (snd.comp fst)).comp P)
    ((fst.pair (snd.comp snd)).comp cons) (snd.comp snd) i (a,(e,ys))
  simp only [time_comp,time_pair,time_fst,time_snd,time_cons,volume_pair,volume_cons,Function.comp_apply] at ht
  simp only [filterBody,time_pair,time_comp,time_snd,time_fst,volume_pair,Function.comp_apply]
  have hv : volume (if p i (a,e) then a :: ys else ys) ≤ volume a+volume ys+1 := by
    have hc := volume_cons a ys
    split <;> omega
  omega

theorem foldTime_filterBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (e : γ i) (T : ℕ) (xs ys : List (α i))
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    Realizer.foldTime ((filterBody P).specialize i) (e,ys) xs ≤
      xs.length*(T+30000*(volume xs+volume e+volume ys+1))+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have ha := hT a (by simp)
    have ht := time_filterBody P i a e ys
    have hi := ih (if p i (a,e) then a :: ys else ys) (fun a ha => hT a (by simp [ha]))
    have hv : volume (if p i (a,e) then a :: ys else ys) ≤ volume a+volume ys+1 := by
      have hc := volume_cons a ys
      split <;> omega
    simp only [Realizer.foldTime]
    change (filterBody P).time i (a,(e,ys))+
      Realizer.foldTime ((filterBody P).specialize i) (e,if p i (a,e) then a :: ys else ys) xs+
      20*(volume (a :: xs)+volume (e,ys)+volume (e,if p i (a,e) then a :: ys else ys)+1) ≤ _
    simp only [volume_pair,volume_cons,List.length_cons] at hi ⊢
    nlinarith [volume_pos a,volume_pos xs,volume_pos ys,volume_pos e]

theorem time_filter {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.filter.time i (xs,e) ≤ 100000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := foldTime_filterBody P i e T xs [] hT
  have hr := time_reverse i ((xs.filter (fun a => p i (a,e))).reverse)
  have hv := volume_filter_le (fun a => p i (a,e)) xs
  have hl := List.length_filter_le (fun a => p i (a,e)) xs
  simp only [volume_nil,List.length_reverse,volume_reverse] at hf hr
  simp only [filter,time_congr,time_comp,time_pair,time_fst,time_snd,time_nil,time_fold,
    Function.comp_apply,filter_fold_eq,List.append_nil,volume_pair,volume_nil,volume_reverse]
  nlinarith [volume_pos xs,volume_pos e]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u33} {α : I → Type u34} {β : I → Type u35} {γ : I → Type u36}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_find? {p : ∀ i, α i × γ i → Bool} (P : Uniform p)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, P.time i (a,e) ≤ T) :
    P.find?.time i (xs,e) ≤ 1000000*(xs.length+1)*(T+volume xs+volume e+1) := by
  have hf := time_filter P i xs e T hT
  have hh := time_head?_le i (xs.filter (fun a => p i (a,e)))
  have hv := volume_filter_le (fun a => p i (a,e)) xs
  simp only [find?,time_congr,time_comp]
  nlinarith [volume_pos xs,volume_pos e]

theorem time_flatMap {f : ∀ i, α i × γ i → List (β i)} (R : Uniform f)
    (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T) :
    R.flatMap.time i (xs,e) ≤ 100000*(xs.length+(xs.flatMap (fun a => f i (a,e))).length+1)*
      (T+volume xs+volume e+volume (xs.map (fun a => f i (a,e)))+1) := by
  have hm := time_map R i xs e T hT
  have hf := time_flatten i (xs.map (fun a => f i (a,e)))
  simp only [List.length_map,← List.flatMap_def] at hf
  simp only [flatMap,time_congr,time_comp]
  nlinarith [volume_pos xs,volume_pos e,volume_pos (xs.map (fun a => f i (a,e)))]

omit [∀ i, Coding (α i)] in
theorem volume_map_options {i : I} (xs : List (α i)) (f : α i → Option (β i)) :
    volume (xs.map (fun a => (f a).toList)) = volume (xs.filterMap f)+2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ho : f a <;> simp only [List.map_cons,List.filterMap_cons,ho,Option.toList_none,
      Option.toList_some,volume_cons,volume_nil,List.length_cons,ih] <;> omega

theorem time_filterMap {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (i : I) (xs : List (α i)) (e : γ i) (T V : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T)
    (hV : ∀ a ∈ xs, volume (f i (a,e)) ≤ V) :
    R.filterMap.time i (xs,e) ≤ 10000000*(xs.length+1)*
      (T+volume xs+volume e+volume (xs.filterMap (fun a => f i (a,e)))+V+1) := by
  have hm := time_flatMap (R.comp optionToList) i xs e (T+11*V+12) (by
    intro a ha
    have ht := hT a ha
    have hv := hV a ha
    simp only [time_comp,optionToList,time_reinterpret]
    omega)
  have he : xs.flatMap (fun a => (f i (a,e)).toList) = xs.filterMap (fun a => f i (a,e)) := by
    clear hm hT hV
    induction xs with
    | nil => rfl
    | cons a xs ih => cases ho : f i (a,e) <;> simp [ho,ih]
  simp only [Function.comp_apply] at hm
  rw [he,volume_map_options] at hm
  have hl := List.length_filterMap_le (f := fun a => f i (a,e)) (l := xs)
  have hv := length_le_volume xs
  simp only [filterMap,time_congr]
  nlinarith [volume_pos xs,volume_pos e]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u37} {α : I → Type u38} {β : I → Type u39} {γ : I → Type u40}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_firstResult {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (i : I) (xs : List (α i)) (e : γ i) (T V : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T)
    (hV : ∀ a ∈ xs, volume (f i (a,e)) ≤ V) :
    R.firstResult.time i (xs,e) ≤ 100000000*(xs.length+1)*
      (T+volume xs+volume e+(xs.length+1)*(V+1)+1) := by
  have hv : volume (xs.filterMap (fun a => f i (a,e))) ≤ (xs.length+1)*(V+1) := by
    have h := volume_list_le (xs.filterMap (fun a => f i (a,e))) V (by
      intro b hb
      obtain ⟨a,ha,hb⟩ := List.mem_filterMap.mp hb
      have hx := hV a ha
      rw [hb,volume_some] at hx
      omega)
    have hl := List.length_filterMap_le (f := fun a => f i (a,e)) (l := xs)
    nlinarith
  have hf := time_filterMap R i xs e T V hT hV
  have hh := time_head?_le i (xs.filterMap (fun a => f i (a,e)))
  simp only [firstResult,time_comp]
  nlinarith [volume_pos xs,volume_pos e]

end Uniform
end ThreeMachine.StackCompiler
end

end OAI
end

section
-- module VolumeBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16

section
namespace ThreeMachine.StackCompiler
namespace Realizer
variable {α : Type u1} [Coding α]

end Realizer
namespace Uniform
variable {I : Type u2} {α : I → Type u3} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

theorem volume_finRange_le (n : ℕ) : volume (List.finRange n) ≤ 3*(n+1)^2 := by
  have h := volume_list_le (List.finRange n) (2*n+1) (fun a _ => by rw [volume_fin]; have := a.isLt; omega)
  rw [List.length_finRange] at h
  nlinarith

theorem volume_universe_le {n : ℕ} (x : Universe n) : volume x ≤ 3*(n+1)^2 :=
  volume_finRange_le n

theorem volume_bool_vector_le {n : ℕ} (v : Fin n → Bool) : volume v ≤ 4*n+1 := by
  have h := volume_function_le v 3 (fun _ => volume_bool _)
  omega

theorem volume_matrix_le {n : ℕ} (M : Matrix n) : volume M ≤ 10*(n+1)^2 := by
  have h := volume_function_le M (4*n+1) (fun _ => volume_bool_vector_le _)
  nlinarith

theorem volume_block_le {n : ℕ} (b : Algorithm.Block (Fin n)) (hl : b.length ≤ n)
    (ht : ∀ v, b.time v ≤ n) : volume b ≤ 10*(n+1)^2 := by
  have h := volume_function_le b.time (2*n+1) (by intro v; rw [volume_nat]; have := ht v; omega)
  change volume (b.length,b.time) ≤ _
  simp only [volume_pair,volume_nat]
  nlinarith

namespace Poly
variable {I : Type u6} {s n f : I → ℕ} {d : ℕ}

theorem volumeUnit (s : I → ℕ) (b : I → Unit) : Poly s (fun i => volume (b i)) 0 := by
  have h : (fun i => volume (b i)) = fun _ => 1 := by funext i; cases b i; rfl
  rw [h]; exact const s 1

theorem volumeUniverse (hn : Poly s n d) (v : ∀ i, Universe (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_universe_le (v i))
  (have polyH0 := Poly.const (s) (3); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem volumeMatrix (hn : Poly s n d) (v : ∀ i, Matrix (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_matrix_le (v i))
  (have polyH0 := Poly.const (s) (10); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

variable {α : I → Type u8} {β : I → Type u9} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end Poly
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end Uniform
end ThreeMachine.StackCompiler
end

section

namespace ThreeMachine.StackCompiler

end ThreeMachine.StackCompiler
end

end OAI
end

section
-- module PolynomialLoops
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

section
namespace ThreeMachine.StackCompiler
namespace Poly
variable {I : Type u1} {J : Type u2} {s : J → ℕ}
variable {α : I → Type u3} {β : I → Type u4} {γ : I → Type u5} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem volumeMap {f : ∀ i, α i × γ i → β i} {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => volume ((xs j).map (fun a => f (idx j) (a,e j)))) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList (V := fun j => C*(s j+2)^v)
  · simpa only [List.length_map] using hl
  · exact powerBase s C v
  · intro j b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact hC ⟨j,⟨a,ha⟩⟩

theorem mapTime {f : ∀ i, α i × γ i → β i} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.map.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  have ho := volumeMap idx xs e hl hv
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_map R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  (have polyH0 := Poly.const (s) (30000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hx); have polyH5 := Poly.add polyH4 (he); have polyH6 := Poly.add polyH5 (ho); have polyH7 := Poly.add polyH6 polyH1; have polyH8 := Poly.mul polyH3 polyH7; exact Poly.lift polyH8 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler
namespace Poly
variable {J : Type u7} {s : J → ℕ} {d : ℕ}

theorem volumeFinRange {n : J → ℕ} (hn : Poly s n d) :
    Poly s (fun j => volume (List.finRange (n j))) (2*d) := by
  apply of_le (fun j => volume_finRange_le (n j))
  (have polyH0 := Poly.const (s) (3); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

variable {α : J → Type u8} {β : J → Type u9} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end Poly
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u10} {s n : J → ℕ} {d : ℕ}
theorem lengthFinRange (hn : Poly s n d) :
    Poly s (fun j => (List.finRange (n j)).length) d := by simpa only [List.length_finRange] using hn

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u12} {J : Type u13} {α : I → Type u14} {β : I → Type u15} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u16} {s n : J → ℕ} {d v : ℕ}

theorem volumeFunction {α : J → Type u17} [∀ j, Coding (α j)]
    (f : ∀ j, Fin (n j) → α j) (hn : Poly s n d)
    (hf : Poly (fun q : FinPool n => s q.1) (fun q => volume (f q.1 q.2)) v) :
    Poly s (fun j => volume (f j)) (d+v) := by
  obtain ⟨C,hC⟩ := hf
  apply of_le (g := fun j => 1+n j*(C*(s j+2)^v+1))
    (fun j => volume_function_le (f j) (C*(s j+2)^v) (fun a => hC ⟨j,a⟩))
  have : Poly s (fun j => C*(s j+2)^v) v := powerBase s C v
  simpa only [Nat.max_zero,Nat.zero_max] using (const s 1).add (hn.mul (this.add (const s 1)))

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u18} {J : Type u19} {s : J → ℕ}
variable {α : I → Type u20} {β : I → Type u21} {γ : I → Type u22} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem volumeFilterMap {f : ∀ i, α i × γ i → Option (β i)} {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => volume ((xs j).filterMap (fun a => f (idx j) (a,e j)))) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList (V := fun j => C*(s j+2)^v)
  · exact of_le (fun j => List.length_filterMap_le _ _) hl
  · exact powerBase s C v
  · intro j b hb
    obtain ⟨a,ha,hb⟩ := List.mem_filterMap.mp hb
    have h := hC ⟨j,⟨a,ha⟩⟩
    dsimp only at h
    rw [hb,volume_some] at h
    omega

theorem filterMapTime {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.filterMap.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  have ho := volumeFilterMap idx xs e hl hv
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_filterMap R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (D*(s j+2)^v) (fun a ha => hC ⟨j,⟨a,ha⟩⟩) (fun a ha => hD ⟨j,⟨a,ha⟩⟩))
  (have polyH0 := Poly.const (s) (10000000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hx); have polyH5 := Poly.add polyH4 (he); have polyH6 := Poly.add polyH5 (ho); have polyH7 := Poly.add polyH6 (hV); have polyH8 := Poly.add polyH7 polyH1; have polyH9 := Poly.mul polyH3 polyH8; exact Poly.lift polyH9 (by first | decide +kernel | omega))

theorem firstResultTime {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.firstResult.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_firstResult R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (D*(s j+2)^v) (fun a ha => hC ⟨j,⟨a,ha⟩⟩) (fun a ha => hD ⟨j,⟨a,ha⟩⟩))
  (have polyH0 := Poly.const (s) (100000000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hx); have polyH5 := Poly.add polyH4 (he); have polyH6 := Poly.add (hV) polyH1; have polyH7 := Poly.mul polyH2 polyH6; have polyH8 := Poly.add polyH5 polyH7; have polyH9 := Poly.add polyH8 polyH1; have polyH10 := Poly.mul polyH3 polyH9; exact Poly.lift polyH10 (by first | decide +kernel | omega))

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u23} {s : J → ℕ} {d e : ℕ} {α : J → Type u24} {β : J → Type u25}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u26} {s : J → ℕ} {α : J → Type u27} [∀ j, Coding (α j)]

end ThreeMachine.StackCompiler.Poly
end

end OAI
end

section
-- module PolynomialLists
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16

section
namespace ThreeMachine.StackCompiler

namespace Poly
variable {J : Type u1} {s n : J → ℕ} {d e : ℕ}

theorem volumeBlock (b : ∀ j, Algorithm.Block (Fin (n j)))
    (hl : Poly s (fun j => (b j).length) d)
    (ht : Poly s (fun j => volume (b j).time) e) : Poly s (fun j => volume (b j)) (Max.max d e) := by
  simp only [volume_block,volume_nat]
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hl); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.add polyH3 (ht); have polyH5 := Poly.add polyH4 polyH2; exact Poly.lift polyH5 (by first | decide +kernel | omega))

variable {α : J → Type u2} {β : J → Type u3} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem volumeOptionSome (a : ∀ j, α j) (h : Poly s (fun j => volume (a j)) d) :
    Poly s (fun j => volume (some (a j))) d := by simp only [volume_some]; (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (h) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u4} {J : Type u5} {s : J → ℕ}
variable {α : I → Type u6} {β : I → Type u7} {γ : I → Type u8} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

variable (o : ∀ j, Option (α (idx j)))

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u9} {s : J → ℕ} {d e : ℕ} {α : J → Type u10} {β : J → Type u11}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u12} {s : J → ℕ} {d : ℕ} {K V : J → Type}
variable [∀ j, Coding (K j)] [∀ j, Coding (V j)] [∀ j, DecidableEq (K j)]

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u13} {s : J → ℕ} {d : ℕ} {α : J → Type u14} [∀ j, Coding (α j)]

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u15} {s : J → ℕ} {d e : ℕ} {α : J → Type u16}

end ThreeMachine.StackCompiler.Poly
end

end OAI
end

section
-- module StateCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_vectorMap {α : ℕ → Type u5} {β : ℕ → Type u6} [∀ n, Coding (α n)] [∀ n, Coding (β n)]
    {f : ∀ n, Fin n × α n → β n} (R : Uniform f) (n : ℕ) (x : Universe n × α n) :
    R.vectorMap.time n x = (universeList.onFst.comp R.map).time n x := rfl

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u7} {α : I → Type u8} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
namespace Costs

end Costs
namespace Uniform

end Uniform
namespace Costs

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

theorem blockEmpty : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.blockEmpty.time x.1 x.2) 3 := by (have polyH0 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (2); have polyH1 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_zero (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH0; have polyH2 := Poly.size (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1); have polyH3 := Poly.volumeUniverse polyH2 (fun (x_1 : (n : ℕ) × Universe n) => x_1.2); have polyH4 := Poly.add polyH3 polyH0; have polyH5 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_id (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_unit (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH0; have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (20); have polyH9 := Poly.add polyH3 polyH3; have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (volume ()); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (1); have polyH13 := Poly.add polyH11 polyH12; have polyH14 := Poly.mul polyH8 polyH13; have polyH15 := Poly.add polyH7 polyH14; have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (Universe) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH15; have polyH17 := Poly.volumeUnit (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => PUnit.unit); have polyH18 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (Sigma.snd x_1, ())) polyH3 polyH17; have polyH19 := Poly.add polyH18 polyH0; have polyH20 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Unit) _ _ (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH19; have polyH21 := Poly.add polyH20 polyH4; have polyH22 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (10); have polyH23 := Poly.add polyH3 polyH12; have polyH24 := Poly.mul polyH22 polyH23; have polyH25 := Poly.add polyH21 polyH24; have polyH26 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (fun (i_1 : ℕ) => Unit) i) (Universe) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Unit) _ _) (Uniform.universeList) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH25; have polyH27 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Unit) _ _ (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH19; have polyH28 := Poly.add polyH26 polyH27; have polyH29 := Poly.volumeFinRange polyH2; have polyH30 := Poly.add polyH18 polyH29; have polyH31 := Poly.add polyH30 polyH17; have polyH32 := Poly.add polyH31 polyH12; have polyH33 := Poly.mul polyH8 polyH32; have polyH34 := Poly.add polyH28 polyH33; have polyH35 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (fun (i_1 : ℕ) => Unit) i) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i × (fun (i_1 : ℕ) => Unit) i) => (fun (n : ℕ) (x_3 : Universe n) => List.finRange n) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (fun (i_1 : ℕ) => Unit) i) Universe (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Unit) _ _) Uniform.universeList) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Unit) _ _) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH34; have polyH36 := Poly.lengthFinRange polyH2; have polyH37 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (2); have polyH38 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) => (le_of_eq (@Uniform.time_zero (ℕ) (fun (i : ℕ) => Fin i × Unit) _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Sigma.snd (Sigma.fst q), ()))))))) polyH37; have polyH39 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (0); have polyH40 := Poly.volumeNat polyH39; have polyH41 := @Poly.mapTime (ℕ) ((n : ℕ) × Universe n) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Fin) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Unit) _ _ _ (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) (fun (x_1 : (n : ℕ) × Universe n) => Prod.snd (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _) (1) (0) (2 * 1) (0) (0) polyH36 polyH38 polyH29 polyH17 polyH40; have polyH42 := Poly.add polyH35 polyH41; have polyH43 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) polyH29 polyH17; have polyH44 := Poly.add polyH43 polyH12; have polyH45 := Poly.mul polyH22 polyH44; have polyH46 := Poly.add polyH42 polyH45; have polyH47 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Unit) (fun (i : ℕ) => List (Fin i) × Unit) (fun (i : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Unit) => (List.finRange i, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Unit) => List.map (fun (a : Fin i) => 0) (Prod.fst x_1)) (@Uniform.onFst ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => Unit) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) Uniform.universeList) (@Uniform.map ℕ Fin (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _)) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH46; have polyH48 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH47; have polyH49 := Poly.add polyH16 polyH48; have polyH50 := Poly.add polyH18 polyH12; have polyH51 := Poly.mul polyH22 polyH50; have polyH52 := Poly.add polyH49 polyH51; have polyH53 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => Universe i × Unit) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (x_1, ())) (fun (n : ℕ) (x_1 : Universe n × Unit) (v : Fin n) => 0) (@Uniform.pair ℕ Universe Universe (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _)) (@Uniform.vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH52; have polyH54 := Poly.add polyH1 polyH53; have polyH55 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (volume (0)); have polyH56 := Poly.add polyH3 polyH55; have polyH57 := Poly.const (fun (q : Poly.FinPool fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (0); have polyH58 := Poly.volumeNat polyH57; have polyH59 := Poly.volumeFunction (fun (x_1 : (n : ℕ) × Universe n) (v : Fin (Sigma.fst x_1)) => 0) polyH2 polyH58; have polyH60 := Poly.add polyH56 polyH59; have polyH61 := Poly.add polyH60 polyH12; have polyH62 := Poly.mul polyH8 polyH61; have polyH63 := Poly.add polyH54 polyH62; have polyH64 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (fun (i : ℕ) => ℕ) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => 0) (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : Universe i × Unit) (v : Fin i) => 0) ((fun (x_3 : Universe i) => (x_3, ())) x_1)) (@Uniform.zero ℕ Universe _) (@Uniform.comp ℕ Universe (fun (i : ℕ) => Universe i × Unit) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (x_1, ())) (fun (n : ℕ) (x_1 : Universe n × Unit) (v : Fin n) => 0) (@Uniform.pair ℕ Universe Universe (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _)) (@Uniform.vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _))) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH63; have polyH65 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (0); have polyH66 := Poly.volumeNat polyH65; have polyH67 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (0, (fun (x_2 : Universe (Sigma.fst x_1) × Unit) (v : Fin (Sigma.fst x_1)) => 0) ((fun (x_2 : Universe (Sigma.fst x_1)) => (x_2, ())) (Sigma.snd x_1)))) polyH66 polyH59; have polyH68 := Poly.add polyH67 polyH0; have polyH69 := Poly.add polyH64 polyH68; have polyH70 := Poly.add polyH67 polyH12; have polyH71 := Poly.mul polyH22 polyH70; have polyH72 := Poly.add polyH69 polyH71; have polyH73 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (0, (fun (x_3 : Universe i × Unit) (v : Fin i) => 0) ((fun (x_3 : Universe i) => (x_3, ())) x_1))) (fun (n : ℕ) (x_1 : ℕ × (Fin n → ℕ)) => OAI.ThreeMachine.Algorithm.Block.mk (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ Universe (fun (i : ℕ) => ℕ) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => 0) (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : Universe i × Unit) (v : Fin i) => 0) ((fun (x_3 : Universe i) => (x_3, ())) x_1)) (@Uniform.zero ℕ Universe _) (@Uniform.comp ℕ Universe (fun (i : ℕ) => Universe i × Unit) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (x_1, ())) (fun (n : ℕ) (x_1 : Universe n × Unit) (v : Fin n) => 0) (@Uniform.pair ℕ Universe Universe (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _)) (@Uniform.vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _)))) (Uniform.blockMake) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH72; exact Poly.lift polyH73 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module StateBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.Algorithm

theorem tableOf_length {K V : Type} (ks : List K) (f : K → Option V) :
    (tableOf ks f).length ≤ ks.length := List.length_filterMap_le _ _

theorem states_length {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (fs zs : List (Finset J)) (W : Finset J) :
    (states r fs zs W).length ≤ fs.length*zs.length := by
  calc
    _ ≤ (fs.flatMap (fun F => zs.map (State.candidate W F))).length := List.length_filter_le _ _
    _ = _ := by simp [List.length_flatMap]

theorem markings_length {J : Type} [DecidableEq J]
    (tab : List (Finset J × Block J)) (sts : List (State J)) (k : ℕ) :
    (markings tab sts k).length ≤ sts.length := by
  cases k <;> exact tableOf_length _ _

end ThreeMachine.Algorithm

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

theorem blockSmall_of_good {n : ℕ} {r : Fin n → Fin n → Prop} {W : Finset (Fin n)}
    {b : Algorithm.Block (Fin n)} (hg : b.Valid r W) (hb : b.Bounded) : BlockSmall b :=
  ⟨hg.length_le,fun v => (hb v).trans hg.length_le⟩

theorem markings_small {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]
    {tab : Table n} {sts : List (Algorithm.State (Fin n))} {W : Finset (Fin n)}
    (ht : Algorithm.TableGood r tab) (hb : Algorithm.TableBounded tab)
    (hs : ∀ u ∈ sts, u.Compatible r W) (k : ℕ) : MarksSmall (Algorithm.markings tab sts k) :=
  fun u b h => blockSmall_of_good ((Algorithm.markings_good r ht hs k u b h).2)
    (Algorithm.markings_bounded hb k u b h)

theorem volume_table_le {n : ℕ} (tab : Table n) (ht : TableSmall tab) :
    volume tab ≤ 1+tab.length*(30*(n+1)^2+1) := by
  have h := volume_list_le tab (30*(n+1)^2) (by
    rintro ⟨W,b⟩ h
    have hW := volume_finset_le W
    have hb := volume_block_le b (ht W b h).1 (ht W b h).2
    rw [volume_pair]
    have hp : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega)
  omega

theorem volume_marks_le {n : ℕ} (ms : Marks n) (ht : MarksSmall ms) :
    volume ms ≤ 1+ms.length*(30*(n+1)^2+1) := by
  have h := volume_list_le ms (30*(n+1)^2) (by
    rintro ⟨u,b⟩ h
    have hW := volume_state_le u
    have hb := volume_block_le b (ht u b h).1 (ht u b h).2
    rw [volume_pair]
    have hp : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega)
  omega

namespace Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

theorem volumeTable (tab : ∀ j, Table (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (tab j).length) l) (ht : ∀ j, TableSmall (tab j)) :
    Poly s (fun j => volume (tab j)) (l+2*d) := by
  apply of_le (fun j => volume_table_le (tab j) (ht j))
  (have polyH0 := Poly.const (s) (1); have polyH1 := Poly.const (s) (30); have polyH2 := Poly.add (hn) polyH0; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH1 polyH3; have polyH5 := Poly.add polyH4 polyH0; have polyH6 := Poly.mul (hl) polyH5; have polyH7 := Poly.add polyH0 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))

theorem volumeMarks (ms : ∀ j, Marks (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (ms j).length) l) (ht : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume (ms j)) (l+2*d) := by
  apply of_le (fun j => volume_marks_le (ms j) (ht j))
  (have polyH0 := Poly.const (s) (1); have polyH1 := Poly.const (s) (30); have polyH2 := Poly.add (hn) polyH0; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH1 polyH3; have polyH5 := Poly.add polyH4 polyH0; have polyH6 := Poly.mul (hl) polyH5; have polyH7 := Poly.add polyH0 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

theorem volume_block_bound {n : ℕ} (b : Block (Fin n)) (B : ℕ)
    (hl : b.length ≤ B) (ht : ∀ v, b.time v ≤ B) :
    volume b ≤ 4*(n+1)*(B+1) := by
  have h := volume_function_le b.time (2*B+1) (by intro v; rw [volume_nat]; have := ht v; omega)
  rw [volume_block,volume_nat]
  nlinarith

theorem volume_advance_le {n : ℕ} (v : Algorithm.State (Fin n)) (b c : Block (Fin n))
    (hb : BlockSmall b) (hc : BlockSmall c) :
    volume (v.advance b c) ≤ 100*(n+2)^2 := by
  have hl : (v.advance b c).length ≤ 2*n+1 := by
    change b.length+1+c.length ≤ _
    have := hb.1; have := hc.1; omega
  have ht (a : Fin n) : (v.advance b c).time a ≤ 2*n+1 := by
    simp only [Algorithm.State.advance,Block.append,Block.triple]
    have := hb.1; have := hb.2 a; have := hc.2 a
    split_ifs <;> omega
  have h := volume_block_bound (v.advance b c) (2*n+1) hl ht
  nlinarith

namespace Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

theorem volumeSmallBlock (b : ∀ j, Block (Fin (n j))) (hn : Poly s n d)
    (hb : ∀ j, BlockSmall (b j)) : Poly s (fun j => volume (b j)) (2*d) := by
  apply of_le (fun j => volume_block_le (b j) (hb j).1 (hb j).2)
  (have polyH0 := Poly.const (s) (10); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem volumeSmallLookup {K : J → Type} [∀ j, Coding (K j)] [∀ j, DecidableEq (K j)]
    (xs : ∀ j, List (K j × Block (Fin (n j)))) (k : ∀ j, K j)
    (hn : Poly s n d) (hb : ∀ j a b, (a,b) ∈ xs j → BlockSmall b) :
    Poly s (fun j => volume (Algorithm.lookup (xs j) (k j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by (have polyH0 := Poly.const (s) (10); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j b h
  exact volume_block_le b (hb j (k j) b (Algorithm.lookup_mem h)).1
    (hb j (k j) b (Algorithm.lookup_mem h)).2

theorem volumeAdvance (v : ∀ j, Algorithm.State (Fin (n j))) (b c : ∀ j, Block (Fin (n j)))
    (hn : Poly s n d) (hb : ∀ j, BlockSmall (b j)) (hc : ∀ j, BlockSmall (c j)) :
    Poly s (fun j => volume ((v j).advance (b j) (c j))) (2*d) := by
  apply of_le (fun j => volume_advance_le (v j) (b j) (c j) (hb j) (hc j))
  (have polyH0 := Poly.const (s) (100); have polyH1 := Poly.const (s) (2); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace Uniform
variable {I : Type u1} {α : I → Type u2} [∀ i, Coding (α i)]

end Uniform
namespace Realizer
variable {α : Type u3} [Coding α]

end Realizer
namespace Uniform
variable {I : Type u4} {α : I → Type u5} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u6} {J : Type u7} {s : J → ℕ} {α : I → Type u8} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s : J → ℕ} {d e : ℕ} {α β : J → Type}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
open Algorithm
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

theorem volumeSetList (xs : ∀ j, List (Finset (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (xs j).length) l) :
    Poly s (fun j => volume (xs j)) (l+2*d) := by
  apply volumeList hl (show Poly s (fun j => 3*(n j+1)^2) (2*d) from by (have polyH0 := Poly.const (s) (3); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j a _ha
  exact volume_finset_le a

end ThreeMachine.StackCompiler.Poly
end

end OAI
end

section
-- module TransitionCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.BlockAppendCellInput (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (W : ∀ j, Finset (Fin (n j)))
variable (b c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (v : ∀ j, Algorithm.State (Fin (n j))) (b c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler

theorem volume_option_mem_le {α : Type u3} [Coding α] {o : Option α} {a : α} (ha : a ∈ o) :
    volume a ≤ volume o := by cases o <;> simp_all [volume_some]

theorem volume_find_le {α : Type u4} [Coding α] (xs : List α) (p : α → Bool) :
    volume (xs.find? p) ≤ volume xs+2 := volume_option_le _ _ (fun _a ha =>
      volume_mem_le (List.mem_of_find?_eq_some ha))

namespace Uniform
variable {I : Type u5} {α : I → Type u6} {β : I → Type u7} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_mapSndOption_le (i : I) (o : Option (α i × β i)) :
    (snd : Uniform (fun i (x : α i × β i) => x.2)).mapOption.time i o ≤
      1000000000*(volume o+1) := by
  let R : Uniform (fun i (x : (α i × β i) × Unit) => x.1.2) := fst.comp snd
  have hm := time_optionMap R i o ()
    (100*(volume o+1)) (volume o) (by
      intro a ha
      have hv := volume_option_mem_le ha
      simp only [R,time_comp,time_fst,time_snd,volume_prod,volume_unit]
      rw [volume_pair] at hv
      omega) (by
      intro a ha
      have hv := volume_option_mem_le ha
      rw [volume_prod] at hv
      dsimp only
      omega)
  simp only [mapOption,time_congr,time_comp,time_pair,time_id,time_unit,Function.comp_apply,volume_pair,volume_unit]
  dsimp only [R] at hm
  simp only [volume_unit] at hm
  nlinarith [volume_pos o]

theorem time_lookup_le [∀ i, DecidableEq (α i)]
    (E : Uniform (fun i (x : α i × α i) => decide (x.1 = x.2)))
    (i : I) (xs : List (α i × β i)) (k : α i) (T : ℕ)
    (hT : ∀ a ∈ xs, E.time i (a.1,k) ≤ T) :
    (lookup E).time i (xs,k) ≤ 100000000000*(xs.length+1)*(T+volume xs+volume k+1) := by
  let P := (((fst.comp fst).pair snd).comp E : Uniform (fun i (x : (α i × β i) × α i) => decide (x.1.1=x.2)))
  have hp : ∀ a ∈ xs, P.time i (a,k) ≤ T+100*(volume xs+volume k+1) := by
    intro a ha
    have h := hT a ha
    have hv := volume_mem_le ha
    simp only [P,time_comp,time_pair,time_fst,time_snd,Function.comp_apply,volume_prod]
    rw [volume_pair] at hv
    omega
  have hf := time_find? P i xs k (T+100*(volume xs+volume k+1)) hp
  have hm := time_mapSndOption_le i (xs.find? (fun a => decide (a.1=k)))
  have hv := volume_find_le xs (fun a => decide (a.1=k))
  simp only [lookup,time_congr,time_comp,Function.comp_apply]
  change P.find?.time i (xs,k)+_+10*(volume (xs.find? (fun a => decide (a.1=k)))+1) ≤ _
  nlinarith [volume_pos xs,volume_pos k]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform
set_option maxHeartbeats 1000000 in
theorem time_lookup_setEq_le {n : ℕ}
    (xs : List (Finset (Fin n) × Algorithm.Block (Fin n))) (k : Finset (Fin n)) :
    (lookupA (β := fun n => Algorithm.Block (Fin n)) setEq).time n (xs,k) ≤ 100000000000*(xs.length+1)*
      (Classical.choose Costs.setEq*(n+2)^4+volume xs+volume k+1) := by
  apply time_lookup_le setEq
  intro a _ha
  exact Classical.choose_spec Costs.setEq ⟨n,(a.1,k)⟩

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module SolverCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (v : ∀ j, Algorithm.State (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))

theorem finishing
    (hl : Poly n (fun j => (tab j).length) 30000)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly n (fun j => Uniform.finishing.time (n j) (u j,(U j,tab j))) 60002 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hbV := Poly.volumeSmallBlock (fun j => (u j).2) (Poly.size n) hb
  have hL : Poly n (fun j => volume (Algorithm.lookup (tab j) (u j).1.right)) 2 :=
    Poly.volumeSmallLookup tab _ (Poly.size n) ht
  have ha := advanceLast (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      (u j).1.right).toList) => n p.1) (fun p => U p.1)
    (fun p => u p.1) (fun p => p.2.1) (fun p => hb p.1) (fun p =>
      ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2)))
  have hAv : Poly (fun p : Poly.ListPool (fun j => (Algorithm.lookup (tab j)
      (u j).1.right).toList) => n p.1)
      (fun p => volume ((u p.1).1.advance (u p.1).2 p.2.1)) 2 := by
    apply Poly.volumeAdvance _ _ _ (Poly.size _) (fun p => hb p.1)
    intro p
    exact ht p.1 _ _ (Algorithm.lookup_mem (by simpa using p.2.2))
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeState polyH0 (fun (j_1 : J) => (u j_1).1); have polyH2 := Poly.volumeProd (fun (j_1 : J) => u j_1) polyH1 (hbV); have polyH3 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, tab j_1)) polyH3 (htv); have polyH5 := Poly.volumeProd (fun (j_1 : J) => (u j_1, U j_1, tab j_1)) polyH2 polyH4; have polyH6 := Poly.const (n) (2); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_15) ((u j_15, U j_15, tab j_15))))) polyH7; have polyH9 := Poly.add polyH4 polyH6; have polyH10 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_15) (Prod.snd (u j_15, U j_15, tab j_15))))) polyH9; have polyH11 := Poly.add polyH8 polyH10; have polyH12 := Poly.const (n) (10); have polyH13 := Poly.const (n) (1); have polyH14 := Poly.add polyH4 polyH13; have polyH15 := Poly.mul polyH12 polyH14; have polyH16 := Poly.add polyH11 polyH15; have polyH17 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH16; have polyH18 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_15) ((u j_15, U j_15, tab j_15))))) polyH7; have polyH19 := Poly.add polyH2 polyH6; have polyH20 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ (n j_15) (Prod.fst (u j_15, U j_15, tab j_15))))) polyH19; have polyH21 := Poly.add polyH18 polyH20; have polyH22 := Poly.add polyH2 polyH13; have polyH23 := Poly.mul polyH12 polyH22; have polyH24 := Poly.add polyH21 polyH23; have polyH25 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH24; have polyH26 := Poly.volumeState polyH0 (fun (j_1 : J) => (Prod.fst (u j_1, U j_1, tab j_1)).1); have polyH27 := Poly.add polyH26 polyH6; have polyH28 := Poly.volumeFinset polyH0 (fun (j_1 : J) => (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))).1); have polyH29 := Poly.volumeFinset polyH0 (fun (j_1 : J) => (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))).2); have polyH30 := Poly.volumeFinset polyH0 (fun (j_1 : J) => (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))).3); have polyH31 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))))) polyH29 polyH30; have polyH32 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))))) polyH28 polyH31; have polyH33 := Poly.add polyH32 polyH6; have polyH34 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (n j_15) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15))), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15))), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15)))))))) polyH33; have polyH35 := Poly.add polyH31 polyH6; have polyH36 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (n j_15) (Prod.snd (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15))), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15))), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15)))))))) polyH35; have polyH37 := Poly.add polyH34 polyH36; have polyH38 := Poly.add polyH31 polyH13; have polyH39 := Poly.mul polyH12 polyH38; have polyH40 := Poly.add polyH37 polyH39; have polyH41 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (n j_15) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15))), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15))), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15)))))))) polyH40; have polyH42 := Poly.add polyH27 polyH41; have polyH43 := Poly.add polyH32 polyH13; have polyH44 := Poly.mul polyH12 polyH43; have polyH45 := Poly.add polyH42 polyH44; have polyH46 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1) × Finset (Fin n_1) × Finset (Fin n_1)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) (x : Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (Uniform.stateParts) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (n j_15) (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15)))))) polyH45; have polyH47 := Poly.add polyH25 polyH46; have polyH48 := Poly.add polyH26 polyH13; have polyH49 := Poly.mul polyH12 polyH48; have polyH50 := Poly.add polyH47 polyH49; have polyH51 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.fst x)) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _)) (Uniform.stateRight) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH50; have polyH52 := Poly.add polyH17 polyH51; have polyH53 := Poly.const (n) (20); have polyH54 := Poly.add polyH5 (htv); have polyH55 := Poly.add polyH54 polyH30; have polyH56 := Poly.add polyH55 polyH13; have polyH57 := Poly.mul polyH53 polyH56; have polyH58 := Poly.add polyH52 polyH57; have polyH59 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.fst x)) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _)) Uniform.stateRight) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH58; have polyH60 := Poly.const (n) (100000000000); have polyH61 := Poly.add (hl) polyH13; have polyH62 := Poly.mul polyH60 polyH61; have polyH63 := Poly.const (n) (Classical.choose Costs.setEq); have polyH64 := Poly.base (n); have polyH65 := Poly.pow polyH64 (4); have polyH66 := Poly.mul polyH63 polyH65; have polyH67 := Poly.add polyH66 (htv); have polyH68 := Poly.add polyH67 polyH30; have polyH69 := Poly.add polyH68 polyH13; have polyH70 := Poly.mul polyH62 polyH69; have polyH71 := Poly.of_le (fun (j_15 : J) => (@Uniform.time_lookup_setEq_le (n j_15) (Prod.snd (Prod.snd (u j_15, U j_15, tab j_15))) ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_15))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst (u j_15, U j_15, tab j_15)))))) polyH70; have polyH72 := Poly.add polyH59 polyH71; have polyH73 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (u j_1, U j_1, tab j_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst (u j_1, U j_1, tab j_1))))) (htv) polyH30; have polyH74 := Poly.add polyH73 polyH13; have polyH75 := Poly.mul polyH12 polyH74; have polyH76 := Poly.add polyH72 polyH75; have polyH77 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd x), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x)))) (fun (i : ℕ) (x : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.fst x)) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _)) Uniform.stateRight)) (@Uniform.lookupA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ Uniform.setEq) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH76; have polyH78 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_15) (Prod.snd (u j_15, U j_15, tab j_15))))) polyH9; have polyH79 := Poly.add polyH8 polyH78; have polyH80 := Poly.add polyH79 polyH15; have polyH81 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH80; have polyH82 := Poly.add polyH81 polyH18; have polyH83 := Poly.add polyH5 polyH3; have polyH84 := Poly.add polyH83 polyH2; have polyH85 := Poly.add polyH84 polyH13; have polyH86 := Poly.mul polyH53 polyH85; have polyH87 := Poly.add polyH82 polyH86; have polyH88 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Universe) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH87; have polyH89 := Poly.add polyH77 polyH88; have polyH90 := Poly.add polyH5 (hL); have polyH91 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (u j_1, U j_1, tab j_1)), Prod.fst (u j_1, U j_1, tab j_1))) polyH3 polyH2; have polyH92 := Poly.add polyH90 polyH91; have polyH93 := Poly.add polyH92 polyH13; have polyH94 := Poly.mul polyH53 polyH93; have polyH95 := Poly.add polyH89 polyH94; have polyH96 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (x_1 : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd x_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x_1)))) x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd x), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd x), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x)))) (fun (i : ℕ) (x : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.fst x)) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _)) Uniform.stateRight)) (@Uniform.lookupA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ Uniform.setEq)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH95; have polyH97 := @Poly.optionMapTime (ℕ) (J) (n) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.snd ((fun (x : List (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Universe (n j_1) × List (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1)))) => (Prod.snd (Prod.snd x), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x)))) (u j_1, U j_1, tab j_1)), Prod.fst (Prod.snd (u j_1, U j_1, tab j_1)), Prod.fst (u j_1, U j_1, tab j_1))) (fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Universe (n j_1) × List (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1)))) => (Prod.snd (Prod.snd x), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x)))) (u j_1, U j_1, tab j_1)), Prod.fst (Prod.snd (u j_1, U j_1, tab j_1)), Prod.fst (u j_1, U j_1, tab j_1))) (fun (n_1 : ℕ) (x : OAI.ThreeMachine.Algorithm.Block (Fin n_1) × Universe n_1 × OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin n_1) => 1)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd x))) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length (Prod.fst x)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd x))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd x))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time (Prod.fst x) x_1) (Uniform.advanceLast) (7) (2) (Max.max (2 * 1) (Max.max (2 * 1) (2 * 1))) (2) (ha) (hL) polyH91 (hAv); have polyH98 := Poly.add polyH96 polyH97; have polyH99 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : List (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Universe (n j_1) × List (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1)))) => (Prod.snd (Prod.snd x), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x)))) (u j_1, U j_1, tab j_1)), Prod.fst (Prod.snd (u j_1, U j_1, tab j_1)), Prod.fst (u j_1, U j_1, tab j_1))) (hL) polyH91; have polyH100 := Poly.add polyH99 polyH13; have polyH101 := Poly.mul polyH12 polyH100; have polyH102 := Poly.add polyH98 polyH101; have polyH103 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => ((fun (x_1 : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd x_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x_1)))) x), Prod.fst (Prod.snd x), Prod.fst x)) (fun (i : ℕ) (x : Option (OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.map (fun (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin i) => 1)) fun (x_1 : Fin i) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin i) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length (Prod.fst (a, Prod.snd x))) fun (x_1 : Fin i) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin i) => 1)) fun (x_2 : Fin i) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin i) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin i) => 1)) fun (x_2 : Fin i) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin i) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time (Prod.fst (a, Prod.snd x)) x_1) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (x_1 : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd x_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x_1)))) x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd x), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd x), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x)))) (fun (i : ℕ) (x : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Prod.fst x))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.fst x)) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _)) Uniform.stateRight)) (@Uniform.lookupA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ Uniform.setEq)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.optionMap ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : OAI.ThreeMachine.Algorithm.Block (Fin n_1) × Universe n_1 × OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin n_1) => 1)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd x))) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length (Prod.fst x)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd x))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.snd (Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.snd (Prod.snd x))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.snd (Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time (Prod.fst x) x_1) Uniform.advanceLast) (n j_15) ((u j_15, U j_15, tab j_15))))) polyH102; exact Poly.lift polyH103 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_solve (n : ℕ) (x : SolveInput n) :
    solve.time n x = ((solveW.comp setIsEmpty).ite (solveU.comp (blockEmpty.comp some)) solveOut).time n x := by
  simp only [solve, time_congr, solveOut, solveMarks, solveS, solveU, solveM, solveT, solveF, solveZ, solveW]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}
theorem volumeSolve (M : ∀ j, Matrix (n j)) (tab : ∀ j, Table (n j))
    (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))
    (hn : Poly s n d) (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly s (fun j => volume (Algorithm.solve (matrixRel (M j)) (tab j) (fs j) (zs j) (W j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by (have polyH0 := Poly.const (s) (10); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j b h
  have hs := blockSmall_of_good (Algorithm.solve_good _ (ht j) _ _ h)
    (Algorithm.solve_bounded _ (hb j) _ _ h)
  exact volume_block_le b hs.1 hs.2
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}
theorem volumeSolveOut (M : ∀ j, Matrix (n j)) (tab : ∀ j, Table (n j))
    (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))
    (hn : Poly s n d) (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly s (fun j => volume (Algorithm.firstResult
      (fun u => (Algorithm.lookup (tab j) u.1.right).map (u.1.finish u.2))
      (Algorithm.markings (tab j) (Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)) (n j)))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 100*(n j+2)^2) (2*d) from by (have polyH0 := Poly.const (s) (100); have polyH1 := Poly.const (s) (2); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j b h
  obtain ⟨⟨u,bb⟩,hmem,hm⟩ := Algorithm.firstResult_some h
  obtain ⟨t,ht',rfl⟩ := Option.map_eq_some_iff.mp hm
  have hmark : MarksSmall (Algorithm.markings (tab j)
      (Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)) (n j)) := markings_small (matrixRel (M j)) (ht j) (hb j)
    (fun _ hu => Algorithm.states_compatible _ hu) (n j)
  have htSmall : TableSmall (tab j) := fun a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  exact volume_advance_le u bb t (hmark u bb hmem) (htSmall _ _ (Algorithm.lookup_mem ht'))
end ThreeMachine.StackCompiler.Poly
end

end OAI
end

section
-- module TableCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

theorem time_tableBody_le {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (i : I) (a : α i) (e : γ i) :
    (tableBody R).time i (a,e) ≤ 10000000000*(R.time i (a,e)+volume (f i (a,e))+volume a+volume e+1) := by
  have hmem : ∀ b ∈ f i (a,e), volume b ≤ volume (f i (a,e)) := by
    intro b hb
    rw [show f i (a,e) = Option.some b from hb,volume_some]
    omega
  have h := time_optionMap (swap : Uniform (fun i (x : β i × α i) => (x.2,x.1))) i
    (f i (a,e)) a (100*(volume (f i (a,e))+volume a+1))
    (volume (f i (a,e))+volume a+1) (by
      intro b hb
      have := hmem b hb
      simp only [swap,time_pair,time_fst,time_snd,volume_pair]
      omega) (by
      intro b hb
      have := hmem b hb
      simp only [volume_pair]
      omega)
  simp only [tableBody,time_comp,time_pair,time_fst,volume_pair]
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler
variable {α : Type u5} {β : Type u6} [Coding α] [Coding β]
theorem volume_tableBody (o : Option β) (a : α) :
    volume (o.map (fun b => (a,b))) ≤ volume o+volume a+1 := by
  cases o <;> simp only [Option.map_none,Option.map_some,volume_none,volume_some,volume_pair] <;> omega
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u7} {J : Type u8} {s : J → ℕ} {α : I → Type u9} {β : I → Type u10} {γ : I → Type u11}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
theorem tableOfTime {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))
    {l t v a vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1) (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hv : Poly (fun p : Pool idx xs => s p.1) (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v)
    (ha : Poly (fun p : Pool idx xs => s p.1) (fun p => volume p.2.1) a)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => R.tableOf.time (idx j) (xs j,e j))
      (l+Max.max (Max.max t (Max.max v (Max.max a ve))) (Max.max vx (Max.max ve (l+Max.max v a)))) := by
  have hve := he.precomp (fun p : Pool idx xs => p.1)
  have hT : Poly (fun p : Pool idx xs => s p.1)
      (fun p => (Uniform.tableBody R).time (idx p.1) (p.2.1,e p.1)) (Max.max t (Max.max v (Max.max a ve))) := by
    apply of_le (fun p : Pool idx xs => Uniform.time_tableBody_le R (idx p.1) p.2.1 (e p.1))
    (have polyH0 := Poly.const (fun (p_1 : Poly.Pool idx xs) => s (Sigma.fst p_1)) (10000000000); have polyH1 := Poly.add (ht) (hv); have polyH2 := Poly.add polyH1 (ha); have polyH3 := Poly.add polyH2 (hve); have polyH4 := Poly.const (fun (p_1 : Poly.Pool idx xs) => s (Sigma.fst p_1)) (1); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.mul polyH0 polyH5; exact Poly.lift polyH6 (by first | decide +kernel | omega))
  have hV : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume ((f (idx p.1) (p.2.1,e p.1)).map (fun b => (p.2.1,b)))) (Max.max v a) := by
    apply of_le (fun p : Pool idx xs => volume_tableBody (f (idx p.1) (p.2.1,e p.1)) p.2.1)
    (have polyH0 := Poly.add (hv) (ha); have polyH1 := Poly.const (fun (p_1 : Poly.Pool idx xs) => s (Sigma.fst p_1)) (1); have polyH2 := Poly.add polyH0 polyH1; exact Poly.lift polyH2 (by first | decide +kernel | omega))
  exact filterMapTime idx xs e (Uniform.tableBody R) hl hT hx he hV
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (ms : ∀ j, Marks (n j)) (v : ∀ j, Algorithm.State (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (tab : ∀ j, Table (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (sts : ∀ j, List (Algorithm.State (Fin (n j))))

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (sts : ∀ j, List (Algorithm.State (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module MatrixCosts
namespace OAI

universe u1 u2 u3 u4 u5

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

theorem solveOut
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solveOut.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  let sts j := Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)
  have hsl : Poly n (fun j => (sts j).length) 30003 := by
    apply Poly.of_le (fun j => Algorithm.states_length _ _ _ _)
    (have polyH0 := Poly.mul (hf) (hz); exact Poly.lift polyH0 (by first | decide +kernel | omega))
  have hs : ∀ j u, u ∈ sts j → u.Compatible (matrixRel (M j)) (W j) :=
    fun j _ hu => Algorithm.states_compatible _ hu
  let ms j := Algorithm.markings (tab j) (sts j) (n j)
  have hml : Poly n (fun j => (ms j).length) 30003 :=
    Poly.of_le (fun j => Algorithm.markings_length _ _ _) hsl
  have hms (j) : MarksSmall (ms j) := markings_small _ (ht j) (hb j) (hs j) _
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hms
  have hMB := Poly.volumeSmallBlock (fun p : Poly.ListPool ms => p.2.1.2)
    ((Poly.size n).precomp Sigma.fst) (fun p => hms p.1 _ _ p.2.2)
  have hMarks := solveMarks n U M tab fs zs W hl hf hz ht hb
  have hFinish := finishing (fun p : Poly.ListPool ms => n p.1) (fun p => U p.1)
    (fun p => tab p.1) (fun p => p.2.1) (hl.precomp Sigma.fst) (fun p => hts p.1)
    (fun p => hms p.1 _ _ p.2.2)
  have hAv : Poly (fun p : Poly.ListPool ms => n p.1)
      (fun p => volume ((Algorithm.lookup (tab p.1) p.2.1.1.right).map
        (p.2.1.1.finish p.2.1.2))) 2 := by
    apply Poly.volumeOption _ (show Poly (fun p : Poly.ListPool ms => n p.1)
      (fun p => 100*(n p.1+2)^2) 2 from by (have polyH0 := Poly.const (fun (p_1 : Poly.ListPool ms) => n (Sigma.fst p_1)) (100); have polyH1 := Poly.base (fun (p_1 : Poly.ListPool ms) => n (Sigma.fst p_1)); have polyH2 := Poly.pow polyH1 (2); have polyH3 := Poly.mul polyH0 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega)))
    intro p b hb'
    obtain ⟨t,ht',rfl⟩ := Option.map_eq_some_iff.mp hb'
    exact volume_advance_le _ _ _ (hms p.1 _ _ p.2.2) (hts p.1 _ _ (Algorithm.lookup_mem ht'))
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, fs j_1, zs j_1, W j_1)) (htv) polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH6; have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH7; have polyH9 := Poly.const (n) (2); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_30) ((U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH10; have polyH12 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_30) ((U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH10; have polyH13 := Poly.add polyH7 polyH9; have polyH14 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_30) (Prod.snd (U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH13; have polyH15 := Poly.add polyH6 polyH9; have polyH16 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_30) (Prod.snd (Prod.snd (U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30)))))) polyH15; have polyH17 := Poly.add polyH14 polyH16; have polyH18 := Poly.const (n) (10); have polyH19 := Poly.const (n) (1); have polyH20 := Poly.add polyH6 polyH19; have polyH21 := Poly.mul polyH18 polyH20; have polyH22 := Poly.add polyH17 polyH21; have polyH23 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _) (n j_30) (Prod.snd (U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH22; have polyH24 := Poly.add polyH12 polyH23; have polyH25 := Poly.add polyH7 polyH19; have polyH26 := Poly.mul polyH18 polyH25; have polyH27 := Poly.add polyH24 polyH26; have polyH28 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _)) (n j_30) ((U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH27; have polyH29 := Poly.add polyH11 polyH28; have polyH30 := Poly.const (n) (20); have polyH31 := Poly.add polyH8 polyH1; have polyH32 := Poly.add polyH31 (htv); have polyH33 := Poly.add polyH32 polyH19; have polyH34 := Poly.mul polyH30 polyH33; have polyH35 := Poly.add polyH29 polyH34; have polyH36 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (Universe) (Table) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (Uniform.solveU) (Uniform.solveT) (n j_30) ((U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH35; have polyH37 := Poly.add (hMarks) polyH36; have polyH38 := Poly.add polyH8 (hmv); have polyH39 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) polyH1 (htv); have polyH40 := Poly.add polyH38 polyH39; have polyH41 := Poly.add polyH40 polyH19; have polyH42 := Poly.mul polyH30 polyH41; have polyH43 := Poly.add polyH37 polyH42; have polyH44 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) (fun (i : ℕ) => Universe i × Table i) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd x))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) n_1) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst x, Prod.fst (Prod.snd (Prod.snd x)))) (Uniform.solveMarks) (@Uniform.pair ℕ Uniform.SolveInput Universe Table _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) Uniform.solveU Uniform.solveT) (n j_30) ((U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH43; have polyH45 := @Poly.firstResultTime (ℕ) (J) (n) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) (n j_1), Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (fun (j_1 : J) => Prod.snd (OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) (n j_1), Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (fun (n_1 : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × Universe n_1 × Table n_1) => Option.map (fun (t : OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin n_1) => 1)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst x)) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length t) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst x)) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst x)) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time t x_1) (OAI.ThreeMachine.Algorithm.lookup (Prod.snd (Prod.snd x)) (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst x))))) (Uniform.finishing) (30003) (60002) (30003 + 2 * 1) (Max.max (2 * 1) (30000 + 2 * 1)) (2) (hml) (hFinish) (hmv) polyH39 (hAv); have polyH46 := Poly.add polyH44 polyH45; have polyH47 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) (n j_1), Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (hmv) polyH39; have polyH48 := Poly.add polyH47 polyH19; have polyH49 := Poly.mul polyH18 polyH48; have polyH50 := Poly.add polyH46 polyH49; have polyH51 := Poly.of_le (fun (j_30 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.SolveInput) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : Uniform.SolveInput i) => (OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd x))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) i, Prod.fst x, Prod.fst (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.map (fun (t : OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst (a, Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin i) => 1)) fun (x_1 : Fin i) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (a, Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst (a, Prod.snd x))) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst (a, Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin i) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length t) fun (x_1 : Fin i) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst (Prod.fst (a, Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst (a, Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin i) => 1)) fun (x_2 : Fin i) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (a, Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst (a, Prod.snd x))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst (a, Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin i) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst (a, Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin i) => 1)) fun (x_2 : Fin i) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst (a, Prod.snd x))) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst (a, Prod.snd x))) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst (a, Prod.snd x))) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin i) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time t x_1) (OAI.ThreeMachine.Algorithm.lookup (Prod.snd (Prod.snd (a, Prod.snd x))) (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst (a, Prod.snd x)))))) (Prod.fst x)) (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) (fun (i : ℕ) => Universe i × Table i) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd x))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) n_1) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst x, Prod.fst (Prod.snd (Prod.snd x)))) Uniform.solveMarks (@Uniform.pair ℕ Uniform.SolveInput Universe Table _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) Uniform.solveU Uniform.solveT)) (@Uniform.firstResultA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i) _ _ _ (fun (n_1 : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × Universe n_1 × Table n_1) => Option.map (fun (t : OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin n_1) => 1)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst x)) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length t) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst x)) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Prod.fst x)) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd (Prod.fst x)) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd (Prod.fst x)) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time t x_1) (OAI.ThreeMachine.Algorithm.lookup (Prod.snd (Prod.snd x)) (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Prod.fst x))))) Uniform.finishing) (n j_30) ((U j_30, M j_30, tab j_30, fs j_30, zs j_30, W j_30))))) polyH50; exact Poly.lift polyH51 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem solve
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solve.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hOut := solveOut n U M tab fs zs W hl hf hz ht hb
  have hOV := Poly.volumeSolveOut M tab fs zs W (Poly.size n) ht hb
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, fs j_1, zs j_1, W j_1)) (htv) polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH6; have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH7; have polyH9 := Poly.const (n) (2); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH10; have polyH12 := Poly.add polyH7 polyH9; have polyH13 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_21) (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH12; have polyH14 := Poly.add polyH6 polyH9; have polyH15 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_21) (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21)))))) polyH14; have polyH16 := Poly.add polyH5 polyH9; have polyH17 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_21) (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))))) polyH16; have polyH18 := Poly.add polyH4 polyH9; have polyH19 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_21) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21)))))))) polyH18; have polyH20 := Poly.add polyH17 polyH19; have polyH21 := Poly.const (n) (10); have polyH22 := Poly.const (n) (1); have polyH23 := Poly.add polyH4 polyH22; have polyH24 := Poly.mul polyH21 polyH23; have polyH25 := Poly.add polyH20 polyH24; have polyH26 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n j_21) (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))))) polyH25; have polyH27 := Poly.add polyH15 polyH26; have polyH28 := Poly.add polyH5 polyH22; have polyH29 := Poly.mul polyH21 polyH28; have polyH30 := Poly.add polyH27 polyH29; have polyH31 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)) (n j_21) (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21)))))) polyH30; have polyH32 := Poly.add polyH13 polyH31; have polyH33 := Poly.add polyH6 polyH22; have polyH34 := Poly.mul polyH21 polyH33; have polyH35 := Poly.add polyH32 polyH34; have polyH36 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _))) (n j_21) (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH35; have polyH37 := Poly.add polyH11 polyH36; have polyH38 := Poly.add polyH7 polyH22; have polyH39 := Poly.mul polyH21 polyH38; have polyH40 := Poly.add polyH37 polyH39; have polyH41 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)))) (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH40; have polyH42 := Poly.add polyH3 polyH9; have polyH43 := Poly.const (n) (10000); have polyH44 := Poly.add polyH3 polyH22; have polyH45 := Poly.mul polyH43 polyH44; have polyH46 := Poly.of_le (fun (j_21 : J) => (@Uniform.time_test_le (ℕ) (fun (i : ℕ) => List (Fin i)) _ (fun (i : ℕ) (xs : List (Fin i)) => !List.isEmpty xs) (@Uniform.isCons._proof_1 (ℕ) (Fin) _) (n j_21) (Finset.sort (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21)))))) fun (x1 x2 : Fin (n j_21)) => x1 ≤ x2))) polyH45; have polyH47 := Poly.add polyH42 polyH46; have polyH48 := Poly.mul polyH21 polyH44; have polyH49 := Poly.add polyH47 polyH48; have polyH50 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => Bool) _ _ _ (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) (fun (i : ℕ) (xs : List (Fin i)) => !List.isEmpty xs) (Uniform.setList) (@Uniform.isCons ℕ Fin _) (n j_21) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))))))) polyH49; have polyH51 := Poly.of_le (fun (j_21 : J) => (@Realizer.time_not_le ((fun (xs : List (Fin (n j_21))) => !List.isEmpty xs) ((fun (s : Finset (Fin (n j_21))) => Finset.sort s fun (x1 x2 : Fin (n j_21)) => x1 ≤ x2) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21)))))))))) polyH43; have polyH52 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (Bool) (Bool) _ _ (Bool.not) (Realizer.not) (n j_21) ((fun (xs : List (Fin (n j_21))) => !List.isEmpty xs) ((fun (s : Finset (Fin (n j_21))) => Finset.sort s fun (x1 x2 : Fin (n j_21)) => x1 ≤ x2) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))))))))) polyH51; have polyH53 := Poly.add polyH50 polyH52; have polyH54 := Poly.volumeBool (n) (fun (j_1 : J) => !List.isEmpty ((fun (s : Finset (Fin (n j_1))) => Finset.sort s fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))))); have polyH55 := Poly.add polyH54 polyH22; have polyH56 := Poly.mul polyH21 polyH55; have polyH57 := Poly.add polyH53 polyH56; have polyH58 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Bool) (fun (x : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : Finset (Fin i)) => (fun (xs : List (Fin i)) => !List.isEmpty xs) ((fun (s : Finset (Fin i)) => Finset.sort s fun (x1 x2 : Fin i) => x1 ≤ x2) x)) (fun (x : ℕ) => Bool.not) (@Uniform.comp ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => Bool) _ _ _ (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) (fun (i : ℕ) (xs : List (Fin i)) => !List.isEmpty xs) Uniform.setList (@Uniform.isCons ℕ Fin _)) (Realizer.uniform Realizer.not ℕ) (n j_21) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))))))) polyH57; have polyH59 := Poly.add polyH41 polyH58; have polyH60 := Poly.add polyH59 polyH48; have polyH61 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.SolveInput) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Bool) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Decidable.decide (s = ∅)) (Uniform.solveW) (Uniform.setIsEmpty) (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH60; have polyH62 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH10; have polyH63 := Poly.reparam (@Costs.blockEmpty) (fun (j_1 : J) => Sigma.mk (n j_1) (Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))) polyH0; have polyH64 := Poly.const (n) (100); have polyH65 := Poly.const (n) (0); have polyH66 := Poly.const (fun (q : Poly.FinPool fun (j_1 : J) => n j_1) => n (Sigma.fst q)) (0); have polyH67 := Poly.volumeNat polyH66; have polyH68 := Poly.volumeFunction (fun (j_1 : J) (x : Fin (n j_1)) => 0) polyH0 polyH67; have polyH69 := Poly.volumeBlock (fun (j_1 : J) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_1)) => 0) polyH65 polyH68; have polyH70 := Poly.add polyH69 polyH22; have polyH71 := Poly.mul polyH64 polyH70; have polyH72 := Poly.of_le (fun (j_21 : J) => (@Uniform.time_some_le (ℕ) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ (n j_21) (OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_21)) => 0))) polyH71; have polyH73 := Poly.add polyH63 polyH72; have polyH74 := Poly.mul polyH21 polyH70; have polyH75 := Poly.add polyH73 polyH74; have polyH76 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin n_1) => 0) (fun (i : ℕ) (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some a) (Uniform.blockEmpty) (@Uniform.some ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _) (n j_21) (Prod.fst (U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH75; have polyH77 := Poly.add polyH62 polyH76; have polyH78 := Poly.add polyH1 polyH22; have polyH79 := Poly.mul polyH21 polyH78; have polyH80 := Poly.add polyH77 polyH79; have polyH81 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.SolveInput) (Universe) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Universe i) => (fun (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some a) ((fun (x_1 : Universe i) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_2 : Fin i) => 0) x)) (Uniform.solveU) (@Uniform.comp ℕ Universe (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin n_1) => 0) (fun (i : ℕ) (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some a) Uniform.blockEmpty (@Uniform.some ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _)) (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH80; have polyH82 := Poly.add polyH61 polyH81; have polyH83 := Poly.add polyH82 (hOut); have polyH84 := Poly.const (n) (1000); have polyH85 := Poly.volumeOptionSome (fun (j_1 : J) => (fun (x : Universe (n j_1)) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin (n j_1)) => 0) ((fun (x : Uniform.SolveInput (n j_1)) => Prod.fst x) (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))) polyH69; have polyH86 := Poly.add polyH8 polyH85; have polyH87 := Poly.add polyH86 (hOV); have polyH88 := Poly.add polyH87 polyH22; have polyH89 := Poly.mul polyH84 polyH88; have polyH90 := Poly.add polyH83 polyH89; have polyH91 := Poly.of_le (fun (j_21 : J) => (@Uniform.time_ite_le (ℕ) (Uniform.SolveInput) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (fun (i : ℕ) (x : Uniform.SolveInput i) => (fun (s : Finset (Fin i)) => Decidable.decide (s = ∅)) ((fun (x_1 : Uniform.SolveInput i) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x_1))))) x)) (fun (i : ℕ) (x : Uniform.SolveInput i) => (fun (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some a) ((fun (x_1 : Universe i) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_2 : Fin i) => 0) ((fun (x_1 : Uniform.SolveInput i) => Prod.fst x_1) x))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.firstResult (fun (u : OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => Option.map (fun (t : OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd u) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_1 : Fin n_1) => 1)) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst u) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd u) x_1 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd u) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1) x_1) + OAI.ThreeMachine.Algorithm.Block.length t) fun (x_1 : Fin n_1) => if x_1 ∈ OAI.ThreeMachine.Algorithm.State.upto (Prod.fst u) then OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd u) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst u) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd u) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd u) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) x_1 else OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (OAI.ThreeMachine.Algorithm.Block.length (Prod.snd u) + OAI.ThreeMachine.Algorithm.Block.length (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_2 : Fin n_1) => 1)) fun (x_2 : Fin n_1) => if x_2 ∈ OAI.ThreeMachine.Algorithm.State.left (Prod.fst u) then OAI.ThreeMachine.Algorithm.Block.time (Prod.snd u) x_2 else OAI.ThreeMachine.Algorithm.Block.length (Prod.snd u) + OAI.ThreeMachine.Algorithm.Block.time (OAI.ThreeMachine.Algorithm.Block.mk (1) fun (x_3 : Fin n_1) => 1) x_2) + OAI.ThreeMachine.Algorithm.Block.time t x_1) (OAI.ThreeMachine.Algorithm.lookup (Prod.fst (Prod.snd (Prod.snd x))) (OAI.ThreeMachine.Algorithm.State.right (Prod.fst u)))) (OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd x))) (OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) n_1)) (@Uniform.comp ℕ Uniform.SolveInput (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Bool) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Decidable.decide (s = ∅)) Uniform.solveW Uniform.setIsEmpty) (@Uniform.comp ℕ Uniform.SolveInput Universe (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Universe i) => (fun (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some a) ((fun (x_1 : Universe i) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_2 : Fin i) => 0) x)) Uniform.solveU (@Uniform.comp ℕ Universe (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin n_1) => 0) (fun (i : ℕ) (a : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some a) Uniform.blockEmpty (@Uniform.some ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _))) (Uniform.solveOut) (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21)))) polyH90; have polyH92 := Poly.of_le (fun (j_21 : J) => (le_of_eq (@Uniform.time_solve (n j_21) ((U j_21, M j_21, tab j_21, fs j_21, zs j_21, W j_21))))) polyH91; exact Poly.lift polyH92 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_layerStep (n : ℕ) (x : LayerEnv n × Table n) :
    layerStep.time n x =
      (fst.pair (((fst.comp (snd.comp (snd.comp fst))).pair id).comp layerBody.tableOfA)).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))
theorem layerBody
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.layerBody.time (n j) (W j,((U j,(M j,(fs j,zs j))),tab j))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hS := solve n U M tab fs zs W hl hf hz ht hb
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH2 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH3 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1)) (hfv) (hzv); have polyH5 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1)) polyH3 polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1)) polyH2 polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1, fs j_1, zs j_1), tab j_1)) polyH6 (htv); have polyH8 := Poly.volumeProd (fun (j_1 : J) => (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1)) polyH1 polyH7; have polyH9 := Poly.const (n) (2); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _ (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH10; have polyH12 := Poly.add polyH7 polyH9; have polyH13 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (Table) _ _ (n j_20) (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH12; have polyH14 := Poly.add polyH6 polyH9; have polyH15 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ (n j_20) (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))) polyH14; have polyH16 := Poly.add polyH13 polyH15; have polyH17 := Poly.const (n) (10); have polyH18 := Poly.const (n) (1); have polyH19 := Poly.add polyH6 polyH18; have polyH20 := Poly.mul polyH17 polyH19; have polyH21 := Poly.add polyH16 polyH20; have polyH22 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (Universe) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (n j_20) (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH21; have polyH23 := Poly.add polyH11 polyH22; have polyH24 := Poly.add polyH7 polyH18; have polyH25 := Poly.mul polyH17 polyH24; have polyH26 := Poly.add polyH23 polyH25; have polyH27 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.fst x)) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _)) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH26; have polyH28 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ (n j_20) (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))) polyH14; have polyH29 := Poly.add polyH5 polyH9; have polyH30 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ (n j_20) (Prod.snd (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))))) polyH29; have polyH31 := Poly.add polyH28 polyH30; have polyH32 := Poly.add polyH5 polyH18; have polyH33 := Poly.mul polyH17 polyH32; have polyH34 := Poly.add polyH31 polyH33; have polyH35 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (n j_20) (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))) polyH34; have polyH36 := Poly.add polyH13 polyH35; have polyH37 := Poly.add polyH36 polyH20; have polyH38 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (Matrix) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _)) (n j_20) (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH37; have polyH39 := Poly.add polyH11 polyH38; have polyH40 := Poly.add polyH39 polyH25; have polyH41 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst x))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _))) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH40; have polyH42 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (Table) _ _ (n j_20) (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH12; have polyH43 := Poly.add polyH11 polyH42; have polyH44 := Poly.add polyH43 polyH25; have polyH45 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH44; have polyH46 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ (n j_20) (Prod.snd (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))))) polyH29; have polyH47 := Poly.add polyH4 polyH9; have polyH48 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ (n j_20) (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))))) polyH47; have polyH49 := Poly.add polyH46 polyH48; have polyH50 := Poly.add polyH4 polyH18; have polyH51 := Poly.mul polyH17 polyH50; have polyH52 := Poly.add polyH49 polyH51; have polyH53 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _) (n j_20) (Prod.snd (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))))) polyH52; have polyH54 := Poly.add polyH28 polyH53; have polyH55 := Poly.add polyH54 polyH33; have polyH56 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)) (n j_20) (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))) polyH55; have polyH57 := Poly.add polyH13 polyH56; have polyH58 := Poly.add polyH57 polyH20; have polyH59 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))) (n j_20) (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH58; have polyH60 := Poly.add polyH11 polyH59; have polyH61 := Poly.add polyH60 polyH25; have polyH62 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)))) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH61; have polyH63 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ (n j_20) (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))))) polyH47; have polyH64 := Poly.add polyH46 polyH63; have polyH65 := Poly.add polyH64 polyH51; have polyH66 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _) (n j_20) (Prod.snd (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))))) polyH65; have polyH67 := Poly.add polyH28 polyH66; have polyH68 := Poly.add polyH67 polyH33; have polyH69 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)) (n j_20) (Prod.fst (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20)))))) polyH68; have polyH70 := Poly.add polyH13 polyH69; have polyH71 := Poly.add polyH70 polyH20; have polyH72 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))) (n j_20) (Prod.snd (W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH71; have polyH73 := Poly.add polyH11 polyH72; have polyH74 := Poly.add polyH73 polyH25; have polyH75 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)))) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH74; have polyH76 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _ (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH10; have polyH77 := Poly.add polyH75 polyH76; have polyH78 := Poly.const (n) (20); have polyH79 := Poly.add polyH8 (hzv); have polyH80 := Poly.add polyH79 polyH1; have polyH81 := Poly.add polyH80 polyH18; have polyH82 := Poly.mul polyH78 polyH81; have polyH83 := Poly.add polyH77 polyH82; have polyH84 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH83; have polyH85 := Poly.add polyH62 polyH84; have polyH86 := Poly.add polyH8 (hfv); have polyH87 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.fst (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))) (hzv) polyH1; have polyH88 := Poly.add polyH86 polyH87; have polyH89 := Poly.add polyH88 polyH18; have polyH90 := Poly.mul polyH78 polyH89; have polyH91 := Poly.add polyH85 polyH90; have polyH92 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _)) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH91; have polyH93 := Poly.add polyH45 polyH92; have polyH94 := Poly.add polyH8 (htv); have polyH95 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.fst (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))) (hfv) polyH87; have polyH96 := Poly.add polyH94 polyH95; have polyH97 := Poly.add polyH96 polyH18; have polyH98 := Poly.mul polyH78 polyH97; have polyH99 := Poly.add polyH93 polyH98; have polyH100 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (Table) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _))) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH99; have polyH101 := Poly.add polyH41 polyH100; have polyH102 := Poly.add polyH8 polyH3; have polyH103 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1)), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.fst (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))) (htv) polyH95; have polyH104 := Poly.add polyH102 polyH103; have polyH105 := Poly.add polyH104 polyH18; have polyH106 := Poly.mul polyH78 polyH105; have polyH107 := Poly.add polyH101 polyH106; have polyH108 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (Matrix) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst (Prod.snd x)))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst x))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _)))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _)))) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH107; have polyH109 := Poly.add polyH27 polyH108; have polyH110 := Poly.add polyH8 polyH2; have polyH111 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1)))), Prod.snd (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1)), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.fst (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))) polyH3 polyH103; have polyH112 := Poly.add polyH110 polyH111; have polyH113 := Poly.add polyH112 polyH18; have polyH114 := Poly.mul polyH78 polyH113; have polyH115 := Poly.add polyH109 polyH114; have polyH116 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (Universe) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.fst (Prod.snd x))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.fst (Prod.snd x))), Prod.snd (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.fst x)) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst (Prod.snd x)))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst x))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _)))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _))))) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH115; have polyH117 := Poly.add polyH116 (hS); have polyH118 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))), Prod.fst (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1)))), Prod.snd (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1)), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))))), Prod.fst (W j_1, (U j_1, M j_1, fs j_1, zs j_1), tab j_1))) polyH2 polyH111; have polyH119 := Poly.add polyH118 polyH18; have polyH120 := Poly.mul polyH17 polyH119; have polyH121 := Poly.add polyH117 polyH120; have polyH122 := Poly.of_le (fun (j_20 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.fst (Prod.snd x)), Prod.fst (Prod.snd (Prod.fst (Prod.snd x))), Prod.snd (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) => OAI.ThreeMachine.Algorithm.solve (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.fst (Prod.snd x))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.fst (Prod.snd x))), Prod.snd (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.fst x)) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst (Prod.snd x)))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.fst x))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _)))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x)))), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.snd (Prod.snd (Prod.snd (Prod.fst x)))) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))))) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _)))))) (Uniform.solve) (n j_20) ((W j_20, (U j_20, M j_20, fs j_20, zs j_20), tab j_20))))) polyH121; exact Poly.lift polyH122 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u5} (s n : J → ℕ) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module SchedulingCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
theorem layerStep
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.layerStep.time (n j) ((U j,(M j,(fs j,zs j))),tab j)) 150009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hBody := layerBody (fun p : Poly.ListPool fs => n p.1) (fun p => U p.1) (fun p => M p.1)
    (fun p => tab p.1) (fun p => fs p.1) (fun p => zs p.1) (fun p => p.2.1)
    (hl.precomp Sigma.fst) (hf.precomp Sigma.fst) (hz.precomp Sigma.fst)
    (fun p => ht p.1) (fun p => hb p.1)
  have hV := Poly.volumeSolve (fun p : Poly.ListPool fs => M p.1) (fun p => tab p.1)
    (fun p => fs p.1) (fun p => zs p.1) (fun p => p.2.1)
    ((Poly.size n).precomp Sigma.fst) (fun p => ht p.1) (fun p => hb p.1)
  have hA : Poly (fun p : Poly.ListPool fs => n p.1) (fun p => volume p.2.1) 2 := by (have polyH0 := Poly.size (fun (p_1 : Poly.ListPool fs) => n (Sigma.fst p_1)); have polyH1 := Poly.volumeFinset polyH0 (fun (p_1 : Poly.ListPool fs) => (Sigma.snd p_1).1); exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hE : Poly n (fun j => volume ((U j,(M j,(fs j,zs j))),tab j)) 30002 := by (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1)) (hfv) (hzv); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1)) polyH2 polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1)) polyH1 polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1, fs j_1, zs j_1), tab j_1)) polyH5 (htv); exact Poly.lift polyH6 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hTable := Poly.tableOfTime Uniform.layerBody n fs (fun j => ((U j,(M j,(fs j,zs j))),tab j))
    hf hBody hV hA hfv hE
  have hExact : Poly n (fun j => Uniform.layerBody.tableOfA.time (n j)
      (fs j,((U j,(M j,(fs j,zs j))),tab j))) 150009 := hTable
  have ho (j : J) : TableSmall (Algorithm.tableOf (fs j)
      (Algorithm.solve (matrixRel (M j)) (tab j) (fs j) (zs j))) := by
    intro W b h
    have hs := (Algorithm.mem_tableOf _ _ W b).mp h
    exact blockSmall_of_good (Algorithm.solve_good _ (ht j) _ _ hs.2)
      (Algorithm.solve_bounded _ (hb j) _ _ hs.2)
  have hOL : Poly n (fun j => (Algorithm.tableOf (fs j)
      (Algorithm.solve (matrixRel (M j)) (tab j) (fs j) (zs j))).length) 30000 :=
    Poly.of_le (fun j => Algorithm.tableOf_length _ _) hf
  have hOV := Poly.volumeTable _ (Poly.size n) hOL ho
  (have polyH0 := Poly.const (n) (2); have polyH1 := Poly.add (hE) polyH0; have polyH2 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (Table) _ _ (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH1; have polyH3 := Poly.size (n); have polyH4 := Poly.volumeUniverse polyH3 (fun (j_1 : J) => U j_1); have polyH5 := Poly.volumeMatrix polyH3 (fun (j_1 : J) => M j_1); have polyH6 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1)) (hfv) (hzv); have polyH7 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1)) polyH5 polyH6; have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1)) polyH4 polyH7; have polyH9 := Poly.add polyH8 polyH0; have polyH10 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ (n j_27) (Prod.fst ((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH9; have polyH11 := Poly.add polyH7 polyH0; have polyH12 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ (n j_27) (Prod.snd (Prod.fst ((U j_27, M j_27, fs j_27, zs j_27), tab j_27)))))) polyH11; have polyH13 := Poly.add polyH6 polyH0; have polyH14 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ (n j_27) (Prod.snd (Prod.snd (Prod.fst ((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))))) polyH13; have polyH15 := Poly.add polyH12 polyH14; have polyH16 := Poly.const (n) (10); have polyH17 := Poly.const (n) (1); have polyH18 := Poly.add polyH6 polyH17; have polyH19 := Poly.mul polyH16 polyH18; have polyH20 := Poly.add polyH15 polyH19; have polyH21 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _) (n j_27) (Prod.snd (Prod.fst ((U j_27, M j_27, fs j_27, zs j_27), tab j_27)))))) polyH20; have polyH22 := Poly.add polyH10 polyH21; have polyH23 := Poly.add polyH7 polyH17; have polyH24 := Poly.mul polyH16 polyH23; have polyH25 := Poly.add polyH22 polyH24; have polyH26 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)) (n j_27) (Prod.fst ((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH25; have polyH27 := Poly.add polyH2 polyH26; have polyH28 := Poly.add polyH8 polyH17; have polyH29 := Poly.mul polyH16 polyH28; have polyH30 := Poly.add polyH27 polyH29; have polyH31 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _))) (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH30; have polyH32 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH1; have polyH33 := Poly.add polyH31 polyH32; have polyH34 := Poly.const (n) (20); have polyH35 := Poly.add (hE) (hfv); have polyH36 := Poly.add polyH35 (hE); have polyH37 := Poly.add polyH36 polyH17; have polyH38 := Poly.mul polyH34 polyH37; have polyH39 := Poly.add polyH33 polyH38; have polyH40 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)))) (@Uniform.id ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _) (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH39; have polyH41 := Poly.add polyH40 (hExact); have polyH42 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst ((U j_1, M j_1, fs j_1, zs j_1), tab j_1)))), (U j_1, M j_1, fs j_1, zs j_1), tab j_1)) (hfv) (hE); have polyH43 := Poly.add polyH42 polyH17; have polyH44 := Poly.mul polyH16 polyH43; have polyH45 := Poly.add polyH41 polyH44; have polyH46 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i)) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst x))), x)) (fun (i : ℕ) (x : List (Finset (Fin i)) × Uniform.LayerEnv i × Table i) => OAI.ThreeMachine.Algorithm.tableOf (Prod.fst x) fun (a : Finset (Fin i)) => OAI.ThreeMachine.Algorithm.solve (matrixRel (Prod.fst (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x)))))) (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x)))))) (Prod.fst (a, Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)))) (@Uniform.id ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _)) (@Uniform.tableOfA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Uniform.LayerEnv i × Table i) _ _ _ (fun (n_1 : ℕ) (x : Finset (Fin n_1) × Uniform.LayerEnv n_1 × Table n_1) => OAI.ThreeMachine.Algorithm.solve (matrixRel (Prod.fst (Prod.snd (Prod.fst (Prod.snd x))))) (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (Prod.fst x)) Uniform.layerBody) (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH45; have polyH47 := Poly.add polyH2 polyH46; have polyH48 := Poly.add (hE) polyH8; have polyH49 := Poly.add polyH48 (hOV); have polyH50 := Poly.add polyH49 polyH17; have polyH51 := Poly.mul polyH34 polyH50; have polyH52 := Poly.add polyH47 polyH51; have polyH53 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (fun (x_1 : List (Finset (Fin i)) × Uniform.LayerEnv i × Table i) => OAI.ThreeMachine.Algorithm.tableOf (Prod.fst x_1) fun (a : Finset (Fin i)) => OAI.ThreeMachine.Algorithm.solve (matrixRel (Prod.fst (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x_1)))))) (Prod.snd (Prod.snd (a, Prod.snd x_1))) (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x_1)))))) (Prod.fst (a, Prod.snd x_1))) ((fun (x_1 : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst x_1))), x_1)) x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i)) × (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => (Prod.fst (Prod.snd (Prod.snd (Prod.fst x))), x)) (fun (i : ℕ) (x : List (Finset (Fin i)) × Uniform.LayerEnv i × Table i) => OAI.ThreeMachine.Algorithm.tableOf (Prod.fst x) fun (a : Finset (Fin i)) => OAI.ThreeMachine.Algorithm.solve (matrixRel (Prod.fst (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x)))))) (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd (a, Prod.snd x)))))) (Prod.fst (a, Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => Prod.fst (Prod.snd (Prod.snd (Prod.fst x)))) (fun (i : ℕ) (x : (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) => x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) Table _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _)))) (@Uniform.id ℕ (fun (i : ℕ) => (Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) × Table i) _)) (@Uniform.tableOfA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Uniform.LayerEnv i × Table i) _ _ _ (fun (n_1 : ℕ) (x : Finset (Fin n_1) × Uniform.LayerEnv n_1 × Table n_1) => OAI.ThreeMachine.Algorithm.solve (matrixRel (Prod.fst (Prod.snd (Prod.fst (Prod.snd x))))) (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.fst (Prod.snd x))))) (Prod.fst x)) Uniform.layerBody)) (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH52; have polyH54 := Poly.of_le (fun (j_27 : J) => (le_of_eq (@Uniform.time_layerStep (n j_27) (((U j_27, M j_27, fs j_27, zs j_27), tab j_27))))) polyH53; exact Poly.lift polyH54 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.layerStep := @OAI.ThreeMachine.StackCompiler.Costs.layerStep
