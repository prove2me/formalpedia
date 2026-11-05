-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.requestRawBound_length
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:44:16.844147+00:00
-- url     : https://prove2.me/submissions/ad8933b4-585c-47cc-afb3-0269011cec04

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_unaryAnswer

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

theorem layers_good (family triples : List (Finset J)) (k : ℕ) :
    TableGood r (layers r family triples k) := by
  induction k with
  | zero =>
    intro W s h
    have he : (W,s) = (∅,Block.empty) := by simpa only [layers, List.mem_singleton] using h
    cases he
    exact Block.valid_empty
  | succ k ih =>
    intro W s h
    exact solve_good r ih family triples ((mem_tableOf family _ W s).mp h).2

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

theorem layers_bounded (family triples : List (Finset J)) (k : ℕ) :
    TableBounded (layers r family triples k) := by
  induction k with
  | zero =>
    intro W s h
    have he : (W,s) = (∅,Block.empty) := by simpa only [layers,List.mem_singleton] using h
    cases he
    exact Block.bounded_empty
  | succ k ih =>
    intro W s h
    exact solve_bounded r ih family triples ((mem_tableOf family _ W s).mp h).2

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

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u33} {α : I → Type u34} {β : I → Type u35} {γ : I → Type u36}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u37} {α : I → Type u38} {β : I → Type u39} {γ : I → Type u40}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

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

theorem foldTime_length_le (i : I) (xs : List (α i)) (n : ℕ) :
    Realizer.foldTime ((snd.comp (Realizer.succ.uniform I) :
      Uniform (fun i (x : α i × ℕ) => x.2+1)).specialize i) n xs ≤
      1000*(xs.length+1)*(volume xs+n+xs.length+1) := by
  induction xs generalizing n with
  | nil => simp only [Realizer.foldTime,List.length_nil,volume_nil]; omega
  | cons a xs ih =>
    have hi := ih (n+1)
    have ht := Realizer.time_succ_le n
    rw [Realizer.foldTime]
    change (snd.comp (Realizer.succ.uniform I)).time i (a,n)+_+
      20*(volume (a::xs)+volume n+volume (n+1)+1) ≤ _
    simp only [time_comp,time_snd,time_uniform,volume_pair,volume_nat,volume_cons,List.length_cons,Function.comp_apply]
    nlinarith [volume_pos a,volume_pos xs]

theorem time_length_le (i : I) (xs : List (α i)) :
    length.time i xs ≤ 100000*(xs.length+1)*(volume xs+1) := by
  have hf := foldTime_length_le i xs 0
  have hv := length_le_volume xs
  simp only [length,time_congr,time_comp,time_pair,time_id,time_zero,time_fold,volume_pair,volume_nat]
  nlinarith [volume_pos xs]

theorem volume_drop_le {i : I} (xs : List (α i)) (n : ℕ) : volume (xs.drop n) ≤ volume xs :=
  volume_sublist (List.drop_sublist _ _)

theorem time_drop_le (i : I) (xs : List (α i)) (n : ℕ) :
    drop.time i (xs,n) ≤ 1000000*(n+1)*(volume xs+n+1) := by
  have he : ∀ j (ys : List (α i)), List.tail^[j] ys = ys.drop j := by
    intro j; induction j with
    | zero => intro ys; rfl
    | succ j ih => intro ys; rw [Function.iterate_succ_apply,ih,List.drop_tail]
  have h := time_iterate_le (tail : Uniform (fun i (xs : List (α i)) => xs.tail)) i n xs
    (volume xs+2) (volume xs)
    (fun j _ => by rw [he,time_tail]; exact Nat.add_le_add_right (volume_drop_le xs j) _)
    (fun j _ => by rw [he]; exact volume_drop_le xs j)
  simp only [drop,time_congr,time_comp,swap,time_pair,time_fst,time_snd,volume_pair,volume_nat]
  nlinarith [volume_pos xs]

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

namespace Poly
variable {I : Type u6} {s n f : I → ℕ} {d : ℕ}

theorem volumeUnit (s : I → ℕ) (b : I → Unit) : Poly s (fun i => volume (b i)) 0 := by
  have h : (fun i => volume (b i)) = fun _ => 1 := by funext i; cases b i; rfl
  rw [h]; exact const s 1

theorem volumeUniverse (hn : Poly s n d) (v : ∀ i, Universe (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_universe_le (v i))
  (have polyH0 := Poly.const (s) (3); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem volumeCardinal (hn : Poly s n d) (v : ∀ i, Cardinal (n i)) :
    Poly s (fun i => volume (v i)) d := by
  simp only [volume_cardinal]
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hn); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega))

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

variable {α : J → Type u8} {β : J → Type u9} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem lengthVolume (xs : ∀ j, List (α j)) (h : Poly s (fun j => volume (xs j)) d) :
    Poly s (fun j => (xs j).length) d := of_le (fun j => length_le_volume (xs j)) h

end Poly
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u10} {s n : J → ℕ} {d : ℕ}

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u12} {J : Type u13} {α : I → Type u14} {β : I → Type u15} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u16} {s n : J → ℕ} {d v : ℕ}

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u18} {J : Type u19} {s : J → ℕ}
variable {α : I → Type u20} {β : I → Type u21} {γ : I → Type u22} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

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

variable {α : J → Type u2} {β : J → Type u3} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

theorem volumeSnd (p : ∀ j, α j × β j) (h : Poly s (fun j => volume (p j)) d) :
    Poly s (fun j => volume (p j).2) d := of_le (fun j => by rw [volume_prod]; omega) h

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

theorem lengthTail (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => (xs j).tail.length) d :=
  of_le (fun j => by simp only [List.length_tail]; omega) h

theorem lengthTake (k : J → ℕ) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).take (k j)).length) d :=
  of_le (fun j => (List.take_sublist (k j) (xs j)).length_le) h

theorem lengthDrop (k : J → ℕ) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).drop (k j)).length) d :=
  of_le (fun j => (List.drop_sublist (k j) (xs j)).length_le) h

theorem lengthReverse (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => (xs j).reverse.length) d := by simpa only [List.length_reverse] using h

theorem lengthReplicate (k : J → ℕ) (a : ∀ j, α j) (h : Poly s k d) :
    Poly s (fun j => (List.replicate (k j) (a j)).length) d := by simpa only [List.length_replicate] using h
end ThreeMachine.StackCompiler.Poly
end

end OAI
end

section
-- module StateBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.Algorithm

end ThreeMachine.Algorithm

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

theorem blockSmall_of_good {n : ℕ} {r : Fin n → Fin n → Prop} {W : Finset (Fin n)}
    {b : Algorithm.Block (Fin n)} (hg : b.Valid r W) (hb : b.Bounded) : BlockSmall b :=
  ⟨hg.length_le,fun v => (hb v).trans hg.length_le⟩

theorem layers_small {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]
    (fs zs : List (Finset (Fin n))) (k : ℕ) : TableSmall (Algorithm.layers r fs zs k) :=
  fun W b h => blockSmall_of_good (Algorithm.layers_good r fs zs k W b h)
    (Algorithm.layers_bounded r fs zs k W b h)

namespace Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

namespace Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace Uniform
variable {I : Type u1} {α : I → Type u2} [∀ i, Coding (α i)]
theorem time_append_le (i : I) (xs ys : List (α i)) :
    append.time i (xs,ys) ≤ 100000*(xs.length+1)*(volume xs+volume ys+1) := by
  have h := time_consFold i xs.reverse ys
  have hr := time_reverse i xs
  simp only [List.length_reverse,volume_reverse] at h
  simp only [append,time_congr,time_comp,time_pair,time_fst,time_snd,volume_prod,Function.comp_apply,volume_reverse]
  nlinarith [volume_pos xs,volume_pos ys]
end Uniform
namespace Realizer
variable {α : Type u3} [Coding α]
theorem time_zero (x : α) : (zero : Realizer (fun _ : α => (0 : ℕ))).time x = 2 := rfl

theorem time_cons (x : α × List α) : cons.time x = volume x+2 := rfl
theorem time_reverse_le (xs : List α) :
    reverse.time xs ≤ 200*(xs.length+1)*(volume xs+1) :=
  Uniform.time_reverse (I := Unit) (α := fun _ => α) () xs

theorem volume_range_le (n : ℕ) : volume (List.range n) ≤ 10*(n+1)^2 := by
  have h := volume_list_le (List.range n) (2*n+1) (by
    intro a ha
    rw [volume_nat]
    have := List.mem_range.mp ha
    omega)
  simp only [List.length_range] at h
  nlinarith

theorem time_rangeStep_le (j n : ℕ) (hj : j ≤ n) :
    rangeStep.time (j,(List.range j).reverse) ≤ 100000*(n+1)^2 := by
  have hv := volume_range_le j
  have ht := time_succ_le j
  simp only [rangeStep,time_pair,time_comp,time_fst,time_cons,volume_prod,volume_nat,
    Function.comp_apply,volume_cons,volume_nat,volume_reverse]
  nlinarith

theorem time_range_le (n : ℕ) : range.time n ≤ 100000000000*(n+1)^3 := by
  have ht := time_iterate_le rangeStep n (0,[]) (100000*(n+1)^2) (20*(n+1)^2)
    (fun j hj => by rw [rangeStep_iterate]; exact time_rangeStep_le j n (by omega))
    (fun j hj => by
      rw [rangeStep_iterate,volume_prod,volume_nat,volume_reverse]
      have := volume_range_le j
      nlinarith)
  have hr := time_reverse_le (List.range n).reverse
  have hv := volume_range_le n
  simp only [List.length_reverse,List.length_range,volume_reverse] at hr
  simp only [range,time_congr,time_comp,time_pair,time_id,time_zero,time_snd,
    Function.comp_apply,rangeStep_iterate,volume_prod,volume_nat,volume_nil,volume_reverse,id_eq]
  have hz : (nil : Realizer (fun _ : ℕ => ([] : List ℕ))).time n = 2 := rfl
  rw [hz]
  nlinarith
end Realizer
namespace Uniform
variable {I : Type u4} {α : I → Type u5} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u6} {J : Type u7} {s : J → ℕ} {α : I → Type u8} [∀ i, Coding (α i)]

theorem iterateTime {f : ∀ i, α i → α i} (R : Uniform f)
    (idx : J → I) (m : J → ℕ) (a : ∀ j, α (idx j)) {l t v : ℕ}
    (hm : Poly s m l)
    (ht : Poly (fun p : IterPool m => s p.1)
      (fun p => R.time (idx p.1) ((f (idx p.1))^[p.2.1] (a p.1))) t)
    (hv : Poly (fun p : IterPool m => s p.1)
      (fun p => volume ((f (idx p.1))^[p.2.1] (a p.1))) v) :
    Poly s (fun j => R.iterate.time (idx j) (m j,a j)) (l+Max.max t (Max.max v l)) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_iterate_le R (idx j) (m j) (a j)
    (C*(s j+2)^t) (D*(s j+2)^v)
    (fun k hk => hC ⟨j,⟨k,by omega⟩⟩) (fun k hk => hD ⟨j,⟨k,by omega⟩⟩))
  (have polyH0 := Poly.const (s) (10000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hm) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hV); have polyH5 := Poly.add polyH4 (hm); have polyH6 := Poly.add polyH5 polyH1; have polyH7 := Poly.mul polyH3 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))
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

end ThreeMachine.StackCompiler.Poly
end

end OAI
end

section
-- module ScheduleBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u1} {s n B : J → ℕ} {d e : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

theorem fullSolve_small {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]
    {b : Block (Fin n)} (h : Algorithm.fullSolve r = some b) : BlockSmall b := by
  exact layers_small r _ _ _ _ _ (Algorithm.lookup_mem h)

theorem scheduleMatrix_bound {n T : ℕ} (M : Matrix n) {t : Fin n → ℕ}
    (h : scheduleMatrix M T = some t) (v : Fin n) : t v ≤ 3*T := by
  simp only [scheduleMatrix] at h
  split_ifs at h with hn
  · obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp h
    exact (fullSolve_small _ hb).2 _

theorem bestMatrix_bound {n k : ℕ} (M : Matrix n) {a : ℕ × (Fin n → ℕ)}
    (h : bestMatrix M k = some a) : a.1 ≤ k ∧ ∀ v, a.2 v ≤ 3*k := by
  induction k with
  | zero => simp only [bestMatrix] at h; contradiction
  | succ k ih =>
    simp only [bestMatrix] at h
    cases he : bestMatrix M k with
    | some b =>
      simp only [he,Option.some.injEq] at h
      subst a
      have hi := ih he
      exact ⟨by omega,fun v => by have := hi.2 v; omega⟩
    | none =>
      rw [he] at h
      obtain ⟨t,ht,ha⟩ := Option.map_eq_some_iff.mp h
      cases ha
      exact ⟨le_rfl,fun v => scheduleMatrix_bound M ht v⟩

theorem answerMatrix_length {n : ℕ} (M : Matrix n) (d : Option ℕ) :
    ((answerMatrix M d).getD []).length ≤ n := by
  cases d with
  | none =>
    simp only [answerMatrix]
    cases bestMatrix M n <;> simp only [Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.length_nil,List.length_ofFn,Nat.zero_le,le_refl]
  | some T =>
    simp only [answerMatrix]
    cases scheduleMatrix M T <;> simp only [Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,List.length_nil,List.length_ofFn,Nat.zero_le,le_refl]

theorem answerMatrix_bound {n : ℕ} (M : Matrix n) (d : Option ℕ) {a : ℕ}
    (h : a ∈ (answerMatrix M d).getD []) : a ≤ 3*(n+d.getD 0) := by
  cases d with
  | none =>
    simp only [answerMatrix,Option.getD_none] at h ⊢
    cases he : bestMatrix M n with
    | none => simp only [he,Option.map_none,Option.getD_none,List.not_mem_nil] at h
    | some b =>
      simp only [he,Option.map_some,Option.getD_some,List.mem_ofFn] at h
      obtain ⟨v,rfl⟩ := h
      have hb := (bestMatrix_bound M he).2 v
      omega
  | some T =>
    simp only [answerMatrix,Option.getD_some] at h ⊢
    cases he : scheduleMatrix M T with
    | none => simp only [he,Option.map_none,Option.getD_none,List.not_mem_nil] at h
    | some t =>
      simp only [he,Option.map_some,Option.getD_some,List.mem_ofFn] at h
      obtain ⟨v,rfl⟩ := h
      have ht := scheduleMatrix_bound M he v
      omega

namespace Poly
variable {J : Type} (s n T : J → ℕ) (M : ∀ j, Matrix (n j))

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Realizer

end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u2}

theorem time_makeUniverse (n : ℕ) (x : Cardinal n) :
    makeUniverse.time n x = Realizer.range.time n := rfl

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n m : J → ℕ} {d e : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
noncomputable section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
end

end

end OAI
end

section
-- module OptimumCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → Option (β i)} {g : ∀ i, α i → γ i}

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u5} {J : Type u6} {s : J → ℕ} {α : I → Type u7} {β : I → Type u8} {γ : I → Type u9}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}
variable (R : Uniform f) (S : Uniform g) (idx : J → I) (x : ∀ j, α (idx j)) {d : ℕ}

theorem compTimeSame (hR : Poly s (fun j => R.time (idx j) (x j)) d)
    (hS : Poly s (fun j => S.time (idx j) (f (idx j) (x j))) d)
    (hV : Poly s (fun j => volume (f (idx j) (x j))) d) :
    Poly s (fun j => (R.comp S).time (idx j) (x j)) d := by
  simp only [Uniform.time_comp]
  have h := hV.add (const s 1)
  have ht := (const s 10).mul h
  simpa only [Nat.zero_add,Nat.max_zero,Nat.max_self] using (hR.add hS).add ht

variable {g' : ∀ i, α i → γ i}
theorem pairTimeSame (S : Uniform g') (hR : Poly s (fun j => R.time (idx j) (x j)) d)
    (hS : Poly s (fun j => S.time (idx j) (x j)) d)
    (hX : Poly s (fun j => volume (x j)) d)
    (hF : Poly s (fun j => volume (f (idx j) (x j))) d)
    (hG : Poly s (fun j => volume (g' (idx j) (x j))) d) :
    Poly s (fun j => (R.pair S).time (idx j) (x j)) d := by
  simp only [Uniform.time_pair]
  have h := ((hX.add hF).add hG).add (const s 1)
  have ht := (const s 20).mul h
  simpa only [Nat.zero_add,Nat.max_zero,Nat.max_self] using (hR.add hS).add ht
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u10} {J : Type u11} {s : J → ℕ} {α : I → Type u12} [∀ i, Coding (α i)]

theorem iterateTimeStrict {f : ∀ i, α i → α i} (R : Uniform f)
    (idx : J → I) (m : J → ℕ) (a : ∀ j, α (idx j)) {l t v : ℕ}
    (hm : Poly s m l)
    (ht : Poly (fun p : StrictIterPool m => s p.1)
      (fun p => R.time (idx p.1) ((f (idx p.1))^[p.2.1] (a p.1))) t)
    (hv : Poly (fun p : IterPool m => s p.1)
      (fun p => volume ((f (idx p.1))^[p.2.1] (a p.1))) v) :
    Poly s (fun j => R.iterate.time (idx j) (m j,a j)) (l+Max.max t (Max.max v l)) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_iterate_le R (idx j) (m j) (a j)
    (C*(s j+2)^t) (D*(s j+2)^v)
    (fun k hk => hC ⟨j,⟨k,hk⟩⟩) (fun k hk => hD ⟨j,⟨k,by omega⟩⟩))
  (have polyH0 := Poly.const (s) (10000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hm) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hV); have polyH5 := Poly.add polyH4 (hm); have polyH6 := Poly.add polyH5 polyH1; have polyH7 := Poly.mul polyH3 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module OutputCosts
namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler

end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

namespace Poly
variable {J : Type} {s n : J → ℕ} {d e : ℕ}
theorem volumeInstance (G : ∀ j, Instance (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (G j).edges.length) e) : Poly s (fun j => volume (G j)) (e+d) := by
  simp only [volume_instance]
  apply volumeList hl (show Poly s (fun j => 4*n j+3) d from by (have polyH0 := Poly.const (s) (4); have polyH1 := Poly.mul polyH0 (hn); have polyH2 := Poly.const (s) (3); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega)))
  intro j a _ha
  rw [volume_prod,volume_fin,volume_fin]
  have := a.1.isLt; have := a.2.isLt
  omega
end Poly
namespace Costs

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module BinaryCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1}
theorem time_binaryValueStep_le (i : I) (x : Bool × ℕ) :
    (binaryValueStep (I := I)).time i x ≤ Costs.valueStepC*(x.2+2)^2 := by
  change (binaryValueStep (I := Unit)).time () x ≤ _
  exact Classical.choose_spec Costs.valueStepCost x
theorem time_binaryLeadingStep_le (i : I) (x : Bool × (Bool × ℕ)) :
    (binaryLeadingStep (I := I)).time i x ≤ Costs.leadingStepC*(x.2.2+2) := by
  change (binaryLeadingStep (I := Unit)).time () x ≤ _
  simpa only [Costs.leadingStepC,pow_one] using Classical.choose_spec Costs.leadingStepCost x
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Realizer
variable {α : Type u2} {β : Type u3} [Coding α] [Coding β] {f : α × β → β}
theorem foldTime_prefix_le (R : Realizer f) (xs : List α) (b : β) (T V : ℕ)
    (hvol : ∀ ys zs, xs = ys ++ zs → volume (ys.foldl (fun b a => f (a,b)) b) ≤ V)
    (htime : ∀ ys a zs, xs = ys ++ a :: zs → R.time (a,ys.foldl (fun b a => f (a,b)) b) ≤ T) :
    foldTime R b xs ≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
  induction xs generalizing b with
  | nil => simp only [foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have hi := ih (f (a,b))
      (fun ys zs he => by
        have h := hvol (a::ys) zs (by simpa using congrArg (List.cons a) he)
        simpa only [List.foldl_cons] using h)
      (fun ys c zs he => by
        have h := htime (a::ys) c zs (by simpa using congrArg (List.cons a) he)
        simpa only [List.foldl_cons] using h)
    have ht : R.time (a,b) ≤ T := htime [] a xs rfl
    have hb : volume b ≤ V := hvol [] (a::xs) rfl
    have hc : volume (f (a,b)) ≤ V := hvol [a] xs rfl
    simp only [foldTime,volume_cons,List.length_cons] at hi ⊢
    nlinarith [volume_pos a,volume_pos xs]
end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u4} {α : I → Type u5} {β : I → Type u6} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
variable {f : ∀ i, α i × β i → β i}
theorem time_fold_prefix_le (R : Uniform f) (i : I) (xs : List (α i)) (b : β i) (T V : ℕ)
    (hvol : ∀ ys zs, xs = ys ++ zs → volume (ys.foldl (fun b a => f i (a,b)) b) ≤ V)
    (htime : ∀ ys a zs, xs = ys ++ a :: zs → R.time i (a,ys.foldl (fun b a => f i (a,b)) b) ≤ T) :
    R.fold.time i (xs,b) ≤ 50*(xs.length+1)*(T+volume xs+V+1) := by
  have h := Realizer.foldTime_prefix_le (R.specialize i) xs b T V hvol htime
  rw [time_fold]
  simp only [volume_pair]
  have hv : volume b ≤ V := hvol [] xs rfl
  nlinarith [volume_pos xs]
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Binary

theorem valueStep_fold_ge (bs : List Bool) (n : ℕ) :
    n ≤ bs.foldl (fun n b => valueStep (b,n)) n := by
  induction bs generalizing n with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldl_cons]
    exact le_trans (by unfold valueStep; omega) (ih _)

theorem value_prefix_le (bs ys zs : List Bool) (h : bs.reverse = ys ++ zs) :
    ys.foldl (fun n b => valueStep (b,n)) 0 ≤ value bs := by
  rw [← value_fold,h,List.foldl_append]
  exact valueStep_fold_ge _ _

theorem leading_le (bs : List Bool) : leading bs ≤ bs.length :=
  (List.takeWhile_sublist id).length_le

end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler

theorem volume_boolList_le (bs : List Bool) : volume bs ≤ 4*bs.length+1 := by
  have h := volume_list_le bs 3 (fun a _ => volume_bool a)
  omega
namespace Uniform
variable {I : Type u7}

theorem time_binaryValueFold_le (i : I) (bs : List Bool) :
    binaryValueStep.fold.time i (bs.reverse,0) ≤
      50*(bs.length+1)*(Costs.valueStepC*(Binary.value bs+2)^2 + volume bs+2*Binary.value bs+2) := by
  have hv : ∀ ys zs, bs.reverse = ys ++ zs →
      volume (ys.foldl (fun n b => Binary.valueStep (b,n)) 0) ≤ 2*Binary.value bs+1 := by
    intro ys zs h; rw [volume_nat]; have := Binary.value_prefix_le bs ys zs h; omega
  have ht : ∀ ys a zs, bs.reverse = ys ++ a::zs →
      binaryValueStep.time i (a,ys.foldl (fun n b => Binary.valueStep (b,n)) 0) ≤
        Costs.valueStepC*(Binary.value bs+2)^2 := by
    intro ys a zs h
    exact (time_binaryValueStep_le i _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by have := Binary.value_prefix_le bs ys (a::zs) h; omega) _))
  have h := time_fold_prefix_le binaryValueStep i bs.reverse 0 _ _ hv ht
  simpa only [List.length_reverse,volume_reverse, Nat.add_assoc] using h

theorem time_binaryLeadingFold_le (i : I) (bs : List Bool) :
    binaryLeadingStep.fold.time i (bs,(true,0)) ≤
      50*(bs.length+1)*(Costs.leadingStepC*(bs.length+2) + volume bs+2*bs.length+6) := by
  have hb : ∀ ys zs, bs = ys ++ zs →
      (ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)).2 ≤ bs.length := by
    intro ys zs h
    rw [Binary.leading_fold]; simp only [ite_true,Nat.zero_add]
    have hL := Binary.leading_le ys
    rw [h,List.length_append]; omega
  have hv : ∀ ys zs, bs = ys ++ zs →
      volume (ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)) ≤ 2*bs.length+5 := by
    intro ys zs h
    rw [volume_prod,volume_nat]
    have := volume_bool (ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)).1
    have := hb ys zs h; omega
  have ht : ∀ ys a zs, bs = ys ++ a::zs →
      binaryLeadingStep.time i (a,ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)) ≤
        Costs.leadingStepC*(bs.length+2) := by
    intro ys a zs h
    exact (time_binaryLeadingStep_le i _).trans (Nat.mul_le_mul_left _ (by dsimp only; have := hb ys (a::zs) h; omega))
  have h := time_fold_prefix_le binaryLeadingStep i bs (true,0) _ _ hv ht
  simpa only [Nat.add_assoc] using h
end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u10}
theorem time_binaryTakeStep_le (i : I) (x : List Bool × List Bool) :
    (takeStep (I := I) (α := fun _ => Bool)).time i x ≤ Costs.takeStepC I*(x.1.length+x.2.length+2) := by
  simpa only [Costs.takeStepC,pow_one] using Classical.choose_spec (Costs.takeStepCost I) ⟨i,x⟩
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u11}

theorem time_binaryTakeIter_le (i : I) (bs : List Bool) (k : ℕ) :
    (takeStep (α := fun _ : I => Bool)).iterate.time i (k,(bs,[])) ≤
      10000*(k+1)*(Costs.takeStepC I*(2*bs.length+2)+(8*bs.length+3)+k+1) := by
  apply time_iterate_le
  · intro j hj
    rw [Binary.takeStep_iterate]
    apply (time_binaryTakeStep_le i _).trans
    apply Nat.mul_le_mul_left
    simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero]
    have h₁ := (List.drop_sublist j bs).length_le
    have h₂ := (List.take_sublist j bs).length_le
    omega
  · intro j hj
    rw [Binary.takeStep_iterate,volume_pair]
    have h₁ := volume_boolList_le (bs.drop j)
    have h₂ := volume_boolList_le ((bs.take j).reverse ++ [])
    simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] at h₂
    have h₃ := (List.drop_sublist j bs).length_le
    have h₄ := (List.take_sublist j bs).length_le
    omega
end Uniform
namespace Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I) (bs : J → List Bool)

theorem binaryValue (hl : Poly s (fun j => (bs j).length) 1)
    (hv : Poly s (fun j => Binary.value (bs j)) 1) :
    Poly s (fun j => (Uniform.binaryValue (I := I)).time (idx j) (bs j)) 3 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (j_1 : J) => bs j_1) (hl) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hfold : Poly s (fun j => (Uniform.binaryValueStep (I := I)).fold.time (idx j) ((bs j).reverse,0)) 3 := by
    apply Poly.of_le (fun j => Uniform.time_binaryValueFold_le (idx j) (bs j))
    (have polyH0 := Poly.const (s) (50); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.const (s) (Costs.valueStepC); have polyH5 := Poly.const (s) (2); have polyH6 := Poly.add (hv) polyH5; have polyH7 := Poly.pow polyH6 (2); have polyH8 := Poly.mul polyH4 polyH7; have polyH9 := Poly.add polyH8 (hb); have polyH10 := Poly.mul polyH5 (hv); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.add polyH11 polyH5; have polyH13 := Poly.mul polyH3 polyH12; exact Poly.lift polyH13 (by first | decide +kernel | omega))
  (have polyH0 := Poly.const (s) (200); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hb) polyH1; have polyH5 := Poly.mul polyH3 polyH4; have polyH6 := Poly.of_le (fun (j_11 : J) => (@Uniform.time_reverse (I) (fun (i : I) => Bool) _ (idx j_11) (bs j_11))) polyH5; have polyH7 := Poly.const (s) (2); have polyH8 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_zero (I) (fun (i : I) => List Bool) _ (idx j_11) (bs j_11)))) polyH7; have polyH9 := Poly.add polyH6 polyH8; have polyH10 := Poly.const (s) (20); have polyH11 := Poly.lengthReverse (fun (j_1 : J) => bs j_1) (hl); have polyH12 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.reverse (bs j_1)) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.reverse (bs j_1)) => (Sigma.snd q).1); have polyH13 := Poly.listVolume (fun (j_1 : J) => List.reverse (bs j_1)) polyH11 polyH12; have polyH14 := Poly.add (hb) polyH13; have polyH15 := Poly.const (s) (volume (0)); have polyH16 := Poly.add polyH14 polyH15; have polyH17 := Poly.add polyH16 polyH1; have polyH18 := Poly.mul polyH10 polyH17; have polyH19 := Poly.add polyH9 polyH18; have polyH20 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (xs : List Bool) => List.reverse xs) (fun (i : I) (x : List Bool) => 0) (@Uniform.reverse I (fun (i : I) => Bool) _) (@Uniform.zero I (fun (i : I) => List Bool) _) (idx j_11) (bs j_11)))) polyH19; have polyH21 := Poly.add polyH20 (hfold); have polyH22 := Poly.const (s) (10); have polyH23 := Poly.const (s) (0); have polyH24 := Poly.volumeNat polyH23; have polyH25 := Poly.volumeProd (fun (j_1 : J) => (List.reverse (bs j_1), 0)) polyH13 polyH24; have polyH26 := Poly.add polyH25 polyH1; have polyH27 := Poly.mul polyH22 polyH26; have polyH28 := Poly.add polyH21 polyH27; have polyH29 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => (List.reverse x, 0)) (fun (i : I) (x : List Bool × ℕ) => List.foldl (fun (b : ℕ) (a : Bool) => Binary.valueStep (a, b)) (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (xs : List Bool) => List.reverse xs) (fun (i : I) (x : List Bool) => 0) (@Uniform.reverse I (fun (i : I) => Bool) _) (@Uniform.zero I (fun (i : I) => List Bool) _)) (@Uniform.fold I (fun (i : I) => Bool) (fun (x : I) => ℕ) _ _ (fun (x : I) => Binary.valueStep) (@Uniform.binaryValueStep I)) (idx j_11) (bs j_11)))) polyH28; exact Poly.lift polyH29 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryLeading (hl : Poly s (fun j => (bs j).length) 1) :
    Poly s (fun j => (Uniform.binaryLeading (I := I)).time (idx j) (bs j)) 2 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (j_1 : J) => bs j_1) (hl) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hfold : Poly s (fun j => (Uniform.binaryLeadingStep (I := I)).fold.time (idx j) (bs j,(true,0))) 2 := by
    apply Poly.of_le (fun j => Uniform.time_binaryLeadingFold_le (idx j) (bs j))
    (have polyH0 := Poly.const (s) (50); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.const (s) (Costs.leadingStepC); have polyH5 := Poly.const (s) (2); have polyH6 := Poly.add (hl) polyH5; have polyH7 := Poly.mul polyH4 polyH6; have polyH8 := Poly.add polyH7 (hb); have polyH9 := Poly.mul polyH5 (hl); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.const (s) (6); have polyH12 := Poly.add polyH10 polyH11; have polyH13 := Poly.mul polyH3 polyH12; exact Poly.lift polyH13 (by first | decide +kernel | omega))
  have hfv : Poly s (fun j => ((bs j).foldl (fun s a => Binary.leadingStep (a,s)) (true,0)).2) 1 := by
    simp only [Binary.leading_fold,ite_true,Nat.zero_add]
    exact Poly.of_le (fun j => Binary.leading_le (bs j)) hl
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (hb) polyH0; have polyH2 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_id (I) (fun (i : I) => List Bool) _ (idx j_11) (bs j_11)))) polyH1; have polyH3 := Poly.const (s) (2 * volume Bool.true + 1); have polyH4 := Poly.const (s) (20); have polyH5 := Poly.mul polyH4 (hb); have polyH6 := Poly.const (s) (50 * volume Bool.true); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.const (s) (50); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.mul polyH3 polyH9; have polyH11 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_constant (I) (fun (i : I) => List Bool) _ (Bool) _ (Bool.true) (idx j_11) (bs j_11)))) polyH10; have polyH12 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_zero (I) (fun (i : I) => List Bool) _ (idx j_11) (bs j_11)))) polyH0; have polyH13 := Poly.add polyH11 polyH12; have polyH14 := Poly.const (s) (volume Bool.true); have polyH15 := Poly.add (hb) polyH14; have polyH16 := Poly.const (s) (volume (0)); have polyH17 := Poly.add polyH15 polyH16; have polyH18 := Poly.const (s) (1); have polyH19 := Poly.add polyH17 polyH18; have polyH20 := Poly.mul polyH4 polyH19; have polyH21 := Poly.add polyH13 polyH20; have polyH22 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List Bool) (fun (i : I) => Bool) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (i : I) (x : List Bool) => 0) (@Uniform.constant I (fun (i : I) => List Bool) _ Bool _ Bool.true) (@Uniform.zero I (fun (i : I) => List Bool) _) (idx j_11) (bs j_11)))) polyH21; have polyH23 := Poly.add polyH2 polyH22; have polyH24 := Poly.add (hb) (hb); have polyH25 := Poly.const (s) (volume (Bool.true, 0)); have polyH26 := Poly.add polyH24 polyH25; have polyH27 := Poly.add polyH26 polyH18; have polyH28 := Poly.mul polyH4 polyH27; have polyH29 := Poly.add polyH23 polyH28; have polyH30 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (i : I) => Bool × ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (Bool.true, 0)) (@Uniform.id I (fun (i : I) => List Bool) _) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => Bool) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (i : I) (x : List Bool) => 0) (@Uniform.constant I (fun (i : I) => List Bool) _ Bool _ Bool.true) (@Uniform.zero I (fun (i : I) => List Bool) _)) (idx j_11) (bs j_11)))) polyH29; have polyH31 := Poly.add polyH30 (hfold); have polyH32 := Poly.const (s) (10); have polyH33 := Poly.const (s) (volume (Prod.fst (Bool.true, 0))); have polyH34 := Poly.const (s) (volume (Prod.snd (Bool.true, 0))); have polyH35 := Poly.volumeProd (fun (j_1 : J) => (Bool.true, 0)) polyH33 polyH34; have polyH36 := Poly.volumeProd (fun (j_1 : J) => (bs j_1, Bool.true, 0)) (hb) polyH35; have polyH37 := Poly.add polyH36 polyH18; have polyH38 := Poly.mul polyH32 polyH37; have polyH39 := Poly.add polyH31 polyH38; have polyH40 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (i : I) => List Bool × Bool × ℕ) (fun (x : I) => Bool × ℕ) _ _ _ (fun (i : I) (x : List Bool) => (x, Bool.true, 0)) (fun (i : I) (x : List Bool × Bool × ℕ) => List.foldl (fun (b : Bool × ℕ) (a : Bool) => Binary.leadingStep (a, b)) (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (i : I) => Bool × ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (Bool.true, 0)) (@Uniform.id I (fun (i : I) => List Bool) _) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => Bool) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (i : I) (x : List Bool) => 0) (@Uniform.constant I (fun (i : I) => List Bool) _ Bool _ Bool.true) (@Uniform.zero I (fun (i : I) => List Bool) _))) (@Uniform.fold I (fun (i : I) => Bool) (fun (x : I) => Bool × ℕ) _ _ (fun (x : I) => Binary.leadingStep) (@Uniform.binaryLeadingStep I)) (idx j_11) (bs j_11)))) polyH39; have polyH41 := Poly.volumeBool (s) (fun (j_1 : J) => (List.foldl (fun (b : Bool × ℕ) (a : Bool) => Binary.leadingStep (a, b)) (Prod.snd ((fun (x : List Bool) => (x, Bool.true, 0)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (x, Bool.true, 0)) (bs j_1)))).1); have polyH42 := Poly.volumeNat (hfv); have polyH43 := Poly.volumeProd (fun (j_1 : J) => List.foldl (fun (b : Bool × ℕ) (a : Bool) => Binary.leadingStep (a, b)) (Prod.snd ((fun (x : List Bool) => (x, Bool.true, 0)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (x, Bool.true, 0)) (bs j_1)))) polyH41 polyH42; have polyH44 := Poly.add polyH43 polyH0; have polyH45 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => Bool) (fun (i : I) => ℕ) _ _ (idx j_11) ((fun (x : List Bool × Bool × ℕ) => List.foldl (fun (b : Bool × ℕ) (a : Bool) => Binary.leadingStep (a, b)) (Prod.snd x) (Prod.fst x)) ((fun (x : List Bool) => (x, Bool.true, 0)) (bs j_11)))))) polyH44; have polyH46 := Poly.add polyH40 polyH45; have polyH47 := Poly.add polyH43 polyH18; have polyH48 := Poly.mul polyH32 polyH47; have polyH49 := Poly.add polyH46 polyH48; have polyH50 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (x : I) => Bool × ℕ) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => (fun (x_1 : List Bool × Bool × ℕ) => List.foldl (fun (b : Bool × ℕ) (a : Bool) => Binary.leadingStep (a, b)) (Prod.snd x_1) (Prod.fst x_1)) ((fun (x_1 : List Bool) => (x_1, Bool.true, 0)) x)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool × Bool × ℕ) (fun (x : I) => Bool × ℕ) _ _ _ (fun (i : I) (x : List Bool) => (x, Bool.true, 0)) (fun (i : I) (x : List Bool × Bool × ℕ) => List.foldl (fun (b : Bool × ℕ) (a : Bool) => Binary.leadingStep (a, b)) (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (i : I) => Bool × ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (Bool.true, 0)) (@Uniform.id I (fun (i : I) => List Bool) _) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => Bool) (fun (i : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (i : I) (x : List Bool) => 0) (@Uniform.constant I (fun (i : I) => List Bool) _ Bool _ Bool.true) (@Uniform.zero I (fun (i : I) => List Bool) _))) (@Uniform.fold I (fun (i : I) => Bool) (fun (x : I) => Bool × ℕ) _ _ (fun (x : I) => Binary.leadingStep) (@Uniform.binaryLeadingStep I))) (@Uniform.snd I (fun (i : I) => Bool) (fun (i : I) => ℕ) _ _) (idx j_11) (bs j_11)))) polyH49; exact Poly.lift polyH50 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryTake (k : J → ℕ) (hl : Poly s (fun j => (bs j).length) 1) (hk : Poly s k 1) :
    Poly s (fun j => (Uniform.take (I := I) (α := fun _ => Bool)).time (idx j) (bs j,k j)) 2 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (j_1 : J) => bs j_1) (hl) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hIter : Poly s (fun j => (Uniform.takeStep (I := I) (α := fun _ => Bool)).iterate.time
      (idx j) (k j,(bs j,[]))) 2 := by
    apply Poly.of_le (fun j => Uniform.time_binaryTakeIter_le (idx j) (bs j) (k j))
    (have polyH0 := Poly.const (s) (10000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hk) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.const (s) (Costs.takeStepC I); have polyH5 := Poly.const (s) (2); have polyH6 := Poly.mul polyH5 (hl); have polyH7 := Poly.add polyH6 polyH5; have polyH8 := Poly.mul polyH4 polyH7; have polyH9 := Poly.const (s) (8); have polyH10 := Poly.mul polyH9 (hl); have polyH11 := Poly.const (s) (3); have polyH12 := Poly.add polyH10 polyH11; have polyH13 := Poly.add polyH8 polyH12; have polyH14 := Poly.add polyH13 (hk); have polyH15 := Poly.add polyH14 polyH1; have polyH16 := Poly.mul polyH3 polyH15; exact Poly.lift polyH16 (by first | decide +kernel | omega))
  have htake : Poly s (fun j => volume ((bs j).take (k j))) 1 :=
    Poly.of_le (fun j => volume_sublist (List.take_sublist _ _)) hb
  have hout : Poly s (fun j => volume (Binary.takeStep^[k j] (bs j,[]))) 1 := by
    simp only [Binary.takeStep_iterate,List.append_nil]
    (have polyH0 := Poly.lengthDrop (fun (j_1 : J) => k j_1) (fun (j_1 : J) => bs j_1) (hl); have polyH1 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (k j_1) (bs j_1)) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (k j_1) (bs j_1)) => (Sigma.snd q).1); have polyH2 := Poly.listVolume (fun (j_1 : J) => List.drop (k j_1) (bs j_1)) polyH0 polyH1; have polyH3 := Poly.lengthTake (fun (j_1 : J) => k j_1) (fun (j_1 : J) => bs j_1) (hl); have polyH4 := Poly.lengthReverse (fun (j_1 : J) => List.take (k j_1) (bs j_1)) polyH3; have polyH5 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.reverse (List.take (k j_1) (bs j_1))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.reverse (List.take (k j_1) (bs j_1))) => (Sigma.snd q).1); have polyH6 := Poly.listVolume (fun (j_1 : J) => List.reverse (List.take (k j_1) (bs j_1))) polyH4 polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (List.drop (k j_1) (bs j_1), List.reverse (List.take (k j_1) (bs j_1)))) polyH2 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hlen : Poly s (fun j => (Binary.takeStep^[k j] (bs j,[])).2.length) 1 := by
    simp only [Binary.takeStep_iterate,List.append_nil,List.length_reverse]
    exact Poly.of_le (fun j => (List.take_sublist _ _).length_le) hl
  (have polyH0 := Poly.volumeNat (hk); have polyH1 := Poly.volumeProd (fun (j_1 : J) => (bs j_1, k j_1)) (hb) polyH0; have polyH2 := Poly.const (s) (2); have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _ (idx j_15) ((bs j_15, k j_15))))) polyH3; have polyH5 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_fst (I) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _ (idx j_15) ((bs j_15, k j_15))))) polyH3; have polyH6 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_nil (I) (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (x : I) => Bool) _ _ (idx j_15) ((bs j_15, k j_15))))) polyH2; have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.const (s) (20); have polyH9 := Poly.add polyH1 (hb); have polyH10 := Poly.const (s) (1); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.add polyH11 polyH10; have polyH13 := Poly.mul polyH8 polyH12; have polyH14 := Poly.add polyH7 polyH13; have polyH15 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => @List.nil ((fun (x_1 : I) => Bool) i)) (@Uniform.fst I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.nil I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (x : I) => Bool) _ _) (idx j_15) ((bs j_15, k j_15))))) polyH14; have polyH16 := Poly.add polyH4 polyH15; have polyH17 := Poly.add polyH1 polyH0; have polyH18 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (bs j_1, k j_1), @List.nil ((fun (x : I) => Bool) (idx j_1)))) (hb) polyH10; have polyH19 := Poly.add polyH17 polyH18; have polyH20 := Poly.add polyH19 polyH10; have polyH21 := Poly.mul polyH8 polyH20; have polyH22 := Poly.add polyH16 polyH21; have polyH23 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => (Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) i))) (@Uniform.snd I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.pair I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => @List.nil ((fun (x_1 : I) => Bool) i)) (@Uniform.fst I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.nil I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (x : I) => Bool) _ _)) (idx j_15) ((bs j_15, k j_15))))) polyH22; have polyH24 := Poly.add polyH23 (hIter); have polyH25 := Poly.const (s) (10); have polyH26 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (bs j_1, k j_1), Prod.fst (bs j_1, k j_1), @List.nil ((fun (x : I) => Bool) (idx j_1)))) polyH0 polyH18; have polyH27 := Poly.add polyH26 polyH10; have polyH28 := Poly.mul polyH25 polyH27; have polyH29 := Poly.add polyH24 polyH28; have polyH30 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => ℕ × List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => (Prod.snd x, Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) i))) (fun (i : I) (x : ℕ × List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) => Binary.takeStep^[Prod.fst x] (Prod.snd x)) (@Uniform.pair I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => (Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) i))) (@Uniform.snd I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.pair I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => @List.nil ((fun (x_1 : I) => Bool) i)) (@Uniform.fst I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.nil I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (x : I) => Bool) _ _))) (@Uniform.iterate I (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ (fun (i : I) => Binary.takeStep) (@Uniform.takeStep I (fun (x : I) => Bool) _)) (idx j_15) ((bs j_15, k j_15))))) polyH29; have polyH31 := Poly.add (hout) polyH2; have polyH32 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ (idx j_15) ((fun (x : ℕ × List ((fun (x : I) => Bool) (idx j_15)) × List ((fun (x : I) => Bool) (idx j_15))) => Binary.takeStep^[Prod.fst x] (Prod.snd x)) ((fun (x : List ((fun (x : I) => Bool) (idx j_15)) × ℕ) => (Prod.snd x, Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) (idx j_15)))) (bs j_15, k j_15)))))) polyH31; have polyH33 := Poly.const (s) (200); have polyH34 := Poly.add (hlen) polyH10; have polyH35 := Poly.mul polyH33 polyH34; have polyH36 := Poly.volumeSnd (fun (j_1 : J) => (fun (x : ℕ × List ((fun (x : I) => Bool) (idx j_1)) × List ((fun (x : I) => Bool) (idx j_1))) => Binary.takeStep^[Prod.fst x] (Prod.snd x)) ((fun (x : List ((fun (x : I) => Bool) (idx j_1)) × ℕ) => (Prod.snd x, Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) (idx j_1)))) (bs j_1, k j_1))) (hout); have polyH37 := Poly.add polyH36 polyH10; have polyH38 := Poly.mul polyH35 polyH37; have polyH39 := Poly.of_le (fun (j_15 : J) => (@Uniform.time_reverse (I) (fun (x : I) => Bool) _ (idx j_15) (Prod.snd ((fun (x : ℕ × List ((fun (x : I) => Bool) (idx j_15)) × List ((fun (x : I) => Bool) (idx j_15))) => Binary.takeStep^[Prod.fst x] (Prod.snd x)) ((fun (x : List ((fun (x : I) => Bool) (idx j_15)) × ℕ) => (Prod.snd x, Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) (idx j_15)))) (bs j_15, k j_15)))))) polyH38; have polyH40 := Poly.add polyH32 polyH39; have polyH41 := Poly.mul polyH25 polyH37; have polyH42 := Poly.add polyH40 polyH41; have polyH43 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) (xs : List ((fun (x : I) => Bool) i)) => List.reverse xs) (@Uniform.snd I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _) (@Uniform.reverse I (fun (x : I) => Bool) _) (idx j_15) ((fun (x : ℕ × List ((fun (x : I) => Bool) (idx j_15)) × List ((fun (x : I) => Bool) (idx j_15))) => Binary.takeStep^[Prod.fst x] (Prod.snd x)) ((fun (x : List ((fun (x : I) => Bool) (idx j_15)) × ℕ) => (Prod.snd x, Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) (idx j_15)))) (bs j_15, k j_15)))))) polyH42; have polyH44 := Poly.add polyH30 polyH43; have polyH45 := Poly.add (hout) polyH10; have polyH46 := Poly.mul polyH25 polyH45; have polyH47 := Poly.add polyH44 polyH46; have polyH48 := Poly.of_le (fun (j_15 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => (fun (x_1 : ℕ × List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Binary.takeStep^[Prod.fst x_1] (Prod.snd x_1)) ((fun (x_1 : List ((fun (x_1 : I) => Bool) i) × ℕ) => (Prod.snd x_1, Prod.fst x_1, @List.nil ((fun (x_2 : I) => Bool) i))) x)) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) => (fun (xs : List ((fun (x_1 : I) => Bool) i)) => List.reverse xs) (Prod.snd x)) (@Uniform.comp I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => ℕ × List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => (Prod.snd x, Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) i))) (fun (i : I) (x : ℕ × List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) => Binary.takeStep^[Prod.fst x] (Prod.snd x)) (@Uniform.pair I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => (Prod.fst x, @List.nil ((fun (x_1 : I) => Bool) i))) (@Uniform.snd I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.pair I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (x : List ((fun (x : I) => Bool) i) × ℕ) => @List.nil ((fun (x_1 : I) => Bool) i)) (@Uniform.fst I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => ℕ) _ _) (@Uniform.nil I (fun (i : I) => List ((fun (x : I) => Bool) i) × ℕ) (fun (x : I) => Bool) _ _))) (@Uniform.iterate I (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) _ (fun (i : I) => Binary.takeStep) (@Uniform.takeStep I (fun (x : I) => Bool) _))) (@Uniform.comp I (fun (i : I) => List ((fun (x : I) => Bool) i) × List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) (xs : List ((fun (x : I) => Bool) i)) => List.reverse xs) (@Uniform.snd I (fun (i : I) => List ((fun (x : I) => Bool) i)) (fun (i : I) => List ((fun (x : I) => Bool) i)) _ _) (@Uniform.reverse I (fun (x : I) => Bool) _)) (idx j_15) ((bs j_15, k j_15))))) polyH47; exact Poly.lift polyH48 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryReadNat (hl : Poly s (fun j => (bs j).length) 1)
    (hv : Poly s (fun j => (Binary.readNat (bs j)).1) 1) :
    Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (bs j)) 3 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (j_1 : J) => bs j_1) (hl) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hlead := binaryLeading s idx bs hl
  have hkl : Poly s (fun j => Binary.leading (bs j)) 1 := Poly.of_le (fun j => Binary.leading_le (bs j)) hl
  have htail : Poly s (fun j => ((bs j).drop (Binary.leading (bs j)+1)).length) 1 := by
    apply Poly.of_le _ hl
    intro j; exact (List.drop_sublist _ _).length_le
  have hbits : Poly s (fun j => (((bs j).drop (Binary.leading (bs j)+1)).take (Binary.leading (bs j))).length) 1 := by
    apply Poly.of_le _ htail
    intro j; exact (List.take_sublist _ _).length_le
  have ht := binaryTake s idx (fun j => (bs j).drop (Binary.leading (bs j)+1))
    (fun j => Binary.leading (bs j)) htail hkl
  change Poly s (fun j => Binary.value (((bs j).drop (Binary.leading (bs j)+1)).take (Binary.leading (bs j)))) 1 at hv
  have hval := binaryValue s idx
    (fun j => ((bs j).drop (Binary.leading (bs j)+1)).take (Binary.leading (bs j))) hbits hv
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (hb) polyH0; have polyH2 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_id (I) (fun (x : I) => List Bool) _ (idx j_17) (bs j_17)))) polyH1; have polyH3 := Poly.const (s) (200); have polyH4 := Poly.const (s) (1); have polyH5 := Poly.add (hkl) polyH4; have polyH6 := Poly.mul polyH3 polyH5; have polyH7 := Poly.of_le (fun (j_17 : J) => (@Realizer.time_succ_le (Binary.leading (bs j_17)))) polyH6; have polyH8 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_uniform (I) (ℕ) (ℕ) _ _ (fun (n : ℕ) => n + 1) (Realizer.succ) (idx j_17) (Binary.leading (bs j_17))))) polyH7; have polyH9 := Poly.add (hlead) polyH8; have polyH10 := Poly.const (s) (10); have polyH11 := Poly.volumeNat (hkl); have polyH12 := Poly.add polyH11 polyH4; have polyH13 := Poly.mul polyH10 polyH12; have polyH14 := Poly.add polyH9 polyH13; have polyH15 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I) (idx j_17) (bs j_17)))) polyH14; have polyH16 := Poly.add polyH2 polyH15; have polyH17 := Poly.const (s) (20); have polyH18 := Poly.add (hb) (hb); have polyH19 := Poly.volumeNat polyH5; have polyH20 := Poly.add polyH18 polyH19; have polyH21 := Poly.add polyH20 polyH4; have polyH22 := Poly.mul polyH17 polyH21; have polyH23 := Poly.add polyH16 polyH22; have polyH24 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I)) (idx j_17) (bs j_17)))) polyH23; have polyH25 := Poly.const (s) (1000000); have polyH26 := Poly.add polyH5 polyH4; have polyH27 := Poly.mul polyH25 polyH26; have polyH28 := Poly.add (hb) polyH5; have polyH29 := Poly.add polyH28 polyH4; have polyH30 := Poly.mul polyH27 polyH29; have polyH31 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_drop_le (I) (fun (i : I) => Bool) _ (idx j_17) (bs j_17) ((fun (n : ℕ) => n + 1) (Binary.leading (bs j_17))))) polyH30; have polyH32 := Poly.add polyH24 polyH31; have polyH33 := Poly.volumeProd (fun (j_1 : J) => (bs j_1, (fun (n : ℕ) => n + 1) (Binary.leading (bs j_1)))) (hb) polyH19; have polyH34 := Poly.add polyH33 polyH4; have polyH35 := Poly.mul polyH10 polyH34; have polyH36 := Poly.add polyH32 polyH35; have polyH37 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _) (idx j_17) (bs j_17)))) polyH36; have polyH38 := Poly.add polyH37 (hlead); have polyH39 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (Binary.leading (bs j_1) + 1) (bs j_1)) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (Binary.leading (bs j_1) + 1) (bs j_1)) => (Sigma.snd q).1); have polyH40 := Poly.listVolume (fun (j_1 : J) => List.drop (Binary.leading (bs j_1) + 1) (bs j_1)) (htail) polyH39; have polyH41 := Poly.add (hb) polyH40; have polyH42 := Poly.add polyH41 polyH11; have polyH43 := Poly.add polyH42 polyH4; have polyH44 := Poly.mul polyH17 polyH43; have polyH45 := Poly.add polyH38 polyH44; have polyH46 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (fun (x : I) => Binary.leading) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (@Uniform.binaryLeading I) (idx j_17) (bs j_17)))) polyH45; have polyH47 := Poly.add polyH46 (ht); have polyH48 := Poly.volumeProd (fun (j_1 : J) => (List.drop (Binary.leading (bs j_1) + 1) (bs j_1), Binary.leading (bs j_1))) polyH40 polyH11; have polyH49 := Poly.add polyH48 polyH4; have polyH50 := Poly.mul polyH10 polyH49; have polyH51 := Poly.add polyH47 polyH50; have polyH52 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (fun (i : I) (x : List Bool × ℕ) => List.take (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (fun (x : I) => Binary.leading) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (@Uniform.binaryLeading I)) (@Uniform.take I (fun (i : I) => Bool) _) (idx j_17) (bs j_17)))) polyH51; have polyH53 := Poly.add polyH52 (hval); have polyH54 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.take (Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1)))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.take (Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1)))) => (Sigma.snd q).1); have polyH55 := Poly.listVolume (fun (j_1 : J) => List.take (Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1)))) (hbits) polyH54; have polyH56 := Poly.add polyH55 polyH4; have polyH57 := Poly.mul polyH10 polyH56; have polyH58 := Poly.add polyH53 polyH57; have polyH59 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => (fun (x_1 : List Bool × ℕ) => List.take (Prod.snd x_1) (Prod.fst x_1)) ((fun (x_1 : List Bool) => (List.drop (Binary.leading x_1 + 1) x_1, Binary.leading x_1)) x)) (fun (x : I) => Binary.value) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (fun (i : I) (x : List Bool × ℕ) => List.take (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (fun (x : I) => Binary.leading) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (@Uniform.binaryLeading I)) (@Uniform.take I (fun (i : I) => Bool) _)) (@Uniform.binaryValue I) (idx j_17) (bs j_17)))) polyH58; have polyH60 := Poly.mul polyH25 polyH5; have polyH61 := Poly.add polyH40 (hkl); have polyH62 := Poly.add polyH61 polyH4; have polyH63 := Poly.mul polyH60 polyH62; have polyH64 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_drop_le (I) (fun (i : I) => Bool) _ (idx j_17) (List.drop (Binary.leading (bs j_17) + 1) (bs j_17)) (Binary.leading (bs j_17)))) polyH63; have polyH65 := Poly.add polyH46 polyH64; have polyH66 := Poly.add polyH65 polyH50; have polyH67 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (fun (x : I) => Binary.leading) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (@Uniform.binaryLeading I)) (@Uniform.drop I (fun (i : I) => Bool) _) (idx j_17) (bs j_17)))) polyH66; have polyH68 := Poly.add polyH59 polyH67; have polyH69 := Poly.volumeNat (hv); have polyH70 := Poly.add (hb) polyH69; have polyH71 := Poly.lengthDrop (fun (j_1 : J) => Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (fun (j_1 : J) => Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (htail); have polyH72 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1)))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1)))) => (Sigma.snd q).1); have polyH73 := Poly.listVolume (fun (j_1 : J) => List.drop (Prod.snd ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1))) (Prod.fst ((fun (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (bs j_1)))) polyH71 polyH72; have polyH74 := Poly.add polyH70 polyH73; have polyH75 := Poly.add polyH74 polyH4; have polyH76 := Poly.mul polyH17 polyH75; have polyH77 := Poly.add polyH68 polyH76; have polyH78 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Binary.value ((fun (x_1 : List Bool × ℕ) => List.take (Prod.snd x_1) (Prod.fst x_1)) ((fun (x_1 : List Bool) => (List.drop (Binary.leading x_1 + 1) x_1, Binary.leading x_1)) x))) (fun (i : I) (x : List Bool) => (fun (x_1 : List Bool × ℕ) => List.drop (Prod.snd x_1) (Prod.fst x_1)) ((fun (x_1 : List Bool) => (List.drop (Binary.leading x_1 + 1) x_1, Binary.leading x_1)) x)) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => (fun (x_1 : List Bool × ℕ) => List.take (Prod.snd x_1) (Prod.fst x_1)) ((fun (x_1 : List Bool) => (List.drop (Binary.leading x_1 + 1) x_1, Binary.leading x_1)) x)) (fun (x : I) => Binary.value) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (fun (i : I) (x : List Bool × ℕ) => List.take (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (fun (x : I) => Binary.leading) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (@Uniform.binaryLeading I)) (@Uniform.take I (fun (i : I) => Bool) _)) (@Uniform.binaryValue I)) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.drop (Binary.leading x + 1) x, Binary.leading x)) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (fun (x : I) => Binary.leading) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (@Uniform.binaryLeading I)) (@Uniform.drop I (fun (i : I) => Bool) _)) (idx j_17) (bs j_17)))) polyH77; exact Poly.lift polyH78 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end Costs
end ThreeMachine.StackCompiler
end

end OAI
end

section
-- module EncodingCosts
namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u1}

theorem readStep_prefix {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest))
    (xs : List α) (rest : List Bool) (acc : List α) (k : ℕ) (hk : k ≤ xs.length) :
    (readStep reader)^[k] (xs.flatMap encode ++ rest,acc) =
      ((xs.drop k).flatMap encode ++ rest,(xs.take k).reverse ++ acc) := by
  have h := readStep_iterate hr (xs.take k) ((xs.drop k).flatMap encode ++ rest) acc
  rw [List.length_take,Nat.min_eq_left hk] at h
  rw [← List.append_assoc,← List.flatMap_append,List.take_append_drop] at h
  exact h

theorem readNat_rest_length (bs : List Bool) : (readNat bs).2.length ≤ bs.length := by
  exact (List.drop_sublist _ _).length_le.trans (List.drop_sublist _ _).length_le

theorem increment_length (bs : List Bool) : (increment bs).length ≤ bs.length+1 := by
  induction bs with
  | nil => simp [increment]
  | cons b bs ih => cases b <;> simp only [increment,List.length_cons] <;> omega

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← increment_encodeNat]; exact (increment_length _).trans (Nat.add_le_add_right ih 1)

theorem encodeNat_length_le (n : ℕ) : (ThreeMachine.encodeNat n).length ≤ 2*n+1 := by
  have h := encodeNat_length n
  simp only [ThreeMachine.encodeNat,List.length_append,List.length_replicate,List.length_cons]
  omega

end ThreeMachine.StackCompiler.Binary
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

theorem binaryIncrement (bs : J → List Bool) (hl : Poly s (fun j => (bs j).length) 1) :
    Poly s (fun j => (Uniform.binaryIncrement (I := I)).time (idx j) (bs j)) 3 := by
  have ht := binaryLeading s idx bs hl
  have hk : Poly s (fun j => Binary.leading (bs j)) 1 := Poly.of_le (fun j => Binary.leading_le _) hl
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_false (I) (fun (x : I) => List Bool) _ (idx j_10) (bs j_10)))) polyH0; have polyH2 := Poly.add (ht) polyH1; have polyH3 := Poly.const (s) (20); have polyH4 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => (Sigma.snd q).1); have polyH5 := Poly.listVolume (fun (j_1 : J) => bs j_1) (hl) polyH4; have polyH6 := Poly.volumeNat (hk); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.const (s) (volume Bool.false); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.const (s) (1); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.mul polyH3 polyH11; have polyH13 := Poly.add polyH2 polyH12; have polyH14 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (x : I) => Binary.leading) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.binaryLeading I) (@Uniform.false I (fun (x : I) => List Bool) _) (idx j_10) (bs j_10)))) polyH13; have polyH15 := Poly.volumeBool (s) (fun (j_1 : J) => Bool.false); have polyH16 := Poly.volumeProd (fun (j_1 : J) => (Binary.leading (bs j_1), Bool.false)) polyH6 polyH15; have polyH17 := Poly.add polyH16 polyH0; have polyH18 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_fst (I) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ (idx j_10) ((Binary.leading (bs j_10), Bool.false))))) polyH17; have polyH19 := Poly.add polyH6 polyH0; have polyH20 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_uniform (I) (ℕ) (List Unit) _ _ (fun (n : ℕ) => List.replicate n ()) (Realizer.unroll) (idx j_10) (Prod.fst (Binary.leading (bs j_10), Bool.false))))) polyH19; have polyH21 := Poly.add polyH18 polyH20; have polyH22 := Poly.const (s) (10); have polyH23 := Poly.add polyH6 polyH10; have polyH24 := Poly.mul polyH22 polyH23; have polyH25 := Poly.add polyH21 polyH24; have polyH26 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) (fun (x : I) => ℕ) (fun (x : I) => List Unit) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) (n : ℕ) => List.replicate n ()) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _) (Realizer.uniform Realizer.unroll I) (idx j_10) ((Binary.leading (bs j_10), Bool.false))))) polyH25; have polyH27 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ (idx j_10) ((Binary.leading (bs j_10), Bool.false))))) polyH17; have polyH28 := Poly.add polyH26 polyH27; have polyH29 := Poly.lengthReplicate (fun (j_1 : J) => Prod.fst (Binary.leading (bs j_1), Bool.false)) (fun (j_1 : J) => ()) (hk); have polyH30 := Poly.volumeUnit (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) ()) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) ()) => (Sigma.snd q).1); have polyH31 := Poly.listVolume (fun (j_1 : J) => List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) ()) polyH29 polyH30; have polyH32 := Poly.add polyH16 polyH31; have polyH33 := Poly.add polyH32 polyH15; have polyH34 := Poly.add polyH33 polyH10; have polyH35 := Poly.mul polyH3 polyH34; have polyH36 := Poly.add polyH28 polyH35; have polyH37 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) (fun (x : I) => List Unit) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) => (fun (x_1 : I) (n : ℕ) => List.replicate n ()) i (Prod.fst x)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) (fun (x : I) => ℕ) (fun (x : I) => List Unit) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) (n : ℕ) => List.replicate n ()) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _) (Realizer.uniform Realizer.unroll I)) (@Uniform.snd I (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _) (idx j_10) ((Binary.leading (bs j_10), Bool.false))))) polyH36; have polyH38 := Poly.lengthReplicate (fun (j_1 : J) => Prod.fst (Binary.leading (bs j_1), Bool.false)) (fun (j_1 : J) => ()) (hk); have polyH39 := Poly.volumeUnit (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) ()) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) ()) => (Sigma.snd q).1); have polyH40 := Poly.listVolume (fun (j_1 : J) => List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) ()) polyH38 polyH39; have polyH41 := Poly.volumePool (fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) polyH40; have polyH42 := Poly.volumeBool (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) => s (Sigma.fst q)) (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) => Bool.false); have polyH43 := Poly.volumeProd (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) => (Subtype.val (Sigma.snd q), Prod.snd (List.replicate (Prod.fst (Binary.leading (bs (Sigma.fst q)), Bool.false)) (), Prod.snd (Binary.leading (bs (Sigma.fst q)), Bool.false)))) polyH41 polyH42; have polyH44 := Poly.const (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) => s (Sigma.fst q)) (2); have polyH45 := Poly.add polyH43 polyH44; have polyH46 := Poly.of_le (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => Unit) (fun (i : I) => Bool) _ _ (idx (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.replicate (Prod.fst (Binary.leading (bs (Sigma.fst q)), Bool.false)) (), Prod.snd (Binary.leading (bs (Sigma.fst q)), Bool.false))))))) polyH45; have polyH47 := @Poly.mapTime (I) (J) (s) (fun (i : I) => Unit) (fun (i : I) => Bool) (fun (i : I) => Bool) _ _ _ (fun (j_1 : J) => idx j_1) (fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) (fun (j_1 : J) => Prod.snd (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) (fun (i : I) => Prod.snd) (@Uniform.snd I (fun (i : I) => Unit) (fun (i : I) => Bool) _ _) (1) (Max.max (Max.max (1 + 0) (0)) (0)) (1 + 0) (0) (0) polyH38 polyH46 polyH40 polyH15 polyH42; have polyH48 := Poly.add polyH37 polyH47; have polyH49 := Poly.volumeProd (fun (j_1 : J) => (List.replicate (Prod.fst (Binary.leading (bs j_1), Bool.false)) (), Prod.snd (Binary.leading (bs j_1), Bool.false))) polyH40 polyH15; have polyH50 := Poly.add polyH49 polyH10; have polyH51 := Poly.mul polyH22 polyH50; have polyH52 := Poly.add polyH48 polyH51; have polyH53 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => ℕ × (fun (i_1 : I) => Bool) i) (fun (i : I) => List Unit × (fun (i_1 : I) => Bool) i) (fun (i : I) => List ((fun (i_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x : ℕ × (fun (i_1 : I) => Bool) i) => (List.replicate (Prod.fst x) (), Prod.snd x)) (fun (i : I) (x : List Unit × (fun (i_1 : I) => Bool) i) => List.map (fun (a : Unit) => Prod.snd (a, Prod.snd x)) (Prod.fst x)) (@Uniform.onFst I (fun (x : I) => ℕ) (fun (x : I) => List Unit) (fun (i : I) => Bool) _ _ _ (fun (x : I) (n : ℕ) => List.replicate n ()) (Realizer.uniform Realizer.unroll I)) (@Uniform.map I (fun (i : I) => Unit) (fun (i : I) => Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) => Prod.snd) (@Uniform.snd I (fun (i : I) => Unit) (fun (i : I) => Bool) _ _)) (idx j_10) ((Binary.leading (bs j_10), Bool.false))))) polyH52; have polyH54 := Poly.add polyH14 polyH53; have polyH55 := Poly.add polyH16 polyH10; have polyH56 := Poly.mul polyH22 polyH55; have polyH57 := Poly.add polyH54 polyH56; have polyH58 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => ℕ × Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (Binary.leading x, Bool.false)) (fun (i : I) (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (x : I) => Binary.leading) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.binaryLeading I) (@Uniform.false I (fun (x : I) => List Bool) _)) (@Uniform.replicate I (fun (i : I) => Bool) _) (idx j_10) (bs j_10)))) polyH57; have polyH59 := Poly.const (s) (2 * volume Bool.true + 1); have polyH60 := Poly.mul polyH3 polyH5; have polyH61 := Poly.const (s) (50 * volume Bool.true); have polyH62 := Poly.add polyH60 polyH61; have polyH63 := Poly.const (s) (50); have polyH64 := Poly.add polyH62 polyH63; have polyH65 := Poly.mul polyH59 polyH64; have polyH66 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_constant (I) (fun (x : I) => List Bool) _ (Bool) _ (Bool.true) (idx j_10) (bs j_10)))) polyH65; have polyH67 := Poly.add polyH5 polyH0; have polyH68 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_id (I) (fun (x : I) => List Bool) _ (idx j_10) (bs j_10)))) polyH67; have polyH69 := Poly.const (s) (200); have polyH70 := Poly.add (hk) polyH10; have polyH71 := Poly.mul polyH69 polyH70; have polyH72 := Poly.of_le (fun (j_10 : J) => (@Realizer.time_succ_le (Binary.leading (bs j_10)))) polyH71; have polyH73 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_uniform (I) (ℕ) (ℕ) _ _ (fun (n : ℕ) => n + 1) (Realizer.succ) (idx j_10) (Binary.leading (bs j_10))))) polyH72; have polyH74 := Poly.add (ht) polyH73; have polyH75 := Poly.add polyH74 polyH24; have polyH76 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I) (idx j_10) (bs j_10)))) polyH75; have polyH77 := Poly.add polyH68 polyH76; have polyH78 := Poly.add polyH5 polyH5; have polyH79 := Poly.volumeNat polyH70; have polyH80 := Poly.add polyH78 polyH79; have polyH81 := Poly.add polyH80 polyH10; have polyH82 := Poly.mul polyH3 polyH81; have polyH83 := Poly.add polyH77 polyH82; have polyH84 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I)) (idx j_10) (bs j_10)))) polyH83; have polyH85 := Poly.const (s) (1000000); have polyH86 := Poly.add polyH70 polyH10; have polyH87 := Poly.mul polyH85 polyH86; have polyH88 := Poly.add polyH5 polyH70; have polyH89 := Poly.add polyH88 polyH10; have polyH90 := Poly.mul polyH87 polyH89; have polyH91 := Poly.of_le (fun (j_10 : J) => (@Uniform.time_drop_le (I) (fun (i : I) => Bool) _ (idx j_10) (bs j_10) ((fun (n : ℕ) => n + 1) (Binary.leading (bs j_10))))) polyH90; have polyH92 := Poly.add polyH84 polyH91; have polyH93 := Poly.volumeProd (fun (j_1 : J) => (bs j_1, (fun (n : ℕ) => n + 1) (Binary.leading (bs j_1)))) polyH5 polyH79; have polyH94 := Poly.add polyH93 polyH10; have polyH95 := Poly.mul polyH22 polyH94; have polyH96 := Poly.add polyH92 polyH95; have polyH97 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _) (idx j_10) (bs j_10)))) polyH96; have polyH98 := Poly.add polyH66 polyH97; have polyH99 := Poly.const (s) (volume Bool.true); have polyH100 := Poly.add polyH5 polyH99; have polyH101 := Poly.lengthDrop (fun (j_1 : J) => Binary.leading (bs j_1) + 1) (fun (j_1 : J) => bs j_1) (hl); have polyH102 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (Binary.leading (bs j_1) + 1) (bs j_1)) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.drop (Binary.leading (bs j_1) + 1) (bs j_1)) => (Sigma.snd q).1); have polyH103 := Poly.listVolume (fun (j_1 : J) => List.drop (Binary.leading (bs j_1) + 1) (bs j_1)) polyH101 polyH102; have polyH104 := Poly.add polyH100 polyH103; have polyH105 := Poly.add polyH104 polyH10; have polyH106 := Poly.mul polyH3 polyH105; have polyH107 := Poly.add polyH98 polyH106; have polyH108 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (@Uniform.constant I (fun (x : I) => List Bool) _ Bool _ Bool.true) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _)) (idx j_10) (bs j_10)))) polyH107; have polyH109 := Poly.volumeBool (s) (fun (j_1 : J) => Bool.true); have polyH110 := Poly.volumeProd (fun (j_1 : J) => (Bool.true, List.drop (Binary.leading (bs j_1) + 1) (bs j_1))) polyH109 polyH103; have polyH111 := Poly.add polyH110 polyH0; have polyH112 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_cons (I) (fun (i : I) => Bool) _ (idx j_10) ((Bool.true, List.drop (Binary.leading (bs j_10) + 1) (bs j_10)))))) polyH111; have polyH113 := Poly.add polyH108 polyH112; have polyH114 := Poly.add polyH110 polyH10; have polyH115 := Poly.mul polyH22 polyH114; have polyH116 := Poly.add polyH113 polyH115; have polyH117 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (x : I) => List Bool) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (@Uniform.constant I (fun (x : I) => List Bool) _ Bool _ Bool.true) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _))) (@Uniform.cons I (fun (i : I) => Bool) _) (idx j_10) (bs j_10)))) polyH116; have polyH118 := Poly.add polyH58 polyH117; have polyH119 := Poly.lengthReplicate (fun (j_1 : J) => Binary.leading (bs j_1)) (fun (j_1 : J) => Bool.false) (hk); have polyH120 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Binary.leading (bs j_1)) Bool.false) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Binary.leading (bs j_1)) Bool.false) => (Sigma.snd q).1); have polyH121 := Poly.listVolume (fun (j_1 : J) => List.replicate (Binary.leading (bs j_1)) Bool.false) polyH119 polyH120; have polyH122 := Poly.add polyH5 polyH121; have polyH123 := Poly.lengthCons (fun (j_1 : J) => Prod.fst ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1))) (fun (j_1 : J) => Prod.snd ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1))) polyH101; have polyH124 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => Prod.fst ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1)) :: Prod.snd ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => Prod.fst ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1)) :: Prod.snd ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1))) => (Sigma.snd q).1); have polyH125 := Poly.listVolume (fun (j_1 : J) => Prod.fst ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1)) :: Prod.snd ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1))) polyH123 polyH124; have polyH126 := Poly.add polyH122 polyH125; have polyH127 := Poly.add polyH126 polyH10; have polyH128 := Poly.mul polyH3 polyH127; have polyH129 := Poly.add polyH118 polyH128; have polyH130 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (i : I) => List Bool) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.replicate (Binary.leading bs_1) Bool.false) (fun (i : I) (x : List Bool) => (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : List Bool) => (Bool.true, List.drop (Binary.leading x_1 + 1) x_1)) x)) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => ℕ × Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (Binary.leading x, Bool.false)) (fun (i : I) (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (x : I) => Binary.leading) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.binaryLeading I) (@Uniform.false I (fun (x : I) => List Bool) _)) (@Uniform.replicate I (fun (i : I) => Bool) _)) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (x : I) => List Bool) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (@Uniform.constant I (fun (x : I) => List Bool) _ Bool _ Bool.true) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _))) (@Uniform.cons I (fun (i : I) => Bool) _)) (idx j_10) (bs j_10)))) polyH129; have polyH131 := Poly.const (s) (100000); have polyH132 := Poly.add polyH119 polyH10; have polyH133 := Poly.mul polyH131 polyH132; have polyH134 := Poly.add polyH121 polyH125; have polyH135 := Poly.add polyH134 polyH10; have polyH136 := Poly.mul polyH133 polyH135; have polyH137 := Poly.of_le (fun (j_10 : J) => (@Uniform.time_append_le (I) (fun (i : I) => Bool) _ (idx j_10) (List.replicate (Binary.leading (bs j_10)) Bool.false) ((fun (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_10))))) polyH136; have polyH138 := Poly.add polyH130 polyH137; have polyH139 := Poly.volumeProd (fun (j_1 : J) => (List.replicate (Binary.leading (bs j_1)) Bool.false, (fun (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) ((fun (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (bs j_1)))) polyH121 polyH125; have polyH140 := Poly.add polyH139 polyH10; have polyH141 := Poly.mul polyH22 polyH140; have polyH142 := Poly.add polyH138 polyH141; have polyH143 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (i : I) => List Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.replicate (Binary.leading x) Bool.false, (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : List Bool) => (Bool.true, List.drop (Binary.leading x_1 + 1) x_1)) x))) (fun (i : I) (x : List Bool × List Bool) => Prod.fst x ++ Prod.snd x) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (i : I) => List Bool) _ _ _ (fun (x : I) (bs_1 : List Bool) => List.replicate (Binary.leading bs_1) Bool.false) (fun (i : I) (x : List Bool) => (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : List Bool) => (Bool.true, List.drop (Binary.leading x_1 + 1) x_1)) x)) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => ℕ × Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (Binary.leading x, Bool.false)) (fun (i : I) (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (x : I) => Binary.leading) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.binaryLeading I) (@Uniform.false I (fun (x : I) => List Bool) _)) (@Uniform.replicate I (fun (i : I) => Bool) _)) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (Bool.true, List.drop (Binary.leading x + 1) x)) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (x : I) => List Bool) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Bool.true) (fun (x : I) (bs_1 : List Bool) => List.drop (Binary.leading bs_1 + 1) bs_1) (@Uniform.constant I (fun (x : I) => List Bool) _ Bool _ Bool.true) (@Uniform.comp I (fun (x : I) => List Bool) (fun (i : I) => List Bool × ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (x, (fun (n : ℕ) => n + 1) (Binary.leading x))) (fun (i : I) (x : List Bool × ℕ) => List.drop (Prod.snd x) (Prod.fst x)) (@Uniform.pair I (fun (x : I) => List Bool) (fun (x : I) => List Bool) (fun (x : I) => ℕ) _ _ _ (fun (i : I) (x : List Bool) => x) (fun (i : I) (x : List Bool) => (fun (n : ℕ) => n + 1) (Binary.leading x)) (@Uniform.id I (fun (x : I) => List Bool) _) (@Uniform.comp I (fun (x : I) => List Bool) (fun (x : I) => ℕ) (fun (x : I) => ℕ) _ _ _ (fun (x : I) => Binary.leading) (fun (x : I) (n : ℕ) => n + 1) (@Uniform.binaryLeading I) (Realizer.uniform Realizer.succ I))) (@Uniform.drop I (fun (i : I) => Bool) _))) (@Uniform.cons I (fun (i : I) => Bool) _))) (@Uniform.append I (fun (i : I) => Bool) _) (idx j_10) (bs j_10)))) polyH142; exact Poly.lift polyH143 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem rawEncodeNat (k : J → ℕ) (hk : Poly s k 1) :
    Poly s (fun j => (Uniform.rawEncodeNat (I := I)).time (idx j) (k j)) 4 := by
  have hp : Poly (fun p : Poly.IterPool k => s p.1) (fun p => p.2.1) 1 :=
    Poly.of_le (fun p => Nat.le_of_lt_succ p.2.2) (hk.precomp Sigma.fst)
  have hlen : Poly (fun p : Poly.IterPool k => s p.1)
      (fun p => (Binary.increment^[p.2.1] []).length) 1 := by
    simp only [Binary.iterate_increment]
    exact Poly.of_le (fun p => Binary.encodeNat_length p.2.1) hp
  have ht := binaryIncrement (fun p : Poly.IterPool k => s p.1) (fun p => idx p.1)
    (fun p => Binary.increment^[p.2.1] []) hlen
  have hv : Poly (fun p : Poly.IterPool k => s p.1)
      (fun p => volume (Binary.increment^[p.2.1] [])) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (p_1 : Poly.IterPool k) => Binary.increment^[Fin.val (Sigma.snd p_1)] []) => (fun (p_1 : Poly.IterPool k) => s (Sigma.fst p_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (p_1 : Poly.IterPool k) => Binary.increment^[Fin.val (Sigma.snd p_1)] []) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (p_1 : Poly.IterPool k) => Binary.increment^[Fin.val (Sigma.snd p_1)] []) (hlen) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hiter := Poly.iterateTime (Uniform.binaryIncrement (I := I)) idx k (fun _ => []) hk ht hv
  (have polyH0 := Poly.volumeNat (hk); have polyH1 := Poly.const (s) (2); have polyH2 := Poly.add polyH0 polyH1; have polyH3 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_id (I) (fun (i : I) => ℕ) _ (idx j_13) (k j_13)))) polyH2; have polyH4 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_nil (I) (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _ (idx j_13) (k j_13)))) polyH1; have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.const (s) (20); have polyH7 := Poly.add polyH0 polyH0; have polyH8 := Poly.const (s) (volume (@List.nil Bool)); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.const (s) (1); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.mul polyH6 polyH11; have polyH13 := Poly.add polyH5 polyH12; have polyH14 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => ℕ) (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => x) (fun (i : I) (x : ℕ) => @List.nil Bool) (@Uniform.id I (fun (i : I) => ℕ) _) (@Uniform.nil I (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _) (idx j_13) (k j_13)))) polyH13; have polyH15 := Poly.add polyH14 (hiter); have polyH16 := Poly.const (s) (10); have polyH17 := Poly.volumeProd (fun (j_1 : J) => (k j_1, @List.nil Bool)) polyH0 polyH10; have polyH18 := Poly.add polyH17 polyH10; have polyH19 := Poly.mul polyH16 polyH18; have polyH20 := Poly.add polyH15 polyH19; have polyH21 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => ℕ) (fun (i : I) => ℕ × List Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => (x, @List.nil Bool)) (fun (i : I) (x : ℕ × List Bool) => Binary.increment^[Prod.fst x] (Prod.snd x)) (@Uniform.pair I (fun (i : I) => ℕ) (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => x) (fun (i : I) (x : ℕ) => @List.nil Bool) (@Uniform.id I (fun (i : I) => ℕ) _) (@Uniform.nil I (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _)) (@Uniform.iterate I (fun (x : I) => List Bool) _ (fun (x : I) => Binary.increment) (@Uniform.binaryIncrement I)) (idx j_13) (k j_13)))) polyH20; exact Poly.lift polyH21 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryEncodeNat (k : J → ℕ) (hk : Poly s k 1) :
    Poly s (fun j => (Uniform.binaryEncodeNat (I := I)).time (idx j) (k j)) 4 := by
  have ht := rawEncodeNat s idx k hk
  have hl : Poly s (fun j => (Computability.encodeNat (k j)).length) 1 :=
    Poly.of_le (fun j => Binary.encodeNat_length _) hk
  (have polyH0 := Poly.const (s) (100000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => Computability.encodeNat (k j_1)) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => Computability.encodeNat (k j_1)) => (Sigma.snd q).1); have polyH5 := Poly.listVolume (fun (j_1 : J) => Computability.encodeNat (k j_1)) (hl) polyH4; have polyH6 := Poly.add polyH5 polyH1; have polyH7 := Poly.mul polyH3 polyH6; have polyH8 := Poly.of_le (fun (j_10 : J) => (@Uniform.time_length_le (I) (fun (i : I) => Bool) _ (idx j_10) (Computability.encodeNat (k j_10)))) polyH7; have polyH9 := Poly.add (ht) polyH8; have polyH10 := Poly.const (s) (10); have polyH11 := Poly.mul polyH10 polyH6; have polyH12 := Poly.add polyH9 polyH11; have polyH13 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (x : I) => Computability.encodeNat) (fun (i : I) (xs : List Bool) => List.length xs) (@Uniform.rawEncodeNat I) (@Uniform.length I (fun (i : I) => Bool) _) (idx j_10) (k j_10)))) polyH12; have polyH14 := Poly.const (s) (2 * volume Bool.true + 1); have polyH15 := Poly.const (s) (20); have polyH16 := Poly.volumeNat (hk); have polyH17 := Poly.mul polyH15 polyH16; have polyH18 := Poly.const (s) (50 * volume Bool.true); have polyH19 := Poly.add polyH17 polyH18; have polyH20 := Poly.const (s) (50); have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.mul polyH14 polyH21; have polyH23 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_constant (I) (fun (x : I) => ℕ) _ (Bool) _ (Bool.true) (idx j_10) (k j_10)))) polyH22; have polyH24 := Poly.add polyH13 polyH23; have polyH25 := Poly.volumeNat (hl); have polyH26 := Poly.add polyH16 polyH25; have polyH27 := Poly.const (s) (volume Bool.true); have polyH28 := Poly.add polyH26 polyH27; have polyH29 := Poly.add polyH28 polyH1; have polyH30 := Poly.mul polyH15 polyH29; have polyH31 := Poly.add polyH24 polyH30; have polyH32 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => ℕ) (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : ℕ) => (fun (xs : List Bool) => List.length xs) (Computability.encodeNat x)) (fun (i : I) (x : ℕ) => Bool.true) (@Uniform.comp I (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (x : I) => Computability.encodeNat) (fun (i : I) (xs : List Bool) => List.length xs) (@Uniform.rawEncodeNat I) (@Uniform.length I (fun (i : I) => Bool) _)) (@Uniform.constant I (fun (x : I) => ℕ) _ Bool _ Bool.true) (idx j_10) (k j_10)))) polyH31; have polyH33 := Poly.volumeBool (s) (fun (j_1 : J) => Bool.true); have polyH34 := Poly.volumeProd (fun (j_1 : J) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) polyH25 polyH33; have polyH35 := Poly.const (s) (2); have polyH36 := Poly.add polyH34 polyH35; have polyH37 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_fst (I) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ (idx j_10) (((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_10)), Bool.true))))) polyH36; have polyH38 := Poly.add polyH25 polyH35; have polyH39 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_uniform (I) (ℕ) (List Unit) _ _ (fun (n : ℕ) => List.replicate n ()) (Realizer.unroll) (idx j_10) (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_10)), Bool.true))))) polyH38; have polyH40 := Poly.add polyH37 polyH39; have polyH41 := Poly.add polyH25 polyH1; have polyH42 := Poly.mul polyH10 polyH41; have polyH43 := Poly.add polyH40 polyH42; have polyH44 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) (fun (x : I) => ℕ) (fun (x : I) => List Unit) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) (n : ℕ) => List.replicate n ()) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _) (Realizer.uniform Realizer.unroll I) (idx j_10) (((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_10)), Bool.true))))) polyH43; have polyH45 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _ (idx j_10) (((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_10)), Bool.true))))) polyH36; have polyH46 := Poly.add polyH44 polyH45; have polyH47 := Poly.lengthReplicate (fun (j_1 : J) => Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (fun (j_1 : J) => ()) (hl); have polyH48 := Poly.volumeUnit (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) ()) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) ()) => (Sigma.snd q).1); have polyH49 := Poly.listVolume (fun (j_1 : J) => List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) ()) polyH47 polyH48; have polyH50 := Poly.add polyH34 polyH49; have polyH51 := Poly.add polyH50 polyH33; have polyH52 := Poly.add polyH51 polyH1; have polyH53 := Poly.mul polyH15 polyH52; have polyH54 := Poly.add polyH46 polyH53; have polyH55 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) (fun (x : I) => List Unit) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) => (fun (x_1 : I) (n : ℕ) => List.replicate n ()) i (Prod.fst x)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => (fun (x : I) => ℕ) i × (fun (i_1 : I) => Bool) i) (fun (x : I) => ℕ) (fun (x : I) => List Unit) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) (n : ℕ) => List.replicate n ()) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _) (Realizer.uniform Realizer.unroll I)) (@Uniform.snd I (fun (x : I) => ℕ) (fun (i : I) => Bool) _ _) (idx j_10) (((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_10)), Bool.true))))) polyH54; have polyH56 := Poly.lengthReplicate (fun (j_1 : J) => Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (fun (j_1 : J) => ()) (hl); have polyH57 := Poly.volumeUnit (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) ()) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) ()) => (Sigma.snd q).1); have polyH58 := Poly.listVolume (fun (j_1 : J) => List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) ()) polyH56 polyH57; have polyH59 := Poly.volumePool (fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) polyH58; have polyH60 := Poly.volumeBool (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) => s (Sigma.fst q)) (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) => Bool.true); have polyH61 := Poly.volumeProd (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) => (Subtype.val (Sigma.snd q), Prod.snd (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k (Sigma.fst q))), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k (Sigma.fst q))), Bool.true)))) polyH59 polyH60; have polyH62 := Poly.const (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) => s (Sigma.fst q)) (2); have polyH63 := Poly.add polyH61 polyH62; have polyH64 := Poly.of_le (fun (q : @Poly.Pool I J (fun (i : I) => Unit) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => Unit) (fun (i : I) => Bool) _ _ (idx (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k (Sigma.fst q))), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k (Sigma.fst q))), Bool.true))))))) polyH63; have polyH65 := @Poly.mapTime (I) (J) (s) (fun (i : I) => Unit) (fun (i : I) => Bool) (fun (i : I) => Bool) _ _ _ (fun (j_1 : J) => idx j_1) (fun (j_1 : J) => Prod.fst (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) (fun (j_1 : J) => Prod.snd (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) (fun (i : I) => Prod.snd) (@Uniform.snd I (fun (i : I) => Unit) (fun (i : I) => Bool) _ _) (1) (Max.max (Max.max (1 + 0) (0)) (0)) (1 + 0) (0) (0) polyH56 polyH64 polyH58 polyH33 polyH60; have polyH66 := Poly.add polyH55 polyH65; have polyH67 := Poly.volumeProd (fun (j_1 : J) => (List.replicate (Prod.fst ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true)) (), Prod.snd ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_1)), Bool.true))) polyH58 polyH33; have polyH68 := Poly.add polyH67 polyH1; have polyH69 := Poly.mul polyH10 polyH68; have polyH70 := Poly.add polyH66 polyH69; have polyH71 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => ℕ × (fun (i_1 : I) => Bool) i) (fun (i : I) => List Unit × (fun (i_1 : I) => Bool) i) (fun (i : I) => List ((fun (i_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x : ℕ × (fun (i_1 : I) => Bool) i) => (List.replicate (Prod.fst x) (), Prod.snd x)) (fun (i : I) (x : List Unit × (fun (i_1 : I) => Bool) i) => List.map (fun (a : Unit) => Prod.snd (a, Prod.snd x)) (Prod.fst x)) (@Uniform.onFst I (fun (x : I) => ℕ) (fun (x : I) => List Unit) (fun (i : I) => Bool) _ _ _ (fun (x : I) (n : ℕ) => List.replicate n ()) (Realizer.uniform Realizer.unroll I)) (@Uniform.map I (fun (i : I) => Unit) (fun (i : I) => Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) => Prod.snd) (@Uniform.snd I (fun (i : I) => Unit) (fun (i : I) => Bool) _ _)) (idx j_10) (((fun (xs : List Bool) => List.length xs) (Computability.encodeNat (k j_10)), Bool.true))))) polyH70; have polyH72 := Poly.add polyH32 polyH71; have polyH73 := Poly.add polyH34 polyH1; have polyH74 := Poly.mul polyH10 polyH73; have polyH75 := Poly.add polyH72 polyH74; have polyH76 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => ℕ) (fun (i : I) => ℕ × Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (fun (i : I) (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : ℕ) => (fun (xs : List Bool) => List.length xs) (Computability.encodeNat x)) (fun (i : I) (x : ℕ) => Bool.true) (@Uniform.comp I (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (x : I) => Computability.encodeNat) (fun (i : I) (xs : List Bool) => List.length xs) (@Uniform.rawEncodeNat I) (@Uniform.length I (fun (i : I) => Bool) _)) (@Uniform.constant I (fun (x : I) => ℕ) _ Bool _ Bool.true)) (@Uniform.replicate I (fun (i : I) => Bool) _) (idx j_10) (k j_10)))) polyH75; have polyH77 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_false (I) (fun (x : I) => ℕ) _ (idx j_10) (k j_10)))) polyH35; have polyH78 := Poly.add polyH77 (ht); have polyH79 := Poly.const (s) (volume Bool.false); have polyH80 := Poly.add polyH16 polyH79; have polyH81 := Poly.add polyH80 polyH5; have polyH82 := Poly.add polyH81 polyH1; have polyH83 := Poly.mul polyH15 polyH82; have polyH84 := Poly.add polyH78 polyH83; have polyH85 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => ℕ) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => Bool.false) (fun (x : I) => Computability.encodeNat) (@Uniform.false I (fun (x : I) => ℕ) _) (@Uniform.rawEncodeNat I) (idx j_10) (k j_10)))) polyH84; have polyH86 := Poly.volumeBool (s) (fun (j_1 : J) => Bool.false); have polyH87 := Poly.volumeProd (fun (j_1 : J) => (Bool.false, Computability.encodeNat (k j_1))) polyH86 polyH5; have polyH88 := Poly.add polyH87 polyH35; have polyH89 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_cons (I) (fun (i : I) => Bool) _ (idx j_10) ((Bool.false, Computability.encodeNat (k j_10)))))) polyH88; have polyH90 := Poly.add polyH85 polyH89; have polyH91 := Poly.add polyH87 polyH1; have polyH92 := Poly.mul polyH10 polyH91; have polyH93 := Poly.add polyH90 polyH92; have polyH94 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => ℕ) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => (Bool.false, Computability.encodeNat x)) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => Bool.false) (fun (x : I) => Computability.encodeNat) (@Uniform.false I (fun (x : I) => ℕ) _) (@Uniform.rawEncodeNat I)) (@Uniform.cons I (fun (i : I) => Bool) _) (idx j_10) (k j_10)))) polyH93; have polyH95 := Poly.add polyH76 polyH94; have polyH96 := Poly.lengthReplicate (fun (j_1 : J) => Prod.fst ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1))) (fun (j_1 : J) => Prod.snd ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1))) (hl); have polyH97 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1))) (Prod.snd ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1)))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.replicate (Prod.fst ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1))) (Prod.snd ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1)))) => (Sigma.snd q).1); have polyH98 := Poly.listVolume (fun (j_1 : J) => List.replicate (Prod.fst ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1))) (Prod.snd ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1)))) polyH96 polyH97; have polyH99 := Poly.add polyH16 polyH98; have polyH100 := Poly.lengthCons (fun (j_1 : J) => Prod.fst ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1))) (fun (j_1 : J) => Prod.snd ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1))) (hl); have polyH101 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => Prod.fst ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1)) :: Prod.snd ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => Prod.fst ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1)) :: Prod.snd ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1))) => (Sigma.snd q).1); have polyH102 := Poly.listVolume (fun (j_1 : J) => Prod.fst ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1)) :: Prod.snd ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1))) polyH100 polyH101; have polyH103 := Poly.add polyH99 polyH102; have polyH104 := Poly.add polyH103 polyH1; have polyH105 := Poly.mul polyH15 polyH104; have polyH106 := Poly.add polyH95 polyH105; have polyH107 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => ℕ) (fun (i : I) => List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => (fun (x_1 : ℕ × Bool) => List.replicate (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x_1), Bool.true)) x)) (fun (i : I) (x : ℕ) => (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : ℕ) => (Bool.false, Computability.encodeNat x_1)) x)) (@Uniform.comp I (fun (x : I) => ℕ) (fun (i : I) => ℕ × Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (fun (i : I) (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : ℕ) => (fun (xs : List Bool) => List.length xs) (Computability.encodeNat x)) (fun (i : I) (x : ℕ) => Bool.true) (@Uniform.comp I (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (x : I) => Computability.encodeNat) (fun (i : I) (xs : List Bool) => List.length xs) (@Uniform.rawEncodeNat I) (@Uniform.length I (fun (i : I) => Bool) _)) (@Uniform.constant I (fun (x : I) => ℕ) _ Bool _ Bool.true)) (@Uniform.replicate I (fun (i : I) => Bool) _)) (@Uniform.comp I (fun (x : I) => ℕ) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => (Bool.false, Computability.encodeNat x)) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => Bool.false) (fun (x : I) => Computability.encodeNat) (@Uniform.false I (fun (x : I) => ℕ) _) (@Uniform.rawEncodeNat I)) (@Uniform.cons I (fun (i : I) => Bool) _)) (idx j_10) (k j_10)))) polyH106; have polyH108 := Poly.add polyH96 polyH1; have polyH109 := Poly.mul polyH0 polyH108; have polyH110 := Poly.add polyH98 polyH102; have polyH111 := Poly.add polyH110 polyH1; have polyH112 := Poly.mul polyH109 polyH111; have polyH113 := Poly.of_le (fun (j_10 : J) => (@Uniform.time_append_le (I) (fun (i : I) => Bool) _ (idx j_10) ((fun (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_10))) ((fun (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_10))))) polyH112; have polyH114 := Poly.add polyH107 polyH113; have polyH115 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) ((fun (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (k j_1)), (fun (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) ((fun (x : ℕ) => (Bool.false, Computability.encodeNat x)) (k j_1)))) polyH98 polyH102; have polyH116 := Poly.add polyH115 polyH1; have polyH117 := Poly.mul polyH10 polyH116; have polyH118 := Poly.add polyH114 polyH117; have polyH119 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => ℕ) (fun (i : I) => List Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => ((fun (x_1 : ℕ × Bool) => List.replicate (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x_1), Bool.true)) x), (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : ℕ) => (Bool.false, Computability.encodeNat x_1)) x))) (fun (i : I) (x : List Bool × List Bool) => Prod.fst x ++ Prod.snd x) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => (fun (x_1 : ℕ × Bool) => List.replicate (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x_1), Bool.true)) x)) (fun (i : I) (x : ℕ) => (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : ℕ) => (Bool.false, Computability.encodeNat x_1)) x)) (@Uniform.comp I (fun (x : I) => ℕ) (fun (i : I) => ℕ × Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => ((fun (xs : List Bool) => List.length xs) (Computability.encodeNat x), Bool.true)) (fun (i : I) (x : ℕ × Bool) => List.replicate (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => ℕ) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : ℕ) => (fun (xs : List Bool) => List.length xs) (Computability.encodeNat x)) (fun (i : I) (x : ℕ) => Bool.true) (@Uniform.comp I (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _ _ (fun (x : I) => Computability.encodeNat) (fun (i : I) (xs : List Bool) => List.length xs) (@Uniform.rawEncodeNat I) (@Uniform.length I (fun (i : I) => Bool) _)) (@Uniform.constant I (fun (x : I) => ℕ) _ Bool _ Bool.true)) (@Uniform.replicate I (fun (i : I) => Bool) _)) (@Uniform.comp I (fun (x : I) => ℕ) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => (Bool.false, Computability.encodeNat x)) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (x : I) => ℕ) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : ℕ) => Bool.false) (fun (x : I) => Computability.encodeNat) (@Uniform.false I (fun (x : I) => ℕ) _) (@Uniform.rawEncodeNat I)) (@Uniform.cons I (fun (i : I) => Bool) _))) (@Uniform.append I (fun (i : I) => Bool) _) (idx j_10) (k j_10)))) polyH118; exact Poly.lift polyH119 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s : J → ℕ} {α : J → Type} [∀ j, Coding (α j)] {l v : ℕ}
theorem volumeListOfPool (xs : ∀ j, List (α j))
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun p : ListPool xs => s p.1) (fun p => volume p.2.1) v) :
    Poly s (fun j => volume (xs j)) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList hl (powerBase s C v)
  intro j a ha
  exact hC ⟨j,⟨a,ha⟩⟩
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

theorem binaryEncodeNatMap (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (Uniform.binaryEncodeNat (I := I)).mapList.time (idx j) (xs j)) 5 := by
  have ht := binaryEncodeNat (fun p : Poly.ListPool xs => s p.1) (fun p => idx p.1)
    (fun p => p.2.1) hk
  have vxp : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => volume p.2.1) 1 := by (have polyH0 := Poly.volumeNat (hk); exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have vx := Poly.volumeListOfPool xs hl vxp
  have hendlen : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => (ThreeMachine.encodeNat p.2.1).length) 1 := by
    apply Poly.of_le (fun p : Poly.ListPool xs => Binary.encodeNat_length_le p.2.1)
    (have polyH0 := Poly.const (fun (p_1 : Poly.ListPool xs) => s (Sigma.fst p_1)) (2); have polyH1 := Poly.mul polyH0 (hk); have polyH2 := Poly.const (fun (p_1 : Poly.ListPool xs) => s (Sigma.fst p_1)) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hendvol : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => volume (ThreeMachine.encodeNat p.2.1)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (p_1 : Poly.ListPool xs) => OAI.ThreeMachine.encodeNat (Subtype.val (Sigma.snd p_1))) => (fun (p_1 : Poly.ListPool xs) => s (Sigma.fst p_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (p_1 : Poly.ListPool xs) => OAI.ThreeMachine.encodeNat (Subtype.val (Sigma.snd p_1))) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (p_1 : Poly.ListPool xs) => OAI.ThreeMachine.encodeNat (Subtype.val (Sigma.snd p_1))) (hendlen) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (vx) polyH0; have polyH2 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_id (I) (fun (i : I) => List ((fun (x : I) => ℕ) i)) _ (idx j_14) (xs j_14)))) polyH1; have polyH3 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_unit (I) (fun (i : I) => List ((fun (x : I) => ℕ) i)) _ (idx j_14) (xs j_14)))) polyH0; have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.const (s) (20); have polyH6 := Poly.add (vx) (vx); have polyH7 := Poly.const (s) (volume ()); have polyH8 := Poly.add polyH6 polyH7; have polyH9 := Poly.const (s) (1); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.mul polyH5 polyH10; have polyH12 := Poly.add polyH4 polyH11; have polyH13 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ((fun (x : I) => ℕ) i)) (fun (i : I) => List ((fun (x : I) => ℕ) i)) (fun (i : I) => Unit) _ _ _ (fun (i : I) (x : List ((fun (x : I) => ℕ) i)) => x) (fun (i : I) (x : List ((fun (x : I) => ℕ) i)) => ()) (@Uniform.id I (fun (i : I) => List ((fun (x : I) => ℕ) i)) _) (@Uniform.unit I (fun (i : I) => List ((fun (x : I) => ℕ) i)) _) (idx j_14) (xs j_14)))) polyH12; have polyH14 := Poly.volumeUnit (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => s (Sigma.fst q)) (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => PUnit.unit); have polyH15 := Poly.volumeProd (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ()))) (vxp) polyH14; have polyH16 := Poly.const (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => s (Sigma.fst q)) (2); have polyH17 := Poly.add polyH15 polyH16; have polyH18 := Poly.of_le (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => (le_of_eq (@Uniform.time_fst (I) (fun (x : I) => ℕ) (fun (i : I) => Unit) _ _ (idx (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ())))))) polyH17; have polyH19 := Poly.add polyH18 (ht); have polyH20 := Poly.const (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => s (Sigma.fst q)) (10); have polyH21 := Poly.const (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => s (Sigma.fst q)) (1); have polyH22 := Poly.add (vxp) polyH21; have polyH23 := Poly.mul polyH20 polyH22; have polyH24 := Poly.add polyH19 polyH23; have polyH25 := Poly.of_le (fun (q : @Poly.Pool I J (fun (x : I) => ℕ) (fun (j_1 : J) => idx j_1) fun (j_1 : J) => Prod.fst (xs j_1, ())) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => (fun (x : I) => ℕ) i × Unit) (fun (x : I) => ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Unit) _ _) (@Uniform.binaryEncodeNat I) (idx (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ())))))) polyH24; have polyH26 := Poly.volumeUnit (s) (fun (j_1 : J) => PUnit.unit); have polyH27 := @Poly.mapTime (I) (J) (s) (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => Unit) _ _ _ (fun (j_1 : J) => idx j_1) (fun (j_1 : J) => Prod.fst (xs j_1, ())) (fun (j_1 : J) => Prod.snd (xs j_1, ())) (fun (i : I) (x : (fun (x : I) => ℕ) i × Unit) => (fun (x_1 : I) => OAI.ThreeMachine.encodeNat) i (Prod.fst x)) (@Uniform.comp I (fun (i : I) => (fun (x : I) => ℕ) i × Unit) (fun (x : I) => ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Unit) _ _) (@Uniform.binaryEncodeNat I)) (1) (Max.max (Max.max (Max.max (Max.max (1) (0)) (0)) (4)) (0 + Max.max (1) (0))) (1 + 1) (0) (1) (hl) polyH25 (vx) polyH26 (hendvol); have polyH28 := Poly.add polyH13 polyH27; have polyH29 := Poly.const (s) (10); have polyH30 := Poly.volumeProd (fun (j_1 : J) => (xs j_1, ())) (vx) polyH26; have polyH31 := Poly.add polyH30 polyH9; have polyH32 := Poly.mul polyH29 polyH31; have polyH33 := Poly.add polyH28 polyH32; have polyH34 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x : I) => ℕ) i)) (fun (i : I) => List ((fun (x : I) => ℕ) i) × Unit) (fun (i : I) => List ((fun (x : I) => List Bool) i)) _ _ _ (fun (i : I) (x : List ((fun (x : I) => ℕ) i)) => (x, ())) (fun (i : I) (x : List ((fun (x : I) => ℕ) i) × Unit) => List.map (fun (a : ℕ) => (fun (x_1 : I) => OAI.ThreeMachine.encodeNat) i (Prod.fst (a, Prod.snd x))) (Prod.fst x)) (@Uniform.pair I (fun (i : I) => List ((fun (x : I) => ℕ) i)) (fun (i : I) => List ((fun (x : I) => ℕ) i)) (fun (i : I) => Unit) _ _ _ (fun (i : I) (x : List ((fun (x : I) => ℕ) i)) => x) (fun (i : I) (x : List ((fun (x : I) => ℕ) i)) => ()) (@Uniform.id I (fun (i : I) => List ((fun (x : I) => ℕ) i)) _) (@Uniform.unit I (fun (i : I) => List ((fun (x : I) => ℕ) i)) _)) (@Uniform.map I (fun (x : I) => ℕ) (fun (x : I) => List Bool) (fun (i : I) => Unit) _ _ _ (fun (i : I) (x : (fun (x : I) => ℕ) i × Unit) => (fun (x_1 : I) => OAI.ThreeMachine.encodeNat) i (Prod.fst x)) (@Uniform.comp I (fun (i : I) => (fun (x : I) => ℕ) i × Unit) (fun (x : I) => ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) => Prod.fst) (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.fst I (fun (x : I) => ℕ) (fun (i : I) => Unit) _ _) (@Uniform.binaryEncodeNat I))) (idx j_14) (xs j_14)))) polyH33; exact Poly.lift polyH34 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem volumeEncodeNatList (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => volume ((xs j).map ThreeMachine.encodeNat)) 2 := by
  have hb : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => (ThreeMachine.encodeNat p.2.1).length) 1 := by
    apply Poly.of_le (fun p : Poly.ListPool xs => Binary.encodeNat_length_le p.2.1)
    (have polyH0 := Poly.const (fun (p_1 : Poly.ListPool xs) => s (Sigma.fst p_1)) (2); have polyH1 := Poly.mul polyH0 (hk); have polyH2 := Poly.const (fun (p_1 : Poly.ListPool xs) => s (Sigma.fst p_1)) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hv : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => volume (ThreeMachine.encodeNat p.2.1)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (p_1 : Poly.ListPool xs) => OAI.ThreeMachine.encodeNat (Subtype.val (Sigma.snd p_1))) => (fun (p_1 : Poly.ListPool xs) => s (Sigma.fst p_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (p_1 : Poly.ListPool xs) => OAI.ThreeMachine.encodeNat (Subtype.val (Sigma.snd p_1))) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (p_1 : Poly.ListPool xs) => OAI.ThreeMachine.encodeNat (Subtype.val (Sigma.snd p_1))) (hb) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  exact Poly.volumeMap _root_.id xs (fun _ => ()) (f := fun _ (x : ℕ × Unit) => ThreeMachine.encodeNat x.1) hl hv

theorem binaryEncodeList (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (Uniform.binaryEncodeList (I := I)).time (idx j) (xs j)) 5 := by
  have hMap := binaryEncodeNatMap s idx xs hl hk
  have hMV := volumeEncodeNatList s xs hl hk
  have hfv : Poly s (fun j => volume (((xs j).map ThreeMachine.encodeNat).flatten)) 2 :=
    Poly.of_le (fun j : J => by rw [volume_flatten]; omega) hMV
  have hfl := Poly.lengthVolume _ hfv
  have hFlat : Poly s (fun j => (Uniform.flatten (I := I) (α := fun _ => Bool)).time
      (idx j) ((xs j).map ThreeMachine.encodeNat)) 4 := by
    apply Poly.of_le (fun j : J => Uniform.time_flatten (α := fun _ : I => Bool) (idx j) ((xs j).map ThreeMachine.encodeNat))
    have hlm : Poly s (fun j => ((xs j).map ThreeMachine.encodeNat).length) 1 := by
      simpa only [List.length_map] using hl
    (have polyH0 := Poly.const (s) (10000); have polyH1 := Poly.add (hlm) (hfl); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.mul polyH0 polyH3; have polyH5 := Poly.add (hMV) polyH2; have polyH6 := Poly.mul polyH4 polyH5; exact Poly.lift polyH6 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hc := binaryEncodeNat s idx (fun j => (xs j).length) hl
  have vxp : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => volume p.2.1) 1 := by (have polyH0 := Poly.volumeNat (hk); exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have vx := Poly.volumeListOfPool xs hl vxp
  have hlenhead : Poly s (fun j => (ThreeMachine.encodeNat (xs j).length).length) 1 := by
    apply Poly.of_le (fun j => Binary.encodeNat_length_le _)
    (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hl); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  (have polyH0 := Poly.const (s) (100000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (vx) polyH1; have polyH5 := Poly.mul polyH3 polyH4; have polyH6 := Poly.of_le (fun (j_18 : J) => (@Uniform.time_length_le (I) (fun (i : I) => ℕ) _ (idx j_18) (xs j_18))) polyH5; have polyH7 := Poly.add polyH6 (hc); have polyH8 := Poly.const (s) (10); have polyH9 := Poly.volumeNat (hl); have polyH10 := Poly.add polyH9 polyH1; have polyH11 := Poly.mul polyH8 polyH10; have polyH12 := Poly.add polyH7 polyH11; have polyH13 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ℕ) (fun (i : I) => ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (xs_1 : List ℕ) => List.length xs_1) (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.length I (fun (i : I) => ℕ) _) (@Uniform.binaryEncodeNat I) (idx j_18) (xs j_18)))) polyH12; have polyH14 := Poly.add (hMap) (hFlat); have polyH15 := Poly.add (hMV) polyH1; have polyH16 := Poly.mul polyH8 polyH15; have polyH17 := Poly.add polyH14 polyH16; have polyH18 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ℕ) (fun (i : I) => List (List Bool)) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) (fun (i : I) (xs_1 : List (List Bool)) => List.flatten xs_1) (@Uniform.mapList I (fun (x : I) => ℕ) (fun (x : I) => List Bool) _ _ (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.binaryEncodeNat I)) (@Uniform.flatten I (fun (i : I) => Bool) _) (idx j_18) (xs j_18)))) polyH17; have polyH19 := Poly.add polyH13 polyH18; have polyH20 := Poly.const (s) (20); have polyH21 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) (xs j_1))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) (xs j_1))) => (Sigma.snd q).1); have polyH22 := Poly.listVolume (fun (j_1 : J) => OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) (xs j_1))) (hlenhead) polyH21; have polyH23 := Poly.add (vx) polyH22; have polyH24 := Poly.add polyH23 (hfv); have polyH25 := Poly.add polyH24 polyH1; have polyH26 := Poly.mul polyH20 polyH25; have polyH27 := Poly.add polyH19 polyH26; have polyH28 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ℕ) (fun (x : I) => List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List ℕ) => OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) x)) (fun (i : I) (x : List ℕ) => (fun (xs_1 : List (List Bool)) => List.flatten xs_1) ((fun (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) x)) (@Uniform.comp I (fun (i : I) => List ℕ) (fun (i : I) => ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (xs_1 : List ℕ) => List.length xs_1) (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.length I (fun (i : I) => ℕ) _) (@Uniform.binaryEncodeNat I)) (@Uniform.comp I (fun (i : I) => List ℕ) (fun (i : I) => List (List Bool)) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) (fun (i : I) (xs_1 : List (List Bool)) => List.flatten xs_1) (@Uniform.mapList I (fun (x : I) => ℕ) (fun (x : I) => List Bool) _ _ (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.binaryEncodeNat I)) (@Uniform.flatten I (fun (i : I) => Bool) _)) (idx j_18) (xs j_18)))) polyH27; have polyH29 := Poly.add (hlenhead) polyH1; have polyH30 := Poly.mul polyH0 polyH29; have polyH31 := Poly.add polyH22 (hfv); have polyH32 := Poly.add polyH31 polyH1; have polyH33 := Poly.mul polyH30 polyH32; have polyH34 := Poly.of_le (fun (j_18 : J) => (@Uniform.time_append_le (I) (fun (i : I) => Bool) _ (idx j_18) (OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) (xs j_18))) ((fun (xs_1 : List (List Bool)) => List.flatten xs_1) ((fun (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) (xs j_18))))) polyH33; have polyH35 := Poly.add polyH28 polyH34; have polyH36 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) (xs j_1)), (fun (xs_1 : List (List Bool)) => List.flatten xs_1) ((fun (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) (xs j_1)))) polyH22 (hfv); have polyH37 := Poly.add polyH36 polyH1; have polyH38 := Poly.mul polyH8 polyH37; have polyH39 := Poly.add polyH35 polyH38; have polyH40 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ℕ) (fun (i : I) => List Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List ℕ) => (OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) x), (fun (xs_1 : List (List Bool)) => List.flatten xs_1) ((fun (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) x))) (fun (i : I) (x : List Bool × List Bool) => Prod.fst x ++ Prod.snd x) (@Uniform.pair I (fun (i : I) => List ℕ) (fun (x : I) => List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List ℕ) => OAI.ThreeMachine.encodeNat ((fun (xs_1 : List ℕ) => List.length xs_1) x)) (fun (i : I) (x : List ℕ) => (fun (xs_1 : List (List Bool)) => List.flatten xs_1) ((fun (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) x)) (@Uniform.comp I (fun (i : I) => List ℕ) (fun (i : I) => ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (xs_1 : List ℕ) => List.length xs_1) (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.length I (fun (i : I) => ℕ) _) (@Uniform.binaryEncodeNat I)) (@Uniform.comp I (fun (i : I) => List ℕ) (fun (i : I) => List (List Bool)) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (xs_1 : List ℕ) => List.map OAI.ThreeMachine.encodeNat xs_1) (fun (i : I) (xs_1 : List (List Bool)) => List.flatten xs_1) (@Uniform.mapList I (fun (x : I) => ℕ) (fun (x : I) => List Bool) _ _ (fun (x : I) => OAI.ThreeMachine.encodeNat) (@Uniform.binaryEncodeNat I)) (@Uniform.flatten I (fun (i : I) => Bool) _))) (@Uniform.append I (fun (i : I) => Bool) _) (idx j_18) (xs j_18)))) polyH39; exact Poly.lift polyH40 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler

theorem volume_option_le_getD {α : Type} [Coding α] (o : Option α) (a : α) :
    volume o ≤ volume (o.getD a)+2 := by
  cases o <;> simp only [Option.getD_none,Option.getD_some,volume_none,volume_some] <;> omega
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem lengthEncodeNatList (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (ThreeMachine.encodeList ThreeMachine.encodeNat (xs j)).length) 2 := by
  have hMV := volumeEncodeNatList s xs hl hk
  have hfv : Poly s (fun j => volume (((xs j).map ThreeMachine.encodeNat).flatten)) 2 :=
    Poly.of_le (fun j : J => by rw [volume_flatten]; omega) hMV
  have hfl := Poly.lengthVolume _ hfv
  have hhead : Poly s (fun j => (ThreeMachine.encodeNat (xs j).length).length) 1 := by
    apply Poly.of_le (fun j : J => Binary.encodeNat_length_le _)
    (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hl); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  simp only [ThreeMachine.encodeList,List.length_append,List.flatMap_def]
  (have polyH0 := Poly.add (hhead) (hfl); exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryEncodeAnswer (o : J → Option (List ℕ))
    (hl : Poly s (fun j => ((o j).getD []).length) 1)
    (hk : Poly (fun p : Poly.ListPool (fun j => (o j).getD []) => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (Uniform.binaryEncodeAnswer (I := I)).time (idx j) (o j)) 5 := by
  have hE := binaryEncodeList s idx (fun j => (o j).getD []) hl hk
  have hitem : Poly (fun p : Poly.ListPool (fun j => (o j).getD []) => s p.1)
      (fun p => volume p.2.1) 1 := by (have polyH0 := Poly.volumeNat (hk); exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hL := Poly.volumeListOfPool (fun j => (o j).getD []) hl hitem
  have hO : Poly s (fun j => volume (o j)) 2 := by
    apply Poly.of_le (fun j : J => volume_option_le_getD (o j) [])
    (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (hL) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | omega))
  have hEncoded := lengthEncodeNatList s (fun j => (o j).getD []) hl hk
  (have polyH0 := Poly.const (s) (10000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hO) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.of_le (fun (j_14 : J) => (@Uniform.time_test_le (I) (fun (i : I) => Option ((fun (i_1 : I) => List ℕ) i)) _ (fun (i : I) (x : Option ((fun (i_1 : I) => List ℕ) i)) => Option.isSome x) (@Uniform.optionIsSome._proof_1 (I) (fun (i : I) => List ℕ) _) (idx j_14) (o j_14))) polyH3; have polyH5 := Poly.const (s) (2 * volume Bool.true + 1); have polyH6 := Poly.const (s) (20); have polyH7 := Poly.mul polyH6 (hO); have polyH8 := Poly.const (s) (50 * volume Bool.true); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.const (s) (50); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.mul polyH5 polyH11; have polyH13 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_constant (I) (fun (i : I) => Option (List ℕ)) _ (Bool) _ (Bool.true) (idx j_14) (o j_14)))) polyH12; have polyH14 := Poly.const (s) (2); have polyH15 := Poly.add (hO) polyH14; have polyH16 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_id (I) (fun (i : I) => Option (List ℕ)) _ (idx j_14) (o j_14)))) polyH15; have polyH17 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_nil (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _ (idx j_14) (o j_14)))) polyH14; have polyH18 := Poly.add polyH16 polyH17; have polyH19 := Poly.add (hO) (hO); have polyH20 := Poly.const (s) (volume (@List.nil ℕ)); have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.add polyH21 polyH1; have polyH23 := Poly.mul polyH6 polyH22; have polyH24 := Poly.add polyH18 polyH23; have polyH25 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => x) (fun (i : I) (x : Option (List ℕ)) => @List.nil ℕ) (@Uniform.id I (fun (i : I) => Option (List ℕ)) _) (@Uniform.nil I (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _) (idx j_14) (o j_14)))) polyH24; have polyH26 := Poly.add (hO) polyH20; have polyH27 := Poly.add polyH26 polyH1; have polyH28 := Poly.mul polyH0 polyH27; have polyH29 := Poly.of_le (fun (j_14 : J) => (@Uniform.time_getD_le (I) (fun (i : I) => List ℕ) _ (idx j_14) (o j_14) (@List.nil ℕ))) polyH28; have polyH30 := Poly.add polyH25 polyH29; have polyH31 := Poly.const (s) (10); have polyH32 := Poly.volumeProd (fun (j_1 : J) => (o j_1, @List.nil ℕ)) (hO) polyH1; have polyH33 := Poly.add polyH32 polyH1; have polyH34 := Poly.mul polyH31 polyH33; have polyH35 := Poly.add polyH30 polyH34; have polyH36 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ) × List ℕ) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (x, @List.nil ℕ)) (fun (i : I) (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => x) (fun (i : I) (x : Option (List ℕ)) => @List.nil ℕ) (@Uniform.id I (fun (i : I) => Option (List ℕ)) _) (@Uniform.nil I (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _)) (@Uniform.getD I (fun (i : I) => List ℕ) _) (idx j_14) (o j_14)))) polyH35; have polyH37 := Poly.add polyH36 (hE); have polyH38 := Poly.add (hL) polyH1; have polyH39 := Poly.mul polyH31 polyH38; have polyH40 := Poly.add polyH37 polyH39; have polyH41 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)) (fun (x : I) (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ) × List ℕ) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (x, @List.nil ℕ)) (fun (i : I) (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => x) (fun (i : I) (x : Option (List ℕ)) => @List.nil ℕ) (@Uniform.id I (fun (i : I) => Option (List ℕ)) _) (@Uniform.nil I (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _)) (@Uniform.getD I (fun (i : I) => List ℕ) _)) (@Uniform.binaryEncodeList I) (idx j_14) (o j_14)))) polyH40; have polyH42 := Poly.add polyH13 polyH41; have polyH43 := Poly.const (s) (volume Bool.true); have polyH44 := Poly.add (hO) polyH43; have polyH45 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat ((fun (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Option (List ℕ)) => (x, @List.nil ℕ)) (o j_1)))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat ((fun (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Option (List ℕ)) => (x, @List.nil ℕ)) (o j_1)))) => (Sigma.snd q).1); have polyH46 := Poly.listVolume (fun (j_1 : J) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat ((fun (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Option (List ℕ)) => (x, @List.nil ℕ)) (o j_1)))) (hEncoded) polyH45; have polyH47 := Poly.add polyH44 polyH46; have polyH48 := Poly.add polyH47 polyH1; have polyH49 := Poly.mul polyH6 polyH48; have polyH50 := Poly.add polyH42 polyH49; have polyH51 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => Bool.true) (fun (i : I) (x : Option (List ℕ)) => (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x))) (@Uniform.constant I (fun (i : I) => Option (List ℕ)) _ Bool _ Bool.true) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)) (fun (x : I) (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ) × List ℕ) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (x, @List.nil ℕ)) (fun (i : I) (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => x) (fun (i : I) (x : Option (List ℕ)) => @List.nil ℕ) (@Uniform.id I (fun (i : I) => Option (List ℕ)) _) (@Uniform.nil I (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _)) (@Uniform.getD I (fun (i : I) => List ℕ) _)) (@Uniform.binaryEncodeList I)) (idx j_14) (o j_14)))) polyH50; have polyH52 := Poly.volumeBool (s) (fun (j_1 : J) => Bool.true); have polyH53 := Poly.volumeProd (fun (j_1 : J) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Option (List ℕ)) => (x, @List.nil ℕ)) (o j_1))))) polyH52 polyH46; have polyH54 := Poly.add polyH53 polyH14; have polyH55 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_cons (I) (fun (i : I) => Bool) _ (idx j_14) ((Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Option (List ℕ)) => (x, @List.nil ℕ)) (o j_14)))))))) polyH54; have polyH56 := Poly.add polyH51 polyH55; have polyH57 := Poly.add polyH53 polyH1; have polyH58 := Poly.mul polyH31 polyH57; have polyH59 := Poly.add polyH56 polyH58; have polyH60 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => Bool.true) (fun (i : I) (x : Option (List ℕ)) => (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x))) (@Uniform.constant I (fun (i : I) => Option (List ℕ)) _ Bool _ Bool.true) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)) (fun (x : I) (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ) × List ℕ) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (x, @List.nil ℕ)) (fun (i : I) (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => x) (fun (i : I) (x : Option (List ℕ)) => @List.nil ℕ) (@Uniform.id I (fun (i : I) => Option (List ℕ)) _) (@Uniform.nil I (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _)) (@Uniform.getD I (fun (i : I) => List ℕ) _)) (@Uniform.binaryEncodeList I))) (@Uniform.cons I (fun (i : I) => Bool) _) (idx j_14) (o j_14)))) polyH59; have polyH61 := Poly.add polyH4 polyH60; have polyH62 := Poly.const (s) (2 * volume (Bool.false :: @List.nil Bool) + 1); have polyH63 := Poly.const (s) (50 * volume (Bool.false :: @List.nil Bool)); have polyH64 := Poly.add polyH7 polyH63; have polyH65 := Poly.add polyH64 polyH10; have polyH66 := Poly.mul polyH62 polyH65; have polyH67 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_constant (I) (fun (i : I) => Option (List ℕ)) _ (List Bool) _ (Bool.false :: @List.nil Bool) (idx j_14) (o j_14)))) polyH66; have polyH68 := Poly.add polyH61 polyH67; have polyH69 := Poly.const (s) (1000); have polyH70 := Poly.lengthCons (fun (j_1 : J) => Prod.fst ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1))) (fun (j_1 : J) => Prod.snd ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1))) (hEncoded); have polyH71 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => Prod.fst ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1)) :: Prod.snd ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1))) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => Prod.fst ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1)) :: Prod.snd ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1))) => (Sigma.snd q).1); have polyH72 := Poly.listVolume (fun (j_1 : J) => Prod.fst ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1)) :: Prod.snd ((fun (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (o j_1))) polyH70 polyH71; have polyH73 := Poly.add (hO) polyH72; have polyH74 := Poly.const (s) (volume (Bool.false :: @List.nil Bool)); have polyH75 := Poly.add polyH73 polyH74; have polyH76 := Poly.add polyH75 polyH1; have polyH77 := Poly.mul polyH69 polyH76; have polyH78 := Poly.add polyH68 polyH77; have polyH79 := Poly.of_le (fun (j_14 : J) => (@Uniform.time_ite_le (I) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List Bool) _ _ (fun (i : I) (x : Option (List ℕ)) => Option.isSome x) (fun (i : I) (x : Option (List ℕ)) => (fun (x_1 : Bool × List Bool) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_2 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Option (List ℕ)) => (x_2, @List.nil ℕ)) x_1)))) x)) (fun (i : I) (x : Option (List ℕ)) => Bool.false :: @List.nil Bool) (@Uniform.optionIsSome I (fun (i : I) => List ℕ) _) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Bool × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (Bool.true, (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)))) (fun (i : I) (x : Bool × List Bool) => Prod.fst x :: Prod.snd x) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Bool) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => Bool.true) (fun (i : I) (x : Option (List ℕ)) => (fun (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) ((fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x))) (@Uniform.constant I (fun (i : I) => Option (List ℕ)) _ Bool _ Bool.true) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) (fun (x : I) => List Bool) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (fun (x_1 : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Option (List ℕ)) => (x_1, @List.nil ℕ)) x)) (fun (x : I) (xs : List ℕ) => OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat xs) (@Uniform.comp I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ) × List ℕ) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => (x, @List.nil ℕ)) (fun (i : I) (x : Option (List ℕ) × List ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => Option (List ℕ)) (fun (i : I) => Option (List ℕ)) (fun (i : I) => List ℕ) _ _ _ (fun (i : I) (x : Option (List ℕ)) => x) (fun (i : I) (x : Option (List ℕ)) => @List.nil ℕ) (@Uniform.id I (fun (i : I) => Option (List ℕ)) _) (@Uniform.nil I (fun (i : I) => Option (List ℕ)) (fun (i : I) => ℕ) _ _)) (@Uniform.getD I (fun (i : I) => List ℕ) _)) (@Uniform.binaryEncodeList I))) (@Uniform.cons I (fun (i : I) => Bool) _)) (@Uniform.constant I (fun (i : I) => Option (List ℕ)) _ (List Bool) _ (Bool.false :: @List.nil Bool)) (idx j_14) (o j_14))) polyH78; exact Poly.lift polyH79 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module RequestBounds
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler
namespace Request

end Request
namespace Binary

theorem input_eq {n : ℕ} (G : Instance n) (d : Option ℕ) :
    ThreeMachine.encodeInput G d = encodeHeader d ++
      (ThreeMachine.encodeList ThreeMachine.encodeNat (vertices n) ++
        ThreeMachine.encodeList encodeEdge (edges G)) := by
  rw [ThreeMachine.encodeInput.eq_def,encodeEdges_map]
  cases d <;> simp only [encodeHeader,List.append_assoc,vertices,edges]

theorem readHeader_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    readHeader (ThreeMachine.encodeInput G d) =
      (d,ThreeMachine.encodeList ThreeMachine.encodeNat (vertices n) ++
        ThreeMachine.encodeList encodeEdge (edges G)) := by
  rw [input_eq,readHeader_correct]

theorem readVertices_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    readList readNat (readHeader (ThreeMachine.encodeInput G d)).2 =
      (vertices n, ThreeMachine.encodeList encodeEdge (edges G)) := by
  rw [readHeader_input,readList_correct readNat_encodeNat]

theorem readEdges_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    readList readEdge (readList readNat (readHeader (ThreeMachine.encodeInput G d)).2).2 =
      (edges G, []) := by
  rw [readVertices_input]
  simpa only [List.append_nil] using readList_correct readEdge_correct (edges G) []

theorem readNat_tail_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    (readNat (ThreeMachine.encodeInput G d).tail).1 = d.getD n := by
  rw [input_eq]
  cases d with
  | none =>
    simp only [encodeHeader,List.cons_append,List.nil_append,List.tail_cons,Option.getD_none,
      ThreeMachine.encodeList,List.append_assoc,readNat_encodeNat,List.length_map,List.length_range,vertices]
  | some T =>
    simp only [encodeHeader,List.cons_append,List.tail_cons,readNat_encodeNat,Option.getD_some]

theorem encodeNat_pos (n : ℕ) : 1 ≤ (ThreeMachine.encodeNat n).length := by
  simp only [ThreeMachine.encodeNat,List.length_append,List.length_replicate,List.length_cons]
  omega

theorem length_le_flatMap_encode {α : Type} (enc : α → List Bool) (h : ∀ a, 1 ≤ (enc a).length) (xs : List α) :
    xs.length ≤ (xs.flatMap enc).length := by
  induction xs with
  | nil => exact le_rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_cons,List.length_append]
    have := h a
    omega

theorem length_le_encodeList {α : Type} (enc : α → List Bool) (h : ∀ a, 1 ≤ (enc a).length) (xs : List α) :
    xs.length ≤ (ThreeMachine.encodeList enc xs).length := by
  have := length_le_flatMap_encode enc h xs
  simp only [ThreeMachine.encodeList,List.length_append]
  omega

theorem input_length_bounds {n : ℕ} (G : Instance n) (d : Option ℕ) :
    n ≤ (ThreeMachine.encodeInput G d).length ∧ G.edges.length ≤ (ThreeMachine.encodeInput G d).length := by
  have hv := length_le_encodeList ThreeMachine.encodeNat encodeNat_pos (vertices n)
  have he := length_le_encodeList encodeEdge (fun e => by
    have := encodeNat_pos (e.1+1)
    simp only [encodeEdge,List.length_append]
    omega) (edges G)
  have hv' : n ≤ (ThreeMachine.encodeList ThreeMachine.encodeNat (vertices n)).length := by
    simpa only [vertices,List.length_map,List.length_range] using hv
  have he' : G.edges.length ≤ (ThreeMachine.encodeList encodeEdge (edges G)).length := by
    simpa only [edges,List.length_map] using he
  rw [input_eq]
  simp only [List.length_append]
  omega
end Binary

theorem requestSize_le {n : ℕ} (x : Request n) (hd : x.deadline.getD 0 ≤ n) :
    x.size ≤ 4*(ThreeMachine.encodeInput x.graph x.deadline).length := by
  have h := Binary.input_length_bounds x.graph x.deadline
  dsimp [Request.size]
  omega
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace RequestData

theorem nPoly : Poly size (fun x => x.1) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,Request.size]; omega

theorem edgesPoly : Poly size (fun x => x.2.graph.edges.length) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,Request.size]; omega

theorem deadlinePoly : Poly size (fun x => x.2.deadline.getD 0) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,Request.size]; omega

theorem bitsPoly : Poly size (fun x => (bits x).length) 1 := by
  apply Poly.of_le _ (Poly.size size)
  intro x; dsimp [size,bits,Request.size]; omega

theorem vrestPoly : Poly size (fun x => (vbytes x ++ ebytes x).length) 1 := by
  apply Poly.of_le _ bitsPoly
  intro x
  dsimp [bits,vbytes,ebytes]
  rw [Binary.input_eq]
  simp only [List.length_append]
  omega

theorem ebytesPoly : Poly size (fun x => (ebytes x).length) 1 := by
  apply Poly.of_le _ vrestPoly
  intro x; simp only [List.length_append]; omega

theorem verticesLength : Poly size (fun x => (Binary.vertices x.1).length) 1 := by
  simpa only [Binary.vertices,List.length_map,List.length_range] using nPoly

theorem edgesLength : Poly size (fun x => (Binary.edges x.2.graph).length) 1 := by
  simpa only [Binary.edges,List.length_map] using edgesPoly

theorem verticesBound (x : Index) (a : ℕ) (ha : a ∈ Binary.vertices x.1) : a ≤ x.1 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hk
  omega

theorem edgesBound (x : Index) (a : ℕ × ℕ) (ha : a ∈ Binary.edges x.2.graph) :
    a.1 ≤ x.1 ∧ a.2 ≤ x.1 := by
  obtain ⟨e,_he,rfl⟩ := List.mem_map.mp ha
  exact ⟨Nat.le_of_lt e.1.isLt,Nat.le_of_lt e.2.isLt⟩

theorem volumeDeadline : Poly size (fun x => volume x.2.deadline) 1 := by
  have h : Poly size (fun x => volume (x.2.deadline.getD 0)) 1 := Poly.volumeNat deadlinePoly
  apply Poly.of_le (fun x : Index => volume_option_le_getD x.2.deadline 0)
  (have polyH0 := Poly.const (RequestData.size) (2); have polyH1 := Poly.add (h) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem volumeVertices : Poly size (fun x => volume (Binary.vertices x.1)) 2 := by
  have hK : Poly size (fun x => 2*x.1+1) 1 := by
    have hn := nPoly
    (have polyH0 := Poly.const (RequestData.size) (2); have polyH1 := Poly.mul polyH0 (hn); have polyH2 := Poly.const (RequestData.size) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  apply Poly.volumeList verticesLength hK
  intro x a ha
  rw [volume_nat]
  have := verticesBound x a ha
  omega

theorem volumeEdges : Poly size (fun x => volume (Binary.edges x.2.graph)) 2 := by
  have hK : Poly size (fun x => 4*x.1+3) 1 := by
    have hn := nPoly
    (have polyH0 := Poly.const (RequestData.size) (4); have polyH1 := Poly.mul polyH0 (hn); have polyH2 := Poly.const (RequestData.size) (3); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  apply Poly.volumeList edgesLength hK
  intro x a ha
  rw [volume_prod,volume_nat,volume_nat]
  have := edgesBound x a ha
  omega

theorem volumeVrest : Poly size (fun x => volume (vbytes x ++ ebytes x)) 1 := by
  apply Poly.of_le (fun x : Index => volume_boolList_le (vbytes x ++ ebytes x))
  have h := vrestPoly
  (have polyH0 := Poly.const (RequestData.size) (4); have polyH1 := Poly.mul polyH0 (h); have polyH2 := Poly.const (RequestData.size) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem volumeEbytes : Poly size (fun x => volume (ebytes x)) 1 := by
  apply Poly.of_le (fun x : Index => volume_boolList_le (ebytes x))
  have h := ebytesPoly
  (have polyH0 := Poly.const (RequestData.size) (4); have polyH1 := Poly.mul polyH0 (h); have polyH2 := Poly.const (RequestData.size) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem volumeGraph : Poly size (fun x => volume x.2.graph) 2 :=
  Poly.volumeInstance (fun x => x.2.graph) nPoly edgesPoly

theorem volumeRequest : Poly size (fun x => volume x.2) 1 := by
  change Poly size (fun x => volume (bits x)) 1
  apply Poly.of_le (fun x : Index => volume_boolList_le (bits x))
  have h := bitsPoly
  (have polyH0 := Poly.const (RequestData.size) (4); have polyH1 := Poly.mul polyH0 (h); have polyH2 := Poly.const (RequestData.size) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end RequestData
end ThreeMachine.StackCompiler
end

end OAI
end

section
-- module ReaderCosts
namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Costs
open RequestData

theorem requestSlotsLength : Poly size (fun x : Index => ((requestSlots x).getD []).length) 1 :=
  Poly.of_le (fun _x => answerMatrix_length _ _) nPoly

theorem requestSlotsBound : Poly (fun p : Poly.ListPool (fun x : Index => (requestSlots x).getD []) => size p.1)
    (fun p => p.2.1) 1 := by
  apply Poly.of_le (fun p : Poly.ListPool (fun x : Index => (requestSlots x).getD []) =>
    answerMatrix_bound (closureMatrix p.1.2.graph p.1.1) p.1.2.deadline p.2.2)
  have hn := nPoly.precomp (Sigma.fst : Poly.ListPool (fun x : Index => (requestSlots x).getD []) → Index)
  have hd := deadlinePoly.precomp (Sigma.fst : Poly.ListPool (fun x : Index => (requestSlots x).getD []) → Index)
  (have polyH0 := Poly.const (fun (p_1 : Poly.ListPool fun (x : RequestData.Index) => Option.getD (Costs.requestSlots x) []) => RequestData.size (Sigma.fst p_1)) (3); have polyH1 := Poly.add (hn) (hd); have polyH2 := Poly.mul polyH0 polyH1; exact Poly.lift polyH2 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem requestSlotsVolume : Poly size (fun x : Index => volume (requestSlots x)) 2 := by
  have hi : Poly (fun p : Poly.ListPool (fun x : Index => (requestSlots x).getD []) => size p.1)
      (fun p => volume p.2.1) 1 := Poly.volumeNat requestSlotsBound
  have hv := Poly.volumeListOfPool (fun x : Index => (requestSlots x).getD []) requestSlotsLength hi
  apply Poly.of_le (fun x : Index => volume_option_le_getD (requestSlots x) [])
  (have polyH0 := Poly.const (RequestData.size) (2); have polyH1 := Poly.add (hv) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem requestEncodeAnswer : Poly size
    (fun x : Index => (Uniform.binaryEncodeAnswer (I := ℕ)).time x.1 (requestSlots x)) 5 :=
  binaryEncodeAnswer size Sigma.fst requestSlots requestSlotsLength requestSlotsBound

theorem requestOutputLength : Poly size (fun x : Index => (Algorithm.output x.2.graph x.2.deadline).length) 2 := by
  have he := lengthEncodeNatList size (fun x : Index => (requestSlots x).getD []) requestSlotsLength requestSlotsBound
  have hb (x : Index) : (ThreeMachine.encodeAnswer (requestSlots x)).length ≤
      1+(ThreeMachine.encodeList ThreeMachine.encodeNat ((requestSlots x).getD [])).length := by
    cases requestSlots x <;> simp only [ThreeMachine.encodeAnswer,Option.getD_none,Option.getD_some,
      List.length_cons,List.length_nil] <;> omega
  have ho : ∀ x : Index, ThreeMachine.encodeAnswer (requestSlots x) = Algorithm.output x.2.graph x.2.deadline :=
    fun x => answerMatrix_closure x.2.graph x.2.deadline
  apply Poly.of_le (g := fun x : Index => 1+(ThreeMachine.encodeList ThreeMachine.encodeNat ((requestSlots x).getD [])).length) (fun x : Index => by rw [← ho x]; exact hb x)
  (have polyH0 := Poly.const (RequestData.size) (1); have polyH1 := Poly.add polyH0 (he); exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]
theorem time_binaryReadStep_le {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (i : I) (bs : List Bool) (acc : List (α i)) :
    R.binaryReadStep.time i (bs,acc) ≤ 1000*(R.time i bs+volume bs+volume acc+volume (reader i bs)+1) := by
  unfold binaryReadStep
  erw [time_congr]
  simp only [time_pair,time_comp,time_fst,time_snd,time_cons,Function.comp_def,volume_pair,volume_cons]
  have hv := volume_pair (reader i bs).1 (reader i bs).2
  simp only [Prod.mk.eta] at hv
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} {α : I → Type} [∀ i, Coding (α i)]
variable (s : J → ℕ) (idx : J → I)
theorem binaryReadStep {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (bs : J → List Bool) (acc : ∀ j, List (α (idx j))) {d : ℕ}
    (ht : Poly s (fun j => R.time (idx j) (bs j)) d)
    (hb : Poly s (fun j => volume (bs j)) d)
    (ha : Poly s (fun j => volume (acc j)) d)
    (hv : Poly s (fun j => volume (reader (idx j) (bs j))) d) :
    Poly s (fun j => R.binaryReadStep.time (idx j) (bs j,acc j)) d := by
  apply Poly.of_le (fun j : J => Uniform.time_binaryReadStep_le R (idx j) (bs j) (acc j))
  (have polyH0 := Poly.const (s) (1000); have polyH1 := Poly.add (ht) (hb); have polyH2 := Poly.add polyH1 (ha); have polyH3 := Poly.add polyH2 (hv); have polyH4 := Poly.const (s) (1); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.mul polyH0 polyH5; exact Poly.lift polyH6 (by first | decide +kernel | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u2}
theorem flatMap_drop_length (enc : α → List Bool) (xs : List α) (k : ℕ) (rest : List Bool) :
    ((xs.drop k).flatMap enc ++ rest).length ≤ (xs.flatMap enc ++ rest).length := by
  have h := congrArg List.length ((List.flatMap_append (xs := xs.take k) (ys := xs.drop k) (f := enc)))
  rw [List.take_append_drop] at h
  simp only [List.length_append] at h ⊢
  omega
end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u3} {α : I → Type} [∀ i, Coding (α i)]
theorem time_binaryReadMany_le {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (i : I) (k : ℕ) (bs : List Bool) :
    R.binaryReadMany.time i (k,bs) ≤ 1000*(R.binaryReadStep.iterate.time i (k,(bs,[]))+
      (reverse (I := I) (α := α)).time i (((Binary.readStep (reader i))^[k] (bs,[])).2)+
      volume bs+k+volume ((Binary.readStep (reader i))^[k] (bs,[]))+1) := by
  unfold binaryReadMany
  erw [time_congr]
  simp only [time_comp,time_pair,time_fst,time_snd,time_nil,volume_pair,volume_nil,volume_nat,
    Function.comp_def,volume_reverse]
  have hv := volume_pair (((Binary.readStep (reader i))^[k] (bs,[])).1)
    (((Binary.readStep (reader i))^[k] (bs,[])).2)
  simp only [Prod.mk.eta] at hv
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} {α : I → Type} [∀ i, Coding (α i)]
variable (s : J → ℕ) (idx : J → I)
theorem binaryReadManyEncoded {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (encode : ∀ i, α i → List Bool)
    (hr : ∀ i a rest, reader i (encode i a ++ rest) = (a,rest))
    (xs : ∀ j, List (α (idx j))) (rest : J → List Bool)
    (hl : Poly s (fun j => (xs j).length) 1)
    (hb : Poly s (fun j => ((xs j).flatMap (encode (idx j)) ++ rest j).length) 1)
    (hx : Poly s (fun j => volume (xs j)) 2)
    (ht : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => R.time (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)) 3)
    (hv : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => volume (reader (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1))) 2) :
    Poly s (fun j => R.binaryReadMany.time (idx j) ((xs j).length,(xs j).flatMap (encode (idx j)) ++ rest j)) 4 := by
  let m j := (xs j).length
  let a j := ((xs j).flatMap (encode (idx j)) ++ rest j,([] : List (α (idx j))))
  have hp (p : Poly.IterPool m) : (Binary.readStep (reader (idx p.1)))^[p.2.1] (a p.1) =
      (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1,((xs p.1).take p.2.1).reverse) := by
    simpa only [a,List.append_nil] using Binary.readStep_prefix (hr (idx p.1)) (xs p.1) (rest p.1) [] p.2.1 (by have := p.2.2; dsimp [m] at *; omega)
  have hrem : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1).length) 1 :=
    Poly.of_le (fun p : Poly.IterPool m => Binary.flatMap_drop_length _ _ _ _) (hb.precomp Sigma.fst)
  have hbrem : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => volume (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (p_1 : Poly.IterPool m) => List.flatMap (encode (idx (Sigma.fst p_1))) (List.drop (Fin.val (Sigma.snd p_1)) (xs (Sigma.fst p_1))) ++ rest (Sigma.fst p_1)) => (fun (p_1 : Poly.IterPool m) => s (Sigma.fst p_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (p_1 : Poly.IterPool m) => List.flatMap (encode (idx (Sigma.fst p_1))) (List.drop (Fin.val (Sigma.snd p_1)) (xs (Sigma.fst p_1))) ++ rest (Sigma.fst p_1)) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (p_1 : Poly.IterPool m) => List.flatMap (encode (idx (Sigma.fst p_1))) (List.drop (Fin.val (Sigma.snd p_1)) (xs (Sigma.fst p_1))) ++ rest (Sigma.fst p_1)) (hrem) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hac : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => volume (((xs p.1).take p.2.1).reverse)) 2 := by
    simp only [volume_reverse]
    exact Poly.of_le (fun p : Poly.IterPool m => volume_sublist (List.take_sublist _ _)) (hx.precomp Sigma.fst)
  have hvol : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => volume ((Binary.readStep (reader (idx p.1)))^[p.2.1] (a p.1))) 2 := by
    simp only [hp,volume_pair]
    (have polyH0 := Poly.add (hbrem) (hac); have polyH1 := Poly.const (fun (p_1 : Poly.IterPool m) => s (Sigma.fst p_1)) (1); have polyH2 := Poly.add polyH0 polyH1; exact Poly.lift polyH2 (by first | decide +kernel | omega))
  let inc (p : Poly.StrictIterPool m) : Poly.IterPool m := ⟨p.1,⟨p.2.1,by have := p.2.2; omega⟩⟩
  have hstep := binaryReadStep (fun p : Poly.StrictIterPool m => s p.1) (fun p => idx p.1) R
    (fun p => ((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)
    (fun p => ((xs p.1).take p.2.1).reverse) ht
    ((hbrem.precomp inc).lift (by decide)) ((hac.precomp inc).lift (by decide)) (hv.lift (by decide))
  have hti : Poly (fun p : Poly.StrictIterPool m => s p.1)
      (fun p => R.binaryReadStep.time (idx p.1) ((Binary.readStep (reader (idx p.1)))^[p.2.1] (a p.1))) 3 := by
    convert hstep using 1
    funext p
    rw [hp (inc p)]
  have hIter := Poly.iterateTimeStrict R.binaryReadStep idx m a hl hti hvol
  have hOut : Poly s (fun j => volume ((Binary.readStep (reader (idx j)))^[m j] (a j))) 2 :=
    hvol.precomp (fun j => ⟨j,⟨m j,by omega⟩⟩)
  have hRev : Poly s (fun j => ((Binary.readStep (reader (idx j)))^[m j] (a j)).2.length) 1 := by
    have he (j : J) := hp ⟨j,⟨m j,by omega⟩⟩
    simp only [he,List.length_reverse,List.length_take,m,Nat.min_self]
    exact hl
  have hSndVol : Poly s (fun j => volume (((Binary.readStep (reader (idx j)))^[m j] (a j)).2)) 2 := by
    apply Poly.of_le _ hOut
    intro j
    let t := (Binary.readStep (reader (idx j)))^[m j] (a j)
    have he := volume_pair t.1 t.2
    simp only [Prod.mk.eta] at he
    change volume t.2 ≤ volume t
    omega
  have hRevTime : Poly s (fun j => (Uniform.reverse (I := I) (α := α)).time (idx j)
      (((Binary.readStep (reader (idx j)))^[m j] (a j)).2)) 3 := by
    apply Poly.of_le (fun j : J => Uniform.time_reverse (idx j) (((Binary.readStep (reader (idx j)))^[m j] (a j)).2))
    (have polyH0 := Poly.const (s) (200); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hRev) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hSndVol) polyH1; have polyH5 := Poly.mul polyH3 polyH4; exact Poly.lift polyH5 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hbs : Poly s (fun j => volume ((xs j).flatMap (encode (idx j)) ++ rest j)) 1 := by (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.flatMap (encode (idx j_1)) (xs j_1) ++ rest j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.flatMap (encode (idx j_1)) (xs j_1) ++ rest j_1) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (j_1 : J) => List.flatMap (encode (idx j_1)) (xs j_1) ++ rest j_1) (hb) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  apply Poly.of_le (fun j : J => Uniform.time_binaryReadMany_le R (idx j) (xs j).length
    ((xs j).flatMap (encode (idx j)) ++ rest j))
  (have polyH0 := Poly.const (s) (1000); have polyH1 := Poly.add (hIter) (hRevTime); have polyH2 := Poly.add polyH1 (hbs); have polyH3 := Poly.add polyH2 (hl); have polyH4 := Poly.add polyH3 (hOut); have polyH5 := Poly.const (s) (1); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.mul polyH0 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module ListParserCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type}
theorem readNat_listHeader (enc : α → List Bool) (xs : List α) (rest : List Bool) :
    readNat (ThreeMachine.encodeList enc xs ++ rest) = (xs.length,xs.flatMap enc ++ rest) := by
  simp only [ThreeMachine.encodeList,List.append_assoc,readNat_encodeNat]
theorem readAtSuffix {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool)
    (k : ℕ) (hk : k < xs.length) :
    reader ((xs.drop k).flatMap encode ++ rest) = (xs[k],(xs.drop (k+1)).flatMap encode ++ rest) := by
  rw [List.drop_eq_getElem_cons hk,List.flatMap_cons,List.append_assoc,hr]
end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler.Realizer
theorem time_pred (n : ℕ) : pred.time n = volume n+2 := rfl
end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type} {α : I → Type} [∀ i, Coding (α i)]
theorem time_binaryReadList {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (i : I) (bs : List Bool) :
    R.binaryReadList.time i bs = binaryReadNat.time i bs +
      R.binaryReadMany.time i (Binary.readNat bs)+10*(volume (Binary.readNat bs)+1) := by
  change (binaryReadNat.comp R.binaryReadMany).time i bs = _
  exact time_comp _ _ _ _
theorem time_binaryReadEdge_le (i : I) (bs : List Bool) :
    (binaryReadEdge (I := I)).time i bs ≤ 1000*(binaryReadNat.time i bs+
      binaryReadNat.time i (Binary.readNat bs).2+volume bs+
      volume (Binary.readNat bs)+volume (Binary.readNat (Binary.readNat bs).2)+1) := by
  let A := binaryReadNat (I := I)
  let B := A.comp (snd.comp binaryReadNat)
  change (((A.comp (fst.comp (Realizer.pred.uniform I))).pair
      (B.comp (fst.comp (Realizer.pred.uniform I)))).pair (B.comp snd)).time i bs ≤ _
  simp only [A,B,time_pair,time_comp,time_snd,time_fst,time_uniform,Realizer.time_pred,
    Function.comp_apply,volume_prod,volume_nat,Nat.pred_eq_sub_one]
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

theorem volumeNatBools (k : J → ℕ) (bs : J → List Bool)
    (hk : Poly s k 1) (hb : Poly s (fun j => (bs j).length) 1) :
    Poly s (fun j => volume (k j,bs j)) 1 := by
  have hv := Poly.of_le (fun j : J => volume_boolList_le (bs j))
    (show Poly s (fun j => 4*(bs j).length+1) 1 from by (have polyH0 := Poly.const (s) (4); have polyH1 := Poly.mul polyH0 (hb); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega)))
  simp only [volume_pair,volume_nat]
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hk); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.add polyH3 (hv); have polyH5 := Poly.add polyH4 polyH2; exact Poly.lift polyH5 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryReadNatEncoded (k : J → ℕ) (rest : J → List Bool)
    (hk : Poly s k 1) (hl : Poly s (fun j => (ThreeMachine.encodeNat (k j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (ThreeMachine.encodeNat (k j) ++ rest j)) 3 := by
  apply binaryReadNat s idx _ hl
  simpa only [Binary.readNat_encodeNat] using hk

theorem binaryReadEdgeCost (bs : J → List Bool)
    (hA : Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (bs j)) 3)
    (hB : Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (Binary.readNat (bs j)).2) 3)
    (hvI : Poly s (fun j => volume (bs j)) 1)
    (hvA : Poly s (fun j => volume (Binary.readNat (bs j))) 1)
    (hvB : Poly s (fun j => volume (Binary.readNat (Binary.readNat (bs j)).2)) 1) :
    Poly s (fun j => (Uniform.binaryReadEdge (I := I)).time (idx j) (bs j)) 3 := by
  apply Poly.of_le (fun j : J => Uniform.time_binaryReadEdge_le (idx j) (bs j))
  (have polyH0 := Poly.const (s) (1000); have polyH1 := Poly.add (hA) (hB); have polyH2 := Poly.add polyH1 (hvI); have polyH3 := Poly.add polyH2 (hvA); have polyH4 := Poly.add polyH3 (hvB); have polyH5 := Poly.const (s) (1); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.mul polyH0 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryReadEdgeEncoded (edge : J → ℕ × ℕ) (rest : J → List Bool)
    (ha : Poly s (fun j => (edge j).1) 1) (hb : Poly s (fun j => (edge j).2) 1)
    (hl : Poly s (fun j => (Binary.encodeEdge (edge j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadEdge (I := I)).time (idx j) (Binary.encodeEdge (edge j) ++ rest j)) 3 := by
  have he (j) : Binary.readNat (Binary.encodeEdge (edge j) ++ rest j) =
      ((edge j).1+1,ThreeMachine.encodeNat ((edge j).2+1) ++ rest j) := by
    simp only [Binary.encodeEdge,List.append_assoc,Binary.readNat_encodeNat]
  have ha1 : Poly s (fun j => (edge j).1+1) 1 := ha.add (Poly.const s 1)
  have hb1 : Poly s (fun j => (edge j).2+1) 1 := hb.add (Poly.const s 1)
  have hA := binaryReadNat s idx (fun j => Binary.encodeEdge (edge j) ++ rest j) hl
    (show Poly s (fun j => (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j)).1) 1 from by
      simpa only [he] using ha1)
  have hRest : Poly s (fun j => (ThreeMachine.encodeNat ((edge j).2+1) ++ rest j).length) 1 := by
    apply Poly.of_le _ hl
    intro j
    simp only [List.length_append,Binary.encodeEdge]
    omega
  have hB := binaryReadNatEncoded s idx (fun j => (edge j).2+1) rest hb1 hRest
  have hvA : Poly s (fun j => volume (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j))) 1 := by
    simp only [he]
    exact volumeNatBools s (fun j => (edge j).1+1) _ ha1 hRest
  have hrl : Poly s (fun j => (rest j).length) 1 :=
    Poly.of_le (fun j : J => by simp only [List.length_append]; omega) hRest
  have hvB : Poly s (fun j => volume (Binary.readNat (ThreeMachine.encodeNat ((edge j).2+1) ++ rest j))) 1 := by
    simp only [Binary.readNat_encodeNat]
    exact volumeNatBools s (fun j => (edge j).2+1) _ hb1 hrl
  have hExact : Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j)
      (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j)).2) 3 := by simpa only [he] using hB
  have hvExact : Poly s (fun j => volume (Binary.readNat (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j)).2)) 1 := by
    simpa only [he] using hvB
  have hvIn : Poly s (fun j => volume (Binary.encodeEdge (edge j) ++ rest j)) 1 :=
    Poly.of_le (fun j => volume_boolList_le _) ((Poly.const s 4 |>.mul hl).add (Poly.const s 1))
  exact binaryReadEdgeCost s idx _ hA hExact hvIn hvA hvExact

variable {α : I → Type} [∀ i, Coding (α i)]
theorem binaryReadListEncoded {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (encode : ∀ i, α i → List Bool)
    (hr : ∀ i a rest, reader i (encode i a ++ rest) = (a,rest))
    (xs : ∀ j, List (α (idx j))) (rest : J → List Bool)
    (hl : Poly s (fun j => (xs j).length) 1)
    (hb : Poly s (fun j => (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j).length) 1)
    (hx : Poly s (fun j => volume (xs j)) 2)
    (ht : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => R.time (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)) 3)
    (hv : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => volume (reader (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1))) 2) :
    Poly s (fun j => R.binaryReadList.time (idx j) (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j)) 4 := by
  have hpay : Poly s (fun j => ((xs j).flatMap (encode (idx j)) ++ rest j).length) 1 := by
    apply Poly.of_le _ hb
    intro j
    simp only [ThreeMachine.encodeList,List.length_append]
    omega
  have hM := binaryReadManyEncoded s idx R encode hr xs rest hl hpay hx ht hv
  have hN := binaryReadNat s idx (fun j => ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j) hb
    (show Poly s (fun j => (Binary.readNat (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j)).1) 1 from by
      simpa only [Binary.readNat_listHeader] using hl)
  have hExact : Poly s (fun j => R.binaryReadMany.time (idx j)
      (Binary.readNat (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j))) 4 := by
    simpa only [Binary.readNat_listHeader] using hM
  have hvN : Poly s (fun j => volume (Binary.readNat (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j))) 1 := by
    simp only [Binary.readNat_listHeader]
    exact volumeNatBools s _ _ hl hpay
  simp only [Uniform.time_binaryReadList]
  (have polyH0 := Poly.add (hN) (hExact); have polyH1 := Poly.const (s) (10); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add (hvN) polyH2; have polyH4 := Poly.mul polyH1 polyH3; have polyH5 := Poly.add polyH0 polyH4; exact Poly.lift polyH5 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem binaryNatList (xs : J → List ℕ) (rest : J → List Bool) (K : J → ℕ)
    (hl : Poly s (fun j => (xs j).length) 1) (hK : Poly s K 1)
    (hB : ∀ j a, a ∈ xs j → a ≤ K j)
    (hb : Poly s (fun j => (ThreeMachine.encodeList ThreeMachine.encodeNat (xs j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadNat (I := I)).binaryReadList.time (idx j)
      (ThreeMachine.encodeList ThreeMachine.encodeNat (xs j) ++ rest j)) 4 := by
  let P := Poly.StrictIterPool (fun j => (xs j).length)
  let sp (p : P) := s p.1
  let a (p : P) := (xs p.1)[p.2.val]
  let suf (p : P) := ((xs p.1).drop p.2.val).flatMap ThreeMachine.encodeNat ++ rest p.1
  have hpay : Poly s (fun j => ((xs j).flatMap ThreeMachine.encodeNat ++ rest j).length) 1 := by
    apply Poly.of_le _ hb
    intro j
    simp only [ThreeMachine.encodeList,List.length_append]
    omega
  have hsuf : Poly sp (fun p => (suf p).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have hafter : Poly sp (fun p => (((xs p.1).drop (p.2.val+1)).flatMap ThreeMachine.encodeNat ++ rest p.1).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have ha : Poly sp a 1 := Poly.of_le (fun p => hB p.1 (a p) (List.getElem_mem _)) (hK.precomp Sigma.fst)
  have he (p : P) : Binary.readNat (suf p) =
      (a p,((xs p.1).drop (p.2.val+1)).flatMap ThreeMachine.encodeNat ++ rest p.1) :=
    Binary.readAtSuffix Binary.readNat_encodeNat (xs p.1) (rest p.1) _ p.2.isLt
  have hval : Poly sp (fun p => (Binary.readNat (suf p)).1) 1 := by simpa only [he] using ha
  have hT := binaryReadNat sp (fun p => idx p.1) suf hsuf hval
  have hV : Poly sp (fun p => volume (Binary.readNat (suf p))) 2 := by
    simp only [he]
    exact (volumeNatBools sp a _ ha hafter).lift (by omega)
  have hX : Poly s (fun j => volume (xs j)) 2 := by
    apply Poly.volumeList hl (show Poly s (fun j => 2*K j+1) 1 from by (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.mul polyH0 (hK); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega)))
    intro j a ha
    rw [volume_nat]
    have := hB j a ha
    omega
  exact binaryReadListEncoded s idx (Uniform.binaryReadNat (I := I)) (fun _ => ThreeMachine.encodeNat)
    (fun _ => Binary.readNat_encodeNat) xs rest hl hb hX hT hV
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem binaryEdgeList (xs : J → List (ℕ × ℕ)) (rest : J → List Bool) (K : J → ℕ)
    (hl : Poly s (fun j => (xs j).length) 1) (hK : Poly s K 1)
    (hB : ∀ j a, a ∈ xs j → a.1 ≤ K j ∧ a.2 ≤ K j)
    (hb : Poly s (fun j => (ThreeMachine.encodeList Binary.encodeEdge (xs j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadEdge (I := I)).binaryReadList.time (idx j)
      (ThreeMachine.encodeList Binary.encodeEdge (xs j) ++ rest j)) 4 := by
  let P := Poly.StrictIterPool (fun j => (xs j).length)
  let sp (p : P) := s p.1
  let a (p : P) := (xs p.1)[p.2.val]
  let suf (p : P) := ((xs p.1).drop p.2.val).flatMap Binary.encodeEdge ++ rest p.1
  have hpay : Poly s (fun j => ((xs j).flatMap Binary.encodeEdge ++ rest j).length) 1 := by
    apply Poly.of_le _ hb
    intro j
    simp only [ThreeMachine.encodeList,List.length_append]
    omega
  have hsuf : Poly sp (fun p => (suf p).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have hafter : Poly sp (fun p => (((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have ha : Poly sp (fun p => (a p).1) 1 :=
    Poly.of_le (fun p => (hB p.1 (a p) (List.getElem_mem _)).1) (hK.precomp Sigma.fst)
  have hc : Poly sp (fun p => (a p).2) 1 :=
    Poly.of_le (fun p => (hB p.1 (a p) (List.getElem_mem _)).2) (hK.precomp Sigma.fst)
  have hs (p : P) : suf p = Binary.encodeEdge (a p) ++
      ((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1 := by
    dsimp [suf,a]
    rw [List.drop_eq_getElem_cons p.2.isLt,List.flatMap_cons,List.append_assoc]
  have hlenc : Poly sp (fun p => (Binary.encodeEdge (a p) ++
      (((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1)).length) 1 := by
    simpa only [hs,List.append_assoc] using hsuf
  have hT0 := binaryReadEdgeEncoded sp (fun p => idx p.1) a
    (fun p => ((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1) ha hc hlenc
  have hT : Poly sp (fun p => (Uniform.binaryReadEdge (I := I)).time (idx p.1) (suf p)) 3 := by
    simpa only [hs,List.append_assoc] using hT0
  have he (p : P) : Binary.readEdge (suf p) =
      (a p,((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1) :=
    Binary.readAtSuffix Binary.readEdge_correct (xs p.1) (rest p.1) _ p.2.isLt
  have hV : Poly sp (fun p => volume (Binary.readEdge (suf p))) 2 := by
    simp only [he,volume_prod,volume_nat]
    have hbV := Poly.of_le (fun p : P => volume_boolList_le
      (((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1))
      (show Poly sp (fun p => 4*((((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1).length)+1) 1 from by (have polyH0 := Poly.const (sp) (4); have polyH1 := Poly.mul polyH0 (hafter); have polyH2 := Poly.const (sp) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega)))
    (have polyH0 := Poly.const (sp) (2); have polyH1 := Poly.mul polyH0 (ha); have polyH2 := Poly.const (sp) (1); have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.mul polyH0 (hc); have polyH5 := Poly.add polyH4 polyH2; have polyH6 := Poly.add polyH3 polyH5; have polyH7 := Poly.add polyH6 polyH2; have polyH8 := Poly.add polyH7 (hbV); have polyH9 := Poly.add polyH8 polyH2; exact Poly.lift polyH9 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hX : Poly s (fun j => volume (xs j)) 2 := by
    apply Poly.volumeList hl (show Poly s (fun j => 4*K j+3) 1 from by (have polyH0 := Poly.const (s) (4); have polyH1 := Poly.mul polyH0 (hK); have polyH2 := Poly.const (s) (3); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega)))
    intro j a ha
    rw [volume_prod,volume_nat,volume_nat]
    have := hB j a ha
    omega
  exact binaryReadListEncoded s idx (Uniform.binaryReadEdge (I := I)) (fun _ => Binary.encodeEdge)
    (fun _ => Binary.readEdge_correct) xs rest hl hb hX hT hV
end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module RequestCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type}

theorem time_binaryParse (i : I) (bs : List Bool) :
    (binaryParse (I := I)).time i bs =
    (parseVertexLength.pair ((parseEdges.comp fst).pair (binaryReadHeader.comp fst))).time i bs := rfl
theorem time_binaryParse_outer (i : I) (bs : List Bool) :
    (binaryParse (I := I)).time i bs =
      (parseVertexLength (I := I)).time i bs +
      (((parseEdges (I := I)).comp fst).pair ((binaryReadHeader (I := I)).comp fst)).time i bs +
      20*(volume bs + volume ((Binary.readList Binary.readNat (Binary.readHeader bs).2).1.length) +
      volume ((Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader bs).2).2).1,
        (Binary.readHeader bs).1)+1) := by
  rw [time_binaryParse]
  exact time_pair (parseVertexLength (I := I))
    (((parseEdges (I := I)).comp fst).pair ((binaryReadHeader (I := I)).comp fst)) i bs
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem binaryReadHeader (bs : J → List Bool)
    (hb : Poly s (fun j => (bs j).length) 1)
    (hn : Poly s (fun j => (Binary.readNat (bs j).tail).1) 1) :
    Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4 := by
  have hh : Poly s (fun j => volume (bs j).head?) 0 := by
    apply Poly.volumeOption _ (Poly.const s 3)
    intro j b hb; exact volume_bool b
  have htail : Poly s (fun j => (bs j).tail.length) 1 := Poly.lengthTail bs hb
  have hT := binaryReadNat s idx (fun j => (bs j).tail) htail hn
  have hRest : Poly s (fun j => (Binary.readNat (bs j).tail).2.length) 1 := by
    apply Poly.of_le (fun j : J => Binary.readNat_rest_length _)
    exact htail
  (have polyH0 := Poly.const (s) (10000); have polyH1 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => bs j_1) => (Sigma.snd q).1); have polyH2 := Poly.listVolume (fun (j_1 : J) => bs j_1) (hb) polyH1; have polyH3 := Poly.const (s) (1); have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.mul polyH0 polyH4; have polyH6 := Poly.of_le (fun (j_13 : J) => (@Uniform.time_head?_le (I) (fun (i : I) => Bool) _ (idx j_13) (bs j_13))) polyH5; have polyH7 := Poly.const (s) (2); have polyH8 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_false (I) (fun (i : I) => List Bool) _ (idx j_13) (bs j_13)))) polyH7; have polyH9 := Poly.add polyH6 polyH8; have polyH10 := Poly.const (s) (20); have polyH11 := Poly.add polyH2 (hh); have polyH12 := Poly.const (s) (volume Bool.false); have polyH13 := Poly.add polyH11 polyH12; have polyH14 := Poly.add polyH13 polyH3; have polyH15 := Poly.mul polyH10 polyH14; have polyH16 := Poly.add polyH9 polyH15; have polyH17 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List Bool) (fun (i : I) => Option Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.head? xs) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.head? I (fun (i : I) => Bool) _) (@Uniform.false I (fun (i : I) => List Bool) _) (idx j_13) (bs j_13)))) polyH16; have polyH18 := Poly.add (hh) polyH12; have polyH19 := Poly.add polyH18 polyH3; have polyH20 := Poly.mul polyH0 polyH19; have polyH21 := Poly.of_le (fun (j_13 : J) => (@Uniform.time_getD_le (I) (fun (i : I) => Bool) _ (idx j_13) (List.head? (bs j_13)) (Bool.false))) polyH20; have polyH22 := Poly.add polyH17 polyH21; have polyH23 := Poly.const (s) (10); have polyH24 := Poly.volumeBool (s) (fun (j_1 : J) => Bool.false); have polyH25 := Poly.volumeProd (fun (j_1 : J) => (List.head? (bs j_1), Bool.false)) (hh) polyH24; have polyH26 := Poly.add polyH25 polyH3; have polyH27 := Poly.mul polyH23 polyH26; have polyH28 := Poly.add polyH22 polyH27; have polyH29 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (i : I) => Option Bool × Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.head? x, Bool.false)) (fun (i : I) (x : Option Bool × Bool) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => Option Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.head? xs) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.head? I (fun (i : I) => Bool) _) (@Uniform.false I (fun (i : I) => List Bool) _)) (@Uniform.getD I (fun (i : I) => Bool) _) (idx j_13) (bs j_13)))) polyH28; have polyH30 := Poly.add polyH2 polyH7; have polyH31 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_tail (I) (fun (i : I) => Bool) _ (idx j_13) (bs j_13)))) polyH30; have polyH32 := Poly.add polyH31 (hT); have polyH33 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => List.tail (bs j_1)) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => List.tail (bs j_1)) => (Sigma.snd q).1); have polyH34 := Poly.listVolume (fun (j_1 : J) => List.tail (bs j_1)) (htail) polyH33; have polyH35 := Poly.add polyH34 polyH3; have polyH36 := Poly.mul polyH23 polyH35; have polyH37 := Poly.add polyH32 polyH36; have polyH38 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I) (idx j_13) (bs j_13)))) polyH37; have polyH39 := Poly.volumeNat (hn); have polyH40 := Poly.volumeBool (fun (q : Poly.ListPool fun (j_1 : J) => (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1))).2) => s (Sigma.fst q)) (fun (q : Poly.ListPool fun (j_1 : J) => (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1))).2) => (Sigma.snd q).1); have polyH41 := Poly.listVolume (fun (j_1 : J) => (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1))).2) (hRest) polyH40; have polyH42 := Poly.volumeProd (fun (j_1 : J) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1))) polyH39 polyH41; have polyH43 := Poly.add polyH42 polyH7; have polyH44 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_fst (I) (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _ (idx j_13) (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_13)))))) polyH43; have polyH45 := Poly.const (s) (100); have polyH46 := Poly.add polyH39 polyH3; have polyH47 := Poly.mul polyH45 polyH46; have polyH48 := Poly.of_le (fun (j_13 : J) => (@Uniform.time_some_le (I) (fun (i : I) => ℕ) _ (idx j_13) (Prod.fst (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_13)))))) polyH47; have polyH49 := Poly.add polyH44 polyH48; have polyH50 := Poly.mul polyH23 polyH46; have polyH51 := Poly.add polyH49 polyH50; have polyH52 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => ℕ × List Bool) (fun (i : I) => ℕ) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (a : ℕ) => Option.some a) (@Uniform.fst I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.some I (fun (i : I) => ℕ) _) (idx j_13) (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_13)))))) polyH51; have polyH53 := Poly.add polyH38 polyH52; have polyH54 := Poly.add polyH42 polyH3; have polyH55 := Poly.mul polyH23 polyH54; have polyH56 := Poly.add polyH53 polyH55; have polyH57 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) (x : List Bool) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)) (fun (i : I) (x : ℕ × List Bool) => (fun (a : ℕ) => Option.some a) (Prod.fst x)) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I)) (@Uniform.comp I (fun (i : I) => ℕ × List Bool) (fun (i : I) => ℕ) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (a : ℕ) => Option.some a) (@Uniform.fst I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.some I (fun (i : I) => ℕ) _)) (idx j_13) (bs j_13)))) polyH56; have polyH58 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _ (idx j_13) (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_13)))))) polyH43; have polyH59 := Poly.add polyH38 polyH58; have polyH60 := Poly.add polyH59 polyH55; have polyH61 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I)) (@Uniform.snd I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _) (idx j_13) (bs j_13)))) polyH60; have polyH62 := Poly.add polyH57 polyH61; have polyH63 := Poly.volumeOptionSome (fun (j_1 : J) => Prod.fst (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1)))) polyH39; have polyH64 := Poly.add polyH2 polyH63; have polyH65 := Poly.add polyH64 polyH41; have polyH66 := Poly.add polyH65 polyH3; have polyH67 := Poly.mul polyH10 polyH66; have polyH68 := Poly.add polyH62 polyH67; have polyH69 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List Bool) (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (fun (a : ℕ) => Option.some a) (Prod.fst (Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)))) (fun (i : I) (x : List Bool) => Prod.snd (Binary.readNat ((fun (xs : List Bool) => List.tail xs) x))) (@Uniform.comp I (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) (x : List Bool) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)) (fun (i : I) (x : ℕ × List Bool) => (fun (a : ℕ) => Option.some a) (Prod.fst x)) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I)) (@Uniform.comp I (fun (i : I) => ℕ × List Bool) (fun (i : I) => ℕ) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (a : ℕ) => Option.some a) (@Uniform.fst I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.some I (fun (i : I) => ℕ) _))) (@Uniform.comp I (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I)) (@Uniform.snd I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _)) (idx j_13) (bs j_13)))) polyH68; have polyH70 := Poly.add polyH29 polyH69; have polyH71 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_none (I) (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _ (idx j_13) (bs j_13)))) polyH7; have polyH72 := Poly.add polyH71 polyH31; have polyH73 := Poly.const (s) (volume (@Option.none ℕ)); have polyH74 := Poly.add polyH2 polyH73; have polyH75 := Poly.add polyH74 polyH34; have polyH76 := Poly.add polyH75 polyH3; have polyH77 := Poly.mul polyH10 polyH76; have polyH78 := Poly.add polyH72 polyH77; have polyH79 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (I) (fun (x : I) => List Bool) (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => @Option.none ℕ) (fun (i : I) (xs : List Bool) => List.tail xs) (@Uniform.none I (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _) (@Uniform.tail I (fun (i : I) => Bool) _) (idx j_13) (bs j_13)))) polyH78; have polyH80 := Poly.add polyH70 polyH79; have polyH81 := Poly.const (s) (1000); have polyH82 := Poly.volumeProd (fun (j_1 : J) => ((fun (a : ℕ) => Option.some a) (Prod.fst (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1)))), Prod.snd (Binary.readNat ((fun (xs : List Bool) => List.tail xs) (bs j_1))))) polyH63 polyH41; have polyH83 := Poly.add polyH2 polyH82; have polyH84 := Poly.volumeProd (fun (j_1 : J) => (@Option.none ℕ, List.tail (bs j_1))) polyH3 polyH34; have polyH85 := Poly.add polyH83 polyH84; have polyH86 := Poly.add polyH85 polyH3; have polyH87 := Poly.mul polyH81 polyH86; have polyH88 := Poly.add polyH80 polyH87; have polyH89 := Poly.of_le (fun (j_13 : J) => (@Uniform.time_ite_le (I) (fun (x : I) => List Bool) (fun (i : I) => Option ℕ × List Bool) _ _ (fun (x : I) (bs_1 : List Bool) => Option.getD (List.head? bs_1) Bool.false) (fun (i : I) (x : List Bool) => ((fun (a : ℕ) => Option.some a) (Prod.fst (Binary.readNat ((fun (xs : List Bool) => List.tail xs) x))), Prod.snd (Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)))) (fun (i : I) (x : List Bool) => (@Option.none ℕ, List.tail x)) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => Option Bool × Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) (x : List Bool) => (List.head? x, Bool.false)) (fun (i : I) (x : Option Bool × Bool) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => Option Bool) (fun (i : I) => Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.head? xs) (fun (i : I) (x : List Bool) => Bool.false) (@Uniform.head? I (fun (i : I) => Bool) _) (@Uniform.false I (fun (i : I) => List Bool) _)) (@Uniform.getD I (fun (i : I) => Bool) _)) (@Uniform.pair I (fun (i : I) => List Bool) (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => (fun (a : ℕ) => Option.some a) (Prod.fst (Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)))) (fun (i : I) (x : List Bool) => Prod.snd (Binary.readNat ((fun (xs : List Bool) => List.tail xs) x))) (@Uniform.comp I (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) (x : List Bool) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)) (fun (i : I) (x : ℕ × List Bool) => (fun (a : ℕ) => Option.some a) (Prod.fst x)) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I)) (@Uniform.comp I (fun (i : I) => ℕ × List Bool) (fun (i : I) => ℕ) (fun (i : I) => Option ℕ) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (a : ℕ) => Option.some a) (@Uniform.fst I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.some I (fun (i : I) => ℕ) _))) (@Uniform.comp I (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => Binary.readNat ((fun (xs : List Bool) => List.tail xs) x)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List Bool) (fun (i : I) => List Bool) (fun (x : I) => ℕ × List Bool) _ _ _ (fun (i : I) (xs : List Bool) => List.tail xs) (fun (x : I) => Binary.readNat) (@Uniform.tail I (fun (i : I) => Bool) _) (@Uniform.binaryReadNat I)) (@Uniform.snd I (fun (i : I) => ℕ) (fun (i : I) => List Bool) _ _))) (@Uniform.pair I (fun (x : I) => List Bool) (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _ _ (fun (i : I) (x : List Bool) => @Option.none ℕ) (fun (i : I) (xs : List Bool) => List.tail xs) (@Uniform.none I (fun (x : I) => List Bool) (fun (i : I) => ℕ) _ _) (@Uniform.tail I (fun (i : I) => Bool) _)) (idx j_13) (bs j_13))) polyH88; exact Poly.lift polyH89 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem parseVertices (bs : J → List Bool)
    (_hb : Poly s (fun j => (bs j).length) 1)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hV : Poly s (fun j => (Uniform.binaryReadNat (I := I)).binaryReadList.time (idx j) (Binary.readHeader (bs j)).2) 4)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2)
    (_hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2) :
    Poly s (fun j => (Uniform.parseVertices (I := I)).time (idx j) (bs j)) 4 := by
  have ht : Poly s (fun j => volume (Binary.readHeader (bs j)).2) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvH
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (hvH) polyH0; have polyH2 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _ (idx j_13) (Binary.readHeader (bs j_13))))) polyH1; have polyH3 := Poly.add polyH2 (hV); have polyH4 := Poly.const (s) (10); have polyH5 := Poly.const (s) (1); have polyH6 := Poly.add (ht) polyH5; have polyH7 := Poly.mul polyH4 polyH6; have polyH8 := Poly.add polyH3 polyH7; have polyH9 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => Option ℕ × List Bool) (fun (i : I) => List Bool) (fun (i : I) => List ℕ × List Bool) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) => Binary.readList Binary.readNat) (@Uniform.snd I (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.binaryReadList I (fun (i : I) => ℕ) _ (fun (x : I) => Binary.readNat) (@Uniform.binaryReadNat I)) (idx j_13) (Binary.readHeader (bs j_13))))) polyH8; have polyH10 := Poly.add (hH) polyH9; have polyH11 := Poly.add (hvH) polyH5; have polyH12 := Poly.mul polyH4 polyH11; have polyH13 := Poly.add polyH10 polyH12; have polyH14 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (x : I) => Option ℕ × List Bool) (fun (i : I) => List ℕ × List Bool) _ _ _ (fun (x : I) => Binary.readHeader) (fun (i : I) (x : Option ℕ × List Bool) => Binary.readList Binary.readNat (Prod.snd x)) (@Uniform.binaryReadHeader I) (@Uniform.comp I (fun (i : I) => Option ℕ × List Bool) (fun (i : I) => List Bool) (fun (i : I) => List ℕ × List Bool) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) => Binary.readList Binary.readNat) (@Uniform.snd I (fun (i : I) => Option ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.binaryReadList I (fun (i : I) => ℕ) _ (fun (x : I) => Binary.readNat) (@Uniform.binaryReadNat I))) (idx j_13) (bs j_13)))) polyH13; exact Poly.lift polyH14 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem parseEdges (bs : J → List Bool)
    (_hb : Poly s (fun j => (bs j).length) 1)
    (hV : Poly s (fun j => (Uniform.parseVertices (I := I)).time (idx j) (bs j)) 4)
    (hE : Poly s (fun j => (Uniform.binaryReadEdge (I := I)).binaryReadList.time (idx j)
      (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2) 4)
    (hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2)
    (_hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2) :
    Poly s (fun j => (Uniform.parseEdges (I := I)).time (idx j) (bs j)) 4 := by
  have hvr : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvV
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (hvV) polyH0; have polyH2 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => List ℕ) (fun (i : I) => List Bool) _ _ (idx j_13) (Binary.readList Binary.readNat (Prod.snd (Binary.readHeader (bs j_13))))))) polyH1; have polyH3 := Poly.add polyH2 (hE); have polyH4 := Poly.const (s) (10); have polyH5 := Poly.const (s) (1); have polyH6 := Poly.add (hvr) polyH5; have polyH7 := Poly.mul polyH4 polyH6; have polyH8 := Poly.add polyH3 polyH7; have polyH9 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ℕ × List Bool) (fun (i : I) => List Bool) (fun (i : I) => List (ℕ × ℕ) × List Bool) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) => Binary.readList Binary.readEdge) (@Uniform.snd I (fun (i : I) => List ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.binaryReadList I (fun (i : I) => ℕ × ℕ) _ (fun (x : I) => Binary.readEdge) (@Uniform.binaryReadEdge I)) (idx j_13) (Binary.readList Binary.readNat (Prod.snd (Binary.readHeader (bs j_13))))))) polyH8; have polyH10 := Poly.add (hV) polyH9; have polyH11 := Poly.add (hvV) polyH5; have polyH12 := Poly.mul polyH4 polyH11; have polyH13 := Poly.add polyH10 polyH12; have polyH14 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (x : I) => List ℕ × List Bool) (fun (i : I) => List (ℕ × ℕ) × List Bool) _ _ _ (fun (x : I) (bs_1 : List Bool) => Binary.readList Binary.readNat (Prod.snd (Binary.readHeader bs_1))) (fun (i : I) (x : List ℕ × List Bool) => Binary.readList Binary.readEdge (Prod.snd x)) (@Uniform.parseVertices I) (@Uniform.comp I (fun (i : I) => List ℕ × List Bool) (fun (i : I) => List Bool) (fun (i : I) => List (ℕ × ℕ) × List Bool) _ _ _ (fun (i : I) => Prod.snd) (fun (i : I) => Binary.readList Binary.readEdge) (@Uniform.snd I (fun (i : I) => List ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.binaryReadList I (fun (i : I) => ℕ × ℕ) _ (fun (x : I) => Binary.readEdge) (@Uniform.binaryReadEdge I))) (idx j_13) (bs j_13)))) polyH13; exact Poly.lift polyH14 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem parseVertexLength (bs : J → List Bool)
    (_hb : Poly s (fun j => (bs j).length) 1)
    (hV : Poly s (fun j => (Uniform.parseVertices (I := I)).time (idx j) (bs j)) 4)
    (hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2) :
    Poly s (fun j => (Uniform.parseVertexLength (I := I)).time (idx j) (bs j)) 4 := by
  have hv : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvV
  have hl := Poly.lengthVolume _ hv
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.add (hvV) polyH0; have polyH2 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_fst (I) (fun (i : I) => List ℕ) (fun (i : I) => List Bool) _ _ (idx j_12) (Binary.readList Binary.readNat (Prod.snd (Binary.readHeader (bs j_12))))))) polyH1; have polyH3 := Poly.const (s) (100000); have polyH4 := Poly.const (s) (1); have polyH5 := Poly.add (hl) polyH4; have polyH6 := Poly.mul polyH3 polyH5; have polyH7 := Poly.add (hv) polyH4; have polyH8 := Poly.mul polyH6 polyH7; have polyH9 := Poly.of_le (fun (j_12 : J) => (@Uniform.time_length_le (I) (fun (i : I) => ℕ) _ (idx j_12) (Prod.fst (Binary.readList Binary.readNat (Prod.snd (Binary.readHeader (bs j_12))))))) polyH8; have polyH10 := Poly.add polyH2 polyH9; have polyH11 := Poly.const (s) (10); have polyH12 := Poly.mul polyH11 polyH7; have polyH13 := Poly.add polyH10 polyH12; have polyH14 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ℕ × List Bool) (fun (i : I) => List ℕ) (fun (i : I) => ℕ) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ℕ) => List.length xs) (@Uniform.fst I (fun (i : I) => List ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.length I (fun (i : I) => ℕ) _) (idx j_12) (Binary.readList Binary.readNat (Prod.snd (Binary.readHeader (bs j_12))))))) polyH13; have polyH15 := Poly.add (hV) polyH14; have polyH16 := Poly.add (hvV) polyH4; have polyH17 := Poly.mul polyH11 polyH16; have polyH18 := Poly.add polyH15 polyH17; have polyH19 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_comp (I) (fun (x : I) => List Bool) (fun (x : I) => List ℕ × List Bool) (fun (i : I) => ℕ) _ _ _ (fun (x : I) (bs_1 : List Bool) => Binary.readList Binary.readNat (Prod.snd (Binary.readHeader bs_1))) (fun (i : I) (x : List ℕ × List Bool) => (fun (xs : List ℕ) => List.length xs) (Prod.fst x)) (@Uniform.parseVertices I) (@Uniform.comp I (fun (i : I) => List ℕ × List Bool) (fun (i : I) => List ℕ) (fun (i : I) => ℕ) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ℕ) => List.length xs) (@Uniform.fst I (fun (i : I) => List ℕ) (fun (i : I) => List Bool) _ _) (@Uniform.length I (fun (i : I) => ℕ) _)) (idx j_12) (bs j_12)))) polyH18; exact Poly.lift polyH19 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem binaryParseEH (bs : J → List Bool)
    (hBV : Poly s (fun j => volume (bs j)) 1)
    (hPE : Poly s (fun j => (Uniform.parseEdges (I := I)).time (idx j) (bs j)) 4)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2) :
    Poly s (fun j => (((Uniform.parseEdges (I := I)).comp Uniform.fst).pair
      ((Uniform.binaryReadHeader (I := I)).comp Uniform.fst)).time (idx j) (bs j)) 4 := by
  have hh : Poly s (fun j => volume (Binary.readHeader (bs j)).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvH
  have he : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvE
  have hvs : Poly s (fun j => (Uniform.fst (α := fun _ : I => List (ℕ × ℕ)) (β := fun _ : I => List Bool)).time (idx j)
      (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 4 := by
    simp only [Uniform.time_fst]
    exact (hvE.add (Poly.const s 2)).lift (by omega)
  have hhs : Poly s (fun j => (Uniform.fst (α := fun _ : I => Option ℕ) (β := fun _ : I => List Bool)).time (idx j) (Binary.readHeader (bs j))) 4 := by
    simp only [Uniform.time_fst]
    exact (hvH.add (Poly.const s 2)).lift (by omega)
  have hA := Poly.compTimeSame (Uniform.parseEdges (I := I)) Uniform.fst idx bs
    hPE hvs (hvE.lift (by omega))
  have hB := Poly.compTimeSame (Uniform.binaryReadHeader (I := I)) Uniform.fst idx bs
    hH hhs (hvH.lift (by omega))
  exact Poly.pairTimeSame ((Uniform.parseEdges (I := I)).comp Uniform.fst)
    idx bs ((Uniform.binaryReadHeader (I := I)).comp Uniform.fst)
    hA hB (hBV.lift (by omega)) (he.lift (by omega)) (hh.lift (by omega))

theorem binaryParseParts (bs : J → List Bool)
    (hb : Poly s (fun j => (bs j).length) 1)
    (hPL : Poly s (fun j => (Uniform.parseVertexLength (I := I)).time (idx j) (bs j)) 4)
    (hPE : Poly s (fun j => (Uniform.parseEdges (I := I)).time (idx j) (bs j)) 4)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2)
    (hl : Poly s (fun j => (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1.length) 2) :
    Poly s (fun j => (Uniform.binaryParse (I := I)).time (idx j) (bs j)) 4 := by
  have hh : Poly s (fun j => volume (Binary.readHeader (bs j)).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvH
  have he : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1) 2 :=
    Poly.of_le (fun j => by rw [volume_prod]; omega) hvE
  have hBV : Poly s (fun j => volume (bs j)) 1 := by
    apply Poly.of_le (fun j : J => volume_boolList_le (bs j))
    exact ((Poly.const s 4).mul hb).add (Poly.const s 1)
  have hAB := binaryParseEH s idx bs hBV hPE hH hvE hvH
  have hvAB : Poly s (fun j => volume
      ((Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1,
       (Binary.readHeader (bs j)).1)) 2 := Poly.volumeProd (fun j : J =>
      ((Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2).1,
       (Binary.readHeader (bs j)).1)) he hh
  have hvl : Poly s (fun j => volume ((Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1.length)) 2 := Poly.volumeNat hl
  have hvol := ((hBV.add hvl).add hvAB).add (Poly.const s 1)
  have hpoly := (hPL.add hAB).add ((Poly.const s 20).mul hvol)
  obtain ⟨C,hC⟩ := hpoly
  refine ⟨C,?_⟩
  intro j
  change (Uniform.binaryParse (I := I)).time (idx j) (bs j) ≤ C * (s j + 2)^4
  rw [Uniform.time_binaryParse_outer]
  exact hC j

theorem binaryParse (bs : J → List Bool)
    (hb : Poly s (fun j => (bs j).length) 1)
    (hH : Poly s (fun j => (Uniform.binaryReadHeader (I := I)).time (idx j) (bs j)) 4)
    (hV : Poly s (fun j => (Uniform.binaryReadNat (I := I)).binaryReadList.time (idx j) (Binary.readHeader (bs j)).2) 4)
    (hE : Poly s (fun j => (Uniform.binaryReadEdge (I := I)).binaryReadList.time (idx j)
      (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2) 4)
    (hvH : Poly s (fun j => volume (Binary.readHeader (bs j))) 2)
    (hvV : Poly s (fun j => volume (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2)) 2)
    (hvE : Poly s (fun j => volume (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).2)) 2) :
    Poly s (fun j => (Uniform.binaryParse (I := I)).time (idx j) (bs j)) 4 := by
  have hPV := parseVertices s idx bs hb hH hV hvH hvV
  have hPE := parseEdges s idx bs hb hPV hE hvV hvE
  have hPL := parseVertexLength s idx bs hb hPV hvV
  have hl : Poly s (fun j => (Binary.readList Binary.readNat (Binary.readHeader (bs j)).2).1.length) 2 :=
    Poly.lengthVolume _ (Poly.of_le (fun j => by rw [volume_prod]; omega) hvV)
  exact binaryParseParts s idx bs hb hPL hPE hH hvE hvH hl
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
theorem time_parseRequest (n : ℕ) (x : Request n) :
    parseRequest.time n x = (binaryParse (I := ℕ)).time n (ThreeMachine.encodeInput x.graph x.deadline) := by
  simp only [Uniform.time,parseRequest]
  exact congrArg (binaryParse (I := ℕ)).charge (show enc x = enc (ThreeMachine.encodeInput x.graph x.deadline) from rfl)
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open RequestData

theorem requestHeader : Poly size
    (fun x : Index => (Uniform.binaryReadHeader (I := ℕ)).time x.1 (bits x)) 4 := by
  have hval : Poly size (fun x : Index => (Binary.readNat (bits x).tail).1) 1 := by
    simp only [bits,Binary.readNat_tail_input]
    apply Poly.of_le (fun x : Index => show x.2.deadline.getD x.1 ≤ x.1+x.2.deadline.getD 0 from by
      cases x.2.deadline <;> simp only [Option.getD_none,Option.getD_some] <;> omega)
    exact nPoly.add deadlinePoly
  exact binaryReadHeader size Sigma.fst bits bitsPoly hval

theorem requestVertices : Poly size
    (fun x : Index => (Uniform.binaryReadNat (I := ℕ)).binaryReadList.time x.1 (Binary.readHeader (bits x)).2) 4 := by
  simp only [bits,Binary.readHeader_input]
  exact binaryNatList size Sigma.fst (fun x : Index => Binary.vertices x.1) ebytes
    (fun x => x.1) verticesLength nPoly verticesBound vrestPoly

theorem requestEdges : Poly size
    (fun x : Index => (Uniform.binaryReadEdge (I := ℕ)).binaryReadList.time x.1
      (Binary.readList Binary.readNat (Binary.readHeader (bits x)).2).2) 4 := by
  simp only [bits,Binary.readVertices_input]
  have h := binaryEdgeList size Sigma.fst (fun x : Index => Binary.edges x.2.graph) (fun _ => [])
    (fun x => x.1) edgesLength nPoly edgesBound
    (show Poly size (fun x : Index => (ThreeMachine.encodeList Binary.encodeEdge
      (Binary.edges x.2.graph) ++ []).length) 1 from by simpa only [List.append_nil,ebytes] using ebytesPoly)
  simpa only [List.append_nil] using h

theorem requestBinaryParse : Poly size
    (fun x : Index => (Uniform.binaryParse (I := ℕ)).time x.1 (bits x)) 4 := by
  have hvH : Poly size (fun x : Index => volume (Binary.readHeader (bits x))) 2 := by
    simp only [bits,Binary.readHeader_input]
    have h := volumeDeadline
    have hv := volumeVrest
    dsimp only [vbytes,ebytes] at hv
    (have polyH0 := Poly.volumeProd (fun (x_1 : RequestData.Index) => (Request.deadline (Sigma.snd x_1), OAI.ThreeMachine.encodeList OAI.ThreeMachine.encodeNat (Binary.vertices (Sigma.fst x_1)) ++ OAI.ThreeMachine.encodeList Binary.encodeEdge (Binary.edges (Request.graph (Sigma.snd x_1))))) (h) (hv); exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hvV : Poly size (fun x : Index => volume
      (Binary.readList Binary.readNat (Binary.readHeader (bits x)).2)) 2 := by
    simp only [bits,Binary.readVertices_input]
    have h := volumeVertices
    have hv := volumeEbytes
    dsimp only [ebytes] at hv
    (have polyH0 := Poly.volumeProd (fun (x_1 : RequestData.Index) => (Binary.vertices (Sigma.fst x_1), OAI.ThreeMachine.encodeList Binary.encodeEdge (Binary.edges (Request.graph (Sigma.snd x_1))))) (h) (hv); exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hvE : Poly size (fun x : Index => volume
      (Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader (bits x)).2).2)) 2 := by
    simp only [bits,Binary.readEdges_input]
    have h := volumeEdges
    (have polyH0 := Poly.const (RequestData.size) (1); have polyH1 := Poly.volumeProd (fun (x_1 : RequestData.Index) => (Binary.edges (Request.graph (Sigma.snd x_1)), @List.nil Bool)) (h) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  exact binaryParse size Sigma.fst bits bitsPoly requestHeader requestVertices requestEdges hvH hvV hvE

theorem parseRequest : Poly size (fun x : Index => Uniform.parseRequest.time x.1 x.2) 4 :=
  by simpa only [Uniform.time_parseRequest,RequestData.bits] using requestBinaryParse
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open RequestData

theorem requestAnswer : Poly size (fun x : Index => Uniform.requestAnswer.time x.1 x.2) 150011 := by
  let U (x : Index) : Universe x.1 := Universe.mk ()
  have hParse := parseRequest
  have hRequest := volumeRequest
  have hGraph := volumeGraph
  have hn := nPoly
  have hD := volumeDeadline
  have hAnswer := unaryAnswer size (fun x : Index => x.1) U (fun x => x.2.graph)
    (fun x => x.2.deadline) nPoly edgesPoly deadlinePoly
  have hOut := requestSlotsVolume
  have hEncode := requestEncodeAnswer
  dsimp only [requestSlots] at hOut hEncode
  (have polyH0 := Poly.volumeCardinal (hn) (fun (x_1 : RequestData.Index) => @Cardinal.mk (Sigma.fst x_1) ()); have polyH1 := Poly.volumeProd (fun (x_1 : RequestData.Index) => (Request.graph (Sigma.snd x_1), Request.deadline (Sigma.snd x_1))) (hGraph) (hD); have polyH2 := Poly.volumeProd (fun (x_1 : RequestData.Index) => (@Cardinal.mk (Sigma.fst x_1) (), Request.graph (Sigma.snd x_1), Request.deadline (Sigma.snd x_1))) polyH0 polyH1; have polyH3 := Poly.const (RequestData.size) (2); have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_fst (ℕ) (Cardinal) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ (Sigma.fst x_11) ((@Cardinal.mk (Sigma.fst x_11) (), Request.graph (Sigma.snd x_11), Request.deadline (Sigma.snd x_11)))))) polyH4; have polyH6 := Poly.const (RequestData.size) (100000000000); have polyH7 := Poly.const (RequestData.size) (1); have polyH8 := Poly.add (hn) polyH7; have polyH9 := Poly.pow polyH8 (3); have polyH10 := Poly.mul polyH6 polyH9; have polyH11 := Poly.of_le (fun (x_11 : RequestData.Index) => (@Realizer.time_range_le (Sigma.fst x_11))) polyH10; have polyH12 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_makeUniverse (Sigma.fst x_11) (Prod.fst (@Cardinal.mk (Sigma.fst x_11) (), Request.graph (Sigma.snd x_11), Request.deadline (Sigma.snd x_11)))))) polyH11; have polyH13 := Poly.add polyH5 polyH12; have polyH14 := Poly.const (RequestData.size) (10); have polyH15 := Poly.add polyH0 polyH7; have polyH16 := Poly.mul polyH14 polyH15; have polyH17 := Poly.add polyH13 polyH16; have polyH18 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Cardinal i × (fun (i_1 : ℕ) => OAI.ThreeMachine.Instance i_1 × Option ℕ) i) (Cardinal) (Universe) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Cardinal n) => @Universe.mk n ()) (@Uniform.fst ℕ Cardinal (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (Uniform.makeUniverse) (Sigma.fst x_11) ((@Cardinal.mk (Sigma.fst x_11) (), Request.graph (Sigma.snd x_11), Request.deadline (Sigma.snd x_11)))))) polyH17; have polyH19 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_snd (ℕ) (Cardinal) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ (Sigma.fst x_11) ((@Cardinal.mk (Sigma.fst x_11) (), Request.graph (Sigma.snd x_11), Request.deadline (Sigma.snd x_11)))))) polyH4; have polyH20 := Poly.add polyH18 polyH19; have polyH21 := Poly.const (RequestData.size) (20); have polyH22 := Poly.volumeUniverse (hn) (fun (x_1 : RequestData.Index) => @Universe.mk (Sigma.fst x_1) ()); have polyH23 := Poly.add polyH2 polyH22; have polyH24 := Poly.add polyH23 polyH1; have polyH25 := Poly.add polyH24 polyH7; have polyH26 := Poly.mul polyH21 polyH25; have polyH27 := Poly.add polyH20 polyH26; have polyH28 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Cardinal i × (fun (i_1 : ℕ) => OAI.ThreeMachine.Instance i_1 × Option ℕ) i) (Universe) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ _ (fun (i : ℕ) (x_1 : Cardinal i × (fun (i_1 : ℕ) => OAI.ThreeMachine.Instance i_1 × Option ℕ) i) => (fun (n : ℕ) (x_2 : Cardinal n) => @Universe.mk n ()) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Cardinal i × (fun (i_1 : ℕ) => OAI.ThreeMachine.Instance i_1 × Option ℕ) i) Cardinal Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Cardinal n) => @Universe.mk n ()) (@Uniform.fst ℕ Cardinal (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) Uniform.makeUniverse) (@Uniform.snd ℕ Cardinal (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (Sigma.fst x_11) ((@Cardinal.mk (Sigma.fst x_11) (), Request.graph (Sigma.snd x_11), Request.deadline (Sigma.snd x_11)))))) polyH27; have polyH29 := Poly.add polyH28 (hAnswer); have polyH30 := Poly.volumeProd (fun (x_1 : RequestData.Index) => (@Universe.mk (Sigma.fst x_1) (), Prod.snd (@Cardinal.mk (Sigma.fst x_1) (), Request.graph (Sigma.snd x_1), Request.deadline (Sigma.snd x_1)))) polyH22 polyH1; have polyH31 := Poly.add polyH30 polyH7; have polyH32 := Poly.mul polyH14 polyH31; have polyH33 := Poly.add polyH29 polyH32; have polyH34 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (n : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x_1 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (@Universe.mk i (), Prod.snd x_1)) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (closureMatrix (Prod.fst (Prod.snd x_1)) n) (Prod.snd (Prod.snd x_1))) (@Uniform.onFst ℕ Cardinal Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ _ (fun (n : ℕ) (x_1 : Cardinal n) => @Universe.mk n ()) Uniform.makeUniverse) (Uniform.unaryAnswer) (Sigma.fst x_11) ((@Cardinal.mk (Sigma.fst x_11) (), Request.graph (Sigma.snd x_11), Request.deadline (Sigma.snd x_11)))))) polyH33; have polyH35 := Poly.add (hParse) polyH34; have polyH36 := Poly.add polyH2 polyH7; have polyH37 := Poly.mul polyH14 polyH36; have polyH38 := Poly.add polyH35 polyH37; have polyH39 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_comp (ℕ) (Request) (fun (n : ℕ) => Cardinal n × OAI.ThreeMachine.Instance n × Option ℕ) (fun (n : ℕ) => Option (List ℕ)) _ _ _ (fun (n : ℕ) (x_1 : Request n) => (@Cardinal.mk n (), Request.graph x_1, Request.deadline x_1)) (fun (i : ℕ) (x_1 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (fun (x_2 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (closureMatrix (Prod.fst (Prod.snd x_2)) i) (Prod.snd (Prod.snd x_2))) ((fun (x_2 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (@Universe.mk i (), Prod.snd x_2)) x_1)) (Uniform.parseRequest) (@Uniform.comp ℕ (fun (i : ℕ) => Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (n : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x_1 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (@Universe.mk i (), Prod.snd x_1)) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (closureMatrix (Prod.fst (Prod.snd x_1)) n) (Prod.snd (Prod.snd x_1))) (@Uniform.onFst ℕ Cardinal Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ _ (fun (n : ℕ) (x_1 : Cardinal n) => @Universe.mk n ()) Uniform.makeUniverse) Uniform.unaryAnswer) (Sigma.fst x_11) (Sigma.snd x_11)))) polyH38; have polyH40 := Poly.add polyH39 (hEncode); have polyH41 := Poly.add (hOut) polyH7; have polyH42 := Poly.mul polyH14 polyH41; have polyH43 := Poly.add polyH40 polyH42; have polyH44 := Poly.of_le (fun (x_11 : RequestData.Index) => (le_of_eq (@Uniform.time_comp (ℕ) (Request) (fun (n : ℕ) => Option (List ℕ)) (fun (x_1 : ℕ) => List Bool) _ _ _ (fun (i : ℕ) (x_1 : Request i) => (fun (x_2 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (closureMatrix (Prod.fst (Prod.snd x_2)) i) (Prod.snd (Prod.snd x_2))) ((fun (x_2 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (@Universe.mk i (), Prod.snd x_2)) ((fun (x_2 : Request i) => (@Cardinal.mk i (), Request.graph x_2, Request.deadline x_2)) x_1))) (fun (x_1 : ℕ) => OAI.ThreeMachine.encodeAnswer) (@Uniform.comp ℕ Request (fun (n : ℕ) => Cardinal n × OAI.ThreeMachine.Instance n × Option ℕ) (fun (n : ℕ) => Option (List ℕ)) _ _ _ (fun (n : ℕ) (x_1 : Request n) => (@Cardinal.mk n (), Request.graph x_1, Request.deadline x_1)) (fun (i : ℕ) (x_1 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (fun (x_2 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (closureMatrix (Prod.fst (Prod.snd x_2)) i) (Prod.snd (Prod.snd x_2))) ((fun (x_2 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (@Universe.mk i (), Prod.snd x_2)) x_1)) Uniform.parseRequest (@Uniform.comp ℕ (fun (i : ℕ) => Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (n : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x_1 : Cardinal i × OAI.ThreeMachine.Instance i × Option ℕ) => (@Universe.mk i (), Prod.snd x_1)) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (closureMatrix (Prod.fst (Prod.snd x_1)) n) (Prod.snd (Prod.snd x_1))) (@Uniform.onFst ℕ Cardinal Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ _ (fun (n : ℕ) (x_1 : Cardinal n) => @Universe.mk n ()) Uniform.makeUniverse) Uniform.unaryAnswer)) (@Uniform.binaryEncodeAnswer ℕ) (Sigma.fst x_11) (Sigma.snd x_11)))) polyH43; exact Poly.lift polyH44 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module Main
namespace OAI

section
namespace ThreeMachine.StackCompiler

theorem requestRawBound_poly : Poly RequestData.size requestRawBound 150011 := by
  have ht := Costs.requestAnswer
  have hb := RequestData.bitsPoly
  have ho := Costs.requestOutputLength
  unfold requestRawBound
  (have polyH0 := Poly.const (RequestData.size) (2000); have polyH1 := Poly.add (ht) (hb); have polyH2 := Poly.add polyH1 (ho); have polyH3 := Poly.const (RequestData.size) (1); have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.mul polyH0 polyH4; exact Poly.lift polyH5 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem requestRawBound_length : Poly (fun x : SmallDeadline => (RequestData.bits x.1).length)
    (fun x => requestRawBound x.1) 150020 := by
  let s (x : SmallDeadline) := (RequestData.bits x.1).length
  have hsize : Poly s (fun x => RequestData.size x.1) 1 := by
    apply Poly.of_le (fun x : SmallDeadline => requestSize_le x.1.2 x.2)
    exact (Poly.const s 4).mul (Poly.size s)
  have h := Poly.reparam (r := 1) requestRawBound_poly (Subtype.val : SmallDeadline → RequestData.Index) hsize
  exact h.lift (by omega)

end ThreeMachine.StackCompiler

end

end OAI

namespace OAI
section
namespace ThreeMachine
open StackCompiler

end ThreeMachine
end
end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.requestRawBound_length := @OAI.ThreeMachine.StackCompiler.requestRawBound_length
