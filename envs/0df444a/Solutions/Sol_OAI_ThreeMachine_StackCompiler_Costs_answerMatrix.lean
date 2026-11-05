-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.answerMatrix
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:57:14.072612+00:00
-- url     : https://prove2.me/submissions/2d487010-3ff9-47d0-9adc-289f06f05634

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_paddedMatrix
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_fullLayers

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false


section
-- module EffectiveFamily
namespace OAI

section

namespace ThreeMachine.Structure
namespace Formula
variable {A B C : Type}

end Formula

theorem assignments_length {A : Type} (alphabet : List A) (k : ℕ) :
    (assignments alphabet k).length = alphabet.length ^ k := by
  induction k with
  | zero => simp [assignments]
  | succ k ih => simp [assignments, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section EffectiveAlphabet
variable {J : Type} [Fintype J] [DecidableEq J]

omit [Fintype J] in
theorem tripleList_length (jobs : List J) : (tripleList jobs).length ≤ jobs.length ^ 3 := by
  calc
    _ ≤ (jobs.flatMap (fun a => jobs.flatMap (fun b => jobs.map
          (fun c => ({a,b,c} : Finset J))))).length := List.length_filterMap_le _ _
    _ = jobs.length ^ 3 := by simp [List.length_flatMap, pow_succ, Nat.mul_assoc]

theorem Atomic.alphabet_length (jobs : List J) :
    (alphabet jobs).length ≤ 2 + 4*(Fintype.card J+2) + 10*jobs.length^3 := by
  have h := tripleList_length jobs
  have he : (alphabet jobs).length = 2 + 4*(Fintype.card J+2) + 10*(tripleList jobs).length := by
    simp [alphabet, List.finRange_succ, Nat.mul_add]
    omega
  rw [he]
  omega

end EffectiveAlphabet
end ThreeMachine.Structure

end

end OAI
end

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
-- module SchedulingAlgorithm
namespace OAI

section

namespace ThreeMachine.Algorithm
section Closure
variable {n : ℕ}

end Closure
end ThreeMachine.Algorithm

namespace ThreeMachine.Structure
section EffectiveFamily
variable {J : Type} [Fintype J] [DecidableEq J]

theorem effectiveFamily_length (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (jobs : List J) (K : ℕ) :
    (effectiveFamily r rank reverseRank jobs K).length =
      (Atomic.alphabet jobs).length^K * (Formula.templates K).length := by
  simp [effectiveFamily,List.length_flatMap,assignments_length]

end EffectiveFamily
end ThreeMachine.Structure

namespace ThreeMachine

end ThreeMachine

namespace ThreeMachine.Algorithm
open Structure

end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure

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

theorem time_getElem?_le (i : I) (xs : List (α i)) (n : ℕ) :
    getElem?.time i (xs,n) ≤ 10000000*(n+1)*(volume xs+n+1) := by
  have hd := time_drop_le i xs n
  have hh := time_head?_le i (xs.drop n)
  have hv := volume_drop_le xs n
  simp only [getElem?,time_congr,time_comp]
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

theorem volumeUniverse (hn : Poly s n d) (v : ∀ i, Universe (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_universe_le (v i))
  (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem volumeCardinal (hn : Poly s n d) (v : ∀ i, Cardinal (n i)) :
    Poly s (fun i => volume (v i)) d := by
  simp only [volume_cardinal]
  (
  have polyH0 := Poly.const (s) (2);
  have polyH1 := Poly.mul polyH0 (hn);
  have polyH2 := Poly.const (s) (1);
  have polyH3 := Poly.add polyH1 polyH2;
  exact Poly.lift polyH3 (by first | decide +kernel | omega))

theorem volumeMatrix (hn : Poly s n d) (v : ∀ i, Matrix (n i)) :
    Poly s (fun i => volume (v i)) (2*d) := by
  apply of_le (fun i => volume_matrix_le (v i))
  (
  have polyH0 := Poly.const (s) (10);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega))

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
  (
  have polyH0 := Poly.const (s) (30000);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hl) polyH1;
  have polyH3 := Poly.mul polyH0 polyH2;
  have polyH4 := Poly.add (hT) (hx);
  have polyH5 := Poly.add polyH4 (he);
  have polyH6 := Poly.add polyH5 (ho);
  have polyH7 := Poly.add polyH6 polyH1;
  have polyH8 := Poly.mul polyH3 polyH7;
  exact Poly.lift polyH8 (by first | decide +kernel | omega))

end Poly
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler
namespace Poly
variable {J : Type u7} {s : J → ℕ} {d : ℕ}

theorem volumeFinRange {n : J → ℕ} (hn : Poly s n d) :
    Poly s (fun j => volume (List.finRange (n j))) (2*d) := by
  apply of_le (fun j => volume_finRange_le (n j))
  (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem finVal {n : J → ℕ} (hn : Poly s n d) (v : ∀ j, Fin (n j)) :
    Poly s (fun j => (v j).val) d := of_le (fun j => Nat.le_of_lt (v j).isLt) hn

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

theorem block_length_le_volume {n : ℕ} (b : Algorithm.Block (Fin n)) : b.length ≤ volume b := by
  rw [volume_block,volume_nat]; omega

theorem block_time_volume_le {n : ℕ} (b : Algorithm.Block (Fin n)) : volume b.time ≤ volume b := by
  rw [volume_block]; omega

namespace Poly
variable {J : Type u1} {s n : J → ℕ} {d e : ℕ}
theorem blockLength (b : ∀ j, Algorithm.Block (Fin (n j)))
    (h : Poly s (fun j => volume (b j)) d) : Poly s (fun j => (b j).length) d :=
  of_le (fun j => block_length_le_volume (b j)) h

theorem blockTime (b : ∀ j, Algorithm.Block (Fin (n j)))
    (h : Poly s (fun j => volume (b j)) d) : Poly s (fun j => volume (b j).time) d :=
  of_le (fun j => block_time_volume_le (b j)) h

variable {α : J → Type u2} {β : J → Type u3} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

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

theorem time_vectorMapAny (d : I → ℕ) {f : ∀ i, Fin (d i) × α i → β i}
    (R : Uniform f) (i : I) (x : Universe (d i) × α i) :
    (R.vectorMapAny d).time i x = ((universeListAny d).onFst.comp R.map).time i x := rfl
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

theorem layers_length {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (fs zs : List (Finset J)) (k : ℕ) :
    (layers r fs zs k).length ≤ fs.length+1 := by
  cases k with
  | zero => simp [layers]
  | succ k => exact (tableOf_length _ _).trans (Nat.le_add_right _ _)

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

namespace Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

theorem volumeTable (tab : ∀ j, Table (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (tab j).length) l) (ht : ∀ j, TableSmall (tab j)) :
    Poly s (fun j => volume (tab j)) (l+2*d) := by
  apply of_le (fun j => volume_table_le (tab j) (ht j))
  (
  have polyH0 := Poly.const (s) (1);
  have polyH1 := Poly.const (s) (30);
  have polyH2 := Poly.add (hn) polyH0;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH1 polyH3;
  have polyH5 := Poly.add polyH4 polyH0;
  have polyH6 := Poly.mul (hl) polyH5;
  have polyH7 := Poly.add polyH0 polyH6;
  exact Poly.lift polyH7 (by first | decide +kernel | omega))

theorem lengthAlphabet (hn : Poly s n d) :
    Poly s (fun j => (Structure.Atomic.alphabet (List.finRange (n j))).length) (3*d) := by
  apply of_le (fun j => Structure.Atomic.alphabet_length (List.finRange (n j)))
  simp only [Fintype.card_fin,List.length_finRange]
  (
  have polyH0 := Poly.const (s) (2);
  have polyH1 := Poly.const (s) (4);
  have polyH2 := Poly.add (hn) polyH0;
  have polyH3 := Poly.mul polyH1 polyH2;
  have polyH4 := Poly.add polyH0 polyH3;
  have polyH5 := Poly.const (s) (10);
  have polyH6 := Poly.pow (hn) (3);
  have polyH7 := Poly.mul polyH5 polyH6;
  have polyH8 := Poly.add polyH4 polyH7;
  exact Poly.lift polyH8 (by first | decide +kernel | omega))

theorem lengthFamily (M : ∀ j, Matrix (n j)) (K : ℕ) (hn : Poly s n d) :
    Poly s (fun j => (Structure.effectiveFamily (matrixRel (M j))
      (Structure.jobRank (matrixRel (M j))) (Structure.reverseJobRank (matrixRel (M j)))
      (List.finRange (n j)) K).length) (3*K*d) := by
  simp only [Structure.effectiveFamily_length]
  have h := (lengthAlphabet hn).pow K
  convert h.mul (const s (Structure.Formula.templates K).length) using 1; ring

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

namespace Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

theorem volumeSmallLookup {K : J → Type} [∀ j, Coding (K j)] [∀ j, DecidableEq (K j)]
    (xs : ∀ j, List (K j × Block (Fin (n j)))) (k : ∀ j, K j)
    (hn : Poly s n d) (hb : ∀ j a b, (a,b) ∈ xs j → BlockSmall b) :
    Poly s (fun j => volume (Algorithm.lookup (xs j) (k j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by (
  have polyH0 := Poly.const (s) (10);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j b h
  exact volume_block_le b (hb j (k j) b (Algorithm.lookup_mem h)).1
    (hb j (k j) b (Algorithm.lookup_mem h)).2

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
  (
  have polyH0 := Poly.const (s) (10000);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hm) polyH1;
  have polyH3 := Poly.mul polyH0 polyH2;
  have polyH4 := Poly.add (hT) (hV);
  have polyH5 := Poly.add polyH4 (hm);
  have polyH6 := Poly.add polyH5 polyH1;
  have polyH7 := Poly.mul polyH3 polyH6;
  exact Poly.lift polyH7 (by first | decide +kernel | omega))
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
-- module TableCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

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

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

theorem volume_list_getD_le {α : Type u1} [Coding α] (xs : List α) (k : ℕ) (a : α) :
    volume (xs.getD k a) ≤ volume xs+volume a := by
  rw [List.getD_eq_getElem?_getD]
  cases h : xs[k]? with
  | none => simp only [Option.getD_none]; omega
  | some b =>
    simp only [Option.getD_some]
    have hv := volume_mem_le (List.mem_of_getElem? h)
    omega

theorem volume_list_getElem?_le {α : Type u2} [Coding α] (xs : List α) (k : ℕ) :
    volume xs[k]? ≤ volume xs+2 := by
  apply volume_option_le
  intro a ha
  exact volume_mem_le (List.mem_of_getElem? ha)

namespace Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]
theorem time_getElemD_le (i : I) (xs : List (α i)) (k : ℕ) (a : α i) :
    getElemD.time i ((xs,k),a) ≤ 1000000000*(k+1)*(volume xs+volume a+k+1) := by
  have hG := time_getElem?_le i xs k
  have hD := time_getD_le i xs[k]? a
  have hV := volume_list_getElem?_le xs k
  simp only [getElemD,time_congr,time_comp,onFst,time_pair,time_fst,time_snd,
    volume_prod,volume_nat,Function.comp_apply]
  nlinarith [volume_pos xs,volume_pos a]

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

namespace Poly
variable {J : Type} (s n T : J → ℕ) (M : ∀ j, Matrix (n j))
theorem volumeSchedule (hn : Poly s n 1) (hT : Poly s T 1) :
    Poly s (fun j => volume (scheduleMatrix (M j) (T j))) 2 := by
  apply volumeOption _ (show Poly s (fun j => 1+n j*(6*T j+2)) 2 from by (
  have polyH0 := Poly.const (s) (1);
  have polyH1 := Poly.const (s) (6);
  have polyH2 := Poly.mul polyH1 (hT);
  have polyH3 := Poly.const (s) (2);
  have polyH4 := Poly.add polyH2 polyH3;
  have polyH5 := Poly.mul (hn) polyH4;
  have polyH6 := Poly.add polyH0 polyH5;
  exact Poly.lift polyH6 (by first | decide +kernel | omega)))
  intro j t ht
  exact volume_function_le t (6*T j+1) (by
    intro v; rw [volume_nat]; have := scheduleMatrix_bound (M j) ht v; omega)

theorem volumeBest (hn : Poly s n 1) (hT : Poly s T 1) :
    Poly s (fun j => volume (bestMatrix (M j) (T j))) 2 := by
  apply volumeOption _ (show Poly s (fun j => (2*T j+1)+(1+n j*(6*T j+2))+1) 2 from by (
  have polyH0 := Poly.const (s) (2);
  have polyH1 := Poly.mul polyH0 (hT);
  have polyH2 := Poly.const (s) (1);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.const (s) (6);
  have polyH5 := Poly.mul polyH4 (hT);
  have polyH6 := Poly.add polyH5 polyH0;
  have polyH7 := Poly.mul (hn) polyH6;
  have polyH8 := Poly.add polyH2 polyH7;
  have polyH9 := Poly.add polyH3 polyH8;
  have polyH10 := Poly.add polyH9 polyH2;
  exact Poly.lift polyH10 (by first | decide +kernel | omega)))
  intro j a ha
  have hb := bestMatrix_bound (M j) ha
  have hv := volume_function_le a.2 (6*T j+1) (by
    intro v; rw [volume_nat]; have := hb.2 v; omega)
  rw [volume_prod,volume_nat]
  have he : 6*T j+1+1=6*T j+2 := by omega
  rw [he] at hv
  omega
end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Realizer
theorem time_triple_le (n : ℕ) : triple.time n ≤ 100000000000*(n+1)^2 := by
  have h1 := time_add_le n n
  have h2 := time_add_le (n+n) n
  simp only [triple,time_congr,time_comp,time_pair,time_id,volume_prod,volume_nat,Function.comp_apply,id_eq]
  nlinarith
end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u2}
theorem time_cardinalMap (d : I → ℕ) {g : ℕ → ℕ} (R : Realizer g) (i : I) (x : Cardinal (d i)) :
    (cardinalMap d R).time i x = R.time (d i) := rfl
theorem time_cardinalValue (d : I → ℕ) (i : I) (x : Cardinal (d i)) :
    (cardinalValue d).time i x = volume x+2 := rfl
theorem time_makeUniverse (n : ℕ) (x : Cardinal n) :
    makeUniverse.time n x = Realizer.range.time n := rfl

theorem time_restrictTime (i : ℕ × ℕ) (x : Universe i.1 × (Fin i.2 → ℕ)) :
    restrictTime.time i x = (restrictCell.vectorMapAny Prod.fst).time i x := rfl
theorem time_recode_input {H : Type u3} {α : I → Type u4} {β : I → Type u5} {δ : H → Type u6} {ε : H → Type u7}
    [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ j, Coding (δ j)] [∀ j, Coding (ε j)]
    {g : ∀ j, δ j → ε j} (R : Uniform g) (f : ∀ i, α i → β i)
    (h : ∀ i x, ∃ j y, enc y = enc x ∧ enc (g j y) = enc (f i x))
    (i : I) (x : α i) (j : H) (y : δ j) (hy : enc x = enc y) :
    (R.recode f h).time i x = R.time j y := congrArg R.charge hy
theorem time_scheduleMatrix (n : ℕ) (x : Universe n × (ℕ × Matrix n)) :
    scheduleMatrix.time n x = scheduleMatrixFixed.time (n,x.2.1) (x.1,(Cardinal.mk (),x.2.2)) := by
  unfold scheduleMatrix
  apply time_recode_input
  rfl
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)
theorem restrictCell (v : ∀ j, Fin (n j)) (hn : Poly s n 1) (_hm : Poly s m 1)
    (hv : Poly s (fun j => volume (r j)) 2) :
    Poly s (fun j => Uniform.restrictCell.time (n j,m j) (v j,r j)) 3 := by
  have ha := Poly.finVal hn v
  simp only [Uniform.restrictCell, Uniform.time_comp, Uniform.time_pair, Uniform.time_fst,
    Uniform.time_snd, Uniform.time_functionListAny, Uniform.time_finValue, Uniform.time_zero,
    Function.comp_apply, volume_ofFn]
  (
  have polyH0 := Poly.volumeFin (hn) (fun (j_1 : J) => v j_1);
  have polyH1 := Poly.volumeProd (fun (j_1 : J) => (v j_1, r j_1)) polyH0 (hv);
  have polyH2 := Poly.const (s) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.add (hv) polyH2;
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.const (s) (10);
  have polyH7 := Poly.const (s) (1);
  have polyH8 := Poly.add (hv) polyH7;
  have polyH9 := Poly.mul polyH6 polyH8;
  have polyH10 := Poly.add polyH5 polyH9;
  have polyH11 := Poly.add polyH0 polyH2;
  have polyH12 := Poly.add polyH3 polyH11;
  have polyH13 := Poly.add polyH0 polyH7;
  have polyH14 := Poly.mul polyH6 polyH13;
  have polyH15 := Poly.add polyH12 polyH14;
  have polyH16 := Poly.add polyH10 polyH15;
  have polyH17 := Poly.const (s) (20);
  have polyH18 := Poly.add polyH1 (hv);
  have polyH19 := Poly.volumeNat (ha);
  have polyH20 := Poly.add polyH18 polyH19;
  have polyH21 := Poly.add polyH20 polyH7;
  have polyH22 := Poly.mul polyH17 polyH21;
  have polyH23 := Poly.add polyH16 polyH22;
  have polyH24 := Poly.add polyH23 polyH2;
  have polyH25 := Poly.volumeProd (fun (j_1 : J) => (List.ofFn (r j_1), Fin.val (v j_1))) (hv) polyH19;
  have polyH26 := Poly.add polyH1 polyH25;
  have polyH27 := Poly.const (s) (volume (0));
  have polyH28 := Poly.add polyH26 polyH27;
  have polyH29 := Poly.add polyH28 polyH7;
  have polyH30 := Poly.mul polyH17 polyH29;
  have polyH31 := Poly.add polyH24 polyH30;
  have polyH32 := Poly.const (s) (1000000000);
  have polyH33 := Poly.add (ha) polyH7;
  have polyH34 := Poly.mul polyH32 polyH33;
  have polyH35 := Poly.add (hv) polyH27;
  have polyH36 := Poly.add polyH35 (ha);
  have polyH37 := Poly.add polyH36 polyH7;
  have polyH38 := Poly.mul polyH34 polyH37;
  have polyH39 := Poly.of_le (fun (j_12 : J) => (@Uniform.time_getElemD_le (ℕ × ℕ) (fun (i : ℕ × ℕ) => ℕ) _ ((n j_12, m j_12)) (List.ofFn (r j_12)) (Fin.val (v j_12)) (0))) polyH38;
  have polyH40 := Poly.add polyH31 polyH39;
  have polyH41 := Poly.const (s) (0);
  have polyH42 := Poly.volumeNat polyH41;
  have polyH43 := Poly.volumeProd (fun (j_1 : J) => ((List.ofFn (r j_1), Fin.val (v j_1)), 0)) polyH25 polyH42;
  have polyH44 := Poly.add polyH43 polyH7;
  have polyH45 := Poly.mul polyH6 polyH44;
  have polyH46 := Poly.add polyH40 polyH45;
  exact Poly.lift polyH46 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)
theorem restrictTime (U : ∀ j, Universe (n j)) (hn : Poly s n 1) (hm : Poly s m 1)
    (hv : Poly s (fun j => volume (r j)) 2) :
    Poly s (fun j => Uniform.restrictTime.time (n j,m j) (U j,r j)) 5 := by
  have hC := restrictCell (fun p : Poly.ListPool (fun j => List.finRange (n j)) => s p.1)
    (fun p => n p.1) (fun p => m p.1) (fun p => r p.1) (fun p => p.2.1)
    (hn.precomp Sigma.fst) (hm.precomp Sigma.fst) (hv.precomp Sigma.fst)
  have hV : Poly (fun p : Poly.ListPool (fun j => List.finRange (n j)) => s p.1)
      (fun p => volume ((List.ofFn (r p.1)).getD p.2.1.val 0)) 2 := by
    apply Poly.of_le (fun p : Poly.ListPool (fun j => List.finRange (n j)) => volume_list_getD_le (List.ofFn (r p.1)) p.2.1.val 0)
    simp only [volume_ofFn,volume_nat]
    have hp := hv.precomp (Sigma.fst : Poly.ListPool (fun j => List.finRange (n j)) → J)
    (
  have polyH0 := Poly.const (fun (p_1 : Poly.ListPool fun (j : J) => List.finRange (n j)) => s (Sigma.fst p_1)) (2 * 0 + 1);
  have polyH1 := Poly.add (hp) polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH0 (hv);
  have polyH2 := Poly.const (s) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _ ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH3;
  have polyH5 := Poly.add polyH0 polyH2;
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.const (s) (10);
  have polyH8 := Poly.const (s) (1);
  have polyH9 := Poly.add polyH0 polyH8;
  have polyH10 := Poly.mul polyH7 polyH9;
  have polyH11 := Poly.add polyH6 polyH10;
  have polyH12 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => (fun (i_1 : ℕ × ℕ) => Universe (Prod.fst i_1)) i × (fun (i_1 : ℕ × ℕ) => Fin (Prod.snd i_1) → ℕ) i) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => List (Fin (Prod.fst i))) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x : Universe (Prod.fst i)) => List.finRange (Prod.fst i)) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _) (@Uniform.universeListAny (ℕ × ℕ) Prod.fst) ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH11;
  have polyH13 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _ ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH3;
  have polyH14 := Poly.add polyH12 polyH13;
  have polyH15 := Poly.const (s) (20);
  have polyH16 := Poly.volumeFinRange (hn);
  have polyH17 := Poly.add polyH1 polyH16;
  have polyH18 := Poly.add polyH17 (hv);
  have polyH19 := Poly.add polyH18 polyH8;
  have polyH20 := Poly.mul polyH15 polyH19;
  have polyH21 := Poly.add polyH14 polyH20;
  have polyH22 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => (fun (i_1 : ℕ × ℕ) => Universe (Prod.fst i_1)) i × (fun (i_1 : ℕ × ℕ) => Fin (Prod.snd i_1) → ℕ) i) (fun (i : ℕ × ℕ) => List (Fin (Prod.fst i))) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _ _ (fun (i : ℕ × ℕ) (x : (fun (i_1 : ℕ × ℕ) => Universe (Prod.fst i_1)) i × (fun (i_1 : ℕ × ℕ) => Fin (Prod.snd i_1) → ℕ) i) => (fun (i_1 : ℕ × ℕ) (x_1 : Universe (Prod.fst i_1)) => List.finRange (Prod.fst i_1)) i (Prod.fst x)) (fun (i : ℕ × ℕ) => Prod.snd) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => (fun (i_1 : ℕ × ℕ) => Universe (Prod.fst i_1)) i × (fun (i_1 : ℕ × ℕ) => Fin (Prod.snd i_1) → ℕ) i) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => List (Fin (Prod.fst i))) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x : Universe (Prod.fst i)) => List.finRange (Prod.fst i)) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _) (@Uniform.universeListAny (ℕ × ℕ) Prod.fst)) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _) ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH21;
  have polyH23 := Poly.lengthFinRange (hn);
  have polyH24 := @Poly.mapTime (ℕ × ℕ) (J) (s) (fun (i : ℕ × ℕ) => Fin (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _ _ (fun (j_1 : J) => (n j_1, m j_1)) (fun (j_1 : J) => Prod.fst (List.finRange (Prod.fst (n j_1, m j_1)), Prod.snd (U j_1, r j_1))) (fun (j_1 : J) => Prod.snd (List.finRange (Prod.fst (n j_1, m j_1)), Prod.snd (U j_1, r j_1))) (fun (i : ℕ × ℕ) (x : Fin (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) => List.getD (List.ofFn (Prod.snd x)) (Fin.val (Prod.fst x)) (0)) (Uniform.restrictCell) (1) (3) (2 * 1) (2) (2) polyH23 (hC) polyH16 (hv) (hV);
  have polyH25 := Poly.add polyH22 polyH24;
  have polyH26 := Poly.volumeProd (fun (j_1 : J) => (List.finRange (Prod.fst (n j_1, m j_1)), Prod.snd (U j_1, r j_1))) polyH16 (hv);
  have polyH27 := Poly.add polyH26 polyH8;
  have polyH28 := Poly.mul polyH7 polyH27;
  have polyH29 := Poly.add polyH25 polyH28;
  have polyH30 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) (fun (i : ℕ × ℕ) => List (Fin (Prod.fst i)) × (Fin (Prod.snd i) → ℕ)) (fun (i : ℕ × ℕ) => List ℕ) _ _ _ (fun (i : ℕ × ℕ) (x : Universe (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) => (List.finRange (Prod.fst i), Prod.snd x)) (fun (i : ℕ × ℕ) (x : List (Fin (Prod.fst i)) × (Fin (Prod.snd i) → ℕ)) => List.map (fun (a : Fin (Prod.fst i)) => List.getD (List.ofFn (Prod.snd (a, Prod.snd x))) (Fin.val (Prod.fst (a, Prod.snd x))) (0)) (Prod.fst x)) (@Uniform.onFst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => List (Fin (Prod.fst i))) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _ _ (fun (i : ℕ × ℕ) (x : Universe (Prod.fst i)) => List.finRange (Prod.fst i)) (@Uniform.universeListAny (ℕ × ℕ) Prod.fst)) (@Uniform.map (ℕ × ℕ) (fun (i : ℕ × ℕ) => Fin (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) _ _ _ (fun (i : ℕ × ℕ) (x : Fin (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) => List.getD (List.ofFn (Prod.snd x)) (Fin.val (Prod.fst x)) (0)) Uniform.restrictCell) ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH29;
  have polyH31 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_vectorMapAny (ℕ × ℕ) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → ℕ) (fun (i : ℕ × ℕ) => ℕ) _ _ (Prod.fst) (fun (i : ℕ × ℕ) (x : Fin (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) => List.getD (List.ofFn (Prod.snd x)) (Fin.val (Prod.fst x)) (0)) (Uniform.restrictCell) ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH30;
  have polyH32 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_restrictTime ((n j_13, m j_13)) ((U j_13, r j_13))))) polyH31;
  exact Poly.lift polyH32 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem restrictTimeBound : Poly
    (fun x : Σ i : ℕ × ℕ, Universe i.1 × (Fin i.2 → ℕ) => x.1.1+x.1.2+volume x.2.2)
    (fun x => Uniform.restrictTime.time x.1 x.2) 5 := by
  let s (x : Σ i : ℕ × ℕ, Universe i.1 × (Fin i.2 → ℕ)) := x.1.1+x.1.2+volume x.2.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hv : Poly s (fun x => volume x.2.2) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  exact restrictTime s (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2.2) (fun x => x.2.1)
    hn hm (hv.lift (by omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n m : J → ℕ} {d e : ℕ}
theorem volumeRestricted (r : ∀ j, Fin (m j) → ℕ) (hn : Poly s n d)
    (hv : Poly s (fun j => volume (r j)) e) :
    Poly s (fun j => volume (fun v : Fin (n j) => (List.ofFn (r j)).getD v.val 0)) (d+e) := by
  have hB : Poly s (fun j => volume (r j)+1) e := by
    simpa only [Nat.max_zero] using hv.add (Poly.const s 1)
  apply Poly.of_le (fun j => volume_function_le
    (fun v : Fin (n j) => (List.ofFn (r j)).getD v.val 0) (volume (r j)+1) (by
      intro v
      simpa only [volume_ofFn,volume_nat,Nat.mul_zero,Nat.zero_add] using
        volume_list_getD_le (List.ofFn (r j)) v.val 0))
  (
  have polyH0 := Poly.const (s) (1);
  have polyH1 := Poly.add (hB) polyH0;
  have polyH2 := Poly.mul (hn) polyH1;
  have polyH3 := Poly.add polyH0 polyH2;
  exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem volumeFullSolve (r : ∀ j, Fin (n j) → Fin (n j) → Prop) [∀ j, DecidableRel (r j)]
    (hn : Poly s n d) : Poly s (fun j => volume (Algorithm.fullSolve (r j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by (
  have polyH0 := Poly.const (s) (10);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j b h
  exact volume_block_le b (fullSolve_small (r j) h).1 (fullSolve_small (r j) h).2
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
-- module SchedulingCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

theorem time_fullSolveK (K n : ℕ) (x : Universe n × Matrix n) :
    (fullSolveK K).time n x = (((fullLayers K).pair (fst.comp universeSet)).comp (lookupA setEq)).time n x := by
  simp only [fullSolveK,time_congr,fullLayers]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem fullSolveK (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.fullSolveK K).time x.1 x.2) 150010 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let fs (x : Σ n, Universe n × Matrix n) := effectiveFamily (matrixRel x.2.2)
    (jobRank (matrixRel x.2.2)) (reverseJobRank (matrixRel x.2.2)) (List.finRange x.1) K
  let zs (x : Σ n, Universe n × Matrix n) := (tripleList (List.finRange x.1)).map Subtype.val
  let tab (x : Σ n, Universe n × Matrix n) := Algorithm.layers (matrixRel x.2.2) (fs x) (zs x) x.1
  have hf : Poly n (fun x => (fs x).length) 30000 :=
    (Poly.lengthFamily (s := n) (n := n) (d := 1) (fun x : Σ n, Universe n × Matrix n => x.2.2) K (Poly.size n)).lift (by omega)
  have hlen : Poly n (fun x => (tab x).length) 30000 := by
    apply Poly.of_le (fun x => Algorithm.layers_length _ _ _ _)
    (
  have polyH0 := Poly.const (n) (1);
  have polyH1 := Poly.add (hf) polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hFL := fullLayers K hk
  have htv := Poly.volumeTable tab (Poly.size n) hlen (fun x => layers_small _ _ _ _)
  have hov := Poly.volumeSmallLookup tab (fun _ => Finset.univ) (Poly.size n) (fun x => layers_small _ _ _ _)
  (
  have polyH0 := Poly.size (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_13) (Sigma.snd x_13)))) polyH5;
  have polyH7 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Sigma.snd x_1).1);
  have polyH8 := Poly.add polyH7 polyH4;
  have polyH9 := Poly.add polyH6 polyH8;
  have polyH10 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (10);
  have polyH11 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (1);
  have polyH12 := Poly.add polyH7 polyH11;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.universeSet) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH14;
  have polyH16 := Poly.add (hFL) polyH15;
  have polyH17 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (20);
  have polyH18 := Poly.add polyH3 (htv);
  have polyH19 := Poly.volumeFinset polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)));
  have polyH20 := Poly.add polyH18 polyH19;
  have polyH21 := Poly.add polyH20 polyH11;
  have polyH22 := Poly.mul polyH17 polyH21;
  have polyH23 := Poly.add polyH16 polyH22;
  have polyH24 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Algorithm.layers (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) n_1) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (Uniform.fullLayers K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeSet) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH23;
  have polyH25 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (100000000000);
  have polyH26 := Poly.add (hlen) polyH11;
  have polyH27 := Poly.mul polyH25 polyH26;
  have polyH28 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Classical.choose Costs.setEq);
  have polyH29 := Poly.base (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1);
  have polyH30 := Poly.pow polyH29 (4);
  have polyH31 := Poly.mul polyH28 polyH30;
  have polyH32 := Poly.add polyH31 (htv);
  have polyH33 := Poly.add polyH32 polyH19;
  have polyH34 := Poly.add polyH33 polyH11;
  have polyH35 := Poly.mul polyH27 polyH34;
  have polyH36 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (@Uniform.time_lookup_setEq_le (Sigma.fst x_13) (OAI.ThreeMachine.Algorithm.layers (matrixRel (Prod.snd (Sigma.snd x_13))) (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd (Sigma.snd x_13))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_13)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_13)))) (List.finRange (Sigma.fst x_13)) K) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_13)))) (Sigma.fst x_13)) ((fun (x_1 : Universe (Sigma.fst x_13)) => @Finset.univ (Fin (Sigma.fst x_13)) (Fin.fintype (Sigma.fst x_13))) (Prod.fst (Sigma.snd x_13))))) polyH35;
  have polyH37 := Poly.add polyH24 polyH36;
  have polyH38 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (OAI.ThreeMachine.Algorithm.layers (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (List.finRange (Sigma.fst x_1)) K) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1)))) (Sigma.fst x_1), (fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)))) (htv) polyH19;
  have polyH39 := Poly.add polyH38 polyH11;
  have polyH40 := Poly.mul polyH10 polyH39;
  have polyH41 := Poly.add polyH37 polyH40;
  have polyH42 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (OAI.ThreeMachine.Algorithm.layers (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) i, (fun (x_2 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1))) (fun (i : ℕ) (x_1 : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Algorithm.layers (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) n_1) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (Uniform.fullLayers K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeSet)) (@Uniform.lookupA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ _ Uniform.setEq) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH41;
  have polyH43 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_fullSolveK (K) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH42;
  exact Poly.lift polyH43 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem fullSolve : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.fullSolve.time x.1 x.2) 150010 := fullSolveK 10000 (by omega)
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
theorem paddedSolve : Poly
    (fun x : Σ i : ℕ × ℕ, Cardinal i.2 × Matrix i.1 => x.1.1+x.1.2)
    (fun x => Uniform.paddedSolve.time x.1 x.2) 150010 := by
  let s (x : Σ i : ℕ × ℕ, Cardinal i.2 × Matrix i.1) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  (
  have polyH0 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => x_1.2.1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => x_1.2.2);
  have polyH2 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => x_1.2) polyH0 polyH1;
  have polyH3 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (2);
  have polyH4 := Poly.add polyH2 polyH3;
  have polyH5 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ (Sigma.fst x_5) (Sigma.snd x_5)))) polyH4;
  have polyH6 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (100000000000);
  have polyH7 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (1);
  have polyH8 := Poly.add (hm) polyH7;
  have polyH9 := Poly.pow polyH8 (2);
  have polyH10 := Poly.mul polyH6 polyH9;
  have polyH11 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Realizer.time_triple_le (Prod.snd (Sigma.fst x_5)))) polyH10;
  have polyH12 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_cardinalMap (ℕ × ℕ) (Prod.snd) (fun (n : ℕ) => 3 * n) (Realizer.triple) (Sigma.fst x_5) (Prod.fst (Sigma.snd x_5))))) polyH11;
  have polyH13 := Poly.add polyH5 polyH12;
  have polyH14 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (10);
  have polyH15 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (Sigma.snd x_1).1);
  have polyH16 := Poly.add polyH15 polyH7;
  have polyH17 := Poly.mul polyH14 polyH16;
  have polyH18 := Poly.add polyH13 polyH17;
  have polyH19 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH18;
  have polyH20 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (3);
  have polyH21 := Poly.mul polyH20 (hm);
  have polyH22 := Poly.add polyH21 polyH7;
  have polyH23 := Poly.pow polyH22 (3);
  have polyH24 := Poly.mul polyH6 polyH23;
  have polyH25 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Realizer.time_range_le (3 * Prod.snd (Sigma.fst x_5)))) polyH24;
  have polyH26 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_makeUniverse (3 * Prod.snd (Sigma.fst x_5)) ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_5))) => @Cardinal.mk (3 * Prod.snd (Sigma.fst x_5)) ()) (Prod.fst (Sigma.snd x_5)))))) polyH25;
  have polyH27 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_reindex (ℕ) (Cardinal) (Universe) _ _ (fun (n : ℕ) (x_1 : Cardinal n) => @Universe.mk n ()) (Uniform.makeUniverse) (ℕ × ℕ) (fun (i : ℕ × ℕ) => 3 * Prod.snd i) (Sigma.fst x_5) ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_5))) => @Cardinal.mk (3 * Prod.snd (Sigma.fst x_5)) ()) (Prod.fst (Sigma.snd x_5)))))) polyH26;
  have polyH28 := Poly.add polyH19 polyH27;
  have polyH29 := Poly.volumeCardinal polyH21 (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Cardinal.mk (3 * Prod.snd (Sigma.fst x_1)) ());
  have polyH30 := Poly.add polyH29 polyH7;
  have polyH31 := Poly.mul polyH14 polyH30;
  have polyH32 := Poly.add polyH28 polyH31;
  have polyH33 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH32;
  have polyH34 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ (Sigma.fst x_5) (Sigma.snd x_5)))) polyH4;
  have polyH35 := Poly.add polyH33 polyH34;
  have polyH36 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (20);
  have polyH37 := Poly.volumeUniverse polyH21 (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd (Sigma.fst x_1)) ());
  have polyH38 := Poly.add polyH2 polyH37;
  have polyH39 := Poly.volumeMatrix (hn) (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (Sigma.snd x_1).2);
  have polyH40 := Poly.add polyH38 polyH39;
  have polyH41 := Poly.add polyH40 polyH7;
  have polyH42 := Poly.mul polyH36 polyH41;
  have polyH43 := Poly.add polyH35 polyH42;
  have polyH44 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd i) ()) (fun (i : ℕ × ℕ) => Prod.snd) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH43;
  have polyH45 := Poly.add (hn) polyH21;
  have polyH46 := Poly.reparam (@Costs.paddedMatrix) (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Sigma.mk (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)) (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), Prod.snd (Sigma.snd x_1))) polyH45;
  have polyH47 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_reindex (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → Fin (Prod.snd i) → Bool) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.snd i) × Matrix (Prod.fst i)) (a b : Fin (Prod.snd i)) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd i) a b)) (Uniform.paddedMatrix) (ℕ × ℕ) (fun (i : ℕ × ℕ) => (Prod.fst i, 3 * Prod.snd i)) (Sigma.fst x_5) ((@Universe.mk (3 * Prod.snd (Sigma.fst x_5)) (), Prod.snd (Sigma.snd x_5)))))) polyH46;
  have polyH48 := Poly.add polyH44 polyH47;
  have polyH49 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), Prod.snd (Sigma.snd x_1))) polyH37 polyH39;
  have polyH50 := Poly.add polyH49 polyH7;
  have polyH51 := Poly.mul polyH14 polyH50;
  have polyH52 := Poly.add polyH48 polyH51;
  have polyH53 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), Prod.snd x_1)) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.snd (Prod.fst j, 3 * Prod.snd j)) × Matrix (Prod.fst (Prod.fst j, 3 * Prod.snd j))) (a b : Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd (Prod.fst j, 3 * Prod.snd j)) a b)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd i) ()) (fun (i : ℕ × ℕ) => Prod.snd) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.reindex (ℕ × ℕ) (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → Fin (Prod.snd i) → Bool) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.snd i) × Matrix (Prod.fst i)) (a b : Fin (Prod.snd i)) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd i) a b)) Uniform.paddedMatrix fun (i : ℕ × ℕ) => (Prod.fst i, 3 * Prod.snd i)) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH52;
  have polyH54 := Poly.add polyH33 polyH53;
  have polyH55 := Poly.volumeMatrix polyH21 (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (a b : Fin (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), Prod.snd x_2)) (Sigma.snd x_1)))) (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1))) a b));
  have polyH56 := Poly.add polyH38 polyH55;
  have polyH57 := Poly.add polyH56 polyH7;
  have polyH58 := Poly.mul polyH36 polyH57;
  have polyH59 := Poly.add polyH54 polyH58;
  have polyH60 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) (fun (j : ℕ × ℕ) => Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd i) ()) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Universe (Prod.snd (Prod.fst i, 3 * Prod.snd i)) × Matrix (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (a b : Fin (Prod.snd (Prod.fst i, 3 * Prod.snd i))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (Prod.snd (Prod.fst i, 3 * Prod.snd i)) a b)) ((fun (x_2 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), Prod.snd x_2)) x_1)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), Prod.snd x_1)) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.snd (Prod.fst j, 3 * Prod.snd j)) × Matrix (Prod.fst (Prod.fst j, 3 * Prod.snd j))) (a b : Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd (Prod.fst j, 3 * Prod.snd j)) a b)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd i) ()) (fun (i : ℕ × ℕ) => Prod.snd) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.reindex (ℕ × ℕ) (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → Fin (Prod.snd i) → Bool) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.snd i) × Matrix (Prod.fst i)) (a b : Fin (Prod.snd i)) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd i) a b)) Uniform.paddedMatrix fun (i : ℕ × ℕ) => (Prod.fst i, 3 * Prod.snd i))) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH59;
  have polyH61 := Poly.reparam (@Costs.fullSolve) (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Sigma.mk (3 * Prod.snd (Sigma.fst x_1)) (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), (fun (x_2 : Universe (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1))) × Matrix (Prod.fst (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)))) (a b : Fin (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1))) a b)) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), Prod.snd x_2)) (Sigma.snd x_1)))) polyH21;
  have polyH62 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_reindex (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n))) _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => OAI.ThreeMachine.Algorithm.fullSolve (matrixRel (Prod.snd x_1))) (Uniform.fullSolve) (ℕ × ℕ) (fun (i : ℕ × ℕ) => 3 * Prod.snd i) (Sigma.fst x_5) ((@Universe.mk (3 * Prod.snd (Sigma.fst x_5)) (), (fun (x_1 : Universe (Prod.snd (Prod.fst (Sigma.fst x_5), 3 * Prod.snd (Sigma.fst x_5))) × Matrix (Prod.fst (Prod.fst (Sigma.fst x_5), 3 * Prod.snd (Sigma.fst x_5)))) (a b : Fin (Prod.snd (Prod.fst (Sigma.fst x_5), 3 * Prod.snd (Sigma.fst x_5)))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd (Prod.fst (Sigma.fst x_5), 3 * Prod.snd (Sigma.fst x_5))) a b)) ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_5)) × Matrix (Prod.fst (Sigma.fst x_5))) => (@Universe.mk (3 * Prod.snd (Sigma.fst x_5)) (), Prod.snd x_1)) (Sigma.snd x_5))))))) polyH61;
  have polyH63 := Poly.add polyH60 polyH62;
  have polyH64 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), (fun (x_2 : Universe (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1))) × Matrix (Prod.fst (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)))) (a b : Fin (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (Prod.snd (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1))) a b)) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => (@Universe.mk (3 * Prod.snd (Sigma.fst x_1)) (), Prod.snd x_2)) (Sigma.snd x_1)))) polyH37 polyH55;
  have polyH65 := Poly.add polyH64 polyH7;
  have polyH66 := Poly.mul polyH14 polyH65;
  have polyH67 := Poly.add polyH63 polyH66;
  have polyH68 := Poly.of_le (fun (x_5 : (i : ℕ × ℕ) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i) × (Fin (Prod.snd (Prod.fst i, 3 * Prod.snd i)) → Fin (Prod.snd (Prod.fst i, 3 * Prod.snd i)) → Bool)) (fun (j : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j)))) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), (fun (x_2 : Universe (Prod.snd (Prod.fst i, 3 * Prod.snd i)) × Matrix (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (a b : Fin (Prod.snd (Prod.fst i, 3 * Prod.snd i))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (Prod.snd (Prod.fst i, 3 * Prod.snd i)) a b)) ((fun (x_2 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), Prod.snd x_2)) x_1))) (fun (j : ℕ × ℕ) (x_1 : Universe (3 * Prod.snd j) × Matrix (3 * Prod.snd j)) => OAI.ThreeMachine.Algorithm.fullSolve (matrixRel (Prod.snd x_1))) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) (fun (j : ℕ × ℕ) => Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd i) ()) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Universe (Prod.snd (Prod.fst i, 3 * Prod.snd i)) × Matrix (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (a b : Fin (Prod.snd (Prod.fst i, 3 * Prod.snd i))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (Prod.snd (Prod.fst i, 3 * Prod.snd i)) a b)) ((fun (x_2 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), Prod.snd x_2)) x_1)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (@Universe.mk (3 * Prod.snd i) (), Prod.snd x_1)) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.snd (Prod.fst j, 3 * Prod.snd j)) × Matrix (Prod.fst (Prod.fst j, 3 * Prod.snd j))) (a b : Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j))) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd (Prod.fst j, 3 * Prod.snd j)) a b)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Universe.mk (3 * Prod.snd i) ()) (fun (i : ℕ × ℕ) => Prod.snd) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) (fun (i : ℕ × ℕ) => Universe (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (3 * Prod.snd i)) => @Universe.mk (3 * Prod.snd i) ()) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Cardinal (3 * Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => @Cardinal.mk (3 * Prod.snd i) ()) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (@Uniform.cardinalMap (ℕ × ℕ) Prod.snd (fun (n : ℕ) => 3 * n) Realizer.triple)) (@Uniform.makeUniverseAny (ℕ × ℕ) fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.reindex (ℕ × ℕ) (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.snd i) → Fin (Prod.snd i) → Bool) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.snd i) × Matrix (Prod.fst i)) (a b : Fin (Prod.snd i)) => Decidable.decide (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (Prod.snd i) a b)) Uniform.paddedMatrix fun (i : ℕ × ℕ) => (Prod.fst i, 3 * Prod.snd i)))) (@Uniform.reindex ℕ (ℕ × ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n))) _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => OAI.ThreeMachine.Algorithm.fullSolve (matrixRel (Prod.snd x_1))) Uniform.fullSolve fun (i : ℕ × ℕ) => 3 * Prod.snd i) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH67;
  have hZ := Poly.lift (e := 150010) polyH68 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega);
  refine Poly.of_le (fun x => le_of_eq ?_) hZ;
  unfold Uniform.paddedSolve;
  exact Uniform.time_congr _ _ _ _)
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_scheduleMatrixFixed (i : ℕ × ℕ) (x : Universe i.1 × (Cardinal i.2 × Matrix i.1)) :
    scheduleMatrixFixed.time i x =
      (((((fst.comp (universeNumber.reindex Prod.fst)).pair
        ((snd.comp fst).comp (cardinalValue Prod.snd) |>.comp (Realizer.triple.uniform (ℕ × ℕ)))).comp
        (Realizer.le.uniform (ℕ × ℕ))).pair id).comp (scheduleCandidate.choose none)).time i x := by
  simp only [scheduleMatrixFixed,time_congr,scheduleCandidate,scheduleRestriction]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem scheduleRestriction : Poly
    (fun x : Σ i : ℕ × ℕ, Algorithm.Block (Fin (3*i.2)) × Universe i.1 => x.1.1+x.1.2+volume x.2.1)
    (fun x => Uniform.scheduleRestriction.time x.1 x.2) 10 := by
  let s (x : Σ i : ℕ × ℕ, Algorithm.Block (Fin (3*i.2)) × Universe i.1) := x.1.1+x.1.2+volume x.2.1
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  have hv : Poly s (fun x => volume x.2.1) 1 := Poly.of_le (fun x => by dsimp [s]; omega) (Poly.size s)
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => x_1.2.2);
  have polyH1 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => x_1.2) (hv) polyH0;
  have polyH2 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1) + volume (Prod.fst (Sigma.snd x_1))) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_snd (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _ (Sigma.fst x_6) (Sigma.snd x_6)))) polyH3;
  have polyH5 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _ (Sigma.fst x_6) (Sigma.snd x_6)))) polyH3;
  have polyH6 := Poly.add (hv) polyH2;
  have polyH7 := Poly.blockLength (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.snd x_1)) (hv);
  have polyH8 := Poly.volumeNat polyH7;
  have polyH9 := Poly.blockTime (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.snd x_1)) (hv);
  have polyH10 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (OAI.ThreeMachine.Algorithm.Block.length (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.Block.time (Prod.fst (Sigma.snd x_1)))) polyH8 polyH9;
  have polyH11 := Poly.add polyH10 polyH2;
  have polyH12 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ (3 * Prod.snd (Sigma.fst x_6)) ((OAI.ThreeMachine.Algorithm.Block.length (Prod.fst (Sigma.snd x_6)), OAI.ThreeMachine.Algorithm.Block.time (Prod.fst (Sigma.snd x_6))))))) polyH11;
  have polyH13 := Poly.add polyH6 polyH12;
  have polyH14 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1) + volume (Prod.fst (Sigma.snd x_1))) (10);
  have polyH15 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1) + volume (Prod.fst (Sigma.snd x_1))) (1);
  have polyH16 := Poly.add polyH10 polyH15;
  have polyH17 := Poly.mul polyH14 polyH16;
  have polyH18 := Poly.add polyH13 polyH17;
  have polyH19 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) (fun (n : ℕ) => ℕ × (Fin n → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (n : ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin n)) => (OAI.ThreeMachine.Algorithm.Block.length s_1, OAI.ThreeMachine.Algorithm.Block.time s_1)) (fun (i : ℕ) => Prod.snd) (Uniform.blockParts) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _) (3 * Prod.snd (Sigma.fst x_6)) (Prod.fst (Sigma.snd x_6))))) polyH18;
  have polyH20 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_reindex (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) (fun (n : ℕ) => Fin n → ℕ) _ _ (fun (n : ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin n)) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Uniform.blockTime) (ℕ × ℕ) (fun (i : ℕ × ℕ) => 3 * Prod.snd i) (Sigma.fst x_6) (Prod.fst (Sigma.snd x_6))))) polyH19;
  have polyH21 := Poly.add polyH5 polyH20;
  have polyH22 := Poly.add (hv) polyH15;
  have polyH23 := Poly.mul polyH14 polyH22;
  have polyH24 := Poly.add polyH21 polyH23;
  have polyH25 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (j : ℕ × ℕ) => Fin (3 * Prod.snd j) → ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) (fun (n : ℕ) => Fin n → ℕ) _ _ (fun (n : ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin n)) => OAI.ThreeMachine.Algorithm.Block.time s_1) Uniform.blockTime fun (i : ℕ × ℕ) => 3 * Prod.snd i) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH24;
  have polyH26 := Poly.add polyH4 polyH25;
  have polyH27 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1) + volume (Prod.fst (Sigma.snd x_1))) (20);
  have polyH28 := Poly.volumeUniverse (hn) (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (Sigma.snd x_1).2);
  have polyH29 := Poly.add polyH1 polyH28;
  have polyH30 := Poly.add polyH29 polyH9;
  have polyH31 := Poly.add polyH30 polyH15;
  have polyH32 := Poly.mul polyH27 polyH31;
  have polyH33 := Poly.add polyH26 polyH32;
  have polyH34 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (j : ℕ × ℕ) => Fin (3 * Prod.snd j) → ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) => (fun (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Prod.fst x_1)) (@Uniform.snd (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (j : ℕ × ℕ) => Fin (3 * Prod.snd j) → ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) (fun (n : ℕ) => Fin n → ℕ) _ _ (fun (n : ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin n)) => OAI.ThreeMachine.Algorithm.Block.time s_1) Uniform.blockTime fun (i : ℕ × ℕ) => 3 * Prod.snd i)) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH33;
  have polyH35 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1) + volume (Prod.fst (Sigma.snd x_1))) (3);
  have polyH36 := Poly.mul polyH35 (hm);
  have polyH37 := Poly.add (hn) polyH36;
  have polyH38 := Poly.add polyH37 polyH9;
  have polyH39 := Poly.reparam (@Costs.restrictTimeBound) (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => Sigma.mk (Prod.fst (Sigma.fst x_1), 3 * Prod.snd (Sigma.fst x_1)) (Prod.snd (Sigma.snd x_1), (fun (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd (Sigma.fst x_1)))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Prod.fst (Sigma.snd x_1)))) polyH38;
  have polyH40 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_reindex (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (Prod.snd x_1)) (Fin.val v) (0)) (Uniform.restrictTime) (ℕ × ℕ) (fun (i : ℕ × ℕ) => (Prod.fst i, 3 * Prod.snd i)) (Sigma.fst x_6) ((Prod.snd (Sigma.snd x_6), (fun (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd (Sigma.fst x_6)))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Prod.fst (Sigma.snd x_6))))))) polyH39;
  have polyH41 := Poly.add polyH34 polyH40;
  have polyH42 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (Prod.snd (Sigma.snd x_1), (fun (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd (Sigma.fst x_1)))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Prod.fst (Sigma.snd x_1)))) polyH28 polyH9;
  have polyH43 := Poly.add polyH42 polyH15;
  have polyH44 := Poly.mul polyH14 polyH43;
  have polyH45 := Poly.add polyH41 polyH44;
  have polyH46 := Poly.of_le (fun (x_6 : (i : ℕ × ℕ) × OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i)) × (Fin (3 * Prod.snd i) → ℕ)) (fun (j : ℕ × ℕ) => Fin (Prod.fst (Prod.fst j, 3 * Prod.snd j)) → ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) => (Prod.snd x_1, (fun (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Prod.fst x_1))) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.fst (Prod.fst j, 3 * Prod.snd j)) × (Fin (Prod.snd (Prod.fst j, 3 * Prod.snd j)) → ℕ)) (v : Fin (Prod.fst (Prod.fst j, 3 * Prod.snd j))) => List.getD (List.ofFn (Prod.snd x_1)) (Fin.val v) (0)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (j : ℕ × ℕ) => Fin (3 * Prod.snd j) → ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) => (fun (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (Prod.fst x_1)) (@Uniform.snd (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (j : ℕ × ℕ) => Fin (3 * Prod.snd j) → ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) => OAI.ThreeMachine.Algorithm.Block.time s_1) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd j))) (fun (i : ℕ × ℕ) => Universe (Prod.fst (Prod.fst i, 3 * Prod.snd i))) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) (fun (n : ℕ) => Fin n → ℕ) _ _ (fun (n : ℕ) (s_1 : OAI.ThreeMachine.Algorithm.Block (Fin n)) => OAI.ThreeMachine.Algorithm.Block.time s_1) Uniform.blockTime fun (i : ℕ × ℕ) => 3 * Prod.snd i))) (@Uniform.reindex (ℕ × ℕ) (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × (Fin (Prod.snd i) → ℕ)) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (Prod.snd x_1)) (Fin.val v) (0)) Uniform.restrictTime fun (i : ℕ × ℕ) => (Prod.fst i, 3 * Prod.snd i)) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH45;
  exact Poly.lift polyH46 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

theorem candidateVolume {J : Type} (s n T : J → ℕ) (M : ∀ j, Matrix (n j))
    (hn : Poly s n 1) (hT : Poly s T 1) :
    Poly s (fun j => volume ((Algorithm.fullSolve (paddedOrder (matrixRel (M j)) (3*T j))).map
      (fun b => (fun v : Fin (n j) => (List.ofFn b.time).getD v.val 0)))) 3 := by
  have h3 : Poly s (fun j => 3*T j) 1 := by (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.mul polyH0 (hT);
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  let o (j : J) := Algorithm.fullSolve (paddedOrder (matrixRel (M j)) (3*T j))
  have hO : Poly s (fun j => volume (o j)) 2 := Poly.volumeFullSolve _ h3
  have hP := Poly.volumePool (fun j => (o j).toList) (Poly.volumeOptionToList o hO)
  have hBT := Poly.blockTime (fun p : Poly.ListPool (fun j => (o j).toList) => p.2.1) hP
  have hR := Poly.volumeRestricted (n := fun p : Poly.ListPool (fun j => (o j).toList) => n p.1)
    (fun p : Poly.ListPool (fun j => (o j).toList) => p.2.1.time)
    (hn.precomp Sigma.fst) hBT
  exact Poly.volumeOptionMap (fun (j : J) (b : Algorithm.Block (Fin (3*T j))) => (fun v : Fin (n j) => (List.ofFn b.time).getD v.val 0)) o hR

theorem scheduleCandidate : Poly
    (fun x : Σ i : ℕ × ℕ, ScheduleInput i => x.1.1+x.1.2)
    (fun x => Uniform.scheduleCandidate.time x.1 x.2) 150010 := by
  let s (x : Σ i : ℕ × ℕ, ScheduleInput i) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have h3 : Poly s (fun x => 3*x.1.2) 1 := by (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.mul polyH0 (hm);
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  let o (x : Σ i : ℕ × ℕ, ScheduleInput i) := Algorithm.fullSolve (paddedOrder (matrixRel x.2.2.2) (3*x.1.2))
  have hO : Poly s (fun x => volume (o x)) 2 := Poly.volumeFullSolve _ h3
  have hP := Poly.volumePool (fun x => (o x).toList) (Poly.volumeOptionToList o hO)
  have hT := Poly.blockTime (fun p : Poly.ListPool (fun x => (o x).toList) => p.2.1) hP
  have hR := Poly.volumeRestricted (n := fun p : Poly.ListPool (fun x => (o x).toList) => p.1.1.1)
    (fun p : Poly.ListPool (fun x => (o x).toList) => p.2.1.time)
    (hn.precomp Sigma.fst) hT
  have hnp := hn.precomp (Sigma.fst : Poly.ListPool (fun x => (o x).toList) → _)
  have hmp := hm.precomp (Sigma.fst : Poly.ListPool (fun x => (o x).toList) → _)
  have hRC : Poly (fun p : Poly.ListPool (fun x => (o x).toList) => s p.1)
      (fun p => Uniform.scheduleRestriction.time p.1.1 (p.2.1,p.1.2.1)) 20 := by
    have hs : Poly (fun p : Poly.ListPool (fun x => (o x).toList) => s p.1)
        (fun p => p.1.1.1+p.1.1.2+volume p.2.1) 2 := by
      exact (hnp.add hmp).add hP
    exact Poly.reparam (r := 2) (d := 10) scheduleRestriction
      (fun p : Poly.ListPool (fun x => (o x).toList) => ⟨p.1.1,(p.2.1,p.1.2.1)⟩) hs
  have hU := Poly.volumeUniverse hn (fun x => x.2.1)
  have hOpt := Poly.optionMapTime (fun x : Σ i, ScheduleInput i => x.1) (fun x => x.2.1) o
    Uniform.scheduleRestriction hRC hO hU hR
  (
  have polyH0 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.2.1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.2.2);
  have polyH2 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.2) polyH0 polyH1;
  have polyH3 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2) (hU) polyH2;
  have polyH4 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_16 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ (Sigma.fst x_16) (Sigma.snd x_16)))) polyH5;
  have polyH7 := Poly.size (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1));
  have polyH8 := Poly.reparam (@Costs.paddedSolve) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Sigma.mk (Sigma.fst x_1) (Prod.snd (Sigma.snd x_1))) polyH7;
  have polyH9 := Poly.add polyH6 polyH8;
  have polyH10 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (10);
  have polyH11 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).2.1);
  have polyH12 := Poly.volumeMatrix (hn) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).2.2);
  have polyH13 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).2) polyH11 polyH12;
  have polyH14 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (1);
  have polyH15 := Poly.add polyH13 polyH14;
  have polyH16 := Poly.mul polyH10 polyH15;
  have polyH17 := Poly.add polyH9 polyH16;
  have polyH18 := Poly.of_le (fun (x_16 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)))) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (3 * Prod.snd i))) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (Uniform.paddedSolve) (Sigma.fst x_16) (Sigma.snd x_16)))) polyH17;
  have polyH19 := Poly.of_le (fun (x_16 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ (Sigma.fst x_16) (Sigma.snd x_16)))) polyH5;
  have polyH20 := Poly.add polyH18 polyH19;
  have polyH21 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (20);
  have polyH22 := Poly.add polyH3 (hO);
  have polyH23 := Poly.add polyH22 (hU);
  have polyH24 := Poly.add polyH23 polyH14;
  have polyH25 := Poly.mul polyH21 polyH24;
  have polyH26 := Poly.add polyH20 polyH25;
  have polyH27 := Poly.of_le (fun (x_16 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)))) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (3 * Prod.snd i))) (Prod.snd x_1)) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)))) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (3 * Prod.snd i))) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) Uniform.paddedSolve) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (Sigma.fst x_16) (Sigma.snd x_16)))) polyH26;
  have polyH28 := Poly.add polyH27 (hOpt);
  have polyH29 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (3 * Prod.snd (Sigma.fst x_1)))) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) (hO) (hU);
  have polyH30 := Poly.add polyH29 polyH14;
  have polyH31 := Poly.mul polyH10 polyH30;
  have polyH32 := Poly.add polyH28 polyH31;
  have polyH33 := Poly.of_le (fun (x_16 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) × Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (Fin (Prod.fst i) → ℕ)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_2 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (3 * Prod.snd i))) (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) × Universe (Prod.fst i)) => Option.map (fun (a : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (OAI.ThreeMachine.Algorithm.Block.time (Prod.fst (a, Prod.snd x_1)))) (Fin.val v) (0)) (Prod.fst x_1)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)))) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_2)) (3 * Prod.snd i))) (Prod.snd x_1)) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)))) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd x_1)) (3 * Prod.snd i))) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) Uniform.paddedSolve) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _)) (@Uniform.optionMap (ℕ × ℕ) (fun (i : ℕ × ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i)) × Universe (Prod.fst i)) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (OAI.ThreeMachine.Algorithm.Block.time (Prod.fst x_1))) (Fin.val v) (0)) Uniform.scheduleRestriction) (Sigma.fst x_16) (Sigma.snd x_16)))) polyH32;
  exact Poly.lift polyH33 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem scheduleMatrixFixed : Poly
    (fun x : Σ i : ℕ × ℕ, ScheduleInput i => x.1.1+x.1.2)
    (fun x => Uniform.scheduleMatrixFixed.time x.1 x.2) 150010 := by
  let s (x : Σ i : ℕ × ℕ, ScheduleInput i) := x.1.1+x.1.2
  have hn : Poly s (fun x => x.1.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.1.2) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have h3 : Poly s (fun x => 3*x.1.2) 1 := by (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.mul polyH0 (hm);
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hO := Poly.volumeFullSolve
    (fun x : Σ i : ℕ × ℕ, ScheduleInput i => paddedOrder (matrixRel x.2.2.2) (3*x.1.2)) h3
  have hV := candidateVolume s (fun x => x.1.1) (fun x => x.1.2) (fun x => x.2.2.2) hn hm
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.1);
  have polyH1 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.2.1);
  have polyH2 := Poly.volumeMatrix (hn) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2.2) polyH1 polyH2;
  have polyH4 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => x_1.2) polyH0 polyH3;
  have polyH5 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ (Sigma.fst x_8) (Sigma.snd x_8)))) polyH6;
  have polyH8 := Poly.volumeUniverse (hn) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).1);
  have polyH9 := Poly.add polyH8 polyH5;
  have polyH10 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (100000);
  have polyH11 := Poly.lengthFinRange (hn);
  have polyH12 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (1);
  have polyH13 := Poly.add polyH11 polyH12;
  have polyH14 := Poly.mul polyH10 polyH13;
  have polyH15 := Poly.volumeFinRange (hn);
  have polyH16 := Poly.add polyH15 polyH12;
  have polyH17 := Poly.mul polyH14 polyH16;
  have polyH18 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (@Uniform.time_length_le (ℕ) (Fin) _ (Prod.fst (Sigma.fst x_8)) (List.finRange (Prod.fst (Sigma.fst x_8))))) polyH17;
  have polyH19 := Poly.add polyH9 polyH18;
  have polyH20 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (10);
  have polyH21 := Poly.mul polyH20 polyH16;
  have polyH22 := Poly.add polyH19 polyH21;
  have polyH23 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (Prod.fst (Sigma.fst x_8)) (Prod.fst (Sigma.snd x_8))))) polyH22;
  have polyH24 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_reindex (ℕ) (Universe) (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Universe n) => n) (Uniform.universeNumber) (ℕ × ℕ) (Prod.fst) (Sigma.fst x_8) (Prod.fst (Sigma.snd x_8))))) polyH23;
  have polyH25 := Poly.add polyH7 polyH24;
  have polyH26 := Poly.add polyH8 polyH12;
  have polyH27 := Poly.mul polyH20 polyH26;
  have polyH28 := Poly.add polyH25 polyH27;
  have polyH29 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (j : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.fst j)) => Prod.fst j) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) Universe (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Universe n) => n) Uniform.universeNumber Prod.fst) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH28;
  have polyH30 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ (Sigma.fst x_8) (Sigma.snd x_8)))) polyH6;
  have polyH31 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).2.1);
  have polyH32 := Poly.volumeMatrix (hn) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).2.2);
  have polyH33 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Sigma.snd x_1).2) polyH31 polyH32;
  have polyH34 := Poly.add polyH33 polyH5;
  have polyH35 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _ (Sigma.fst x_8) (Prod.snd (Sigma.snd x_8))))) polyH34;
  have polyH36 := Poly.add polyH30 polyH35;
  have polyH37 := Poly.add polyH33 polyH12;
  have polyH38 := Poly.mul polyH20 polyH37;
  have polyH39 := Poly.add polyH36 polyH38;
  have polyH40 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH39;
  have polyH41 := Poly.volumeCardinal (hm) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (Prod.snd (Sigma.snd x_1)).1);
  have polyH42 := Poly.add polyH41 polyH5;
  have polyH43 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_cardinalValue (ℕ × ℕ) (Prod.snd) (Sigma.fst x_8) (Prod.fst (Prod.snd (Sigma.snd x_8)))))) polyH42;
  have polyH44 := Poly.add polyH40 polyH43;
  have polyH45 := Poly.add polyH41 polyH12;
  have polyH46 := Poly.mul polyH20 polyH45;
  have polyH47 := Poly.add polyH44 polyH46;
  have polyH48 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => Prod.snd i) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.cardinalValue (ℕ × ℕ) Prod.snd) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH47;
  have polyH49 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (100000000000);
  have polyH50 := Poly.add (hm) polyH12;
  have polyH51 := Poly.pow polyH50 (2);
  have polyH52 := Poly.mul polyH49 polyH51;
  have polyH53 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (@Realizer.time_triple_le ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd (Sigma.snd x_8)))))) polyH52;
  have polyH54 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_uniform (ℕ × ℕ) (ℕ) (ℕ) _ _ (fun (n : ℕ) => 3 * n) (Realizer.triple) (Sigma.fst x_8) ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd (Sigma.snd x_8))))))) polyH53;
  have polyH55 := Poly.add polyH48 polyH54;
  have polyH56 := Poly.volumeNat (hm);
  have polyH57 := Poly.add polyH56 polyH12;
  have polyH58 := Poly.mul polyH20 polyH57;
  have polyH59 := Poly.add polyH55 polyH58;
  have polyH60 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))) (fun (x_1 : ℕ × ℕ) (n : ℕ) => 3 * n) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => Prod.snd i) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.cardinalValue (ℕ × ℕ) Prod.snd)) (Realizer.uniform Realizer.triple (ℕ × ℕ)) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH59;
  have polyH61 := Poly.add polyH29 polyH60;
  have polyH62 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (20);
  have polyH63 := Poly.volumeNat (hn);
  have polyH64 := Poly.add polyH4 polyH63;
  have polyH65 := Poly.volumeNat (h3);
  have polyH66 := Poly.add polyH64 polyH65;
  have polyH67 := Poly.add polyH66 polyH12;
  have polyH68 := Poly.mul polyH62 polyH67;
  have polyH69 := Poly.add polyH61 polyH68;
  have polyH70 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1)))) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (j : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.fst j)) => Prod.fst j) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) Universe (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Universe n) => n) Uniform.universeNumber Prod.fst)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))) (fun (x_1 : ℕ × ℕ) (n : ℕ) => 3 * n) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => Prod.snd i) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.cardinalValue (ℕ × ℕ) Prod.snd)) (Realizer.uniform Realizer.triple (ℕ × ℕ))) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH69;
  have polyH71 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (1000000000);
  have polyH72 := Poly.add (hn) (h3);
  have polyH73 := Poly.add polyH72 polyH12;
  have polyH74 := Poly.pow polyH73 (2);
  have polyH75 := Poly.mul polyH71 polyH74;
  have polyH76 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (@Realizer.time_le_le ((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst (Sigma.snd x_8))) ((fun (n : ℕ) => 3 * n) ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd (Sigma.snd x_8))))))) polyH75;
  have polyH77 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_uniform (ℕ × ℕ) (ℕ × ℕ) (Bool) _ _ (fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) (Realizer.le) (Sigma.fst x_8) (((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst (Sigma.snd x_8)), (fun (n : ℕ) => 3 * n) ((fun (x_1 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd (Sigma.snd x_8))))))))) polyH76;
  have polyH78 := Poly.add polyH70 polyH77;
  have polyH79 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_1))) => Prod.fst (Sigma.fst x_1)) (Prod.fst (Sigma.snd x_1)), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_1))) => Prod.snd (Sigma.fst x_1)) (Prod.fst (Prod.snd (Sigma.snd x_1)))))) polyH63 polyH65;
  have polyH80 := Poly.add polyH79 polyH12;
  have polyH81 := Poly.mul polyH20 polyH80;
  have polyH82 := Poly.add polyH78 polyH81;
  have polyH83 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ × ℕ) (fun (x_1 : ℕ × ℕ) => Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))))) (fun (x_1 x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1)))) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (j : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.fst j)) => Prod.fst j) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) Universe (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Universe n) => n) Uniform.universeNumber Prod.fst)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))) (fun (x_1 : ℕ × ℕ) (n : ℕ) => 3 * n) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => Prod.snd i) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.cardinalValue (ℕ × ℕ) Prod.snd)) (Realizer.uniform Realizer.triple (ℕ × ℕ)))) (Realizer.uniform Realizer.le (ℕ × ℕ)) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH82;
  have polyH84 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_id (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ (Sigma.fst x_8) (Sigma.snd x_8)))) polyH6;
  have polyH85 := Poly.add polyH83 polyH84;
  have polyH86 := Poly.volumeBool (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Decidable.decide (Prod.fst ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_1)) × Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => ((fun (x_3 : Universe (Prod.fst (Sigma.fst x_1))) => Prod.fst (Sigma.fst x_1)) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd (Sigma.fst x_1))) => Prod.snd (Sigma.fst x_1)) (Prod.fst (Prod.snd x_2))))) (Sigma.snd x_1)) ≤ Prod.snd ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_1)) × Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => ((fun (x_3 : Universe (Prod.fst (Sigma.fst x_1))) => Prod.fst (Sigma.fst x_1)) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd (Sigma.fst x_1))) => Prod.snd (Sigma.fst x_1)) (Prod.fst (Prod.snd x_2))))) (Sigma.snd x_1))));
  have polyH87 := Poly.add polyH4 polyH86;
  have polyH88 := Poly.add polyH87 polyH4;
  have polyH89 := Poly.add polyH88 polyH12;
  have polyH90 := Poly.mul polyH62 polyH89;
  have polyH91 := Poly.add polyH85 polyH90;
  have polyH92 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (x_1 : ℕ × ℕ) => Bool) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) ((fun (x_2 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_3 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_2))))) x_1)) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => x_1) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ × ℕ) (fun (x_1 : ℕ × ℕ) => Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))))) (fun (x_1 x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1)))) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (j : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.fst j)) => Prod.fst j) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) Universe (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Universe n) => n) Uniform.universeNumber Prod.fst)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))) (fun (x_1 : ℕ × ℕ) (n : ℕ) => 3 * n) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => Prod.snd i) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.cardinalValue (ℕ × ℕ) Prod.snd)) (Realizer.uniform Realizer.triple (ℕ × ℕ)))) (Realizer.uniform Realizer.le (ℕ × ℕ))) (@Uniform.id (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH91;
  have polyH93 := Poly.volumeProd (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => ((fun (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_1)) × Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => ((fun (x_3 : Universe (Prod.fst (Sigma.fst x_1))) => Prod.fst (Sigma.fst x_1)) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd (Sigma.fst x_1))) => Prod.snd (Sigma.fst x_1)) (Prod.fst (Prod.snd x_2))))) (Sigma.snd x_1)), Sigma.snd x_1)) polyH86 polyH4;
  have polyH94 := Poly.add polyH93 polyH5;
  have polyH95 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_snd (ℕ × ℕ) (fun (x_1 : ℕ × ℕ) => Bool) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ (Sigma.fst x_8) (((fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) ((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8)) × Cardinal (Prod.snd (Sigma.fst x_8)) × Matrix (Prod.fst (Sigma.fst x_8))) => ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd x_1))))) (Sigma.snd x_8)), Sigma.snd x_8))))) polyH94;
  have polyH96 := Poly.size (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1));
  have polyH97 := Poly.reparam (@Costs.scheduleCandidate) (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Sigma.mk (Sigma.fst x_1) (Prod.snd ((fun (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_1)) × Cardinal (Prod.snd (Sigma.fst x_1)) × Matrix (Prod.fst (Sigma.fst x_1))) => ((fun (x_3 : Universe (Prod.fst (Sigma.fst x_1))) => Prod.fst (Sigma.fst x_1)) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd (Sigma.fst x_1))) => Prod.snd (Sigma.fst x_1)) (Prod.fst (Prod.snd x_2))))) (Sigma.snd x_1)), Sigma.snd x_1))) polyH96;
  have polyH98 := Poly.add polyH95 polyH97;
  have polyH99 := Poly.add polyH4 polyH12;
  have polyH100 := Poly.mul polyH20 polyH99;
  have polyH101 := Poly.add polyH98 polyH100;
  have polyH102 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Bool × Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (Fin (Prod.fst i) → ℕ)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Option.map (fun (b : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (OAI.ThreeMachine.Algorithm.Block.time b)) (Fin.val v) (0)) (OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd (Prod.snd x_1))) (3 * Prod.snd i)))) (@Uniform.snd (ℕ × ℕ) (fun (x_1 : ℕ × ℕ) => Bool) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (Uniform.scheduleCandidate) (Sigma.fst x_8) (((fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) ((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8)) × Cardinal (Prod.snd (Sigma.fst x_8)) × Matrix (Prod.fst (Sigma.fst x_8))) => ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd x_1))))) (Sigma.snd x_8)), Sigma.snd x_8))))) polyH101;
  have polyH103 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_none (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) _ _ (Sigma.fst x_8) (Prod.snd ((fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) ((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8)) × Cardinal (Prod.snd (Sigma.fst x_8)) × Matrix (Prod.fst (Sigma.fst x_8))) => ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd x_1))))) (Sigma.snd x_8)), Sigma.snd x_8))))) polyH5;
  have polyH104 := Poly.add polyH95 polyH103;
  have polyH105 := Poly.add polyH104 polyH100;
  have polyH106 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Bool × Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (Fin (Prod.fst i) → ℕ)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Option.none (Fin (Prod.fst i) → ℕ)) (@Uniform.snd (ℕ × ℕ) (fun (x_1 : ℕ × ℕ) => Bool) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.none (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) _ _) (Sigma.fst x_8) (((fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) ((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8)) × Cardinal (Prod.snd (Sigma.fst x_8)) × Matrix (Prod.fst (Sigma.fst x_8))) => ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd x_1))))) (Sigma.snd x_8)), Sigma.snd x_8))))) polyH105;
  have polyH107 := Poly.add polyH102 polyH106;
  have polyH108 := Poly.const (fun (x_1 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => Prod.fst (Sigma.fst x_1) + Prod.snd (Sigma.fst x_1)) (30);
  have polyH109 := Poly.add polyH93 (hV);
  have polyH110 := Poly.add polyH109 polyH12;
  have polyH111 := Poly.add polyH110 polyH12;
  have polyH112 := Poly.mul polyH108 polyH111;
  have polyH113 := Poly.add polyH107 polyH112;
  have polyH114 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_choose (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (Fin (Prod.fst i) → ℕ)) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Option.map (fun (b : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (OAI.ThreeMachine.Algorithm.Block.time b)) (Fin.val v) (0)) (OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd (Prod.snd x_1))) (3 * Prod.snd i)))) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Option.none (Fin (Prod.fst i) → ℕ)) (Uniform.scheduleCandidate) (@Uniform.none (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) _ _) (Sigma.fst x_8) (((fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) ((fun (x_1 : Universe (Prod.fst (Sigma.fst x_8)) × Cardinal (Prod.snd (Sigma.fst x_8)) × Matrix (Prod.fst (Sigma.fst x_8))) => ((fun (x_2 : Universe (Prod.fst (Sigma.fst x_8))) => Prod.fst (Sigma.fst x_8)) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd (Sigma.fst x_8))) => Prod.snd (Sigma.fst x_8)) (Prod.fst (Prod.snd x_1))))) (Sigma.snd x_8)), Sigma.snd x_8))))) polyH113;
  have polyH115 := Poly.add polyH92 polyH114;
  have polyH116 := Poly.add polyH93 polyH12;
  have polyH117 := Poly.mul polyH20 polyH116;
  have polyH118 := Poly.add polyH115 polyH117;
  have polyH119 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Bool × Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (Fin (Prod.fst i) → ℕ)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) ((fun (x_2 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_3 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_2))))) x_1), x_1)) (fun (i : ℕ × ℕ) (x_1 : Bool × Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => if Prod.fst x_1 = Bool.true then Option.map (fun (b : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (OAI.ThreeMachine.Algorithm.Block.time b)) (Fin.val v) (0)) (OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd (Prod.snd (Prod.snd x_1)))) (3 * Prod.snd i))) else @Option.none (Fin (Prod.fst i) → ℕ)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (x_1 : ℕ × ℕ) => Bool) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) ((fun (x_2 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_3 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_2), (fun (n : ℕ) => 3 * n) ((fun (x_3 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_2))))) x_1)) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => x_1) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ × ℕ) (fun (x_1 : ℕ × ℕ) => Bool) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => ((fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1), (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))))) (fun (x_1 x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) (@Uniform.pair (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Universe (Prod.fst i)) => Prod.fst i) (Prod.fst x_1)) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (n : ℕ) => 3 * n) ((fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1)))) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (j : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) => Prod.fst) (fun (j : ℕ × ℕ) (x_1 : Universe (Prod.fst j)) => Prod.fst j) (@Uniform.fst (ℕ × ℕ) (fun (j : ℕ × ℕ) => Universe (Prod.fst j)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.reindex ℕ (ℕ × ℕ) Universe (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Universe n) => n) Uniform.universeNumber Prod.fst)) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => ℕ) (fun (x_1 : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => (fun (x_2 : Cardinal (Prod.snd i)) => Prod.snd i) (Prod.fst (Prod.snd x_1))) (fun (x_1 : ℕ × ℕ) (n : ℕ) => 3 * n) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => ℕ) _ _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ × ℕ) (x_1 : Cardinal (Prod.snd i)) => Prod.snd i) (@Uniform.comp (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) _ _ _ (fun (i : ℕ × ℕ) => Prod.snd) (fun (i : ℕ × ℕ) => Prod.fst) (@Uniform.snd (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i)) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _ _) (@Uniform.fst (ℕ × ℕ) (fun (i : ℕ × ℕ) => Cardinal (Prod.snd i)) (fun (i : ℕ × ℕ) => Matrix (Prod.fst i)) _ _)) (@Uniform.cardinalValue (ℕ × ℕ) Prod.snd)) (Realizer.uniform Realizer.triple (ℕ × ℕ)))) (Realizer.uniform Realizer.le (ℕ × ℕ))) (@Uniform.id (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) _)) (@Uniform.choose (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Option (Fin (Prod.fst i) → ℕ)) _ _ (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => Option.map (fun (b : OAI.ThreeMachine.Algorithm.Block (Fin (3 * Prod.snd i))) (v : Fin (Prod.fst i)) => List.getD (List.ofFn (OAI.ThreeMachine.Algorithm.Block.time b)) (Fin.val v) (0)) (OAI.ThreeMachine.Algorithm.fullSolve (OAI.ThreeMachine.paddedOrder (matrixRel (Prod.snd (Prod.snd x_1))) (3 * Prod.snd i)))) (fun (i : ℕ × ℕ) (x_1 : Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) => @Option.none (Fin (Prod.fst i) → ℕ)) Uniform.scheduleCandidate (@Uniform.none (ℕ × ℕ) (fun (i : ℕ × ℕ) => Universe (Prod.fst i) × Cardinal (Prod.snd i) × Matrix (Prod.fst i)) (fun (i : ℕ × ℕ) => Fin (Prod.fst i) → ℕ) _ _)) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH118;
  have polyH120 := Poly.of_le (fun (x_8 : (i : ℕ × ℕ) × Costs.ScheduleInput i) => (le_of_eq (@Uniform.time_scheduleMatrixFixed (Sigma.fst x_8) (Sigma.snd x_8)))) polyH119;
  exact Poly.lift polyH120 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem scheduleMatrix : Poly
    (fun x : Σ n, Universe n × (ℕ × Matrix n) => x.1+x.2.2.1)
    (fun x => Uniform.scheduleMatrix.time x.1 x.2) 150010 := by
  let s (x : Σ n, Universe n × (ℕ × Matrix n)) := x.1+x.2.2.1
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hm : Poly s (fun x => x.2.2.1) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × ℕ × Matrix n) => Sigma.fst x_1 + Prod.fst (Prod.snd (Sigma.snd x_1)));
  have polyH1 := Poly.reparam (@Costs.scheduleMatrixFixed) (fun (x_1 : (n : ℕ) × Universe n × ℕ × Matrix n) => Sigma.mk (Sigma.fst x_1, Prod.fst (Prod.snd (Sigma.snd x_1))) (Prod.fst (Sigma.snd x_1), @Cardinal.mk (Prod.snd (Sigma.fst x_1, Prod.fst (Prod.snd (Sigma.snd x_1)))) (), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH0;
  have polyH2 := Poly.of_le (fun (x_5 : (n : ℕ) × Universe n × ℕ × Matrix n) => (le_of_eq (@Uniform.time_scheduleMatrix (Sigma.fst x_5) (Sigma.snd x_5)))) polyH1;
  exact Poly.lift polyH2 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module OptimumCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_bestMatrixStep (n : ℕ) (x : BestState n) :
    bestMatrixStep.time n x = (fst.pair (bestNext.pair bestRetain)).time n x := by
  simp only [bestMatrixStep,time_congr,bestNext,bestRetain,bestAttempt]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho
theorem bestNext : Poly s (fun j => Uniform.bestNext.time (n j) ((U j,M j),(k j,o j))) 2 := by
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1)) polyH0 polyH1;
  have polyH3 := Poly.volumeNat (hk);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (k j_1, o j_1)) polyH3 (ho);
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), k j_1, o j_1)) polyH2 polyH4;
  have polyH6 := Poly.const (s) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _ (n j_12) (((U j_12, M j_12), k j_12, o j_12))))) polyH7;
  have polyH9 := Poly.add polyH4 polyH6;
  have polyH10 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ (n j_12) (Prod.snd ((U j_12, M j_12), k j_12, o j_12))))) polyH9;
  have polyH11 := Poly.add polyH8 polyH10;
  have polyH12 := Poly.const (s) (10);
  have polyH13 := Poly.const (s) (1);
  have polyH14 := Poly.add polyH4 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _) (n j_12) (((U j_12, M j_12), k j_12, o j_12))))) polyH16;
  have polyH18 := Poly.const (s) (200);
  have polyH19 := Poly.add (hk) polyH13;
  have polyH20 := Poly.mul polyH18 polyH19;
  have polyH21 := Poly.of_le (fun (j_12 : J) => (@Realizer.time_succ_le (Prod.fst (Prod.snd ((U j_12, M j_12), k j_12, o j_12))))) polyH20;
  have polyH22 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ) (ℕ) _ _ (fun (n_1 : ℕ) => n_1 + 1) (Realizer.succ) (n j_12) (Prod.fst (Prod.snd ((U j_12, M j_12), k j_12, o j_12)))))) polyH21;
  have polyH23 := Poly.add polyH17 polyH22;
  have polyH24 := Poly.add polyH3 polyH13;
  have polyH25 := Poly.mul polyH12 polyH24;
  have polyH26 := Poly.add polyH23 polyH25;
  have polyH27 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) => Nat.succ) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _)) (Realizer.uniform Realizer.succ ℕ) (n j_12) (((U j_12, M j_12), k j_12, o j_12))))) polyH26;
  exact Poly.lift polyH27 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → Option (β i)} {g : ∀ i, α i → γ i}

theorem time_attach_le (R : Uniform f) (K : Uniform g) (i : I) (x : α i) :
    ((R.pair K).comp swap.optionMap).time i x ≤
      10000000000*(R.time i x+K.time i x+volume x+volume (f i x)+volume (g i x)+1) := by
  have hmem : ∀ b ∈ f i x, volume b ≤ volume (f i x) := by
    intro b hb
    rw [show f i x = Option.some b from hb,volume_some]
    omega
  have h := time_optionMap (swap : Uniform (fun i (a : β i × γ i) => (a.2,a.1))) i
    (f i x) (g i x) (100*(volume (f i x)+volume (g i x)+1))
    (volume (f i x)+volume (g i x)+1) (by
      intro b hb
      have := hmem b hb
      simp only [swap,time_pair,time_fst,time_snd,volume_pair]
      omega) (by
      intro b hb
      have := hmem b hb
      simp only [volume_pair]
      omega)
  simp only [time_comp,time_pair,volume_pair]
  omega
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

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

theorem bestAttempt : Poly s (fun j => Uniform.bestAttempt.time (n j) ((U j,M j),(k j,o j))) 150010 := by
  let P : Uniform (fun (n : ℕ) (x : Uniform.BestState n) => (x.1.1,(x.2.1+1,x.1.2))) :=
    (Uniform.fst.comp Uniform.fst).pair (Uniform.bestNext.pair (Uniform.fst.comp Uniform.snd))
  have hsucc : Poly s (fun j => k j+1) 1 := hk.add (Poly.const s 1)
  have hS := Poly.volumeSchedule s n (fun j => k j+1) M hn hsucc
  have hN := bestNext s n U M k o hn hk ho
  have hP : Poly s (fun j => P.time (n j) ((U j,M j),(k j,o j))) 2 := by
    dsimp only [P]
    (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1)) polyH0 polyH1;
  have polyH3 := Poly.volumeNat (hk);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (k j_1, o j_1)) polyH3 (ho);
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), k j_1, o j_1)) polyH2 polyH4;
  have polyH6 := Poly.const (s) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => ℕ × Option (ℕ × (Fin n_1 → ℕ))) _ _ (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH7;
  have polyH9 := Poly.add polyH2 polyH6;
  have polyH10 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (n j_16) (Prod.fst ((U j_16, M j_16), k j_16, o j_16))))) polyH9;
  have polyH11 := Poly.add polyH8 polyH10;
  have polyH12 := Poly.const (s) (10);
  have polyH13 := Poly.const (s) (1);
  have polyH14 := Poly.add polyH2 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Universe i × Matrix i) (Universe) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => ℕ × Option (ℕ × (Fin n_1 → ℕ))) _ _) (@Uniform.fst ℕ Universe Matrix _ _) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH16;
  have polyH18 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (Matrix) _ _ (n j_16) (Prod.fst ((U j_16, M j_16), k j_16, o j_16))))) polyH9;
  have polyH19 := Poly.add polyH8 polyH18;
  have polyH20 := Poly.add polyH19 polyH15;
  have polyH21 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (Matrix) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => ℕ × Option (ℕ × (Fin n_1 → ℕ))) _ _) (@Uniform.snd ℕ Universe Matrix _ _) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH20;
  have polyH22 := Poly.add (hN) polyH21;
  have polyH23 := Poly.const (s) (20);
  have polyH24 := Poly.volumeNat (hsucc);
  have polyH25 := Poly.add polyH5 polyH24;
  have polyH26 := Poly.add polyH25 polyH1;
  have polyH27 := Poly.add polyH26 polyH13;
  have polyH28 := Poly.mul polyH23 polyH27;
  have polyH29 := Poly.add polyH22 polyH28;
  have polyH30 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.BestState) (fun (n_1 : ℕ) => ℕ) (Matrix) _ _ _ (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Prod.fst (Prod.snd x) + 1) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Prod.snd (Prod.fst x)) (Uniform.bestNext) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => ℕ × Option (ℕ × (Fin n_1 → ℕ))) _ _) (@Uniform.snd ℕ Universe Matrix _ _)) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH29;
  have polyH31 := Poly.add polyH17 polyH30;
  have polyH32 := Poly.add polyH5 polyH0;
  have polyH33 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd ((U j_1, M j_1), k j_1, o j_1)) + 1, Prod.snd (Prod.fst ((U j_1, M j_1), k j_1, o j_1)))) polyH24 polyH1;
  have polyH34 := Poly.add polyH32 polyH33;
  have polyH35 := Poly.add polyH34 polyH13;
  have polyH36 := Poly.mul polyH23 polyH35;
  have polyH37 := Poly.add polyH31 polyH36;
  have polyH38 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (Universe) (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.fst (Prod.fst x)) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => (Prod.fst (Prod.snd x) + 1, Prod.snd (Prod.fst x))) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Universe i × Matrix i) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => ℕ × Option (ℕ × (Fin n_1 → ℕ))) _ _) (@Uniform.fst ℕ Universe Matrix _ _)) (@Uniform.pair ℕ Uniform.BestState (fun (n_1 : ℕ) => ℕ) Matrix _ _ _ (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Prod.fst (Prod.snd x) + 1) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Prod.snd (Prod.fst x)) Uniform.bestNext (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => ℕ × Option (ℕ × (Fin n_1 → ℕ))) _ _) (@Uniform.snd ℕ Universe Matrix _ _))) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH37;
  exact Poly.lift polyH38 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hV : Poly s (fun j => volume (U j,(k j+1,M j))) 2 := by (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeNat (hsucc);
  have polyH2 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (k j_1 + 1, M j_1)) polyH1 polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, k j_1 + 1, M j_1)) polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hST : Poly s (fun j => Uniform.scheduleMatrix.time (n j) (U j,(k j+1,M j))) 150010 := by
    have hs : Poly s (fun j => n j+(k j+1)) 1 := hn.add hsucc
    exact Poly.reparam (r := 1) (d := 150010) scheduleMatrix
      (fun j => ⟨n j,(U j,(k j+1,M j))⟩) hs
  have hSC := Poly.compTimeSame P Uniform.scheduleMatrix n (fun j => ((U j,M j),(k j,o j)))
    (hP.lift (show 2 ≤ 150010 by decide)) hST (hV.lift (show 2 ≤ 150010 by decide))
  apply Poly.of_le (fun j => Uniform.time_attach_le (P.comp Uniform.scheduleMatrix) Uniform.bestNext
    (n j) ((U j,M j),(k j,o j)))
  (
  have polyH0 := Poly.const (s) (10000000000);
  have polyH1 := Poly.add (hSC) (hN);
  have polyH2 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH3 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1)) polyH2 polyH3;
  have polyH5 := Poly.volumeNat (hk);
  have polyH6 := Poly.volumeProd (fun (j_1 : J) => (k j_1, o j_1)) polyH5 (ho);
  have polyH7 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), k j_1, o j_1)) polyH4 polyH6;
  have polyH8 := Poly.add polyH1 polyH7;
  have polyH9 := Poly.add polyH8 (hS);
  have polyH10 := Poly.volumeNat (hsucc);
  have polyH11 := Poly.add polyH9 polyH10;
  have polyH12 := Poly.const (s) (1);
  have polyH13 := Poly.add polyH11 polyH12;
  have polyH14 := Poly.mul polyH0 polyH13;
  exact Poly.lift polyH14 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho
theorem bestRetain : Poly s (fun j => Uniform.bestRetain.time (n j) ((U j,M j),(k j,o j))) 150010 := by
  have hsucc : Poly s (fun j => k j+1) 1 := hk.add (Poly.const s 1)
  have hS := Poly.volumeSchedule s n (fun j => k j+1) M hn hsucc
  have hAV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)).map (fun t => (k j+1,t)))) 2 := by
    apply Poly.of_le (fun j => volume_tableBody (ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)) (k j+1))
    have hvn := Poly.volumeNat hsucc
    exact (hS.add hvn).add (Poly.const s 1)
  have hA := bestAttempt s n U M k o hn hk ho
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1)) polyH0 polyH1;
  have polyH3 := Poly.volumeNat (hk);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (k j_1, o j_1)) polyH3 (ho);
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), k j_1, o j_1)) polyH2 polyH4;
  have polyH6 := Poly.const (s) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _ (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH7;
  have polyH9 := Poly.add polyH4 polyH6;
  have polyH10 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ (n j_16) (Prod.snd ((U j_16, M j_16), k j_16, o j_16))))) polyH9;
  have polyH11 := Poly.add polyH8 polyH10;
  have polyH12 := Poly.const (s) (10);
  have polyH13 := Poly.const (s) (1);
  have polyH14 := Poly.add polyH4 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH16;
  have polyH18 := Poly.const (s) (10000);
  have polyH19 := Poly.add (ho) polyH13;
  have polyH20 := Poly.mul polyH18 polyH19;
  have polyH21 := Poly.of_le (fun (j_16 : J) => (@Uniform.time_test_le (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => ℕ × (Fin i_1 → ℕ)) i)) _ (fun (i : ℕ) (x : Option ((fun (i_1 : ℕ) => ℕ × (Fin i_1 → ℕ)) i)) => Option.isSome x) (@Uniform.optionIsSome._proof_1 (ℕ) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _) (n j_16) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))))) polyH20;
  have polyH22 := Poly.add polyH17 polyH21;
  have polyH23 := Poly.mul polyH12 polyH19;
  have polyH24 := Poly.add polyH22 polyH23;
  have polyH25 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.isSome x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _)) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH24;
  have polyH26 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _ (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH7;
  have polyH27 := Poly.add polyH25 polyH26;
  have polyH28 := Poly.const (s) (20);
  have polyH29 := Poly.volumeBool (s) (fun (j_1 : J) => Option.isSome (Prod.snd (Prod.snd ((U j_1, M j_1), k j_1, o j_1))));
  have polyH30 := Poly.add polyH5 polyH29;
  have polyH31 := Poly.add polyH30 polyH5;
  have polyH32 := Poly.add polyH31 polyH13;
  have polyH33 := Poly.mul polyH28 polyH32;
  have polyH34 := Poly.add polyH27 polyH33;
  have polyH35 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Bool) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => (fun (x_1 : Option (ℕ × (Fin i → ℕ))) => Option.isSome x_1) (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.isSome x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _)) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _)) (@Uniform.id ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH34;
  have polyH36 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Option (ℕ × (Fin (n j_1) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_1, M j_1), k j_1, o j_1))), (U j_1, M j_1), k j_1, o j_1)) polyH29 polyH5;
  have polyH37 := Poly.add polyH36 polyH6;
  have polyH38 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (x : ℕ) => Bool) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _ _ (n j_16) (((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16))))) polyH37;
  have polyH39 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _ (n j_16) (Prod.snd ((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16))))) polyH7;
  have polyH40 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ (n j_16) (Prod.snd (Prod.snd ((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16)))))) polyH9;
  have polyH41 := Poly.add polyH39 polyH40;
  have polyH42 := Poly.add polyH41 polyH15;
  have polyH43 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _) (n j_16) (Prod.snd ((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16))))) polyH42;
  have polyH44 := Poly.add polyH38 polyH43;
  have polyH45 := Poly.add polyH5 polyH13;
  have polyH46 := Poly.mul polyH12 polyH45;
  have polyH47 := Poly.add polyH44 polyH46;
  have polyH48 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Bool × (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (x : ℕ) => Bool) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _)) (n j_16) (((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16))))) polyH47;
  have polyH49 := Poly.add polyH38 (hA);
  have polyH50 := Poly.add polyH49 polyH46;
  have polyH51 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Bool × (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Option.map (fun (t : Fin n_1 → ℕ) => (Prod.fst (Prod.snd x) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst x)) (Prod.fst (Prod.snd x) + 1))) (@Uniform.snd ℕ (fun (x : ℕ) => Bool) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (Uniform.bestAttempt) (n j_16) (((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16))))) polyH50;
  have polyH52 := Poly.add polyH48 polyH51;
  have polyH53 := Poly.const (s) (30);
  have polyH54 := Poly.add polyH36 (ho);
  have polyH55 := Poly.add polyH54 (hAV);
  have polyH56 := Poly.add polyH55 polyH13;
  have polyH57 := Poly.mul polyH53 polyH56;
  have polyH58 := Poly.add polyH52 polyH57;
  have polyH59 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_choose (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.snd (Prod.snd x)) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Option.map (fun (t : Fin n_1 → ℕ) => (Prod.fst (Prod.snd x) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst x)) (Prod.fst (Prod.snd x) + 1))) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _)) (Uniform.bestAttempt) (n j_16) (((fun (x : Option (ℕ × (Fin (n j_16) → ℕ))) => Option.isSome x) (Prod.snd (Prod.snd ((U j_16, M j_16), k j_16, o j_16))), (U j_16, M j_16), k j_16, o j_16))))) polyH58;
  have polyH60 := Poly.add polyH35 polyH59;
  have polyH61 := Poly.add polyH36 polyH13;
  have polyH62 := Poly.mul polyH12 polyH61;
  have polyH63 := Poly.add polyH60 polyH62;
  have polyH64 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Bool × (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => ((fun (x_1 : Option (ℕ × (Fin i → ℕ))) => Option.isSome x_1) (Prod.snd (Prod.snd x)), x)) (fun (i : ℕ) (x : Bool × (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => if Prod.fst x = Bool.true then Prod.snd (Prod.snd (Prod.snd x)) else Option.map (fun (t : Fin i → ℕ) => (Prod.fst (Prod.snd (Prod.snd x)) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd x)) + 1))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Bool) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => (fun (x_1 : Option (ℕ × (Fin i → ℕ))) => Option.isSome x_1) (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.isSome x) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _)) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _)) (@Uniform.id ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) _)) (@Uniform.choose ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ (fun (i : ℕ) (x : (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) => Prod.snd (Prod.snd x)) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Option.map (fun (t : Fin n_1 → ℕ) => (Prod.fst (Prod.snd x) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst x)) (Prod.fst (Prod.snd x) + 1))) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Option (ℕ × (Fin i → ℕ))) _ _)) Uniform.bestAttempt) (n j_16) (((U j_16, M j_16), k j_16, o j_16))))) polyH63;
  exact Poly.lift polyH64 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho
theorem bestMatrixStep :
    Poly s (fun j => Uniform.bestMatrixStep.time (n j) ((U j,M j),(k j,o j))) 150010 := by
  have hsucc : Poly s (fun j => k j+1) 1 := hk.add (Poly.const s 1)
  have hS := Poly.volumeSchedule s n (fun j => k j+1) M hn hsucc
  have hAV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)).map (fun t => (k j+1,t)))) 2 := by
    apply Poly.of_le (fun j => volume_tableBody (ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)) (k j+1))
    have hvn := Poly.volumeNat hsucc
    exact (hS.add hvn).add (Poly.const s 1)
  have hRV := Poly.volumeIte (fun j => (o j).isSome = true) o
    (fun j => (ThreeMachine.StackCompiler.scheduleMatrix (M j) (k j+1)).map (fun t => (k j+1,t))) ho hAV
  have hN := bestNext s n U M k o hn hk ho
  have hR := bestRetain s n U M k o hn hk ho
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1)) polyH0 polyH1;
  have polyH3 := Poly.volumeNat (hk);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (k j_1, o j_1)) polyH3 (ho);
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), k j_1, o j_1)) polyH2 polyH4;
  have polyH6 := Poly.const (s) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _ (n j_18) (((U j_18, M j_18), k j_18, o j_18))))) polyH7;
  have polyH9 := Poly.add (hN) (hR);
  have polyH10 := Poly.const (s) (20);
  have polyH11 := Poly.volumeNat (hsucc);
  have polyH12 := Poly.add polyH5 polyH11;
  have polyH13 := Poly.add polyH12 (hRV);
  have polyH14 := Poly.const (s) (1);
  have polyH15 := Poly.add polyH13 polyH14;
  have polyH16 := Poly.mul polyH10 polyH15;
  have polyH17 := Poly.add polyH9 polyH16;
  have polyH18 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.BestState) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Prod.fst (Prod.snd x) + 1) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => if Option.isSome (Prod.snd (Prod.snd x)) = Bool.true then Prod.snd (Prod.snd x) else Option.map (fun (t : Fin n_1 → ℕ) => (Prod.fst (Prod.snd x) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst x)) (Prod.fst (Prod.snd x) + 1))) (Uniform.bestNext) (Uniform.bestRetain) (n j_18) (((U j_18, M j_18), k j_18, o j_18))))) polyH17;
  have polyH19 := Poly.add polyH8 polyH18;
  have polyH20 := Poly.add polyH5 polyH2;
  have polyH21 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd ((U j_1, M j_1), k j_1, o j_1)) + 1, if Option.isSome (Prod.snd (Prod.snd ((U j_1, M j_1), k j_1, o j_1))) = Bool.true then Prod.snd (Prod.snd ((U j_1, M j_1), k j_1, o j_1)) else Option.map (fun (t : Fin (n j_1) → ℕ) => (Prod.fst (Prod.snd ((U j_1, M j_1), k j_1, o j_1)) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst ((U j_1, M j_1), k j_1, o j_1))) (Prod.fst (Prod.snd ((U j_1, M j_1), k j_1, o j_1)) + 1)))) polyH11 (hRV);
  have polyH22 := Poly.add polyH20 polyH21;
  have polyH23 := Poly.add polyH22 polyH14;
  have polyH24 := Poly.mul polyH10 polyH23;
  have polyH25 := Poly.add polyH19 polyH24;
  have polyH26 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Matrix i) × ℕ × Option (ℕ × (Fin i → ℕ))) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Uniform.BestState i) => (Prod.fst (Prod.snd x) + 1, if Option.isSome (Prod.snd (Prod.snd x)) = Bool.true then Prod.snd (Prod.snd x) else Option.map (fun (t : Fin i → ℕ) => (Prod.fst (Prod.snd x) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst x)) (Prod.fst (Prod.snd x) + 1)))) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Option (ℕ × (Fin i → ℕ))) _ _) (@Uniform.pair ℕ Uniform.BestState (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => Prod.fst (Prod.snd x) + 1) (fun (n_1 : ℕ) (x : Uniform.BestState n_1) => if Option.isSome (Prod.snd (Prod.snd x)) = Bool.true then Prod.snd (Prod.snd x) else Option.map (fun (t : Fin n_1 → ℕ) => (Prod.fst (Prod.snd x) + 1, t)) (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.fst x)) (Prod.fst (Prod.snd x) + 1))) Uniform.bestNext Uniform.bestRetain) (n j_18) (((U j_18, M j_18), k j_18, o j_18))))) polyH25;
  have polyH27 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_bestMatrixStep (n j_18) (((U j_18, M j_18), k j_18, o j_18))))) polyH26;
  exact Poly.lift polyH27 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u10} {J : Type u11} {s : J → ℕ} {α : I → Type u12} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
theorem bestMatrix (hn : Poly s n 1) :
    Poly s (fun j => Uniform.bestMatrix.time (n j) (U j,M j)) 150011 := by
  let a (j : J) : (Universe (n j) × Matrix (n j)) × (ℕ × Option (ℕ × (Fin (n j) → ℕ))) :=
    ((U j,M j),(0,none))
  have hnp := hn.precomp (Sigma.fst : Poly.IterPool n → J)
  have hkp : Poly (fun p : Poly.IterPool n => s p.1) (fun p => p.2.1) 1 :=
    Poly.of_le (fun p : Poly.IterPool n => Nat.le_of_lt_succ p.2.isLt) hnp
  have hbest := Poly.volumeBest (fun p : Poly.IterPool n => s p.1) (fun p => n p.1)
    (fun p => p.2.1) (fun p => M p.1) hnp hkp
  have hstep := bestMatrixStep (fun p : Poly.IterPool n => s p.1) (fun p => n p.1)
    (fun p => U p.1) (fun p => M p.1) (fun p => p.2.1) (fun p => ThreeMachine.StackCompiler.bestMatrix (M p.1) p.2.1)
    hnp hkp hbest
  have hti : Poly (fun p : Poly.IterPool n => s p.1)
      (fun p => Uniform.bestMatrixStep.time (n p.1)
        (ThreeMachine.StackCompiler.bestMatrixStep^[p.2.1] (a p.1))) 150010 := by
    simpa only [a,bestMatrix_iterate] using hstep
  have hvi : Poly (fun p : Poly.IterPool n => s p.1)
      (fun p => volume (ThreeMachine.StackCompiler.bestMatrixStep^[p.2.1] (a p.1))) 2 := by
    simp only [a,bestMatrix_iterate]
    (
  have polyH0 := Poly.volumeUniverse (hnp) (fun (p_1 : Poly.IterPool n) => U (Sigma.fst p_1));
  have polyH1 := Poly.volumeMatrix (hnp) (fun (p_1 : Poly.IterPool n) => M (Sigma.fst p_1));
  have polyH2 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (U (Sigma.fst p_1), M (Sigma.fst p_1))) polyH0 polyH1;
  have polyH3 := Poly.volumeNat (hkp);
  have polyH4 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (Fin.val (Sigma.snd p_1), OAI.ThreeMachine.StackCompiler.bestMatrix (M (Sigma.fst p_1)) (Fin.val (Sigma.snd p_1)))) polyH3 (hbest);
  have polyH5 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => ((U (Sigma.fst p_1), M (Sigma.fst p_1)), Fin.val (Sigma.snd p_1), OAI.ThreeMachine.StackCompiler.bestMatrix (M (Sigma.fst p_1)) (Fin.val (Sigma.snd p_1)))) polyH2 polyH4;
  exact Poly.lift polyH5 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hIter := Poly.iterateTime Uniform.bestMatrixStep n n a hn hti hvi
  have hB := Poly.volumeBest s n n M hn hn
  dsimp only [a] at hIter
  simp only [Uniform.bestMatrix,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,
    Uniform.time_fst,Uniform.time_snd,Function.comp_apply]
  simp only [bestMatrix_iterate]
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1)) polyH0 polyH1;
  have polyH3 := Poly.const (s) (2);
  have polyH4 := Poly.add polyH2 polyH3;
  have polyH5 := Poly.add polyH0 polyH3;
  have polyH6 := Poly.const (s) (100000);
  have polyH7 := Poly.lengthFinRange (hn);
  have polyH8 := Poly.const (s) (1);
  have polyH9 := Poly.add polyH7 polyH8;
  have polyH10 := Poly.mul polyH6 polyH9;
  have polyH11 := Poly.volumeFinRange (hn);
  have polyH12 := Poly.add polyH11 polyH8;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_length_le (ℕ) (Fin) _ (n j_17) (List.finRange (n j_17)))) polyH13;
  have polyH15 := Poly.add polyH5 polyH14;
  have polyH16 := Poly.const (s) (10);
  have polyH17 := Poly.mul polyH16 polyH12;
  have polyH18 := Poly.add polyH15 polyH17;
  have polyH19 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (n j_17) (U j_17)))) polyH18;
  have polyH20 := Poly.add polyH4 polyH19;
  have polyH21 := Poly.add polyH0 polyH8;
  have polyH22 := Poly.mul polyH16 polyH21;
  have polyH23 := Poly.add polyH20 polyH22;
  have polyH24 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => Universe i × Matrix i) _ (n j_17) ((U j_17, M j_17))))) polyH4;
  have polyH25 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_zero (ℕ) (fun (i : ℕ) => Universe i × Matrix i) _ (n j_17) ((U j_17, M j_17))))) polyH3;
  have polyH26 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_none (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ (n j_17) ((U j_17, M j_17))))) polyH3;
  have polyH27 := Poly.add polyH25 polyH26;
  have polyH28 := Poly.const (s) (20);
  have polyH29 := Poly.const (s) (volume (0));
  have polyH30 := Poly.add polyH2 polyH29;
  have polyH31 := Poly.add polyH30 polyH8;
  have polyH32 := Poly.add polyH31 polyH8;
  have polyH33 := Poly.mul polyH28 polyH32;
  have polyH34 := Poly.add polyH27 polyH33;
  have polyH35 := Poly.add polyH24 polyH34;
  have polyH36 := Poly.add polyH2 polyH2;
  have polyH37 := Poly.const (s) (0);
  have polyH38 := Poly.volumeNat polyH37;
  have polyH39 := Poly.volumeProd (fun (j_1 : J) => (0, @Option.none (ℕ × (Fin (n j_1) → ℕ)))) polyH38 polyH8;
  have polyH40 := Poly.add polyH36 polyH39;
  have polyH41 := Poly.add polyH40 polyH8;
  have polyH42 := Poly.mul polyH28 polyH41;
  have polyH43 := Poly.add polyH35 polyH42;
  have polyH44 := Poly.add polyH23 polyH43;
  have polyH45 := Poly.volumeNat (hn);
  have polyH46 := Poly.add polyH2 polyH45;
  have polyH47 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), 0, @Option.none (ℕ × (Fin (n j_1) → ℕ)))) polyH2 polyH39;
  have polyH48 := Poly.add polyH46 polyH47;
  have polyH49 := Poly.add polyH48 polyH8;
  have polyH50 := Poly.mul polyH28 polyH49;
  have polyH51 := Poly.add polyH44 polyH50;
  have polyH52 := Poly.add polyH51 (hIter);
  have polyH53 := Poly.volumeProd (fun (j_1 : J) => (n j_1, (U j_1, M j_1), 0, @Option.none (ℕ × (Fin (n j_1) → ℕ)))) polyH45 polyH47;
  have polyH54 := Poly.add polyH53 polyH8;
  have polyH55 := Poly.mul polyH16 polyH54;
  have polyH56 := Poly.add polyH52 polyH55;
  have polyH57 := Poly.volumeProd (fun (j_1 : J) => (n j_1, OAI.ThreeMachine.StackCompiler.bestMatrix (M j_1) (n j_1))) polyH45 (hB);
  have polyH58 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1), n j_1, OAI.ThreeMachine.StackCompiler.bestMatrix (M j_1) (n j_1))) polyH2 polyH57;
  have polyH59 := Poly.add polyH58 polyH3;
  have polyH60 := Poly.add polyH57 polyH3;
  have polyH61 := Poly.add polyH59 polyH60;
  have polyH62 := Poly.add polyH57 polyH8;
  have polyH63 := Poly.mul polyH16 polyH62;
  have polyH64 := Poly.add polyH61 polyH63;
  have polyH65 := Poly.add polyH56 polyH64;
  have polyH66 := Poly.add polyH58 polyH8;
  have polyH67 := Poly.mul polyH16 polyH66;
  have polyH68 := Poly.add polyH65 polyH67;
  exact Poly.lift polyH68 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

theorem time_mapOption_linear {f : ∀ i, α i → β i} (R : Uniform f) (i : I)
    (o : Option (α i)) (C : ℕ)
    (ht : ∀ a ∈ o, R.time i a ≤ C*(volume o+1))
    (hv : ∀ a ∈ o, volume (f i a) ≤ volume o) :
    R.mapOption.time i o ≤ 1000000000*(C+1)*(volume o+1) := by
  let S : Uniform (fun i (a : α i × Unit) => f i a.1) := fst.comp R
  have hm := time_optionMap S i o () ((C+100)*(volume o+1)) (volume o) (by
    intro a ha
    have h := ht a ha
    have h' := volume_option_mem_le ha
    simp only [S,time_comp,time_fst,volume_pair,volume_unit]
    nlinarith) (by intro a ha; exact hv a ha)
  simp only [mapOption,time_congr,time_comp,time_pair,time_id,time_unit,Function.comp_apply,volume_pair,volume_unit]
  dsimp only [S] at hm
  simp only [volume_unit] at hm
  nlinarith [volume_pos o]

theorem time_functionListOption_le (n : ℕ) (o : Option (Fin n → ℕ)) :
    (functionList (α := fun _ => ℕ)).mapOption.time n o ≤ 10000000000*(volume o+1) := by
  have h := time_mapOption_linear (functionList (α := fun _ => ℕ)) n o 3 (by
    intro a ha
    have hv := volume_option_mem_le ha
    change volume a+2 ≤ _
    omega) (by intro a ha; rw [volume_ofFn]; exact volume_option_mem_le ha)
  omega

theorem time_sndFunctionListOption_le (n : ℕ) (o : Option (ℕ × (Fin n → ℕ))) :
    ((snd (α := fun _ : ℕ => ℕ)).comp (functionList (α := fun _ => ℕ))).mapOption.time n o ≤ 100000000000*(volume o+1) := by
  have h := time_mapOption_linear ((snd (α := fun _ : ℕ => ℕ)).comp (functionList (α := fun _ => ℕ))) n o 30 (by
    intro a ha
    have hv := volume_option_mem_le ha
    simp only [time_comp,time_snd]
    change (volume a+2)+(volume a.2+2)+10*(volume a.2+1) ≤ _
    rw [volume_prod] at hv ⊢
    omega) (by
      intro a ha
      have hv := volume_option_mem_le ha
      simp only [Function.comp_apply,volume_ofFn]
      rw [volume_prod] at hv
      omega)
  omega
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler

theorem volume_optionSndFunctionList_le {n : ℕ} (o : Option (ℕ × (Fin n → ℕ))) :
    volume (o.map (fun a => List.ofFn a.2)) ≤ volume o := by
  cases o with
  | none => rfl
  | some a => simp only [Option.map_some,volume_some,volume_ofFn,volume_prod]; omega
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

namespace Poly
variable {J : Type} {s n : J → ℕ} {d e : ℕ}

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
-- module EncodingCosts
namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u1}

end ThreeMachine.StackCompiler.Binary
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s : J → ℕ} {α : J → Type} [∀ j, Coding (α j)] {l v : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

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
theorem answerMatrix (d : J → Option ℕ) (hn : Poly s n 1)
    (hd : Poly s (fun j => (d j).getD 0) 1) :
    Poly s (fun j => Uniform.answerMatrix.time (n j) (U j,(M j,d j))) 150011 := by
  have hD : Poly s (fun j => volume (d j)) 1 := by
    apply Poly.of_le (fun j : J => volume_option_le_getD (d j) 0)
    have hv := Poly.volumeNat hd
    (
  have polyH0 := Poly.const (s) (2);
  have polyH1 := Poly.add (hv) polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hS := Poly.volumeSchedule s n (fun j => (d j).getD 0) M hn hd
  have hB := Poly.volumeBest s n n M hn hn
  have hST : Poly s (fun j => Uniform.scheduleMatrix.time (n j) (U j,((d j).getD 0,M j))) 150010 :=
    Poly.reparam (r := 1) (d := 150010) scheduleMatrix
      (fun j => ⟨n j,(U j,((d j).getD 0,M j))⟩) (hn.add hd)
  have hSV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.scheduleMatrix (M j) ((d j).getD 0)).map List.ofFn)) 2 := by
    simpa only [volume_optionFunctionList] using hS
  have hBV : Poly s (fun j => volume ((ThreeMachine.StackCompiler.bestMatrix (M j) (n j)).map (fun a => List.ofFn a.2))) 2 :=
    Poly.of_le (fun j => volume_optionSndFunctionList_le _) hB
  have hBT := bestMatrix s n U M hn
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeMatrix (hn) (fun (j_1 : J) => M j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (M j_1, d j_1)) polyH1 (hD);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, d j_1)) polyH0 polyH2;
  have polyH4 := Poly.const (s) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Option ℕ) _ _ (n j_17) ((U j_17, M j_17, d j_17))))) polyH5;
  have polyH7 := Poly.add polyH2 polyH4;
  have polyH8 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Option ℕ) _ _ (n j_17) (Prod.snd (U j_17, M j_17, d j_17))))) polyH7;
  have polyH9 := Poly.add polyH6 polyH8;
  have polyH10 := Poly.const (s) (10);
  have polyH11 := Poly.const (s) (1);
  have polyH12 := Poly.add polyH2 polyH11;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _) (n j_17) ((U j_17, M j_17, d j_17))))) polyH14;
  have polyH16 := Poly.const (s) (10000);
  have polyH17 := Poly.add (hD) polyH11;
  have polyH18 := Poly.mul polyH16 polyH17;
  have polyH19 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_test_le (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => ℕ) i)) _ (fun (i : ℕ) (x : Option ((fun (i_1 : ℕ) => ℕ) i)) => Option.isSome x) (@Uniform.optionIsSome._proof_1 (ℕ) (fun (i : ℕ) => ℕ) _) (n j_17) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))))) polyH18;
  have polyH20 := Poly.add polyH15 polyH19;
  have polyH21 := Poly.mul polyH10 polyH17;
  have polyH22 := Poly.add polyH20 polyH21;
  have polyH23 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Option ℕ) => Option.isSome x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => ℕ) _) (n j_17) ((U j_17, M j_17, d j_17))))) polyH22;
  have polyH24 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _ (n j_17) ((U j_17, M j_17, d j_17))))) polyH5;
  have polyH25 := Poly.add polyH23 polyH24;
  have polyH26 := Poly.const (s) (20);
  have polyH27 := Poly.volumeBool (s) (fun (j_1 : J) => Option.isSome (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))));
  have polyH28 := Poly.add polyH3 polyH27;
  have polyH29 := Poly.add polyH28 polyH3;
  have polyH30 := Poly.add polyH29 polyH11;
  have polyH31 := Poly.mul polyH26 polyH30;
  have polyH32 := Poly.add polyH25 polyH31;
  have polyH33 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Bool) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ) => Option.isSome x_1) (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Option ℕ) => Option.isSome x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.id ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _) (n j_17) ((U j_17, M j_17, d j_17))))) polyH32;
  have polyH34 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1)) polyH27 polyH3;
  have polyH35 := Poly.add polyH34 polyH4;
  have polyH36 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (x : ℕ) => Bool) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) _ _ (n j_17) (((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH35;
  have polyH37 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Option ℕ) _ _ (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH5;
  have polyH38 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Option ℕ) _ _ (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH5;
  have polyH39 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Option ℕ) _ _ (n j_17) (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17)))))) polyH7;
  have polyH40 := Poly.add polyH38 polyH39;
  have polyH41 := Poly.add polyH40 polyH13;
  have polyH42 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH41;
  have polyH43 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_zero (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _ (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH4;
  have polyH44 := Poly.add polyH42 polyH43;
  have polyH45 := Poly.add polyH3 (hD);
  have polyH46 := Poly.const (s) (volume (0));
  have polyH47 := Poly.add polyH45 polyH46;
  have polyH48 := Poly.add polyH47 polyH11;
  have polyH49 := Poly.mul polyH26 polyH48;
  have polyH50 := Poly.add polyH44 polyH49;
  have polyH51 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH50;
  have polyH52 := Poly.add (hD) polyH46;
  have polyH53 := Poly.add polyH52 polyH11;
  have polyH54 := Poly.mul polyH16 polyH53;
  have polyH55 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_getD_le (ℕ) (fun (i : ℕ) => ℕ) _ (n j_17) (Prod.snd (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17)))) (0))) polyH54;
  have polyH56 := Poly.add polyH51 polyH55;
  have polyH57 := Poly.const (s) (0);
  have polyH58 := Poly.volumeNat polyH57;
  have polyH59 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1))), 0)) (hD) polyH58;
  have polyH60 := Poly.add polyH59 polyH11;
  have polyH61 := Poly.mul polyH10 polyH60;
  have polyH62 := Poly.add polyH56 polyH61;
  have polyH63 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH62;
  have polyH64 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Matrix) (fun (i : ℕ) => Option ℕ) _ _ (n j_17) (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17)))))) polyH7;
  have polyH65 := Poly.add polyH38 polyH64;
  have polyH66 := Poly.add polyH65 polyH13;
  have polyH67 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH66;
  have polyH68 := Poly.add polyH63 polyH67;
  have polyH69 := Poly.volumeNat (hd);
  have polyH70 := Poly.add polyH3 polyH69;
  have polyH71 := Poly.add polyH70 polyH1;
  have polyH72 := Poly.add polyH71 polyH11;
  have polyH73 := Poly.mul polyH26 polyH72;
  have polyH74 := Poly.add polyH68 polyH73;
  have polyH75 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) (Matrix) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH74;
  have polyH76 := Poly.add polyH37 polyH75;
  have polyH77 := Poly.add polyH3 polyH0;
  have polyH78 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Universe (n j_1) × Matrix (n j_1) × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1))), Prod.fst (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1))))) polyH69 polyH1;
  have polyH79 := Poly.add polyH77 polyH78;
  have polyH80 := Poly.add polyH79 polyH11;
  have polyH81 := Poly.mul polyH26 polyH80;
  have polyH82 := Poly.add polyH76 polyH81;
  have polyH83 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (Universe) (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) Matrix _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _))) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH82;
  have polyH84 := Poly.add polyH83 (hST);
  have polyH85 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1)), (fun (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) ((fun (x : Universe (n j_1) × Matrix (n j_1) × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1))), Prod.fst (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1))))) polyH0 polyH78;
  have polyH86 := Poly.add polyH85 polyH11;
  have polyH87 := Poly.mul polyH10 polyH86;
  have polyH88 := Poly.add polyH84 polyH87;
  have polyH89 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × ℕ × Matrix i) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × ℕ × Matrix n_1) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) Matrix _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)))) (Uniform.scheduleMatrix) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH88;
  have polyH90 := Poly.const (s) (10000000000);
  have polyH91 := Poly.add (hS) polyH11;
  have polyH92 := Poly.mul polyH90 polyH91;
  have polyH93 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_functionListOption_le (n j_17) ((fun (x : Universe (n j_17) × ℕ × Matrix (n j_17)) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd x))) ((fun (x : Universe (n j_17) × Matrix (n j_17) × Option ℕ) => (Prod.fst x, (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (n j_17) × Matrix (n j_17) × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17)))))) polyH92;
  have polyH94 := Poly.add polyH89 polyH93;
  have polyH95 := Poly.mul polyH10 polyH91;
  have polyH96 := Poly.add polyH94 polyH95;
  have polyH97 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × ℕ × Matrix i) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x_1)) (Prod.fst (Prod.snd x_1))) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, (fun (x_2 : Option ℕ × ℕ) => Option.getD (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_2), 0)) x_1), Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (Fin i → ℕ)) => Option.map (fun (f : Fin i → ℕ) => List.ofFn f) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × ℕ × Matrix i) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × ℕ × Matrix n_1) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) Matrix _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)))) Uniform.scheduleMatrix) (@Uniform.mapOption ℕ (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.functionList (fun (i : ℕ) => ℕ) _)) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH96;
  have polyH98 := Poly.add polyH36 polyH97;
  have polyH99 := Poly.add polyH3 polyH11;
  have polyH100 := Poly.mul polyH10 polyH99;
  have polyH101 := Poly.add polyH98 polyH100;
  have polyH102 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Bool × Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) (fun (n_1 : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => Option.map List.ofFn (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.fst (Prod.snd x)) (Option.getD (Prod.snd (Prod.snd x)) (0)))) (@Uniform.snd ℕ (fun (x : ℕ) => Bool) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × ℕ × Matrix i) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x_1)) (Prod.fst (Prod.snd x_1))) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, (fun (x_2 : Option ℕ × ℕ) => Option.getD (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_2), 0)) x_1), Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (Fin i → ℕ)) => Option.map (fun (f : Fin i → ℕ) => List.ofFn f) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × ℕ × Matrix i) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × ℕ × Matrix n_1) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) Matrix _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)))) Uniform.scheduleMatrix) (@Uniform.mapOption ℕ (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.functionList (fun (i : ℕ) => ℕ) _))) (n j_17) (((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH101;
  have polyH103 := Poly.add polyH37 polyH67;
  have polyH104 := Poly.add polyH77 polyH1;
  have polyH105 := Poly.add polyH104 polyH11;
  have polyH106 := Poly.mul polyH26 polyH105;
  have polyH107 := Poly.add polyH103 polyH106;
  have polyH108 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (Universe) (Matrix) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Option ℕ) _ _)) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH107;
  have polyH109 := Poly.add polyH108 (hBT);
  have polyH110 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1)), Prod.fst (Prod.snd (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_1, M j_1, d j_1))), U j_1, M j_1, d j_1))))) polyH0 polyH1;
  have polyH111 := Poly.add polyH110 polyH11;
  have polyH112 := Poly.mul polyH10 polyH111;
  have polyH113 := Poly.add polyH109 polyH112;
  have polyH114 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Option ℕ) _ _))) (Uniform.bestMatrix) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH113;
  have polyH115 := Poly.const (s) (100000000000);
  have polyH116 := Poly.add (hB) polyH11;
  have polyH117 := Poly.mul polyH115 polyH116;
  have polyH118 := Poly.of_le (fun (j_17 : J) => (@Uniform.time_sndFunctionListOption_le (n j_17) ((fun (x : Universe (n j_17) × Matrix (n j_17)) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x) (n j_17)) ((fun (x : Universe (n j_17) × Matrix (n j_17) × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17)))))) polyH117;
  have polyH119 := Poly.add polyH114 polyH118;
  have polyH120 := Poly.mul polyH10 polyH116;
  have polyH121 := Poly.add polyH119 polyH120;
  have polyH122 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × Matrix i) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.map (fun (x_1 : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x_1)) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Option ℕ) _ _))) Uniform.bestMatrix) (@Uniform.mapOption ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (i : ℕ) (x : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (@Uniform.functionList (fun (i : ℕ) => ℕ) _))) (n j_17) (Prod.snd ((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH121;
  have polyH123 := Poly.add polyH36 polyH122;
  have polyH124 := Poly.add polyH123 polyH100;
  have polyH125 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Bool × Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) (fun (n_1 : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => Option.map (fun (a : ℕ × (Fin n_1 → ℕ)) => List.ofFn (Prod.snd a)) (OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.fst (Prod.snd x)) n_1)) (@Uniform.snd ℕ (fun (x : ℕ) => Bool) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × Matrix i) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.map (fun (x_1 : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x_1)) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Option ℕ) _ _))) Uniform.bestMatrix) (@Uniform.mapOption ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (i : ℕ) (x : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (@Uniform.functionList (fun (i : ℕ) => ℕ) _)))) (n j_17) (((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH124;
  have polyH126 := Poly.add polyH102 polyH125;
  have polyH127 := Poly.const (s) (30);
  have polyH128 := Poly.add polyH34 (hSV);
  have polyH129 := Poly.add polyH128 (hBV);
  have polyH130 := Poly.add polyH129 polyH11;
  have polyH131 := Poly.mul polyH127 polyH130;
  have polyH132 := Poly.add polyH126 polyH131;
  have polyH133 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_choose (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) (fun (n_1 : ℕ) => Option (List ℕ)) _ _ (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => Option.map List.ofFn (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.fst (Prod.snd x)) (Option.getD (Prod.snd (Prod.snd x)) (0)))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => Option.map (fun (a : ℕ × (Fin n_1 → ℕ)) => List.ofFn (Prod.snd a)) (OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.fst (Prod.snd x)) n_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × ℕ × Matrix i) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x_1)) (Prod.fst (Prod.snd x_1))) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, (fun (x_2 : Option ℕ × ℕ) => Option.getD (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_2), 0)) x_1), Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (Fin i → ℕ)) => Option.map (fun (f : Fin i → ℕ) => List.ofFn f) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × ℕ × Matrix i) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × ℕ × Matrix n_1) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) Matrix _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)))) Uniform.scheduleMatrix) (@Uniform.mapOption ℕ (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.functionList (fun (i : ℕ) => ℕ) _))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × Matrix i) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.map (fun (x_1 : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x_1)) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Option ℕ) _ _))) Uniform.bestMatrix) (@Uniform.mapOption ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (i : ℕ) (x : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (@Uniform.functionList (fun (i : ℕ) => ℕ) _)))) (n j_17) (((fun (x : Option ℕ) => Option.isSome x) (Prod.snd (Prod.snd (U j_17, M j_17, d j_17))), U j_17, M j_17, d j_17))))) polyH132;
  have polyH134 := Poly.add polyH33 polyH133;
  have polyH135 := Poly.add polyH34 polyH11;
  have polyH136 := Poly.mul polyH10 polyH135;
  have polyH137 := Poly.add polyH134 polyH136;
  have polyH138 := Poly.of_le (fun (j_17 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Bool × Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ) => Option.isSome x_1) (Prod.snd (Prod.snd x)), x)) (fun (i : ℕ) (x : Bool × Universe i × Matrix i × Option ℕ) => if Prod.fst x = Bool.true then Option.map List.ofFn (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.fst (Prod.snd (Prod.snd x))) (Option.getD (Prod.snd (Prod.snd (Prod.snd x))) (0))) else Option.map (fun (a : ℕ × (Fin i → ℕ)) => List.ofFn (Prod.snd a)) (OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.fst (Prod.snd (Prod.snd x))) i)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Bool) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ) => Option.isSome x_1) (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Option ℕ) => Option.isSome x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.id ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.choose ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1 × Option ℕ) (fun (n_1 : ℕ) => Option (List ℕ)) _ _ (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => Option.map List.ofFn (OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.fst (Prod.snd x)) (Option.getD (Prod.snd (Prod.snd x)) (0)))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => Option.map (fun (a : ℕ × (Fin n_1 → ℕ)) => List.ofFn (Prod.snd a)) (OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.fst (Prod.snd x)) n_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × ℕ × Matrix i) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x_1)) (Prod.fst (Prod.snd x_1))) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, (fun (x_2 : Option ℕ × ℕ) => Option.getD (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_2), 0)) x_1), Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (Fin i → ℕ)) => Option.map (fun (f : Fin i → ℕ) => List.ofFn f) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × ℕ × Matrix i) (fun (n_1 : ℕ) => Option (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × ℕ × Matrix n_1) => OAI.ThreeMachine.StackCompiler.scheduleMatrix (Prod.snd (Prod.snd x)) (Prod.fst (Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe (fun (i : ℕ) => ℕ × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => ((fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x), Prod.fst (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => ℕ) Matrix _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Option ℕ × ℕ) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x_1), 0)) x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ × ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.snd (Prod.snd x), 0)) (fun (i : ℕ) (x : Option ℕ × ℕ) => Option.getD (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.snd (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => 0) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)) (@Uniform.zero ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) _)) (@Uniform.getD ℕ (fun (i : ℕ) => ℕ) _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Option ℕ) _ _)))) Uniform.scheduleMatrix) (@Uniform.mapOption ℕ (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.functionList (fun (i : ℕ) => ℕ) _))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) (fun (i : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (fun (x_1 : Universe i × Matrix i) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × Matrix i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Option (ℕ × (Fin i → ℕ))) => Option.map (fun (x_1 : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x_1)) x) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => Option (ℕ × (Fin n_1 → ℕ))) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.StackCompiler.bestMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) Universe Matrix _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (i : ℕ) => Matrix i × Option ℕ) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Option ℕ) _ _))) Uniform.bestMatrix) (@Uniform.mapOption ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => List ℕ) _ _ (fun (i : ℕ) (x : ℕ × (Fin i → ℕ)) => (fun (f : Fin i → ℕ) => List.ofFn f) (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => Fin n_1 → ℕ) (fun (n_1 : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (f : Fin n_1 → ℕ) => List.ofFn f) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (@Uniform.functionList (fun (i : ℕ) => ℕ) _))))) (n j_17) ((U j_17, M j_17, d j_17))))) polyH137;
  have hZ := Poly.lift (e := 150011) polyH138 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega);
  refine Poly.of_le (fun x => le_of_eq ?_) hZ;
  unfold Uniform.answerMatrix;
  exact Uniform.time_congr _ _ _ _)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler
namespace Request

end Request
namespace Binary

end Binary

end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace RequestData

end RequestData
end ThreeMachine.StackCompiler
end

end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.answerMatrix := @OAI.ThreeMachine.StackCompiler.Costs.answerMatrix
