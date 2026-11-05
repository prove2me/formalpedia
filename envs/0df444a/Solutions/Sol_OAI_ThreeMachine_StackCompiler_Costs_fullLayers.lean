-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.fullLayers
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:55:40.981484+00:00
-- url     : https://prove2.me/submissions/60c94472-0063-4fb4-ba95-000237da7da6

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_triplesA
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_familyAssignments
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_layerStep

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

theorem volumeUnit (s : I → ℕ) (b : I → Unit) : Poly s (fun i => volume (b i)) 0 := by
  have h : (fun i => volume (b i)) = fun _ => 1 := by funext i; cases b i; rfl
  rw [h]; exact const s 1

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

theorem volume_function_apply_le {α : Type u11} [Coding α] {n : ℕ} (f : Fin n → α) (v : Fin n) :
    volume (f v) ≤ volume f := volume_mem_le (List.mem_ofFn.mpr ⟨v,rfl⟩)

namespace Uniform
variable {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_functionGetOptionAny_le (d : I → ℕ) (i : I) (f : Fin (d i) → α i) (v : Fin (d i)) :
    (functionGetOptionAny d).time i (f,v) ≤ 100000000*(d i+1)*(volume f+d i+1) := by
  have ht := time_getElem?_le i (List.ofFn f) v.val
  have hv := v.isLt
  simp only [functionGetOptionAny,time_congr,time_comp,time_pair,time_fst,time_snd,
    time_functionListAny,time_finValue,volume_pair,volume_fin,volume_nat,volume_ofFn,
    Function.comp_apply] at ht ⊢
  nlinarith [volume_pos f]

theorem time_functionGetAny_eq (d : I → ℕ) (i : I) (f : Fin (d i) → α i) (v : Fin (d i)) :
    (functionGetAny d).time i (f,v) = (functionGetOptionAny d).time i (f,v)+11*volume (f v)+34 := by
  change (functionGetOptionAny d).time i (f,v)+
    ((functionGetOptionAny d).transform (enc (f,v))).size+2+
    10*(((functionGetOptionAny d).transform (enc (f,v))).size+1) = _
  rw [(functionGetOptionAny d).correct]
  change _+volume (Option.some (f v))+2+10*(volume (Option.some (f v))+1) = _
  rw [volume_some]
  omega

theorem time_functionGetAny_le (d : I → ℕ) (i : I) (f : Fin (d i) → α i) (v : Fin (d i)) :
    (functionGetAny d).time i (f,v) ≤ 1000000000*(d i+1)*(volume f+d i+1) := by
  rw [time_functionGetAny_eq]
  have h := time_functionGetOptionAny_le d i f v
  have hv := volume_function_apply_le f v
  nlinarith [volume_pos f]

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

theorem filterTime {p : ∀ i, α i × γ i → Bool} (P : Uniform p) {l t vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun q : Pool idx xs => s q.1)
      (fun q => P.time (idx q.1) (q.2.1,e q.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => P.filter.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx ve)) := by
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_filter P (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  (
  have polyH0 := Poly.const (s) (100000);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hl) polyH1;
  have polyH3 := Poly.mul polyH0 polyH2;
  have polyH4 := Poly.add (hT) (hx);
  have polyH5 := Poly.add polyH4 (he);
  have polyH6 := Poly.add polyH5 polyH1;
  have polyH7 := Poly.mul polyH3 polyH6;
  exact Poly.lift polyH7 (by first | decide +kernel | omega))

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

variable {α : J → Type u8} {β : J → Type u9} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem lengthVolume (xs : ∀ j, List (α j)) (h : Poly s (fun j => volume (xs j)) d) :
    Poly s (fun j => (xs j).length) d := of_le (fun j => length_le_volume (xs j)) h

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

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u23} {s : J → ℕ} {d e : ℕ} {α : J → Type u24} {β : J → Type u25}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]
omit [∀ j, Coding (α j)] [∀ j, Coding (β j)] in
theorem lengthMap (f : ∀ j, α j → β j) {xs : ∀ j, List (α j)}
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).map (f j)).length) d := by simpa only [List.length_map] using h

omit [∀ j, Coding (α j)] [∀ j, Coding (β j)] in
theorem lengthProduct {xs : ∀ j, List (α j)} {ys : ∀ j, List (β j)}
    (hx : Poly s (fun j => (xs j).length) d) (hy : Poly s (fun j => (ys j).length) e) :
    Poly s (fun j => ((xs j).product (ys j)).length) (d+e) := by
  have h (j : J) : ((xs j).product (ys j)).length = (xs j).length*(ys j).length := by
    simp [List.product,List.length_flatMap]
  simpa only [h] using hx.mul hy

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
  (
  have polyH0 := Poly.const (s) (2);
  have polyH1 := Poly.mul polyH0 (hl);
  have polyH2 := Poly.const (s) (1);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.add polyH3 (ht);
  have polyH5 := Poly.add polyH4 polyH2;
  exact Poly.lift polyH5 (by first | decide +kernel | omega))

variable {α : J → Type u2} {β : J → Type u3} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u4} {J : Type u5} {s : J → ℕ}
variable {α : I → Type u6} {β : I → Type u7} {γ : I → Type u8} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

theorem flatMapTime {f : ∀ i, α i × γ i → List (β i)} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.flatMap.time (idx j) (xs j,e j))
      (l+v+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  have hm := volumeMap idx xs e (β := fun i => List (β i)) hl hv
  have hfV : Poly s (fun j => volume ((xs j).flatMap (fun a => f (idx j) (a,e j)))) (l+v) := by
    have hv (j : J) : volume ((xs j).flatMap (fun a => f (idx j) (a,e j))) ≤
        volume ((xs j).map (fun a => f (idx j) (a,e j))) := by
      rw [volume_flatten,← List.flatMap_def]
      omega
    exact of_le hv hm
  have hf := lengthVolume _ hfV
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_flatMap R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  (
  have polyH0 := Poly.const (s) (100000);
  have polyH1 := Poly.add (hl) (hf);
  have polyH2 := Poly.const (s) (1);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.mul polyH0 polyH3;
  have polyH5 := Poly.add (hT) (hx);
  have polyH6 := Poly.add polyH5 (he);
  have polyH7 := Poly.add polyH6 (hm);
  have polyH8 := Poly.add polyH7 polyH2;
  have polyH9 := Poly.mul polyH4 polyH8;
  exact Poly.lift polyH9 (by first | decide +kernel | omega))

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

theorem time_setFilter {γ : ℕ → Type u4} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) (n : ℕ) (x : Finset (Fin n) × γ n) :
    P.setFilter.time n x = (setList.onFst.comp P.filter).time n x := rfl

theorem time_setEmpty (n : ℕ) (x : Universe n) : setEmpty.time n x = 2 := rfl

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

theorem setInter : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setInter.time x.1 x.2) 4 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.1);
  have polyH2 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5;
  have polyH7 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1);
  have polyH8 := Poly.add polyH7 polyH4;
  have polyH9 := Poly.add polyH6 polyH8;
  have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (10);
  have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (1);
  have polyH12 := Poly.add polyH7 polyH11;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _) (Uniform.setList) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH14;
  have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5;
  have polyH17 := Poly.add polyH15 polyH16;
  have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (20);
  have polyH19 := Poly.add polyH3 polyH7;
  have polyH20 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2);
  have polyH21 := Poly.add polyH19 polyH20;
  have polyH22 := Poly.add polyH21 polyH11;
  have polyH23 := Poly.mul polyH18 polyH22;
  have polyH24 := Poly.add polyH17 polyH23;
  have polyH25 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) => (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH24;
  have polyH26 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1);
  have polyH27 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Sigma.snd x_1)) polyH26;
  have polyH28 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q));
  have polyH29 := Poly.reparam (@Costs.setMem) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q))))) polyH28;
  have polyH30 := @Poly.filterTime (ℕ) ((n : ℕ) × Finset (Fin n) × Finset (Fin n)) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Fin) (fun (n : ℕ) => Finset (Fin n)) _ _ (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.snd (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (Uniform.setMem) (1) (3 * 1) (2 * 1) (2 * 1) polyH27 polyH29 polyH7 polyH20;
  have polyH31 := Poly.add polyH25 polyH30;
  have polyH32 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) polyH7 polyH20;
  have polyH33 := Poly.add polyH32 polyH11;
  have polyH34 := Poly.mul polyH10 polyH33;
  have polyH35 := Poly.add polyH31 polyH34;
  have polyH36 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Finset.sort (Prod.fst x_1) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Finset (Fin i)) => List.filter (fun (a : Fin i) => Decidable.decide (Prod.fst (a, Prod.snd x_1) ∈ Prod.snd (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.onFst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) Uniform.setList) (@Uniform.filter ℕ Fin (fun (n : ℕ) => Finset (Fin n)) _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) Uniform.setMem) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH35;
  have polyH37 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_setFilter (fun (n : ℕ) => Finset (Fin n)) _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (Uniform.setMem) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH36;
  exact Poly.lift polyH37 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem setDiff : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setDiff.time x.1 x.2) 4 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.1);
  have polyH2 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5;
  have polyH7 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1);
  have polyH8 := Poly.add polyH7 polyH4;
  have polyH9 := Poly.add polyH6 polyH8;
  have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (10);
  have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (1);
  have polyH12 := Poly.add polyH7 polyH11;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _) (Uniform.setList) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH14;
  have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5;
  have polyH17 := Poly.add polyH15 polyH16;
  have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (20);
  have polyH19 := Poly.add polyH3 polyH7;
  have polyH20 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2);
  have polyH21 := Poly.add polyH19 polyH20;
  have polyH22 := Poly.add polyH21 polyH11;
  have polyH23 := Poly.mul polyH18 polyH22;
  have polyH24 := Poly.add polyH17 polyH23;
  have polyH25 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) => (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH24;
  have polyH26 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1);
  have polyH27 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Sigma.snd x_1)) polyH26;
  have polyH28 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q));
  have polyH29 := Poly.reparam (@Costs.setMem) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q))))) polyH28;
  have polyH30 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (10000);
  have polyH31 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (@Realizer.time_not_le (Decidable.decide (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q)))) ∈ Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH30;
  have polyH32 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (le_of_eq (@Uniform.time_uniform (ℕ) (Bool) (Bool) _ _ (Bool.not) (Realizer.not) (Sigma.fst (Sigma.fst q)) (Decidable.decide (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q)))) ∈ Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH31;
  have polyH33 := Poly.add polyH29 polyH32;
  have polyH34 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (10);
  have polyH35 := Poly.volumeBool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => Decidable.decide (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q)))) ∈ Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q))))));
  have polyH36 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (1);
  have polyH37 := Poly.add polyH35 polyH36;
  have polyH38 := Poly.mul polyH34 polyH37;
  have polyH39 := Poly.add polyH33 polyH38;
  have polyH40 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => Fin n × Finset (Fin n)) (fun (n : ℕ) => Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (fun (x_1 : ℕ) => Bool.not) (Uniform.setMem) (Realizer.uniform Realizer.not ℕ) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH39;
  have polyH41 := @Poly.filterTime (ℕ) ((n : ℕ) × Finset (Fin n) × Finset (Fin n)) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Fin) (fun (n : ℕ) => Finset (Fin n)) _ _ (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.snd (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i)) => !(fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) x_1) (@Uniform.comp ℕ (fun (n : ℕ) => Fin n × Finset (Fin n)) (fun (n : ℕ) => Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (fun (x_1 : ℕ) => Bool.not) Uniform.setMem (Realizer.uniform Realizer.not ℕ)) (1) (Max.max (Max.max (3 * 1) (0)) (0 + Max.max (0) (0))) (2 * 1) (2 * 1) polyH27 polyH40 polyH7 polyH20;
  have polyH42 := Poly.add polyH25 polyH41;
  have polyH43 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) polyH7 polyH20;
  have polyH44 := Poly.add polyH43 polyH11;
  have polyH45 := Poly.mul polyH10 polyH44;
  have polyH46 := Poly.add polyH42 polyH45;
  have polyH47 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Finset.sort (Prod.fst x_1) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Finset (Fin i)) => List.filter (fun (a : Fin i) => !(fun (x_3 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_3 ∈ Prod.snd x_3)) (a, Prod.snd x_1)) (Prod.fst x_1)) (@Uniform.onFst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) Uniform.setList) (@Uniform.filter ℕ Fin (fun (n : ℕ) => Finset (Fin n)) _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i)) => !(fun (x_3 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_3 ∈ Prod.snd x_3)) x_1) (@Uniform.comp ℕ (fun (n : ℕ) => Fin n × Finset (Fin n)) (fun (n : ℕ) => Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (fun (x_1 : ℕ) => Bool.not) Uniform.setMem (Realizer.uniform Realizer.not ℕ))) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH46;
  have polyH48 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_setFilter (fun (n : ℕ) => Finset (Fin n)) _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i)) => !(fun (x_3 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_3 ∈ Prod.snd x_3)) x_1) (@Uniform.comp ℕ (fun (n : ℕ) => Fin n × Finset (Fin n)) (fun (n : ℕ) => Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (fun (x_1 : ℕ) => Bool.not) Uniform.setMem (Realizer.uniform Realizer.not ℕ)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH47;
  exact Poly.lift polyH48 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

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
theorem setCard : Poly (fun x : Σ n, Finset (Fin n) => x.1)
    (fun x => Uniform.setCard.time x.1 x.2) 3 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Finset (Fin n)) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n)) => x_1.2);
  have polyH2 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n)) => Sigma.fst x_1) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n)) => Sigma.fst x_1) (100000);
  have polyH5 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n)) => x_1.2);
  have polyH6 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Finset (Fin n)) => Sigma.snd x_1) polyH5;
  have polyH7 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n)) => Sigma.fst x_1) (1);
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.mul polyH4 polyH8;
  have polyH10 := Poly.add polyH1 polyH7;
  have polyH11 := Poly.mul polyH9 polyH10;
  have polyH12 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n)) => (@Uniform.time_length_le (ℕ) (Fin) _ (Sigma.fst x_2) (Finset.sort (Sigma.snd x_2) fun (x1 x2 : Fin (Sigma.fst x_2)) => x1 ≤ x2))) polyH11;
  have polyH13 := Poly.add polyH3 polyH12;
  have polyH14 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n)) => Sigma.fst x_1) (10);
  have polyH15 := Poly.mul polyH14 polyH10;
  have polyH16 := Poly.add polyH13 polyH15;
  have polyH17 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.setList) (@Uniform.length ℕ Fin _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH16;
  exact Poly.lift polyH17 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem setUnion : Poly (fun x : Σ n, Universe n × (Finset (Fin n) × Finset (Fin n)) => x.1)
    (fun x => Uniform.setUnion.time x.1 x.2) 4 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => x_1.2.1);
  have polyH2 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => x_1.2.2.1);
  have polyH3 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => x_1.2.2.2);
  have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => x_1.2.2) polyH2 polyH3;
  have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => x_1.2) polyH1 polyH4;
  have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH9 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1);
  have polyH10 := Poly.add polyH9 polyH6;
  have polyH11 := Poly.add polyH8 polyH10;
  have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (10);
  have polyH13 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (1);
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) (Universe) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (Uniform.universeSet) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH16;
  have polyH18 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH19 := Poly.add polyH17 polyH18;
  have polyH20 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (20);
  have polyH21 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)));
  have polyH22 := Poly.add polyH5 polyH21;
  have polyH23 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2.1);
  have polyH24 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2.2);
  have polyH25 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2) polyH23 polyH24;
  have polyH26 := Poly.add polyH22 polyH25;
  have polyH27 := Poly.add polyH26 polyH13;
  have polyH28 := Poly.mul polyH20 polyH27;
  have polyH29 := Poly.add polyH19 polyH28;
  have polyH30 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Finset (Fin i) × Finset (Fin i)) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH29;
  have polyH31 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) polyH21 polyH25;
  have polyH32 := Poly.add polyH31 polyH6;
  have polyH33 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _ (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH32;
  have polyH34 := Poly.add polyH21 polyH6;
  have polyH35 := Poly.add polyH33 polyH34;
  have polyH36 := Poly.add polyH21 polyH13;
  have polyH37 := Poly.mul polyH12 polyH36;
  have polyH38 := Poly.add polyH35 polyH37;
  have polyH39 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _) (Uniform.setList) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH38;
  have polyH40 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _ (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH32;
  have polyH41 := Poly.add polyH39 polyH40;
  have polyH42 := Poly.add polyH31 polyH21;
  have polyH43 := Poly.add polyH42 polyH25;
  have polyH44 := Poly.add polyH43 polyH13;
  have polyH45 := Poly.mul polyH20 polyH44;
  have polyH46 := Poly.add polyH41 polyH45;
  have polyH47 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) i) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) i) => (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH46;
  have polyH48 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)));
  have polyH49 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) polyH48;
  have polyH50 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q));
  have polyH51 := Poly.volumeFin polyH50 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd q).1);
  have polyH52 := Poly.volumeFinset polyH50 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd (Sigma.fst q)).2.1);
  have polyH53 := Poly.volumeFinset polyH50 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd (Sigma.fst q)).2.2);
  have polyH54 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd (Sigma.fst q)).2) polyH52 polyH53;
  have polyH55 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))) polyH51 polyH54;
  have polyH56 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (2);
  have polyH57 := Poly.add polyH55 polyH56;
  have polyH58 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH57;
  have polyH59 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH57;
  have polyH60 := Poly.add polyH54 polyH56;
  have polyH61 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH60;
  have polyH62 := Poly.add polyH59 polyH61;
  have polyH63 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (10);
  have polyH64 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (1);
  have polyH65 := Poly.add polyH54 polyH64;
  have polyH66 := Poly.mul polyH63 polyH65;
  have polyH67 := Poly.add polyH62 polyH66;
  have polyH68 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH67;
  have polyH69 := Poly.add polyH58 polyH68;
  have polyH70 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (20);
  have polyH71 := Poly.add polyH55 polyH51;
  have polyH72 := Poly.volumeFinset polyH50 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))).1);
  have polyH73 := Poly.add polyH71 polyH72;
  have polyH74 := Poly.add polyH73 polyH64;
  have polyH75 := Poly.mul polyH70 polyH74;
  have polyH76 := Poly.add polyH69 polyH75;
  have polyH77 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (Fin) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH76;
  have polyH78 := Poly.reparam (@Costs.setMem) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))), Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH50;
  have polyH79 := Poly.add polyH77 polyH78;
  have polyH80 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))), Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH51 polyH72;
  have polyH81 := Poly.add polyH80 polyH64;
  have polyH82 := Poly.mul polyH63 polyH81;
  have polyH83 := Poly.add polyH79 polyH82;
  have polyH84 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) Fin (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) (Uniform.setMem) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH83;
  have polyH85 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH60;
  have polyH86 := Poly.add polyH59 polyH85;
  have polyH87 := Poly.add polyH86 polyH66;
  have polyH88 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH87;
  have polyH89 := Poly.add polyH58 polyH88;
  have polyH90 := Poly.volumeFinset polyH50 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))).2);
  have polyH91 := Poly.add polyH71 polyH90;
  have polyH92 := Poly.add polyH91 polyH64;
  have polyH93 := Poly.mul polyH70 polyH92;
  have polyH94 := Poly.add polyH89 polyH93;
  have polyH95 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (Fin) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH94;
  have polyH96 := Poly.reparam (@Costs.setMem) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH50;
  have polyH97 := Poly.add polyH95 polyH96;
  have polyH98 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH51 polyH90;
  have polyH99 := Poly.add polyH98 polyH64;
  have polyH100 := Poly.mul polyH63 polyH99;
  have polyH101 := Poly.add polyH97 polyH100;
  have polyH102 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) Fin (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) (Uniform.setMem) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH101;
  have polyH103 := Poly.add polyH84 polyH102;
  have polyH104 := Poly.volumeBool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Decidable.decide (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))) ∈ Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))));
  have polyH105 := Poly.add polyH55 polyH104;
  have polyH106 := Poly.volumeBool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Decidable.decide (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))) ∈ Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))));
  have polyH107 := Poly.add polyH105 polyH106;
  have polyH108 := Poly.add polyH107 polyH64;
  have polyH109 := Poly.mul polyH70 polyH108;
  have polyH110 := Poly.add polyH103 polyH109;
  have polyH111 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) ((fun (x_2 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) x_1)) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) ((fun (x_2 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_2, Prod.snd (Prod.snd x_2))) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) Fin (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) Uniform.setMem) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) Fin (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) Uniform.setMem) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH110;
  have polyH112 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)) (10000);
  have polyH113 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (@Realizer.time_or_le (((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))), (fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))))) polyH112;
  have polyH114 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_uniform (ℕ) (Bool × Bool) (Bool) _ _ (fun (x_1 : Bool × Bool) => Prod.fst x_1 || Prod.snd x_1) (Realizer.or) (Sigma.fst (Sigma.fst q)) (((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))), (fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH113;
  have polyH115 := Poly.add polyH111 polyH114;
  have polyH116 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))), (fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Finset (Fin (Sigma.fst (Sigma.fst q))) × Finset (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH104 polyH106;
  have polyH117 := Poly.add polyH116 polyH64;
  have polyH118 := Poly.mul polyH63 polyH117;
  have polyH119 := Poly.add polyH115 polyH118;
  have polyH120 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Bool × Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => ((fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) ((fun (x_2 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) x_1), (fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) ((fun (x_2 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_2, Prod.snd (Prod.snd x_2))) x_1))) (fun (x_1 : ℕ) (x_2 : Bool × Bool) => Prod.fst x_2 || Prod.snd x_2) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) ((fun (x_2 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) x_1)) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (fun (x_2 : Fin i × Finset (Fin i)) => Decidable.decide (Prod.fst x_2 ∈ Prod.snd x_2)) ((fun (x_2 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_2, Prod.snd (Prod.snd x_2))) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) Fin (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) Uniform.setMem) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) Fin (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) Uniform.setMem)) (Realizer.uniform Realizer.or ℕ) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH119;
  have polyH121 := @Poly.filterTime (ℕ) ((n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Fin) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _ (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => Prod.snd (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.fst (Prod.snd x_1) ∨ Prod.fst x_1 ∈ Prod.snd (Prod.snd x_1))) (Uniform.setUnionBody) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (Max.max (Max.max (2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (2 * 1) (2 * 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (1)) (2 * 1)) (0))) (3 * 1)) (0 + Max.max (Max.max (1) (2 * 1)) (0))) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (Max.max (Max.max (2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (2 * 1) (2 * 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (1)) (2 * 1)) (0))) (3 * 1)) (0 + Max.max (Max.max (1) (2 * 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (0)) (0))) (0)) (0 + Max.max (Max.max (0) (0)) (0))) (2 * 1) (Max.max (2 * 1) (2 * 1)) polyH49 polyH120 polyH21 polyH25;
  have polyH122 := Poly.add polyH47 polyH121;
  have polyH123 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) polyH21 polyH25;
  have polyH124 := Poly.add polyH123 polyH13;
  have polyH125 := Poly.mul polyH12 polyH124;
  have polyH126 := Poly.add polyH122 polyH125;
  have polyH127 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) => (Finset.sort (Prod.fst x_1) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Finset (Fin i) × Finset (Fin i)) => List.filter (fun (a : Fin i) => Decidable.decide (Prod.fst (a, Prod.snd x_1) ∈ Prod.fst (Prod.snd (a, Prod.snd x_1)) ∨ Prod.fst (a, Prod.snd x_1) ∈ Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst x_1)) (@Uniform.onFst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _ _ (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) Uniform.setList) (@Uniform.filter ℕ Fin (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.fst (Prod.snd x_1) ∨ Prod.fst x_1 ∈ Prod.snd (Prod.snd x_1))) Uniform.setUnionBody) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH126;
  have polyH128 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_setFilter (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.fst (Prod.snd x_1) ∨ Prod.fst x_1 ∈ Prod.snd (Prod.snd x_1))) (Uniform.setUnionBody) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH127;
  have polyH129 := Poly.add polyH30 polyH128;
  have polyH130 := Poly.add polyH31 polyH13;
  have polyH131 := Poly.mul polyH12 polyH130;
  have polyH132 := Poly.add polyH129 polyH131;
  have polyH133 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Finset (Fin i) × Finset (Fin i)) => ((fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), Prod.snd x_1)) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) => {a ∈ Prod.fst x_1 | Decidable.decide (Prod.fst (a, Prod.snd x_1) ∈ Prod.fst (Prod.snd (a, Prod.snd x_1)) ∨ Prod.fst (a, Prod.snd x_1) ∈ Prod.snd (Prod.snd (a, Prod.snd x_1))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Finset (Fin i) × Finset (Fin i)) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _)) (@Uniform.setFilter (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.fst (Prod.snd x_1) ∨ Prod.fst x_1 ∈ Prod.snd (Prod.snd x_1))) Uniform.setUnionBody) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH132;
  exact Poly.lift polyH133 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

theorem blockEmpty : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.blockEmpty.time x.1 x.2) 3 := by (
  have polyH0 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (2);
  have polyH1 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_zero (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH0;
  have polyH2 := Poly.size (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1);
  have polyH3 := Poly.volumeUniverse polyH2 (fun (x_1 : (n : ℕ) × Universe n) => x_1.2);
  have polyH4 := Poly.add polyH3 polyH0;
  have polyH5 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_id (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH4;
  have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_unit (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH0;
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (20);
  have polyH9 := Poly.add polyH3 polyH3;
  have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (volume ());
  have polyH11 := Poly.add polyH9 polyH10;
  have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (1);
  have polyH13 := Poly.add polyH11 polyH12;
  have polyH14 := Poly.mul polyH8 polyH13;
  have polyH15 := Poly.add polyH7 polyH14;
  have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (Universe) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH15;
  have polyH17 := Poly.volumeUnit (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => PUnit.unit);
  have polyH18 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (Sigma.snd x_1, ())) polyH3 polyH17;
  have polyH19 := Poly.add polyH18 polyH0;
  have polyH20 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Unit) _ _ (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH19;
  have polyH21 := Poly.add polyH20 polyH4;
  have polyH22 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (10);
  have polyH23 := Poly.add polyH3 polyH12;
  have polyH24 := Poly.mul polyH22 polyH23;
  have polyH25 := Poly.add polyH21 polyH24;
  have polyH26 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (fun (i_1 : ℕ) => Unit) i) (Universe) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Unit) _ _) (Uniform.universeList) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH25;
  have polyH27 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Unit) _ _ (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH19;
  have polyH28 := Poly.add polyH26 polyH27;
  have polyH29 := Poly.volumeFinRange polyH2;
  have polyH30 := Poly.add polyH18 polyH29;
  have polyH31 := Poly.add polyH30 polyH17;
  have polyH32 := Poly.add polyH31 polyH12;
  have polyH33 := Poly.mul polyH8 polyH32;
  have polyH34 := Poly.add polyH28 polyH33;
  have polyH35 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (fun (i_1 : ℕ) => Unit) i) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i × (fun (i_1 : ℕ) => Unit) i) => (fun (n : ℕ) (x_3 : Universe n) => List.finRange n) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (fun (i_1 : ℕ) => Unit) i) Universe (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Unit) _ _) Uniform.universeList) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Unit) _ _) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH34;
  have polyH36 := Poly.lengthFinRange polyH2;
  have polyH37 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (2);
  have polyH38 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) => (le_of_eq (@Uniform.time_zero (ℕ) (fun (i : ℕ) => Fin i × Unit) _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Sigma.snd (Sigma.fst q), ()))))))) polyH37;
  have polyH39 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (0);
  have polyH40 := Poly.volumeNat polyH39;
  have polyH41 := @Poly.mapTime (ℕ) ((n : ℕ) × Universe n) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Fin) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Unit) _ _ _ (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) (fun (x_1 : (n : ℕ) × Universe n) => Prod.snd (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _) (1) (0) (2 * 1) (0) (0) polyH36 polyH38 polyH29 polyH17 polyH40;
  have polyH42 := Poly.add polyH35 polyH41;
  have polyH43 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (List.finRange (Sigma.fst x_1), Prod.snd (Sigma.snd x_1, ()))) polyH29 polyH17;
  have polyH44 := Poly.add polyH43 polyH12;
  have polyH45 := Poly.mul polyH22 polyH44;
  have polyH46 := Poly.add polyH42 polyH45;
  have polyH47 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Unit) (fun (i : ℕ) => List (Fin i) × Unit) (fun (i : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Unit) => (List.finRange i, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Unit) => List.map (fun (a : Fin i) => 0) (Prod.fst x_1)) (@Uniform.onFst ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => Unit) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) Uniform.universeList) (@Uniform.map ℕ Fin (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _)) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH46;
  have polyH48 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _) (Sigma.fst x_2) ((Sigma.snd x_2, ()))))) polyH47;
  have polyH49 := Poly.add polyH16 polyH48;
  have polyH50 := Poly.add polyH18 polyH12;
  have polyH51 := Poly.mul polyH22 polyH50;
  have polyH52 := Poly.add polyH49 polyH51;
  have polyH53 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => Universe i × Unit) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (x_1, ())) (fun (n : ℕ) (x_1 : Universe n × Unit) (v : Fin n) => 0) (@Uniform.pair ℕ Universe Universe (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _)) (@Uniform.vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH52;
  have polyH54 := Poly.add polyH1 polyH53;
  have polyH55 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (volume (0));
  have polyH56 := Poly.add polyH3 polyH55;
  have polyH57 := Poly.const (fun (q : Poly.FinPool fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (0);
  have polyH58 := Poly.volumeNat polyH57;
  have polyH59 := Poly.volumeFunction (fun (x_1 : (n : ℕ) × Universe n) (v : Fin (Sigma.fst x_1)) => 0) polyH2 polyH58;
  have polyH60 := Poly.add polyH56 polyH59;
  have polyH61 := Poly.add polyH60 polyH12;
  have polyH62 := Poly.mul polyH8 polyH61;
  have polyH63 := Poly.add polyH54 polyH62;
  have polyH64 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (fun (i : ℕ) => ℕ) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => 0) (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : Universe i × Unit) (v : Fin i) => 0) ((fun (x_3 : Universe i) => (x_3, ())) x_1)) (@Uniform.zero ℕ Universe _) (@Uniform.comp ℕ Universe (fun (i : ℕ) => Universe i × Unit) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (x_1, ())) (fun (n : ℕ) (x_1 : Universe n × Unit) (v : Fin n) => 0) (@Uniform.pair ℕ Universe Universe (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _)) (@Uniform.vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _))) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH63;
  have polyH65 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (0);
  have polyH66 := Poly.volumeNat polyH65;
  have polyH67 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (0, (fun (x_2 : Universe (Sigma.fst x_1) × Unit) (v : Fin (Sigma.fst x_1)) => 0) ((fun (x_2 : Universe (Sigma.fst x_1)) => (x_2, ())) (Sigma.snd x_1)))) polyH66 polyH59;
  have polyH68 := Poly.add polyH67 polyH0;
  have polyH69 := Poly.add polyH64 polyH68;
  have polyH70 := Poly.add polyH67 polyH12;
  have polyH71 := Poly.mul polyH22 polyH70;
  have polyH72 := Poly.add polyH69 polyH71;
  have polyH73 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (0, (fun (x_3 : Universe i × Unit) (v : Fin i) => 0) ((fun (x_3 : Universe i) => (x_3, ())) x_1))) (fun (n : ℕ) (x_1 : ℕ × (Fin n → ℕ)) => OAI.ThreeMachine.Algorithm.Block.mk (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ Universe (fun (i : ℕ) => ℕ) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => 0) (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : Universe i × Unit) (v : Fin i) => 0) ((fun (x_3 : Universe i) => (x_3, ())) x_1)) (@Uniform.zero ℕ Universe _) (@Uniform.comp ℕ Universe (fun (i : ℕ) => Universe i × Unit) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (x_1, ())) (fun (n : ℕ) (x_1 : Universe n × Unit) (v : Fin n) => 0) (@Uniform.pair ℕ Universe Universe (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => x_1) (fun (i : ℕ) (x_1 : Universe i) => ()) (@Uniform.id ℕ Universe _) (@Uniform.unit ℕ Universe _)) (@Uniform.vectorMap (fun (i : ℕ) => Unit) (fun (i : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Unit) => 0) (@Uniform.zero ℕ (fun (i : ℕ) => Fin i × Unit) _)))) (Uniform.blockMake) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH72;
  exact Poly.lift polyH73 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

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

theorem lengthTriples (hn : Poly s n d) :
    Poly s (fun j => (Structure.tripleList (List.finRange (n j))).length) (3*d) := by
  apply of_le (fun j => Structure.tripleList_length (List.finRange (n j)))
  simp only [List.length_finRange]
  (
  have polyH0 := Poly.pow (hn) (3);
  exact Poly.lift polyH0 (by first | decide +kernel | omega))

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

theorem volumeSetList (xs : ∀ j, List (Finset (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (xs j).length) l) :
    Poly s (fun j => volume (xs j)) (l+2*d) := by
  apply volumeList hl (show Poly s (fun j => 3*(n j+1)^2) (2*d) from by (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j a _ha
  exact volume_finset_le a

end ThreeMachine.StackCompiler.Poly
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

theorem layerStep_iterate {n : ℕ} (e : Uniform.LayerEnv n) (k : ℕ) :
    (fun p : Uniform.LayerEnv n × Table n =>
      (p.1,Algorithm.tableOf p.1.2.2.1 (Algorithm.solve (matrixRel p.1.2.1) p.2 p.1.2.2.1 p.1.2.2.2)))^[k]
        (e,[(∅,Algorithm.Block.empty)]) =
        (e,Algorithm.layers (matrixRel e.2.1) e.2.2.1 e.2.2.2 k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

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
-- module RankCosts
namespace OAI

universe u1 u2

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.RankCellInput (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_triples (n : ℕ) (x : Universe n) :
    triples.time n x = ((triplesA.pair unit).comp triplesP.filter).time n x := rfl

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem triplesP : Poly (fun x : Σ n, Finset (Fin n) × Unit => x.1)
    (fun x => Uniform.triplesP.time x.1 x.2) 3 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => x_1.2.1);
  have polyH2 := Poly.volumeUnit (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Unit) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5;
  have polyH7 := Poly.reparam (@Costs.setCard) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.mk (Sigma.fst x_1) (Prod.fst (Sigma.snd x_1))) polyH0;
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (10);
  have polyH10 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => (Sigma.snd x_1).1);
  have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (1);
  have polyH12 := Poly.add polyH10 polyH11;
  have polyH13 := Poly.mul polyH9 polyH12;
  have polyH14 := Poly.add polyH8 polyH13;
  have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Unit) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.card s) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Unit) _ _) (Uniform.setCard) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH14;
  have polyH16 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (2 * volume (3) + 1);
  have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (20);
  have polyH18 := Poly.mul polyH17 polyH3;
  have polyH19 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (50 * volume (3));
  have polyH20 := Poly.add polyH18 polyH19;
  have polyH21 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (50);
  have polyH22 := Poly.add polyH20 polyH21;
  have polyH23 := Poly.mul polyH16 polyH22;
  have polyH24 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (le_of_eq (@Uniform.time_constant (ℕ) (fun (i : ℕ) => Finset (Fin i) × Unit) _ (ℕ) _ (3) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH23;
  have polyH25 := Poly.add polyH15 polyH24;
  have polyH26 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => (Sigma.snd x_1).1);
  have polyH27 := Poly.volumeNat polyH26;
  have polyH28 := Poly.add polyH3 polyH27;
  have polyH29 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (volume (3));
  have polyH30 := Poly.add polyH28 polyH29;
  have polyH31 := Poly.add polyH30 polyH11;
  have polyH32 := Poly.mul polyH17 polyH31;
  have polyH33 := Poly.add polyH25 polyH32;
  have polyH34 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × Unit) (fun (n : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Unit) => (fun (s : Finset (Fin i)) => Finset.card s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Unit) => 3) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Unit) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.card s) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Unit) _ _) Uniform.setCard) (@Uniform.constant ℕ (fun (i : ℕ) => Finset (Fin i) × Unit) _ ℕ _ (3)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH33;
  have polyH35 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (10000000000);
  have polyH36 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => Sigma.fst x_1) (3);
  have polyH37 := Poly.add polyH26 polyH36;
  have polyH38 := Poly.add polyH37 polyH11;
  have polyH39 := Poly.pow polyH38 (2);
  have polyH40 := Poly.mul polyH35 polyH39;
  have polyH41 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (@Realizer.time_eqNat_le ((fun (s : Finset (Fin (Sigma.fst x_2))) => Finset.card s) (Prod.fst (Sigma.snd x_2))) (3))) polyH40;
  have polyH42 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ × ℕ) (Bool) _ _ (fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (Realizer.eqNat) (Sigma.fst x_2) (((fun (s : Finset (Fin (Sigma.fst x_2))) => Finset.card s) (Prod.fst (Sigma.snd x_2)), 3))))) polyH41;
  have polyH43 := Poly.add polyH34 polyH42;
  have polyH44 := Poly.volumeNat polyH36;
  have polyH45 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Unit) => ((fun (s : Finset (Fin (Sigma.fst x_1))) => Finset.card s) (Prod.fst (Sigma.snd x_1)), 3)) polyH27 polyH44;
  have polyH46 := Poly.add polyH45 polyH11;
  have polyH47 := Poly.mul polyH9 polyH46;
  have polyH48 := Poly.add polyH43 polyH47;
  have polyH49 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Unit) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Unit) (fun (i : ℕ) => ℕ × ℕ) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Unit) => ((fun (s : Finset (Fin i)) => Finset.card s) (Prod.fst x_1), 3)) (fun (x_1 : ℕ) (x_3 : ℕ × ℕ) => Decidable.decide (Prod.fst x_3 = Prod.snd x_3)) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × Unit) (fun (n : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Unit) => (fun (s : Finset (Fin i)) => Finset.card s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Unit) => 3) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Unit) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.card s) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Unit) _ _) Uniform.setCard) (@Uniform.constant ℕ (fun (i : ℕ) => Finset (Fin i) × Unit) _ ℕ _ (3))) (Realizer.uniform Realizer.eqNat ℕ) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH48;
  exact Poly.lift polyH49 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem triples : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.triples.time x.1 x.2) 20 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1);
  have polyH1 := Poly.reparam (@Costs.triplesA) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0;
  have polyH2 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (2);
  have polyH3 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_unit (ℕ) (Universe) _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH2;
  have polyH4 := Poly.add polyH1 polyH3;
  have polyH5 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (20);
  have polyH6 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n) => x_1.2);
  have polyH7 := Poly.lengthFinRange polyH0;
  have polyH8 := Poly.lengthProduct polyH7 polyH7;
  have polyH9 := Poly.lengthProduct polyH7 polyH8;
  have polyH10 := Poly.lengthMap (fun (x_1 : (n : ℕ) × Universe n) (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_2 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_2)) {Prod.fst (Prod.snd (Prod.snd x_2)), Prod.snd (Prod.snd (Prod.snd x_2))}) ((fun (x_2 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_2, Prod.fst x_2)) (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1))))) polyH9;
  have polyH11 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_2 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_2)) {Prod.fst (Prod.snd (Prod.snd x_2)), Prod.snd (Prod.snd (Prod.snd x_2))}) ((fun (x_2 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_2, Prod.fst x_2)) (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1))))) (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH12 := Poly.volumeFinset polyH11 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_2 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_2)) {Prod.fst (Prod.snd (Prod.snd x_2)), Prod.snd (Prod.snd (Prod.snd x_2))}) ((fun (x_2 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_2, Prod.fst x_2)) (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1))))) (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)))) => (Sigma.snd q).1);
  have polyH13 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_2 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_2)) {Prod.fst (Prod.snd (Prod.snd x_2)), Prod.snd (Prod.snd (Prod.snd x_2))}) ((fun (x_2 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_2, Prod.fst x_2)) (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1))))) (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)))) polyH10 polyH12;
  have polyH14 := Poly.add polyH6 polyH13;
  have polyH15 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (volume ());
  have polyH16 := Poly.add polyH14 polyH15;
  have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (1);
  have polyH18 := Poly.add polyH16 polyH17;
  have polyH19 := Poly.mul polyH5 polyH18;
  have polyH20 := Poly.add polyH4 polyH19;
  have polyH21 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : List (Fin i × Fin i × Fin i) × Universe i) => List.map (fun (a : Fin i × Fin i × Fin i) => (fun (x_4 : Universe i × Fin i × Fin i × Fin i) => @Insert.insert (Fin i) (Finset (Fin i)) Finset.instInsert (Prod.fst (Prod.snd x_4)) {Prod.fst (Prod.snd (Prod.snd x_4)), Prod.snd (Prod.snd (Prod.snd x_4))}) ((fun (x_4 : (Fin i × Fin i × Fin i) × Universe i) => (Prod.snd x_4, Prod.fst x_4)) (a, Prod.snd x_3))) (Prod.fst x_3)) ((fun (x_3 : Universe i) => ((fun (x_4 : List (Fin i) × List (Fin i × Fin i)) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe i) => (List.finRange i, (fun (x_5 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_5) (Prod.snd x_5)) ((fun (x_5 : Universe i) => (List.finRange i, List.finRange i)) x_4))) x_3), x_3)) x_1)) (fun (i : ℕ) (x_1 : Universe i) => ()) (Uniform.triplesA) (@Uniform.unit ℕ Universe _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH20;
  have polyH22 := Poly.size (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) (fun (i : ℕ) => Finset (Fin i)) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst ((fun (x_2 : List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_3 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_3)) {Prod.fst (Prod.snd (Prod.snd x_3)), Prod.snd (Prod.snd (Prod.snd x_3))}) ((fun (x_3 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_3, Prod.fst x_3)) (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)), ())) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH23 := Poly.reparam (@Costs.triplesP) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) (fun (i : ℕ) => Finset (Fin i)) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst ((fun (x_2 : List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_3 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_3)) {Prod.fst (Prod.snd (Prod.snd x_3)), Prod.snd (Prod.snd (Prod.snd x_3))}) ((fun (x_3 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_3, Prod.fst x_3)) (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)), ())) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd ((fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) × Universe (Sigma.fst (Sigma.fst q))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (fun (x_2 : Universe (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => @Insert.insert (Fin (Sigma.fst (Sigma.fst q))) (Finset (Fin (Sigma.fst (Sigma.fst q)))) Finset.instInsert (Prod.fst (Prod.snd x_2)) {Prod.fst (Prod.snd (Prod.snd x_2)), Prod.snd (Prod.snd (Prod.snd x_2))}) ((fun (x_2 : (Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) × Universe (Sigma.fst (Sigma.fst q))) => (Prod.snd x_2, Prod.fst x_2)) (a, Prod.snd x_1))) (Prod.fst x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => ((fun (x_2 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_3 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) x_2))) x_1), x_1)) (Sigma.snd (Sigma.fst q))), ()))) polyH22;
  have polyH24 := Poly.volumeUnit (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => PUnit.unit);
  have polyH25 := @Poly.filterTime (ℕ) ((n : ℕ) × Universe n) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Unit) _ _ (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst ((fun (x_2 : List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_3 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_3)) {Prod.fst (Prod.snd (Prod.snd x_3)), Prod.snd (Prod.snd (Prod.snd x_3))}) ((fun (x_3 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_3, Prod.fst x_3)) (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)), ())) (fun (x_1 : (n : ℕ) × Universe n) => Prod.snd ((fun (x_2 : List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_3 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_3)) {Prod.fst (Prod.snd (Prod.snd x_3)), Prod.snd (Prod.snd (Prod.snd x_3))}) ((fun (x_3 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_3, Prod.fst x_3)) (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)), ())) (fun (n : ℕ) (x_1 : Finset (Fin n) × Unit) => Decidable.decide (Finset.card (Prod.fst x_1) = 3)) (Uniform.triplesP) (1 + (1 + 1)) (3 * 1) (1 + (1 + 1) + 2 * 1) (0) polyH10 polyH23 polyH13 polyH24;
  have polyH26 := Poly.add polyH21 polyH25;
  have polyH27 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (10);
  have polyH28 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => ((fun (x_2 : List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => List.map (fun (a : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (fun (x_3 : Universe (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => @Insert.insert (Fin (Sigma.fst x_1)) (Finset (Fin (Sigma.fst x_1))) Finset.instInsert (Prod.fst (Prod.snd x_3)) {Prod.fst (Prod.snd (Prod.snd x_3)), Prod.snd (Prod.snd (Prod.snd x_3))}) ((fun (x_3 : (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) × Universe (Sigma.fst x_1)) => (Prod.snd x_3, Prod.fst x_3)) (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => ((fun (x_3 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1))) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), (fun (x_4 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) x_3))) x_2), x_2)) (Sigma.snd x_1)), ())) polyH13 polyH24;
  have polyH29 := Poly.add polyH28 polyH17;
  have polyH30 := Poly.mul polyH27 polyH29;
  have polyH31 := Poly.add polyH26 polyH30;
  have polyH32 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => List (Finset (Fin i)) × Unit) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => ((fun (x_3 : List (Fin i × Fin i × Fin i) × Universe i) => List.map (fun (a : Fin i × Fin i × Fin i) => (fun (x_4 : Universe i × Fin i × Fin i × Fin i) => @Insert.insert (Fin i) (Finset (Fin i)) Finset.instInsert (Prod.fst (Prod.snd x_4)) {Prod.fst (Prod.snd (Prod.snd x_4)), Prod.snd (Prod.snd (Prod.snd x_4))}) ((fun (x_4 : (Fin i × Fin i × Fin i) × Universe i) => (Prod.snd x_4, Prod.fst x_4)) (a, Prod.snd x_3))) (Prod.fst x_3)) ((fun (x_3 : Universe i) => ((fun (x_4 : List (Fin i) × List (Fin i × Fin i)) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe i) => (List.finRange i, (fun (x_5 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_5) (Prod.snd x_5)) ((fun (x_5 : Universe i) => (List.finRange i, List.finRange i)) x_4))) x_3), x_3)) x_1), ())) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × Unit) => List.filter (fun (a : Finset (Fin i)) => Decidable.decide (Finset.card (Prod.fst (a, Prod.snd x_1)) = 3)) (Prod.fst x_1)) (@Uniform.pair ℕ Universe (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => Unit) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : List (Fin i × Fin i × Fin i) × Universe i) => List.map (fun (a : Fin i × Fin i × Fin i) => (fun (x_4 : Universe i × Fin i × Fin i × Fin i) => @Insert.insert (Fin i) (Finset (Fin i)) Finset.instInsert (Prod.fst (Prod.snd x_4)) {Prod.fst (Prod.snd (Prod.snd x_4)), Prod.snd (Prod.snd (Prod.snd x_4))}) ((fun (x_4 : (Fin i × Fin i × Fin i) × Universe i) => (Prod.snd x_4, Prod.fst x_4)) (a, Prod.snd x_3))) (Prod.fst x_3)) ((fun (x_3 : Universe i) => ((fun (x_4 : List (Fin i) × List (Fin i × Fin i)) => List.product (Prod.fst x_4) (Prod.snd x_4)) ((fun (x_4 : Universe i) => (List.finRange i, (fun (x_5 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_5) (Prod.snd x_5)) ((fun (x_5 : Universe i) => (List.finRange i, List.finRange i)) x_4))) x_3), x_3)) x_1)) (fun (i : ℕ) (x_1 : Universe i) => ()) Uniform.triplesA (@Uniform.unit ℕ Universe _)) (@Uniform.filter ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Unit) _ _ (fun (n : ℕ) (x_1 : Finset (Fin n) × Unit) => Decidable.decide (Finset.card (Prod.fst x_1) = 3)) Uniform.triplesP) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH31;
  have polyH33 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_triples (Sigma.fst x_2) (Sigma.snd x_2)))) polyH32;
  exact Poly.lift polyH33 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

section
-- module FamilyCosts
namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (k : ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (xs : ∀ j, List (Finset (Fin (n j))))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable {K : ℕ} (r : ∀ j, Fin K → Finset (Fin (n j)))

theorem evalTemplate (p : Formula (Fin K)) :
    Poly n (fun j => (Uniform.evalTemplate p).time (n j) (U j,r j)) 4 := by
  induction p with
  | leaf a b => cases b <;> simp only [Uniform.evalTemplate,Bool.false_eq_true,↓reduceDIte] <;> [(
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.const (n) (K);
  have polyH3 := Poly.size (fun (q : Poly.FinPool fun (j_1 : J) => K) => n (Sigma.fst q));
  have polyH4 := Poly.volumeFinset polyH3 (fun (q : Poly.FinPool fun (j_1 : J) => K) => r (Sigma.fst q) (Sigma.snd q));
  have polyH5 := Poly.volumeFunction (fun (j_1 : J) => r j_1) polyH2 polyH4;
  have polyH6 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH1 polyH5;
  have polyH7 := Poly.const (n) (2);
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _ (n j_9) ((U j_9, r j_9))))) polyH8;
  have polyH10 := Poly.const (n) (2 * volume a + 1);
  have polyH11 := Poly.const (n) (20);
  have polyH12 := Poly.mul polyH11 polyH6;
  have polyH13 := Poly.const (n) (50 * volume a);
  have polyH14 := Poly.add polyH12 polyH13;
  have polyH15 := Poly.const (n) (50);
  have polyH16 := Poly.add polyH14 polyH15;
  have polyH17 := Poly.mul polyH10 polyH16;
  have polyH18 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_constant (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ (a) (n j_9) ((U j_9, r j_9))))) polyH17;
  have polyH19 := Poly.add polyH9 polyH18;
  have polyH20 := Poly.add polyH6 polyH5;
  have polyH21 := Poly.const (n) (volume a);
  have polyH22 := Poly.add polyH20 polyH21;
  have polyH23 := Poly.const (n) (1);
  have polyH24 := Poly.add polyH22 polyH23;
  have polyH25 := Poly.mul polyH11 polyH24;
  have polyH26 := Poly.add polyH19 polyH25;
  have polyH27 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Fin K → Finset (Fin i)) (fun (i : ℕ) => Fin K) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => a) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ a) (n j_9) ((U j_9, r j_9))))) polyH26;
  have polyH28 := Poly.const (n) (1000000000 * (K + 1));
  have polyH29 := Poly.add polyH5 polyH2;
  have polyH30 := Poly.add polyH29 polyH23;
  have polyH31 := Poly.mul polyH28 polyH30;
  have polyH32 := Poly.of_le (fun (j_9 : J) => (@Uniform.time_functionGetAny_le (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (fun (x : ℕ) => K) (n j_9) (Prod.snd (U j_9, r j_9)) (a))) polyH31;
  have polyH33 := Poly.add polyH27 polyH32;
  have polyH34 := Poly.const (n) (10);
  have polyH35 := Poly.volumeFin polyH2 (fun (j_1 : J) => a);
  have polyH36 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (U j_1, r j_1), a)) polyH5 polyH35;
  have polyH37 := Poly.add polyH36 polyH23;
  have polyH38 := Poly.mul polyH34 polyH37;
  have polyH39 := Poly.add polyH33 polyH38;
  have polyH40 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => (Fin K → Finset (Fin i)) × Fin K) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x, a)) (fun (i : ℕ) (x : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Fin K → Finset (Fin i)) (fun (i : ℕ) => Fin K) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => a) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ a)) (@Uniform.functionGetAny ℕ (fun (i : ℕ) => Finset (Fin i)) _ fun (x : ℕ) => K) (n j_9) ((U j_9, r j_9))))) polyH39;
  exact Poly.lift polyH40 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega)); (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.const (n) (K);
  have polyH3 := Poly.size (fun (q : Poly.FinPool fun (j_1 : J) => K) => n (Sigma.fst q));
  have polyH4 := Poly.volumeFinset polyH3 (fun (q : Poly.FinPool fun (j_1 : J) => K) => r (Sigma.fst q) (Sigma.snd q));
  have polyH5 := Poly.volumeFunction (fun (j_1 : J) => r j_1) polyH2 polyH4;
  have polyH6 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH1 polyH5;
  have polyH7 := Poly.const (n) (2);
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _ (n j_9) ((U j_9, r j_9))))) polyH8;
  have polyH10 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _ (n j_9) ((U j_9, r j_9))))) polyH8;
  have polyH11 := Poly.const (n) (2 * volume a + 1);
  have polyH12 := Poly.const (n) (20);
  have polyH13 := Poly.mul polyH12 polyH6;
  have polyH14 := Poly.const (n) (50 * volume a);
  have polyH15 := Poly.add polyH13 polyH14;
  have polyH16 := Poly.const (n) (50);
  have polyH17 := Poly.add polyH15 polyH16;
  have polyH18 := Poly.mul polyH11 polyH17;
  have polyH19 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_constant (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ (a) (n j_9) ((U j_9, r j_9))))) polyH18;
  have polyH20 := Poly.add polyH10 polyH19;
  have polyH21 := Poly.add polyH6 polyH5;
  have polyH22 := Poly.const (n) (volume a);
  have polyH23 := Poly.add polyH21 polyH22;
  have polyH24 := Poly.const (n) (1);
  have polyH25 := Poly.add polyH23 polyH24;
  have polyH26 := Poly.mul polyH12 polyH25;
  have polyH27 := Poly.add polyH20 polyH26;
  have polyH28 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Fin K → Finset (Fin i)) (fun (i : ℕ) => Fin K) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => a) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ a) (n j_9) ((U j_9, r j_9))))) polyH27;
  have polyH29 := Poly.const (n) (1000000000 * (K + 1));
  have polyH30 := Poly.add polyH5 polyH2;
  have polyH31 := Poly.add polyH30 polyH24;
  have polyH32 := Poly.mul polyH29 polyH31;
  have polyH33 := Poly.of_le (fun (j_9 : J) => (@Uniform.time_functionGetAny_le (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (fun (x : ℕ) => K) (n j_9) (Prod.snd (U j_9, r j_9)) (a))) polyH32;
  have polyH34 := Poly.add polyH28 polyH33;
  have polyH35 := Poly.const (n) (10);
  have polyH36 := Poly.volumeFin polyH2 (fun (j_1 : J) => a);
  have polyH37 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (U j_1, r j_1), a)) polyH5 polyH36;
  have polyH38 := Poly.add polyH37 polyH24;
  have polyH39 := Poly.mul polyH35 polyH38;
  have polyH40 := Poly.add polyH34 polyH39;
  have polyH41 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => (Fin K → Finset (Fin i)) × Fin K) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x, a)) (fun (i : ℕ) (x : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Fin K → Finset (Fin i)) (fun (i : ℕ) => Fin K) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => a) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ a)) (@Uniform.functionGetAny ℕ (fun (i : ℕ) => Finset (Fin i)) _ fun (x : ℕ) => K) (n j_9) ((U j_9, r j_9))))) polyH40;
  have polyH42 := Poly.add polyH9 polyH41;
  have polyH43 := Poly.add polyH6 polyH1;
  have polyH44 := Poly.volumeFinset polyH0 (fun (j_1 : J) => r j_1 (Prod.snd ((fun (x : Universe (n j_1) × (Fin K → Finset (Fin (n j_1)))) => (Prod.snd x, a)) (U j_1, r j_1))));
  have polyH45 := Poly.add polyH43 polyH44;
  have polyH46 := Poly.add polyH45 polyH24;
  have polyH47 := Poly.mul polyH12 polyH46;
  have polyH48 := Poly.add polyH42 polyH47;
  have polyH49 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (Universe) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (fun (x_1 : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x_1, a)) x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => (Fin K → Finset (Fin i)) × Fin K) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x, a)) (fun (i : ℕ) (x : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Fin K → Finset (Fin i)) (fun (i : ℕ) => Fin K) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => a) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ a)) (@Uniform.functionGetAny ℕ (fun (i : ℕ) => Finset (Fin i)) _ fun (x : ℕ) => K)) (n j_9) ((U j_9, r j_9))))) polyH48;
  have polyH50 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, r j_1), (fun (x : (Fin K → Finset (Fin (n j_1))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_1) × (Fin K → Finset (Fin (n j_1)))) => (Prod.snd x, a)) (U j_1, r j_1)))) polyH1 polyH44;
  have polyH51 := Poly.add polyH50 polyH7;
  have polyH52 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Finset (Fin i)) _ _ (n j_9) ((Prod.fst (U j_9, r j_9), (fun (x : (Fin K → Finset (Fin (n j_9))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_9) × (Fin K → Finset (Fin (n j_9)))) => (Prod.snd x, a)) (U j_9, r j_9))))))) polyH51;
  have polyH53 := Poly.add polyH1 polyH7;
  have polyH54 := Poly.add polyH52 polyH53;
  have polyH55 := Poly.add polyH1 polyH24;
  have polyH56 := Poly.mul polyH35 polyH55;
  have polyH57 := Poly.add polyH54 polyH56;
  have polyH58 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Finset (Fin i)) (Universe) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Finset (Fin i)) _ _) (Uniform.universeSet) (n j_9) ((Prod.fst (U j_9, r j_9), (fun (x : (Fin K → Finset (Fin (n j_9))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_9) × (Fin K → Finset (Fin (n j_9)))) => (Prod.snd x, a)) (U j_9, r j_9))))))) polyH57;
  have polyH59 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Finset (Fin i)) _ _ (n j_9) ((Prod.fst (U j_9, r j_9), (fun (x : (Fin K → Finset (Fin (n j_9))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_9) × (Fin K → Finset (Fin (n j_9)))) => (Prod.snd x, a)) (U j_9, r j_9))))))) polyH51;
  have polyH60 := Poly.add polyH58 polyH59;
  have polyH61 := Poly.volumeFinset polyH0 (fun (j_1 : J) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1)));
  have polyH62 := Poly.add polyH50 polyH61;
  have polyH63 := Poly.add polyH62 polyH44;
  have polyH64 := Poly.add polyH63 polyH24;
  have polyH65 := Poly.mul polyH12 polyH64;
  have polyH66 := Poly.add polyH60 polyH65;
  have polyH67 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Universe i × Finset (Fin i)) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Finset (Fin i)) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Finset (Fin i)) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Finset (Fin i)) _ _) (n j_9) ((Prod.fst (U j_9, r j_9), (fun (x : (Fin K → Finset (Fin (n j_9))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_9) × (Fin K → Finset (Fin (n j_9)))) => (Prod.snd x, a)) (U j_9, r j_9))))))) polyH66;
  have polyH68 := Poly.reparam (@Costs.setDiff) (fun (j_1 : J) => Sigma.mk (n j_1) ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.fst (U j_1, r j_1), (fun (x : (Fin K → Finset (Fin (n j_1))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_1) × (Fin K → Finset (Fin (n j_1)))) => (Prod.snd x, a)) (U j_1, r j_1)))), Prod.snd (Prod.fst (U j_1, r j_1), (fun (x : (Fin K → Finset (Fin (n j_1))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_1) × (Fin K → Finset (Fin (n j_1)))) => (Prod.snd x, a)) (U j_1, r j_1))))) polyH0;
  have polyH69 := Poly.add polyH67 polyH68;
  have polyH70 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.fst (U j_1, r j_1), (fun (x : (Fin K → Finset (Fin (n j_1))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_1) × (Fin K → Finset (Fin (n j_1)))) => (Prod.snd x, a)) (U j_1, r j_1)))), Prod.snd (Prod.fst (U j_1, r j_1), (fun (x : (Fin K → Finset (Fin (n j_1))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_1) × (Fin K → Finset (Fin (n j_1)))) => (Prod.snd x, a)) (U j_1, r j_1))))) polyH61 polyH44;
  have polyH71 := Poly.add polyH70 polyH24;
  have polyH72 := Poly.mul polyH35 polyH71;
  have polyH73 := Poly.add polyH69 polyH72;
  have polyH74 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × Finset (Fin i)) => ((fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x), Prod.snd x)) (fun (n_1 : ℕ) (x : Finset (Fin n_1) × Finset (Fin n_1)) => Prod.fst x \ Prod.snd x) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Universe i × Finset (Fin i)) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Finset (Fin i)) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Finset (Fin i)) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Finset (Fin i)) _ _)) (Uniform.setDiff) (n j_9) ((Prod.fst (U j_9, r j_9), (fun (x : (Fin K → Finset (Fin (n j_9))) × Fin K) => Prod.fst x (Prod.snd x)) ((fun (x : Universe (n j_9) × (Fin K → Finset (Fin (n j_9)))) => (Prod.snd x, a)) (U j_9, r j_9))))))) polyH73;
  have polyH75 := Poly.add polyH49 polyH74;
  have polyH76 := Poly.add polyH50 polyH24;
  have polyH77 := Poly.mul polyH35 polyH76;
  have polyH78 := Poly.add polyH75 polyH77;
  have polyH79 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Universe i × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (Prod.fst x, (fun (x_1 : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x_1, a)) x))) (fun (n_1 : ℕ) (x : Universe n_1 × Finset (Fin n_1)) => (Prod.snd x)ᶜ) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) Universe (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (fun (x_1 : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x_1, a)) x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => (Fin K → Finset (Fin i)) × Fin K) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (Prod.snd x, a)) (fun (i : ℕ) (x : (Fin K → Finset (Fin i)) × Fin K) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Fin K → Finset (Fin i)) (fun (i : ℕ) => Fin K) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => a) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) _ (Fin K) _ a)) (@Uniform.functionGetAny ℕ (fun (i : ℕ) => Finset (Fin i)) _ fun (x : ℕ) => K))) (Uniform.setCompl) (n j_9) ((U j_9, r j_9))))) polyH78;
  exact Poly.lift polyH79 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))]
  | conj p q ihp ihq => (
  have polyH0 := Poly.add (ihp) (ihq);
  have polyH1 := Poly.const (n) (20);
  have polyH2 := Poly.size (n);
  have polyH3 := Poly.volumeUniverse polyH2 (fun (j_1 : J) => U j_1);
  have polyH4 := Poly.const (n) (K);
  have polyH5 := Poly.size (fun (q_1 : Poly.FinPool fun (j_1 : J) => K) => n (Sigma.fst q_1));
  have polyH6 := Poly.volumeFinset polyH5 (fun (q_1 : Poly.FinPool fun (j_1 : J) => K) => r (Sigma.fst q_1) (Sigma.snd q_1));
  have polyH7 := Poly.volumeFunction (fun (j_1 : J) => r j_1) polyH4 polyH6;
  have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH3 polyH7;
  have polyH9 := Poly.volumeFinset polyH2 (fun (j_1 : J) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p);
  have polyH10 := Poly.add polyH8 polyH9;
  have polyH11 := Poly.volumeFinset polyH2 (fun (j_1 : J) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q);
  have polyH12 := Poly.add polyH10 polyH11;
  have polyH13 := Poly.const (n) (1);
  have polyH14 := Poly.add polyH12 polyH13;
  have polyH15 := Poly.mul polyH1 polyH14;
  have polyH16 := Poly.add polyH0 polyH15;
  have polyH17 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q) (@Uniform.evalTemplate K p) (@Uniform.evalTemplate K q) (n j_12) ((U j_12, r j_12))))) polyH16;
  have polyH18 := Poly.reparam (@Costs.setInter) (fun (j_1 : J) => Sigma.mk (n j_1) (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q)) polyH2;
  have polyH19 := Poly.add polyH17 polyH18;
  have polyH20 := Poly.const (n) (10);
  have polyH21 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q)) polyH9 polyH11;
  have polyH22 := Poly.add polyH21 polyH13;
  have polyH23 := Poly.mul polyH20 polyH22;
  have polyH24 := Poly.add polyH19 polyH23;
  have polyH25 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q)) (fun (n_1 : ℕ) (x : Finset (Fin n_1) × Finset (Fin n_1)) => Prod.fst x ∩ Prod.snd x) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q) (@Uniform.evalTemplate K p) (@Uniform.evalTemplate K q)) (Uniform.setInter) (n j_12) ((U j_12, r j_12))))) polyH24;
  exact Poly.lift polyH25 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  | disj p q ihp ihq => (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.const (n) (K);
  have polyH3 := Poly.size (fun (q_1 : Poly.FinPool fun (j_1 : J) => K) => n (Sigma.fst q_1));
  have polyH4 := Poly.volumeFinset polyH3 (fun (q_1 : Poly.FinPool fun (j_1 : J) => K) => r (Sigma.fst q_1) (Sigma.snd q_1));
  have polyH5 := Poly.volumeFunction (fun (j_1 : J) => r j_1) polyH2 polyH4;
  have polyH6 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH1 polyH5;
  have polyH7 := Poly.const (n) (2);
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _ (n j_12) ((U j_12, r j_12))))) polyH8;
  have polyH10 := Poly.add (ihp) (ihq);
  have polyH11 := Poly.const (n) (20);
  have polyH12 := Poly.volumeFinset polyH0 (fun (j_1 : J) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p);
  have polyH13 := Poly.add polyH6 polyH12;
  have polyH14 := Poly.volumeFinset polyH0 (fun (j_1 : J) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q);
  have polyH15 := Poly.add polyH13 polyH14;
  have polyH16 := Poly.const (n) (1);
  have polyH17 := Poly.add polyH15 polyH16;
  have polyH18 := Poly.mul polyH11 polyH17;
  have polyH19 := Poly.add polyH10 polyH18;
  have polyH20 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q) (@Uniform.evalTemplate K p) (@Uniform.evalTemplate K q) (n j_12) ((U j_12, r j_12))))) polyH19;
  have polyH21 := Poly.add polyH9 polyH20;
  have polyH22 := Poly.add polyH6 polyH1;
  have polyH23 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q)) polyH12 polyH14;
  have polyH24 := Poly.add polyH22 polyH23;
  have polyH25 := Poly.add polyH24 polyH16;
  have polyH26 := Poly.mul polyH11 polyH25;
  have polyH27 := Poly.add polyH21 polyH26;
  have polyH28 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (Universe) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q) (@Uniform.evalTemplate K p) (@Uniform.evalTemplate K q)) (n j_12) ((U j_12, r j_12))))) polyH27;
  have polyH29 := Poly.reparam (@Costs.setUnion) (fun (j_1 : J) => Sigma.mk (n j_1) (Prod.fst (U j_1, r j_1), OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q)) polyH0;
  have polyH30 := Poly.add polyH28 polyH29;
  have polyH31 := Poly.const (n) (10);
  have polyH32 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, r j_1), OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) q)) polyH1 polyH23;
  have polyH33 := Poly.add polyH32 polyH16;
  have polyH34 := Poly.mul polyH31 polyH33;
  have polyH35 := Poly.add polyH30 polyH34;
  have polyH36 := Poly.of_le (fun (j_12 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => Universe i × Finset (Fin i) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (Prod.fst x, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q)) (fun (n_1 : ℕ) (x : Universe n_1 × Finset (Fin n_1) × Finset (Fin n_1)) => Prod.fst (Prod.snd x) ∪ Prod.snd (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) Universe (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p, OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) q) (@Uniform.evalTemplate K p) (@Uniform.evalTemplate K q))) (Uniform.setUnion) (n j_12) ((U j_12, r j_12))))) polyH35;
  exact Poly.lift polyH36 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem evalTemplates (ps : List (Formula (Fin K))) :
    Poly n (fun j => (Uniform.evalTemplates ps).time (n j) (U j,r j)) 4 := by
  induction ps with
  | nil => (
  have polyH0 := Poly.const (n) (2);
  have polyH1 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_nil (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_7) ((U j_7, r j_7))))) polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  | cons p ps ih =>
    have hc := evalTemplate n U r p
    have hl : Poly n (fun j => (ps.map (Formula.evalFinset (r j))).length) 0 := by
      simpa only [List.length_map] using Poly.const n ps.length
    (
  have polyH0 := Poly.add (hc) (ih);
  have polyH1 := Poly.const (n) (20);
  have polyH2 := Poly.size (n);
  have polyH3 := Poly.volumeUniverse polyH2 (fun (j_1 : J) => U j_1);
  have polyH4 := Poly.const (n) (K);
  have polyH5 := Poly.size (fun (q : Poly.FinPool fun (j_1 : J) => K) => n (Sigma.fst q));
  have polyH6 := Poly.volumeFinset polyH5 (fun (q : Poly.FinPool fun (j_1 : J) => K) => r (Sigma.fst q) (Sigma.snd q));
  have polyH7 := Poly.volumeFunction (fun (j_1 : J) => r j_1) polyH4 polyH6;
  have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH3 polyH7;
  have polyH9 := Poly.volumeFinset polyH2 (fun (j_1 : J) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p);
  have polyH10 := Poly.add polyH8 polyH9;
  have polyH11 := Poly.size (fun (q : Poly.ListPool fun (j_1 : J) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1))) ps) => n (Sigma.fst q));
  have polyH12 := Poly.volumeFinset polyH11 (fun (q : Poly.ListPool fun (j_1 : J) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1))) ps) => (Sigma.snd q).1);
  have polyH13 := Poly.listVolume (fun (j_1 : J) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1))) ps) (hl) polyH12;
  have polyH14 := Poly.add polyH10 polyH13;
  have polyH15 := Poly.const (n) (1);
  have polyH16 := Poly.add polyH14 polyH15;
  have polyH17 := Poly.mul polyH1 polyH16;
  have polyH18 := Poly.add polyH0 polyH17;
  have polyH19 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x)) ps) (@Uniform.evalTemplate K p) (@Uniform.evalTemplates K ps) (n j_13) ((U j_13, r j_13))))) polyH18;
  have polyH20 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1)) p, List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_1, r j_1))) ps)) polyH9 polyH13;
  have polyH21 := Poly.const (n) (2);
  have polyH22 := Poly.add polyH20 polyH21;
  have polyH23 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_cons (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (n j_13) ((OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_13, r j_13)) p, List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd (U j_13, r j_13))) ps))))) polyH22;
  have polyH24 := Poly.add polyH19 polyH23;
  have polyH25 := Poly.const (n) (10);
  have polyH26 := Poly.add polyH20 polyH15;
  have polyH27 := Poly.mul polyH25 polyH26;
  have polyH28 := Poly.add polyH24 polyH27;
  have polyH29 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (i : ℕ) => Finset (Fin i) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin K → Finset (Fin i))) => (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p, List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x)) ps)) (fun (i : ℕ) (x : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x :: Prod.snd x) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin K → Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x) p) (fun (n_1 : ℕ) (x : Universe n_1 × (Fin K → Finset (Fin n_1))) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x)) ps) (@Uniform.evalTemplate K p) (@Uniform.evalTemplates K ps)) (@Uniform.cons ℕ (fun (i : ℕ) => Finset (Fin i)) _) (n j_13) ((U j_13, r j_13))))) polyH28;
  exact Poly.lift polyH29 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type}

theorem evalTemplatesCanonical {K : ℕ} (ps : List (Formula (Fin K))) :
    Poly (fun x : Σ n, Universe n × (Fin K → Finset (Fin n)) => x.1)
      (fun x => (Uniform.evalTemplates ps).time x.1 x.2) 4 :=
  evalTemplates (fun x : Σ n, Universe n × (Fin K → Finset (Fin n)) => x.1) (fun x => x.2.1) (fun x => x.2.2) ps

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

theorem time_family (K n : ℕ) (x : Universe n × Matrix n) :
    (family K).time n x = (((familyAssignments K).pair fst).comp (familyFlatten K)).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem familyEval (K : ℕ) : Poly (fun x : Σ n, (Fin K → Finset (Fin n)) × Universe n => x.1)
    (fun x => (Uniform.familyEval K).time x.1 x.2) 4 := by
  (
  have polyH0 := Poly.const (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1) (K);
  have polyH1 := Poly.size (fun (q : Poly.FinPool fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => K) => (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => K) => (Sigma.fst q).2.1 (Sigma.snd q));
  have polyH3 := Poly.volumeFunction (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => x_1.2.1) polyH0 polyH2;
  have polyH4 := Poly.size (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1);
  have polyH5 := Poly.volumeUniverse polyH4 (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => x_1.2.2);
  have polyH6 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => x_1.2) polyH3 polyH5;
  have polyH7 := Poly.const (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1) (2);
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.of_le (fun (x_3 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin K → Finset (Fin i)) (Universe) _ _ (Sigma.fst x_3) (Sigma.snd x_3)))) polyH8;
  have polyH10 := Poly.of_le (fun (x_3 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin K → Finset (Fin i)) (Universe) _ _ (Sigma.fst x_3) (Sigma.snd x_3)))) polyH8;
  have polyH11 := Poly.add polyH9 polyH10;
  have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1) (20);
  have polyH13 := Poly.volumeUniverse polyH4 (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (Sigma.snd x_1).2);
  have polyH14 := Poly.add polyH6 polyH13;
  have polyH15 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => K) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q));
  have polyH16 := Poly.volumeFunction (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (Sigma.snd x_1).1) polyH0 polyH15;
  have polyH17 := Poly.add polyH14 polyH16;
  have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1) (1);
  have polyH19 := Poly.add polyH17 polyH18;
  have polyH20 := Poly.mul polyH12 polyH19;
  have polyH21 := Poly.add polyH11 polyH20;
  have polyH22 := Poly.of_le (fun (x_3 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Fin K → Finset (Fin i_1)) i × Universe i) (Universe) (fun (i : ℕ) => Fin K → Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin K → Finset (Fin i)) Universe _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin K → Finset (Fin i)) Universe _ _) (Sigma.fst x_3) (Sigma.snd x_3)))) polyH21;
  have polyH23 := Poly.reparam (@Costs.evalTemplatesCanonical (K) (OAI.ThreeMachine.Structure.Formula.templates K)) (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.mk (Sigma.fst x_1) (Prod.snd (Sigma.snd x_1), Prod.fst (Sigma.snd x_1))) polyH4;
  have polyH24 := Poly.add polyH22 polyH23;
  have polyH25 := Poly.const (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => Sigma.fst x_1) (10);
  have polyH26 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (Prod.snd (Sigma.snd x_1), Prod.fst (Sigma.snd x_1))) polyH13 polyH16;
  have polyH27 := Poly.add polyH26 polyH18;
  have polyH28 := Poly.mul polyH25 polyH27;
  have polyH29 := Poly.add polyH24 polyH28;
  have polyH30 := Poly.of_le (fun (x_3 : (n : ℕ) × (Fin K → Finset (Fin n)) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin K → Finset (Fin i)) × Universe i) (fun (i : ℕ) => Universe i × (Fin K → Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : (Fin K → Finset (Fin i)) × Universe i) => (Prod.snd x_1, Prod.fst x_1)) (fun (n : ℕ) (x_1 : Universe n × (Fin K → Finset (Fin n))) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x_1)) (OAI.ThreeMachine.Structure.Formula.templates K)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin K → Finset (Fin i)) Universe _ _) (@Uniform.evalTemplates K (OAI.ThreeMachine.Structure.Formula.templates K)) (Sigma.fst x_3) (Sigma.snd x_3)))) polyH29;
  exact Poly.lift polyH30 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem familyFlatten {J : Type} (K : ℕ) (n : J → ℕ) (U : ∀ j, Universe (n j))
    (xs : ∀ j, List (Fin K → Finset (Fin (n j))))
    (hl : Poly n (fun j => (xs j).length) 30000) :
    Poly n (fun j => (Uniform.familyFlatten K).time (n j) (xs j,U j)) 60004 := by
  let P := Σ j, {a : Fin K → Finset (Fin (n j)) // a ∈ xs j}
  let sp (p : P) := n p.1
  have ht : Poly sp (fun p => (Uniform.familyEval K).time (n p.1) (p.2.1,U p.1)) 4 := by
    exact (familyEval K).precomp (fun p : P => (⟨n p.1,(p.2.1,U p.1)⟩ : Σ m, (Fin K → Finset (Fin m)) × Universe m))
  have hx : Poly n (fun j => volume (xs j)) 30002 := by (
  have polyH0 := Poly.const (fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => n (Sigma.fst q)) (K);
  have polyH1 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => K) => (fun (q_1 : Poly.ListPool fun (j_1 : J) => xs j_1) => n (Sigma.fst q_1)) (Sigma.fst q));
  have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => K) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q));
  have polyH3 := Poly.volumeFunction (fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => (Sigma.snd q).1) polyH0 polyH2;
  have polyH4 := Poly.listVolume (fun (j_1 : J) => xs j_1) (hl) polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have he : Poly n (fun j => volume (U j)) 2 := by (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hlout : Poly sp (fun p => ((Formula.templates K).map (Formula.evalFinset p.2.1)).length) 0 := by
    simpa only [List.length_map] using Poly.const sp (Formula.templates K).length
  have hv : Poly sp (fun p => volume ((Formula.templates K).map (Formula.evalFinset p.2.1))) 2 := by
    (
  have polyH0 := Poly.size (fun (q : Poly.ListPool fun (p_1 : P) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Subtype.val (Sigma.snd p_1))) (OAI.ThreeMachine.Structure.Formula.templates K)) => sp (Sigma.fst q));
  have polyH1 := Poly.volumeFinset polyH0 (fun (q : Poly.ListPool fun (p_1 : P) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Subtype.val (Sigma.snd p_1))) (OAI.ThreeMachine.Structure.Formula.templates K)) => (Sigma.snd q).1);
  have polyH2 := Poly.listVolume (fun (p_1 : P) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Subtype.val (Sigma.snd p_1))) (OAI.ThreeMachine.Structure.Formula.templates K)) (hlout) polyH1;
  exact Poly.lift polyH2 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  exact (Poly.flatMapTime (α := fun n => Fin K → Finset (Fin n)) n xs U (Uniform.familyEval K) hl ht hx he hv).lift (by decide)

theorem familyBound (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.family K).time x.1 x.2) 90010 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let xs (x : Σ n, Universe n × Matrix n) :=
    (Atomic.alphabet (List.finRange x.1)).map
      (Atomic.finsetEval (matrixRel x.2.2) (Structure.jobRank (matrixRel x.2.2)) (Structure.reverseJobRank (matrixRel x.2.2)))
  have hl : Poly n (fun x => (xs x).length) 3 := by
    simpa only [xs,List.length_map] using Poly.lengthAlphabet (Poly.size n)
  have hAL : Poly n (fun x => (Structure.assignments (xs x) K).length) 30000 := by
    simpa only [Structure.assignments_length] using (hl.pow K).lift (Nat.mul_le_mul_left 3 hk)
  have hAV : Poly n (fun x => volume (Structure.assignments (xs x) K)) 30002 := by (
  have polyH0 := Poly.const (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => n (Sigma.fst q)) (K);
  have polyH1 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => K) => (fun (q_1 : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => n (Sigma.fst q_1)) (Sigma.fst q));
  have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => K) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q));
  have polyH3 := Poly.volumeFunction (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => (Sigma.snd q).1) polyH0 polyH2;
  have polyH4 := Poly.listVolume (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) (hAL) polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hA := (familyAssignments K).lift (show max (max 100 (9*K+10)) 5 ≤ 90010 by omega)
  have hF := familyFlatten K n (fun x => x.2.1) (fun x => Structure.assignments (xs x) K) hAL
  (
  have polyH0 := Poly.size (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_11 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_11) (Sigma.snd x_11)))) polyH5;
  have polyH7 := Poly.add (hA) polyH6;
  have polyH8 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (20);
  have polyH9 := Poly.add polyH3 (hAV);
  have polyH10 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Sigma.snd x_1).1);
  have polyH11 := Poly.add polyH9 polyH10;
  have polyH12 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (1);
  have polyH13 := Poly.add polyH11 polyH12;
  have polyH14 := Poly.mul polyH8 polyH13;
  have polyH15 := Poly.add polyH7 polyH14;
  have polyH16 := Poly.of_le (fun (x_11 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => List (Fin K → Finset (Fin i))) (Universe) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (xs_1 : List (Finset (Fin i))) => OAI.ThreeMachine.Structure.assignments xs_1 K) ((fun (x_2 : Universe i × Matrix i) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd x_2)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange i))) x_1)) (fun (i : ℕ) => Prod.fst) (Uniform.familyAssignments K) (@Uniform.fst ℕ Universe Matrix _ _) (Sigma.fst x_11) (Sigma.snd x_11)))) polyH15;
  have polyH17 := Poly.add polyH16 (hF);
  have polyH18 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (10);
  have polyH19 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => ((fun (xs_1 : List (Finset (Fin (Sigma.fst x_1)))) => OAI.ThreeMachine.Structure.assignments xs_1 K) ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd x_2)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange (Sigma.fst x_1)))) (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) (hAV) polyH10;
  have polyH20 := Poly.add polyH19 polyH12;
  have polyH21 := Poly.mul polyH18 polyH20;
  have polyH22 := Poly.add polyH17 polyH21;
  have polyH23 := Poly.of_le (fun (x_11 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => List (Fin K → Finset (Fin i)) × Universe i) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (xs_1 : List (Finset (Fin i))) => OAI.ThreeMachine.Structure.assignments xs_1 K) ((fun (x_2 : Universe i × Matrix i) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd x_2)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange i))) x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : List (Fin K → Finset (Fin i)) × Universe i) => List.flatMap (fun (a : Fin K → Finset (Fin i)) => (fun (x_2 : Universe i × (Fin K → Finset (Fin i))) => List.map (OAI.ThreeMachine.Structure.Formula.evalFinset (Prod.snd x_2)) (OAI.ThreeMachine.Structure.Formula.templates K)) ((fun (x_2 : (Fin K → Finset (Fin i)) × Universe i) => (Prod.snd x_2, Prod.fst x_2)) (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (i : ℕ) => List (Fin K → Finset (Fin i))) Universe _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (xs_1 : List (Finset (Fin i))) => OAI.ThreeMachine.Structure.assignments xs_1 K) ((fun (x_2 : Universe i × Matrix i) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd x_2)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange i))) x_1)) (fun (i : ℕ) => Prod.fst) (Uniform.familyAssignments K) (@Uniform.fst ℕ Universe Matrix _ _)) (Uniform.familyFlatten K) (Sigma.fst x_11) (Sigma.snd x_11)))) polyH22;
  have polyH24 := Poly.of_le (fun (x_11 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_family (K) (Sigma.fst x_11) (Sigma.snd x_11)))) polyH23;
  exact Poly.lift polyH24 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section

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

theorem layers
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.layers.time (n j) (n j,(U j,(M j,(fs j,zs j))))) 150010 := by
  let e j : Uniform.LayerEnv (n j) := (U j,(M j,(fs j,zs j)))
  let a j : Uniform.LayerEnv (n j) × Table (n j) := (e j,[(∅,Algorithm.Block.empty)])
  have hlen : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => (Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1).length) 30000 := by
    apply Poly.of_le (fun p : Poly.IterPool n => Algorithm.layers_length _ _ _ _)
    have hf' := hf.precomp (fun p : Poly.IterPool n => p.1)
    (
  have polyH0 := Poly.const (fun (p_1 : Poly.IterPool n) => n (Sigma.fst p_1)) (1);
  have polyH1 := Poly.add (hf') polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have ht := layerStep (fun p : Poly.IterPool n => n p.1) (fun p => U p.1) (fun p => M p.1)
    (fun p => Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1)
    (fun p => fs p.1) (fun p => zs p.1) hlen (hf.precomp Sigma.fst) (hz.precomp Sigma.fst)
    (fun p => Algorithm.layers_good _ _ _ _) (fun p => Algorithm.layers_bounded _ _ _ _)
  have hvTab := Poly.volumeTable _ ((Poly.size n).precomp (fun p : Poly.IterPool n => p.1)) hlen
    (fun p => layers_small _ _ _ _)
  have hfV := Poly.volumeSetList fs (Poly.size n) hf
  have hzV := Poly.volumeSetList zs (Poly.size n) hz
  have hti : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => Uniform.layerStep.time (n p.1)
        ((Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1))) 150009 := by
    convert ht using 1
    funext p
    rw [show (Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1) =
      (e p.1,Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1) from layerStep_iterate (e p.1) p.2.1]
  have hvi : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => volume ((Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1))) 30002 := by
    have hf' := hfV.precomp (fun p : Poly.IterPool n => p.1)
    have hz' := hzV.precomp (fun p : Poly.IterPool n => p.1)
    have hn' := (Poly.size n).precomp (fun p : Poly.IterPool n => p.1)
    simp only [show ∀ p : Poly.IterPool n, (Uniform.eval Uniform.layerStep (n p.1))^[p.2.1] (a p.1) =
      (e p.1,Algorithm.layers (matrixRel (M p.1)) (fs p.1) (zs p.1) p.2.1) from fun p => layerStep_iterate (e p.1) p.2.1]
    dsimp only [e]
    (
  have polyH0 := Poly.volumeUniverse (hn') (fun (p_1 : Poly.IterPool n) => U (Sigma.fst p_1));
  have polyH1 := Poly.volumeMatrix (hn') (fun (p_1 : Poly.IterPool n) => M (Sigma.fst p_1));
  have polyH2 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (fs (Sigma.fst p_1), zs (Sigma.fst p_1))) (hf') (hz');
  have polyH3 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (M (Sigma.fst p_1), fs (Sigma.fst p_1), zs (Sigma.fst p_1))) polyH1 polyH2;
  have polyH4 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (U (Sigma.fst p_1), M (Sigma.fst p_1), fs (Sigma.fst p_1), zs (Sigma.fst p_1))) polyH0 polyH3;
  have polyH5 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => ((U (Sigma.fst p_1), M (Sigma.fst p_1), fs (Sigma.fst p_1), zs (Sigma.fst p_1)), OAI.ThreeMachine.Algorithm.layers (matrixRel (M (Sigma.fst p_1))) (fs (Sigma.fst p_1)) (zs (Sigma.fst p_1)) (Fin.val (Sigma.snd p_1)))) polyH4 (hvTab);
  exact Poly.lift polyH5 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hInitV := Poly.volumeTable (fun j => ([(∅,Algorithm.Block.empty)] : Table (n j)))
    (Poly.size n) (Poly.const n 1) (fun j => layers_small (matrixRel (M j)) (fs j) (zs j) 0)
  have hIter := Poly.iterateTime Uniform.layerStep n n a (Poly.size n) hti hvi
  have hFinalV := hvTab.precomp (fun j => ⟨j,⟨n j,by omega⟩⟩)
  dsimp only [a, e] at hIter
  simp only [Uniform.layers, Uniform.time_congr, Uniform.time_comp, Uniform.time_pair,
    Uniform.time_fst, Uniform.time_snd, Function.comp_apply]
  simp only [layerStep_iterate]
  (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeNat polyH0;
  have polyH2 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH3 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1)) (hfV) (hzV);
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1)) polyH3 polyH4;
  have polyH6 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1)) polyH2 polyH5;
  have polyH7 := Poly.volumeProd (fun (j_1 : J) => (n j_1, U j_1, M j_1, fs j_1, zs j_1)) polyH1 polyH6;
  have polyH8 := Poly.const (n) (2);
  have polyH9 := Poly.add polyH7 polyH8;
  have polyH10 := Poly.add polyH6 polyH8;
  have polyH11 := Poly.add polyH9 polyH10;
  have polyH12 := Poly.const (n) (10);
  have polyH13 := Poly.const (n) (1);
  have polyH14 := Poly.add polyH6 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_setEmpty (n j_22) (U j_22)))) polyH8;
  have polyH18 := Poly.reparam (@Costs.blockEmpty) (fun (j_1 : J) => Sigma.mk (n j_1) (U j_1)) polyH0;
  have polyH19 := Poly.add polyH17 polyH18;
  have polyH20 := Poly.const (n) (20);
  have polyH21 := Poly.volumeFinset polyH0 (fun (j_1 : J) => ∅);
  have polyH22 := Poly.add polyH2 polyH21;
  have polyH23 := Poly.const (n) (0);
  have polyH24 := Poly.const (fun (q : Poly.FinPool fun (j_1 : J) => n j_1) => n (Sigma.fst q)) (0);
  have polyH25 := Poly.volumeNat polyH24;
  have polyH26 := Poly.volumeFunction (fun (j_1 : J) (x : Fin (n j_1)) => 0) polyH0 polyH25;
  have polyH27 := Poly.volumeBlock (fun (j_1 : J) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_1)) => 0) polyH23 polyH26;
  have polyH28 := Poly.add polyH22 polyH27;
  have polyH29 := Poly.add polyH28 polyH13;
  have polyH30 := Poly.mul polyH20 polyH29;
  have polyH31 := Poly.add polyH19 polyH30;
  have polyH32 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => ∅) (fun (n_1 : ℕ) (x : Universe n_1) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin n_1) => 0) (Uniform.setEmpty) (Uniform.blockEmpty) (n j_22) (U j_22)))) polyH31;
  have polyH33 := Poly.volumeProd (fun (j_1 : J) => (∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_1)) => 0)) polyH21 polyH27;
  have polyH34 := Poly.add polyH33 polyH8;
  have polyH35 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ (n j_22) ((∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_22)) => 0))))) polyH34;
  have polyH36 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_nil (ℕ) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _ (n j_22) ((∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_22)) => 0))))) polyH8;
  have polyH37 := Poly.add polyH35 polyH36;
  have polyH38 := Poly.add polyH33 polyH33;
  have polyH39 := Poly.add polyH38 polyH13;
  have polyH40 := Poly.add polyH39 polyH13;
  have polyH41 := Poly.mul polyH20 polyH40;
  have polyH42 := Poly.add polyH37 polyH41;
  have polyH43 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => x) (fun (i : ℕ) (x : Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => @List.nil ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (@Uniform.id ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (@Uniform.nil ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _) (n j_22) ((∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_22)) => 0))))) polyH42;
  have polyH44 := Poly.volumeProd (fun (j_1 : J) => ((∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_1)) => 0), @List.nil ((fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (n j_1)))) polyH33 polyH13;
  have polyH45 := Poly.add polyH44 polyH8;
  have polyH46 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_cons (ℕ) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ (n j_22) (((∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_22)) => 0), @List.nil ((fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (n j_22))))))) polyH45;
  have polyH47 := Poly.add polyH43 polyH46;
  have polyH48 := Poly.add polyH44 polyH13;
  have polyH49 := Poly.mul polyH12 polyH48;
  have polyH50 := Poly.add polyH47 polyH49;
  have polyH51 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => (x, @List.nil ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i))) (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) => Prod.fst x :: Prod.snd x) (@Uniform.pair ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => x) (fun (i : ℕ) (x : Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => @List.nil ((fun (i_1 : ℕ) => Finset (Fin i_1) × OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (@Uniform.id ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (@Uniform.nil ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _ _)) (@Uniform.cons ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (n j_22) ((∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_22)) => 0))))) polyH50;
  have polyH52 := Poly.add polyH32 polyH51;
  have polyH53 := Poly.add polyH33 polyH13;
  have polyH54 := Poly.mul polyH12 polyH53;
  have polyH55 := Poly.add polyH52 polyH54;
  have polyH56 := Poly.of_le (fun (j_22 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : Universe i) => (∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin i) => 0)) (fun (i : ℕ) (a_1 : Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => a_1 :: @List.nil (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (@Uniform.pair ℕ Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => ∅) (fun (n_1 : ℕ) (x : Universe n_1) => OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x_1 : Fin n_1) => 0) Uniform.setEmpty Uniform.blockEmpty) (@Uniform.singleton ℕ (fun (i : ℕ) => Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (n j_22) (U j_22)))) polyH55;
  have polyH57 := Poly.add polyH16 polyH56;
  have polyH58 := Poly.add polyH2 polyH13;
  have polyH59 := Poly.mul polyH12 polyH58;
  have polyH60 := Poly.add polyH57 polyH59;
  have polyH61 := Poly.add polyH9 polyH60;
  have polyH62 := Poly.add polyH7 polyH6;
  have polyH63 := Poly.add polyH62 (hInitV);
  have polyH64 := Poly.add polyH63 polyH13;
  have polyH65 := Poly.mul polyH20 polyH64;
  have polyH66 := Poly.add polyH61 polyH65;
  have polyH67 := Poly.add polyH9 polyH66;
  have polyH68 := Poly.add polyH7 polyH1;
  have polyH69 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1, fs j_1, zs j_1), (∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_1)) => 0) :: @List.nil (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))))) polyH6 (hInitV);
  have polyH70 := Poly.add polyH68 polyH69;
  have polyH71 := Poly.add polyH70 polyH13;
  have polyH72 := Poly.mul polyH20 polyH71;
  have polyH73 := Poly.add polyH67 polyH72;
  have polyH74 := Poly.add polyH73 (hIter);
  have polyH75 := Poly.volumeProd (fun (j_1 : J) => (n j_1, (U j_1, M j_1, fs j_1, zs j_1), (∅, OAI.ThreeMachine.Algorithm.Block.mk (0) fun (x : Fin (n j_1)) => 0) :: @List.nil (Finset (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))))) polyH1 polyH69;
  have polyH76 := Poly.add polyH75 polyH13;
  have polyH77 := Poly.mul polyH12 polyH76;
  have polyH78 := Poly.add polyH74 polyH77;
  have polyH79 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, M j_1, fs j_1, zs j_1), OAI.ThreeMachine.Algorithm.layers (matrixRel (M j_1)) (fs j_1) (zs j_1) (n j_1))) polyH6 (hFinalV);
  have polyH80 := Poly.add polyH79 polyH8;
  have polyH81 := Poly.add polyH78 polyH80;
  have polyH82 := Poly.add polyH79 polyH13;
  have polyH83 := Poly.mul polyH12 polyH82;
  have polyH84 := Poly.add polyH81 polyH83;
  exact Poly.lift polyH84 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
theorem fullLayers (K : ℕ) (hk : K ≤ 10000) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.fullLayers K).time x.1 x.2) 150010 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let fs (x : Σ n, Universe n × Matrix n) := effectiveFamily (matrixRel x.2.2)
    (jobRank (matrixRel x.2.2)) (reverseJobRank (matrixRel x.2.2)) (List.finRange x.1) K
  let zs (x : Σ n, Universe n × Matrix n) := (tripleList (List.finRange x.1)).map Subtype.val
  have hf : Poly n (fun x => (fs x).length) 30000 :=
    (Poly.lengthFamily (s := n) (n := n) (d := 1) (fun x : Σ n, Universe n × Matrix n => x.2.2) K (Poly.size n)).lift (by omega)
  have hz : Poly n (fun x => (zs x).length) 3 := by
    simpa only [zs,List.length_map] using Poly.lengthTriples (Poly.size n)
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have hF := familyBound K hk
  have hL := layers n (fun x => x.2.1) (fun x => x.2.2) fs zs hf hz
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
  have polyH9 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (100000);
  have polyH10 := Poly.lengthFinRange polyH0;
  have polyH11 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (1);
  have polyH12 := Poly.add polyH10 polyH11;
  have polyH13 := Poly.mul polyH9 polyH12;
  have polyH14 := Poly.volumeFinRange polyH0;
  have polyH15 := Poly.add polyH14 polyH11;
  have polyH16 := Poly.mul polyH13 polyH15;
  have polyH17 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (@Uniform.time_length_le (ℕ) (Fin) _ (Sigma.fst x_13) (List.finRange (Sigma.fst x_13)))) polyH16;
  have polyH18 := Poly.add polyH8 polyH17;
  have polyH19 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (10);
  have polyH20 := Poly.mul polyH19 polyH15;
  have polyH21 := Poly.add polyH18 polyH20;
  have polyH22 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.finRange n_1) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (Sigma.fst x_13) (Prod.fst (Sigma.snd x_13))))) polyH21;
  have polyH23 := Poly.add polyH6 polyH22;
  have polyH24 := Poly.add polyH7 polyH11;
  have polyH25 := Poly.mul polyH19 polyH24;
  have polyH26 := Poly.add polyH23 polyH25;
  have polyH27 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => n_1) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.universeNumber) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH26;
  have polyH28 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_13) (Sigma.snd x_13)))) polyH5;
  have polyH29 := Poly.reparam (@Costs.triples) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.mk (Sigma.fst x_1) (Prod.fst (Sigma.snd x_1))) polyH0;
  have polyH30 := Poly.add polyH6 polyH29;
  have polyH31 := Poly.add polyH30 polyH25;
  have polyH32 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.triples) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH31;
  have polyH33 := Poly.add (hF) polyH32;
  have polyH34 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (20);
  have polyH35 := Poly.add polyH3 (hfv);
  have polyH36 := Poly.add polyH35 (hzv);
  have polyH37 := Poly.add polyH36 polyH11;
  have polyH38 := Poly.mul polyH34 polyH37;
  have polyH39 := Poly.add polyH33 polyH38;
  have polyH40 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1)) (Uniform.family K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.triples) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH39;
  have polyH41 := Poly.add polyH28 polyH40;
  have polyH42 := Poly.volumeMatrix polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Sigma.snd x_1).2);
  have polyH43 := Poly.add polyH3 polyH42;
  have polyH44 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (List.finRange (Sigma.fst x_1)) K, (fun (x_2 : Universe (Sigma.fst x_1)) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1)))) (Prod.fst (Sigma.snd x_1)))) (hfv) (hzv);
  have polyH45 := Poly.add polyH43 polyH44;
  have polyH46 := Poly.add polyH45 polyH11;
  have polyH47 := Poly.mul polyH34 polyH46;
  have polyH48 := Poly.add polyH41 polyH47;
  have polyH49 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.snd ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1)) (Uniform.family K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.triples)) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH48;
  have polyH50 := Poly.add polyH6 polyH49;
  have polyH51 := Poly.add polyH3 polyH7;
  have polyH52 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Prod.snd (Sigma.snd x_1), OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (List.finRange (Sigma.fst x_1)) K, (fun (x_2 : Universe (Sigma.fst x_1)) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1)))) (Prod.fst (Sigma.snd x_1)))) polyH42 polyH44;
  have polyH53 := Poly.add polyH51 polyH52;
  have polyH54 := Poly.add polyH53 polyH11;
  have polyH55 := Poly.mul polyH34 polyH54;
  have polyH56 := Poly.add polyH50 polyH55;
  have polyH57 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.snd x_1, OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.snd ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1)) (Uniform.family K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.triples))) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH56;
  have polyH58 := Poly.add polyH27 polyH57;
  have polyH59 := Poly.volumeNat polyH0;
  have polyH60 := Poly.add polyH3 polyH59;
  have polyH61 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Prod.fst (Sigma.snd x_1), Prod.snd (Sigma.snd x_1), OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (List.finRange (Sigma.fst x_1)) K, (fun (x_2 : Universe (Sigma.fst x_1)) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1)))) (Prod.fst (Sigma.snd x_1)))) polyH7 polyH52;
  have polyH62 := Poly.add polyH60 polyH61;
  have polyH63 := Poly.add polyH62 polyH11;
  have polyH64 := Poly.mul polyH34 polyH63;
  have polyH65 := Poly.add polyH58 polyH64;
  have polyH66 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => i) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, Prod.snd x_1, OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => n_1) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeNumber) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.snd x_1, OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.snd ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1)) (Uniform.family K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.triples)))) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH65;
  have polyH67 := Poly.add polyH66 (hL);
  have polyH68 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => ((fun (x_2 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1), Prod.snd (Sigma.snd x_1), OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (List.finRange (Sigma.fst x_1)) K, (fun (x_2 : Universe (Sigma.fst x_1)) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1)))) (Prod.fst (Sigma.snd x_1)))) polyH59 polyH61;
  have polyH69 := Poly.add polyH68 polyH11;
  have polyH70 := Poly.mul polyH19 polyH69;
  have polyH71 := Poly.add polyH67 polyH70;
  have polyH72 := Poly.of_le (fun (x_13 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => ℕ × Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) (fun (n_1 : ℕ) => List (Finset (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (x_2 : Universe i) => i) (Prod.fst x_1), Prod.fst x_1, Prod.snd x_1, OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (fun (n_1 : ℕ) (x_1 : ℕ × Universe n_1 × Matrix n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1))) => OAI.ThreeMachine.Algorithm.layers (matrixRel (Prod.fst (Prod.snd (Prod.snd x_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1)))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd x_1)))) (Prod.fst x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => i) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, Prod.snd x_1, OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => n_1) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeNumber) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.snd x_1, OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange i) K, (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1))) (@Uniform.snd ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.effectiveFamily (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1))) (List.finRange n_1) K) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : Universe i) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i))) (Prod.fst x_1)) (Uniform.family K) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange n_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.triples))))) (Uniform.layers) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH71;
  exact Poly.lift polyH72 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

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

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.fullLayers := @OAI.ThreeMachine.StackCompiler.Costs.fullLayers
