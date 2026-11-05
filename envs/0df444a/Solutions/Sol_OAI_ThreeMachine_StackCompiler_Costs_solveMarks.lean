-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.solveMarks
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:42:10.479209+00:00
-- url     : https://prove2.me/submissions/f5a0abc7-f7e4-4522-b713-06b7e8234bc0

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_statesC
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_statesP
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_markingsStep

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
  (have polyH0 := Poly.const (s) (100000); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hl) polyH1; have polyH3 := Poly.mul polyH0 polyH2; have polyH4 := Poly.add (hT) (hx); have polyH5 := Poly.add polyH4 (he); have polyH6 := Poly.add polyH5 polyH1; have polyH7 := Poly.mul polyH3 polyH6; exact Poly.lift polyH7 (by first | decide +kernel | omega))

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
  (have polyH0 := Poly.const (s) (100000); have polyH1 := Poly.add (hl) (hf); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.mul polyH0 polyH3; have polyH5 := Poly.add (hT) (hx); have polyH6 := Poly.add polyH5 (he); have polyH7 := Poly.add polyH6 (hm); have polyH8 := Poly.add polyH7 polyH2; have polyH9 := Poly.mul polyH4 polyH8; exact Poly.lift polyH9 (by first | decide +kernel | omega))

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

namespace Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

theorem volumeSmallLookup {K : J → Type} [∀ j, Coding (K j)] [∀ j, DecidableEq (K j)]
    (xs : ∀ j, List (K j × Block (Fin (n j)))) (k : ∀ j, K j)
    (hn : Poly s n d) (hb : ∀ j a b, (a,b) ∈ xs j → BlockSmall b) :
    Poly s (fun j => volume (Algorithm.lookup (xs j) (k j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by (have polyH0 := Poly.const (s) (10); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega)))
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
theorem volumeStateList (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (sts j).length) l) :
    Poly s (fun j => volume (sts j)) (l+2*d) := by
  apply volumeList hl (show Poly s (fun j => 12*(n j+1)^2) (2*d) from by (have polyH0 := Poly.const (s) (12); have polyH1 := Poly.const (s) (1); have polyH2 := Poly.add (hn) polyH1; have polyH3 := Poly.pow polyH2 (2); have polyH4 := Poly.mul polyH0 polyH3; exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j a _ha
  exact volume_state_le a

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

theorem time_states (n : ℕ) (x : StatesInput n) :
    states.time n x =
    ((statesS.pair (fst.pair ((snd.comp fst).pair statesW))).comp statesP.filter).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))
theorem statesPairs
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.statesPairs.time (n j) (U j,(M j,(fs j,(zs j,W j))))) 60020 := by
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH6; have polyH8 := Poly.const (n) (2); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_13) ((U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH9; have polyH11 := Poly.add polyH6 polyH8; have polyH12 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_13) (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH11; have polyH13 := Poly.add polyH5 polyH8; have polyH14 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_13) (Prod.snd (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13)))))) polyH13; have polyH15 := Poly.add polyH12 polyH14; have polyH16 := Poly.const (n) (10); have polyH17 := Poly.const (n) (1); have polyH18 := Poly.add polyH5 polyH17; have polyH19 := Poly.mul polyH16 polyH18; have polyH20 := Poly.add polyH15 polyH19; have polyH21 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _) (n j_13) (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH20; have polyH22 := Poly.add polyH10 polyH21; have polyH23 := Poly.add polyH6 polyH17; have polyH24 := Poly.mul polyH16 polyH23; have polyH25 := Poly.add polyH22 polyH24; have polyH26 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _)) (n j_13) ((U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH25; have polyH27 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_13) (Prod.snd (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13)))))) polyH13; have polyH28 := Poly.add polyH4 polyH8; have polyH29 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_13) (Prod.snd (Prod.snd (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13))))))) polyH28; have polyH30 := Poly.add polyH27 polyH29; have polyH31 := Poly.add polyH4 polyH17; have polyH32 := Poly.mul polyH16 polyH31; have polyH33 := Poly.add polyH30 polyH32; have polyH34 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n j_13) (Prod.snd (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13)))))) polyH33; have polyH35 := Poly.add polyH12 polyH34; have polyH36 := Poly.add polyH35 polyH19; have polyH37 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)) (n j_13) (Prod.snd (U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH36; have polyH38 := Poly.add polyH10 polyH37; have polyH39 := Poly.add polyH38 polyH24; have polyH40 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _))) (n j_13) ((U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH39; have polyH41 := Poly.add polyH26 polyH40; have polyH42 := Poly.const (n) (20); have polyH43 := Poly.add polyH7 (hfv); have polyH44 := Poly.add polyH43 (hzv); have polyH45 := Poly.add polyH44 polyH17; have polyH46 := Poly.mul polyH42 polyH45; have polyH47 := Poly.add polyH41 polyH46; have polyH48 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.StatesInput) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Uniform.statesF) (Uniform.statesZ) (n j_13) ((U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH47; have polyH49 := Poly.size (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)); have polyH50 := Poly.volumeFinset polyH49 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (Sigma.snd q).1); have polyH51 := Poly.precomp (hzv) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Sigma.fst q); have polyH52 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))) polyH50 polyH51; have polyH53 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) (2); have polyH54 := Poly.add polyH52 polyH53; have polyH55 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) polyH54; have polyH56 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) polyH54; have polyH57 := Poly.add polyH55 polyH56; have polyH58 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) (20); have polyH59 := Poly.add polyH52 polyH51; have polyH60 := Poly.add polyH59 polyH50; have polyH61 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) (1); have polyH62 := Poly.add polyH60 polyH61; have polyH63 := Poly.mul polyH58 polyH62; have polyH64 := Poly.add polyH57 polyH63; have polyH65 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) polyH64; have polyH66 := Poly.precomp (hz) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Sigma.fst q); have polyH67 := Poly.size (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH68 := Poly.volumeFinset polyH67 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (Sigma.snd q).1); have polyH69 := Poly.volumePool (fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (hfv); have polyH70 := Poly.precomp polyH69 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => Sigma.fst q); have polyH71 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))))))))) polyH68 polyH70; have polyH72 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) (Sigma.fst q)) (2); have polyH73 := Poly.add polyH71 polyH72; have polyH74 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1))))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1))))))))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (n (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))))))))) polyH73; have polyH75 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1))))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1))))))))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (n (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))))))))) polyH73; have polyH76 := Poly.add polyH74 polyH75; have polyH77 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) (Sigma.fst q)) (20); have polyH78 := Poly.add polyH71 polyH70; have polyH79 := Poly.add polyH78 polyH68; have polyH80 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) (Sigma.fst q)) (1); have polyH81 := Poly.add polyH79 polyH80; have polyH82 := Poly.mul polyH77 polyH81; have polyH83 := Poly.add polyH76 polyH82; have polyH84 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1))))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q_1), M (Sigma.fst q_1), fs (Sigma.fst q_1), zs (Sigma.fst q_1), W (Sigma.fst q_1))))))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (n (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))))))))) polyH83; have polyH85 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) => Finset (Fin i)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst (Sigma.fst q)), M (Sigma.fst (Sigma.fst q)), fs (Sigma.fst (Sigma.fst q)), zs (Sigma.fst (Sigma.fst q)), W (Sigma.fst (Sigma.fst q)))))))))))) polyH70 polyH68; have polyH86 := @Poly.mapTime (ℕ) (@Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => (Prod.snd x, Prod.fst x)) (@Uniform.swap ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (3) (Max.max (Max.max (Max.max (Max.max (2 * 1) (30000 + 2 * 1)) (0)) (Max.max (Max.max (2 * 1) (30000 + 2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (2 * 1) (30000 + 2 * 1)) (30000 + 2 * 1)) (2 * 1)) (0))) (3 + 2 * 1) (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)) polyH66 polyH84 polyH51 polyH50 polyH85; have polyH87 := Poly.add polyH65 polyH86; have polyH88 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)) (10); have polyH89 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) polyH51 polyH50; have polyH90 := Poly.add polyH89 polyH61; have polyH91 := Poly.mul polyH88 polyH90; have polyH92 := Poly.add polyH87 polyH91; have polyH93 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i) × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _ _ (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i) × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => List.map (fun (a : Finset (Fin i)) => (Prod.snd (a, Prod.snd x), Prod.fst (a, Prod.snd x))) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _)) (@Uniform.map ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => (Prod.snd x, Prod.fst x)) (@Uniform.swap ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) polyH92; have polyH94 := Poly.lengthMap (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (a : Finset (Fin (n (Sigma.fst q)))) => (Prod.snd (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))), Prod.fst (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) polyH66; have polyH95 := Poly.size (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => List.map (fun (a : Finset (Fin (n (Sigma.fst q)))) => (Prod.snd (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))), Prod.fst (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) (Prod.fst ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))))) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH96 := Poly.volumeFinset polyH95 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => List.map (fun (a : Finset (Fin (n (Sigma.fst q)))) => (Prod.snd (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))), Prod.fst (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) (Prod.fst ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))))) => (Sigma.snd q).1.1); have polyH97 := Poly.volumeFinset polyH95 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => List.map (fun (a : Finset (Fin (n (Sigma.fst q)))) => (Prod.snd (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))), Prod.fst (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) (Prod.fst ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))))) => (Sigma.snd q).1.2); have polyH98 := Poly.volumeProd (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => List.map (fun (a : Finset (Fin (n (Sigma.fst q)))) => (Prod.snd (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))), Prod.fst (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) (Prod.fst ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))))) => (Sigma.snd q).1) polyH96 polyH97; have polyH99 := Poly.listVolume (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => List.map (fun (a : Finset (Fin (n (Sigma.fst q)))) => (Prod.snd (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))), Prod.fst (a, Prod.snd ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))))) (Prod.fst ((fun (x : (fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)) × List ((fun (i : ℕ) => Finset (Fin i)) (n (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.fst (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))))) polyH94 polyH98; have polyH100 := @Poly.flatMapTime (ℕ) (J) (n) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (j_1 : J) => Prod.snd (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) => (fun (x_1 : List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i) × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => List.map (fun (a : Finset (Fin i)) => (Prod.snd (a, Prod.snd x_1), Prod.fst (a, Prod.snd x_1))) (Prod.fst x_1)) ((fun (x_1 : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) => (Prod.snd x_1, Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i) × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _ _ (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i) × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => List.map (fun (a : Finset (Fin i)) => (Prod.snd (a, Prod.snd x), Prod.fst (a, Prod.snd x))) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Finset (Fin i_1)) i)) _ _)) (@Uniform.map ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => (Prod.snd x, Prod.fst x)) (@Uniform.swap ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _))) (30000) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (3 + 2 * 1)) (0)) (Max.max (Max.max (2 * 1) (3 + 2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (2 * 1) (3 + 2 * 1)) (3 + 2 * 1)) (2 * 1)) (0))) (3 + Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (30000 + 2 * 1)) (0)) (Max.max (Max.max (2 * 1) (30000 + 2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (2 * 1) (30000 + 2 * 1)) (30000 + 2 * 1)) (2 * 1)) (0))) (Max.max (3 + 2 * 1) (Max.max (2 * 1) (3 + Max.max (30000 + 2 * 1) (2 * 1)))))) (0 + Max.max (Max.max (3 + 2 * 1) (2 * 1)) (0))) (30000 + 2 * 1) (3 + 2 * 1) (3 + Max.max (2 * 1) (2 * 1)) (hf) polyH93 (hfv) (hzv) polyH99; have polyH101 := Poly.add polyH48 polyH100; have polyH102 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (hfv) (hzv); have polyH103 := Poly.add polyH102 polyH17; have polyH104 := Poly.mul polyH16 polyH103; have polyH105 := Poly.add polyH101 polyH104; have polyH106 := Poly.of_le (fun (j_13 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.StatesInput) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × Finset (Fin i))) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ Uniform.StatesInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) Uniform.statesF Uniform.statesZ) (@Uniform.product ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (n j_13) ((U j_13, M j_13, fs j_13, zs j_13, W j_13))))) polyH105; exact Poly.lift polyH106 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem statesS
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.statesS.time (n j) (U j,(M j,(fs j,(zs j,W j))))) 60020 := by
  have hp := statesPairs n U M fs zs W hf hz
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH6; have polyH8 := Poly.const (n) (2); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH9; have polyH11 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH9; have polyH12 := Poly.add polyH6 polyH8; have polyH13 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH12; have polyH14 := Poly.add polyH5 polyH8; have polyH15 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) (Prod.snd (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14)))))) polyH14; have polyH16 := Poly.add polyH4 polyH8; have polyH17 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_14) (Prod.snd (Prod.snd (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))))) polyH16; have polyH18 := Poly.add polyH15 polyH17; have polyH19 := Poly.const (n) (10); have polyH20 := Poly.const (n) (1); have polyH21 := Poly.add polyH4 polyH20; have polyH22 := Poly.mul polyH19 polyH21; have polyH23 := Poly.add polyH18 polyH22; have polyH24 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n j_14) (Prod.snd (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14)))))) polyH23; have polyH25 := Poly.add polyH13 polyH24; have polyH26 := Poly.add polyH5 polyH20; have polyH27 := Poly.mul polyH19 polyH26; have polyH28 := Poly.add polyH25 polyH27; have polyH29 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)) (n j_14) (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH28; have polyH30 := Poly.add polyH11 polyH29; have polyH31 := Poly.add polyH6 polyH20; have polyH32 := Poly.mul polyH19 polyH31; have polyH33 := Poly.add polyH30 polyH32; have polyH34 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _))) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH33; have polyH35 := Poly.add polyH10 polyH34; have polyH36 := Poly.const (n) (20); have polyH37 := Poly.add polyH7 polyH1; have polyH38 := Poly.add polyH37 polyH3; have polyH39 := Poly.add polyH38 polyH20; have polyH40 := Poly.mul polyH36 polyH39; have polyH41 := Poly.add polyH35 polyH40; have polyH42 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Universe) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (Uniform.statesW) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH41; have polyH43 := Poly.add (hp) polyH42; have polyH44 := Poly.lengthProduct (hf) (hz); have polyH45 := Poly.size (fun (q : Poly.ListPool fun (j_1 : J) => List.product (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))) (Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) => n (Sigma.fst q)); have polyH46 := Poly.volumeFinset polyH45 (fun (q : Poly.ListPool fun (j_1 : J) => List.product (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))) (Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) => (Sigma.snd q).1.1); have polyH47 := Poly.volumeFinset polyH45 (fun (q : Poly.ListPool fun (j_1 : J) => List.product (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))) (Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) => (Sigma.snd q).1.2); have polyH48 := Poly.volumeProd (fun (q : Poly.ListPool fun (j_1 : J) => List.product (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))) (Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) => (Sigma.snd q).1) polyH46 polyH47; have polyH49 := Poly.listVolume (fun (j_1 : J) => List.product (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))) (Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) polyH44 polyH48; have polyH50 := Poly.add polyH7 polyH49; have polyH51 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) polyH1 polyH3; have polyH52 := Poly.add polyH50 polyH51; have polyH53 := Poly.add polyH52 polyH20; have polyH54 := Poly.mul polyH36 polyH53; have polyH55 := Poly.add polyH43 polyH54; have polyH56 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.StatesInput) (fun (i : ℕ) => List (Finset (Fin i) × Finset (Fin i))) (fun (i : ℕ) => Universe i × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => (fun (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x)) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Uniform.statesPairs) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) Uniform.statesW) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH55; have polyH57 := Poly.size (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)); have polyH58 := Poly.reparam (@Costs.statesC) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Sigma.mk (n (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd ((fun (x : List (Finset (Fin (n (Sigma.fst q)))) × List (Finset (Fin (n (Sigma.fst q))))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n (Sigma.fst q))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))), Prod.fst (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))) polyH57; have polyH59 := Poly.volumeState polyH57 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd ((fun (x : List (Finset (Fin (n (Sigma.fst q)))) × List (Finset (Fin (n (Sigma.fst q))))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n (Sigma.fst q))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))), Prod.fst (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) (Prod.fst (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd ((fun (x : List (Finset (Fin (n (Sigma.fst q)))) × List (Finset (Fin (n (Sigma.fst q))))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n (Sigma.fst q))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))), Prod.fst (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))))))))) (Prod.snd (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd ((fun (x : List (Finset (Fin (n (Sigma.fst q)))) × List (Finset (Fin (n (Sigma.fst q))))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n (Sigma.fst q))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))), Prod.fst (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))))); have polyH60 := @Poly.mapTime (ℕ) (J) (n) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => Universe i × Finset (Fin i)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (j_1 : J) => Prod.snd ((fun (x : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (n_1 : ℕ) (x : (Finset (Fin n_1) × Finset (Fin n_1)) × Universe n_1 × Finset (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd x)) (Prod.fst (Prod.fst x)) (Prod.snd (Prod.fst x))) (Uniform.statesC) (30000 + 3) (5 * 1) (30000 + 3 + Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (2 * 1)) (2 * 1) polyH44 polyH58 polyH49 polyH51 polyH59; have polyH61 := Poly.add polyH56 polyH60; have polyH62 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x) (Prod.snd x)) ((fun (x : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) polyH49 polyH51; have polyH63 := Poly.add polyH62 polyH20; have polyH64 := Poly.mul polyH19 polyH63; have polyH65 := Poly.add polyH61 polyH64; have polyH66 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.StatesInput) (fun (i : ℕ) => List (Finset (Fin i) × Finset (Fin i)) × Universe i × Finset (Fin i)) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => ((fun (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (i : ℕ) (x : List (Finset (Fin i) × Finset (Fin i)) × Universe i × Finset (Fin i)) => List.map (fun (a : Finset (Fin i) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) (@Uniform.pair ℕ Uniform.StatesInput (fun (i : ℕ) => List (Finset (Fin i) × Finset (Fin i))) (fun (i : ℕ) => Universe i × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => (fun (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x)) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) Uniform.statesPairs (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) Uniform.statesW)) (@Uniform.map ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => Universe i × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : (Finset (Fin n_1) × Finset (Fin n_1)) × Universe n_1 × Finset (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd x)) (Prod.fst (Prod.fst x)) (Prod.snd (Prod.fst x))) Uniform.statesC) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH65; exact Poly.lift polyH66 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem states
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3) :
    Poly n (fun j => Uniform.states.time (n j) (U j,(M j,(fs j,(zs j,W j))))) 120008 := by
  have hS := statesS n U M fs zs W hf hz
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (M j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH6; have polyH8 := Poly.const (n) (2); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH9; have polyH11 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH9; have polyH12 := Poly.add polyH6 polyH8; have polyH13 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH12; have polyH14 := Poly.add polyH11 polyH13; have polyH15 := Poly.const (n) (10); have polyH16 := Poly.const (n) (1); have polyH17 := Poly.add polyH6 polyH16; have polyH18 := Poly.mul polyH15 polyH17; have polyH19 := Poly.add polyH14 polyH18; have polyH20 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH19; have polyH21 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH12; have polyH22 := Poly.add polyH5 polyH8; have polyH23 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_14) (Prod.snd (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14)))))) polyH22; have polyH24 := Poly.add polyH4 polyH8; have polyH25 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_14) (Prod.snd (Prod.snd (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))))) polyH24; have polyH26 := Poly.add polyH23 polyH25; have polyH27 := Poly.add polyH4 polyH16; have polyH28 := Poly.mul polyH15 polyH27; have polyH29 := Poly.add polyH26 polyH28; have polyH30 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n j_14) (Prod.snd (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14)))))) polyH29; have polyH31 := Poly.add polyH21 polyH30; have polyH32 := Poly.add polyH5 polyH16; have polyH33 := Poly.mul polyH15 polyH32; have polyH34 := Poly.add polyH31 polyH33; have polyH35 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)) (n j_14) (Prod.snd (U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH34; have polyH36 := Poly.add polyH11 polyH35; have polyH37 := Poly.add polyH36 polyH18; have polyH38 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _))) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH37; have polyH39 := Poly.add polyH20 polyH38; have polyH40 := Poly.const (n) (20); have polyH41 := Poly.add polyH7 polyH2; have polyH42 := Poly.add polyH41 polyH3; have polyH43 := Poly.add polyH42 polyH16; have polyH44 := Poly.mul polyH40 polyH43; have polyH45 := Poly.add polyH39 polyH44; have polyH46 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Matrix) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _)) (Uniform.statesW) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH45; have polyH47 := Poly.add polyH10 polyH46; have polyH48 := Poly.add polyH7 polyH1; have polyH49 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) polyH2 polyH3; have polyH50 := Poly.add polyH48 polyH49; have polyH51 := Poly.add polyH50 polyH16; have polyH52 := Poly.mul polyH40 polyH51; have polyH53 := Poly.add polyH47 polyH52; have polyH54 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Universe) (fun (i : ℕ) => Matrix i × Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _)) Uniform.statesW) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH53; have polyH55 := Poly.add (hS) polyH54; have polyH56 := Poly.lengthProduct (hf) (hz); have polyH57 := Poly.lengthMap (fun (j_1 : J) (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.snd (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) polyH56; have polyH58 := Poly.size (fun (q : Poly.ListPool fun (j_1 : J) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.snd (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) => n (Sigma.fst q)); have polyH59 := Poly.volumeState polyH58 (fun (q : Poly.ListPool fun (j_1 : J) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.snd (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) => (Sigma.snd q).1); have polyH60 := Poly.listVolume (fun (j_1 : J) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1))))) (Prod.snd (Prod.fst (a, Prod.snd ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (Prod.fst ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)))) polyH57 polyH59; have polyH61 := Poly.add polyH7 polyH60; have polyH62 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) polyH1 polyH49; have polyH63 := Poly.add polyH61 polyH62; have polyH64 := Poly.add polyH63 polyH16; have polyH65 := Poly.mul polyH40 polyH64; have polyH66 := Poly.add polyH55 polyH65; have polyH67 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.StatesInput) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Matrix i × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => (fun (x_1 : List (Finset (Fin i) × Finset (Fin i)) × Universe i × Finset (Fin i)) => List.map (fun (a : Finset (Fin i) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x_1))) (Prod.fst (Prod.fst (a, Prod.snd x_1))) (Prod.snd (Prod.fst (a, Prod.snd x_1)))) (Prod.fst x_1)) ((fun (x_1 : Uniform.StatesInput i) => ((fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x_2)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_2))))) x_1), Prod.fst x_1, Prod.snd (Prod.snd (Prod.snd (Prod.snd x_1))))) x)) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst x, Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Uniform.statesS) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Universe (fun (i : ℕ) => Matrix i × Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _)) Uniform.statesW)) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH66; have polyH68 := Poly.size (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1)) × Finset (Fin (n j_1))) × Universe (n j_1) × Finset (Fin (n j_1))) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => n (Sigma.fst q)); have polyH69 := Poly.reparam (@Costs.statesP) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1)) × Finset (Fin (n j_1))) × Universe (n j_1) × Finset (Fin (n j_1))) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) => Sigma.mk (n (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd ((fun (x : List (Finset (Fin (n (Sigma.fst q))) × Finset (Fin (n (Sigma.fst q)))) × Universe (n (Sigma.fst q)) × Finset (Fin (n (Sigma.fst q)))) => List.map (fun (a : Finset (Fin (n (Sigma.fst q))) × Finset (Fin (n (Sigma.fst q)))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) ((fun (x : Uniform.StatesInput (n (Sigma.fst q))) => ((fun (x_1 : List (Finset (Fin (n (Sigma.fst q)))) × List (Finset (Fin (n (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n (Sigma.fst q))) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))), Prod.fst (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)), Prod.fst (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U (Sigma.fst q), M (Sigma.fst q), fs (Sigma.fst q), zs (Sigma.fst q), W (Sigma.fst q)))))))) polyH68; have polyH70 := @Poly.filterTime (ℕ) (J) (n) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Matrix i × Finset (Fin i)) _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst ((fun (x : List (Finset (Fin (n j_1)) × Finset (Fin (n j_1))) × Universe (n j_1) × Finset (Fin (n j_1))) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (j_1 : J) => Prod.snd ((fun (x : List (Finset (Fin (n j_1)) × Finset (Fin (n j_1))) × Universe (n j_1) × Finset (Fin (n j_1))) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) (fun (n_1 : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin n_1) × Universe n_1 × Matrix n_1 × Finset (Fin n_1)) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.Compatible (matrixRel (Prod.fst (Prod.snd (Prod.snd x)))) (Prod.snd (Prod.snd (Prod.snd x))) (Prod.fst x))) (Uniform.statesP) (30000 + 3) (5 * 1) (30000 + 3 + 2 * 1) (Max.max (2 * 1) (Max.max (2 * 1) (2 * 1))) polyH57 polyH69 polyH60 polyH62; have polyH71 := Poly.add polyH67 polyH70; have polyH72 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : List (Finset (Fin (n j_1)) × Finset (Fin (n j_1))) × Universe (n j_1) × Finset (Fin (n j_1))) => List.map (fun (a : Finset (Fin (n j_1)) × Finset (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x))) (Prod.fst (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) ((fun (x : Uniform.StatesInput (n j_1)) => ((fun (x_1 : List (Finset (Fin (n j_1))) × List (Finset (Fin (n j_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Uniform.StatesInput (n j_1)) => (Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)), Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, fs j_1, zs j_1, W j_1)))))) polyH60 polyH62; have polyH73 := Poly.add polyH72 polyH16; have polyH74 := Poly.mul polyH15 polyH73; have polyH75 := Poly.add polyH71 polyH74; have polyH76 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.StatesInput) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Universe i × Matrix i × Finset (Fin i)) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => ((fun (x_1 : List (Finset (Fin i) × Finset (Fin i)) × Universe i × Finset (Fin i)) => List.map (fun (a : Finset (Fin i) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x_1))) (Prod.fst (Prod.fst (a, Prod.snd x_1))) (Prod.snd (Prod.fst (a, Prod.snd x_1)))) (Prod.fst x_1)) ((fun (x_1 : Uniform.StatesInput i) => ((fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x_2)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_2))))) x_1), Prod.fst x_1, Prod.snd (Prod.snd (Prod.snd (Prod.snd x_1))))) x), Prod.fst x, Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Universe i × Matrix i × Finset (Fin i)) => List.filter (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i)) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.Compatible (matrixRel (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) (@Uniform.pair ℕ Uniform.StatesInput (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Matrix i × Finset (Fin i)) _ _ _ (fun (i : ℕ) (x : Uniform.StatesInput i) => (fun (x_1 : List (Finset (Fin i) × Finset (Fin i)) × Universe i × Finset (Fin i)) => List.map (fun (a : Finset (Fin i) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.State.candidate (Prod.snd (Prod.snd (a, Prod.snd x_1))) (Prod.fst (Prod.fst (a, Prod.snd x_1))) (Prod.snd (Prod.fst (a, Prod.snd x_1)))) (Prod.fst x_1)) ((fun (x_1 : Uniform.StatesInput i) => ((fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Uniform.StatesInput i) => (Prod.fst (Prod.snd (Prod.snd x_2)), Prod.fst (Prod.snd (Prod.snd (Prod.snd x_2))))) x_1), Prod.fst x_1, Prod.snd (Prod.snd (Prod.snd (Prod.snd x_1))))) x)) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst x, Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) Uniform.statesS (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Universe (fun (i : ℕ) => Matrix i × Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => (Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Uniform.StatesInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _)) Uniform.statesW))) (@Uniform.filter ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Matrix i × Finset (Fin i)) _ _ (fun (n_1 : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin n_1) × Universe n_1 × Matrix n_1 × Finset (Fin n_1)) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.Compatible (matrixRel (Prod.fst (Prod.snd (Prod.snd x)))) (Prod.snd (Prod.snd (Prod.snd x))) (Prod.fst x))) Uniform.statesP) (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH75; have polyH77 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_states (n j_14) ((U j_14, M j_14, fs j_14, zs j_14, W j_14))))) polyH76; exact Poly.lift polyH77 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

theorem time_initialMarks (n : ℕ) (x : Table n × List (Algorithm.State (Fin n))) :
    initialMarks.time n x = (swap.comp initialMarkBody.tableOfA).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (tab : ∀ j, Table (n j))
theorem initialMarkBody (v : ∀ j, Algorithm.State (Fin (n j)))
    (hl : Poly n (fun j => (tab j).length) 30000) (ht : ∀ j, TableSmall (tab j)) :
    Poly n (fun j => Uniform.initialMarkBody.time (n j) (v j,tab j)) 60002 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hv := Poly.volumeSmallLookup tab (fun j => (v j).left) (Poly.size n) ht
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeState polyH0 (fun (j_1 : J) => v j_1); have polyH2 := Poly.volumeProd (fun (j_1 : J) => (v j_1, tab j_1)) polyH1 (htv); have polyH3 := Poly.const (n) (2); have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_10) ((v j_10, tab j_10))))) polyH4; have polyH6 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_10) ((v j_10, tab j_10))))) polyH4; have polyH7 := Poly.add polyH1 polyH3; have polyH8 := Poly.volumeFinset polyH0 (fun (j_1 : J) => (Prod.fst (v j_1, tab j_1)).1); have polyH9 := Poly.volumeFinset polyH0 (fun (j_1 : J) => (Prod.fst (v j_1, tab j_1)).2); have polyH10 := Poly.volumeFinset polyH0 (fun (j_1 : J) => (Prod.fst (v j_1, tab j_1)).3); have polyH11 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (v j_1, tab j_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (v j_1, tab j_1)))) polyH9 polyH10; have polyH12 := Poly.volumeProd (fun (j_1 : J) => (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (v j_1, tab j_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (v j_1, tab j_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (v j_1, tab j_1)))) polyH8 polyH11; have polyH13 := Poly.add polyH12 polyH3; have polyH14 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (n j_10) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (v j_10, tab j_10)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (v j_10, tab j_10)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (v j_10, tab j_10))))))) polyH13; have polyH15 := Poly.add polyH7 polyH14; have polyH16 := Poly.const (n) (10); have polyH17 := Poly.const (n) (1); have polyH18 := Poly.add polyH12 polyH17; have polyH19 := Poly.mul polyH16 polyH18; have polyH20 := Poly.add polyH15 polyH19; have polyH21 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1) × Finset (Fin n_1) × Finset (Fin n_1)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) => Prod.fst) (Uniform.stateParts) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (n j_10) (Prod.fst (v j_10, tab j_10))))) polyH20; have polyH22 := Poly.add polyH6 polyH21; have polyH23 := Poly.add polyH1 polyH17; have polyH24 := Poly.mul polyH16 polyH23; have polyH25 := Poly.add polyH22 polyH24; have polyH26 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (Uniform.stateLeft) (n j_10) ((v j_10, tab j_10))))) polyH25; have polyH27 := Poly.add polyH5 polyH26; have polyH28 := Poly.const (n) (20); have polyH29 := Poly.add polyH2 (htv); have polyH30 := Poly.add polyH29 polyH8; have polyH31 := Poly.add polyH30 polyH17; have polyH32 := Poly.mul polyH28 polyH31; have polyH33 := Poly.add polyH27 polyH32; have polyH34 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst x)) (@Uniform.snd ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) Uniform.stateLeft) (n j_10) ((v j_10, tab j_10))))) polyH33; have polyH35 := Poly.const (n) (100000000000); have polyH36 := Poly.add (hl) polyH17; have polyH37 := Poly.mul polyH35 polyH36; have polyH38 := Poly.const (n) (Classical.choose Costs.setEq); have polyH39 := Poly.base (n); have polyH40 := Poly.pow polyH39 (4); have polyH41 := Poly.mul polyH38 polyH40; have polyH42 := Poly.add polyH41 (htv); have polyH43 := Poly.add polyH42 polyH8; have polyH44 := Poly.add polyH43 polyH17; have polyH45 := Poly.mul polyH37 polyH44; have polyH46 := Poly.of_le (fun (j_10 : J) => (@Uniform.time_lookup_setEq_le (n j_10) (Prod.snd (v j_10, tab j_10)) ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_10))) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst (v j_10, tab j_10))))) polyH45; have polyH47 := Poly.add polyH34 polyH46; have polyH48 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (v j_1, tab j_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst (v j_1, tab j_1)))) (htv) polyH8; have polyH49 := Poly.add polyH48 polyH17; have polyH50 := Poly.mul polyH16 polyH49; have polyH51 := Poly.add polyH47 polyH50; have polyH52 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd x, (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst x))) (fun (i : ℕ) (x : List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Finset (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst x)) (@Uniform.snd ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.fst ℕ (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n_1)) (fun (i : ℕ) => List (Finset (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) Uniform.stateLeft)) (@Uniform.lookupA ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ _ _ Uniform.setEq) (n j_10) ((v j_10, tab j_10))))) polyH51; exact Poly.lift polyH52 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_markings (n : ℕ) (x : ℕ × MarkEnv n) :
    markings.time n x =
      ((((fst.pair (snd.pair (snd.comp (snd.comp initialMarks)))).comp markingsStep.iterate).comp snd)).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

theorem markingsStep_iterate {n : ℕ} (e : Uniform.MarkEnv n) (k : ℕ) :
    (fun p : Uniform.MarkEnv n × Marks n => (p.1,Algorithm.expand p.1.2.1 p.1.2.2 p.2))^[k]
      (e,Algorithm.tableOf e.2.2 (fun v => Algorithm.lookup e.2.1 v.left)) =
      (e,Algorithm.markings e.2.1 e.2.2 k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (sts : ∀ j, List (Algorithm.State (Fin (n j))))

theorem initialMarks
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) :
    Poly n (fun j => Uniform.initialMarks.time (n j) (tab j,sts j)) 90005 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hlook : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume (Algorithm.lookup (tab p.1) p.2.1.left)) 2 :=
    Poly.volumeSmallLookup (fun p : Poly.ListPool sts => tab p.1) (fun p => p.2.1.left)
      ((Poly.size n).precomp Sigma.fst) (fun p => ht p.1)
  have hbody := initialMarkBody (fun p : Poly.ListPool sts => n p.1) (fun p => tab p.1)
    (fun p => p.2.1) (hl.precomp Sigma.fst) (fun p => ht p.1)
  have hA : Poly (fun p : Poly.ListPool sts => n p.1) (fun p => volume p.2.1) 2 := by (have polyH0 := Poly.size (fun (p_1 : Poly.ListPool sts) => n (Sigma.fst p_1)); have polyH1 := Poly.volumeState polyH0 (fun (p_1 : Poly.ListPool sts) => (Sigma.snd p_1).1); exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hTable := Poly.tableOfTime Uniform.initialMarkBody n sts tab hsl hbody hlook hA hsv htv
  have hExact : Poly n (fun j => Uniform.initialMarkBody.tableOfA.time (n j) (sts j,tab j)) 90005 := hTable
  (have polyH0 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, sts j_1)) (htv) (hsv); have polyH1 := Poly.const (n) (2); have polyH2 := Poly.add polyH0 polyH1; have polyH3 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_16) ((tab j_16, sts j_16))))) polyH2; have polyH4 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_16) ((tab j_16, sts j_16))))) polyH2; have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.const (n) (20); have polyH7 := Poly.add polyH0 (hsv); have polyH8 := Poly.add polyH7 (htv); have polyH9 := Poly.const (n) (1); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.mul polyH6 polyH10; have polyH12 := Poly.add polyH5 polyH11; have polyH13 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Table i × (fun (i_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i_1))) i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (n j_16) ((tab j_16, sts j_16))))) polyH12; have polyH14 := Poly.add polyH13 (hExact); have polyH15 := Poly.const (n) (10); have polyH16 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (tab j_1, sts j_1), Prod.fst (tab j_1, sts j_1))) (hsv) (htv); have polyH17 := Poly.add polyH16 polyH9; have polyH18 := Poly.mul polyH15 polyH17; have polyH19 := Poly.add polyH14 polyH18; have polyH20 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Table i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Table i) => OAI.ThreeMachine.Algorithm.tableOf (Prod.fst x) fun (a : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.snd (a, Prod.snd x)) (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (a, Prod.snd x)))) (@Uniform.swap ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.tableOfA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) Table _ _ _ (fun (n_1 : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin n_1) × Table n_1) => OAI.ThreeMachine.Algorithm.lookup (Prod.snd x) (OAI.ThreeMachine.Algorithm.State.left (Prod.fst x))) Uniform.initialMarkBody) (n j_16) ((tab j_16, sts j_16))))) polyH19; have polyH21 := Poly.of_le (fun (j_16 : J) => (le_of_eq (@Uniform.time_initialMarks (n j_16) ((tab j_16, sts j_16))))) polyH20; exact Poly.lift polyH21 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (sts : ∀ j, List (Algorithm.State (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

theorem markings
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j))
    (hs : ∀ j u, u ∈ sts j → u.Compatible (matrixRel (M j)) (W j)) :
    Poly n (fun j => Uniform.markings.time (n j) (n j,(U j,(tab j,sts j)))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hInit := initialMarks n tab sts hl hsl hts
  let ms (p : Poly.IterPool n) := Algorithm.markings (tab p.1) (sts p.1) p.2.1
  have hml : Poly (fun p : Poly.IterPool n => n p.1) (fun p => (ms p).length) 30003 :=
    Poly.of_le (fun p => Algorithm.markings_length _ _ _) (hsl.precomp Sigma.fst)
  have hms (p : Poly.IterPool n) : MarksSmall (ms p) := markings_small (matrixRel (M p.1)) (ht p.1) (hb p.1) (hs p.1) _
  have hmv := Poly.volumeMarks ms ((Poly.size n).precomp Sigma.fst) hml hms
  have hStep := markingsStep (fun p : Poly.IterPool n => n p.1) (fun p => U p.1) (fun p => tab p.1)
    (fun p => sts p.1) ms (hl.precomp Sigma.fst) (hsl.precomp Sigma.fst) hml (fun p => hts p.1) hms
  have htIter : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => Uniform.markingsStep.time (n p.1) ((fun q : Uniform.MarkEnv (n p.1) × Marks (n p.1) =>
        (q.1,Algorithm.expand q.1.2.1 q.1.2.2 q.2))^[p.2.1]
        ((U p.1,(tab p.1,sts p.1)),Algorithm.tableOf (sts p.1) (fun v => Algorithm.lookup (tab p.1) v.left)))) 120008 := by
    apply Poly.of_le _ hStep
    intro p
    exact le_of_eq (congrArg (fun q => Uniform.markingsStep.time (n p.1) q)
      (markingsStep_iterate (U p.1,(tab p.1,sts p.1)) p.2.1))
  have hvIter : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => volume ((fun q : Uniform.MarkEnv (n p.1) × Marks (n p.1) =>
        (q.1,Algorithm.expand q.1.2.1 q.1.2.2 q.2))^[p.2.1]
        ((U p.1,(tab p.1,sts p.1)),Algorithm.tableOf (sts p.1) (fun v => Algorithm.lookup (tab p.1) v.left)))) 30005 := by
    have hpair : Poly (fun p : Poly.IterPool n => n p.1)
        (fun p => volume ((U p.1,(tab p.1,sts p.1)),ms p)) 30005 := by
      have htv' := htv.precomp (fun p : Poly.IterPool n => p.1)
      have hsv' := hsv.precomp (fun p : Poly.IterPool n => p.1)
      (have polyH0 := Poly.size (fun (p_1 : Poly.IterPool n) => n (Sigma.fst p_1)); have polyH1 := Poly.volumeUniverse polyH0 (fun (p_1 : Poly.IterPool n) => U (Sigma.fst p_1)); have polyH2 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (tab (Sigma.fst p_1), sts (Sigma.fst p_1))) (htv') (hsv'); have polyH3 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => (U (Sigma.fst p_1), tab (Sigma.fst p_1), sts (Sigma.fst p_1))) polyH1 polyH2; have polyH4 := Poly.volumeProd (fun (p_1 : Poly.IterPool n) => ((U (Sigma.fst p_1), tab (Sigma.fst p_1), sts (Sigma.fst p_1)), ms p_1)) polyH3 (hmv); exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
    apply Poly.of_le _ hpair
    intro p
    exact le_of_eq (congrArg volume (markingsStep_iterate (U p.1,(tab p.1,sts p.1)) p.2.1))
  have hIter := Poly.iterateTime Uniform.markingsStep n n
    (fun j => ((U j,(tab j,sts j)),Algorithm.tableOf (sts j) (fun v => Algorithm.lookup (tab j) v.left)))
    (Poly.size n) htIter hvIter
  have hmi : Poly n (fun j => volume (Algorithm.tableOf (sts j) (fun v => Algorithm.lookup (tab j) v.left))) 30005 := by
    have hml : Poly n (fun j => (Algorithm.markings (tab j) (sts j) 0).length) 30003 :=
      Poly.of_le (fun j => Algorithm.markings_length _ _ _) hsl
    exact Poly.volumeMarks (d := 1) (l := 30003) (fun j => Algorithm.markings (tab j) (sts j) 0) (Poly.size n) hml
      (fun j => markings_small _ (ht j) (hb j) (hs j) 0)
  have hFinal := hvIter.precomp (fun j : J => (⟨j,⟨n j,by omega⟩⟩ : Poly.IterPool n))
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeNat polyH0; have polyH2 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH3 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, sts j_1)) (htv) (hsv); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, tab j_1, sts j_1)) polyH2 polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (n j_1, U j_1, tab j_1, sts j_1)) polyH1 polyH4; have polyH6 := Poly.const (n) (2); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH7; have polyH9 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH7; have polyH10 := Poly.add polyH4 polyH6; have polyH11 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _ (n j_28) (Prod.snd (n j_28, U j_28, tab j_28, sts j_28))))) polyH10; have polyH12 := Poly.add polyH11 (hInit); have polyH13 := Poly.const (n) (10); have polyH14 := Poly.const (n) (1); have polyH15 := Poly.add polyH3 polyH14; have polyH16 := Poly.mul polyH13 polyH15; have polyH17 := Poly.add polyH12 polyH16; have polyH18 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _) (Uniform.initialMarks) (n j_28) (Prod.snd (n j_28, U j_28, tab j_28, sts j_28))))) polyH17; have polyH19 := Poly.add polyH9 polyH18; have polyH20 := Poly.add polyH4 polyH14; have polyH21 := Poly.mul polyH13 polyH20; have polyH22 := Poly.add polyH19 polyH21; have polyH23 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _) Uniform.initialMarks) (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH22; have polyH24 := Poly.add polyH9 polyH23; have polyH25 := Poly.const (n) (20); have polyH26 := Poly.add polyH5 polyH4; have polyH27 := Poly.add polyH26 (hmi); have polyH28 := Poly.add polyH27 polyH14; have polyH29 := Poly.mul polyH25 polyH28; have polyH30 := Poly.add polyH24 polyH29; have polyH31 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _) Uniform.initialMarks)) (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH30; have polyH32 := Poly.add polyH8 polyH31; have polyH33 := Poly.add polyH5 polyH1; have polyH34 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (n j_1, U j_1, tab j_1, sts j_1), (fun (x : Table (n j_1) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd (n j_1, U j_1, tab j_1, sts j_1))))) polyH4 (hmi); have polyH35 := Poly.add polyH33 polyH34; have polyH36 := Poly.add polyH35 polyH14; have polyH37 := Poly.mul polyH25 polyH36; have polyH38 := Poly.add polyH32 polyH37; have polyH39 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.snd x, (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _) Uniform.initialMarks))) (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH38; have polyH40 := Poly.add polyH39 (hIter); have polyH41 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (n j_1, U j_1, tab j_1, sts j_1), Prod.snd (n j_1, U j_1, tab j_1, sts j_1), (fun (x : Table (n j_1) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd (n j_1, U j_1, tab j_1, sts j_1))))) polyH1 polyH34; have polyH42 := Poly.add polyH41 polyH14; have polyH43 := Poly.mul polyH13 polyH42; have polyH44 := Poly.add polyH40 polyH43; have polyH45 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => ℕ × (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Uniform.MarkEnv n_1 × Marks n_1) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.fst x, Prod.snd x, (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : ℕ × Uniform.MarkEnv i × Marks i) => (fun (x_1 : Uniform.MarkEnv i × Marks i) => (Prod.fst x_1, OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x_1))) (Prod.snd (Prod.snd (Prod.fst x_1))) (Prod.snd x_1)))^[Prod.fst x] (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.snd x, (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _) Uniform.initialMarks)))) (@Uniform.iterate ℕ (fun (n_1 : ℕ) => Uniform.MarkEnv n_1 × Marks n_1) _ (fun (n_1 : ℕ) (x : Uniform.MarkEnv n_1 × Marks n_1) => (Prod.fst x, OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x))) (Prod.snd (Prod.snd (Prod.fst x))) (Prod.snd x))) Uniform.markingsStep) (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH44; have polyH46 := Poly.add (hFinal) polyH6; have polyH47 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Uniform.MarkEnv) (Marks) _ _ (n j_28) ((fun (x : ℕ × Uniform.MarkEnv (n j_28) × Marks (n j_28)) => (fun (x_1 : Uniform.MarkEnv (n j_28) × Marks (n j_28)) => (Prod.fst x_1, OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x_1))) (Prod.snd (Prod.snd (Prod.fst x_1))) (Prod.snd x_1)))^[Prod.fst x] (Prod.snd x)) ((fun (x : ℕ × Universe (n j_28) × Table (n j_28) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_28)))) => (Prod.fst x, Prod.snd x, (fun (x_1 : Table (n j_28) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_28)))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin (n j_28))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x)))) (n j_28, U j_28, tab j_28, sts j_28)))))) polyH46; have polyH48 := Poly.add polyH45 polyH47; have polyH49 := Poly.add (hFinal) polyH14; have polyH50 := Poly.mul polyH13 polyH49; have polyH51 := Poly.add polyH48 polyH50; have polyH52 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Uniform.MarkEnv n_1 × Marks n_1) (Marks) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : ℕ × Uniform.MarkEnv i × Marks i) => (fun (x_2 : Uniform.MarkEnv i × Marks i) => (Prod.fst x_2, OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x_2))) (Prod.snd (Prod.snd (Prod.fst x_2))) (Prod.snd x_2)))^[Prod.fst x_1] (Prod.snd x_1)) ((fun (x_1 : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.fst x_1, Prod.snd x_1, (fun (x_2 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_2) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_2) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x_1)))) x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => ℕ × (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (n_1 : ℕ) => Uniform.MarkEnv n_1 × Marks n_1) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.fst x, Prod.snd x, (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : ℕ × Uniform.MarkEnv i × Marks i) => (fun (x_1 : Uniform.MarkEnv i × Marks i) => (Prod.fst x_1, OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x_1))) (Prod.snd (Prod.snd (Prod.fst x_1))) (Prod.snd x_1)))^[Prod.fst x] (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (Prod.snd x, (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => (fun (x_1 : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x_1) fun (v : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (OAI.ThreeMachine.Algorithm.State.left v)) (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) (x : Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.tableOf (Prod.snd x) fun (v : OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (OAI.ThreeMachine.Algorithm.State.left v)) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _) Uniform.initialMarks)))) (@Uniform.iterate ℕ (fun (n_1 : ℕ) => Uniform.MarkEnv n_1 × Marks n_1) _ (fun (n_1 : ℕ) (x : Uniform.MarkEnv n_1 × Marks n_1) => (Prod.fst x, OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x))) (Prod.snd (Prod.snd (Prod.fst x))) (Prod.snd x))) Uniform.markingsStep)) (@Uniform.snd ℕ Uniform.MarkEnv Marks _ _) (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH51; have polyH53 := Poly.of_le (fun (j_28 : J) => (le_of_eq (@Uniform.time_markings (n j_28) ((n j_28, U j_28, tab j_28, sts j_28))))) polyH52; exact Poly.lift polyH53 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

theorem solveS
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, TableSmall (tab j)) :
    Poly n (fun j => Uniform.solveS.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120008 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  have h := states n U M fs zs W hf hz
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, fs j_1, zs j_1, W j_1)) (htv) polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH6; have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH7; have polyH9 := Poly.const (n) (2); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH10; have polyH12 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH10; have polyH13 := Poly.add polyH7 polyH9; have polyH14 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Matrix) (fun (n_1 : ℕ) => Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_18) (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH13; have polyH15 := Poly.add polyH12 polyH14; have polyH16 := Poly.const (n) (10); have polyH17 := Poly.const (n) (1); have polyH18 := Poly.add polyH7 polyH17; have polyH19 := Poly.mul polyH16 polyH18; have polyH20 := Poly.add polyH15 polyH19; have polyH21 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _) (@Uniform.fst ℕ Matrix (fun (n_1 : ℕ) => Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH20; have polyH22 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_18) (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH13; have polyH23 := Poly.add polyH6 polyH9; have polyH24 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_18) (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18)))))) polyH23; have polyH25 := Poly.add polyH5 polyH9; have polyH26 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_18) (Prod.snd (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))))) polyH25; have polyH27 := Poly.add polyH24 polyH26; have polyH28 := Poly.add polyH5 polyH17; have polyH29 := Poly.mul polyH16 polyH28; have polyH30 := Poly.add polyH27 polyH29; have polyH31 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _) (n j_18) (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18)))))) polyH30; have polyH32 := Poly.add polyH22 polyH31; have polyH33 := Poly.add polyH6 polyH17; have polyH34 := Poly.mul polyH16 polyH33; have polyH35 := Poly.add polyH32 polyH34; have polyH36 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _)) (n j_18) (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH35; have polyH37 := Poly.add polyH12 polyH36; have polyH38 := Poly.add polyH37 polyH19; have polyH39 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _))) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH38; have polyH40 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_18) (Prod.snd (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))))) polyH25; have polyH41 := Poly.add polyH4 polyH9; have polyH42 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_18) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18)))))))) polyH41; have polyH43 := Poly.add polyH40 polyH42; have polyH44 := Poly.add polyH4 polyH17; have polyH45 := Poly.mul polyH16 polyH44; have polyH46 := Poly.add polyH43 polyH45; have polyH47 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n j_18) (Prod.snd (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))))) polyH46; have polyH48 := Poly.add polyH24 polyH47; have polyH49 := Poly.add polyH48 polyH29; have polyH50 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)) (n j_18) (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18)))))) polyH49; have polyH51 := Poly.add polyH22 polyH50; have polyH52 := Poly.add polyH51 polyH34; have polyH53 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _))) (n j_18) (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH52; have polyH54 := Poly.add polyH12 polyH53; have polyH55 := Poly.add polyH54 polyH19; have polyH56 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)))) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH55; have polyH57 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n j_18) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18)))))))) polyH41; have polyH58 := Poly.add polyH40 polyH57; have polyH59 := Poly.add polyH58 polyH45; have polyH60 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n j_18) (Prod.snd (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))))) polyH59; have polyH61 := Poly.add polyH24 polyH60; have polyH62 := Poly.add polyH61 polyH29; have polyH63 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)) (n j_18) (Prod.snd (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18)))))) polyH62; have polyH64 := Poly.add polyH22 polyH63; have polyH65 := Poly.add polyH64 polyH34; have polyH66 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _))) (n j_18) (Prod.snd (U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH65; have polyH67 := Poly.add polyH12 polyH66; have polyH68 := Poly.add polyH67 polyH19; have polyH69 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _)))) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH68; have polyH70 := Poly.add polyH56 polyH69; have polyH71 := Poly.const (n) (20); have polyH72 := Poly.add polyH8 (hzv); have polyH73 := Poly.add polyH72 polyH3; have polyH74 := Poly.add polyH73 polyH17; have polyH75 := Poly.mul polyH71 polyH74; have polyH76 := Poly.add polyH70 polyH75; have polyH77 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Uniform.solveZ) (Uniform.solveW) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH76; have polyH78 := Poly.add polyH39 polyH77; have polyH79 := Poly.add polyH8 (hfv); have polyH80 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) (hzv) polyH3; have polyH81 := Poly.add polyH79 polyH80; have polyH82 := Poly.add polyH81 polyH17; have polyH83 := Poly.mul polyH71 polyH82; have polyH84 := Poly.add polyH78 polyH83; have polyH85 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) (Uniform.solveF) (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) Uniform.solveZ Uniform.solveW) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH84; have polyH86 := Poly.add polyH21 polyH85; have polyH87 := Poly.add polyH8 polyH2; have polyH88 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) (hfv) polyH80; have polyH89 := Poly.add polyH87 polyH88; have polyH90 := Poly.add polyH89 polyH17; have polyH91 := Poly.mul polyH71 polyH90; have polyH92 := Poly.add polyH86 polyH91; have polyH93 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (Matrix) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd x))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) (Uniform.solveM) (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveF (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) Uniform.solveZ Uniform.solveW)) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH92; have polyH94 := Poly.add polyH11 polyH93; have polyH95 := Poly.add polyH8 polyH1; have polyH96 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) polyH2 polyH88; have polyH97 := Poly.add polyH95 polyH96; have polyH98 := Poly.add polyH97 polyH17; have polyH99 := Poly.mul polyH71 polyH98; have polyH100 := Poly.add polyH94 polyH99; have polyH101 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (Universe) (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) (Uniform.solveU) (@Uniform.pair ℕ Uniform.SolveInput Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd x))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveM (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveF (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) Uniform.solveZ Uniform.solveW))) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH100; have polyH102 := Poly.add polyH101 (h); have polyH103 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)), Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))))) polyH1 polyH96; have polyH104 := Poly.add polyH103 polyH17; have polyH105 := Poly.mul polyH16 polyH104; have polyH106 := Poly.add polyH102 polyH105; have polyH107 := Poly.of_le (fun (j_18 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.SolveInput) (fun (i : ℕ) => Universe i × Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _ _ (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst x, Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) => OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (@Uniform.pair ℕ Uniform.SolveInput Universe (fun (i : ℕ) => Matrix i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd (Prod.snd x))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveU (@Uniform.pair ℕ Uniform.SolveInput Matrix (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd x))), Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveM (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Finset (Fin i)) × Finset (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))), Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveF (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) Uniform.solveZ Uniform.solveW)))) (Uniform.states) (n j_18) ((U j_18, M j_18, tab j_18, fs j_18, zs j_18, W j_18))))) polyH106; exact Poly.lift polyH107 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem solveMarks
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hf : Poly n (fun j => (fs j).length) 30000) (hz : Poly n (fun j => (zs j).length) 3)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j)) :
    Poly n (fun j => Uniform.solveMarks.time (n j) (U j,(M j,(tab j,(fs j,(zs j,W j)))))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hfv := Poly.volumeSetList fs (Poly.size n) hf
  have hzv := Poly.volumeSetList zs (Poly.size n) hz
  let sts j := Algorithm.states (matrixRel (M j)) (fs j) (zs j) (W j)
  have hsl : Poly n (fun j => (sts j).length) 30003 := by
    apply Poly.of_le (fun j => Algorithm.states_length _ _ _ _)
    (have polyH0 := Poly.mul (hf) (hz); exact Poly.lift polyH0 (by first | decide +kernel | omega))
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hs : ∀ j u, u ∈ sts j → u.Compatible (matrixRel (M j)) (W j) :=
    fun j _ hu => Algorithm.states_compatible _ hu
  have hS := solveS n U M tab fs zs W hl hf hz hts
  have hMarks := markings n U M tab sts W hl hsl ht hb hs
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeMatrix polyH0 (fun (j_1 : J) => M j_1); have polyH3 := Poly.volumeFinset polyH0 (fun (j_1 : J) => W j_1); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (zs j_1, W j_1)) (hzv) polyH3; have polyH5 := Poly.volumeProd (fun (j_1 : J) => (fs j_1, zs j_1, W j_1)) (hfv) polyH4; have polyH6 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, fs j_1, zs j_1, W j_1)) (htv) polyH5; have polyH7 := Poly.volumeProd (fun (j_1 : J) => (M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH2 polyH6; have polyH8 := Poly.volumeProd (fun (j_1 : J) => (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)) polyH1 polyH7; have polyH9 := Poly.const (n) (2); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => Matrix n_1 × Table n_1 × List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH10; have polyH12 := Poly.add polyH1 polyH9; have polyH13 := Poly.const (n) (100000); have polyH14 := Poly.lengthFinRange polyH0; have polyH15 := Poly.const (n) (1); have polyH16 := Poly.add polyH14 polyH15; have polyH17 := Poly.mul polyH13 polyH16; have polyH18 := Poly.volumeFinRange polyH0; have polyH19 := Poly.add polyH18 polyH15; have polyH20 := Poly.mul polyH17 polyH19; have polyH21 := Poly.of_le (fun (j_25 : J) => (@Uniform.time_length_le (ℕ) (Fin) _ (n j_25) (List.finRange (n j_25)))) polyH20; have polyH22 := Poly.add polyH12 polyH21; have polyH23 := Poly.const (n) (10); have polyH24 := Poly.mul polyH23 polyH19; have polyH25 := Poly.add polyH22 polyH24; have polyH26 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (n j_25) (Prod.fst (U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH25; have polyH27 := Poly.add polyH11 polyH26; have polyH28 := Poly.add polyH1 polyH15; have polyH29 := Poly.mul polyH23 polyH28; have polyH30 := Poly.add polyH27 polyH29; have polyH31 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.SolveInput) (Universe) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (Uniform.solveU) (Uniform.universeNumber) (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH30; have polyH32 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH10; have polyH33 := Poly.add polyH7 polyH9; have polyH34 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _ (n j_25) (Prod.snd (U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH33; have polyH35 := Poly.add polyH6 polyH9; have polyH36 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _ (n j_25) (Prod.snd (Prod.snd (U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25)))))) polyH35; have polyH37 := Poly.add polyH34 polyH36; have polyH38 := Poly.add polyH6 polyH15; have polyH39 := Poly.mul polyH23 polyH38; have polyH40 := Poly.add polyH37 polyH39; have polyH41 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _) (n j_25) (Prod.snd (U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH40; have polyH42 := Poly.add polyH32 polyH41; have polyH43 := Poly.add polyH7 polyH15; have polyH44 := Poly.mul polyH23 polyH43; have polyH45 := Poly.add polyH42 polyH44; have polyH46 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Table i × List (Finset (Fin i)) × List (Finset (Fin i)) × Finset (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (n_1 : ℕ) => List (Finset (Fin n_1)) × List (Finset (Fin n_1)) × Finset (Fin n_1)) _ _)) (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH45; have polyH47 := Poly.add polyH46 (hS); have polyH48 := Poly.const (n) (20); have polyH49 := Poly.add polyH8 (htv); have polyH50 := Poly.add polyH49 (hsv); have polyH51 := Poly.add polyH50 polyH15; have polyH52 := Poly.mul polyH48 polyH51; have polyH53 := Poly.add polyH47 polyH52; have polyH54 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (Table) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) (Uniform.solveT) (Uniform.solveS) (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH53; have polyH55 := Poly.add polyH11 polyH54; have polyH56 := Poly.add polyH8 polyH1; have polyH57 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))))) (htv) (hsv); have polyH58 := Poly.add polyH56 polyH57; have polyH59 := Poly.add polyH58 polyH15; have polyH60 := Poly.mul polyH48 polyH59; have polyH61 := Poly.add polyH55 polyH60; have polyH62 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd x)), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))))) (Uniform.solveU) (@Uniform.pair ℕ Uniform.SolveInput Table (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveT Uniform.solveS) (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH61; have polyH63 := Poly.add polyH31 polyH62; have polyH64 := Poly.volumeNat polyH0; have polyH65 := Poly.add polyH8 polyH64; have polyH66 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))))) polyH1 polyH57; have polyH67 := Poly.add polyH65 polyH66; have polyH68 := Poly.add polyH67 polyH15; have polyH69 := Poly.mul polyH48 polyH68; have polyH70 := Poly.add polyH63 polyH69; have polyH71 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.SolveInput) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) (x : Uniform.SolveInput i) => (fun (x_1 : Universe i) => i) ((fun (x_1 : Uniform.SolveInput i) => Prod.fst x_1) x)) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst x, Prod.fst (Prod.snd (Prod.snd x)), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))))) (@Uniform.comp ℕ Uniform.SolveInput Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) Uniform.solveU Uniform.universeNumber) (@Uniform.pair ℕ Uniform.SolveInput Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd x)), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))))) Uniform.solveU (@Uniform.pair ℕ Uniform.SolveInput Table (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveT Uniform.solveS)) (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH70; have polyH72 := Poly.add polyH71 (hMarks); have polyH73 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Universe (n j_1)) => n j_1) ((fun (x : Uniform.SolveInput (n j_1)) => Prod.fst x) (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)), Prod.fst (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1), Prod.fst (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1))))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd (U j_1, M j_1, tab j_1, fs j_1, zs j_1, W j_1)))))))) polyH64 polyH66; have polyH74 := Poly.add polyH73 polyH15; have polyH75 := Poly.mul polyH23 polyH74; have polyH76 := Poly.add polyH72 polyH75; have polyH77 := Poly.of_le (fun (j_25 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.SolveInput) (fun (i : ℕ) => ℕ × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : Uniform.SolveInput i) => ((fun (x_1 : Universe i) => i) ((fun (x_1 : Uniform.SolveInput i) => Prod.fst x_1) x), Prod.fst x, Prod.fst (Prod.snd (Prod.snd x)), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))))) (fun (n_1 : ℕ) (x : ℕ × Universe n_1 × Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) => OAI.ThreeMachine.Algorithm.markings (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x))) (Prod.fst x)) (@Uniform.pair ℕ Uniform.SolveInput (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) (x : Uniform.SolveInput i) => (fun (x_1 : Universe i) => i) ((fun (x_1 : Uniform.SolveInput i) => Prod.fst x_1) x)) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst x, Prod.fst (Prod.snd (Prod.snd x)), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))))) (@Uniform.comp ℕ Uniform.SolveInput Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) Uniform.solveU Uniform.universeNumber) (@Uniform.pair ℕ Uniform.SolveInput Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst x) (fun (i : ℕ) (x : Uniform.SolveInput i) => (Prod.fst (Prod.snd (Prod.snd x)), OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))))) Uniform.solveU (@Uniform.pair ℕ Uniform.SolveInput Table (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => Prod.fst (Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Uniform.SolveInput n_1) => OAI.ThreeMachine.Algorithm.states (matrixRel (Prod.fst (Prod.snd x))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))) (Prod.fst (Prod.snd (Prod.snd (Prod.snd (Prod.snd x))))) (Prod.snd (Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))))) Uniform.solveT Uniform.solveS))) (Uniform.markings) (n j_25) ((U j_25, M j_25, tab j_25, fs j_25, zs j_25, W j_25))))) polyH76; exact Poly.lift polyH77 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

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

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.solveMarks := @OAI.ThreeMachine.StackCompiler.Costs.solveMarks
