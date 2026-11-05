-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.markingsStep
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:55:09.464445+00:00
-- url     : https://prove2.me/submissions/755cec98-9004-46d2-915d-dafd3abc5440

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_tryAdvance

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

end Block

namespace State
variable {J : Type} [Fintype J] [DecidableEq J] {r : J → J → Prop}

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

namespace Walk
variable {K : Type} {r : K → K → Prop}

end Walk
end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure
section DynamicProgram
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

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

end Poly
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler
namespace Poly
variable {J : Type u7} {s : J → ℕ} {d : ℕ}

variable {α : J → Type u8} {β : J → Type u9} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

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
  (
  have polyH0 := Poly.const (s) (10000000);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hl) polyH1;
  have polyH3 := Poly.mul polyH0 polyH2;
  have polyH4 := Poly.add (hT) (hx);
  have polyH5 := Poly.add polyH4 (he);
  have polyH6 := Poly.add polyH5 (ho);
  have polyH7 := Poly.add polyH6 (hV);
  have polyH8 := Poly.add polyH7 polyH1;
  have polyH9 := Poly.mul polyH3 polyH8;
  exact Poly.lift polyH9 (by first | decide +kernel | omega))

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
  (
  have polyH0 := Poly.const (s) (100000000);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hl) polyH1;
  have polyH3 := Poly.mul polyH0 polyH2;
  have polyH4 := Poly.add (hT) (hx);
  have polyH5 := Poly.add polyH4 (he);
  have polyH6 := Poly.add (hV) polyH1;
  have polyH7 := Poly.mul polyH2 polyH6;
  have polyH8 := Poly.add polyH5 polyH7;
  have polyH9 := Poly.add polyH8 polyH1;
  have polyH10 := Poly.mul polyH3 polyH9;
  exact Poly.lift polyH10 (by first | decide +kernel | omega))

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
-- module StateBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.Algorithm

theorem tableOf_length {K V : Type} (ks : List K) (f : K → Option V) :
    (tableOf ks f).length ≤ ks.length := List.length_filterMap_le _ _

end ThreeMachine.Algorithm

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

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

theorem volumeMarks (ms : ∀ j, Marks (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (ms j).length) l) (ht : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume (ms j)) (l+2*d) := by
  apply of_le (fun j => volume_marks_le (ms j) (ht j))
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
  (
  have polyH0 := Poly.const (s) (10);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega))

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

theorem volumeTryAdvance (tab : ∀ j, Table (n j)) (u : ∀ j, Algorithm.State (Fin (n j)) × Block (Fin (n j)))
    (v : ∀ j, Algorithm.State (Fin (n j))) (hn : Poly s n d)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly s (fun j => volume (Algorithm.tryAdvance (tab j) (u j) (v j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 100*(n j+2)^2) (2*d) from by (
  have polyH0 := Poly.const (s) (100);
  have polyH1 := Poly.const (s) (2);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j b h
  simp only [Algorithm.tryAdvance] at h
  split_ifs at h with hp
  · cases hc : Algorithm.lookup (tab j) ((v j).left \ (u j).1.upto) with
    | none => simp [hc] at h
    | some c =>
      have he : (u j).1.advance (u j).2 c = b := by simpa [hc] using h
      subst b
      exact volume_advance_le _ _ _ (hb j) (ht j _ c (Algorithm.lookup_mem hc))
  · simp at h

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
omit [∀ j, Coding (α j)] in
theorem volumeFirstResult (xs : ∀ j, List (α j)) (f : ∀ j, α j → Option (β j))
    (hv : Poly (fun p : ListPool xs => s p.1) (fun p => volume (f p.1 p.2.1)) d) :
    Poly s (fun j => volume (Algorithm.firstResult (f j) (xs j))) d := by
  obtain ⟨C,hC⟩ := hv
  apply volumeOption _ (powerBase s C d)
  intro j b hb
  obtain ⟨a,ha,h⟩ := Algorithm.firstResult_some hb
  have ht := hC ⟨j,⟨a,ha⟩⟩
  dsimp only at ht
  rw [h,volume_some] at ht
  omega

omit [∀ j, Coding (β j)] in
theorem volumeOptionOr (a b : ∀ j, Option (α j))
    (ha : Poly s (fun j => volume (a j)) d) (hb : Poly s (fun j => volume (b j)) e) :
    Poly s (fun j => volume ((a j).or (b j))) (Max.max d e) := by
  apply of_le (g := fun j => Max.max (volume (a j)) (volume (b j))) _ (ha.max hb)
  intro j
  cases a j <;> simp
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
open Algorithm
variable {J : Type} {s n : J → ℕ} {d l : ℕ}
theorem volumeStateList (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (sts j).length) l) :
    Poly s (fun j => volume (sts j)) (l+2*d) := by
  apply volumeList hl (show Poly s (fun j => 12*(n j+1)^2) (2*d) from by (
  have polyH0 := Poly.const (s) (12);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega)))
  intro j a _ha
  exact volume_state_le a

theorem volumeExpandBody (tab : ∀ j, Table (n j)) (ms : ∀ j, Marks (n j))
    (v : ∀ j, Algorithm.State (Fin (n j))) (hn : Poly s n d)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume ((Algorithm.lookup (ms j) (v j)).or
      (Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab j) u (v j)) (ms j)))) (2*d) := by
  have h₁ := volumeSmallLookup ms v hn hm
  have h₂ : Poly s (fun j => volume (Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab j) u (v j)) (ms j))) (2*d) := by
    apply volumeFirstResult
    exact volumeTryAdvance (fun p : ListPool ms => tab p.1) (fun p => p.2.1) (fun p => v p.1)
      (hn.precomp (fun p : ListPool ms => p.1)) (fun p => ht p.1)
      (fun p => hm p.1 _ _ p.2.2)
  simpa only [Nat.max_self] using volumeOptionOr _ _ h₁ h₂
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
theorem time_lookup_stateEq_le {n : ℕ}
    (xs : List (Algorithm.State (Fin n) × Algorithm.Block (Fin n))) (k : Algorithm.State (Fin n)) :
    (lookupA (β := fun n => Algorithm.Block (Fin n)) stateEq).time n (xs,k) ≤ 100000000000*(xs.length+1)*
      (Classical.choose Costs.stateEq*(n+2)^4+volume xs+volume k+1) := by
  apply time_lookup_le stateEq
  intro a _ha
  exact Classical.choose_spec Costs.stateEq ⟨n,(a.1,k)⟩
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
    (
  have polyH0 := Poly.const (fun (p_1 : Poly.Pool idx xs) => s (Sigma.fst p_1)) (10000000000);
  have polyH1 := Poly.add (ht) (hv);
  have polyH2 := Poly.add polyH1 (ha);
  have polyH3 := Poly.add polyH2 (hve);
  have polyH4 := Poly.const (fun (p_1 : Poly.Pool idx xs) => s (Sigma.fst p_1)) (1);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.mul polyH0 polyH5;
  exact Poly.lift polyH6 (by first | decide +kernel | omega))
  have hV : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume ((f (idx p.1) (p.2.1,e p.1)).map (fun b => (p.2.1,b)))) (Max.max v a) := by
    apply of_le (fun p : Pool idx xs => volume_tableBody (f (idx p.1) (p.2.1,e p.1)) p.2.1)
    (
  have polyH0 := Poly.add (hv) (ha);
  have polyH1 := Poly.const (fun (p_1 : Poly.Pool idx xs) => s (Sigma.fst p_1)) (1);
  have polyH2 := Poly.add polyH0 polyH1;
  exact Poly.lift polyH2 (by first | decide +kernel | omega))
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

theorem expandBody
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hml : Poly n (fun j => (ms j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly n (fun j => Uniform.expandBody.time (n j) (v j,(U j,(tab j,ms j)))) 90005 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hm
  have hTry := tryAdvance (fun p : Poly.ListPool ms => n p.1) (fun p => U p.1)
    (fun p => tab p.1) (fun p => p.2.1) (fun p => v p.1)
    (hl.precomp Sigma.fst) (fun p => ht p.1) (fun p => hm p.1 _ _ p.2.2)
  have hVolTry := Poly.volumeTryAdvance (fun p : Poly.ListPool ms => tab p.1)
    (fun p => p.2.1) (fun p => v p.1) ((Poly.size n).precomp Sigma.fst)
    (fun p => ht p.1) (fun p => hm p.1 _ _ p.2.2)
  have hLookup := Poly.volumeSmallLookup ms v (Poly.size n) hm
  have hFirst := Poly.volumeFirstResult ms (fun j u => Algorithm.tryAdvance (tab j) u (v j)) hVolTry
  have hpoolB := Poly.volumeSmallBlock (fun p : Poly.ListPool ms => p.2.1.2)
    ((Poly.size n).precomp Sigma.fst) (fun p => hm p.1 _ _ p.2.2)
  (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeState polyH0 (fun (j_1 : J) => v j_1);
  have polyH2 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, ms j_1)) (htv) (hmv);
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, tab j_1, ms j_1)) polyH2 polyH3;
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => (v j_1, U j_1, tab j_1, ms j_1)) polyH1 polyH4;
  have polyH6 := Poly.const (n) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH7;
  have polyH9 := Poly.add polyH4 polyH6;
  have polyH10 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_19) (Prod.snd (v j_19, U j_19, tab j_19, ms j_19))))) polyH9;
  have polyH11 := Poly.add polyH3 polyH6;
  have polyH12 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_19) (Prod.snd (Prod.snd (v j_19, U j_19, tab j_19, ms j_19)))))) polyH11;
  have polyH13 := Poly.add polyH10 polyH12;
  have polyH14 := Poly.const (n) (10);
  have polyH15 := Poly.const (n) (1);
  have polyH16 := Poly.add polyH3 polyH15;
  have polyH17 := Poly.mul polyH14 polyH16;
  have polyH18 := Poly.add polyH13 polyH17;
  have polyH19 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_19) (Prod.snd (v j_19, U j_19, tab j_19, ms j_19))))) polyH18;
  have polyH20 := Poly.add polyH8 polyH19;
  have polyH21 := Poly.add polyH4 polyH15;
  have polyH22 := Poly.mul polyH14 polyH21;
  have polyH23 := Poly.add polyH20 polyH22;
  have polyH24 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH23;
  have polyH25 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH7;
  have polyH26 := Poly.add polyH24 polyH25;
  have polyH27 := Poly.const (n) (20);
  have polyH28 := Poly.add polyH5 (hmv);
  have polyH29 := Poly.add polyH28 polyH1;
  have polyH30 := Poly.add polyH29 polyH15;
  have polyH31 := Poly.mul polyH27 polyH30;
  have polyH32 := Poly.add polyH26 polyH31;
  have polyH33 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH32;
  have polyH34 := Poly.const (n) (100000000000);
  have polyH35 := Poly.add (hml) polyH15;
  have polyH36 := Poly.mul polyH34 polyH35;
  have polyH37 := Poly.const (n) (Classical.choose Costs.stateEq);
  have polyH38 := Poly.base (n);
  have polyH39 := Poly.pow polyH38 (4);
  have polyH40 := Poly.mul polyH37 polyH39;
  have polyH41 := Poly.add polyH40 (hmv);
  have polyH42 := Poly.add polyH41 polyH1;
  have polyH43 := Poly.add polyH42 polyH15;
  have polyH44 := Poly.mul polyH36 polyH43;
  have polyH45 := Poly.of_le (fun (j_19 : J) => (@Uniform.time_lookup_stateEq_le (n j_19) (Prod.snd (Prod.snd (Prod.snd (v j_19, U j_19, tab j_19, ms j_19)))) (Prod.fst (v j_19, U j_19, tab j_19, ms j_19)))) polyH44;
  have polyH46 := Poly.add polyH33 polyH45;
  have polyH47 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) (hmv) polyH1;
  have polyH48 := Poly.add polyH47 polyH15;
  have polyH49 := Poly.mul polyH14 polyH48;
  have polyH50 := Poly.add polyH46 polyH49;
  have polyH51 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.lookupA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ _ _ Uniform.stateEq) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH50;
  have polyH52 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_19) (Prod.snd (v j_19, U j_19, tab j_19, ms j_19))))) polyH9;
  have polyH53 := Poly.add polyH8 polyH52;
  have polyH54 := Poly.add polyH53 polyH22;
  have polyH55 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH54;
  have polyH56 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ (n j_19) (Prod.snd (Prod.snd (v j_19, U j_19, tab j_19, ms j_19)))))) polyH11;
  have polyH57 := Poly.add polyH10 polyH56;
  have polyH58 := Poly.add polyH57 polyH17;
  have polyH59 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_19) (Prod.snd (v j_19, U j_19, tab j_19, ms j_19))))) polyH58;
  have polyH60 := Poly.add polyH8 polyH59;
  have polyH61 := Poly.add polyH60 polyH22;
  have polyH62 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH61;
  have polyH63 := Poly.add polyH62 polyH25;
  have polyH64 := Poly.add polyH5 (htv);
  have polyH65 := Poly.add polyH64 polyH1;
  have polyH66 := Poly.add polyH65 polyH15;
  have polyH67 := Poly.mul polyH27 polyH66;
  have polyH68 := Poly.add polyH63 polyH67;
  have polyH69 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Table) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH68;
  have polyH70 := Poly.add polyH55 polyH69;
  have polyH71 := Poly.add polyH5 polyH2;
  have polyH72 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) (htv) polyH1;
  have polyH73 := Poly.add polyH71 polyH72;
  have polyH74 := Poly.add polyH73 polyH15;
  have polyH75 := Poly.mul polyH27 polyH74;
  have polyH76 := Poly.add polyH70 polyH75;
  have polyH77 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (Universe) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH76;
  have polyH78 := Poly.add polyH24 polyH77;
  have polyH79 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) polyH2 polyH72;
  have polyH80 := Poly.add polyH28 polyH79;
  have polyH81 := Poly.add polyH80 polyH15;
  have polyH82 := Poly.mul polyH27 polyH81;
  have polyH83 := Poly.add polyH78 polyH82;
  have polyH84 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH83;
  have polyH85 := Poly.size (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => n (Sigma.fst q));
  have polyH86 := Poly.volumeState polyH85 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Sigma.snd q).1.1);
  have polyH87 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Sigma.snd q).1) polyH86 (hpoolB);
  have polyH88 := Poly.volumeUniverse polyH85 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => U (Sigma.fst q));
  have polyH89 := Poly.precomp (htv) (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => Sigma.fst q);
  have polyH90 := Poly.volumeState polyH85 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => v (Sigma.fst q));
  have polyH91 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))) polyH89 polyH90;
  have polyH92 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))) polyH88 polyH91;
  have polyH93 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))))) polyH87 polyH92;
  have polyH94 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => n (Sigma.fst q)) (2);
  have polyH95 := Poly.add polyH93 polyH94;
  have polyH96 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH95;
  have polyH97 := Poly.add polyH92 polyH94;
  have polyH98 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ (n (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH97;
  have polyH99 := Poly.add polyH96 polyH98;
  have polyH100 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => n (Sigma.fst q)) (10);
  have polyH101 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => n (Sigma.fst q)) (1);
  have polyH102 := Poly.add polyH92 polyH101;
  have polyH103 := Poly.mul polyH100 polyH102;
  have polyH104 := Poly.add polyH99 polyH103;
  have polyH105 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH104;
  have polyH106 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ (n (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH97;
  have polyH107 := Poly.add polyH91 polyH94;
  have polyH108 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ (n (Sigma.fst q)) (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))))))))) polyH107;
  have polyH109 := Poly.add polyH106 polyH108;
  have polyH110 := Poly.add polyH91 polyH101;
  have polyH111 := Poly.mul polyH100 polyH110;
  have polyH112 := Poly.add polyH109 polyH111;
  have polyH113 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (n (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH112;
  have polyH114 := Poly.add polyH96 polyH113;
  have polyH115 := Poly.add polyH114 polyH103;
  have polyH116 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH115;
  have polyH117 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH95;
  have polyH118 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ (n (Sigma.fst q)) (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))))))))) polyH107;
  have polyH119 := Poly.add polyH106 polyH118;
  have polyH120 := Poly.add polyH119 polyH111;
  have polyH121 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (n (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH120;
  have polyH122 := Poly.add polyH96 polyH121;
  have polyH123 := Poly.add polyH122 polyH103;
  have polyH124 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH123;
  have polyH125 := Poly.add polyH117 polyH124;
  have polyH126 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => n (Sigma.fst q)) (20);
  have polyH127 := Poly.add polyH93 polyH87;
  have polyH128 := Poly.add polyH127 polyH90;
  have polyH129 := Poly.add polyH128 polyH101;
  have polyH130 := Poly.mul polyH126 polyH129;
  have polyH131 := Poly.add polyH125 polyH130;
  have polyH132 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH131;
  have polyH133 := Poly.add polyH116 polyH132;
  have polyH134 := Poly.add polyH93 polyH89;
  have polyH135 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.snd (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH87 polyH90;
  have polyH136 := Poly.add polyH134 polyH135;
  have polyH137 := Poly.add polyH136 polyH101;
  have polyH138 := Poly.mul polyH126 polyH137;
  have polyH139 := Poly.add polyH133 polyH138;
  have polyH140 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (Table) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)))) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH139;
  have polyH141 := Poly.add polyH105 polyH140;
  have polyH142 := Poly.add polyH93 polyH88;
  have polyH143 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Prod.fst (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.snd (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH89 polyH135;
  have polyH144 := Poly.add polyH142 polyH143;
  have polyH145 := Poly.add polyH144 polyH101;
  have polyH146 := Poly.mul polyH126 polyH145;
  have polyH147 := Poly.add polyH141 polyH146;
  have polyH148 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (Universe) (fun (i : ℕ) => Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))))) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH147;
  have polyH149 := Poly.add polyH148 (hTry);
  have polyH150 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))))), Prod.fst (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.snd (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH88 polyH143;
  have polyH151 := Poly.add polyH150 polyH101;
  have polyH152 := Poly.mul polyH100 polyH151;
  have polyH153 := Poly.add polyH149 polyH152;
  have polyH154 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe (fun (i : ℕ) => Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)))))) (Uniform.tryAdvance) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q))), Prod.fst (Prod.snd (Prod.snd (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))), Prod.fst (v (Sigma.fst q), U (Sigma.fst q), tab (Sigma.fst q), ms (Sigma.fst q)))))))) polyH153;
  have polyH155 := @Poly.firstResultTime (ℕ) (J) (n) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) (fun (j_1 : J) => Prod.snd (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) (fun (n_1 : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × Universe n_1 × Table n_1 × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd x))) (Prod.fst x) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe (fun (i : ℕ) => Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)))))) Uniform.tryAdvance) (30003) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (0)) (Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (0))) (0 + Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (0))) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (0)) (Max.max (Max.max (Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (0)) (Max.max (Max.max (30000 + 2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (30000 + 2 * 1) (2 * 1)) (0)))) (0 + Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (0))) (Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (0)) (Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (0)) (Max.max (Max.max (Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (0)) (Max.max (Max.max (30000 + 2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (30000 + 2 * 1) (2 * 1)) (0)))) (0 + Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (Max.max (2 * 1) (2 * 1))) (2 * 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (30000 + 2 * 1)) (Max.max (Max.max (2 * 1) (2 * 1)) (2 * 1))) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (2 * 1)) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1)))) (2 * 1)) (Max.max (30000 + 2 * 1) (Max.max (Max.max (2 * 1) (2 * 1)) (2 * 1)))) (0))) (60002)) (0 + Max.max (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (Max.max (Max.max (2 * 1) (2 * 1)) (2 * 1)))) (0))) (30003 + 2 * 1) (Max.max (2 * 1) (Max.max (30000 + 2 * 1) (2 * 1))) (2 * 1) (hml) polyH154 (hmv) polyH79 (hVolTry);
  have polyH156 := Poly.add polyH84 polyH155;
  have polyH157 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (Prod.snd (v j_1, U j_1, tab j_1, ms j_1)), Prod.fst (Prod.snd (Prod.snd (v j_1, U j_1, tab j_1, ms j_1))), Prod.fst (v j_1, U j_1, tab j_1, ms j_1))) (hmv) polyH79;
  have polyH158 := Poly.add polyH157 polyH15;
  have polyH159 := Poly.mul polyH14 polyH158;
  have polyH160 := Poly.add polyH156 polyH159;
  have polyH161 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)))) (@Uniform.firstResultA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × Universe n_1 × Table n_1 × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd x))) (Prod.fst x) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe (fun (i : ℕ) => Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)))))) Uniform.tryAdvance)) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH160;
  have polyH162 := Poly.add polyH51 polyH161;
  have polyH163 := Poly.add polyH5 (hLookup);
  have polyH164 := Poly.add polyH163 (hFirst);
  have polyH165 := Poly.add polyH164 polyH15;
  have polyH166 := Poly.mul polyH27 polyH165;
  have polyH167 := Poly.add polyH162 polyH166;
  have polyH168 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (x_1 : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x_1)), Prod.fst x_1)) x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (x_1 : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst (a, Prod.snd x_1)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x_1))))) (Prod.fst x_1)) ((fun (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd x_1), Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.lookupA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ _ _ Uniform.stateEq)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)))) (@Uniform.firstResultA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × Universe n_1 × Table n_1 × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd x))) (Prod.fst x) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe (fun (i : ℕ) => Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)))))) Uniform.tryAdvance))) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH167;
  have polyH169 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × Universe (n j_1) × Table (n j_1) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_1, U j_1, tab j_1, ms j_1)), (fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) × Universe (n j_1) × Table (n j_1) × OAI.ThreeMachine.Algorithm.State (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1))) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × Universe (n j_1) × Table (n j_1) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_1)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_1)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_1, U j_1, tab j_1, ms j_1)))) (hLookup) (hFirst);
  have polyH170 := Poly.add polyH169 polyH6;
  have polyH171 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _ (n j_19) (((fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)), (fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × Universe (n j_19) × Table (n j_19) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19))))))) polyH170;
  have polyH172 := Poly.const (n) (10000);
  have polyH173 := Poly.add (hLookup) polyH15;
  have polyH174 := Poly.mul polyH172 polyH173;
  have polyH175 := Poly.of_le (fun (j_19 : J) => (@Uniform.time_test_le (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ (fun (i : ℕ) (x : Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) => Option.isSome x) (@Uniform.optionIsSome._proof_1 (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (n j_19) (Prod.fst ((fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)), (fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × Universe (n j_19) × Table (n j_19) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)))))) polyH174;
  have polyH176 := Poly.add polyH171 polyH175;
  have polyH177 := Poly.mul polyH14 polyH173;
  have polyH178 := Poly.add polyH176 polyH177;
  have polyH179 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i) × Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) => Option.isSome x) (@Uniform.fst ℕ (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (n j_19) (((fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)), (fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × Universe (n j_19) × Table (n j_19) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19))))))) polyH178;
  have polyH180 := Poly.add polyH179 polyH171;
  have polyH181 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _ (n j_19) (((fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)), (fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × Universe (n j_19) × Table (n j_19) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19))))))) polyH170;
  have polyH182 := Poly.add polyH180 polyH181;
  have polyH183 := Poly.const (n) (1000);
  have polyH184 := Poly.add polyH169 (hLookup);
  have polyH185 := Poly.add polyH184 (hFirst);
  have polyH186 := Poly.add polyH185 polyH15;
  have polyH187 := Poly.mul polyH183 polyH186;
  have polyH188 := Poly.add polyH182 polyH187;
  have polyH189 := Poly.of_le (fun (j_19 : J) => (@Uniform.time_ite_le (ℕ) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i) × Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _ (fun (i : ℕ) (x : Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i) × Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) => (fun (x_1 : Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) => Option.isSome x_1) (Prod.fst x)) (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i) × Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) => Option.isSome x) (@Uniform.fst ℕ (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _) (@Uniform.optionIsSome ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _)) (@Uniform.fst ℕ (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) (fun (i : ℕ) => Option ((fun (i_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i_1)) i)) _ _) (n j_19) (((fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)), (fun (x : List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) × Universe (n j_19) × Table (n j_19) × OAI.ThreeMachine.Algorithm.State (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19))) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) ((fun (x : OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × Universe (n j_19) × Table (n j_19) × List (OAI.ThreeMachine.Algorithm.State (Fin (n j_19)) × OAI.ThreeMachine.Algorithm.Block (Fin (n j_19)))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (v j_19, U j_19, tab j_19, ms j_19)))))) polyH188;
  have polyH190 := Poly.add polyH168 polyH189;
  have polyH191 := Poly.add polyH169 polyH15;
  have polyH192 := Poly.mul polyH14 polyH191;
  have polyH193 := Poly.add polyH190 polyH192;
  have polyH194 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i)) × Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => ((fun (x_1 : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x_1)), Prod.fst x_1)) x), (fun (x_1 : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst (a, Prod.snd x_1)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x_1))))) (Prod.fst x_1)) ((fun (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd x_1), Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst x_1)) x))) (fun (i : ℕ) (x : Option (OAI.ThreeMachine.Algorithm.Block (Fin i)) × Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) => Option.or (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (x_1 : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x_1)), Prod.fst x_1)) x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (fun (x_1 : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst (a, Prod.snd x_1)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x_1))))) (Prod.fst x_1)) ((fun (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x_1)), Prod.fst (Prod.snd x_1), Prod.fst (Prod.snd (Prod.snd x_1)), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.lookup (Prod.fst x) (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.lookupA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin n_1)) _ _ _ Uniform.stateEq)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.snd (Prod.snd (Prod.snd x)), Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.firstResult (fun (a : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x)) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _)))) (@Uniform.firstResultA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (n_1 : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × Universe n_1 × Table n_1 × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd x))) (Prod.fst x) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n_1 : ℕ) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd x), Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) × OAI.ThreeMachine.Algorithm.State (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe (fun (i : ℕ) => Table i × (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => (Prod.fst x, Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.fst ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) × Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × OAI.ThreeMachine.Algorithm.State (Fin i)) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) _ _)))))) Uniform.tryAdvance)))) (@Uniform.optionOrElse ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) _) (n j_19) ((v j_19, U j_19, tab j_19, ms j_19))))) polyH193;
  exact Poly.lift polyH194 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem expand (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (hml : Poly n (fun j => (ms j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly n (fun j => Uniform.expand.time (n j) (U j,(tab j,(sts j,ms j)))) 120008 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hm
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hBody := expandBody (fun p : Poly.ListPool sts => n p.1) (fun p => U p.1)
    (fun p => tab p.1) (fun p => ms p.1) (fun p => p.2.1)
    (hl.precomp Sigma.fst) (hml.precomp Sigma.fst) (fun p => ht p.1) (fun p => hm p.1)
  have hVolBody := Poly.volumeExpandBody (fun p : Poly.ListPool sts => tab p.1)
    (fun p => ms p.1) (fun p => p.2.1) ((Poly.size n).precomp Sigma.fst)
    (fun p => ht p.1) (fun p => hm p.1)
  have hVolBodyExact : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume (match Algorithm.lookup (ms p.1) p.2.1 with
        | some b => some b
        | none => Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab p.1) u p.2.1) (ms p.1))) 2 := by
    convert hVolBody using 1 <;> try rfl
    funext p
    cases Algorithm.lookup (ms p.1) p.2.1 <;> rfl
  have hVRun : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume (Uniform.eval Uniform.expandBody (n p.1)
        (p.2.1,(U p.1,(tab p.1,ms p.1))))) 2 := by
    convert hVolBodyExact using 1; try rfl
    funext p
    dsimp only [Uniform.eval]
    cases Algorithm.lookup (ms p.1) p.2.1 <;> rfl
  have hState : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume p.2.1) 2 := by (
  have polyH0 := Poly.size (fun (p_1 : Poly.ListPool sts) => n (Sigma.fst p_1));
  have polyH1 := Poly.volumeState polyH0 (fun (p_1 : Poly.ListPool sts) => (Sigma.snd p_1).1);
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have he : Poly n (fun j => volume (U j,(tab j,ms j))) 30005 := by (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, ms j_1)) (htv) (hmv);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (U j_1, tab j_1, ms j_1)) polyH1 polyH2;
  exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hTable := Poly.tableOfTime Uniform.expandBody n sts (fun j => (U j,(tab j,ms j)))
    hsl hBody hVRun hState hsv he
  have hExact : Poly n (fun j => Uniform.expandBody.tableOfA.time (n j)
      (sts j,(U j,(tab j,ms j)))) 120008 := hTable
  (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (sts j_1, ms j_1)) (hsv) (hmv);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, sts j_1, ms j_1)) (htv) polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, tab j_1, sts j_1, ms j_1)) polyH1 polyH3;
  have polyH5 := Poly.const (n) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH6;
  have polyH8 := Poly.add polyH3 polyH5;
  have polyH9 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ (n j_24) (Prod.snd (U j_24, tab j_24, sts j_24, ms j_24))))) polyH8;
  have polyH10 := Poly.add polyH2 polyH5;
  have polyH11 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Marks) _ _ (n j_24) (Prod.snd (Prod.snd (U j_24, tab j_24, sts j_24, ms j_24)))))) polyH10;
  have polyH12 := Poly.add polyH9 polyH11;
  have polyH13 := Poly.const (n) (10);
  have polyH14 := Poly.const (n) (1);
  have polyH15 := Poly.add polyH2 polyH14;
  have polyH16 := Poly.mul polyH13 polyH15;
  have polyH17 := Poly.add polyH12 polyH16;
  have polyH18 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (n j_24) (Prod.snd (U j_24, tab j_24, sts j_24, ms j_24))))) polyH17;
  have polyH19 := Poly.add polyH7 polyH18;
  have polyH20 := Poly.add polyH3 polyH14;
  have polyH21 := Poly.mul polyH13 polyH20;
  have polyH22 := Poly.add polyH19 polyH21;
  have polyH23 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH22;
  have polyH24 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH6;
  have polyH25 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ (n j_24) (Prod.snd (U j_24, tab j_24, sts j_24, ms j_24))))) polyH8;
  have polyH26 := Poly.add polyH7 polyH25;
  have polyH27 := Poly.add polyH26 polyH21;
  have polyH28 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH27;
  have polyH29 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Marks) _ _ (n j_24) (Prod.snd (Prod.snd (U j_24, tab j_24, sts j_24, ms j_24)))))) polyH10;
  have polyH30 := Poly.add polyH9 polyH29;
  have polyH31 := Poly.add polyH30 polyH16;
  have polyH32 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (Marks) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (n j_24) (Prod.snd (U j_24, tab j_24, sts j_24, ms j_24))))) polyH31;
  have polyH33 := Poly.add polyH7 polyH32;
  have polyH34 := Poly.add polyH33 polyH21;
  have polyH35 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (Marks) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH34;
  have polyH36 := Poly.add polyH28 polyH35;
  have polyH37 := Poly.const (n) (20);
  have polyH38 := Poly.add polyH4 (htv);
  have polyH39 := Poly.add polyH38 (hmv);
  have polyH40 := Poly.add polyH39 polyH14;
  have polyH41 := Poly.mul polyH37 polyH40;
  have polyH42 := Poly.add polyH36 polyH41;
  have polyH43 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (Table) (Marks) _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _))) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH42;
  have polyH44 := Poly.add polyH24 polyH43;
  have polyH45 := Poly.add polyH4 polyH1;
  have polyH46 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (U j_1, tab j_1, sts j_1, ms j_1)), Prod.snd (Prod.snd (Prod.snd (U j_1, tab j_1, sts j_1, ms j_1))))) (htv) (hmv);
  have polyH47 := Poly.add polyH45 polyH46;
  have polyH48 := Poly.add polyH47 polyH14;
  have polyH49 := Poly.mul polyH37 polyH48;
  have polyH50 := Poly.add polyH44 polyH49;
  have polyH51 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (Universe) (fun (i : ℕ) => Table i × Marks i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => (Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table Marks _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)))) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH50;
  have polyH52 := Poly.add polyH23 polyH51;
  have polyH53 := Poly.add polyH4 (hsv);
  have polyH54 := Poly.add polyH53 (he);
  have polyH55 := Poly.add polyH54 polyH14;
  have polyH56 := Poly.mul polyH37 polyH55;
  have polyH57 := Poly.add polyH52 polyH56;
  have polyH58 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × Marks i) _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => (Prod.fst x, Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Universe (fun (i : ℕ) => Table i × Marks i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => (Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table Marks _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _))))) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH57;
  have polyH59 := Poly.add polyH58 (hExact);
  have polyH60 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.snd (U j_1, tab j_1, sts j_1, ms j_1))), Prod.fst (U j_1, tab j_1, sts j_1, ms j_1), Prod.fst (Prod.snd (U j_1, tab j_1, sts j_1, ms j_1)), Prod.snd (Prod.snd (Prod.snd (U j_1, tab j_1, sts j_1, ms j_1))))) (hsv) (he);
  have polyH61 := Poly.add polyH60 polyH14;
  have polyH62 := Poly.mul polyH13 polyH61;
  have polyH63 := Poly.add polyH59 polyH62;
  have polyH64 := Poly.of_le (fun (j_24 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Universe i × Table i × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => (Prod.fst (Prod.snd (Prod.snd x)), Prod.fst x, Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd x)))) (fun (i : ℕ) (x : List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Universe i × Table i × Marks i) => OAI.ThreeMachine.Algorithm.tableOf (Prod.fst x) fun (a : OAI.ThreeMachine.Algorithm.State (Fin i)) => Uniform.expandBody.match_1 i (fun (x_1 : Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) => Option (OAI.ThreeMachine.Algorithm.Block (Fin i))) (OAI.ThreeMachine.Algorithm.lookup (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst (a, Prod.snd x))) (fun (s : OAI.ThreeMachine.Algorithm.Block (Fin i)) => Option.some s) fun (_ : Unit) => OAI.ThreeMachine.Algorithm.firstResult (fun (u : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd (a, Prod.snd x)))) u (Prod.fst (a, Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd (a, Prod.snd x))))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Universe i × Table i × Marks i) _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd (Prod.snd x))) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => (Prod.fst x, Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Universe (fun (i : ℕ) => Table i × Marks i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => (Prod.fst (Prod.snd x), Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table Marks _ _ _ (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd (Prod.snd x))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x : Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) => Prod.snd (Prod.snd x)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) Marks _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)))))) (@Uniform.tableOfA ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.Block (Fin i)) (fun (i : ℕ) => Universe i × Table i × Marks i) _ _ _ (fun (n_1 : ℕ) (x : OAI.ThreeMachine.Algorithm.State (Fin n_1) × Universe n_1 × Table n_1 × Marks n_1) => Uniform.expandBody.match_1 n_1 (fun (x_1 : Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) => Option (OAI.ThreeMachine.Algorithm.Block (Fin n_1))) (OAI.ThreeMachine.Algorithm.lookup (Prod.snd (Prod.snd (Prod.snd x))) (Prod.fst x)) (fun (s : OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => Option.some s) fun (_ : Unit) => OAI.ThreeMachine.Algorithm.firstResult (fun (u : OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1)) => OAI.ThreeMachine.Algorithm.tryAdvance (Prod.fst (Prod.snd (Prod.snd x))) u (Prod.fst x)) (Prod.snd (Prod.snd (Prod.snd x)))) Uniform.expandBody) (n j_24) ((U j_24, tab j_24, sts j_24, ms j_24))))) polyH63;
  exact Poly.lift polyH64 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}
theorem volumeExpand (tab : ∀ j, Table (n j)) (ms : ∀ j, Marks (n j))
    (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (sts j).length) l)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume (Algorithm.expand (tab j) (sts j) (ms j))) (l+2*d) := by
  have hb := volumeExpandBody (fun p : ListPool sts => tab p.1) (fun p => ms p.1)
    (fun p => p.2.1) (hn.precomp Sigma.fst) (fun p => ht p.1) (fun p => hm p.1)
  have hv : Poly (fun p : ListPool sts => s p.1) (fun p => volume
      (((Algorithm.lookup (ms p.1) p.2.1).or
        (Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab p.1) u p.2.1) (ms p.1))).map
        (fun b => (p.2.1,b)))) (2*d) := by
    have hs : Poly (fun p : ListPool sts => s p.1) (fun p => volume p.2.1) (2*d) :=
      volumeState (hn.precomp (fun p : ListPool sts => p.1)) (fun p => p.2.1)
    apply of_le (fun p : ListPool sts => volume_tableBody _ p.2.1)
    (
  have polyH0 := Poly.add (hb) (hs);
  have polyH1 := Poly.const (fun (p_1 : Poly.ListPool sts) => s (Sigma.fst p_1)) (1);
  have polyH2 := Poly.add polyH0 polyH1;
  exact Poly.lift polyH2 (by first | decide +kernel | omega))
  have h := volumeFilterMap (fun j : J => j) sts (fun j : J => (tab j,ms j))
    (f := fun _ x => ((Algorithm.lookup x.2.2 x.1).or
      (Algorithm.firstResult (fun u => Algorithm.tryAdvance x.2.1 u x.1) x.2.2)).map
      (fun b => (x.1,b))) hl hv
  convert h using 1
  funext j
  congr 1
  apply List.filterMap_congr
  intro a ha
  dsimp only
  cases Algorithm.lookup (ms j) a <;> rfl
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

theorem markingsStep (ms : ∀ j, Marks (n j))
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (hml : Poly n (fun j => (ms j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly n (fun j => Uniform.markingsStep.time (n j) ((U j,(tab j,sts j)),ms j)) 120008 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hm
  have hev := Poly.volumeExpand tab ms sts (Poly.size n) hsl ht hm
  have hel : Poly n (fun j => (Algorithm.expand (tab j) (sts j) (ms j)).length) 30003 :=
    Poly.of_le (fun j => Algorithm.tableOf_length _ _) hsl
  have h := expand n U tab ms sts hl hsl hml ht hm
  (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (tab j_1, sts j_1)) (htv) (hsv);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (U j_1, tab j_1, sts j_1)) polyH1 polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => ((U j_1, tab j_1, sts j_1), ms j_1)) polyH3 (hmv);
  have polyH5 := Poly.const (n) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Uniform.MarkEnv) (Marks) _ _ (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH6;
  have polyH8 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Marks) _ _ (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH6;
  have polyH9 := Poly.add polyH3 polyH5;
  have polyH10 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_19) (Prod.fst ((U j_19, tab j_19, sts j_19), ms j_19))))) polyH9;
  have polyH11 := Poly.add polyH8 polyH10;
  have polyH12 := Poly.const (n) (10);
  have polyH13 := Poly.const (n) (1);
  have polyH14 := Poly.add polyH3 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Universe) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH16;
  have polyH18 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_19) (Prod.fst ((U j_19, tab j_19, sts j_19), ms j_19))))) polyH9;
  have polyH19 := Poly.add polyH2 polyH5;
  have polyH20 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_19) (Prod.snd (Prod.fst ((U j_19, tab j_19, sts j_19), ms j_19)))))) polyH19;
  have polyH21 := Poly.add polyH18 polyH20;
  have polyH22 := Poly.add polyH2 polyH13;
  have polyH23 := Poly.mul polyH12 polyH22;
  have polyH24 := Poly.add polyH21 polyH23;
  have polyH25 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Table) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (n j_19) (Prod.fst ((U j_19, tab j_19, sts j_19), ms j_19))))) polyH24;
  have polyH26 := Poly.add polyH8 polyH25;
  have polyH27 := Poly.add polyH26 polyH15;
  have polyH28 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Table) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _)) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH27;
  have polyH29 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ (n j_19) (Prod.snd (Prod.fst ((U j_19, tab j_19, sts j_19), ms j_19)))))) polyH19;
  have polyH30 := Poly.add polyH18 polyH29;
  have polyH31 := Poly.add polyH30 polyH23;
  have polyH32 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (n j_19) (Prod.fst ((U j_19, tab j_19, sts j_19), ms j_19))))) polyH31;
  have polyH33 := Poly.add polyH8 polyH32;
  have polyH34 := Poly.add polyH33 polyH15;
  have polyH35 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _)) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH34;
  have polyH36 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Marks) _ _ (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH6;
  have polyH37 := Poly.add polyH35 polyH36;
  have polyH38 := Poly.const (n) (20);
  have polyH39 := Poly.add polyH4 (hsv);
  have polyH40 := Poly.add polyH39 (hmv);
  have polyH41 := Poly.add polyH40 polyH13;
  have polyH42 := Poly.mul polyH38 polyH41;
  have polyH43 := Poly.add polyH37 polyH42;
  have polyH44 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) (Marks) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.snd (Prod.snd (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH43;
  have polyH45 := Poly.add polyH28 polyH44;
  have polyH46 := Poly.add polyH4 (htv);
  have polyH47 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (Prod.fst ((U j_1, tab j_1, sts j_1), ms j_1))), Prod.snd ((U j_1, tab j_1, sts j_1), ms j_1))) (hsv) (hmv);
  have polyH48 := Poly.add polyH46 polyH47;
  have polyH49 := Poly.add polyH48 polyH13;
  have polyH50 := Poly.mul polyH38 polyH49;
  have polyH51 := Poly.add polyH45 polyH50;
  have polyH52 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (Table) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.snd (Prod.fst x))) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.snd (Prod.snd (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH51;
  have polyH53 := Poly.add polyH17 polyH52;
  have polyH54 := Poly.add polyH4 polyH1;
  have polyH55 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (Prod.fst ((U j_1, tab j_1, sts j_1), ms j_1))), Prod.snd (Prod.snd (Prod.fst ((U j_1, tab j_1, sts j_1), ms j_1))), Prod.snd ((U j_1, tab j_1, sts j_1), ms j_1))) (htv) polyH47;
  have polyH56 := Poly.add polyH54 polyH55;
  have polyH57 := Poly.add polyH56 polyH13;
  have polyH58 := Poly.mul polyH38 polyH57;
  have polyH59 := Poly.add polyH53 polyH58;
  have polyH60 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (Universe) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.fst x)) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.fst (Prod.snd (Prod.fst x)), Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.snd (Prod.fst x))) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.snd (Prod.snd (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _))) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH59;
  have polyH61 := Poly.add polyH60 (h);
  have polyH62 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.fst ((U j_1, tab j_1, sts j_1), ms j_1)), Prod.fst (Prod.snd (Prod.fst ((U j_1, tab j_1, sts j_1), ms j_1))), Prod.snd (Prod.snd (Prod.fst ((U j_1, tab j_1, sts j_1), ms j_1))), Prod.snd ((U j_1, tab j_1, sts j_1), ms j_1))) polyH1 polyH55;
  have polyH63 := Poly.add polyH62 polyH13;
  have polyH64 := Poly.mul polyH12 polyH63;
  have polyH65 := Poly.add polyH61 polyH64;
  have polyH66 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.fst (Prod.fst x), Prod.fst (Prod.snd (Prod.fst x)), Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1)) × Marks n_1) => OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.fst x)) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.fst (Prod.snd (Prod.fst x)), Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.snd (Prod.fst x))) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.snd (Prod.snd (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)))) (Uniform.expand) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH65;
  have polyH67 := Poly.add polyH7 polyH66;
  have polyH68 := Poly.add polyH4 polyH3;
  have polyH69 := Poly.add polyH68 (hev);
  have polyH70 := Poly.add polyH69 polyH13;
  have polyH71 := Poly.mul polyH38 polyH70;
  have polyH72 := Poly.add polyH67 polyH71;
  have polyH73 := Poly.of_le (fun (j_19 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Uniform.MarkEnv i × Marks i) (Uniform.MarkEnv) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.Block (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Uniform.MarkEnv n_1 × Marks n_1) => OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd (Prod.fst x))) (Prod.snd (Prod.snd (Prod.fst x))) (Prod.snd x)) (@Uniform.fst ℕ Uniform.MarkEnv Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) (fun (n_1 : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin n_1) × OAI.ThreeMachine.Algorithm.Block (Fin n_1))) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.fst (Prod.fst x), Prod.fst (Prod.snd (Prod.fst x)), Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (fun (n_1 : ℕ) (x : Universe n_1 × Table n_1 × List (OAI.ThreeMachine.Algorithm.State (Fin n_1)) × Marks n_1) => OAI.ThreeMachine.Algorithm.expand (Prod.fst (Prod.snd x)) (Prod.fst (Prod.snd (Prod.snd x))) (Prod.snd (Prod.snd (Prod.snd x)))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.fst x)) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.fst (Prod.snd (Prod.fst x)), Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Universe _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i)) × Marks i) _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.fst (Prod.snd (Prod.fst x))) (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => (Prod.snd (Prod.snd (Prod.fst x)), Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Table _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.fst ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.pair ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _ _ (fun (i : ℕ) (x : (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) => Prod.snd (Prod.snd (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) × Marks i) (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _) (@Uniform.snd ℕ Table (fun (i : ℕ) => List (OAI.ThreeMachine.Algorithm.State (Fin i))) _ _))) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Table i × List (OAI.ThreeMachine.Algorithm.State (Fin i))) Marks _ _)))) Uniform.expand) (n j_19) (((U j_19, tab j_19, sts j_19), ms j_19))))) polyH72;
  exact Poly.lift polyH73 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.markingsStep := @OAI.ThreeMachine.StackCompiler.Costs.markingsStep
