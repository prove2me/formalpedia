-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.familyAssignments
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:39:29.980907+00:00
-- url     : https://prove2.me/submissions/a0ccc669-3d82-4aa9-8dba-00b36709cdbf

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_ranks
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_atomSetsD

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false


section
-- module HierarchySoundness
namespace OAI

section

namespace ThreeMachine.Structure
section Soundness
variable {J A : Type} [Fintype J] {r : J → J → Prop} {atoms : A → Set J}

namespace FullBlock
variable {U V W : Set J}

end FullBlock

namespace SplitVertex
variable {W : Set J} {u v : SplitVertex r atoms W}

end SplitVertex

end Soundness
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section AtomicFamily
variable {J : Type} [Fintype J]

namespace Atomic

end Atomic
end AtomicFamily
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Ranks
variable {J K : Type} [Fintype J] [LinearOrder K]

theorem rankOfKey_bounds (key : J → K) (x : J) :
    1 ≤ rankOfKey key x ∧ rankOfKey key x ≤ Fintype.card J := by
  have hsub : Finset.univ.filter (fun y => key y < key x) ⊂ (Finset.univ : Finset J) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ Finset.univ.filter (fun y => key y < key x) := by rw [he]; exact Finset.mem_univ _
    exact lt_irrefl _ (Finset.mem_filter.mp hm).2
  have := Finset.card_lt_card hsub
  simp only [Finset.card_univ] at this
  dsimp [rankOfKey]
  omega

end Ranks

section IndexedRanks
variable {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]

theorem jobRank_bounds (x : Fin n) : 1 ≤ jobRank r x ∧ jobRank r x ≤ n := by
  simpa [jobRank] using rankOfKey_bounds (jobKey r) x

theorem reverseJobRank_bounds (x : Fin n) : 1 ≤ reverseJobRank r x ∧ reverseJobRank r x ≤ n := by
  have := jobRank_bounds r x
  dsimp [reverseJobRank]
  omega

end IndexedRanks
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ScheduleLayouts
variable {J : Type} [Fintype J]

end ScheduleLayouts
end ThreeMachine.Structure

end

end OAI
end

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

theorem volume_function_apply_le {α : Type u11} [Coding α] {n : ℕ} (f : Fin n → α) (v : Fin n) :
    volume (f v) ≤ volume f := volume_mem_le (List.mem_ofFn.mpr ⟨v,rfl⟩)

theorem nat_function_apply_le {n : ℕ} (f : Fin n → ℕ) (v : Fin n) : f v ≤ volume f := by
  have := volume_function_apply_le f v
  rw [volume_nat] at this
  omega

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

theorem time_functionGet_le {α : ℕ → Type u15} [∀ n, Coding (α n)]
    (n : ℕ) (f : Fin n → α n) (v : Fin n) :
    functionGet.time n (f,v) ≤ 1000000000*(n+1)*(volume f+n+1) :=
  time_functionGetAny_le (fun n => n) n f v

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

theorem volumeFunction {α : J → Type u17} [∀ j, Coding (α j)]
    (f : ∀ j, Fin (n j) → α j) (hn : Poly s n d)
    (hf : Poly (fun q : FinPool n => s q.1) (fun q => volume (f q.1 q.2)) v) :
    Poly s (fun j => volume (f j)) (d+v) := by
  obtain ⟨C,hC⟩ := hf
  apply of_le (g := fun j => 1+n j*(C*(s j+2)^v+1))
    (fun j => volume_function_le (f j) (C*(s j+2)^v) (fun a => hC ⟨j,a⟩))
  have : Poly s (fun j => C*(s j+2)^v) v := powerBase s C v
  simpa only [Nat.max_zero,Nat.zero_max] using (const s 1).add (hn.mul (this.add (const s 1)))

theorem natFunctionApply {f : ∀ j, Fin (n j) → ℕ} (a : ∀ j, Fin (n j))
    (hf : Poly s (fun j => volume (f j)) d) : Poly s (fun j => f j (a j)) d :=
  of_le (fun j => nat_function_apply_le (f j) (a j)) hf

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

theorem lengthAppend (xs ys : ∀ j, List (α j))
    (hx : Poly s (fun j => (xs j).length) d) (hy : Poly s (fun j => (ys j).length) e) :
    Poly s (fun j => (xs j ++ ys j).length) (Max.max d e) := by
  simpa only [List.length_append] using hx.add hy

theorem lengthRange (k : J → ℕ) (h : Poly s k d) :
    Poly s (fun j => (List.range (k j)).length) d := by simpa only [List.length_range] using h

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

end ThreeMachine.Algorithm

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

theorem lengthTriples (hn : Poly s n d) :
    Poly s (fun j => (Structure.tripleList (List.finRange (n j))).length) (3*d) := by
  apply of_le (fun j => Structure.tripleList_length (List.finRange (n j)))
  simp only [List.length_finRange]
  (have polyH0 := Poly.pow (hn) (3); exact Poly.lift polyH0 (by first | decide +kernel | omega))

theorem lengthAlphabet (hn : Poly s n d) :
    Poly s (fun j => (Structure.Atomic.alphabet (List.finRange (n j))).length) (3*d) := by
  apply of_le (fun j => Structure.Atomic.alphabet_length (List.finRange (n j)))
  simp only [Fintype.card_fin,List.length_finRange]
  (have polyH0 := Poly.const (s) (2); have polyH1 := Poly.const (s) (4); have polyH2 := Poly.add (hn) polyH0; have polyH3 := Poly.mul polyH1 polyH2; have polyH4 := Poly.add polyH0 polyH3; have polyH5 := Poly.const (s) (10); have polyH6 := Poly.pow (hn) (3); have polyH7 := Poly.mul polyH5 polyH6; have polyH8 := Poly.add polyH4 polyH7; exact Poly.lift polyH8 (by first | decide +kernel | omega))

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
theorem volumeBoundedFunction (f : ∀ j, Fin (n j) → ℕ)
    (hn : Poly s n d) (hB : Poly s B e) (hf : ∀ j v, f j v ≤ B j) :
    Poly s (fun j => volume (f j)) (d+e) := by
  apply of_le (g := fun j => 1+(n j)*(2*B j+1+1))
    (fun j => volume_function_le (f j) (2*B j+1) (by
        intro v; rw [volume_nat]; have := hf j v; omega))
  (have polyH0 := Poly.const (s) (1); have polyH1 := Poly.const (s) (2); have polyH2 := Poly.mul polyH1 (hB); have polyH3 := Poly.add polyH2 polyH0; have polyH4 := Poly.add polyH3 polyH0; have polyH5 := Poly.mul (hn) polyH4; have polyH6 := Poly.add polyH0 polyH5; exact Poly.lift polyH6 (by first | decide +kernel | omega))

theorem volumeRank (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.jobRank (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.jobRank (matrixRel (M j))) hn hn
    (fun j v => (Structure.jobRank_bounds (matrixRel (M j)) v).2)
  simpa only [two_mul] using h

theorem volumeReverseRank (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.reverseJobRank (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.reverseJobRank (matrixRel (M j))) hn hn
    (fun j v => (Structure.reverseJobRank_bounds (matrixRel (M j)) v).2)
  simpa only [two_mul] using h
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

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

theorem time_thresholdSets (upper : Bool) (n : ℕ) (x : Universe n × (Fin n → ℕ)) :
    (thresholdSets upper).time n x = ((thresholdN.pair id).comp (thresholdF upper).map).time n x := by
  cases upper <;> rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
theorem thresholdP (upper : Bool) (x : ∀ j, Uniform.ThresholdInput (n j))
    (hk : Poly n (fun j => (x j).2.1) 1) (hr : Poly n (fun j => volume (x j).2.2) 2) :
    Poly n (fun j => (Uniform.thresholdP upper).time (n j) (x j)) 4 := by
  cases upper <;> [(have polyH0 := Poly.size (n); have polyH1 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).1); have polyH2 := Poly.volumeNat (hk); have polyH3 := Poly.volumeProd (fun (j_1 : J) => (x j_1).2) polyH2 (hr); have polyH4 := Poly.volumeProd (fun (j_1 : J) => x j_1) polyH1 polyH3; have polyH5 := Poly.const (n) (2); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (n j_8) (x j_8)))) polyH6; have polyH8 := Poly.add polyH3 polyH5; have polyH9 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ (n j_8) (Prod.snd (x j_8))))) polyH8; have polyH10 := Poly.add polyH7 polyH9; have polyH11 := Poly.const (n) (10); have polyH12 := Poly.const (n) (1); have polyH13 := Poly.add polyH3 polyH12; have polyH14 := Poly.mul polyH11 polyH13; have polyH15 := Poly.add polyH10 polyH14; have polyH16 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (n j_8) (x j_8)))) polyH15; have polyH17 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ (n j_8) (Prod.snd (x j_8))))) polyH8; have polyH18 := Poly.add polyH7 polyH17; have polyH19 := Poly.add polyH18 polyH14; have polyH20 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _) (n j_8) (x j_8)))) polyH19; have polyH21 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ (n j_8) (x j_8)))) polyH6; have polyH22 := Poly.add polyH20 polyH21; have polyH23 := Poly.const (n) (20); have polyH24 := Poly.add polyH4 (hr); have polyH25 := Poly.add polyH24 polyH1; have polyH26 := Poly.add polyH25 polyH12; have polyH27 := Poly.mul polyH23 polyH26; have polyH28 := Poly.add polyH22 polyH27; have polyH29 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (n j_8) (x j_8)))) polyH28; have polyH30 := Poly.const (n) (1000000000); have polyH31 := Poly.add polyH0 polyH12; have polyH32 := Poly.mul polyH30 polyH31; have polyH33 := Poly.add (hr) polyH0; have polyH34 := Poly.add polyH33 polyH12; have polyH35 := Poly.mul polyH32 polyH34; have polyH36 := Poly.of_le (fun (j_8 : J) => (@Uniform.time_functionGet_le (fun (n_1 : ℕ) => ℕ) _ (n j_8) (Prod.snd (Prod.snd (x j_8))) (Prod.fst (x j_8)))) polyH35; have polyH37 := Poly.add polyH29 polyH36; have polyH38 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (x j_1)), Prod.fst (x j_1))) (hr) polyH1; have polyH39 := Poly.add polyH38 polyH12; have polyH40 := Poly.mul polyH11 polyH39; have polyH41 := Poly.add polyH37 polyH40; have polyH42 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (n_1 : ℕ) => ℕ) _) (n j_8) (x j_8)))) polyH41; have polyH43 := Poly.add polyH16 polyH42; have polyH44 := Poly.add polyH4 polyH2; have polyH45 := Poly.natFunctionApply (fun (j_1 : J) => Prod.fst (x j_1)) (hr); have polyH46 := Poly.volumeNat polyH45; have polyH47 := Poly.add polyH44 polyH46; have polyH48 := Poly.add polyH47 polyH12; have polyH49 := Poly.mul polyH23 polyH48; have polyH50 := Poly.add polyH43 polyH49; have polyH51 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.ThresholdInput) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.fst (Prod.snd x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.snd (Prod.snd x_1) (Prod.fst x_1)) (Uniform.thresholdB) (Uniform.thresholdA) (n j_8) (x j_8)))) polyH50; have polyH52 := Poly.add (hk) polyH45; have polyH53 := Poly.add polyH52 polyH12; have polyH54 := Poly.pow polyH53 (2); have polyH55 := Poly.mul polyH30 polyH54; have polyH56 := Poly.of_le (fun (j_8 : J) => (@Realizer.time_le_le (Prod.fst (Prod.snd (x j_8))) (Prod.snd (Prod.snd (x j_8)) (Prod.fst (x j_8))))) polyH55; have polyH57 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ × ℕ) (Bool) _ _ (fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) (Realizer.le) (n j_8) ((Prod.fst (Prod.snd (x j_8)), Prod.snd (Prod.snd (x j_8)) (Prod.fst (x j_8))))))) polyH56; have polyH58 := Poly.add polyH51 polyH57; have polyH59 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)), Prod.snd (Prod.snd (x j_1)) (Prod.fst (x j_1)))) polyH2 polyH46; have polyH60 := Poly.add polyH59 polyH12; have polyH61 := Poly.mul polyH11 polyH60; have polyH62 := Poly.add polyH58 polyH61; have polyH63 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.ThresholdInput) (fun (i : ℕ) => ℕ × ℕ) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Uniform.ThresholdInput i) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1) (Prod.fst x_1))) (fun (x_1 : ℕ) (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) (@Uniform.pair ℕ Uniform.ThresholdInput (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.fst (Prod.snd x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.snd (Prod.snd x_1) (Prod.fst x_1)) Uniform.thresholdB Uniform.thresholdA) (Realizer.uniform Realizer.le ℕ) (n j_8) (x j_8)))) polyH62; exact Poly.lift polyH63 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega)); (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).1); have polyH2 := Poly.volumeNat (hk); have polyH3 := Poly.volumeProd (fun (j_1 : J) => (x j_1).2) polyH2 (hr); have polyH4 := Poly.volumeProd (fun (j_1 : J) => x j_1) polyH1 polyH3; have polyH5 := Poly.const (n) (2); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ (n j_8) (x j_8)))) polyH6; have polyH8 := Poly.add polyH3 polyH5; have polyH9 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ (n j_8) (Prod.snd (x j_8))))) polyH8; have polyH10 := Poly.add polyH7 polyH9; have polyH11 := Poly.const (n) (10); have polyH12 := Poly.const (n) (1); have polyH13 := Poly.add polyH3 polyH12; have polyH14 := Poly.mul polyH11 polyH13; have polyH15 := Poly.add polyH10 polyH14; have polyH16 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _) (n j_8) (x j_8)))) polyH15; have polyH17 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ (n j_8) (x j_8)))) polyH6; have polyH18 := Poly.add polyH16 polyH17; have polyH19 := Poly.const (n) (20); have polyH20 := Poly.add polyH4 (hr); have polyH21 := Poly.add polyH20 polyH1; have polyH22 := Poly.add polyH21 polyH12; have polyH23 := Poly.mul polyH19 polyH22; have polyH24 := Poly.add polyH18 polyH23; have polyH25 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (n j_8) (x j_8)))) polyH24; have polyH26 := Poly.const (n) (1000000000); have polyH27 := Poly.add polyH0 polyH12; have polyH28 := Poly.mul polyH26 polyH27; have polyH29 := Poly.add (hr) polyH0; have polyH30 := Poly.add polyH29 polyH12; have polyH31 := Poly.mul polyH28 polyH30; have polyH32 := Poly.of_le (fun (j_8 : J) => (@Uniform.time_functionGet_le (fun (n_1 : ℕ) => ℕ) _ (n j_8) (Prod.snd (Prod.snd (x j_8))) (Prod.fst (x j_8)))) polyH31; have polyH33 := Poly.add polyH25 polyH32; have polyH34 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (x j_1)), Prod.fst (x j_1))) (hr) polyH1; have polyH35 := Poly.add polyH34 polyH12; have polyH36 := Poly.mul polyH11 polyH35; have polyH37 := Poly.add polyH33 polyH36; have polyH38 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (n_1 : ℕ) => ℕ) _) (n j_8) (x j_8)))) polyH37; have polyH39 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ (n j_8) (Prod.snd (x j_8))))) polyH8; have polyH40 := Poly.add polyH7 polyH39; have polyH41 := Poly.add polyH40 polyH14; have polyH42 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n_1 : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (n j_8) (x j_8)))) polyH41; have polyH43 := Poly.add polyH38 polyH42; have polyH44 := Poly.natFunctionApply (fun (j_1 : J) => Prod.fst (x j_1)) (hr); have polyH45 := Poly.volumeNat polyH44; have polyH46 := Poly.add polyH4 polyH45; have polyH47 := Poly.add polyH46 polyH2; have polyH48 := Poly.add polyH47 polyH12; have polyH49 := Poly.mul polyH19 polyH48; have polyH50 := Poly.add polyH43 polyH49; have polyH51 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.ThresholdInput) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.snd (Prod.snd x_1) (Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.fst (Prod.snd x_1)) (Uniform.thresholdA) (Uniform.thresholdB) (n j_8) (x j_8)))) polyH50; have polyH52 := Poly.add polyH44 (hk); have polyH53 := Poly.add polyH52 polyH12; have polyH54 := Poly.pow polyH53 (2); have polyH55 := Poly.mul polyH26 polyH54; have polyH56 := Poly.of_le (fun (j_8 : J) => (@Realizer.time_le_le (Prod.snd (Prod.snd (x j_8)) (Prod.fst (x j_8))) (Prod.fst (Prod.snd (x j_8))))) polyH55; have polyH57 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ × ℕ) (Bool) _ _ (fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 ≤ Prod.snd x_1)) (Realizer.le) (n j_8) ((Prod.snd (Prod.snd (x j_8)) (Prod.fst (x j_8)), Prod.fst (Prod.snd (x j_8))))))) polyH56; have polyH58 := Poly.add polyH51 polyH57; have polyH59 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (Prod.snd (x j_1)) (Prod.fst (x j_1)), Prod.fst (Prod.snd (x j_1)))) polyH45 polyH2; have polyH60 := Poly.add polyH59 polyH12; have polyH61 := Poly.mul polyH11 polyH60; have polyH62 := Poly.add polyH58 polyH61; have polyH63 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.ThresholdInput) (fun (i : ℕ) => ℕ × ℕ) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Uniform.ThresholdInput i) => (Prod.snd (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1))) (fun (x_1 : ℕ) (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 ≤ Prod.snd x_2)) (@Uniform.pair ℕ Uniform.ThresholdInput (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.snd (Prod.snd x_1) (Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.ThresholdInput n_1) => Prod.fst (Prod.snd x_1)) Uniform.thresholdA Uniform.thresholdB) (Realizer.uniform Realizer.le ℕ) (n j_8) (x j_8)))) polyH62; exact Poly.lift polyH63 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))]

theorem thresholdF (upper : Bool) (U : ∀ j, Universe (n j))
    (r : ∀ j, Fin (n j) → ℕ) (k : J → ℕ)
    (hk : Poly n k 1) (hr : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => (Uniform.thresholdF upper).time (n j) (k j,(U j,r j))) 5 := by
  have hp := thresholdP (fun p : Poly.ListPool (fun j => (Finset.univ : Finset (Fin (n j))).sort (· ≤ ·)) => n p.1)
    upper (fun p => (p.2.1,(k p.1,r p.1))) (hk.precomp Sigma.fst) (hr.precomp Sigma.fst)
  (have polyH0 := Poly.volumeNat (hk); have polyH1 := Poly.size (n); have polyH2 := Poly.volumeUniverse polyH1 (fun (j_1 : J) => U j_1); have polyH3 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH2 (hr); have polyH4 := Poly.volumeProd (fun (j_1 : J) => (k j_1, U j_1, r j_1)) polyH0 polyH3; have polyH5 := Poly.const (n) (2); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ (n j_11) ((k j_11, U j_11, r j_11))))) polyH6; have polyH8 := Poly.add polyH3 polyH5; have polyH9 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Fin i → ℕ) _ _ (n j_11) (Prod.snd (k j_11, U j_11, r j_11))))) polyH8; have polyH10 := Poly.add polyH7 polyH9; have polyH11 := Poly.const (n) (10); have polyH12 := Poly.const (n) (1); have polyH13 := Poly.add polyH3 polyH12; have polyH14 := Poly.mul polyH11 polyH13; have polyH15 := Poly.add polyH10 polyH14; have polyH16 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (n j_11) ((k j_11, U j_11, r j_11))))) polyH15; have polyH17 := Poly.add polyH2 polyH5; have polyH18 := Poly.add polyH16 polyH17; have polyH19 := Poly.add polyH2 polyH12; have polyH20 := Poly.mul polyH11 polyH19; have polyH21 := Poly.add polyH18 polyH20; have polyH22 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (Universe) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (Uniform.universeSet) (n j_11) ((k j_11, U j_11, r j_11))))) polyH21; have polyH23 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ (n j_11) ((k j_11, U j_11, r j_11))))) polyH6; have polyH24 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Fin i → ℕ) _ _ (n j_11) (Prod.snd (k j_11, U j_11, r j_11))))) polyH8; have polyH25 := Poly.add polyH7 polyH24; have polyH26 := Poly.add polyH25 polyH14; have polyH27 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (n j_11) ((k j_11, U j_11, r j_11))))) polyH26; have polyH28 := Poly.add polyH23 polyH27; have polyH29 := Poly.const (n) (20); have polyH30 := Poly.add polyH4 polyH0; have polyH31 := Poly.add polyH30 (hr); have polyH32 := Poly.add polyH31 polyH12; have polyH33 := Poly.mul polyH29 polyH32; have polyH34 := Poly.add polyH28 polyH33; have polyH35 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (n j_11) ((k j_11, U j_11, r j_11))))) polyH34; have polyH36 := Poly.add polyH22 polyH35; have polyH37 := Poly.volumeFinset polyH1 (fun (j_1 : J) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))); have polyH38 := Poly.add polyH4 polyH37; have polyH39 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1)))) polyH0 (hr); have polyH40 := Poly.add polyH38 polyH39; have polyH41 := Poly.add polyH40 polyH12; have polyH42 := Poly.mul polyH29 polyH41; have polyH43 := Poly.add polyH36 polyH42; have polyH44 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst (Prod.snd x))) (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => (Prod.fst x, Prod.snd (Prod.snd x))) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) Uniform.universeSet) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _))) (n j_11) ((k j_11, U j_11, r j_11))))) polyH43; have polyH45 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1)))) polyH37 polyH39; have polyH46 := Poly.add polyH45 polyH5; have polyH47 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (n j_11) (((fun (x : Universe (n j_11)) => @Finset.univ (Fin (n j_11)) (Fin.fintype (n j_11))) (Prod.fst (Prod.snd (k j_11, U j_11, r j_11))), Prod.fst (k j_11, U j_11, r j_11), Prod.snd (Prod.snd (k j_11, U j_11, r j_11))))))) polyH46; have polyH48 := Poly.add polyH37 polyH5; have polyH49 := Poly.add polyH47 polyH48; have polyH50 := Poly.add polyH37 polyH12; have polyH51 := Poly.mul polyH11 polyH50; have polyH52 := Poly.add polyH49 polyH51; have polyH53 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) (Uniform.setList) (n j_11) (((fun (x : Universe (n j_11)) => @Finset.univ (Fin (n j_11)) (Fin.fintype (n j_11))) (Prod.fst (Prod.snd (k j_11, U j_11, r j_11))), Prod.fst (k j_11, U j_11, r j_11), Prod.snd (Prod.snd (k j_11, U j_11, r j_11))))))) polyH52; have polyH54 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (n j_11) (((fun (x : Universe (n j_11)) => @Finset.univ (Fin (n j_11)) (Fin.fintype (n j_11))) (Prod.fst (Prod.snd (k j_11, U j_11, r j_11))), Prod.fst (k j_11, U j_11, r j_11), Prod.snd (Prod.snd (k j_11, U j_11, r j_11))))))) polyH46; have polyH55 := Poly.add polyH53 polyH54; have polyH56 := Poly.add polyH45 polyH37; have polyH57 := Poly.add polyH56 polyH39; have polyH58 := Poly.add polyH57 polyH12; have polyH59 := Poly.mul polyH29 polyH58; have polyH60 := Poly.add polyH55 polyH59; have polyH61 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) => (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) i (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) (n j_11) (((fun (x : Universe (n j_11)) => @Finset.univ (Fin (n j_11)) (Fin.fintype (n j_11))) (Prod.fst (Prod.snd (k j_11, U j_11, r j_11))), Prod.fst (k j_11, U j_11, r j_11), Prod.snd (Prod.snd (k j_11, U j_11, r j_11))))))) polyH60; have polyH62 := Poly.finsetCard polyH1 (fun (j_1 : J) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))); have polyH63 := Poly.lengthSort (fun (j_1 : J) => Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1)))) polyH62; have polyH64 := @Poly.filterTime (ℕ) (J) (n) (Fin) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (Finset.sort (Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1)))) fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2, Prod.snd ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1))))) (fun (j_1 : J) => Prod.snd (Finset.sort (Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1)))) fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2, Prod.snd ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1))))) (fun (n_1 : ℕ) (x : Uniform.ThresholdInput n_1) => Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd x) (Prod.fst x) ≤ Prod.fst (Prod.snd x) else Prod.fst (Prod.snd x) ≤ Prod.snd (Prod.snd x) (Prod.fst x))) (Uniform.thresholdP upper) (1) (4) (2 * 1) (Max.max (1) (2)) polyH63 (hp) polyH37 polyH39; have polyH65 := Poly.add polyH61 polyH64; have polyH66 := Poly.volumeProd (fun (j_1 : J) => (Finset.sort (Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1)))) fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2, Prod.snd ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (Prod.snd (k j_1, U j_1, r j_1))), Prod.fst (k j_1, U j_1, r j_1), Prod.snd (Prod.snd (k j_1, U j_1, r j_1))))) polyH37 polyH39; have polyH67 := Poly.add polyH66 polyH12; have polyH68 := Poly.mul polyH11 polyH67; have polyH69 := Poly.add polyH65 polyH68; have polyH70 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => List (Fin i) × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × ℕ × (Fin i → ℕ)) => (Finset.sort (Prod.fst x) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x)) (fun (i : ℕ) (x : List (Fin i) × ℕ × (Fin i → ℕ)) => List.filter (fun (a : Fin i) => Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd (a, Prod.snd x)) (Prod.fst (a, Prod.snd x)) ≤ Prod.fst (Prod.snd (a, Prod.snd x)) else Prod.fst (Prod.snd (a, Prod.snd x)) ≤ Prod.snd (Prod.snd (a, Prod.snd x)) (Prod.fst (a, Prod.snd x)))) (Prod.fst x)) (@Uniform.onFst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ _ (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) Uniform.setList) (@Uniform.filter ℕ Fin (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (fun (n_1 : ℕ) (x : Uniform.ThresholdInput n_1) => Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd x) (Prod.fst x) ≤ Prod.fst (Prod.snd x) else Prod.fst (Prod.snd x) ≤ Prod.snd (Prod.snd x) (Prod.fst x))) (Uniform.thresholdP upper)) (n j_11) (((fun (x : Universe (n j_11)) => @Finset.univ (Fin (n j_11)) (Fin.fintype (n j_11))) (Prod.fst (Prod.snd (k j_11, U j_11, r j_11))), Prod.fst (k j_11, U j_11, r j_11), Prod.snd (Prod.snd (k j_11, U j_11, r j_11))))))) polyH69; have polyH71 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_setFilter (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ (fun (n_1 : ℕ) (x : Uniform.ThresholdInput n_1) => Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd x) (Prod.fst x) ≤ Prod.fst (Prod.snd x) else Prod.fst (Prod.snd x) ≤ Prod.snd (Prod.snd x) (Prod.fst x))) (Uniform.thresholdP upper) (n j_11) (((fun (x : Universe (n j_11)) => @Finset.univ (Fin (n j_11)) (Fin.fintype (n j_11))) (Prod.fst (Prod.snd (k j_11, U j_11, r j_11))), Prod.fst (k j_11, U j_11, r j_11), Prod.snd (Prod.snd (k j_11, U j_11, r j_11))))))) polyH70; have polyH72 := Poly.add polyH44 polyH71; have polyH73 := Poly.add polyH45 polyH12; have polyH74 := Poly.mul polyH11 polyH73; have polyH75 := Poly.add polyH72 polyH74; have polyH76 := Poly.of_le (fun (j_11 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Finset (Fin i) × ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => ((fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst (Prod.snd x)), Prod.fst x, Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Finset (Fin n_1) × ℕ × (Fin n_1 → ℕ)) => {a ∈ Prod.fst x | Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd (a, Prod.snd x)) (Prod.fst (a, Prod.snd x)) ≤ Prod.fst (Prod.snd (a, Prod.snd x)) else Prod.fst (Prod.snd (a, Prod.snd x)) ≤ Prod.snd (Prod.snd (a, Prod.snd x)) (Prod.fst (a, Prod.snd x))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst (Prod.snd x))) (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => (Prod.fst x, Prod.snd (Prod.snd x))) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) Uniform.universeSet) (@Uniform.pair ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : ℕ × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)))) (@Uniform.setFilter (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ (fun (n_1 : ℕ) (x : Uniform.ThresholdInput n_1) => Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd x) (Prod.fst x) ≤ Prod.fst (Prod.snd x) else Prod.fst (Prod.snd x) ≤ Prod.snd (Prod.snd x) (Prod.fst x))) (Uniform.thresholdP upper)) (n j_11) ((k j_11, U j_11, r j_11))))) polyH75; exact Poly.lift polyH76 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem thresholdSets (upper : Bool) (U : ∀ j, Universe (n j))
    (r : ∀ j, Fin (n j) → ℕ) (hr : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => (Uniform.thresholdSets upper).time (n j) (U j,r j)) 6 := by
  have hk : Poly (fun p : Poly.ListPool (fun j => List.range (n j+2)) => n p.1)
      (fun p => p.2.1) 1 := by
    apply Poly.of_le (fun p => (Nat.le_of_lt (List.mem_range.mp p.2.2)))
    exact (Poly.base n).precomp Sigma.fst
  have hF := thresholdF (fun p : Poly.ListPool (fun j => List.range (n j+2)) => n p.1)
    upper (fun p => U p.1) (fun p => r p.1) (fun p => p.2.1) hk (hr.precomp Sigma.fst)
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1); have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH1 (hr); have polyH3 := Poly.const (n) (2); have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ (n j_10) ((U j_10, r j_10))))) polyH4; have polyH6 := Poly.add polyH1 polyH3; have polyH7 := Poly.const (n) (100000); have polyH8 := Poly.lengthFinRange polyH0; have polyH9 := Poly.const (n) (1); have polyH10 := Poly.add polyH8 polyH9; have polyH11 := Poly.mul polyH7 polyH10; have polyH12 := Poly.volumeFinRange polyH0; have polyH13 := Poly.add polyH12 polyH9; have polyH14 := Poly.mul polyH11 polyH13; have polyH15 := Poly.of_le (fun (j_10 : J) => (@Uniform.time_length_le (ℕ) (Fin) _ (n j_10) (List.finRange (n j_10)))) polyH14; have polyH16 := Poly.add polyH6 polyH15; have polyH17 := Poly.const (n) (10); have polyH18 := Poly.mul polyH17 polyH13; have polyH19 := Poly.add polyH16 polyH18; have polyH20 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (n j_10) (Prod.fst (U j_10, r j_10))))) polyH19; have polyH21 := Poly.add polyH5 polyH20; have polyH22 := Poly.add polyH1 polyH9; have polyH23 := Poly.mul polyH17 polyH22; have polyH24 := Poly.add polyH21 polyH23; have polyH25 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (Universe) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) (Uniform.universeNumber) (n j_10) ((U j_10, r j_10))))) polyH24; have polyH26 := Poly.const (n) (2 * volume (2) + 1); have polyH27 := Poly.const (n) (20); have polyH28 := Poly.mul polyH27 polyH2; have polyH29 := Poly.const (n) (50 * volume (2)); have polyH30 := Poly.add polyH28 polyH29; have polyH31 := Poly.const (n) (50); have polyH32 := Poly.add polyH30 polyH31; have polyH33 := Poly.mul polyH26 polyH32; have polyH34 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_constant (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ (ℕ) _ (2) (n j_10) ((U j_10, r j_10))))) polyH33; have polyH35 := Poly.add polyH25 polyH34; have polyH36 := Poly.volumeNat polyH0; have polyH37 := Poly.add polyH2 polyH36; have polyH38 := Poly.const (n) (volume (2)); have polyH39 := Poly.add polyH37 polyH38; have polyH40 := Poly.add polyH39 polyH9; have polyH41 := Poly.mul polyH27 polyH40; have polyH42 := Poly.add polyH35 polyH41; have polyH43 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => 2) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) Uniform.universeNumber) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ ℕ _ (2)) (n j_10) ((U j_10, r j_10))))) polyH42; have polyH44 := Poly.const (n) (10000000); have polyH45 := Poly.base (n); have polyH46 := Poly.add polyH45 polyH9; have polyH47 := Poly.pow polyH46 (2); have polyH48 := Poly.mul polyH44 polyH47; have polyH49 := Poly.of_le (fun (j_10 : J) => (@Realizer.time_add_le ((fun (x : Universe (n j_10)) => n j_10) (Prod.fst (U j_10, r j_10))) (2))) polyH48; have polyH50 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ × ℕ) (ℕ) _ _ (fun (x : ℕ × ℕ) => Prod.fst x + Prod.snd x) (Realizer.add) (n j_10) (((fun (x : Universe (n j_10)) => n j_10) (Prod.fst (U j_10, r j_10)), 2))))) polyH49; have polyH51 := Poly.add polyH43 polyH50; have polyH52 := Poly.volumeNat polyH3; have polyH53 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1)), 2)) polyH36 polyH52; have polyH54 := Poly.add polyH53 polyH9; have polyH55 := Poly.mul polyH17 polyH54; have polyH56 := Poly.add polyH51 polyH55; have polyH57 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => ((fun (x_1 : Universe i) => i) (Prod.fst x), 2)) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => 2) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) Uniform.universeNumber) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ ℕ _ (2))) (Realizer.uniform Realizer.add ℕ) (n j_10) ((U j_10, r j_10))))) polyH56; have polyH58 := Poly.const (n) (100000000000); have polyH59 := Poly.add polyH0 polyH3; have polyH60 := Poly.add polyH59 polyH9; have polyH61 := Poly.pow polyH60 (3); have polyH62 := Poly.mul polyH58 polyH61; have polyH63 := Poly.of_le (fun (j_10 : J) => (@Realizer.time_range_le ((fun (x : ℕ × ℕ) => Prod.fst x + Prod.snd x) ((fun (x : Universe (n j_10) × (Fin (n j_10) → ℕ)) => ((fun (x_1 : Universe (n j_10)) => n j_10) (Prod.fst x), 2)) (U j_10, r j_10))))) polyH62; have polyH64 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ) (List ℕ) _ _ (List.range) (Realizer.range) (n j_10) ((fun (x : ℕ × ℕ) => Prod.fst x + Prod.snd x) ((fun (x : Universe (n j_10) × (Fin (n j_10) → ℕ)) => ((fun (x_1 : Universe (n j_10)) => n j_10) (Prod.fst x), 2)) (U j_10, r j_10)))))) polyH63; have polyH65 := Poly.add polyH57 polyH64; have polyH66 := Poly.volumeNat polyH59; have polyH67 := Poly.add polyH66 polyH9; have polyH68 := Poly.mul polyH17 polyH67; have polyH69 := Poly.add polyH65 polyH68; have polyH70 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (x : ℕ) => ℕ) (fun (x : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) ((fun (x_1 : Universe i × (Fin i → ℕ)) => ((fun (x_2 : Universe i) => i) (Prod.fst x_1), 2)) x)) (fun (x : ℕ) => List.range) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => ((fun (x_1 : Universe i) => i) (Prod.fst x), 2)) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => 2) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _) Uniform.universeNumber) (@Uniform.constant ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ ℕ _ (2))) (Realizer.uniform Realizer.add ℕ)) (Realizer.uniform Realizer.range ℕ) (n j_10) ((U j_10, r j_10))))) polyH69; have polyH71 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ (n j_10) ((U j_10, r j_10))))) polyH4; have polyH72 := Poly.add polyH70 polyH71; have polyH73 := Poly.lengthRange (fun (j_1 : J) => n j_1 + 2) polyH45; have polyH74 := Poly.volumeNat (hk); have polyH75 := Poly.listVolume (fun (j_1 : J) => List.range (n j_1 + 2)) polyH73 polyH74; have polyH76 := Poly.add polyH2 polyH75; have polyH77 := Poly.add polyH76 polyH2; have polyH78 := Poly.add polyH77 polyH9; have polyH79 := Poly.mul polyH27 polyH78; have polyH80 := Poly.add polyH72 polyH79; have polyH81 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => List ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin n_1 → ℕ)) => List.range (n_1 + 2)) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => x) (Uniform.thresholdN) (@Uniform.id ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _) (n j_10) ((U j_10, r j_10))))) polyH80; have polyH82 := Poly.size (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => ℕ) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.range (n j_1 + 2), U j_1, r j_1)) => n (Sigma.fst q)); have polyH83 := Poly.volumeFinset polyH82 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => ℕ) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.range (n j_1 + 2), U j_1, r j_1)) => {v ∈ @Finset.univ (Fin (n (Sigma.fst q))) (Fin.fintype (n (Sigma.fst q))) | Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.range (n (Sigma.fst q) + 2), U (Sigma.fst q), r (Sigma.fst q)))) v ≤ Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.range (n (Sigma.fst q) + 2), U (Sigma.fst q), r (Sigma.fst q))) else Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.range (n (Sigma.fst q) + 2), U (Sigma.fst q), r (Sigma.fst q))) ≤ Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.range (n (Sigma.fst q) + 2), U (Sigma.fst q), r (Sigma.fst q)))) v) = Bool.true}); have polyH84 := @Poly.mapTime (ℕ) (J) (n) (fun (i : ℕ) => ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (List.range (n j_1 + 2), U j_1, r j_1)) (fun (j_1 : J) => Prod.snd (List.range (n j_1 + 2), U j_1, r j_1)) (fun (n_1 : ℕ) (x : ℕ × Universe n_1 × (Fin n_1 → ℕ)) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd x) v ≤ Prod.fst x else Prod.fst x ≤ Prod.snd (Prod.snd x) v) = Bool.true}) (Uniform.thresholdF upper) (1) (5) (1 + 1) (Max.max (2 * 1) (2)) (2 * 1) polyH73 (hF) polyH75 polyH2 polyH83; have polyH85 := Poly.add polyH81 polyH84; have polyH86 := Poly.volumeProd (fun (j_1 : J) => (List.range (n j_1 + 2), U j_1, r j_1)) polyH75 polyH2; have polyH87 := Poly.add polyH86 polyH9; have polyH88 := Poly.mul polyH17 polyH87; have polyH89 := Poly.add polyH85 polyH88; have polyH90 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (i : ℕ) => List ℕ × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (List.range (i + 2), x)) (fun (i : ℕ) (x : List ℕ × Universe i × (Fin i → ℕ)) => List.map (fun (a : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd (a, Prod.snd x)) v ≤ Prod.fst (a, Prod.snd x) else Prod.fst (a, Prod.snd x) ≤ Prod.snd (Prod.snd (a, Prod.snd x)) v) = Bool.true}) (Prod.fst x)) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => List ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1 × (Fin n_1 → ℕ)) => List.range (n_1 + 2)) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => x) Uniform.thresholdN (@Uniform.id ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _)) (@Uniform.map ℕ (fun (i : ℕ) => ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ _ (fun (n_1 : ℕ) (x : ℕ × Universe n_1 × (Fin n_1 → ℕ)) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Decidable.decide (if upper = Bool.true then Prod.snd (Prod.snd x) v ≤ Prod.fst x else Prod.fst x ≤ Prod.snd (Prod.snd x) v) = Bool.true}) (Uniform.thresholdF upper)) (n j_10) ((U j_10, r j_10))))) polyH89; have polyH91 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_thresholdSets (upper) (n j_10) ((U j_10, r j_10))))) polyH90; exact Poly.lift polyH91 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

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
theorem time_finEmpty (i : I) (xs : List (α i)) : finEmpty.time i xs = 2 := rfl
theorem time_finCons (k : ℕ) (i : I) (x : α i × (Fin k → α i)) :
    (finCons k).time i x = volume x+2 := rfl

theorem time_assignments_succ (k : ℕ) (i : I) (xs : List (α i)) :
    (assignments (k+1)).time i xs =
      (((id.pair (assignments k)).comp (assignmentsStep k))).time i xs := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (k : ℕ)

theorem assignmentsInner (ys : ∀ j, List (Fin k → Finset (Fin (n j))))
    (a : ∀ j, Finset (Fin (n j))) (hl : Poly n (fun j => (ys j).length) (3*k)) :
    Poly n (fun j => (Uniform.assignmentsInner (α := fun n => Finset (Fin n)) k).time (n j) (a j,ys j)) (6*k+5) := by
  have hv : Poly n (fun j => volume (ys j)) (3*k+2) := by (have polyH0 := Poly.const (fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => n (Sigma.fst q)) (k); have polyH1 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => k) => (fun (q_1 : Poly.ListPool fun (j_1 : J) => ys j_1) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => k) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q)); have polyH3 := Poly.volumeFunction (fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => (Sigma.snd q).1) polyH0 polyH2; have polyH4 := Poly.listVolume (fun (j_1 : J) => ys j_1) (hl) polyH3; exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hdegree :
      max
        (max
          (max (max (max (max (2 * 1) (3 * k + 2)) 0) (max (max (2 * 1) (3 * k + 2)) 0))
            (0 + max (max (max (max (2 * 1) (3 * k + 2)) (3 * k + 2)) (2 * 1)) 0))
          (3 * k + max 2 (max (3 * k + 2) (max (2 * 1) (3 * k + 2)))))
        (0 + max (max (3 * k + 2) (2 * 1)) 0) ≤ 6 * k + 5 := by omega
  (have polyH0 := Poly.size (n); have polyH1 := Poly.volumeFinset polyH0 (fun (j_1 : J) => a j_1); have polyH2 := Poly.volumeProd (fun (j_1 : J) => (a j_1, ys j_1)) polyH1 (hv); have polyH3 := Poly.const (n) (2); have polyH4 := Poly.add polyH2 polyH3; have polyH5 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _ (n j_10) ((a j_10, ys j_10))))) polyH4; have polyH6 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _ (n j_10) ((a j_10, ys j_10))))) polyH4; have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.const (n) (20); have polyH9 := Poly.add polyH2 (hv); have polyH10 := Poly.add polyH9 polyH1; have polyH11 := Poly.const (n) (1); have polyH12 := Poly.add polyH10 polyH11; have polyH13 := Poly.mul polyH8 polyH12; have polyH14 := Poly.add polyH7 polyH13; have polyH15 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _) (n j_10) ((a j_10, ys j_10))))) polyH14; have polyH16 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)) (k); have polyH17 := Poly.size (fun (q : Poly.FinPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => k) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH18 := Poly.volumeFinset polyH17 (fun (q : Poly.FinPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => k) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q)); have polyH19 := Poly.volumeFunction (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (Sigma.snd q).1) polyH16 polyH18; have polyH20 := Poly.size (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)); have polyH21 := Poly.volumeFinset polyH20 (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => a (Sigma.fst q)); have polyH22 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q))))) polyH19 polyH21; have polyH23 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)) (2); have polyH24 := Poly.add polyH22 polyH23; have polyH25 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))))))) polyH24; have polyH26 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))))))) polyH24; have polyH27 := Poly.add polyH25 polyH26; have polyH28 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)) (20); have polyH29 := Poly.add polyH22 polyH21; have polyH30 := Poly.add polyH29 polyH19; have polyH31 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)) (1); have polyH32 := Poly.add polyH30 polyH31; have polyH33 := Poly.mul polyH28 polyH32; have polyH34 := Poly.add polyH27 polyH33; have polyH35 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))))))) polyH34; have polyH36 := Poly.volumeProd (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))))) polyH21 polyH19; have polyH37 := Poly.add polyH36 polyH23; have polyH38 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (le_of_eq (@Uniform.time_finCons (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ (k) (n (Sigma.fst q)) ((Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q))))))))) polyH37; have polyH39 := Poly.add polyH35 polyH38; have polyH40 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)) (10); have polyH41 := Poly.add polyH36 polyH31; have polyH42 := Poly.mul polyH40 polyH41; have polyH43 := Poly.add polyH39 polyH42; have polyH44 := Poly.of_le (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _ _ (fun (i : ℕ) (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x) (Prod.snd x)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (@Uniform.finCons ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))))))) polyH43; have polyH45 := Poly.const (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q)) (k + 1); have polyH46 := Poly.size (fun (q : Poly.FinPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => k + 1) => (fun (q_1 : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH47 := Poly.volumeFinset polyH46 (fun (q : Poly.FinPool fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => k + 1) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst (Sigma.fst q)))) (Prod.fst ((fun (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst (Sigma.fst q)))) × (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.snd (a (Sigma.fst (Sigma.fst q)), ys (Sigma.fst (Sigma.fst q))), Prod.fst (a (Sigma.fst (Sigma.fst q)), ys (Sigma.fst (Sigma.fst q))))))) (Prod.snd ((fun (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst (Sigma.fst q)))) × (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst (Sigma.fst q)))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (Prod.snd (a (Sigma.fst (Sigma.fst q)), ys (Sigma.fst (Sigma.fst q))), Prod.fst (a (Sigma.fst (Sigma.fst q)), ys (Sigma.fst (Sigma.fst q))))))) (Sigma.snd q)); have polyH48 := Poly.volumeFunction (fun (q : @Poly.Pool ℕ J (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst q))) (Prod.fst ((fun (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst q))) × (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst q))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q)))))) (Prod.snd ((fun (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst q))) × (fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst q))) => (Prod.snd x, Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (a (Sigma.fst q), ys (Sigma.fst q)), Prod.fst (a (Sigma.fst q), ys (Sigma.fst q))))))) polyH45 polyH47; have polyH49 := @Poly.mapTime (ℕ) (J) (n) (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) (fun (j_1 : J) => Prod.snd (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) (fun (i : ℕ) (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (fun (x_1 : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (Prod.snd x_1, Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _ _ (fun (i : ℕ) (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x) (Prod.snd x)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (@Uniform.finCons ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k)) (3 * k) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (0 + 2 * 1) (2 * 1)) (0)) (Max.max (Max.max (0 + 2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (0 + 2 * 1) (2 * 1)) (2 * 1)) (0 + 2 * 1)) (0))) (Max.max (Max.max (2 * 1) (0 + 2 * 1)) (0))) (0 + Max.max (Max.max (2 * 1) (0 + 2 * 1)) (0))) (3 * k + 2) (2 * 1) (0 + 2 * 1) (hl) polyH44 (hv) polyH1 polyH48; have polyH50 := Poly.add polyH15 polyH49; have polyH51 := Poly.const (n) (10); have polyH52 := Poly.volumeProd (fun (j_1 : J) => (Prod.snd (a j_1, ys j_1), Prod.fst (a j_1, ys j_1))) (hv) polyH1; have polyH53 := Poly.add polyH52 polyH11; have polyH54 := Poly.mul polyH51 polyH53; have polyH55 := Poly.add polyH50 polyH54; have polyH56 := Poly.of_le (fun (j_10 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => List (Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _ _ (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => List.map (fun (a_1 : Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (fun (x_1 : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.cons k (fun (a_2 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (Prod.snd x_1, Prod.fst x_1)) (a_1, Prod.snd x))) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _)) (@Uniform.map ℕ (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (fun (x_1 : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (Prod.snd x_1, Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _ _ (fun (i : ℕ) (x : (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) × (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (Prod.snd x, Prod.fst x)) (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x) (Prod.snd x)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _) (@Uniform.finCons ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k))) (n j_10) ((a j_10, ys j_10))))) polyH55; exact Poly.lift polyH56 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem assignmentsStep (xs : ∀ j, List (Finset (Fin (n j))))
    (ys : ∀ j, List (Fin k → Finset (Fin (n j))))
    (hl : Poly n (fun j => (xs j).length) 3)
    (hL : Poly n (fun j => (ys j).length) (3*k)) :
    Poly n (fun j => (Uniform.assignmentsStep (α := fun n => Finset (Fin n)) k).time (n j) (xs j,ys j)) (9*k+10) := by
  have hv : Poly n (fun j => volume (ys j)) (3*k+2) := by (have polyH0 := Poly.const (fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => n (Sigma.fst q)) (k); have polyH1 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => k) => (fun (q_1 : Poly.ListPool fun (j_1 : J) => ys j_1) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => k) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q)); have polyH3 := Poly.volumeFunction (fun (q : Poly.ListPool fun (j_1 : J) => ys j_1) => (Sigma.snd q).1) polyH0 polyH2; have polyH4 := Poly.listVolume (fun (j_1 : J) => ys j_1) (hL) polyH3; exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hx : Poly n (fun j => volume (xs j)) 5 := by (have polyH0 := Poly.size (fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => n (Sigma.fst q)); have polyH1 := Poly.volumeFinset polyH0 (fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => (Sigma.snd q).1); have polyH2 := Poly.listVolume (fun (j_1 : J) => xs j_1) (hl) polyH1; exact Poly.lift polyH2 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hI := assignmentsInner (fun p : Poly.ListPool xs => n p.1) k
    (fun p => ys p.1) (fun p => p.2.1) (hL.precomp Sigma.fst)
  have hdegree : 3 + (3 * k + 2) +
      max (6 * k + 5) (max 5 (max (3 * k + 2) (3 + (3 * k + 2)))) ≤ 9 * k + 10 := by omega
  (have polyH0 := Poly.precomp (hL) (fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => Sigma.fst q); have polyH1 := Poly.lengthMap (fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) (f : Fin k → Finset (Fin (n (Sigma.fst q)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q)))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q)))) f) polyH0; have polyH2 := Poly.const (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => List.map (fun (f : Fin k → Finset (Fin (n (Sigma.fst q)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q)))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q)))) f) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q))))) => (fun (q_1 : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => n (Sigma.fst q_1)) (Sigma.fst q)) (k + 1); have polyH3 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => List.map (fun (f : Fin k → Finset (Fin (n (Sigma.fst q)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q)))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q)))) f) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q))))) => k + 1) => (fun (q_1 : Poly.ListPool fun (q_1 : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => List.map (fun (f : Fin k → Finset (Fin (n (Sigma.fst q_1)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q_1)))) (Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (xs (Sigma.fst q_1), ys (Sigma.fst q_1)))) f) (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (xs (Sigma.fst q_1), ys (Sigma.fst q_1))))) => (fun (q_2 : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => n (Sigma.fst q_2)) (Sigma.fst q_1)) (Sigma.fst q)); have polyH4 := Poly.volumeFinset polyH3 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => List.map (fun (f : Fin k → Finset (Fin (n (Sigma.fst q)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q)))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q)))) f) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q))))) => k + 1) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q)); have polyH5 := Poly.volumeFunction (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => List.map (fun (f : Fin k → Finset (Fin (n (Sigma.fst q)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q)))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q)))) f) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q))))) => (Sigma.snd q).1) polyH2 polyH4; have polyH6 := Poly.listVolume (fun (q : @Poly.Pool ℕ J (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) => List.map (fun (f : Fin k → Finset (Fin (n (Sigma.fst q)))) => @Fin.cons k (fun (a : Fin (k + 1)) => Finset (Fin (n (Sigma.fst q)))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q)))) f) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (xs (Sigma.fst q), ys (Sigma.fst q))))) polyH1 polyH5; have polyH7 := @Poly.flatMapTime (ℕ) (J) (n) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => Fin (k + 1) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (xs j_1, ys j_1)) (fun (j_1 : J) => Prod.snd (xs j_1, ys j_1)) (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × List (Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => List.map (fun (f : Fin k → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => @Fin.cons k (fun (a : Fin (k + 1)) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (Prod.fst x) f) (Prod.snd x)) (@Uniform.assignmentsInner ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k) (3) (6 * k + 5) (5) (3 * k + 2) (3 * k + (0 + 2 * 1)) (hl) (hI) (hx) (hv) polyH6; exact Poly.lift polyH7 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (xs : ∀ j, List (Finset (Fin (n j))))
theorem assignments (hl : Poly n (fun j => (xs j).length) 3) (k : ℕ) :
    Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) k).time (n j) (xs j)) (9*k+10) := by
  have hx : Poly n (fun j => volume (xs j)) 5 := by (have polyH0 := Poly.size (fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => n (Sigma.fst q)); have polyH1 := Poly.volumeFinset polyH0 (fun (q : Poly.ListPool fun (j_1 : J) => xs j_1) => (Sigma.snd q).1); have polyH2 := Poly.listVolume (fun (j_1 : J) => xs j_1) (hl) polyH1; exact Poly.lift polyH2 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  induction k with
  | zero =>
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) 0).time (n j) (xs j)) 10
    (have polyH0 := Poly.const (n) (2); have polyH1 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_finEmpty (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ (n j_8) (xs j_8)))) polyH0; have polyH2 := Poly.const (n) (0); have polyH3 := Poly.size (fun (q : Poly.FinPool fun (j_1 : J) => 0) => n (Sigma.fst q)); have polyH4 := Poly.volumeFinset polyH3 (fun (q : Poly.FinPool fun (j_1 : J) => 0) => @Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n (Sigma.fst q))) (Sigma.snd q)); have polyH5 := Poly.volumeFunction (fun (j_1 : J) => @Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_1))) polyH2 polyH4; have polyH6 := Poly.add polyH5 polyH0; have polyH7 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ (n j_8) (@Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_8)))))) polyH6; have polyH8 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_nil (ℕ) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _ (n j_8) (@Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_8)))))) polyH0; have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.const (n) (20); have polyH11 := Poly.add polyH5 polyH5; have polyH12 := Poly.const (n) (1); have polyH13 := Poly.add polyH11 polyH12; have polyH14 := Poly.add polyH13 polyH12; have polyH15 := Poly.mul polyH10 polyH14; have polyH16 := Poly.add polyH9 polyH15; have polyH17 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) _ _ _ (fun (i : ℕ) (x : Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => x) (fun (i : ℕ) (x : Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => @List.nil ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) (@Uniform.id ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _) (@Uniform.nil ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _) (n j_8) (@Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_8)))))) polyH16; have polyH18 := Poly.volumeProd (fun (j_1 : J) => (@Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_1)), @List.nil ((fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (n j_1)))) polyH5 polyH12; have polyH19 := Poly.add polyH18 polyH0; have polyH20 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_cons (ℕ) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ (n j_8) ((@Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_8)), @List.nil ((fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (n j_8))))))) polyH19; have polyH21 := Poly.add polyH17 polyH20; have polyH22 := Poly.const (n) (10); have polyH23 := Poly.add polyH18 polyH12; have polyH24 := Poly.mul polyH22 polyH23; have polyH25 := Poly.add polyH21 polyH24; have polyH26 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => (fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i × List ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) _ _ _ (fun (i : ℕ) (x : Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => (x, @List.nil ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i))) (fun (i : ℕ) (x : (fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i × List ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) => Prod.fst x :: Prod.snd x) (@Uniform.pair ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) _ _ _ (fun (i : ℕ) (x : Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => x) (fun (i : ℕ) (x : Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => @List.nil ((fun (i_1 : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i_1) i)) (@Uniform.id ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _) (@Uniform.nil ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _ _)) (@Uniform.cons ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _) (n j_8) (@Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) (n j_8)))))) polyH25; have polyH27 := Poly.add polyH1 polyH26; have polyH28 := Poly.add polyH5 polyH12; have polyH29 := Poly.mul polyH22 polyH28; have polyH30 := Poly.add polyH27 polyH29; have polyH31 := Poly.of_le (fun (j_8 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List ((fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) (fun (i : ℕ) => List (Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) _ _ _ (fun (i : ℕ) (x : List ((fun (n_1 : ℕ) => Finset (Fin n_1)) i)) => @Fin.elim0 ((fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (fun (i : ℕ) (a : Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) => a :: @List.nil (Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i)) (@Uniform.finEmpty ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _) (@Uniform.singleton ℕ (fun (i : ℕ) => Fin (0) → (fun (n_1 : ℕ) => Finset (Fin n_1)) i) _) (n j_8) (xs j_8)))) polyH30; exact Poly.lift polyH31 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  | succ k ih =>
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) (k+1)).time (n j) (xs j)) (9*(k+1)+10)
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) k).time (n j) (xs j)) (9*k+10) at ih
    have hL : Poly n (fun j => (Structure.assignments (xs j) k).length) (3*k) := by
      simpa only [Structure.assignments_length] using hl.pow k
    have hV : Poly n (fun j => volume (Structure.assignments (xs j) k)) (3*k+2) := by (have polyH0 := Poly.const (fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.Structure.assignments (xs j_1) k) => n (Sigma.fst q)) (k); have polyH1 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.Structure.assignments (xs j_1) k) => k) => (fun (q_1 : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.Structure.assignments (xs j_1) k) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.Structure.assignments (xs j_1) k) => k) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q)); have polyH3 := Poly.volumeFunction (fun (q : Poly.ListPool fun (j_1 : J) => OAI.ThreeMachine.Structure.assignments (xs j_1) k) => (Sigma.snd q).1) polyH0 polyH2; have polyH4 := Poly.listVolume (fun (j_1 : J) => OAI.ThreeMachine.Structure.assignments (xs j_1) k) (hL) polyH3; exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
    change Poly n (fun j => (Uniform.assignments (α := fun n => Finset (Fin n)) (k+1)).time (n j) (xs j)) (9*(k+1)+10)
    have hStep := assignmentsStep n k xs (fun j => Structure.assignments (xs j) k) hl hL
    have hdegree :
      max (max (max (max 5 (9 * k + 10)) (0 + max (max (max 5 5) (3 * k + 2)) 0)) (9 * k + 10))
        (0 + max (max 5 (3 * k + 2)) 0) ≤ 9 * (k + 1) + 10 := by omega
    (have polyH0 := Poly.const (n) (2); have polyH1 := Poly.add (hx) polyH0; have polyH2 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => List (Finset (Fin i))) _ (n j_14) (xs j_14)))) polyH1; have polyH3 := Poly.add polyH2 (ih); have polyH4 := Poly.const (n) (20); have polyH5 := Poly.add (hx) (hx); have polyH6 := Poly.add polyH5 (hV); have polyH7 := Poly.const (n) (1); have polyH8 := Poly.add polyH6 polyH7; have polyH9 := Poly.mul polyH4 polyH8; have polyH10 := Poly.add polyH3 polyH9; have polyH11 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Fin k → Finset (Fin i))) _ _ _ (fun (i : ℕ) (x : List (Finset (Fin i))) => x) (fun (i : ℕ) (xs_1 : List (Finset (Fin i))) => OAI.ThreeMachine.Structure.assignments xs_1 k) (@Uniform.id ℕ (fun (i : ℕ) => List (Finset (Fin i))) _) (@Uniform.assignments ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k) (n j_14) (xs j_14)))) polyH10; have polyH12 := Poly.add polyH11 (hStep); have polyH13 := Poly.const (n) (10); have polyH14 := Poly.volumeProd (fun (j_1 : J) => (xs j_1, OAI.ThreeMachine.Structure.assignments (xs j_1) k)) (hx) (hV); have polyH15 := Poly.add polyH14 polyH7; have polyH16 := Poly.mul polyH13 polyH15; have polyH17 := Poly.add polyH12 polyH16; have polyH18 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i)) × List (Fin k → Finset (Fin i))) (fun (i : ℕ) => List (Fin (k + 1) → Finset (Fin i))) _ _ _ (fun (i : ℕ) (x : List (Finset (Fin i))) => (x, OAI.ThreeMachine.Structure.assignments x k)) (fun (i : ℕ) (x : List (Finset (Fin i)) × List (Fin k → Finset (Fin i))) => List.flatMap (fun (a : Finset (Fin i)) => List.map (fun (f : Fin k → Finset (Fin i)) => @Fin.cons k (fun (a_1 : Fin (k + 1)) => Finset (Fin i)) a f) (Prod.snd x)) (Prod.fst x)) (@Uniform.pair ℕ (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Fin k → Finset (Fin i))) _ _ _ (fun (i : ℕ) (x : List (Finset (Fin i))) => x) (fun (i : ℕ) (xs_1 : List (Finset (Fin i))) => OAI.ThreeMachine.Structure.assignments xs_1 k) (@Uniform.id ℕ (fun (i : ℕ) => List (Finset (Fin i))) _) (@Uniform.assignments ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k)) (@Uniform.assignmentsStep ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) _ k) (n j_14) (xs j_14)))) polyH17; have polyH19 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_assignments_succ (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ (k) (n j_14) (xs j_14)))) polyH18; exact Poly.lift polyH19 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable {K : ℕ} (r : ∀ j, Fin K → Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_atomSets (n : ℕ) (x : Universe n × Matrix n) :
    atomSets.time n x = ((atomSetsC.pair atomSetsT).comp append |>.pair atomSetsD |>.comp append).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type}
theorem lengthThresholds (n : J → ℕ) (M : ∀ j, Matrix (n j)) (frame : Bool) :
    Poly n (fun j => ([Bool.false,true].flatMap (fun upper => (List.range (n j+2)).map
      (fun k => Finset.univ.filter (fun v => if upper then
        (if frame then reverseJobRank (matrixRel (M j)) else jobRank (matrixRel (M j))) v ≤ k
        else k ≤ (if frame then reverseJobRank (matrixRel (M j)) else jobRank (matrixRel (M j))) v)))).length) 1 := by
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,List.length_map,List.length_range]
  (have polyH0 := Poly.base (n); have polyH1 := Poly.add polyH0 polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem lengthCones (n : J → ℕ) (M : ∀ j, Matrix (n j)) (frame : Bool) (ks : List (Fin 5)) :
    Poly n (fun j => (ks.flatMap (fun k => ((tripleList (List.finRange (n j))).map Subtype.val).map
      (coneSet (M j) frame k))).length) 3 := by
  have htr := Poly.lengthTriples (Poly.size n)
  have he (j : J) :
      (ks.flatMap (fun k => ((tripleList (List.finRange (n j))).map Subtype.val).map
        (coneSet (M j) frame k))).length = ks.length*(tripleList (List.finRange (n j))).length := by
    simp [List.length_flatMap]
  apply Poly.of_le (fun j => (he j).le)
  (have polyH0 := Poly.const (n) (List.length ks); have polyH1 := Poly.mul polyH0 (htr); exact Poly.lift polyH1 (by first | decide +kernel | omega))

theorem thresholds (frame : Bool) :
    Poly (fun x : Σ n, Universe n × Matrix n => x.1)
      (fun x => (Uniform.thresholds frame).time x.1 x.2) 6 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let r (x : Σ n, Universe n × Matrix n) :=
    if frame then Structure.reverseJobRank (matrixRel x.2.2) else Structure.jobRank (matrixRel x.2.2)
  have hv : Poly n (fun x => volume (r x)) 2 := by
    cases frame
    · exact Poly.volumeRank (fun x : Σ n, Universe n × Matrix n => x.2.2) (Poly.size n)
    · exact Poly.volumeReverseRank (fun x : Σ n, Universe n × Matrix n => x.2.2) (Poly.size n)
  have hF := thresholdSets n Bool.false (fun x => x.2.1) r hv
  have hT := thresholdSets n true (fun x => x.2.1) r hv
  (have polyH0 := Poly.size (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1); have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.1); have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_8 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_8) (Sigma.snd x_8)))) polyH5; have polyH7 := Poly.reparam (@Costs.ranks (frame)) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH8 := Poly.add polyH6 polyH7; have polyH9 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (20); have polyH10 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Sigma.snd x_1).1); have polyH11 := Poly.add polyH3 polyH10; have polyH12 := Poly.add polyH11 (hv); have polyH13 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (1); have polyH14 := Poly.add polyH12 polyH13; have polyH15 := Poly.mul polyH9 polyH14; have polyH16 := Poly.add polyH8 polyH15; have polyH17 := Poly.of_le (fun (x_8 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.ranks frame) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH16; have polyH18 := Poly.add (hF) (hT); have polyH19 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1))))) polyH10 (hv); have polyH20 := Poly.base (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1); have polyH21 := Poly.lengthRange (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1 + 2) polyH20; have polyH22 := Poly.lengthMap (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.false = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) polyH21; have polyH23 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.false = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)); have polyH24 := Poly.volumeFinset polyH23 (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.false = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) => (Sigma.snd q).1); have polyH25 := Poly.listVolume (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.false = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) polyH22 polyH24; have polyH26 := Poly.add polyH19 polyH25; have polyH27 := Poly.lengthMap (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.true = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) polyH21; have polyH28 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.true = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)); have polyH29 := Poly.volumeFinset polyH28 (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.true = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) => (Sigma.snd q).1); have polyH30 := Poly.listVolume (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.true = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) polyH27 polyH29; have polyH31 := Poly.add polyH26 polyH30; have polyH32 := Poly.add polyH31 polyH13; have polyH33 := Poly.mul polyH9 polyH32; have polyH34 := Poly.add polyH18 polyH33; have polyH35 := Poly.of_le (fun (x_8 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ)) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | if Bool.false = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (n_1 + 2))) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ)) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | if Bool.true = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (n_1 + 2))) (Uniform.thresholdSets Bool.false) (Uniform.thresholdSets Bool.true) (Sigma.fst x_8) ((Prod.fst (Sigma.snd x_8), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_8))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_8)))))))) polyH34; have polyH36 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (100000); have polyH37 := Poly.add polyH22 polyH13; have polyH38 := Poly.mul polyH36 polyH37; have polyH39 := Poly.add polyH25 polyH30; have polyH40 := Poly.add polyH39 polyH13; have polyH41 := Poly.mul polyH38 polyH40; have polyH42 := Poly.of_le (fun (x_8 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (@Uniform.time_append_le (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (Sigma.fst x_8) (List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_8)) (Fin.fintype (Sigma.fst x_8)) | if Bool.false = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_8), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_8))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_8)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_8), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_8))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_8)))) v}) (List.range (Sigma.fst x_8 + 2))) (List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_8)) (Fin.fintype (Sigma.fst x_8)) | if Bool.true = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_8), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_8))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_8)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_8), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_8))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_8)))) v}) (List.range (Sigma.fst x_8 + 2))))) polyH41; have polyH43 := Poly.add polyH35 polyH42; have polyH44 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (10); have polyH45 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.false = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2)), List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if Bool.true = Bool.true then Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ Prod.snd (Prod.fst (Sigma.snd x_1), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2)))) polyH25 polyH30; have polyH46 := Poly.add polyH45 polyH13; have polyH47 := Poly.mul polyH44 polyH46; have polyH48 := Poly.add polyH43 polyH47; have polyH49 := Poly.of_le (fun (x_8 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × (Fin i → ℕ)) => (List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if Bool.false = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (i + 2)), List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if Bool.true = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (i + 2)))) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ)) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | if Bool.false = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (n_1 + 2))) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ)) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | if Bool.true = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (n_1 + 2))) (Uniform.thresholdSets Bool.false) (Uniform.thresholdSets Bool.true)) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _) (Sigma.fst x_8) ((Prod.fst (Sigma.snd x_8), if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_8))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_8)))))))) polyH48; have polyH50 := Poly.add polyH17 polyH49; have polyH51 := Poly.add polyH19 polyH13; have polyH52 := Poly.mul polyH44 polyH51; have polyH53 := Poly.add polyH50 polyH52; have polyH54 := Poly.of_le (fun (x_8 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1)))) (fun (i : ℕ) (x_1 : Universe i × (Fin i → ℕ)) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × (Fin i → ℕ)) => (List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if Bool.false = Bool.true then Prod.snd x_2 v ≤ k else k ≤ Prod.snd x_2 v}) (List.range (i + 2)), List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if Bool.true = Bool.true then Prod.snd x_2 v ≤ k else k ≤ Prod.snd x_2 v}) (List.range (i + 2)))) x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => if frame = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.ranks frame)) (@Uniform.comp ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × (Fin i → ℕ)) => (List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if Bool.false = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (i + 2)), List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if Bool.true = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (i + 2)))) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ)) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | if Bool.false = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (n_1 + 2))) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ)) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | if Bool.true = Bool.true then Prod.snd x_1 v ≤ k else k ≤ Prod.snd x_1 v}) (List.range (n_1 + 2))) (Uniform.thresholdSets Bool.false) (Uniform.thresholdSets Bool.true)) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _)) (Sigma.fst x_8) (Sigma.snd x_8)))) polyH53; exact Poly.lift polyH54 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem atomSetsC : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSetsC.time x.1 x.2) 3 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1); have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.1); have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH7 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_setEmpty (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2))))) polyH4; have polyH8 := Poly.add polyH6 polyH7; have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (10); have polyH10 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (Sigma.snd x_1).1); have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (1); have polyH12 := Poly.add polyH10 polyH11; have polyH13 := Poly.mul polyH9 polyH12; have polyH14 := Poly.add polyH8 polyH13; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => ∅) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.setEmpty) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH14; have polyH16 := Poly.add polyH10 polyH4; have polyH17 := Poly.add polyH6 polyH16; have polyH18 := Poly.add polyH17 polyH13; have polyH19 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.universeSet) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH18; have polyH20 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_nil (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH4; have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (20); have polyH23 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))); have polyH24 := Poly.add polyH3 polyH23; have polyH25 := Poly.add polyH24 polyH11; have polyH26 := Poly.add polyH25 polyH11; have polyH27 := Poly.mul polyH22 polyH26; have polyH28 := Poly.add polyH21 polyH27; have polyH29 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => @List.nil (Finset (Fin i))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeSet) (@Uniform.nil ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH28; have polyH30 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), @List.nil (Finset (Fin (Sigma.fst x_1))))) polyH23 polyH11; have polyH31 := Poly.add polyH30 polyH4; have polyH32 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_cons (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), @List.nil (Finset (Fin (Sigma.fst x_2)))))))) polyH31; have polyH33 := Poly.add polyH29 polyH32; have polyH34 := Poly.add polyH30 polyH11; have polyH35 := Poly.mul polyH9 polyH34; have polyH36 := Poly.add polyH33 polyH35; have polyH37 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), @List.nil (Finset (Fin i)))) (fun (i : ℕ) (x_1 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => @List.nil (Finset (Fin i))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeSet) (@Uniform.nil ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i)) _ _)) (@Uniform.cons ℕ (fun (i : ℕ) => Finset (Fin i)) _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH36; have polyH38 := Poly.add polyH15 polyH37; have polyH39 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => ∅); have polyH40 := Poly.add polyH3 polyH39; have polyH41 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (0); have polyH42 := Poly.lengthCons (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1))) polyH41; have polyH43 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1)) :: Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH44 := Poly.volumeFinset polyH43 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1)) :: Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1))) => (Sigma.snd q).1); have polyH45 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1)) :: Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1))) polyH42 polyH44; have polyH46 := Poly.add polyH40 polyH45; have polyH47 := Poly.add polyH46 polyH11; have polyH48 := Poly.mul polyH22 polyH47; have polyH49 := Poly.add polyH38 polyH48; have polyH50 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Universe i) => ∅) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_3 :: Prod.snd x_3) ((fun (x_3 : Universe i × Matrix i) => ((fun (x_4 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_3), @List.nil (Finset (Fin i)))) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => ∅) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.setEmpty) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), @List.nil (Finset (Fin i)))) (fun (i : ℕ) (x_1 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => @List.nil (Finset (Fin i))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeSet) (@Uniform.nil ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i)) _ _)) (@Uniform.cons ℕ (fun (i : ℕ) => Finset (Fin i)) _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH49; have polyH51 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => ((fun (x_2 : Universe (Sigma.fst x_1)) => ∅) (Prod.fst (Sigma.snd x_1)), (fun (x_2 : Finset (Fin (Sigma.fst x_1)) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_2 :: Prod.snd x_2) ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), @List.nil (Finset (Fin (Sigma.fst x_1))))) (Sigma.snd x_1)))) polyH39 polyH45; have polyH52 := Poly.add polyH51 polyH4; have polyH53 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_cons (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => ∅) (Prod.fst (Sigma.snd x_2)), (fun (x_1 : Finset (Fin (Sigma.fst x_2)) × List (Finset (Fin (Sigma.fst x_2)))) => Prod.fst x_1 :: Prod.snd x_1) ((fun (x_1 : Universe (Sigma.fst x_2) × Matrix (Sigma.fst x_2)) => ((fun (x_3 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst x_1), @List.nil (Finset (Fin (Sigma.fst x_2))))) (Sigma.snd x_2))))))) polyH52; have polyH54 := Poly.add polyH50 polyH53; have polyH55 := Poly.add polyH51 polyH11; have polyH56 := Poly.mul polyH9 polyH55; have polyH57 := Poly.add polyH54 polyH56; have polyH58 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (x_3 : Universe i) => ∅) (Prod.fst x_1), (fun (x_3 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_3 :: Prod.snd x_3) ((fun (x_3 : Universe i × Matrix i) => ((fun (x_4 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_3), @List.nil (Finset (Fin i)))) x_1))) (fun (i : ℕ) (x_1 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Universe i) => ∅) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_3 :: Prod.snd x_3) ((fun (x_3 : Universe i × Matrix i) => ((fun (x_4 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_3), @List.nil (Finset (Fin i)))) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => ∅) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.setEmpty) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), @List.nil (Finset (Fin i)))) (fun (i : ℕ) (x_1 : Finset (Fin i) × List (Finset (Fin i))) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => @List.nil (Finset (Fin i))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.universeSet) (@Uniform.nil ℕ (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Finset (Fin i)) _ _)) (@Uniform.cons ℕ (fun (i : ℕ) => Finset (Fin i)) _))) (@Uniform.cons ℕ (fun (i : ℕ) => Finset (Fin i)) _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH57; exact Poly.lift polyH58 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem atomSetsT : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSetsT.time x.1 x.2) 6 := by
  have hF := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) Bool.false
  have hT := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) true
  (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.thresholds (Bool.false)) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.reparam (@Costs.thresholds (Bool.true)) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (20); have polyH5 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.1); have polyH6 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.2); have polyH7 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2) polyH5 polyH6; have polyH8 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true]) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH9 := Poly.volumeFinset polyH8 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true]) => (Sigma.snd q).1); have polyH10 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true]) (hF) polyH9; have polyH11 := Poly.add polyH7 polyH10; have polyH12 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true]) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH13 := Poly.volumeFinset polyH12 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true]) => (Sigma.snd q).1); have polyH14 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true]) (hT) polyH13; have polyH15 := Poly.add polyH11 polyH14; have polyH16 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (1); have polyH17 := Poly.add polyH15 polyH16; have polyH18 := Poly.mul polyH4 polyH17; have polyH19 := Poly.add polyH3 polyH18; have polyH20 := Poly.of_le (fun (x_4 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => List (Finset (Fin n))) (fun (n : ℕ) => List (Finset (Fin n))) _ _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n) (Fin.fintype n) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (n + 2))) [Bool.false, Bool.true]) (fun (n : ℕ) (x_1 : Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n) (Fin.fintype n) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (n + 2))) [Bool.false, Bool.true]) (Uniform.thresholds Bool.false) (Uniform.thresholds Bool.true) (Sigma.fst x_4) (Sigma.snd x_4)))) polyH19; have polyH21 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (100000); have polyH22 := Poly.add (hF) polyH16; have polyH23 := Poly.mul polyH21 polyH22; have polyH24 := Poly.add polyH10 polyH14; have polyH25 := Poly.add polyH24 polyH16; have polyH26 := Poly.mul polyH23 polyH25; have polyH27 := Poly.of_le (fun (x_4 : (n : ℕ) × Universe n × Matrix n) => (@Uniform.time_append_le (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (Sigma.fst x_4) (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_4)) (Fin.fintype (Sigma.fst x_4)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_4))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_4)))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_4))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_4)))) v}) (List.range (Sigma.fst x_4 + 2))) [Bool.false, Bool.true]) (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_4)) (Fin.fintype (Sigma.fst x_4)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_4))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_4)))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_4))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_4)))) v}) (List.range (Sigma.fst x_4 + 2))) [Bool.false, Bool.true]))) polyH26; have polyH28 := Poly.add polyH20 polyH27; have polyH29 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (10); have polyH30 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) polyH10 polyH14; have polyH31 := Poly.add polyH30 polyH16; have polyH32 := Poly.mul polyH29 polyH31; have polyH33 := Poly.add polyH28 polyH32; have polyH34 := Poly.of_le (fun (x_4 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => List (Finset (Fin n))) (fun (n : ℕ) => List (Finset (Fin n))) _ _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n) (Fin.fintype n) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (n + 2))) [Bool.false, Bool.true]) (fun (n : ℕ) (x_1 : Universe n × Matrix n) => List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin n) (Fin.fintype n) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (n + 2))) [Bool.false, Bool.true]) (Uniform.thresholds Bool.false) (Uniform.thresholds Bool.true)) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _) (Sigma.fst x_4) (Sigma.snd x_4)))) polyH33; exact Poly.lift polyH34 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem atomSets : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.atomSets.time x.1 x.2) 100 := by
  have htF := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) Bool.false
  have htT := lengthThresholds (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => x.2.2) true
  have hF := lengthCones (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.2) Bool.false (List.finRange 5)
  have hT := lengthCones (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.2) true (List.finRange 5)
  (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.atomSetsC) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.reparam (@Costs.atomSetsT) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (20); have polyH5 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.1); have polyH6 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.2); have polyH7 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2) polyH5 polyH6; have polyH8 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (0); have polyH9 := Poly.lengthCons (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => []) polyH8; have polyH10 := Poly.lengthCons (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => ∅) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => [@Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))]) polyH9; have polyH11 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => [∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))]) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH12 := Poly.volumeFinset polyH11 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => [∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))]) => (Sigma.snd q).1); have polyH13 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => [∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))]) polyH10 polyH12; have polyH14 := Poly.add polyH7 polyH13; have polyH15 := Poly.lengthAppend (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1))) (htF) (htT); have polyH16 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH17 := Poly.volumeFinset polyH16 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1))) => (Sigma.snd q).1); have polyH18 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1))) polyH15 polyH17; have polyH19 := Poly.add polyH14 polyH18; have polyH20 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (1); have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.mul polyH4 polyH21; have polyH23 := Poly.add polyH3 polyH22; have polyH24 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => List (Finset (Fin n))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => [∅, @Finset.univ (Fin n) (Fin.fintype n)]) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1)) (Uniform.atomSetsC) (Uniform.atomSetsT) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH23; have polyH25 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (100000); have polyH26 := Poly.add polyH10 polyH20; have polyH27 := Poly.mul polyH25 polyH26; have polyH28 := Poly.add polyH13 polyH18; have polyH29 := Poly.add polyH28 polyH20; have polyH30 := Poly.mul polyH27 polyH29; have polyH31 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (@Uniform.time_append_le (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (Sigma.fst x_6) ([∅, @Finset.univ (Fin (Sigma.fst x_6)) (Fin.fintype (Sigma.fst x_6))]) ((fun (x_1 : List (Finset (Fin (Sigma.fst x_6))) × List (Finset (Fin (Sigma.fst x_6)))) => Prod.fst x_1 ++ Prod.snd x_1) ((fun (x_1 : Universe (Sigma.fst x_6) × Matrix (Sigma.fst x_6)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_6)) (Fin.fintype (Sigma.fst x_6)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (Sigma.fst x_6 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_6)) (Fin.fintype (Sigma.fst x_6)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) v}) (List.range (Sigma.fst x_6 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_6))))) polyH30; have polyH32 := Poly.add polyH24 polyH31; have polyH33 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (10); have polyH34 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_2 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) (Sigma.snd x_1)))) polyH13 polyH18; have polyH35 := Poly.add polyH34 polyH20; have polyH36 := Poly.mul polyH33 polyH35; have polyH37 := Poly.add polyH32 polyH36; have polyH38 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ([∅, @Finset.univ (Fin i) (Fin.fintype i)], (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1))) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => List (Finset (Fin n))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => [∅, @Finset.univ (Fin n) (Fin.fintype n)]) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1)) Uniform.atomSetsC Uniform.atomSetsT) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH37; have polyH39 := Poly.reparam (@Costs.atomSetsD) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH40 := Poly.add polyH38 polyH39; have polyH41 := Poly.lengthAppend (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1))) polyH10 polyH15; have polyH42 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH43 := Poly.volumeFinset polyH42 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1))) => (Sigma.snd q).1); have polyH44 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1))) polyH41 polyH43; have polyH45 := Poly.add polyH7 polyH44; have polyH46 := Poly.lengthAppend (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1))) (hF) (hT); have polyH47 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q)); have polyH48 := Poly.volumeFinset polyH47 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1))) => (Sigma.snd q).1); have polyH49 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1)) ++ Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1))) polyH46 polyH48; have polyH50 := Poly.add polyH45 polyH49; have polyH51 := Poly.add polyH50 polyH20; have polyH52 := Poly.mul polyH4 polyH51; have polyH53 := Poly.add polyH40 polyH52; have polyH54 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => ([∅, @Finset.univ (Fin i) (Fin.fintype i)], (fun (x_3 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_2))) x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i)))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i)))) (List.finRange (5)))) x_1)) (@Uniform.comp ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ([∅, @Finset.univ (Fin i) (Fin.fintype i)], (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1))) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => List (Finset (Fin n))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => [∅, @Finset.univ (Fin n) (Fin.fintype n)]) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1)) Uniform.atomSetsC Uniform.atomSetsT) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _)) (Uniform.atomSetsD) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH53; have polyH55 := Poly.add polyH41 polyH20; have polyH56 := Poly.mul polyH25 polyH55; have polyH57 := Poly.add polyH44 polyH49; have polyH58 := Poly.add polyH57 polyH20; have polyH59 := Poly.mul polyH56 polyH58; have polyH60 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (@Uniform.time_append_le (ℕ) (fun (i : ℕ) => Finset (Fin i)) _ (Sigma.fst x_6) ((fun (x_1 : List (Finset (Fin (Sigma.fst x_6))) × List (Finset (Fin (Sigma.fst x_6)))) => Prod.fst x_1 ++ Prod.snd x_1) ((fun (x_1 : Universe (Sigma.fst x_6) × Matrix (Sigma.fst x_6)) => ([∅, @Finset.univ (Fin (Sigma.fst x_6)) (Fin.fintype (Sigma.fst x_6))], (fun (x_2 : List (Finset (Fin (Sigma.fst x_6))) × List (Finset (Fin (Sigma.fst x_6)))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe (Sigma.fst x_6) × Matrix (Sigma.fst x_6)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_6)) (Fin.fintype (Sigma.fst x_6)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_6 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_6)) (Fin.fintype (Sigma.fst x_6)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (Sigma.fst x_6 + 2))) [Bool.false, Bool.true])) x_1))) (Sigma.snd x_6))) ((fun (x_1 : List (Finset (Fin (Sigma.fst x_6))) × List (Finset (Fin (Sigma.fst x_6)))) => Prod.fst x_1 ++ Prod.snd x_1) ((fun (x_1 : Universe (Sigma.fst x_6) × Matrix (Sigma.fst x_6)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_1) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_6))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_1) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_6))))) (List.finRange (5)))) (Sigma.snd x_6))))) polyH59; have polyH61 := Poly.add polyH54 polyH60; have polyH62 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => ((fun (x_2 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => ([∅, @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))], (fun (x_3 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (Sigma.fst x_1 + 2))) [Bool.false, Bool.true])) x_2))) (Sigma.snd x_1)), (fun (x_2 : List (Finset (Fin (Sigma.fst x_1))) × List (Finset (Fin (Sigma.fst x_1)))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange (Sigma.fst x_1))))) (List.finRange (5)))) (Sigma.snd x_1)))) polyH44 polyH49; have polyH63 := Poly.add polyH62 polyH20; have polyH64 := Poly.mul polyH33 polyH63; have polyH65 := Poly.add polyH61 polyH64; have polyH66 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ((fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => ([∅, @Finset.univ (Fin i) (Fin.fintype i)], (fun (x_3 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_2))) x_1), (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i)))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i)))) (List.finRange (5)))) x_1))) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => ([∅, @Finset.univ (Fin i) (Fin.fintype i)], (fun (x_3 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_3 ++ Prod.snd x_3) ((fun (x_3 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_3)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_3))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_2))) x_1)) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.false k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i)))) (List.finRange (5)), List.flatMap (fun (k : Fin (5)) => List.map (coneSet (Prod.snd x_2) Bool.true k) (List.map Subtype.val (OAI.ThreeMachine.Structure.tripleList (List.finRange i)))) (List.finRange (5)))) x_1)) (@Uniform.comp ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (i : ℕ) => List (Finset (Fin i)) × List (Finset (Fin i))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => ([∅, @Finset.univ (Fin i) (Fin.fintype i)], (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1))) (fun (i : ℕ) (x_1 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_1 ++ Prod.snd x_1) (@Uniform.pair ℕ (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => List (Finset (Fin n))) (fun (i : ℕ) => List (Finset (Fin i))) _ _ _ (fun (n : ℕ) (x_1 : Universe n × Matrix n) => [∅, @Finset.univ (Fin n) (Fin.fintype n)]) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (fun (x_2 : List (Finset (Fin i)) × List (Finset (Fin i))) => Prod.fst x_2 ++ Prod.snd x_2) ((fun (x_2 : Universe i × Matrix i) => (List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.false = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true], List.flatMap (fun (upper : Bool) => List.map (fun (k : ℕ) => {v ∈ @Finset.univ (Fin i) (Fin.fintype i) | if upper = Bool.true then (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v ≤ k else k ≤ (if Bool.true = Bool.true then OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_2)) else OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_2))) v}) (List.range (i + 2))) [Bool.false, Bool.true])) x_1)) Uniform.atomSetsC Uniform.atomSetsT) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _)) Uniform.atomSetsD) (@Uniform.append ℕ (fun (i : ℕ) => Finset (Fin i)) _) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH65; have polyH67 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_atomSets (Sigma.fst x_6) (Sigma.snd x_6)))) polyH66; exact Poly.lift polyH67 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
theorem familyAssignments (K : ℕ) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.familyAssignments K).time x.1 x.2) (max (max 100 (9*K+10)) 5) := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  let xs (x : Σ n, Universe n × Matrix n) :=
    (Atomic.alphabet (List.finRange x.1)).map
      (Atomic.finsetEval (matrixRel x.2.2) (Structure.jobRank (matrixRel x.2.2)) (Structure.reverseJobRank (matrixRel x.2.2)))
  have hl : Poly n (fun x => (xs x).length) 3 := by
    simpa only [xs,List.length_map] using Poly.lengthAlphabet (Poly.size n)
  have hA := assignments n xs hl K
  have hAL : Poly n (fun x => (Structure.assignments (xs x) K).length) (3*K) := by
    simpa only [Structure.assignments_length] using hl.pow K
  have hAV : Poly n (fun x => volume (Structure.assignments (xs x) K)) (3*K+2) := by (have polyH0 := Poly.const (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => n (Sigma.fst q)) (K); have polyH1 := Poly.size (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => K) => (fun (q_1 : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => n (Sigma.fst q_1)) (Sigma.fst q)); have polyH2 := Poly.volumeFinset polyH1 (fun (q : Poly.FinPool fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => K) => (Sigma.snd (Sigma.fst q)).1 (Sigma.snd q)); have polyH3 := Poly.volumeFunction (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) => (Sigma.snd q).1) polyH0 polyH2; have polyH4 := Poly.listVolume (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.assignments (xs x_1) K) (hAL) polyH3; exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  (have polyH0 := Poly.size (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.atomSets) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.add polyH1 (hA); have polyH3 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (10); have polyH4 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange (Sigma.fst x_1)))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)); have polyH5 := Poly.volumeFinset polyH4 (fun (q : Poly.ListPool fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange (Sigma.fst x_1)))) => (Sigma.snd q).1); have polyH6 := Poly.listVolume (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd (Sigma.snd x_1))) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1)))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd (Sigma.snd x_1))))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange (Sigma.fst x_1)))) (hl) polyH5; have polyH7 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (1); have polyH8 := Poly.add polyH6 polyH7; have polyH9 := Poly.mul polyH3 polyH8; have polyH10 := Poly.add polyH2 polyH9; have polyH11 := Poly.of_le (fun (x_9 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n_1 : ℕ) => Universe n_1 × Matrix n_1) (fun (n_1 : ℕ) => List (Finset (Fin n_1))) (fun (i : ℕ) => List (Fin K → Finset (Fin i))) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => List.map (OAI.ThreeMachine.Structure.Atomic.finsetEval (matrixRel (Prod.snd x_1)) (OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (OAI.ThreeMachine.Structure.reverseJobRank (matrixRel (Prod.snd x_1)))) (OAI.ThreeMachine.Structure.Atomic.alphabet (List.finRange n_1))) (fun (i : ℕ) (xs_1 : List (Finset (Fin i))) => OAI.ThreeMachine.Structure.assignments xs_1 K) (Uniform.atomSets) (@Uniform.assignments ℕ (fun (i : ℕ) => Finset (Fin i)) _ K) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH10; exact Poly.lift polyH11 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

section

end

end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.familyAssignments := @OAI.ThreeMachine.StackCompiler.Costs.familyAssignments
