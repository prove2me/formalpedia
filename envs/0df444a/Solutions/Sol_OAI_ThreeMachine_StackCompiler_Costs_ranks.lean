-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.ranks
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:54:06.637485+00:00
-- url     : https://prove2.me/submissions/5bb0220a-75fc-4681-9444-501d4e7fbc66

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02

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
-- module Polynomial
namespace OAI

universe u1 u2

section

namespace ThreeMachine.StackCompiler

namespace Poly
variable {I : Type u2} {s f g : I → ℕ} {d e : ℕ}

theorem sub (hf : Poly s f d) (g : I → ℕ) : Poly s (fun i => f i-g i) d :=
  of_le (fun _ => Nat.sub_le _ _) hf

end Poly
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
  (
  have polyH0 := Poly.const (s) (3);
  have polyH1 := Poly.const (s) (1);
  have polyH2 := Poly.add (hn) polyH1;
  have polyH3 := Poly.pow polyH2 (2);
  have polyH4 := Poly.mul polyH0 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | omega))

theorem volumeBoolVector (hn : Poly s n d) (v : ∀ i, Fin (n i) → Bool) :
    Poly s (fun i => volume (v i)) d := by
  apply of_le (fun i => volume_bool_vector_le (v i))
  (
  have polyH0 := Poly.const (s) (4);
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

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u26} {s : J → ℕ} {α : J → Type u27} [∀ j, Coding (α j)]

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

theorem time_vectorMap {α : ℕ → Type u5} {β : ℕ → Type u6} [∀ n, Coding (α n)] [∀ n, Coding (β n)]
    {f : ∀ n, Fin n × α n → β n} (R : Uniform f) (n : ℕ) (x : Universe n × α n) :
    R.vectorMap.time n x = (universeList.onFst.comp R.map).time n x := rfl

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u7} {α : I → Type u8} [∀ i, Coding (α i)]
theorem time_andD_le {p q : ∀ i, α i → Prop}
    [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x)))
    (i : I) (x : α i) : (P.andD Q).time i x ≤ P.time i x+Q.time i x+20*volume x+11000 := by
  rw [andD,time_congr,time_comp,time_pair,time_uniform]
  have h := Realizer.time_and_le (decide (p i x),decide (q i x))
  have hp := volume_bool (decide (p i x))
  have hq := volume_bool (decide (q i x))
  simp only [volume_pair] at *
  omega
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
namespace Costs
theorem matrixGet : Poly (fun x : Σ n, Matrix n × (Fin n × Fin n) => x.1)
    (fun x => Uniform.matrixGet.time x.1 x.2) 3 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.1);
  have polyH2 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2.1);
  have polyH3 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2.2);
  have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2) polyH2 polyH3;
  have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2) polyH1 polyH4;
  have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH9 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH10 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2.1);
  have polyH11 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2.2);
  have polyH12 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2) polyH10 polyH11;
  have polyH13 := Poly.add polyH12 polyH6;
  have polyH14 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH13;
  have polyH15 := Poly.add polyH9 polyH14;
  have polyH16 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (10);
  have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (1);
  have polyH18 := Poly.add polyH12 polyH17;
  have polyH19 := Poly.mul polyH16 polyH18;
  have polyH20 := Poly.add polyH15 polyH19;
  have polyH21 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH20;
  have polyH22 := Poly.add polyH8 polyH21;
  have polyH23 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (20);
  have polyH24 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).1);
  have polyH25 := Poly.add polyH5 polyH24;
  have polyH26 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).1);
  have polyH27 := Poly.add polyH25 polyH26;
  have polyH28 := Poly.add polyH27 polyH17;
  have polyH29 := Poly.mul polyH23 polyH28;
  have polyH30 := Poly.add polyH22 polyH29;
  have polyH31 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) (Fin) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH30;
  have polyH32 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (1000000000);
  have polyH33 := Poly.add polyH0 polyH17;
  have polyH34 := Poly.mul polyH32 polyH33;
  have polyH35 := Poly.add polyH24 polyH0;
  have polyH36 := Poly.add polyH35 polyH17;
  have polyH37 := Poly.mul polyH34 polyH36;
  have polyH38 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (@Uniform.time_functionGet_le (fun (i : ℕ) => Fin i → Bool) _ (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2)) (Prod.fst (Prod.snd (Sigma.snd x_2))))) polyH37;
  have polyH39 := Poly.add polyH31 polyH38;
  have polyH40 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.fst (Sigma.snd x_1), Prod.fst (Prod.snd (Sigma.snd x_1)))) polyH24 polyH26;
  have polyH41 := Poly.add polyH40 polyH17;
  have polyH42 := Poly.mul polyH16 polyH41;
  have polyH43 := Poly.add polyH39 polyH42;
  have polyH44 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i) (fun (i : ℕ) => Fin i → Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (i : ℕ) => Fin i → Bool) _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH43;
  have polyH45 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH13;
  have polyH46 := Poly.add polyH9 polyH45;
  have polyH47 := Poly.add polyH46 polyH19;
  have polyH48 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH47;
  have polyH49 := Poly.add polyH44 polyH48;
  have polyH50 := Poly.volumeBoolVector polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).1 (Prod.snd ((fun (x_2 : (Fin (Sigma.fst x_1) → Fin (Sigma.fst x_1) → Bool) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) (Sigma.snd x_1))));
  have polyH51 := Poly.add polyH5 polyH50;
  have polyH52 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).2);
  have polyH53 := Poly.add polyH51 polyH52;
  have polyH54 := Poly.add polyH53 polyH17;
  have polyH55 := Poly.mul polyH23 polyH54;
  have polyH56 := Poly.add polyH49 polyH55;
  have polyH57 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Bool) (Fin) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (fun (x_3 : (Fin i → Fin i → Bool) × Fin i) => Prod.fst x_3 (Prod.snd x_3)) ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_3, Prod.fst (Prod.snd x_3))) x_1)) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i) (fun (i : ℕ) => Fin i → Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (i : ℕ) => Fin i → Bool) _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH56;
  have polyH58 := Poly.add polyH50 polyH0;
  have polyH59 := Poly.add polyH58 polyH17;
  have polyH60 := Poly.mul polyH34 polyH59;
  have polyH61 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (@Uniform.time_functionGet_le (fun (n : ℕ) => Bool) _ (Sigma.fst x_2) ((fun (x_1 : (Fin (Sigma.fst x_2) → Fin (Sigma.fst x_2) → Bool) × Fin (Sigma.fst x_2)) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : (Fin (Sigma.fst x_2) → Fin (Sigma.fst x_2) → Bool) × Fin (Sigma.fst x_2) × Fin (Sigma.fst x_2)) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Sigma.snd x_2))) (Prod.snd (Prod.snd (Sigma.snd x_2))))) polyH60;
  have polyH62 := Poly.add polyH57 polyH61;
  have polyH63 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => ((fun (x_2 : (Fin (Sigma.fst x_1) → Fin (Sigma.fst x_1) → Bool) × Fin (Sigma.fst x_1)) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : (Fin (Sigma.fst x_1) → Fin (Sigma.fst x_1) → Bool) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) (Sigma.snd x_1)), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH50 polyH52;
  have polyH64 := Poly.add polyH63 polyH17;
  have polyH65 := Poly.mul polyH16 polyH64;
  have polyH66 := Poly.add polyH62 polyH65;
  have polyH67 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Bool) × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i) => Prod.fst x_3 (Prod.snd x_3)) ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_3, Prod.fst (Prod.snd x_3))) x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Bool) Fin _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (fun (x_3 : (Fin i → Fin i → Bool) × Fin i) => Prod.fst x_3 (Prod.snd x_3)) ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_3, Prod.fst (Prod.snd x_3))) x_1)) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i) (fun (i : ℕ) => Fin i → Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (i : ℕ) => Fin i → Bool) _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (n : ℕ) => Bool) _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH66;
  exact Poly.lift polyH67 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

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
theorem time_orD_le {p q : ∀ i, α i → Prop}
    [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x)))
    (i : I) (x : α i) : (P.orD Q).time i x ≤ P.time i x+Q.time i x+20*volume x+11000 := by
  rw [orD,time_congr,time_comp,time_pair,time_uniform]
  have h := Realizer.time_or_le (decide (p i x),decide (q i x))
  have hp := volume_bool (decide (p i x)); have hq := volume_bool (decide (q i x))
  simp only [volume_pair] at *
  omega
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
  (
  have polyH0 := Poly.const (s) (1);
  have polyH1 := Poly.const (s) (2);
  have polyH2 := Poly.mul polyH1 (hB);
  have polyH3 := Poly.add polyH2 polyH0;
  have polyH4 := Poly.add polyH3 polyH0;
  have polyH5 := Poly.mul (hn) polyH4;
  have polyH6 := Poly.add polyH0 polyH5;
  exact Poly.lift polyH6 (by first | decide +kernel | omega))

theorem volumePredecessors (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.predecessorCount (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.predecessorCount (matrixRel (M j))) hn hn
    (fun j v => by
      dsimp [Structure.predecessorCount]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp))
  simpa only [two_mul] using h

theorem volumeRank (M : ∀ j, Matrix (n j)) (hn : Poly s n d) :
    Poly s (fun j => volume (Structure.jobRank (matrixRel (M j)))) (2*d) := by
  have h := volumeBoundedFunction (fun j => Structure.jobRank (matrixRel (M j))) hn hn
    (fun j v => (Structure.jobRank_bounds (matrixRel (M j)) v).2)
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

theorem time_predecessorCount (n : ℕ) (x : Universe n × (Matrix n × Fin n)) :
    predecessorCount.time n x =
      ((((fst.comp universeSet).pair snd).comp predecessorCell.setFilter).comp setCard).time n x := rfl

theorem time_predecessors (n : ℕ) (x : Universe n × Matrix n) :
    predecessors.time n x = ((fst.pair id).comp predecessorsBody.vectorMap).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem predecessorCell : Poly (fun x : Σ n, Uniform.PredecessorInput n => x.1)
    (fun x => Uniform.predecessorCell.time x.1 x.2) 3 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => x_1.2.2.1);
  have polyH3 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => x_1.2.2.2);
  have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => x_1.2.2) polyH2 polyH3;
  have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => x_1.2) polyH1 polyH4;
  have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => Sigma.fst x_1) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => Matrix i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH9 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Sigma.snd x_1).2.1);
  have polyH10 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Sigma.snd x_1).2.2);
  have polyH11 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Sigma.snd x_1).2) polyH9 polyH10;
  have polyH12 := Poly.add polyH11 polyH6;
  have polyH13 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (Matrix) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH12;
  have polyH14 := Poly.add polyH8 polyH13;
  have polyH15 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => Sigma.fst x_1) (10);
  have polyH16 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => Sigma.fst x_1) (1);
  have polyH17 := Poly.add polyH11 polyH16;
  have polyH18 := Poly.mul polyH15 polyH17;
  have polyH19 := Poly.add polyH14 polyH18;
  have polyH20 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.fst ℕ Matrix Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH19;
  have polyH21 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => Matrix i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH22 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH12;
  have polyH23 := Poly.add polyH8 polyH22;
  have polyH24 := Poly.add polyH23 polyH18;
  have polyH25 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.snd ℕ Matrix Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH24;
  have polyH26 := Poly.add polyH21 polyH25;
  have polyH27 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => Sigma.fst x_1) (20);
  have polyH28 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Sigma.snd x_1).1);
  have polyH29 := Poly.add polyH5 polyH28;
  have polyH30 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Prod.snd (Sigma.snd x_1)).2);
  have polyH31 := Poly.add polyH29 polyH30;
  have polyH32 := Poly.add polyH31 polyH16;
  have polyH33 := Poly.mul polyH27 polyH32;
  have polyH34 := Poly.add polyH26 polyH33;
  have polyH35 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Matrix i × Fin i) (Fin) (Fin) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.snd ℕ Matrix Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH34;
  have polyH36 := Poly.add polyH20 polyH35;
  have polyH37 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Prod.snd (Sigma.snd x_1)).1);
  have polyH38 := Poly.add polyH5 polyH37;
  have polyH39 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Prod.fst (Sigma.snd x_1), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH28 polyH30;
  have polyH40 := Poly.add polyH38 polyH39;
  have polyH41 := Poly.add polyH40 polyH16;
  have polyH42 := Poly.mul polyH27 polyH41;
  have polyH43 := Poly.add polyH36 polyH42;
  have polyH44 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Matrix i × Fin i) (Matrix) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.fst ℕ Matrix Fin _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) Fin Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.snd ℕ Matrix Fin _ _))) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH43;
  have polyH45 := Poly.reparam (@Costs.matrixGet) (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => Sigma.mk (Sigma.fst x_1) (Prod.fst (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH0;
  have polyH46 := Poly.add polyH44 polyH45;
  have polyH47 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorInput n) => (Prod.fst (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH37 polyH39;
  have polyH48 := Poly.add polyH47 polyH16;
  have polyH49 := Poly.mul polyH15 polyH48;
  have polyH50 := Poly.add polyH46 polyH49;
  have polyH51 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Matrix n × Fin n × Fin n) => Prod.fst x_1 (Prod.fst (Prod.snd x_1)) (Prod.snd (Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) Matrix (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.fst ℕ Matrix Fin _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) Fin Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin i × Matrix i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Matrix i × Fin i) (fun (i : ℕ) => Matrix i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Matrix i × Fin i) _ _) (@Uniform.snd ℕ Matrix Fin _ _)))) (Uniform.matrixGet) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH50;
  exact Poly.lift polyH51 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem predecessorCount :
    Poly (fun x : Σ n, Universe n × (Matrix n × Fin n) => x.1)
      (fun x => Uniform.predecessorCount.time x.1 x.2) 4 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => x_1.2.2.1);
  have polyH3 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => x_1.2.2.2);
  have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => x_1.2.2) polyH2 polyH3;
  have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => x_1.2) polyH1 polyH4;
  have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH9 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => (Sigma.snd x_1).1);
  have polyH10 := Poly.add polyH9 polyH6;
  have polyH11 := Poly.add polyH8 polyH10;
  have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (10);
  have polyH13 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (1);
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.mul polyH12 polyH14;
  have polyH16 := Poly.add polyH11 polyH15;
  have polyH17 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Fin i) (Universe) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _) (Uniform.universeSet) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH16;
  have polyH18 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Matrix i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH19 := Poly.add polyH17 polyH18;
  have polyH20 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (20);
  have polyH21 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)));
  have polyH22 := Poly.add polyH5 polyH21;
  have polyH23 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => (Sigma.snd x_1).2.1);
  have polyH24 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => (Sigma.snd x_1).2.2);
  have polyH25 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => (Sigma.snd x_1).2) polyH23 polyH24;
  have polyH26 := Poly.add polyH22 polyH25;
  have polyH27 := Poly.add polyH26 polyH13;
  have polyH28 := Poly.mul polyH20 polyH27;
  have polyH29 := Poly.add polyH19 polyH28;
  have polyH30 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Matrix i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i × Fin i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Fin i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH29;
  have polyH31 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) polyH21 polyH25;
  have polyH32 := Poly.add polyH31 polyH6;
  have polyH33 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _ (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH32;
  have polyH34 := Poly.add polyH21 polyH6;
  have polyH35 := Poly.add polyH33 polyH34;
  have polyH36 := Poly.add polyH21 polyH13;
  have polyH37 := Poly.mul polyH12 polyH36;
  have polyH38 := Poly.add polyH35 polyH37;
  have polyH39 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Matrix n × Fin n) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _) (Uniform.setList) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH38;
  have polyH40 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _ (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH32;
  have polyH41 := Poly.add polyH39 polyH40;
  have polyH42 := Poly.add polyH31 polyH21;
  have polyH43 := Poly.add polyH42 polyH25;
  have polyH44 := Poly.add polyH43 polyH13;
  have polyH45 := Poly.mul polyH20 polyH44;
  have polyH46 := Poly.add polyH41 polyH45;
  have polyH47 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Matrix n × Fin n) i) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _ _ (fun (i : ℕ) (x_1 : (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Matrix n × Fin n) i) => (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (n : ℕ) => Matrix n × Fin n) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH46;
  have polyH48 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1)));
  have polyH49 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) polyH48;
  have polyH50 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH51 := Poly.reparam (@Costs.predecessorCell) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q)))) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))) polyH50;
  have polyH52 := @Poly.filterTime (ℕ) ((n : ℕ) × Universe n × Matrix n × Fin n) (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (Fin) (fun (n : ℕ) => Matrix n × Fin n) _ _ (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Prod.fst (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Prod.snd (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) (fun (n : ℕ) (x_1 : Uniform.PredecessorInput n) => Prod.fst (Prod.snd x_1) (Prod.fst x_1) (Prod.snd (Prod.snd x_1))) (Uniform.predecessorCell) (1) (3 * 1) (2 * 1) (Max.max (2 * 1) (1)) polyH49 polyH51 polyH21 polyH25;
  have polyH53 := Poly.add polyH47 polyH52;
  have polyH54 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => (Finset.sort (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) polyH21 polyH25;
  have polyH55 := Poly.add polyH54 polyH13;
  have polyH56 := Poly.mul polyH12 polyH55;
  have polyH57 := Poly.add polyH53 polyH56;
  have polyH58 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Matrix i × Fin i) (fun (i : ℕ) => List (Fin i) × Matrix i × Fin i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Matrix i × Fin i) => (Finset.sort (Prod.fst x_1) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Matrix i × Fin i) => List.filter (fun (a : Fin i) => Prod.fst (Prod.snd (a, Prod.snd x_1)) (Prod.fst (a, Prod.snd x_1)) (Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst x_1)) (@Uniform.onFst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Matrix n × Fin n) _ _ _ (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) Uniform.setList) (@Uniform.filter ℕ Fin (fun (n : ℕ) => Matrix n × Fin n) _ _ (fun (n : ℕ) (x_1 : Uniform.PredecessorInput n) => Prod.fst (Prod.snd x_1) (Prod.fst x_1) (Prod.snd (Prod.snd x_1))) Uniform.predecessorCell) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH57;
  have polyH59 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_setFilter (fun (n : ℕ) => Matrix n × Fin n) _ (fun (n : ℕ) (x_1 : Uniform.PredecessorInput n) => Prod.fst (Prod.snd x_1) (Prod.fst x_1) (Prod.snd (Prod.snd x_1))) (Uniform.predecessorCell) (Sigma.fst x_2) (((fun (x_1 : Universe (Sigma.fst x_2)) => @Finset.univ (Fin (Sigma.fst x_2)) (Fin.fintype (Sigma.fst x_2))) (Prod.fst (Sigma.snd x_2)), Prod.snd (Sigma.snd x_2)))))) polyH58;
  have polyH60 := Poly.add polyH30 polyH59;
  have polyH61 := Poly.add polyH31 polyH13;
  have polyH62 := Poly.mul polyH12 polyH61;
  have polyH63 := Poly.add polyH60 polyH62;
  have polyH64 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (i : ℕ) => Finset (Fin i) × Matrix i × Fin i) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i × Fin i) => ((fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), Prod.snd x_1)) (fun (n : ℕ) (x_1 : Finset (Fin n) × Matrix n × Fin n) => {a ∈ Prod.fst x_1 | Prod.fst (Prod.snd (a, Prod.snd x_1)) (Prod.fst (a, Prod.snd x_1)) (Prod.snd (Prod.snd (a, Prod.snd x_1))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Matrix i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i × Fin i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Fin i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _)) (@Uniform.setFilter (fun (n : ℕ) => Matrix n × Fin n) _ (fun (n : ℕ) (x_1 : Uniform.PredecessorInput n) => Prod.fst (Prod.snd x_1) (Prod.fst x_1) (Prod.snd (Prod.snd x_1))) Uniform.predecessorCell) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH63;
  have polyH65 := Poly.reparam (@Costs.setCard) (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => Sigma.mk (Sigma.fst x_1) ((fun (x_2 : Finset (Fin (Sigma.fst x_1)) × Matrix (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => {a ∈ Prod.fst x_2 | Prod.fst (Prod.snd (a, Prod.snd x_2)) (Prod.fst (a, Prod.snd x_2)) (Prod.snd (Prod.snd (a, Prod.snd x_2))) = Bool.true}) ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), Prod.snd x_2)) (Sigma.snd x_1)))) polyH0;
  have polyH66 := Poly.add polyH64 polyH65;
  have polyH67 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n × Fin n) => {a ∈ Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), Prod.snd x_2)) (Sigma.snd x_1)) | Prod.fst (Prod.snd (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), Prod.snd x_2)) (Sigma.snd x_1)))) (Prod.fst (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), Prod.snd x_2)) (Sigma.snd x_1)))) (Prod.snd (Prod.snd (a, Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => @Finset.univ (Fin (Sigma.fst x_1)) (Fin.fintype (Sigma.fst x_1))) (Prod.fst x_2), Prod.snd x_2)) (Sigma.snd x_1))))) = Bool.true});
  have polyH68 := Poly.add polyH67 polyH13;
  have polyH69 := Poly.mul polyH12 polyH68;
  have polyH70 := Poly.add polyH66 polyH69;
  have polyH71 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i × Fin i) => (fun (x_3 : Finset (Fin i) × Matrix i × Fin i) => {a ∈ Prod.fst x_3 | Prod.fst (Prod.snd (a, Prod.snd x_3)) (Prod.fst (a, Prod.snd x_3)) (Prod.snd (Prod.snd (a, Prod.snd x_3))) = Bool.true}) ((fun (x_3 : Universe i × Matrix i × Fin i) => ((fun (x_4 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_3), Prod.snd x_3)) x_1)) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.card s) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (i : ℕ) => Finset (Fin i) × Matrix i × Fin i) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i × Fin i) => ((fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), Prod.snd x_1)) (fun (n : ℕ) (x_1 : Finset (Fin n) × Matrix n × Fin n) => {a ∈ Prod.fst x_1 | Prod.fst (Prod.snd (a, Prod.snd x_1)) (Prod.fst (a, Prod.snd x_1)) (Prod.snd (Prod.snd (a, Prod.snd x_1))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Matrix i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i × Fin i) => (fun (x_3 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × Matrix i × Fin i) Universe (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => @Finset.univ (Fin n) (Fin.fintype n)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Matrix i × Fin i) _ _)) (@Uniform.setFilter (fun (n : ℕ) => Matrix n × Fin n) _ (fun (n : ℕ) (x_1 : Uniform.PredecessorInput n) => Prod.fst (Prod.snd x_1) (Prod.fst x_1) (Prod.snd (Prod.snd x_1))) Uniform.predecessorCell)) (Uniform.setCard) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH70;
  have polyH72 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n × Matrix n × Fin n) => (le_of_eq (@Uniform.time_predecessorCount (Sigma.fst x_2) (Sigma.snd x_2)))) polyH71;
  exact Poly.lift polyH72 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem predecessorsBody : Poly (fun x : Σ n, Uniform.PredecessorsInput n => x.1)
    (fun x => Uniform.predecessorsBody.time x.1 x.2) 4 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => x_1.2.1);
  have polyH2 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => x_1.2.2.1);
  have polyH3 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => x_1.2.2.2);
  have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => x_1.2.2) polyH2 polyH3;
  have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => x_1.2) polyH1 polyH4;
  have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => Sigma.fst x_1) (2);
  have polyH7 := Poly.add polyH5 polyH6;
  have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => Universe i × Matrix i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH9 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Sigma.snd x_1).2.1);
  have polyH10 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Sigma.snd x_1).2.2);
  have polyH11 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Sigma.snd x_1).2) polyH9 polyH10;
  have polyH12 := Poly.add polyH11 polyH6;
  have polyH13 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH12;
  have polyH14 := Poly.add polyH8 polyH13;
  have polyH15 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => Sigma.fst x_1) (10);
  have polyH16 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => Sigma.fst x_1) (1);
  have polyH17 := Poly.add polyH11 polyH16;
  have polyH18 := Poly.mul polyH15 polyH17;
  have polyH19 := Poly.add polyH14 polyH18;
  have polyH20 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.fst ℕ Universe Matrix _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH19;
  have polyH21 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH12;
  have polyH22 := Poly.add polyH8 polyH21;
  have polyH23 := Poly.add polyH22 polyH18;
  have polyH24 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) (Matrix) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.snd ℕ Universe Matrix _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH23;
  have polyH25 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => Universe i × Matrix i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7;
  have polyH26 := Poly.add polyH24 polyH25;
  have polyH27 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => Sigma.fst x_1) (20);
  have polyH28 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Prod.snd (Sigma.snd x_1)).2);
  have polyH29 := Poly.add polyH5 polyH28;
  have polyH30 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Sigma.snd x_1).1);
  have polyH31 := Poly.add polyH29 polyH30;
  have polyH32 := Poly.add polyH31 polyH16;
  have polyH33 := Poly.mul polyH27 polyH32;
  have polyH34 := Poly.add polyH26 polyH33;
  have polyH35 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Universe i × Matrix i) (Matrix) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.snd ℕ Universe Matrix _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH34;
  have polyH36 := Poly.add polyH20 polyH35;
  have polyH37 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Prod.snd (Sigma.snd x_1)).1);
  have polyH38 := Poly.add polyH5 polyH37;
  have polyH39 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Prod.snd (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) polyH28 polyH30;
  have polyH40 := Poly.add polyH38 polyH39;
  have polyH41 := Poly.add polyH40 polyH16;
  have polyH42 := Poly.mul polyH27 polyH41;
  have polyH43 := Poly.add polyH36 polyH42;
  have polyH44 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Universe i × Matrix i) (Universe) (fun (i : ℕ) => Matrix i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.fst ℕ Universe Matrix _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) Matrix Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.snd ℕ Universe Matrix _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH43;
  have polyH45 := Poly.reparam (@Costs.predecessorCount) (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => Sigma.mk (Sigma.fst x_1) (Prod.fst (Prod.snd (Sigma.snd x_1)), Prod.snd (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) polyH0;
  have polyH46 := Poly.add polyH44 polyH45;
  have polyH47 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.PredecessorsInput n) => (Prod.fst (Prod.snd (Sigma.snd x_1)), Prod.snd (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) polyH37 polyH39;
  have polyH48 := Poly.add polyH47 polyH16;
  have polyH49 := Poly.mul polyH15 polyH48;
  have polyH50 := Poly.add polyH46 polyH49;
  have polyH51 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.PredecessorsInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i × Fin i) (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n : ℕ) (x_1 : Universe n × Matrix n × Fin n) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.fst (Prod.snd x_1))) (Prod.snd (Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) Universe (fun (i : ℕ) => Matrix i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.fst ℕ Universe Matrix _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) Matrix Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × Matrix i) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × Matrix i) (fun (i : ℕ) => Universe i × Matrix i) Matrix _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _) (@Uniform.snd ℕ Universe Matrix _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × Matrix i) _ _))) (Uniform.predecessorCount) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH50;
  exact Poly.lift polyH51 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem predecessors :
    Poly (fun x : Σ n, Universe n × Matrix n => x.1)
      (fun x => Uniform.predecessors.time x.1 x.2) 5 := by
  have hv := Poly.volumePredecessors (fun x : Σ n, Universe n × Matrix n => x.2.2)
    (Poly.size (fun x : Σ n, Universe n × Matrix n => x.1))
  (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_3) (Sigma.snd x_3)))) polyH5;
  have polyH7 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => Universe i × Matrix i) _ (Sigma.fst x_3) (Sigma.snd x_3)))) polyH5;
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (20);
  have polyH10 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (Sigma.snd x_1).1);
  have polyH11 := Poly.add polyH3 polyH10;
  have polyH12 := Poly.add polyH11 polyH3;
  have polyH13 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (1);
  have polyH14 := Poly.add polyH12 polyH13;
  have polyH15 := Poly.mul polyH9 polyH14;
  have polyH16 := Poly.add polyH8 polyH15;
  have polyH17 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (i : ℕ) => Universe i × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => x_1) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.id ℕ (fun (i : ℕ) => Universe i × Matrix i) _) (Sigma.fst x_3) (Sigma.snd x_3)))) polyH16;
  have polyH18 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (Prod.fst (Sigma.snd x_1), Sigma.snd x_1)) polyH10 polyH3;
  have polyH19 := Poly.add polyH18 polyH4;
  have polyH20 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n : ℕ) => Universe n × Matrix n) _ _ (Sigma.fst x_3) ((Prod.fst (Sigma.snd x_3), Sigma.snd x_3))))) polyH19;
  have polyH21 := Poly.add polyH10 polyH4;
  have polyH22 := Poly.add polyH20 polyH21;
  have polyH23 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (10);
  have polyH24 := Poly.add polyH10 polyH13;
  have polyH25 := Poly.mul polyH23 polyH24;
  have polyH26 := Poly.add polyH22 polyH25;
  have polyH27 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (fun (n : ℕ) => Universe n × Matrix n) i) (Universe) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (@Uniform.fst ℕ Universe (fun (n : ℕ) => Universe n × Matrix n) _ _) (Uniform.universeList) (Sigma.fst x_3) ((Prod.fst (Sigma.snd x_3), Sigma.snd x_3))))) polyH26;
  have polyH28 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (n : ℕ) => Universe n × Matrix n) _ _ (Sigma.fst x_3) ((Prod.fst (Sigma.snd x_3), Sigma.snd x_3))))) polyH19;
  have polyH29 := Poly.add polyH27 polyH28;
  have polyH30 := Poly.volumeFinRange polyH0;
  have polyH31 := Poly.add polyH18 polyH30;
  have polyH32 := Poly.add polyH31 polyH3;
  have polyH33 := Poly.add polyH32 polyH13;
  have polyH34 := Poly.mul polyH9 polyH33;
  have polyH35 := Poly.add polyH29 polyH34;
  have polyH36 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (fun (n : ℕ) => Universe n × Matrix n) i) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Universe n × Matrix n) _ _ _ (fun (i : ℕ) (x_1 : Universe i × (fun (n : ℕ) => Universe n × Matrix n) i) => (fun (n : ℕ) (x_2 : Universe n) => List.finRange n) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (fun (n : ℕ) => Universe n × Matrix n) i) Universe (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (@Uniform.fst ℕ Universe (fun (n : ℕ) => Universe n × Matrix n) _ _) Uniform.universeList) (@Uniform.snd ℕ Universe (fun (n : ℕ) => Universe n × Matrix n) _ _) (Sigma.fst x_3) ((Prod.fst (Sigma.snd x_3), Sigma.snd x_3))))) polyH35;
  have polyH37 := Poly.lengthFinRange polyH0;
  have polyH38 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH39 := Poly.reparam (@Costs.predecessorsBody) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))) polyH38;
  have polyH40 := Poly.precomp (hv) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst q);
  have polyH41 := Poly.natFunctionApply (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))) polyH40;
  have polyH42 := Poly.volumeNat polyH41;
  have polyH43 := @Poly.mapTime (ℕ) ((n : ℕ) × Universe n × Matrix n) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (Fin) (fun (n : ℕ) => ℕ) (fun (n : ℕ) => Universe n × Matrix n) _ _ _ (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Prod.snd (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) (fun (n : ℕ) (x_1 : Uniform.PredecessorsInput n) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Prod.snd x_1))) (Prod.fst x_1)) (Uniform.predecessorsBody) (1) (4 * 1) (2 * 1) (Max.max (2 * 1) (2 * 1)) (2 * 1) polyH37 polyH39 polyH30 polyH3 polyH42;
  have polyH44 := Poly.add polyH36 polyH43;
  have polyH45 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) polyH30 polyH3;
  have polyH46 := Poly.add polyH45 polyH13;
  have polyH47 := Poly.mul polyH23 polyH46;
  have polyH48 := Poly.add polyH44 polyH47;
  have polyH49 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Universe i × Matrix i) (fun (i : ℕ) => List (Fin i) × Universe i × Matrix i) (fun (i : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Universe i × Matrix i) => (List.finRange i, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Universe i × Matrix i) => List.map (fun (a : Fin i) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.onFst ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => Universe n × Matrix n) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) Uniform.universeList) (@Uniform.map ℕ Fin (fun (n : ℕ) => ℕ) (fun (n : ℕ) => Universe n × Matrix n) _ _ _ (fun (n : ℕ) (x_1 : Uniform.PredecessorsInput n) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Prod.snd x_1))) (Prod.fst x_1)) Uniform.predecessorsBody) (Sigma.fst x_3) ((Prod.fst (Sigma.snd x_3), Sigma.snd x_3))))) polyH48;
  have polyH50 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_vectorMap (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Uniform.PredecessorsInput n) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Prod.snd x_1))) (Prod.fst x_1)) (Uniform.predecessorsBody) (Sigma.fst x_3) ((Prod.fst (Sigma.snd x_3), Sigma.snd x_3))))) polyH49;
  have polyH51 := Poly.add polyH17 polyH50;
  have polyH52 := Poly.add polyH18 polyH13;
  have polyH53 := Poly.mul polyH23 polyH52;
  have polyH54 := Poly.add polyH51 polyH53;
  have polyH55 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Universe i × Universe i × Matrix i) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, x_1)) (fun (n : ℕ) (x_1 : Universe n × Universe n × Matrix n) (v : Fin n) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Prod.snd (v, Prod.snd x_1)))) (Prod.fst (v, Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (i : ℕ) => Universe i × Matrix i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => x_1) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.id ℕ (fun (i : ℕ) => Universe i × Matrix i) _)) (@Uniform.vectorMap (fun (n : ℕ) => Universe n × Matrix n) (fun (n : ℕ) => ℕ) _ _ (fun (n : ℕ) (x_1 : Uniform.PredecessorsInput n) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Prod.snd x_1))) (Prod.fst x_1)) Uniform.predecessorsBody) (Sigma.fst x_3) (Sigma.snd x_3)))) polyH54;
  have polyH56 := Poly.of_le (fun (x_3 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_predecessors (Sigma.fst x_3) (Sigma.snd x_3)))) polyH55;
  exact Poly.lift polyH56 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
noncomputable section
namespace ThreeMachine.StackCompiler.Uniform

theorem time_rankFromCounts (n : ℕ) (x : Universe n × ((Fin n → ℕ) × Fin n)) :
    rankFromCounts.time n x =
      (((((fst.comp universeSet).pair snd).comp rankCell.setFilter).comp setCard).comp
        (Realizer.succ.uniform ℕ)).time n x := by
  simp only [rankFromCounts, time_congr, rankCell, rankCellLT, rankCellEQ, rankCellFinLT, rankCellA, rankCellB]
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
theorem time_natLT_le {I : Type u8} (i : I) (a b : ℕ) :
    (natLT (I := I)).time i (a,b) ≤ 100000000000*(a+b+1)^2 := by
  have h := Realizer.time_le_le b a
  have hn := Realizer.time_not_le (decide (b ≤ a))
  have hv := volume_bool (decide (b ≤ a))
  simp only [natLT,time_congr,time_comp,swap,time_pair,time_fst,time_snd,
    time_uniform,volume_prod,volume_nat]
  have hs : a+b+1 ≤ (a+b+1)^2 := le_self_pow (by omega) (by decide)
  nlinarith
theorem time_finVal (n : ℕ) (v : Fin n) : finVal.time n v = volume v+2 := rfl
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
theorem rankCellLT (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCellLT.time (n j) (x j)) 4 := by (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).1);
  have polyH2 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).2.2);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (x j_1).2) (h) polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => x j_1) polyH1 polyH3;
  have polyH5 := Poly.const (n) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ (n j_6) (x j_6)))) polyH6;
  have polyH8 := Poly.add polyH3 polyH5;
  have polyH9 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ (n j_6) (Prod.snd (x j_6))))) polyH8;
  have polyH10 := Poly.add polyH7 polyH9;
  have polyH11 := Poly.const (n) (10);
  have polyH12 := Poly.const (n) (1);
  have polyH13 := Poly.add polyH3 polyH12;
  have polyH14 := Poly.mul polyH11 polyH13;
  have polyH15 := Poly.add polyH10 polyH14;
  have polyH16 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _) (n j_6) (x j_6)))) polyH15;
  have polyH17 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ (n j_6) (x j_6)))) polyH6;
  have polyH18 := Poly.add polyH16 polyH17;
  have polyH19 := Poly.const (n) (20);
  have polyH20 := Poly.add polyH4 (h);
  have polyH21 := Poly.add polyH20 polyH1;
  have polyH22 := Poly.add polyH21 polyH12;
  have polyH23 := Poly.mul polyH19 polyH22;
  have polyH24 := Poly.add polyH18 polyH23;
  have polyH25 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (n j_6) (x j_6)))) polyH24;
  have polyH26 := Poly.const (n) (1000000000);
  have polyH27 := Poly.add polyH0 polyH12;
  have polyH28 := Poly.mul polyH26 polyH27;
  have polyH29 := Poly.add (h) polyH0;
  have polyH30 := Poly.add polyH29 polyH12;
  have polyH31 := Poly.mul polyH28 polyH30;
  have polyH32 := Poly.of_le (fun (j_6 : J) => (@Uniform.time_functionGet_le (fun (n_1 : ℕ) => ℕ) _ (n j_6) (Prod.fst (Prod.snd (x j_6))) (Prod.fst (x j_6)))) polyH31;
  have polyH33 := Poly.add polyH25 polyH32;
  have polyH34 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)), Prod.fst (x j_1))) (h) polyH1;
  have polyH35 := Poly.add polyH34 polyH12;
  have polyH36 := Poly.mul polyH11 polyH35;
  have polyH37 := Poly.add polyH33 polyH36;
  have polyH38 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _)) (@Uniform.functionGet (fun (n_1 : ℕ) => ℕ) _) (n j_6) (x j_6)))) polyH37;
  have polyH39 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ (n j_6) (Prod.snd (x j_6))))) polyH8;
  have polyH40 := Poly.add polyH7 polyH39;
  have polyH41 := Poly.add polyH40 polyH14;
  have polyH42 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _) (n j_6) (x j_6)))) polyH41;
  have polyH43 := Poly.add polyH16 polyH42;
  have polyH44 := Poly.volumeFin polyH0 (fun (j_1 : J) => (Prod.snd (x j_1)).2);
  have polyH45 := Poly.add polyH20 polyH44;
  have polyH46 := Poly.add polyH45 polyH12;
  have polyH47 := Poly.mul polyH19 polyH46;
  have polyH48 := Poly.add polyH43 polyH47;
  have polyH49 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (n j_6) (x j_6)))) polyH48;
  have polyH50 := Poly.of_le (fun (j_6 : J) => (@Uniform.time_functionGet_le (fun (n_1 : ℕ) => ℕ) _ (n j_6) (Prod.fst (Prod.snd (x j_6))) (Prod.snd (Prod.snd (x j_6))))) polyH31;
  have polyH51 := Poly.add polyH49 polyH50;
  have polyH52 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)), Prod.snd (Prod.snd (x j_1)))) (h) polyH44;
  have polyH53 := Poly.add polyH52 polyH12;
  have polyH54 := Poly.mul polyH11 polyH53;
  have polyH55 := Poly.add polyH51 polyH54;
  have polyH56 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1))) (fun (n_1 : ℕ) (x_1 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _))) (@Uniform.functionGet (fun (n_1 : ℕ) => ℕ) _) (n j_6) (x j_6)))) polyH55;
  have polyH57 := Poly.add polyH38 polyH56;
  have polyH58 := Poly.natFunctionApply (fun (j_1 : J) => Prod.fst (x j_1)) (h);
  have polyH59 := Poly.volumeNat polyH58;
  have polyH60 := Poly.add polyH4 polyH59;
  have polyH61 := Poly.natFunctionApply (fun (j_1 : J) => Prod.snd (Prod.snd (x j_1))) (h);
  have polyH62 := Poly.volumeNat polyH61;
  have polyH63 := Poly.add polyH60 polyH62;
  have polyH64 := Poly.add polyH63 polyH12;
  have polyH65 := Poly.mul polyH19 polyH64;
  have polyH66 := Poly.add polyH57 polyH65;
  have polyH67 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.RankCellInput) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1))) (Uniform.rankCellA) (Uniform.rankCellB) (n j_6) (x j_6)))) polyH66;
  have polyH68 := Poly.const (n) (100000000000);
  have polyH69 := Poly.add polyH58 polyH61;
  have polyH70 := Poly.add polyH69 polyH12;
  have polyH71 := Poly.pow polyH70 (2);
  have polyH72 := Poly.mul polyH68 polyH71;
  have polyH73 := Poly.of_le (fun (j_6 : J) => (@Uniform.time_natLT_le (ℕ) (n j_6) (Prod.fst (Prod.snd (x j_6)) (Prod.fst (x j_6))) (Prod.fst (Prod.snd (x j_6)) (Prod.snd (Prod.snd (x j_6)))))) polyH72;
  have polyH74 := Poly.add polyH67 polyH73;
  have polyH75 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)) (Prod.fst (x j_1)), Prod.fst (Prod.snd (x j_1)) (Prod.snd (Prod.snd (x j_1))))) polyH59 polyH62;
  have polyH76 := Poly.add polyH75 polyH12;
  have polyH77 := Poly.mul polyH11 polyH76;
  have polyH78 := Poly.add polyH74 polyH77;
  have polyH79 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.RankCellInput) (fun (i : ℕ) => ℕ × ℕ) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (fun (x_1 : ℕ) (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 < Prod.snd x_2)) (@Uniform.pair ℕ Uniform.RankCellInput (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1))) Uniform.rankCellA Uniform.rankCellB) (@Uniform.natLT ℕ) (n j_6) (x j_6)))) polyH78;
  exact Poly.lift polyH79 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem rankCellEQ (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCellEQ.time (n j) (x j)) 4 := by (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).1);
  have polyH2 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).2.2);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (x j_1).2) (h) polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => x j_1) polyH1 polyH3;
  have polyH5 := Poly.const (n) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ (n j_6) (x j_6)))) polyH6;
  have polyH8 := Poly.add polyH3 polyH5;
  have polyH9 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ (n j_6) (Prod.snd (x j_6))))) polyH8;
  have polyH10 := Poly.add polyH7 polyH9;
  have polyH11 := Poly.const (n) (10);
  have polyH12 := Poly.const (n) (1);
  have polyH13 := Poly.add polyH3 polyH12;
  have polyH14 := Poly.mul polyH11 polyH13;
  have polyH15 := Poly.add polyH10 polyH14;
  have polyH16 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _) (n j_6) (x j_6)))) polyH15;
  have polyH17 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ (n j_6) (x j_6)))) polyH6;
  have polyH18 := Poly.add polyH16 polyH17;
  have polyH19 := Poly.const (n) (20);
  have polyH20 := Poly.add polyH4 (h);
  have polyH21 := Poly.add polyH20 polyH1;
  have polyH22 := Poly.add polyH21 polyH12;
  have polyH23 := Poly.mul polyH19 polyH22;
  have polyH24 := Poly.add polyH18 polyH23;
  have polyH25 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (n j_6) (x j_6)))) polyH24;
  have polyH26 := Poly.const (n) (1000000000);
  have polyH27 := Poly.add polyH0 polyH12;
  have polyH28 := Poly.mul polyH26 polyH27;
  have polyH29 := Poly.add (h) polyH0;
  have polyH30 := Poly.add polyH29 polyH12;
  have polyH31 := Poly.mul polyH28 polyH30;
  have polyH32 := Poly.of_le (fun (j_6 : J) => (@Uniform.time_functionGet_le (fun (n_1 : ℕ) => ℕ) _ (n j_6) (Prod.fst (Prod.snd (x j_6))) (Prod.fst (x j_6)))) polyH31;
  have polyH33 := Poly.add polyH25 polyH32;
  have polyH34 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)), Prod.fst (x j_1))) (h) polyH1;
  have polyH35 := Poly.add polyH34 polyH12;
  have polyH36 := Poly.mul polyH11 polyH35;
  have polyH37 := Poly.add polyH33 polyH36;
  have polyH38 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _)) (@Uniform.functionGet (fun (n_1 : ℕ) => ℕ) _) (n j_6) (x j_6)))) polyH37;
  have polyH39 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ (n j_6) (Prod.snd (x j_6))))) polyH8;
  have polyH40 := Poly.add polyH7 polyH39;
  have polyH41 := Poly.add polyH40 polyH14;
  have polyH42 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _) (n j_6) (x j_6)))) polyH41;
  have polyH43 := Poly.add polyH16 polyH42;
  have polyH44 := Poly.volumeFin polyH0 (fun (j_1 : J) => (Prod.snd (x j_1)).2);
  have polyH45 := Poly.add polyH20 polyH44;
  have polyH46 := Poly.add polyH45 polyH12;
  have polyH47 := Poly.mul polyH19 polyH46;
  have polyH48 := Poly.add polyH43 polyH47;
  have polyH49 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (n j_6) (x j_6)))) polyH48;
  have polyH50 := Poly.of_le (fun (j_6 : J) => (@Uniform.time_functionGet_le (fun (n_1 : ℕ) => ℕ) _ (n j_6) (Prod.fst (Prod.snd (x j_6))) (Prod.snd (Prod.snd (x j_6))))) polyH31;
  have polyH51 := Poly.add polyH49 polyH50;
  have polyH52 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)), Prod.snd (Prod.snd (x j_1)))) (h) polyH44;
  have polyH53 := Poly.add polyH52 polyH12;
  have polyH54 := Poly.mul polyH11 polyH53;
  have polyH55 := Poly.add polyH51 polyH54;
  have polyH56 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1))) (fun (n_1 : ℕ) (x_1 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × (Fin i → ℕ) × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → ℕ) Fin _ _))) (@Uniform.functionGet (fun (n_1 : ℕ) => ℕ) _) (n j_6) (x j_6)))) polyH55;
  have polyH57 := Poly.add polyH38 polyH56;
  have polyH58 := Poly.natFunctionApply (fun (j_1 : J) => Prod.fst (x j_1)) (h);
  have polyH59 := Poly.volumeNat polyH58;
  have polyH60 := Poly.add polyH4 polyH59;
  have polyH61 := Poly.natFunctionApply (fun (j_1 : J) => Prod.snd (Prod.snd (x j_1))) (h);
  have polyH62 := Poly.volumeNat polyH61;
  have polyH63 := Poly.add polyH60 polyH62;
  have polyH64 := Poly.add polyH63 polyH12;
  have polyH65 := Poly.mul polyH19 polyH64;
  have polyH66 := Poly.add polyH57 polyH65;
  have polyH67 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.RankCellInput) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1))) (Uniform.rankCellA) (Uniform.rankCellB) (n j_6) (x j_6)))) polyH66;
  have polyH68 := Poly.const (n) (10000000000);
  have polyH69 := Poly.add polyH58 polyH61;
  have polyH70 := Poly.add polyH69 polyH12;
  have polyH71 := Poly.pow polyH70 (2);
  have polyH72 := Poly.mul polyH68 polyH71;
  have polyH73 := Poly.of_le (fun (j_6 : J) => (@Realizer.time_eqNat_le (Prod.fst (Prod.snd (x j_6)) (Prod.fst (x j_6))) (Prod.fst (Prod.snd (x j_6)) (Prod.snd (Prod.snd (x j_6)))))) polyH72;
  have polyH74 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ × ℕ) (Bool) _ _ (fun (x_1 : ℕ × ℕ) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (Realizer.eqNat) (n j_6) ((Prod.fst (Prod.snd (x j_6)) (Prod.fst (x j_6)), Prod.fst (Prod.snd (x j_6)) (Prod.snd (Prod.snd (x j_6)))))))) polyH73;
  have polyH75 := Poly.add polyH67 polyH74;
  have polyH76 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (Prod.snd (x j_1)) (Prod.fst (x j_1)), Prod.fst (Prod.snd (x j_1)) (Prod.snd (Prod.snd (x j_1))))) polyH59 polyH62;
  have polyH77 := Poly.add polyH76 polyH12;
  have polyH78 := Poly.mul polyH11 polyH77;
  have polyH79 := Poly.add polyH75 polyH78;
  have polyH80 := Poly.of_le (fun (j_6 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.RankCellInput) (fun (i : ℕ) => ℕ × ℕ) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (fun (x_1 : ℕ) (x_2 : ℕ × ℕ) => Decidable.decide (Prod.fst x_2 = Prod.snd x_2)) (@Uniform.pair ℕ Uniform.RankCellInput (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Uniform.RankCellInput n_1) => Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1))) Uniform.rankCellA Uniform.rankCellB) (Realizer.uniform Realizer.eqNat ℕ) (n j_6) (x j_6)))) polyH79;
  exact Poly.lift polyH80 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem rankCellFinLT (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCellFinLT.time (n j) (x j)) 4 := by
  simp only [Uniform.rankCellFinLT, Uniform.time_comp, Uniform.time_pair, Uniform.time_fst, Uniform.time_snd, Uniform.time_finVal, Function.comp_apply]
  (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).1);
  have polyH2 := Poly.volumeFin polyH0 (fun (j_1 : J) => (x j_1).2.2);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (x j_1).2) (h) polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => x j_1) polyH1 polyH3;
  have polyH5 := Poly.const (n) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.add polyH1 polyH5;
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.const (n) (10);
  have polyH10 := Poly.const (n) (1);
  have polyH11 := Poly.add polyH1 polyH10;
  have polyH12 := Poly.mul polyH9 polyH11;
  have polyH13 := Poly.add polyH8 polyH12;
  have polyH14 := Poly.add polyH3 polyH5;
  have polyH15 := Poly.add polyH6 polyH14;
  have polyH16 := Poly.add polyH3 polyH10;
  have polyH17 := Poly.mul polyH9 polyH16;
  have polyH18 := Poly.add polyH15 polyH17;
  have polyH19 := Poly.volumeFin polyH0 (fun (j_1 : J) => (Prod.snd (x j_1)).2);
  have polyH20 := Poly.add polyH19 polyH5;
  have polyH21 := Poly.add polyH18 polyH20;
  have polyH22 := Poly.add polyH19 polyH10;
  have polyH23 := Poly.mul polyH9 polyH22;
  have polyH24 := Poly.add polyH21 polyH23;
  have polyH25 := Poly.add polyH13 polyH24;
  have polyH26 := Poly.const (n) (20);
  have polyH27 := Poly.finVal polyH0 (fun (j_1 : J) => Prod.fst (x j_1));
  have polyH28 := Poly.volumeNat polyH27;
  have polyH29 := Poly.add polyH4 polyH28;
  have polyH30 := Poly.finVal polyH0 (fun (j_1 : J) => Prod.snd (Prod.snd (x j_1)));
  have polyH31 := Poly.volumeNat polyH30;
  have polyH32 := Poly.add polyH29 polyH31;
  have polyH33 := Poly.add polyH32 polyH10;
  have polyH34 := Poly.mul polyH26 polyH33;
  have polyH35 := Poly.add polyH25 polyH34;
  have polyH36 := Poly.const (n) (100000000000);
  have polyH37 := Poly.add polyH27 polyH30;
  have polyH38 := Poly.add polyH37 polyH10;
  have polyH39 := Poly.pow polyH38 (2);
  have polyH40 := Poly.mul polyH36 polyH39;
  have polyH41 := Poly.of_le (fun (j_6 : J) => (@Uniform.time_natLT_le (ℕ) (n j_6) (Fin.val (Prod.fst (x j_6))) (Fin.val (Prod.snd (Prod.snd (x j_6)))))) polyH40;
  have polyH42 := Poly.add polyH35 polyH41;
  have polyH43 := Poly.volumeProd (fun (j_1 : J) => (Fin.val (Prod.fst (x j_1)), Fin.val (Prod.snd (Prod.snd (x j_1))))) polyH28 polyH31;
  have polyH44 := Poly.add polyH43 polyH10;
  have polyH45 := Poly.mul polyH9 polyH44;
  have polyH46 := Poly.add polyH42 polyH45;
  exact Poly.lift polyH46 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem rankCell (h : Poly n (fun j => volume (x j).2.1) 2) :
    Poly n (fun j => Uniform.rankCell.time (n j) (x j)) 4 := by
  have h1 := rankCellLT n x h
  have h2 := rankCellEQ n x h
  have h3 := rankCellFinLT n x h
  (
  have polyH0 := Poly.add (h2) (h3);
  have polyH1 := Poly.const (n) (20);
  have polyH2 := Poly.size (n);
  have polyH3 := Poly.volumeFin polyH2 (fun (j_1 : J) => (x j_1).1);
  have polyH4 := Poly.volumeFin polyH2 (fun (j_1 : J) => (x j_1).2.2);
  have polyH5 := Poly.volumeProd (fun (j_1 : J) => (x j_1).2) (h) polyH4;
  have polyH6 := Poly.volumeProd (fun (j_1 : J) => x j_1) polyH3 polyH5;
  have polyH7 := Poly.mul polyH1 polyH6;
  have polyH8 := Poly.add polyH0 polyH7;
  have polyH9 := Poly.const (n) (11000);
  have polyH10 := Poly.add polyH8 polyH9;
  have polyH11 := Poly.of_le (fun (j_9 : J) => (@Uniform.time_andD_le (ℕ) (Uniform.RankCellInput) _ (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1) = Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1)) (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => Prod.fst x_1 < Prod.snd (Prod.snd x_1)) _ _ (Uniform.rankCellEQ) (Uniform.rankCellFinLT) (n j_9) (x j_9))) polyH10;
  have polyH12 := Poly.add (h1) polyH11;
  have polyH13 := Poly.add polyH12 polyH7;
  have polyH14 := Poly.add polyH13 polyH9;
  have polyH15 := Poly.of_le (fun (j_9 : J) => (@Uniform.time_orD_le (ℕ) (Uniform.RankCellInput) _ (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1) < Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1)) (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1) = Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1) ∧ Prod.fst x_1 < Prod.snd (Prod.snd x_1)) _ _ (Uniform.rankCellLT) (@Uniform.andD ℕ Uniform.RankCellInput _ (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1) = Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) x_1)) (fun (i : ℕ) (x_1 : Uniform.RankCellInput i) => Prod.fst x_1 < Prod.snd (Prod.snd x_1)) _ _ Uniform.rankCellEQ Uniform.rankCellFinLT) (n j_9) (x j_9))) polyH14;
  exact Poly.lift polyH15 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)
theorem rankFromCounts (U : ∀ j, Universe (n j)) (r : ∀ j, Fin (n j) → ℕ)
    (v : ∀ j, Fin (n j)) (h : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => Uniform.rankFromCounts.time (n j) (U j,(r j,v j))) 5 := by
  have hc := rankCell (fun p : Poly.ListPool (fun j => (Finset.univ : Finset (Fin (n j))).sort (· ≤ ·)) => n p.1)
    (fun p => (p.2.1,(r p.1,v p.1))) (h.precomp Sigma.fst)
  (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.volumeFin polyH0 (fun (j_1 : J) => v j_1);
  have polyH3 := Poly.volumeProd (fun (j_1 : J) => (r j_1, v j_1)) (h) polyH2;
  have polyH4 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1, v j_1)) polyH1 polyH3;
  have polyH5 := Poly.const (n) (2);
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ (n j_9) ((U j_9, r j_9, v j_9))))) polyH6;
  have polyH8 := Poly.add polyH1 polyH5;
  have polyH9 := Poly.add polyH7 polyH8;
  have polyH10 := Poly.const (n) (10);
  have polyH11 := Poly.const (n) (1);
  have polyH12 := Poly.add polyH1 polyH11;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (Universe) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (Uniform.universeSet) (n j_9) ((U j_9, r j_9, v j_9))))) polyH14;
  have polyH16 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ (n j_9) ((U j_9, r j_9, v j_9))))) polyH6;
  have polyH17 := Poly.add polyH15 polyH16;
  have polyH18 := Poly.const (n) (20);
  have polyH19 := Poly.volumeFinset polyH0 (fun (j_1 : J) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1)));
  have polyH20 := Poly.add polyH4 polyH19;
  have polyH21 := Poly.add polyH20 polyH3;
  have polyH22 := Poly.add polyH21 polyH11;
  have polyH23 := Poly.mul polyH18 polyH22;
  have polyH24 := Poly.add polyH17 polyH23;
  have polyH25 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) (n j_9) ((U j_9, r j_9, v j_9))))) polyH24;
  have polyH26 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1))) polyH19 polyH3;
  have polyH27 := Poly.add polyH26 polyH5;
  have polyH28 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _ (n j_9) (((fun (x : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst (U j_9, r j_9, v j_9)), Prod.snd (U j_9, r j_9, v j_9)))))) polyH27;
  have polyH29 := Poly.add polyH19 polyH5;
  have polyH30 := Poly.add polyH28 polyH29;
  have polyH31 := Poly.add polyH19 polyH11;
  have polyH32 := Poly.mul polyH10 polyH31;
  have polyH33 := Poly.add polyH30 polyH32;
  have polyH34 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _) (Uniform.setList) (n j_9) (((fun (x : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst (U j_9, r j_9, v j_9)), Prod.snd (U j_9, r j_9, v j_9)))))) polyH33;
  have polyH35 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _ (n j_9) (((fun (x : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst (U j_9, r j_9, v j_9)), Prod.snd (U j_9, r j_9, v j_9)))))) polyH27;
  have polyH36 := Poly.add polyH34 polyH35;
  have polyH37 := Poly.add polyH26 polyH19;
  have polyH38 := Poly.add polyH37 polyH3;
  have polyH39 := Poly.add polyH38 polyH11;
  have polyH40 := Poly.mul polyH18 polyH39;
  have polyH41 := Poly.add polyH36 polyH40;
  have polyH42 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) i) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _ _ (fun (i : ℕ) (x : (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) i) => (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) i (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n_1 : ℕ) => Finset (Fin n_1)) i × (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _) (n j_9) (((fun (x : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst (U j_9, r j_9, v j_9)), Prod.snd (U j_9, r j_9, v j_9)))))) polyH41;
  have polyH43 := Poly.finsetCard polyH0 (fun (j_1 : J) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1)));
  have polyH44 := Poly.lengthSort (fun (j_1 : J) => Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1))) polyH43;
  have polyH45 := @Poly.filterTime (ℕ) (J) (n) (Fin) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (Finset.sort (Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1))) fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2, Prod.snd ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1)))) (fun (j_1 : J) => Prod.snd (Finset.sort (Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1))) fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2, Prod.snd ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1)))) (fun (i : ℕ) (x : Uniform.RankCellInput i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∧ Prod.fst x < Prod.snd (Prod.snd x))) (Uniform.rankCell) (1) (4) (2 * 1) (Max.max (2) (1)) polyH44 (hc) polyH19 polyH3;
  have polyH46 := Poly.add polyH42 polyH45;
  have polyH47 := Poly.volumeProd (fun (j_1 : J) => (Finset.sort (Prod.fst ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1))) fun (x1 x2 : Fin (n j_1)) => x1 ≤ x2, Prod.snd ((fun (x : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst (U j_1, r j_1, v j_1)), Prod.snd (U j_1, r j_1, v j_1)))) polyH19 polyH3;
  have polyH48 := Poly.add polyH47 polyH11;
  have polyH49 := Poly.mul polyH10 polyH48;
  have polyH50 := Poly.add polyH46 polyH49;
  have polyH51 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => List (Fin i) × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) (x : Finset (Fin i) × (Fin i → ℕ) × Fin i) => (Finset.sort (Prod.fst x) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x)) (fun (i : ℕ) (x : List (Fin i) × (Fin i → ℕ) × Fin i) => List.filter (fun (a : Fin i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x)))) (Prod.fst x)) (@Uniform.onFst ℕ (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _ _ (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.sort s fun (x1 x2 : Fin n_1) => x1 ≤ x2) Uniform.setList) (@Uniform.filter ℕ Fin (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ _ (fun (i : ℕ) (x : Uniform.RankCellInput i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∧ Prod.fst x < Prod.snd (Prod.snd x))) Uniform.rankCell) (n j_9) (((fun (x : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst (U j_9, r j_9, v j_9)), Prod.snd (U j_9, r j_9, v j_9)))))) polyH50;
  have polyH52 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_setFilter (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ (fun (i : ℕ) (x : Uniform.RankCellInput i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∧ Prod.fst x < Prod.snd (Prod.snd x))) (Uniform.rankCell) (n j_9) (((fun (x : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst (U j_9, r j_9, v j_9)), Prod.snd (U j_9, r j_9, v j_9)))))) polyH51;
  have polyH53 := Poly.add polyH25 polyH52;
  have polyH54 := Poly.add polyH26 polyH11;
  have polyH55 := Poly.mul polyH10 polyH54;
  have polyH56 := Poly.add polyH53 polyH55;
  have polyH57 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Finset (Fin i) × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => ((fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x), Prod.snd x)) (fun (n_1 : ℕ) (x : Finset (Fin n_1) × (Fin n_1 → ℕ) × Fin n_1) => {a ∈ Prod.fst x | Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _)) (@Uniform.setFilter (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ (fun (i : ℕ) (x : Uniform.RankCellInput i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∧ Prod.fst x < Prod.snd (Prod.snd x))) Uniform.rankCell) (n j_9) ((U j_9, r j_9, v j_9))))) polyH56;
  have polyH58 := Poly.reparam (@Costs.setCard) (fun (j_1 : J) => Sigma.mk (n j_1) ((fun (x : Finset (Fin (n j_1)) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => {a ∈ Prod.fst x | Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x))) = Bool.true}) ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) polyH0;
  have polyH59 := Poly.add polyH57 polyH58;
  have polyH60 := Poly.volumeFinset polyH0 (fun (j_1 : J) => {a ∈ Prod.fst ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)) | Decidable.decide (Prod.fst ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) < Prod.snd ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) ∨ Prod.fst ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) = Prod.snd ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) ∧ Prod.fst (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1))) < Prod.snd (Prod.snd (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1))))) = Bool.true});
  have polyH61 := Poly.add polyH60 polyH11;
  have polyH62 := Poly.mul polyH10 polyH61;
  have polyH63 := Poly.add polyH59 polyH62;
  have polyH64 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (x_1 : Finset (Fin i) × (Fin i → ℕ) × Fin i) => {a ∈ Prod.fst x_1 | Decidable.decide (Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) < Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) ∨ Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) = Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) ∧ Prod.fst (a, Prod.snd x_1) < Prod.snd (Prod.snd (a, Prod.snd x_1))) = Bool.true}) ((fun (x_1 : Universe i × (Fin i → ℕ) × Fin i) => ((fun (x_2 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), Prod.snd x_1)) x)) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.card s) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Finset (Fin i) × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => ((fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x), Prod.snd x)) (fun (n_1 : ℕ) (x : Finset (Fin n_1) × (Fin n_1 → ℕ) × Fin n_1) => {a ∈ Prod.fst x | Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _)) (@Uniform.setFilter (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ (fun (i : ℕ) (x : Uniform.RankCellInput i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∧ Prod.fst x < Prod.snd (Prod.snd x))) Uniform.rankCell)) (Uniform.setCard) (n j_9) ((U j_9, r j_9, v j_9))))) polyH63;
  have polyH65 := Poly.const (n) (200);
  have polyH66 := Poly.finsetCard polyH0 (fun (j_1 : J) => {a ∈ Prod.fst ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)) | Decidable.decide (Prod.fst ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) < Prod.snd ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) ∨ Prod.fst ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) = Prod.snd ((fun (x : Uniform.RankCellInput (n j_1)) => (Prod.fst (Prod.snd x) (Prod.fst x), Prod.fst (Prod.snd x) (Prod.snd (Prod.snd x)))) (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1)))) ∧ Prod.fst (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1))) < Prod.snd (Prod.snd (a, Prod.snd ((fun (x : Universe (n j_1) × (Fin (n j_1) → ℕ) × Fin (n j_1)) => ((fun (x_1 : Universe (n j_1)) => @Finset.univ (Fin (n j_1)) (Fin.fintype (n j_1))) (Prod.fst x), Prod.snd x)) (U j_1, r j_1, v j_1))))) = Bool.true});
  have polyH67 := Poly.add polyH66 polyH11;
  have polyH68 := Poly.mul polyH65 polyH67;
  have polyH69 := Poly.of_le (fun (j_9 : J) => (@Realizer.time_succ_le ((fun (s : Finset (Fin (n j_9))) => Finset.card s) ((fun (x : Finset (Fin (n j_9)) × (Fin (n j_9) → ℕ) × Fin (n j_9)) => {a ∈ Prod.fst x | Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x))) = Bool.true}) ((fun (x : Universe (n j_9) × (Fin (n j_9) → ℕ) × Fin (n j_9)) => ((fun (x_1 : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst x), Prod.snd x)) (U j_9, r j_9, v j_9)))))) polyH68;
  have polyH70 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ) (ℕ) _ _ (fun (n_1 : ℕ) => n_1 + 1) (Realizer.succ) (n j_9) ((fun (s : Finset (Fin (n j_9))) => Finset.card s) ((fun (x : Finset (Fin (n j_9)) × (Fin (n j_9) → ℕ) × Fin (n j_9)) => {a ∈ Prod.fst x | Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput (n j_9)) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x))) = Bool.true}) ((fun (x : Universe (n j_9) × (Fin (n j_9) → ℕ) × Fin (n j_9)) => ((fun (x_1 : Universe (n j_9)) => @Finset.univ (Fin (n j_9)) (Fin.fintype (n j_9))) (Prod.fst x), Prod.snd x)) (U j_9, r j_9, v j_9))))))) polyH69;
  have polyH71 := Poly.add polyH64 polyH70;
  have polyH72 := Poly.volumeNat polyH66;
  have polyH73 := Poly.add polyH72 polyH11;
  have polyH74 := Poly.mul polyH10 polyH73;
  have polyH75 := Poly.add polyH71 polyH74;
  have polyH76 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (s : Finset (Fin i)) => Finset.card s) ((fun (x_1 : Finset (Fin i) × (Fin i → ℕ) × Fin i) => {a ∈ Prod.fst x_1 | Decidable.decide (Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) < Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) ∨ Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) = Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) ∧ Prod.fst (a, Prod.snd x_1) < Prod.snd (Prod.snd (a, Prod.snd x_1))) = Bool.true}) ((fun (x_1 : Universe i × (Fin i → ℕ) × Fin i) => ((fun (x_2 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), Prod.snd x_1)) x))) (fun (x n_1 : ℕ) => n_1 + 1) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (x_1 : Finset (Fin i) × (Fin i → ℕ) × Fin i) => {a ∈ Prod.fst x_1 | Decidable.decide (Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) < Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) ∨ Prod.fst ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) = Prod.snd ((fun (x_2 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_2) (Prod.fst x_2), Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)))) (a, Prod.snd x_1)) ∧ Prod.fst (a, Prod.snd x_1) < Prod.snd (Prod.snd (a, Prod.snd x_1))) = Bool.true}) ((fun (x_1 : Universe i × (Fin i → ℕ) × Fin i) => ((fun (x_2 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x_1), Prod.snd x_1)) x)) (fun (n_1 : ℕ) (s : Finset (Fin n_1)) => Finset.card s) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (i : ℕ) => Finset (Fin i) × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => ((fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x), Prod.snd x)) (fun (n_1 : ℕ) (x : Finset (Fin n_1) × (Fin n_1 → ℕ) × Fin n_1) => {a ∈ Prod.fst x | Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) < Prod.snd ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) = Prod.snd ((fun (x_1 : Uniform.RankCellInput n_1) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) (a, Prod.snd x)) ∧ Prod.fst (a, Prod.snd x) < Prod.snd (Prod.snd (a, Prod.snd x))) = Bool.true}) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => Finset (Fin n_1)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ) × Fin i) => (fun (x_1 : Universe i) => @Finset.univ (Fin i) (Fin.fintype i)) (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) Universe (fun (n_1 : ℕ) => Finset (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => @Finset.univ (Fin n_1) (Fin.fintype n_1)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _) Uniform.universeSet) (@Uniform.snd ℕ Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _)) (@Uniform.setFilter (fun (n_1 : ℕ) => (Fin n_1 → ℕ) × Fin n_1) _ (fun (i : ℕ) (x : Uniform.RankCellInput i) => Decidable.decide (Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) < Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∨ Prod.fst ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) = Prod.snd ((fun (x_1 : Uniform.RankCellInput i) => (Prod.fst (Prod.snd x_1) (Prod.fst x_1), Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)))) x) ∧ Prod.fst x < Prod.snd (Prod.snd x))) Uniform.rankCell)) Uniform.setCard) (Realizer.uniform Realizer.succ ℕ) (n j_9) ((U j_9, r j_9, v j_9))))) polyH75;
  have polyH77 := Poly.of_le (fun (j_9 : J) => (le_of_eq (@Uniform.time_rankFromCounts (n j_9) ((U j_9, r j_9, v j_9))))) polyH76;
  exact Poly.lift polyH77 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem rank : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => Uniform.rank.time x.1 x.2) 6 := by
  let n : (Σ n, Universe n × Matrix n) → ℕ := Sigma.fst
  have hv := Poly.volumePredecessors (fun x : Σ n, Universe n × Matrix n => x.2.2) (Poly.size n)
  have hC := rankFromCounts (fun p : Poly.ListPool (fun x : Σ n, Universe n × Matrix n => List.finRange x.1) => p.1.1)
    (fun p => p.1.2.1) (fun p => Structure.predecessorCount (matrixRel p.1.2.2))
    (fun p => p.2.1) (hv.precomp Sigma.fst)
  (
  have polyH0 := Poly.size (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_5) (Sigma.snd x_5)))) polyH5;
  have polyH7 := Poly.reparam (@Costs.predecessors) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0;
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (20);
  have polyH10 := Poly.volumeUniverse polyH0 (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Sigma.snd x_1).1);
  have polyH11 := Poly.add polyH3 polyH10;
  have polyH12 := Poly.add polyH11 (hv);
  have polyH13 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (1);
  have polyH14 := Poly.add polyH12 polyH13;
  have polyH15 := Poly.mul polyH9 polyH14;
  have polyH16 := Poly.add polyH8 polyH15;
  have polyH17 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.predecessors) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH16;
  have polyH18 := Poly.add polyH6 polyH17;
  have polyH19 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1))))) polyH10 (hv);
  have polyH20 := Poly.add polyH11 polyH19;
  have polyH21 := Poly.add polyH20 polyH13;
  have polyH22 := Poly.mul polyH9 polyH21;
  have polyH23 := Poly.add polyH18 polyH22;
  have polyH24 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd x_1)))) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.predecessors) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH23;
  have polyH25 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1))))) polyH10 polyH19;
  have polyH26 := Poly.add polyH25 polyH4;
  have polyH27 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ (Sigma.fst x_5) ((Prod.fst (Sigma.snd x_5), Prod.fst (Sigma.snd x_5), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_5)))))))) polyH26;
  have polyH28 := Poly.add polyH10 polyH4;
  have polyH29 := Poly.add polyH27 polyH28;
  have polyH30 := Poly.const (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (10);
  have polyH31 := Poly.add polyH10 polyH13;
  have polyH32 := Poly.mul polyH30 polyH31;
  have polyH33 := Poly.add polyH29 polyH32;
  have polyH34 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) i) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.finRange n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _) (Uniform.universeList) (Sigma.fst x_5) ((Prod.fst (Sigma.snd x_5), Prod.fst (Sigma.snd x_5), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_5)))))))) polyH33;
  have polyH35 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ (Sigma.fst x_5) ((Prod.fst (Sigma.snd x_5), Prod.fst (Sigma.snd x_5), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_5)))))))) polyH26;
  have polyH36 := Poly.add polyH34 polyH35;
  have polyH37 := Poly.volumeFinRange polyH0;
  have polyH38 := Poly.add polyH25 polyH37;
  have polyH39 := Poly.add polyH38 polyH19;
  have polyH40 := Poly.add polyH39 polyH13;
  have polyH41 := Poly.mul polyH9 polyH40;
  have polyH42 := Poly.add polyH36 polyH41;
  have polyH43 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) i) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) i) => (fun (n_1 : ℕ) (x_2 : Universe n_1) => List.finRange n_1) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) i) Universe (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.finRange n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _) Uniform.universeList) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _) (Sigma.fst x_5) ((Prod.fst (Sigma.snd x_5), Prod.fst (Sigma.snd x_5), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_5)))))))) polyH42;
  have polyH44 := Poly.lengthFinRange polyH0;
  have polyH45 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q));
  have polyH46 := Poly.volumeFin polyH45 (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (Sigma.snd q).1);
  have polyH47 := Poly.volumeUniverse polyH45 (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (Sigma.snd (Sigma.fst q)).1);
  have polyH48 := Poly.precomp (hv) (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => Sigma.fst q);
  have polyH49 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))) polyH47 polyH48;
  have polyH50 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH46 polyH49;
  have polyH51 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)) (2);
  have polyH52 := Poly.add polyH50 polyH51;
  have polyH53 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH52;
  have polyH54 := Poly.add polyH49 polyH51;
  have polyH55 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Fin i → ℕ) _ _ (Sigma.fst (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH54;
  have polyH56 := Poly.add polyH53 polyH55;
  have polyH57 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)) (10);
  have polyH58 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)) (1);
  have polyH59 := Poly.add polyH49 polyH58;
  have polyH60 := Poly.mul polyH57 polyH59;
  have polyH61 := Poly.add polyH56 polyH60;
  have polyH62 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (Universe) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH61;
  have polyH63 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Fin i → ℕ) _ _ (Sigma.fst (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH54;
  have polyH64 := Poly.add polyH53 polyH63;
  have polyH65 := Poly.add polyH64 polyH60;
  have polyH66 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH65;
  have polyH67 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH52;
  have polyH68 := Poly.add polyH66 polyH67;
  have polyH69 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Sigma.fst q)) (20);
  have polyH70 := Poly.add polyH50 polyH48;
  have polyH71 := Poly.add polyH70 polyH46;
  have polyH72 := Poly.add polyH71 polyH58;
  have polyH73 := Poly.mul polyH69 polyH72;
  have polyH74 := Poly.add polyH68 polyH73;
  have polyH75 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH74;
  have polyH76 := Poly.add polyH62 polyH75;
  have polyH77 := Poly.add polyH50 polyH47;
  have polyH78 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH48 polyH46;
  have polyH79 := Poly.add polyH77 polyH78;
  have polyH80 := Poly.add polyH79 polyH58;
  have polyH81 := Poly.mul polyH69 polyH80;
  have polyH82 := Poly.add polyH76 polyH81;
  have polyH83 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (Universe) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH82;
  have polyH84 := Poly.add polyH83 (hC);
  have polyH85 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))) polyH47 polyH78;
  have polyH86 := Poly.add polyH85 polyH58;
  have polyH87 := Poly.mul polyH57 polyH86;
  have polyH88 := Poly.add polyH84 polyH87;
  have polyH89 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ) × Fin n_1) => Finset.card ({y ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Prod.fst (Prod.snd x_1) y < Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∨ Prod.fst (Prod.snd x_1) y = Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∧ y < Prod.snd (Prod.snd x_1)}) + 1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _))) (Uniform.rankFromCounts) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))))) polyH88;
  have polyH90 := Poly.finsetCard polyH45 (fun (q : Poly.Pool (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) => {y ∈ @Finset.univ (Fin (Sigma.fst (Sigma.fst q))) (Fin.fintype (Sigma.fst (Sigma.fst q))) | Prod.fst (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))) y < Prod.fst (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))) (Prod.snd (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))))) ∨ Prod.fst (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))) y = Prod.fst (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q))))))))) (Prod.snd (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))))) ∧ y < Prod.snd (Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × Universe (Sigma.fst (Sigma.fst q)) × (Fin (Sigma.fst (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Prod.fst (Sigma.snd (Sigma.fst q)), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd (Sigma.fst q)))))))))});
  have polyH91 := Poly.add polyH90 polyH58;
  have polyH92 := Poly.volumeNat polyH91;
  have polyH93 := @Poly.mapTime (ℕ) ((n_1 : ℕ) × Universe n_1 × Matrix n_1) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (Fin) (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ _ (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Sigma.fst x_1) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => Prod.snd (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (fun (x_2 : Universe i × (Fin i → ℕ) × Fin i) => Finset.card ({y ∈ @Finset.univ (Fin i) (Fin.fintype i) | Prod.fst (Prod.snd x_2) y < Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∨ Prod.fst (Prod.snd x_2) y = Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∧ y < Prod.snd (Prod.snd x_2)}) + 1) ((fun (x_2 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_2), Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ) × Fin n_1) => Finset.card ({y ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Prod.fst (Prod.snd x_1) y < Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∨ Prod.fst (Prod.snd x_1) y = Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∧ y < Prod.snd (Prod.snd x_1)}) + 1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _))) Uniform.rankFromCounts) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (Max.max (Max.max (2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (2 * 1) (2 * 1)) (0))) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0)) (Max.max (Max.max (2 * 1) (2 * 1)) (0))) (0 + Max.max (Max.max (2 * 1) (2 * 1)) (0))) (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (2 * 1)) (1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (2 * 1))) (2 * 1)) (Max.max (2 * 1) (1))) (0))) (5)) (0 + Max.max (Max.max (2 * 1) (Max.max (2 * 1) (1))) (0))) (2 * 1) (Max.max (2 * 1) (2 * 1)) (Max.max (1) (0)) polyH44 polyH89 polyH37 polyH19 polyH92;
  have polyH94 := Poly.add polyH43 polyH93;
  have polyH95 := Poly.volumeProd (fun (x_1 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_1)))))) polyH37 polyH19;
  have polyH96 := Poly.add polyH95 polyH13;
  have polyH97 := Poly.mul polyH30 polyH96;
  have polyH98 := Poly.add polyH94 polyH97;
  have polyH99 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => List (Fin i) × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Universe i × (Fin i → ℕ)) => (List.finRange i, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Universe i × (Fin i → ℕ)) => List.map (fun (a : Fin i) => (fun (x_2 : Universe i × (Fin i → ℕ) × Fin i) => Finset.card ({y ∈ @Finset.univ (Fin i) (Fin.fintype i) | Prod.fst (Prod.snd x_2) y < Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∨ Prod.fst (Prod.snd x_2) y = Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∧ y < Prod.snd (Prod.snd x_2)}) + 1) ((fun (x_2 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_2), Prod.snd (Prod.snd x_2), Prod.fst x_2)) (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.onFst ℕ Universe (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ _ (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.finRange n_1) Uniform.universeList) (@Uniform.map ℕ Fin (fun (n_1 : ℕ) => ℕ) (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (fun (x_2 : Universe i × (Fin i → ℕ) × Fin i) => Finset.card ({y ∈ @Finset.univ (Fin i) (Fin.fintype i) | Prod.fst (Prod.snd x_2) y < Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∨ Prod.fst (Prod.snd x_2) y = Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∧ y < Prod.snd (Prod.snd x_2)}) + 1) ((fun (x_2 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_2), Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ) × Fin n_1) => Finset.card ({y ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Prod.fst (Prod.snd x_1) y < Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∨ Prod.fst (Prod.snd x_1) y = Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∧ y < Prod.snd (Prod.snd x_1)}) + 1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _))) Uniform.rankFromCounts)) (Sigma.fst x_5) ((Prod.fst (Sigma.snd x_5), Prod.fst (Sigma.snd x_5), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_5)))))))) polyH98;
  have polyH100 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_vectorMap (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (fun (x_2 : Universe i × (Fin i → ℕ) × Fin i) => Finset.card ({y ∈ @Finset.univ (Fin i) (Fin.fintype i) | Prod.fst (Prod.snd x_2) y < Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∨ Prod.fst (Prod.snd x_2) y = Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∧ y < Prod.snd (Prod.snd x_2)}) + 1) ((fun (x_2 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_2), Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ) × Fin n_1) => Finset.card ({y ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Prod.fst (Prod.snd x_1) y < Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∨ Prod.fst (Prod.snd x_1) y = Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∧ y < Prod.snd (Prod.snd x_1)}) + 1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _))) Uniform.rankFromCounts) (Sigma.fst x_5) ((Prod.fst (Sigma.snd x_5), Prod.fst (Sigma.snd x_5), OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd (Sigma.snd x_5)))))))) polyH99;
  have polyH101 := Poly.add polyH24 polyH100;
  have polyH102 := Poly.add polyH25 polyH13;
  have polyH103 := Poly.mul polyH30 polyH102;
  have polyH104 := Poly.add polyH101 polyH103;
  have polyH105 := Poly.of_le (fun (x_5 : (n_1 : ℕ) × Universe n_1 × Matrix n_1) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Universe i × Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, Prod.fst x_1, OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd x_1)))) (fun (n_1 : ℕ) (x_1 : Universe n_1 × Universe n_1 × (Fin n_1 → ℕ)) (v : Fin n_1) => (fun (x_2 : Universe n_1 × (Fin n_1 → ℕ) × Fin n_1) => Finset.card ({y ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Prod.fst (Prod.snd x_2) y < Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∨ Prod.fst (Prod.snd x_2) y = Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∧ y < Prod.snd (Prod.snd x_2)}) + 1) ((fun (x_2 : Fin n_1 × Universe n_1 × (Fin n_1 → ℕ)) => (Prod.fst (Prod.snd x_2), Prod.snd (Prod.snd x_2), Prod.fst x_2)) (v, Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd x_1)))) (@Uniform.fst ℕ Universe Matrix _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x_1 : Universe n_1 × Matrix n_1) => OAI.ThreeMachine.Structure.predecessorCount (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.predecessors)) (@Uniform.vectorMap (fun (n_1 : ℕ) => Universe n_1 × (Fin n_1 → ℕ)) (fun (n_1 : ℕ) => ℕ) _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (fun (x_2 : Universe i × (Fin i → ℕ) × Fin i) => Finset.card ({y ∈ @Finset.univ (Fin i) (Fin.fintype i) | Prod.fst (Prod.snd x_2) y < Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∨ Prod.fst (Prod.snd x_2) y = Prod.fst (Prod.snd x_2) (Prod.snd (Prod.snd x_2)) ∧ y < Prod.snd (Prod.snd x_2)}) + 1) ((fun (x_2 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_2), Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ) × Fin i) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), Prod.snd (Prod.snd x_1), Prod.fst x_1)) (fun (n_1 : ℕ) (x_1 : Universe n_1 × (Fin n_1 → ℕ) × Fin n_1) => Finset.card ({y ∈ @Finset.univ (Fin n_1) (Fin.fintype n_1) | Prod.fst (Prod.snd x_1) y < Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∨ Prod.fst (Prod.snd x_1) y = Prod.fst (Prod.snd x_1) (Prod.snd (Prod.snd x_1)) ∧ y < Prod.snd (Prod.snd x_1)}) + 1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) Universe (fun (i : ℕ) => (Fin i → ℕ) × Fin i) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Universe i × (Fin i → ℕ)) => Prod.snd (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Universe i × (Fin i → ℕ)) _ _))) Uniform.rankFromCounts)) (Sigma.fst x_5) (Sigma.snd x_5)))) polyH104;
  exact Poly.lift polyH105 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem reverseRank (U : ∀ j, Universe (n j)) (r : ∀ j, Fin (n j) → ℕ)
    (h : Poly n (fun j => volume (r j)) 2) :
    Poly n (fun j => Uniform.reverseRank.time (n j) (U j,r j)) 5 := by (
  have polyH0 := Poly.size (n);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (j_1 : J) => U j_1);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, r j_1)) polyH1 (h);
  have polyH3 := Poly.const (n) (2);
  have polyH4 := Poly.add polyH2 polyH3;
  have polyH5 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => Fin i → ℕ) _ _ (n j_7) ((U j_7, r j_7))))) polyH4;
  have polyH6 := Poly.add polyH1 polyH3;
  have polyH7 := Poly.const (n) (100000);
  have polyH8 := Poly.lengthFinRange polyH0;
  have polyH9 := Poly.const (n) (1);
  have polyH10 := Poly.add polyH8 polyH9;
  have polyH11 := Poly.mul polyH7 polyH10;
  have polyH12 := Poly.volumeFinRange polyH0;
  have polyH13 := Poly.add polyH12 polyH9;
  have polyH14 := Poly.mul polyH11 polyH13;
  have polyH15 := Poly.of_le (fun (j_7 : J) => (@Uniform.time_length_le (ℕ) (Fin) _ (n j_7) (List.finRange (n j_7)))) polyH14;
  have polyH16 := Poly.add polyH6 polyH15;
  have polyH17 := Poly.const (n) (10);
  have polyH18 := Poly.mul polyH17 polyH13;
  have polyH19 := Poly.add polyH16 polyH18;
  have polyH20 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (n j_7) (Prod.fst (U j_7, r j_7))))) polyH19;
  have polyH21 := Poly.add polyH5 polyH20;
  have polyH22 := Poly.add polyH1 polyH9;
  have polyH23 := Poly.mul polyH17 polyH22;
  have polyH24 := Poly.add polyH21 polyH23;
  have polyH25 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (Universe) (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (Uniform.universeNumber) (n j_7) ((U j_7, r j_7))))) polyH24;
  have polyH26 := Poly.const (n) (200);
  have polyH27 := Poly.add polyH0 polyH9;
  have polyH28 := Poly.mul polyH26 polyH27;
  have polyH29 := Poly.of_le (fun (j_7 : J) => (@Realizer.time_succ_le ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))))) polyH28;
  have polyH30 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ) (ℕ) _ _ (fun (n_1 : ℕ) => n_1 + 1) (Realizer.succ) (n j_7) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7)))))) polyH29;
  have polyH31 := Poly.add polyH25 polyH30;
  have polyH32 := Poly.volumeNat polyH0;
  have polyH33 := Poly.add polyH32 polyH9;
  have polyH34 := Poly.mul polyH17 polyH33;
  have polyH35 := Poly.add polyH31 polyH34;
  have polyH36 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (x n_1 : ℕ) => n_1 + 1) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) Uniform.universeNumber) (Realizer.uniform Realizer.succ ℕ) (n j_7) ((U j_7, r j_7))))) polyH35;
  have polyH37 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => Fin i → ℕ) _ _ (n j_7) ((U j_7, r j_7))))) polyH4;
  have polyH38 := Poly.add polyH36 polyH37;
  have polyH39 := Poly.const (n) (20);
  have polyH40 := Poly.volumeNat polyH27;
  have polyH41 := Poly.add polyH2 polyH40;
  have polyH42 := Poly.add polyH41 (h);
  have polyH43 := Poly.add polyH42 polyH9;
  have polyH44 := Poly.mul polyH39 polyH43;
  have polyH45 := Poly.add polyH38 polyH44;
  have polyH46 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (x : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (n_1 : ℕ) => n_1 + 1) ((fun (x_1 : Universe i) => i) (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (x n_1 : ℕ) => n_1 + 1) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) Uniform.universeNumber) (Realizer.uniform Realizer.succ ℕ)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (n j_7) ((U j_7, r j_7))))) polyH45;
  have polyH47 := Poly.add polyH5 polyH46;
  have polyH48 := Poly.add polyH2 polyH1;
  have polyH49 := Poly.volumeProd (fun (j_1 : J) => ((fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1))) polyH40 (h);
  have polyH50 := Poly.add polyH48 polyH49;
  have polyH51 := Poly.add polyH50 polyH9;
  have polyH52 := Poly.mul polyH39 polyH51;
  have polyH53 := Poly.add polyH47 polyH52;
  have polyH54 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (Universe) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => ((fun (n_1 : ℕ) => n_1 + 1) ((fun (x_1 : Universe i) => i) (Prod.fst x)), Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (x : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (n_1 : ℕ) => n_1 + 1) ((fun (x_1 : Universe i) => i) (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (x n_1 : ℕ) => n_1 + 1) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) Uniform.universeNumber) (Realizer.uniform Realizer.succ ℕ)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _)) (n j_7) ((U j_7, r j_7))))) polyH53;
  have polyH55 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1))) polyH1 polyH49;
  have polyH56 := Poly.add polyH55 polyH3;
  have polyH57 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (n j_7) ((Prod.fst (U j_7, r j_7), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))), Prod.snd (U j_7, r j_7)))))) polyH56;
  have polyH58 := Poly.add polyH57 polyH6;
  have polyH59 := Poly.add polyH58 polyH23;
  have polyH60 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) (Universe) (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) (Uniform.universeList) (n j_7) ((Prod.fst (U j_7, r j_7), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))), Prod.snd (U j_7, r j_7)))))) polyH59;
  have polyH61 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ (n j_7) ((Prod.fst (U j_7, r j_7), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))), Prod.snd (U j_7, r j_7)))))) polyH56;
  have polyH62 := Poly.add polyH60 polyH61;
  have polyH63 := Poly.add polyH55 polyH12;
  have polyH64 := Poly.add polyH63 polyH49;
  have polyH65 := Poly.add polyH64 polyH9;
  have polyH66 := Poly.mul polyH39 polyH65;
  have polyH67 := Poly.add polyH62 polyH66;
  have polyH68 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) => (fun (n_1 : ℕ) (x_1 : Universe n_1) => List.finRange n_1) i (Prod.fst x)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) i) Universe (fun (n_1 : ℕ) => List (Fin n_1)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) (@Uniform.fst ℕ Universe (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) Uniform.universeList) (@Uniform.snd ℕ Universe (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _) (n j_7) ((Prod.fst (U j_7, r j_7), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))), Prod.snd (U j_7, r j_7)))))) polyH67;
  have polyH69 := Poly.size (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q));
  have polyH70 := Poly.volumeFin polyH69 (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (Sigma.snd q).1);
  have polyH71 := Poly.const (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q)) (1);
  have polyH72 := Poly.add polyH69 polyH71;
  have polyH73 := Poly.volumeNat polyH72;
  have polyH74 := Poly.precomp (h) (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => Sigma.fst q);
  have polyH75 := Poly.volumeProd (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => ((fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))) polyH73 polyH74;
  have polyH76 := Poly.volumeProd (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))) polyH70 polyH75;
  have polyH77 := Poly.const (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q)) (2);
  have polyH78 := Poly.add polyH76 polyH77;
  have polyH79 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH78;
  have polyH80 := Poly.add polyH75 polyH77;
  have polyH81 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ (n (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH80;
  have polyH82 := Poly.add polyH79 polyH81;
  have polyH83 := Poly.const (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q)) (10);
  have polyH84 := Poly.add polyH75 polyH71;
  have polyH85 := Poly.mul polyH83 polyH84;
  have polyH86 := Poly.add polyH82 polyH85;
  have polyH87 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH86;
  have polyH88 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ (n (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH80;
  have polyH89 := Poly.add polyH79 polyH88;
  have polyH90 := Poly.add polyH89 polyH85;
  have polyH91 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH90;
  have polyH92 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH78;
  have polyH93 := Poly.add polyH91 polyH92;
  have polyH94 := Poly.const (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q)) (20);
  have polyH95 := Poly.add polyH76 polyH74;
  have polyH96 := Poly.add polyH95 polyH70;
  have polyH97 := Poly.add polyH96 polyH71;
  have polyH98 := Poly.mul polyH94 polyH97;
  have polyH99 := Poly.add polyH93 polyH98;
  have polyH100 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) (Fin) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH99;
  have polyH101 := Poly.const (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q)) (1000000000);
  have polyH102 := Poly.mul polyH101 polyH72;
  have polyH103 := Poly.add polyH74 polyH69;
  have polyH104 := Poly.add polyH103 polyH71;
  have polyH105 := Poly.mul polyH102 polyH104;
  have polyH106 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (@Uniform.time_functionGet_le (fun (i : ℕ) => ℕ) _ (n (Sigma.fst q)) (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))) (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))))) polyH105;
  have polyH107 := Poly.add polyH100 polyH106;
  have polyH108 := Poly.volumeProd (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))) polyH74 polyH70;
  have polyH109 := Poly.add polyH108 polyH71;
  have polyH110 := Poly.mul polyH83 polyH109;
  have polyH111 := Poly.add polyH107 polyH110;
  have polyH112 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH111;
  have polyH113 := Poly.add polyH87 polyH112;
  have polyH114 := Poly.add polyH76 polyH73;
  have polyH115 := Poly.natFunctionApply (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => Prod.snd ((fun (x : Fin (n (Sigma.fst q)) × ℕ × (Fin (n (Sigma.fst q)) → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))) polyH74;
  have polyH116 := Poly.volumeNat polyH115;
  have polyH117 := Poly.add polyH114 polyH116;
  have polyH118 := Poly.add polyH117 polyH71;
  have polyH119 := Poly.mul polyH94 polyH118;
  have polyH120 := Poly.add polyH113 polyH119;
  have polyH121 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _)) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH120;
  have polyH122 := Poly.const (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => n (Sigma.fst q)) (10000000);
  have polyH123 := Poly.add polyH72 polyH115;
  have polyH124 := Poly.add polyH123 polyH71;
  have polyH125 := Poly.pow polyH124 (2);
  have polyH126 := Poly.mul polyH122 polyH125;
  have polyH127 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (@Realizer.time_sub_le (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))) ((fun (x : (Fin (n (Sigma.fst q)) → ℕ) × Fin (n (Sigma.fst q))) => Prod.fst x (Prod.snd x)) ((fun (x : Fin (n (Sigma.fst q)) × ℕ × (Fin (n (Sigma.fst q)) → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH126;
  have polyH128 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_uniform (ℕ) (ℕ × ℕ) (ℕ) _ _ (fun (x : ℕ × ℕ) => Prod.fst x - Prod.snd x) (Realizer.sub) (n (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))), (fun (x : (Fin (n (Sigma.fst q)) → ℕ) × Fin (n (Sigma.fst q))) => Prod.fst x (Prod.snd x)) ((fun (x : Fin (n (Sigma.fst q)) × ℕ × (Fin (n (Sigma.fst q)) → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))))) polyH127;
  have polyH129 := Poly.add polyH121 polyH128;
  have polyH130 := Poly.volumeProd (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))), (fun (x : (Fin (n (Sigma.fst q)) → ℕ) × Fin (n (Sigma.fst q))) => Prod.fst x (Prod.snd x)) ((fun (x : Fin (n (Sigma.fst q)) × ℕ × (Fin (n (Sigma.fst q)) → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))))) polyH73 polyH116;
  have polyH131 := Poly.add polyH130 polyH71;
  have polyH132 := Poly.mul polyH83 polyH131;
  have polyH133 := Poly.add polyH129 polyH132;
  have polyH134 := Poly.of_le (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x), (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x))) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _))) (Realizer.uniform Realizer.sub ℕ) (n (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q))))))))) polyH133;
  have polyH135 := Poly.sub polyH72 (fun (q : Poly.Pool (fun (j_1 : J) => n j_1) fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) => Prod.snd ((fun (x : Fin (n (Sigma.fst q)) × ℕ × (Fin (n (Sigma.fst q)) → ℕ)) => (Prod.fst (Prod.snd x), (fun (x_1 : (Fin (n (Sigma.fst q)) → ℕ) × Fin (n (Sigma.fst q))) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin (n (Sigma.fst q)) × ℕ × (Fin (n (Sigma.fst q)) → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (n (Sigma.fst q)), Prod.snd (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n (Sigma.fst q))) => n (Sigma.fst q)) (Prod.fst (U (Sigma.fst q), r (Sigma.fst q)))), Prod.snd (U (Sigma.fst q), r (Sigma.fst q)))))));
  have polyH136 := Poly.volumeNat polyH135;
  have polyH137 := @Poly.mapTime (ℕ) (J) (n) (Fin) (fun (x : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ _ (fun (j_1 : J) => n j_1) (fun (j_1 : J) => Prod.fst (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) (fun (j_1 : J) => Prod.snd (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), (fun (x_2 : (Fin i → ℕ) × Fin i) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1))) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x), (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x))) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _))) (Realizer.uniform Realizer.sub ℕ)) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (Max.max (1) (0)) (2))) (0)) (Max.max (Max.max (Max.max (1) (0)) (2)) (0))) (0 + Max.max (Max.max (Max.max (1) (0)) (2)) (0))) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (Max.max (1) (0)) (2))) (0)) (Max.max (Max.max (Max.max (1) (0)) (2)) (0))) (0 + Max.max (Max.max (Max.max (1) (0)) (2)) (0))) (Max.max (Max.max (1) (Max.max (Max.max (1) (0)) (2))) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (Max.max (1) (0)) (2))) (2)) (1)) (0))) (0 + Max.max (1) (0) + Max.max (Max.max (2) (1)) (0))) (0 + Max.max (Max.max (2) (1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (Max.max (1) (0)) (2))) (Max.max (1) (0))) (2)) (0))) (0 + Max.max (Max.max (Max.max (1) (0)) (2)) (0) * 2)) (0 + Max.max (Max.max (Max.max (1) (0)) (2)) (0))) (2 * 1) (Max.max (Max.max (1) (0)) (2)) (Max.max (1) (0)) polyH8 polyH134 polyH12 polyH49 polyH136;
  have polyH138 := Poly.add polyH68 polyH137;
  have polyH139 := Poly.volumeProd (fun (j_1 : J) => (List.finRange (n j_1), Prod.snd (Prod.fst (U j_1, r j_1), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_1)) => n j_1) (Prod.fst (U j_1, r j_1))), Prod.snd (U j_1, r j_1)))) polyH12 polyH49;
  have polyH140 := Poly.add polyH139 polyH9;
  have polyH141 := Poly.mul polyH17 polyH140;
  have polyH142 := Poly.add polyH138 polyH141;
  have polyH143 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => List (Fin i) × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => List ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × ℕ × (Fin i → ℕ)) => (List.finRange i, Prod.snd x)) (fun (i : ℕ) (x : List (Fin i) × ℕ × (Fin i → ℕ)) => List.map (fun (a : Fin i) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), (fun (x_2 : (Fin i → ℕ) × Fin i) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1))) (a, Prod.snd x))) (Prod.fst x)) (@Uniform.onFst ℕ Universe (fun (n_1 : ℕ) => List (Fin n_1)) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ _ (fun (n_1 : ℕ) (x : Universe n_1) => List.finRange n_1) Uniform.universeList) (@Uniform.map ℕ Fin (fun (x : ℕ) => ℕ) (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), (fun (x_2 : (Fin i → ℕ) × Fin i) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1))) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x), (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x))) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _))) (Realizer.uniform Realizer.sub ℕ))) (n j_7) ((Prod.fst (U j_7, r j_7), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))), Prod.snd (U j_7, r j_7)))))) polyH142;
  have polyH144 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_vectorMap (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) (fun (x : ℕ) => ℕ) _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), (fun (x_2 : (Fin i → ℕ) × Fin i) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1))) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x), (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x))) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _))) (Realizer.uniform Realizer.sub ℕ)) (n j_7) ((Prod.fst (U j_7, r j_7), (fun (n_1 : ℕ) => n_1 + 1) ((fun (x : Universe (n j_7)) => n j_7) (Prod.fst (U j_7, r j_7))), Prod.snd (U j_7, r j_7)))))) polyH143;
  have polyH145 := Poly.add polyH54 polyH144;
  have polyH146 := Poly.add polyH55 polyH9;
  have polyH147 := Poly.mul polyH17 polyH146;
  have polyH148 := Poly.add polyH145 polyH147;
  have polyH149 := Poly.of_le (fun (j_7 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (i : ℕ) => Universe i × ℕ × (Fin i → ℕ)) (fun (n_1 : ℕ) => Fin n_1 → ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (Prod.fst x, (fun (n_1 : ℕ) => n_1 + 1) ((fun (x_1 : Universe i) => i) (Prod.fst x)), Prod.snd x)) (fun (n_1 : ℕ) (x : Universe n_1 × ℕ × (Fin n_1 → ℕ)) (v : Fin n_1) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) ((fun (x_1 : Fin n_1 × ℕ × (Fin n_1 → ℕ)) => (Prod.fst (Prod.snd x_1), (fun (x_2 : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : Fin n_1 × ℕ × (Fin n_1 → ℕ)) => (Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1))) (v, Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => ((fun (n_1 : ℕ) => n_1 + 1) ((fun (x_1 : Universe i) => i) (Prod.fst x)), Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (x : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (n_1 : ℕ) => n_1 + 1) ((fun (x_1 : Universe i) => i) (Prod.fst x))) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n_1 : ℕ) => ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × (Fin i → ℕ)) => (fun (x_1 : Universe i) => i) (Prod.fst x)) (fun (x n_1 : ℕ) => n_1 + 1) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × (Fin i → ℕ)) Universe (fun (n_1 : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n_1 : ℕ) (x : Universe n_1) => n_1) (@Uniform.fst ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _) Uniform.universeNumber) (Realizer.uniform Realizer.succ ℕ)) (@Uniform.snd ℕ Universe (fun (i : ℕ) => Fin i → ℕ) _ _))) (@Uniform.vectorMap (fun (n_1 : ℕ) => ℕ × (Fin n_1 → ℕ)) (fun (x : ℕ) => ℕ) _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x_1), (fun (x_2 : (Fin i → ℕ) × Fin i) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_2), Prod.fst x_2)) x_1))) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × ℕ) (fun (x : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.fst (Prod.snd x), (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x))) (fun (x : ℕ) (x_1 : ℕ × ℕ) => Prod.fst x_1 - Prod.snd x_1) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.fst (Prod.snd x)) (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (fun (x_1 : (Fin i → ℕ) × Fin i) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x_1), Prod.fst x_1)) x)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => (Fin i → ℕ) × Fin i) (fun (i : ℕ) => ℕ) _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => (Prod.snd (Prod.snd x), Prod.fst x)) (fun (n_1 : ℕ) (x : (Fin n_1 → ℕ) × Fin n_1) => Prod.fst x (Prod.snd x)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) Fin _ _ _ (fun (i : ℕ) (x : Fin i × ℕ × (Fin i → ℕ)) => Prod.snd (Prod.snd x)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × ℕ × (Fin i → ℕ)) (fun (i : ℕ) => ℕ × (Fin i → ℕ)) (fun (i : ℕ) => Fin i → ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => ℕ) (fun (i : ℕ) => Fin i → ℕ) _ _)) (@Uniform.fst ℕ Fin (fun (i : ℕ) => ℕ × (Fin i → ℕ)) _ _)) (@Uniform.functionGet (fun (i : ℕ) => ℕ) _))) (Realizer.uniform Realizer.sub ℕ))) (n j_7) ((U j_7, r j_7))))) polyH148;
  exact Poly.lift polyH149 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem ranks (frame : Bool) : Poly (fun x : Σ n, Universe n × Matrix n => x.1)
    (fun x => (Uniform.ranks frame).time x.1 x.2) 6 := by
  cases frame
  · (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1);
  have polyH1 := Poly.reparam (@Costs.rank) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  · have hv := Poly.volumeRank (fun x : Σ n, Universe n × Matrix n => x.2.2)
      (Poly.size (fun x : Σ n, Universe n × Matrix n => x.1))
    have hr := reverseRank (fun x : Σ n, Universe n × Matrix n => x.1) (fun x => x.2.1)
      (fun x => Structure.jobRank (matrixRel x.2.2)) hv
    (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.1);
  have polyH2 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => x_1.2) polyH1 polyH2;
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_4 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (Matrix) _ _ (Sigma.fst x_4) (Sigma.snd x_4)))) polyH5;
  have polyH7 := Poly.reparam (@Costs.rank) (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0;
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (20);
  have polyH10 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (Sigma.snd x_1).1);
  have polyH11 := Poly.add polyH3 polyH10;
  have polyH12 := Poly.add polyH11 (hv);
  have polyH13 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (1);
  have polyH14 := Poly.add polyH12 polyH13;
  have polyH15 := Poly.mul polyH9 polyH14;
  have polyH16 := Poly.add polyH8 polyH15;
  have polyH17 := Poly.of_le (fun (x_4 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Universe) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × Matrix n) => OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) (Uniform.rank) (Sigma.fst x_4) (Sigma.snd x_4)))) polyH16;
  have polyH18 := Poly.add polyH17 (hr);
  have polyH19 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => Sigma.fst x_1) (10);
  have polyH20 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × Matrix n) => (Prod.fst (Sigma.snd x_1), OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd (Sigma.snd x_1))))) polyH10 (hv);
  have polyH21 := Poly.add polyH20 polyH13;
  have polyH22 := Poly.mul polyH19 polyH21;
  have polyH23 := Poly.add polyH18 polyH22;
  have polyH24 := Poly.of_le (fun (x_4 : (n : ℕ) × Universe n × Matrix n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (fun (i : ℕ) => Universe i × (Fin i → ℕ)) (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Matrix i) => (Prod.fst x_1, OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1)))) (fun (n : ℕ) (x_1 : Universe n × (Fin n → ℕ)) (v : Fin n) => n + 1 - Prod.snd x_1 v) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × Matrix i) Universe (fun (n : ℕ) => Fin n → ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × Matrix n) => OAI.ThreeMachine.Structure.jobRank (matrixRel (Prod.snd x_1))) (@Uniform.fst ℕ Universe Matrix _ _) Uniform.rank) (Uniform.reverseRank) (Sigma.fst x_4) (Sigma.snd x_4)))) polyH23;
  exact Poly.lift polyH24 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.ranks := @OAI.ThreeMachine.StackCompiler.Costs.ranks
