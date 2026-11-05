-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.triplesE
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:48:53.818903+00:00
-- url     : https://prove2.me/submissions/ca317178-1a73-4121-95ec-4caeff6c22c9

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false


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

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

theorem triplesE : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.triplesE.time x.1 x.2) 20 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeUniverse polyH0 (fun (x_1 : (n : ℕ) × Universe n) => x_1.2);
  have polyH2 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.add polyH3 polyH3;
  have polyH5 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (20);
  have polyH6 := Poly.volumeFinRange polyH0;
  have polyH7 := Poly.add polyH1 polyH6;
  have polyH8 := Poly.add polyH7 polyH6;
  have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (1);
  have polyH10 := Poly.add polyH8 polyH9;
  have polyH11 := Poly.mul polyH5 polyH10;
  have polyH12 := Poly.add polyH4 polyH11;
  have polyH13 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (Uniform.universeList) (Uniform.universeList) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH12;
  have polyH14 := Poly.lengthFinRange polyH0;
  have polyH15 := Poly.size (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH16 := Poly.volumeFin polyH15 (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (Sigma.snd q).1);
  have polyH17 := Poly.volumeFinRange polyH15;
  have polyH18 := Poly.volumeProd (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q))))) polyH16 polyH17;
  have polyH19 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (2);
  have polyH20 := Poly.add polyH18 polyH19;
  have polyH21 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => List (Fin i)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) polyH20;
  have polyH22 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => List (Fin i)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) polyH20;
  have polyH23 := Poly.add polyH21 polyH22;
  have polyH24 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (20);
  have polyH25 := Poly.add polyH18 polyH17;
  have polyH26 := Poly.add polyH25 polyH16;
  have polyH27 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (1);
  have polyH28 := Poly.add polyH26 polyH27;
  have polyH29 := Poly.mul polyH24 polyH28;
  have polyH30 := Poly.add polyH23 polyH29;
  have polyH31 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × List (Fin i)) (fun (i : ℕ) => List (Fin i)) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => List (Fin i)) _ _) (@Uniform.fst ℕ Fin (fun (i : ℕ) => List (Fin i)) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) polyH30;
  have polyH32 := Poly.lengthFinRange polyH15;
  have polyH33 := Poly.size (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q));
  have polyH34 := Poly.volumeFin polyH33 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (Sigma.snd q).1);
  have polyH35 := Poly.volumePool (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) polyH6;
  have polyH36 := Poly.precomp polyH35 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => Sigma.fst q);
  have polyH37 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q)))))))) polyH34 polyH36;
  have polyH38 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q)) (2);
  have polyH39 := Poly.add polyH37 polyH38;
  have polyH40 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))))) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (Fin) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))))))))) polyH39;
  have polyH41 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))))) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (Fin) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))))))))) polyH39;
  have polyH42 := Poly.add polyH40 polyH41;
  have polyH43 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q)) (20);
  have polyH44 := Poly.add polyH37 polyH36;
  have polyH45 := Poly.add polyH44 polyH34;
  have polyH46 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q)) (1);
  have polyH47 := Poly.add polyH45 polyH46;
  have polyH48 := Poly.mul polyH43 polyH47;
  have polyH49 := Poly.add polyH42 polyH48;
  have polyH50 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Fin i) (Fin) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin Fin _ _) (@Uniform.fst ℕ Fin Fin _ _) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))))))))) polyH49;
  have polyH51 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) Fin (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))))))) polyH36 polyH34;
  have polyH52 := @Poly.mapTime (ℕ) (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (Fin) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Sigma.fst (Sigma.fst q)) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) (fun (i : ℕ) (x_1 : Fin i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.swap ℕ Fin Fin _ _) (1) (Max.max (Max.max (Max.max (Max.max (1) (2 * 1)) (0)) (Max.max (Max.max (1) (2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (2 * 1)) (2 * 1)) (1)) (0))) (2 * 1) (1) (Max.max (2 * 1) (1)) polyH32 polyH50 polyH17 polyH16 polyH51;
  have polyH53 := Poly.add polyH31 polyH52;
  have polyH54 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (10);
  have polyH55 := Poly.volumeProd (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))) polyH17 polyH16;
  have polyH56 := Poly.add polyH55 polyH27;
  have polyH57 := Poly.mul polyH54 polyH56;
  have polyH58 := Poly.add polyH53 polyH57;
  have polyH59 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × List (Fin i)) (fun (i : ℕ) => List (Fin i) × Fin i) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Fin i × List (Fin i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Fin i) => List.map (fun (a : Fin i) => (Prod.snd (a, Prod.snd x_1), Prod.fst (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × List (Fin i)) (fun (i : ℕ) => List (Fin i)) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => List (Fin i)) _ _) (@Uniform.fst ℕ Fin (fun (i : ℕ) => List (Fin i)) _ _)) (@Uniform.map ℕ Fin (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.swap ℕ Fin Fin _ _)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) polyH58;
  have polyH60 := Poly.lengthMap (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (a : Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) polyH32;
  have polyH61 := Poly.size (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q))))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q));
  have polyH62 := Poly.volumeFin polyH61 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q))))))) => (Sigma.snd q).1.1);
  have polyH63 := Poly.volumeFin polyH61 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q))))))) => (Sigma.snd q).1.2);
  have polyH64 := Poly.volumeProd (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q))))))) => (Sigma.snd q).1) polyH62 polyH63;
  have polyH65 := Poly.listVolume (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List (Fin (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q))))))) polyH60 polyH64;
  have polyH66 := @Poly.flatMapTime (ℕ) ((n : ℕ) × Universe n) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Fin) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (fun (x_1 : (n : ℕ) × Universe n) => Prod.snd (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (fun (i : ℕ) (x_1 : Fin i × List (Fin i)) => (fun (x_2 : List (Fin i) × Fin i) => List.map (fun (a : Fin i) => (Prod.snd (a, Prod.snd x_2), Prod.fst (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Fin i × List (Fin i)) => (Prod.snd x_2, Prod.fst x_2)) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × List (Fin i)) (fun (i : ℕ) => List (Fin i) × Fin i) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Fin i × List (Fin i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Fin i) => List.map (fun (a : Fin i) => (Prod.snd (a, Prod.snd x_1), Prod.fst (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × List (Fin i)) (fun (i : ℕ) => List (Fin i)) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => List (Fin i)) _ _) (@Uniform.fst ℕ Fin (fun (i : ℕ) => List (Fin i)) _ _)) (@Uniform.map ℕ Fin (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.swap ℕ Fin Fin _ _))) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (2 * 1)) (0)) (Max.max (Max.max (1) (2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (2 * 1)) (2 * 1)) (1)) (0))) (1 + Max.max (Max.max (Max.max (Max.max (Max.max (1) (2 * 1)) (0)) (Max.max (Max.max (1) (2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (2 * 1)) (2 * 1)) (1)) (0))) (Max.max (2 * 1) (Max.max (1) (1 + Max.max (2 * 1) (1)))))) (0 + Max.max (Max.max (2 * 1) (1)) (0))) (2 * 1) (2 * 1) (1 + Max.max (1) (1)) polyH14 polyH59 polyH6 polyH6 polyH65;
  have polyH67 := Poly.add polyH13 polyH66;
  have polyH68 := Poly.const (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (10);
  have polyH69 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) polyH6 polyH6;
  have polyH70 := Poly.add polyH69 polyH9;
  have polyH71 := Poly.mul polyH68 polyH70;
  have polyH72 := Poly.add polyH67 polyH71;
  have polyH73 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => List (Fin i) × List (Fin i)) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (List.finRange i, List.finRange i)) (fun (i : ℕ) (x_1 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) Uniform.universeList Uniform.universeList) (@Uniform.product ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH72;
  have polyH74 := Poly.add polyH3 polyH73;
  have polyH75 := Poly.lengthProduct polyH14 polyH14;
  have polyH76 := Poly.size (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n) => List.product (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH77 := Poly.volumeFin polyH76 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n) => List.product (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (Sigma.snd q).1.1);
  have polyH78 := Poly.volumeFin polyH76 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n) => List.product (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (Sigma.snd q).1.2);
  have polyH79 := Poly.volumeProd (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × Universe n) => List.product (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (Sigma.snd q).1) polyH77 polyH78;
  have polyH80 := Poly.listVolume (fun (x_1 : (n : ℕ) × Universe n) => List.product (Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) polyH75 polyH79;
  have polyH81 := Poly.add polyH7 polyH80;
  have polyH82 := Poly.add polyH81 polyH9;
  have polyH83 := Poly.mul polyH5 polyH82;
  have polyH84 := Poly.add polyH74 polyH83;
  have polyH85 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_pair (ℕ) (Universe) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe i) => (List.finRange i, List.finRange i)) x_1)) (Uniform.universeList) (@Uniform.comp ℕ Universe (fun (i : ℕ) => List (Fin i) × List (Fin i)) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (List.finRange i, List.finRange i)) (fun (i : ℕ) (x_1 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) Uniform.universeList Uniform.universeList) (@Uniform.product ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH84;
  have polyH86 := Poly.size (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q));
  have polyH87 := Poly.volumeFin polyH86 (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (Sigma.snd q).1);
  have polyH88 := Poly.lengthFinRange polyH86;
  have polyH89 := Poly.lengthProduct polyH88 polyH88;
  have polyH90 := Poly.size (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.product (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))) (Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q));
  have polyH91 := Poly.volumeFin polyH90 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.product (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))) (Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))) => (Sigma.snd q).1.1);
  have polyH92 := Poly.volumeFin polyH90 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.product (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))) (Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))) => (Sigma.snd q).1.2);
  have polyH93 := Poly.volumeProd (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.product (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))) (Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))) => (Sigma.snd q).1) polyH91 polyH92;
  have polyH94 := Poly.listVolume (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.product (Prod.fst ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))) (Prod.snd ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))) polyH89 polyH93;
  have polyH95 := Poly.volumeProd (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))) polyH87 polyH94;
  have polyH96 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (2);
  have polyH97 := Poly.add polyH95 polyH96;
  have polyH98 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) polyH97;
  have polyH99 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) polyH97;
  have polyH100 := Poly.add polyH98 polyH99;
  have polyH101 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (20);
  have polyH102 := Poly.add polyH95 polyH94;
  have polyH103 := Poly.add polyH102 polyH87;
  have polyH104 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (1);
  have polyH105 := Poly.add polyH103 polyH104;
  have polyH106 := Poly.mul polyH101 polyH105;
  have polyH107 := Poly.add polyH100 polyH106;
  have polyH108 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _) (@Uniform.fst ℕ Fin (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) polyH107;
  have polyH109 := Poly.size (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q));
  have polyH110 := Poly.volumeFin polyH109 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (Sigma.snd q).1.1);
  have polyH111 := Poly.volumeFin polyH109 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (Sigma.snd q).1.2);
  have polyH112 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (Sigma.snd q).1) polyH110 polyH111;
  have polyH113 := Poly.volumePool (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) polyH6;
  have polyH114 := Poly.precomp polyH113 (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => Sigma.fst q);
  have polyH115 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q))))))))) polyH112 polyH114;
  have polyH116 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q)) (2);
  have polyH117 := Poly.add polyH115 polyH116;
  have polyH118 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q_1))) × List (Fin (Sigma.fst (Sigma.fst q_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q_1))) => (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))) (Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q_1))) × List (Fin (Sigma.fst (Sigma.fst q_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q_1))) => (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))) (Sigma.snd (Sigma.fst q_1))))))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))))))))) polyH117;
  have polyH119 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q_1))) × List (Fin (Sigma.fst (Sigma.fst q_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q_1))) => (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))) (Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q_1))) × List (Fin (Sigma.fst (Sigma.fst q_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q_1))) => (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))) (Sigma.snd (Sigma.fst q_1))))))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))))))))) polyH117;
  have polyH120 := Poly.add polyH118 polyH119;
  have polyH121 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q)) (20);
  have polyH122 := Poly.add polyH115 polyH114;
  have polyH123 := Poly.add polyH122 polyH112;
  have polyH124 := Poly.const (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q)) (1);
  have polyH125 := Poly.add polyH123 polyH124;
  have polyH126 := Poly.mul polyH121 polyH125;
  have polyH127 := Poly.add polyH120 polyH126;
  have polyH128 := Poly.of_le (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q_1))) × List (Fin (Sigma.fst (Sigma.fst q_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q_1))) => (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))) (Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q_1))) × List (Fin (Sigma.fst (Sigma.fst q_1)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q_1))) => (List.finRange (Sigma.fst (Sigma.fst q_1)), List.finRange (Sigma.fst (Sigma.fst q_1)))) (Sigma.snd (Sigma.fst q_1))))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i × Fin i) (Fin) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) Fin _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) Fin _ _) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))))))))) polyH127;
  have polyH129 := Poly.volumeProd (fun (q : @Poly.Pool ℕ (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q)))) × List (Fin (Sigma.fst (Sigma.fst (Sigma.fst q))))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst (Sigma.fst q)))) => (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))))) (Sigma.snd (Sigma.fst (Sigma.fst q)))))))))) polyH114 polyH112;
  have polyH130 := @Poly.mapTime (ℕ) (@Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) (Fin) _ _ _ (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Sigma.fst (Sigma.fst q)) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) (fun (i : ℕ) (x_1 : (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin i × Fin i) Fin _ _) (1 + 1) (Max.max (Max.max (Max.max (Max.max (Max.max (1) (1)) (2 * 1)) (0)) (Max.max (Max.max (Max.max (1) (1)) (2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (Max.max (1) (1)) (2 * 1)) (2 * 1)) (Max.max (1) (1))) (0))) (1 + 1 + Max.max (1) (1)) (1) (Max.max (2 * 1) (Max.max (1) (1))) polyH89 polyH128 polyH94 polyH87 polyH129;
  have polyH131 := Poly.add polyH108 polyH130;
  have polyH132 := Poly.const (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q)) (10);
  have polyH133 := Poly.volumeProd (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))) polyH94 polyH87;
  have polyH134 := Poly.add polyH133 polyH104;
  have polyH135 := Poly.mul polyH132 polyH134;
  have polyH136 := Poly.add polyH131 polyH135;
  have polyH137 := Poly.of_le (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) × Fin i) (fun (i : ℕ) => List (Fin i × (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (i : ℕ) (x_1 : List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) × Fin i) => List.map (fun (a : Fin i × Fin i) => (Prod.snd (a, Prod.snd x_1), Prod.fst (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _) (@Uniform.fst ℕ Fin (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _)) (@Uniform.map ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) Fin _ _ _ (fun (i : ℕ) (x_1 : (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin i × Fin i) Fin _ _)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) polyH136;
  have polyH138 := Poly.lengthMap (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) polyH89;
  have polyH139 := Poly.size (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Sigma.fst q_1)) (Sigma.fst q));
  have polyH140 := Poly.volumeFin polyH139 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) => (Sigma.snd q).1.1);
  have polyH141 := Poly.volumeFin polyH139 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) => (Sigma.snd q).1.2.1);
  have polyH142 := Poly.volumeFin polyH139 (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) => (Sigma.snd q).1.2.2);
  have polyH143 := Poly.volumeProd (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) => (Sigma.snd q).1.2) polyH141 polyH142;
  have polyH144 := Poly.volumeProd (fun (q : Poly.ListPool fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) => (Sigma.snd q).1) polyH140 polyH143;
  have polyH145 := Poly.listVolume (fun (q : @Poly.Pool ℕ ((n : ℕ) × Universe n) Fin (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) => List.map (fun (a : Fin (Sigma.fst (Sigma.fst q)) × Fin (Sigma.fst (Sigma.fst q))) => (Prod.snd (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))), Prod.fst (a, Prod.snd ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q))))))))) (Prod.fst ((fun (x_1 : Fin (Sigma.fst (Sigma.fst q)) × List ((fun (i : ℕ) => Fin i × Fin i) (Sigma.fst (Sigma.fst q)))) => (Prod.snd x_1, Prod.fst x_1)) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), (fun (x_1 : List (Fin (Sigma.fst (Sigma.fst q))) × List (Fin (Sigma.fst (Sigma.fst q)))) => List.product (Prod.fst x_1) (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst (Sigma.fst q))) => (List.finRange (Sigma.fst (Sigma.fst q)), List.finRange (Sigma.fst (Sigma.fst q)))) (Sigma.snd (Sigma.fst q)))))))) polyH138 polyH144;
  have polyH146 := @Poly.flatMapTime (ℕ) ((n : ℕ) × Universe n) (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (Fin) (fun (i : ℕ) => Fin i × (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _ _ (fun (x_1 : (n : ℕ) × Universe n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n) => Prod.fst (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (x_1 : (n : ℕ) × Universe n) => Prod.snd (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) (fun (i : ℕ) (x_1 : Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) => (fun (x_2 : List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) × Fin i) => List.map (fun (a : Fin i × Fin i) => (Prod.snd (a, Prod.snd x_2), Prod.fst (a, Prod.snd x_2))) (Prod.fst x_2)) ((fun (x_2 : Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) => (Prod.snd x_2, Prod.fst x_2)) x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) × Fin i) (fun (i : ℕ) => List (Fin i × (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (i : ℕ) (x_1 : List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) × Fin i) => List.map (fun (a : Fin i × Fin i) => (Prod.snd (a, Prod.snd x_1), Prod.fst (a, Prod.snd x_1))) (Prod.fst x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _) (@Uniform.fst ℕ Fin (fun (i : ℕ) => List ((fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i)) _ _)) (@Uniform.map ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i) Fin _ _ _ (fun (i : ℕ) (x_1 : (fun (i_1 : ℕ) => Fin i_1 × Fin i_1) i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.swap ℕ (fun (i : ℕ) => Fin i × Fin i) Fin _ _))) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (1 + 1 + Max.max (1) (1))) (0)) (Max.max (Max.max (1) (1 + 1 + Max.max (1) (1))) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (1 + 1 + Max.max (1) (1))) (1 + 1 + Max.max (1) (1))) (1)) (0))) (1 + 1 + Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (1)) (2 * 1)) (0)) (Max.max (Max.max (Max.max (1) (1)) (2 * 1)) (0))) (0 + Max.max (Max.max (Max.max (Max.max (Max.max (1) (1)) (2 * 1)) (2 * 1)) (Max.max (1) (1))) (0))) (Max.max (1 + 1 + Max.max (1) (1)) (Max.max (1) (1 + 1 + Max.max (2 * 1) (Max.max (1) (1))))))) (0 + Max.max (Max.max (1 + 1 + Max.max (1) (1)) (1)) (0))) (2 * 1) (1 + 1 + Max.max (1) (1)) (1 + 1 + Max.max (1) (Max.max (1) (1))) polyH14 polyH137 polyH6 polyH80 polyH145;
  have polyH147 := Poly.add polyH85 polyH146;
  have polyH148 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n) => (List.finRange (Sigma.fst x_1), (fun (x_2 : List (Fin (Sigma.fst x_1)) × List (Fin (Sigma.fst x_1))) => List.product (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : Universe (Sigma.fst x_1)) => (List.finRange (Sigma.fst x_1), List.finRange (Sigma.fst x_1))) (Sigma.snd x_1)))) polyH6 polyH80;
  have polyH149 := Poly.add polyH148 polyH9;
  have polyH150 := Poly.mul polyH68 polyH149;
  have polyH151 := Poly.add polyH147 polyH150;
  have polyH152 := Poly.of_le (fun (x_2 : (n : ℕ) × Universe n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (i : ℕ) => List (Fin i) × List (Fin i × Fin i)) (fun (i : ℕ) => List (Fin i × Fin i × Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (List.finRange i, (fun (x_3 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe i) => (List.finRange i, List.finRange i)) x_1))) (fun (i : ℕ) (x_1 : List (Fin i) × List (Fin i × Fin i)) => List.product (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (i : ℕ) (x_1 : Universe i) => (fun (x_3 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_3) (Prod.snd x_3)) ((fun (x_3 : Universe i) => (List.finRange i, List.finRange i)) x_1)) Uniform.universeList (@Uniform.comp ℕ Universe (fun (i : ℕ) => List (Fin i) × List (Fin i)) (fun (i : ℕ) => List (Fin i × Fin i)) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => (List.finRange i, List.finRange i)) (fun (i : ℕ) (x_1 : List (Fin i) × List (Fin i)) => List.product (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair ℕ Universe (fun (n : ℕ) => List (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) Uniform.universeList Uniform.universeList) (@Uniform.product ℕ Fin Fin _ _))) (@Uniform.product ℕ Fin (fun (i : ℕ) => Fin i × Fin i) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH151;
  exact Poly.lift polyH152 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.triplesE := @OAI.ThreeMachine.StackCompiler.Costs.triplesE
