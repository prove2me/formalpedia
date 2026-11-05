-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.unaryAnswer
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:52:33.230786+00:00
-- url     : https://prove2.me/submissions/c5a690bc-cf9e-4f41-9402-6b236aeaa4a2

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_closureMatrixStep
import Theorems.Thm_OAI_ThreeMachine_StackCompiler_Costs_answerMatrix

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

end ThreeMachine.StackCompiler.Poly
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
  apply volumeList hl (show Poly s (fun j => 4*n j+3) d from by (
  have polyH0 := Poly.const (s) (4);
  have polyH1 := Poly.mul polyH0 (hn);
  have polyH2 := Poly.const (s) (3);
  have polyH3 := Poly.add polyH1 polyH2;
  exact Poly.lift polyH3 (by first | decide +kernel | omega)))
  intro j a _ha
  rw [volume_prod,volume_fin,volume_fin]
  have := a.1.isLt; have := a.2.isLt
  omega
end Poly
namespace Costs
theorem edgePairEq : Poly (fun x : Σ n, (Fin n × Fin n) × (Fin n × Fin n) => x.1)
    (fun x => Uniform.edgePairEq.time x.1 x.2) 2 := by (
  have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.fst x_1);
  have polyH1 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2.1.1);
  have polyH2 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2.1.2);
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2.1) polyH1 polyH2;
  have polyH4 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2.2.1);
  have polyH5 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2.2.2);
  have polyH6 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2.2) polyH4 polyH5;
  have polyH7 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => x_1.2) polyH3 polyH6;
  have polyH8 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.fst x_1) (2);
  have polyH9 := Poly.add polyH7 polyH8;
  have polyH10 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH9;
  have polyH11 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Sigma.snd x_1).1.1);
  have polyH12 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Sigma.snd x_1).1.2);
  have polyH13 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Sigma.snd x_1).1) polyH11 polyH12;
  have polyH14 := Poly.add polyH13 polyH8;
  have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2))))) polyH14;
  have polyH16 := Poly.add polyH10 polyH15;
  have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.fst x_1) (10);
  have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.fst x_1) (1);
  have polyH19 := Poly.add polyH13 polyH18;
  have polyH20 := Poly.mul polyH17 polyH19;
  have polyH21 := Poly.add polyH16 polyH20;
  have polyH22 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH21;
  have polyH23 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH9;
  have polyH24 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Sigma.snd x_1).2.1);
  have polyH25 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Sigma.snd x_1).2.2);
  have polyH26 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Sigma.snd x_1).2) polyH24 polyH25;
  have polyH27 := Poly.add polyH26 polyH8;
  have polyH28 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH27;
  have polyH29 := Poly.add polyH23 polyH28;
  have polyH30 := Poly.add polyH26 polyH18;
  have polyH31 := Poly.mul polyH17 polyH30;
  have polyH32 := Poly.add polyH29 polyH31;
  have polyH33 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH32;
  have polyH34 := Poly.add polyH22 polyH33;
  have polyH35 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.fst x_1) (20);
  have polyH36 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Prod.fst (Sigma.snd x_1)).1);
  have polyH37 := Poly.add polyH7 polyH36;
  have polyH38 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).1);
  have polyH39 := Poly.add polyH37 polyH38;
  have polyH40 := Poly.add polyH39 polyH18;
  have polyH41 := Poly.mul polyH35 polyH40;
  have polyH42 := Poly.add polyH34 polyH41;
  have polyH43 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (Fin) (Fin) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst (Prod.fst x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH42;
  have polyH44 := Poly.reparam (@Costs.finEq) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.mk (Sigma.fst x_1) (Prod.fst (Prod.fst (Sigma.snd x_1)), Prod.fst (Prod.snd (Sigma.snd x_1)))) polyH0;
  have polyH45 := Poly.add polyH43 polyH44;
  have polyH46 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Prod.fst (Prod.fst (Sigma.snd x_1)), Prod.fst (Prod.snd (Sigma.snd x_1)))) polyH36 polyH38;
  have polyH47 := Poly.add polyH46 polyH18;
  have polyH48 := Poly.mul polyH17 polyH47;
  have polyH49 := Poly.add polyH45 polyH48;
  have polyH50 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.fst (Prod.fst x_1), Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) Fin Fin _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst (Prod.fst x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (Uniform.finEq) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH49;
  have polyH51 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2))))) polyH14;
  have polyH52 := Poly.add polyH10 polyH51;
  have polyH53 := Poly.add polyH52 polyH20;
  have polyH54 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH53;
  have polyH55 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH27;
  have polyH56 := Poly.add polyH23 polyH55;
  have polyH57 := Poly.add polyH56 polyH31;
  have polyH58 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH57;
  have polyH59 := Poly.add polyH54 polyH58;
  have polyH60 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Prod.fst (Sigma.snd x_1)).2);
  have polyH61 := Poly.add polyH7 polyH60;
  have polyH62 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).2);
  have polyH63 := Poly.add polyH61 polyH62;
  have polyH64 := Poly.add polyH63 polyH18;
  have polyH65 := Poly.mul polyH35 polyH64;
  have polyH66 := Poly.add polyH59 polyH65;
  have polyH67 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (Fin) (Fin) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.snd (Prod.fst x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH66;
  have polyH68 := Poly.reparam (@Costs.finEq) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.mk (Sigma.fst x_1) (Prod.snd (Prod.fst (Sigma.snd x_1)), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH0;
  have polyH69 := Poly.add polyH67 polyH68;
  have polyH70 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (Prod.snd (Prod.fst (Sigma.snd x_1)), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH60 polyH62;
  have polyH71 := Poly.add polyH70 polyH18;
  have polyH72 := Poly.mul polyH17 polyH71;
  have polyH73 := Poly.add polyH69 polyH72;
  have polyH74 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.snd (Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) Fin Fin _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.snd (Prod.fst x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _))) (Uniform.finEq) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH73;
  have polyH75 := Poly.add polyH50 polyH74;
  have polyH76 := Poly.mul polyH35 polyH7;
  have polyH77 := Poly.add polyH75 polyH76;
  have polyH78 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => Sigma.fst x_1) (11000);
  have polyH79 := Poly.add polyH77 polyH78;
  have polyH80 := Poly.of_le (fun (x_2 : (n : ℕ) × (Fin n × Fin n) × Fin n × Fin n) => (@Uniform.time_andD_le (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst ((fun (x_3 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.fst (Prod.fst x_3), Prod.fst (Prod.snd x_3))) x_1) = Prod.snd ((fun (x_3 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.fst (Prod.fst x_3), Prod.fst (Prod.snd x_3))) x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst ((fun (x_3 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.snd (Prod.fst x_3), Prod.snd (Prod.snd x_3))) x_1) = Prod.snd ((fun (x_3 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.snd (Prod.fst x_3), Prod.snd (Prod.snd x_3))) x_1)) _ _ (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.fst (Prod.fst x_1), Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) Fin Fin _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst (Prod.fst x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.fst) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) Uniform.finEq) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => (Prod.snd (Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) Fin Fin _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.snd (Prod.fst x_1)) (fun (i : ℕ) (x_1 : (Fin i × Fin i) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) => Prod.snd) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _))) Uniform.finEq) (Sigma.fst x_2) (Sigma.snd x_2))) polyH79;
  exact Poly.lift polyH80 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem edgeAt : Poly (fun x : Σ n, (Fin n × Fin n) × Instance n => x.1+x.2.2.edges.length)
    (fun x => Uniform.edgeAt.time x.1 x.2) 10 := by
  let s (x : Σ n, (Fin n × Fin n) × Instance n) := x.1+x.2.2.edges.length
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hl : Poly s (fun x => x.2.2.edges.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have hv := Poly.volumeInstance (fun x => x.2.2) hn hl
  (
  have polyH0 := Poly.volumeFin (hn) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => x_1.2.1.1);
  have polyH1 := Poly.volumeFin (hn) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => x_1.2.1.2);
  have polyH2 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => x_1.2.1) polyH0 polyH1;
  have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => x_1.2) polyH2 (hv);
  have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (2);
  have polyH5 := Poly.add polyH3 polyH4;
  have polyH6 := Poly.of_le (fun (x_6 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i × Fin i) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst x_6) (Sigma.snd x_6)))) polyH5;
  have polyH7 := Poly.add (hv) polyH4;
  have polyH8 := Poly.add polyH6 polyH7;
  have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (10);
  have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (1);
  have polyH11 := Poly.add (hv) polyH10;
  have polyH12 := Poly.mul polyH9 polyH11;
  have polyH13 := Poly.add polyH8 polyH12;
  have polyH14 := Poly.of_le (fun (x_6 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × OAI.ThreeMachine.Instance i) (OAI.ThreeMachine.Instance) (fun (n : ℕ) => List (Fin n × Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (G : OAI.ThreeMachine.Instance n) => OAI.ThreeMachine.Instance.edges G) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) OAI.ThreeMachine.Instance _ _) (Uniform.instanceEdges) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH13;
  have polyH15 := Poly.of_le (fun (x_6 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i × Fin i) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst x_6) (Sigma.snd x_6)))) polyH5;
  have polyH16 := Poly.add polyH14 polyH15;
  have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (20);
  have polyH18 := Poly.precomp (hn) (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Prod.snd (Sigma.snd x_1)).1) => Sigma.fst q);
  have polyH19 := Poly.volumeFin polyH18 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Prod.snd (Sigma.snd x_1)).1) => (Sigma.snd q).1.1);
  have polyH20 := Poly.volumeFin polyH18 (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Prod.snd (Sigma.snd x_1)).1) => (Sigma.snd q).1.2);
  have polyH21 := Poly.volumeProd (fun (q : Poly.ListPool fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Prod.snd (Sigma.snd x_1)).1) => (Sigma.snd q).1) polyH19 polyH20;
  have polyH22 := Poly.listVolume (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Prod.snd (Sigma.snd x_1)).1) (hl) polyH21;
  have polyH23 := Poly.add polyH3 polyH22;
  have polyH24 := Poly.volumeFin (hn) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Sigma.snd x_1).1.1);
  have polyH25 := Poly.volumeFin (hn) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Sigma.snd x_1).1.2);
  have polyH26 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (Sigma.snd x_1).1) polyH24 polyH25;
  have polyH27 := Poly.add polyH23 polyH26;
  have polyH28 := Poly.add polyH27 polyH10;
  have polyH29 := Poly.mul polyH17 polyH28;
  have polyH30 := Poly.add polyH16 polyH29;
  have polyH31 := Poly.of_le (fun (x_6 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × OAI.ThreeMachine.Instance i) (fun (n : ℕ) => List (Fin n × Fin n)) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × OAI.ThreeMachine.Instance i) => (fun (G : OAI.ThreeMachine.Instance i) => OAI.ThreeMachine.Instance.edges G) (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance (fun (n : ℕ) => List (Fin n × Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (G : OAI.ThreeMachine.Instance n) => OAI.ThreeMachine.Instance.edges G) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) OAI.ThreeMachine.Instance _ _) Uniform.instanceEdges) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) OAI.ThreeMachine.Instance _ _) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH30;
  have polyH32 := Poly.precomp (hn) (fun (q : @Poly.Pool ℕ ((n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) (fun (i : ℕ) => Fin i × Fin i) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Prod.fst ((fun (G : OAI.ThreeMachine.Instance (Sigma.fst x_1)) => OAI.ThreeMachine.Instance.edges G) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) => Sigma.fst q);
  have polyH33 := Poly.reparam (@Costs.edgePairEq) (fun (q : @Poly.Pool ℕ ((n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) (fun (i : ℕ) => Fin i × Fin i) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Prod.fst ((fun (G : OAI.ThreeMachine.Instance (Sigma.fst x_1)) => OAI.ThreeMachine.Instance.edges G) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd ((fun (G : OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst q))) => OAI.ThreeMachine.Instance.edges G) (Prod.snd (Sigma.snd (Sigma.fst q))), Prod.fst (Sigma.snd (Sigma.fst q))))) polyH32;
  have polyH34 := @Poly.anyTime (ℕ) ((n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Prod.fst ((fun (G : OAI.ThreeMachine.Instance (Sigma.fst x_1)) => OAI.ThreeMachine.Instance.edges G) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Prod.snd ((fun (G : OAI.ThreeMachine.Instance (Sigma.fst x_1)) => OAI.ThreeMachine.Instance.edges G) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (Uniform.edgePairEq) (1) (2 * 1) (1 + Max.max (1) (1)) (Max.max (1) (1)) (hl) polyH33 polyH22 polyH26;
  have polyH35 := Poly.add polyH31 polyH34;
  have polyH36 := Poly.volumeProd (fun (x_1 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => ((fun (G : OAI.ThreeMachine.Instance (Sigma.fst x_1)) => OAI.ThreeMachine.Instance.edges G) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) polyH22 polyH26;
  have polyH37 := Poly.add polyH36 polyH10;
  have polyH38 := Poly.mul polyH9 polyH37;
  have polyH39 := Poly.add polyH35 polyH38;
  have polyH40 := Poly.of_le (fun (x_6 : (n : ℕ) × (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i × Fin i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => List (Fin i × Fin i) × Fin i × Fin i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × OAI.ThreeMachine.Instance i) => ((fun (G : OAI.ThreeMachine.Instance i) => OAI.ThreeMachine.Instance.edges G) (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : List (Fin i × Fin i) × Fin i × Fin i) => List.any (Prod.fst x_1) fun (a : Fin i × Fin i) => Decidable.decide (Prod.fst (a, Prod.snd x_1) = Prod.snd (a, Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i × Fin i) × OAI.ThreeMachine.Instance i) (fun (n : ℕ) => List (Fin n × Fin n)) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) (x_1 : (Fin i × Fin i) × OAI.ThreeMachine.Instance i) => (fun (G : OAI.ThreeMachine.Instance i) => OAI.ThreeMachine.Instance.edges G) (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i × Fin i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance (fun (n : ℕ) => List (Fin n × Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (G : OAI.ThreeMachine.Instance n) => OAI.ThreeMachine.Instance.edges G) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i × Fin i) OAI.ThreeMachine.Instance _ _) Uniform.instanceEdges) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i × Fin i) OAI.ThreeMachine.Instance _ _)) (@Uniform.any ℕ (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ (fun (n : ℕ) (x_1 : (Fin n × Fin n) × Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) Uniform.edgePairEq) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH39;
  exact Poly.lift polyH40 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

theorem edgeMatrix : Poly (fun x : Σ n, Universe n × Instance n => x.1+x.2.2.edges.length)
    (fun x => Uniform.edgeMatrix.time x.1 x.2) 20 := by
  let s (x : Σ n, Universe n × Instance n) := x.1+x.2.2.edges.length
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hl : Poly s (fun x => x.2.2.edges.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have hv := Poly.volumeInstance (fun x => x.2.2) hn hl
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => x_1.2.1);
  have polyH1 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => x_1.2) polyH0 (hv);
  have polyH2 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst x_6) (Sigma.snd x_6)))) polyH3;
  have polyH5 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_id (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ (Sigma.fst x_6) (Sigma.snd x_6)))) polyH3;
  have polyH6 := Poly.add polyH4 polyH5;
  have polyH7 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (20);
  have polyH8 := Poly.volumeUniverse (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (Sigma.snd x_1).1);
  have polyH9 := Poly.add polyH1 polyH8;
  have polyH10 := Poly.add polyH9 polyH1;
  have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (1);
  have polyH12 := Poly.add polyH10 polyH11;
  have polyH13 := Poly.mul polyH7 polyH12;
  have polyH14 := Poly.add polyH6 polyH13;
  have polyH15 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => x_1) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _) (@Uniform.id ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH14;
  have polyH16 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (Prod.fst (Sigma.snd x_1), Sigma.snd x_1)) polyH8 polyH1;
  have polyH17 := Poly.add polyH16 polyH2;
  have polyH18 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst x_6) ((Prod.fst (Sigma.snd x_6), Sigma.snd x_6))))) polyH17;
  have polyH19 := Poly.add polyH8 polyH2;
  have polyH20 := Poly.add polyH18 polyH19;
  have polyH21 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (10);
  have polyH22 := Poly.add polyH8 polyH11;
  have polyH23 := Poly.mul polyH21 polyH22;
  have polyH24 := Poly.add polyH20 polyH23;
  have polyH25 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Universe ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i) => List.finRange i) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.universeListAny ℕ fun (n : ℕ) => n) (Sigma.fst x_6) ((Prod.fst (Sigma.snd x_6), Sigma.snd x_6))))) polyH24;
  have polyH26 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst x_6) ((Prod.fst (Sigma.snd x_6), Sigma.snd x_6))))) polyH17;
  have polyH27 := Poly.add polyH25 polyH26;
  have polyH28 := Poly.volumeFinRange (hn);
  have polyH29 := Poly.add polyH16 polyH28;
  have polyH30 := Poly.add polyH29 polyH1;
  have polyH31 := Poly.add polyH30 polyH11;
  have polyH32 := Poly.mul polyH7 polyH31;
  have polyH33 := Poly.add polyH27 polyH32;
  have polyH34 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Universe ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) (fun (i : ℕ) => List (Fin i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Universe ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) => (fun (i_1 : ℕ) (x_2 : Universe i_1) => List.finRange i_1) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Universe ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i) => List.finRange i) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.universeListAny ℕ fun (n : ℕ) => n)) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (Sigma.fst x_6) ((Prod.fst (Sigma.snd x_6), Sigma.snd x_6))))) polyH33;
  have polyH35 := Poly.lengthFinRange (hn);
  have polyH36 := Poly.precomp (hn) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst q);
  have polyH37 := Poly.volumeFin polyH36 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Sigma.snd q).1);
  have polyH38 := Poly.volumeUniverse polyH36 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Sigma.fst q).2.1);
  have polyH39 := Poly.precomp (hv) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst q);
  have polyH40 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Sigma.fst q).2) polyH38 polyH39;
  have polyH41 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))) polyH37 polyH40;
  have polyH42 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q)) (2);
  have polyH43 := Poly.add polyH41 polyH42;
  have polyH44 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH43;
  have polyH45 := Poly.add polyH40 polyH42;
  have polyH46 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH45;
  have polyH47 := Poly.add polyH44 polyH46;
  have polyH48 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q)) (10);
  have polyH49 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q)) (1);
  have polyH50 := Poly.add polyH40 polyH49;
  have polyH51 := Poly.mul polyH48 polyH50;
  have polyH52 := Poly.add polyH47 polyH51;
  have polyH53 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH52;
  have polyH54 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH43;
  have polyH55 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst (Sigma.fst q)) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH45;
  have polyH56 := Poly.add polyH44 polyH55;
  have polyH57 := Poly.add polyH56 polyH51;
  have polyH58 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (OAI.ThreeMachine.Instance) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH57;
  have polyH59 := Poly.add polyH54 polyH58;
  have polyH60 := Poly.const (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q)) (20);
  have polyH61 := Poly.add polyH41 polyH37;
  have polyH62 := Poly.add polyH61 polyH39;
  have polyH63 := Poly.add polyH62 polyH49;
  have polyH64 := Poly.mul polyH60 polyH63;
  have polyH65 := Poly.add polyH59 polyH64;
  have polyH66 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH65;
  have polyH67 := Poly.add polyH53 polyH66;
  have polyH68 := Poly.volumeUniverse polyH36 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))).1);
  have polyH69 := Poly.add polyH41 polyH68;
  have polyH70 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))))) polyH37 polyH39;
  have polyH71 := Poly.add polyH69 polyH70;
  have polyH72 := Poly.add polyH71 polyH49;
  have polyH73 := Poly.mul polyH60 polyH72;
  have polyH74 := Poly.add polyH67 polyH73;
  have polyH75 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH74;
  have polyH76 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))))) polyH68 polyH70;
  have polyH77 := Poly.add polyH76 polyH42;
  have polyH78 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))))) polyH77;
  have polyH79 := Poly.add polyH68 polyH42;
  have polyH80 := Poly.add polyH78 polyH79;
  have polyH81 := Poly.add polyH68 polyH49;
  have polyH82 := Poly.mul polyH48 polyH81;
  have polyH83 := Poly.add polyH80 polyH82;
  have polyH84 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Fin ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i) => List.finRange i) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.universeListAny ℕ fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))))) polyH83;
  have polyH85 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))))) polyH77;
  have polyH86 := Poly.add polyH84 polyH85;
  have polyH87 := Poly.volumeFinRange polyH36;
  have polyH88 := Poly.add polyH76 polyH87;
  have polyH89 := Poly.add polyH88 polyH70;
  have polyH90 := Poly.add polyH89 polyH49;
  have polyH91 := Poly.mul polyH60 polyH90;
  have polyH92 := Poly.add polyH86 polyH91;
  have polyH93 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Fin ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) (fun (i : ℕ) => List (Fin i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Fin ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) => (fun (i_1 : ℕ) (x_2 : Universe i_1) => List.finRange i_1) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (i_1 : ℕ) => Universe i_1) i × (fun (i_1 : ℕ) => Fin ((fun (n : ℕ) => n) i_1) × OAI.ThreeMachine.Instance i_1) i) (fun (i : ℕ) => Universe i) (fun (i : ℕ) => List (Fin i)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe i) => List.finRange i) (@Uniform.fst ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.universeListAny ℕ fun (n : ℕ) => n)) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))))) polyH92;
  have polyH94 := Poly.lengthFinRange polyH36;
  have polyH95 := Poly.precomp polyH36 (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => Sigma.fst q);
  have polyH96 := Poly.volumeFin polyH95 (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (Sigma.snd q).1);
  have polyH97 := Poly.volumePool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) polyH28;
  have polyH98 := Poly.precomp polyH97 (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => Sigma.fst q);
  have polyH99 := Poly.precomp polyH39 (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => Sigma.fst q);
  have polyH100 := Poly.volumeProd (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))) polyH98 polyH99;
  have polyH101 := Poly.volumeProd (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))) polyH96 polyH100;
  have polyH102 := Poly.const (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q_1)) (Sigma.fst q)) (2);
  have polyH103 := Poly.add polyH101 polyH102;
  have polyH104 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH103;
  have polyH105 := Poly.add polyH100 polyH102;
  have polyH106 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH105;
  have polyH107 := Poly.add polyH104 polyH106;
  have polyH108 := Poly.const (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q_1)) (Sigma.fst q)) (10);
  have polyH109 := Poly.const (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q_1)) (Sigma.fst q)) (1);
  have polyH110 := Poly.add polyH100 polyH109;
  have polyH111 := Poly.mul polyH108 polyH110;
  have polyH112 := Poly.add polyH107 polyH111;
  have polyH113 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH112;
  have polyH114 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH103;
  have polyH115 := Poly.add polyH113 polyH114;
  have polyH116 := Poly.const (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q_1)) (Sigma.fst q)) (20);
  have polyH117 := Poly.add polyH101 polyH98;
  have polyH118 := Poly.add polyH117 polyH96;
  have polyH119 := Poly.add polyH118 polyH109;
  have polyH120 := Poly.mul polyH116 polyH119;
  have polyH121 := Poly.add polyH115 polyH120;
  have polyH122 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH121;
  have polyH123 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst (Sigma.fst (Sigma.fst q))) (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH105;
  have polyH124 := Poly.add polyH104 polyH123;
  have polyH125 := Poly.add polyH124 polyH111;
  have polyH126 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (OAI.ThreeMachine.Instance) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH125;
  have polyH127 := Poly.add polyH122 polyH126;
  have polyH128 := Poly.volumeProd (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))) polyH98 polyH96;
  have polyH129 := Poly.add polyH101 polyH128;
  have polyH130 := Poly.add polyH129 polyH99;
  have polyH131 := Poly.add polyH130 polyH109;
  have polyH132 := Poly.mul polyH116 polyH131;
  have polyH133 := Poly.add polyH127 polyH132;
  have polyH134 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) (OAI.ThreeMachine.Instance) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH133;
  have polyH135 := Poly.size (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q_1)) (Sigma.fst q));
  have polyH136 := Poly.reparam (@Costs.edgeAt) (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => Sigma.mk (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))))) polyH135;
  have polyH137 := Poly.add polyH134 polyH136;
  have polyH138 := Poly.volumeProd (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))))) polyH128 polyH99;
  have polyH139 := Poly.add polyH138 polyH109;
  have polyH140 := Poly.mul polyH108 polyH139;
  have polyH141 := Poly.add polyH137 polyH140;
  have polyH142 := Poly.of_le (fun (q : Poly.Pool (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q_1)) fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1))))), Prod.fst (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q_1), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q_1)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q_1)), Sigma.snd (Sigma.fst q_1)))))))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) (Uniform.edgeAt) (Sigma.fst (Sigma.fst (Sigma.fst q))) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))) polyH141;
  have polyH143 := Poly.volumeBool (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => (fun (q_1 : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q_1)) (Sigma.fst q)) (fun (q : Poly.Pool (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd ((fun (x_1 : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst (Sigma.fst q)))) × Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst (Sigma.fst q)))) × OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst (Sigma.fst q)))) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))) (Prod.fst (Prod.fst ((fun (x_1 : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst (Sigma.fst q)))) × Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst (Sigma.fst q)))) × OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst (Sigma.fst q)))) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))))))))) (Prod.snd (Prod.fst ((fun (x_1 : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst (Sigma.fst q)))) × Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst (Sigma.fst q)))) × OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst (Sigma.fst q)))) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q)))))), Prod.fst (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd (Sigma.fst q)), Prod.snd (List.finRange (Sigma.fst (Sigma.fst (Sigma.fst q))), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst (Sigma.fst q))), Sigma.snd (Sigma.fst (Sigma.fst q))))))))))))));
  have polyH144 := @Poly.mapTime (ℕ) (Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (Sigma.fst q)) (fun (i : ℕ) => Fin i) (fun (i : ℕ) => Bool) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Sigma.fst (Sigma.fst q)) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.fst (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (2 * 1) (1 + 1)) (0))) (0 + Max.max (Max.max (2 * 1) (1 + 1)) (0))) (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (2 * 1)) (1)) (0))) (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (2 * 1) (1 + 1)) (0))) (0 + Max.max (Max.max (2 * 1) (1 + 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (Max.max (2 * 1) (1))) (1 + 1)) (0))) (10 * 1)) (0 + Max.max (Max.max (Max.max (2 * 1) (1)) (1 + 1)) (0))) (2 * 1) (Max.max (1) (1 + 1)) (0) polyH94 polyH142 polyH87 polyH70 polyH143;
  have polyH145 := Poly.add polyH93 polyH144;
  have polyH146 := Poly.volumeProd (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH87 polyH70;
  have polyH147 := Poly.add polyH146 polyH49;
  have polyH148 := Poly.mul polyH48 polyH147;
  have polyH149 := Poly.add polyH145 polyH148;
  have polyH150 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => List (Fin i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => List Bool) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (List.finRange i, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => List.map (fun (a : Fin i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd (a, Prod.snd x_1)), Prod.fst (a, Prod.snd x_1)), Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst x_1)) (@Uniform.onFst ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => List (Fin i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => List.finRange i) (@Uniform.universeListAny ℕ fun (n : ℕ) => n)) (@Uniform.map ℕ (fun (i : ℕ) => Fin i) (fun (i : ℕ) => Bool) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt)) (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))))) polyH149;
  have polyH151 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_vectorMapAny (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt) (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))), Prod.fst (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))), Prod.snd (Prod.snd (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))))) polyH150;
  have polyH152 := Poly.add polyH75 polyH151;
  have polyH153 := Poly.add polyH76 polyH49;
  have polyH154 := Poly.mul polyH48 polyH153;
  have polyH155 := Poly.add polyH152 polyH154;
  have polyH156 := Poly.of_le (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (v : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd (v, Prod.snd x_1)), Prod.fst (v, Prod.snd x_1)), Prod.snd (Prod.snd (v, Prod.snd x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)))) (@Uniform.vectorMapAny ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt)) (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))) polyH155;
  have polyH157 := Poly.volumeBoolVector polyH36 (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) (v : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q)))) => (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (Sigma.fst (Sigma.fst q)) ((Prod.fst (Prod.snd (v, Prod.snd ((fun (x_1 : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q))) × Universe ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q))) × OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst q))) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))))), Prod.fst (v, Prod.snd ((fun (x_1 : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q))) × Universe ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q))) × OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst q))) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q))))))), Prod.snd (Prod.snd (v, Prod.snd ((fun (x_1 : Fin ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q))) × Universe ((fun (n : ℕ) => n) (Sigma.fst (Sigma.fst q))) × OAI.ThreeMachine.Instance (Sigma.fst (Sigma.fst q))) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (Subtype.val (Sigma.snd q), Prod.snd (List.finRange (Sigma.fst (Sigma.fst q)), Prod.snd (Prod.fst (Sigma.snd (Sigma.fst q)), Sigma.snd (Sigma.fst q)))))))));
  have polyH158 := @Poly.mapTime (ℕ) ((n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (fun (i : ℕ) => Fin i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.fst (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Prod.snd (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (b : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst x_1, b), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (v : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd (v, Prod.snd x_1)), Prod.fst (v, Prod.snd x_1)), Prod.snd (Prod.snd (v, Prod.snd x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)))) (@Uniform.vectorMapAny ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt))) (1) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (2 * 1) (1 + 1)) (0))) (0 + Max.max (Max.max (2 * 1) (1 + 1)) (0))) (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (2 * 1) (1 + 1)) (0))) (0 + Max.max (Max.max (2 * 1) (1 + 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (1)) (1 + 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (2 * 1)) (Max.max (1) (1 + 1))) (0))) (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (2 * 1) (Max.max (1) (1 + 1))) (0)) (Max.max (2 * 1) (0))) (0 + Max.max (2 * 1) (0))) (Max.max (Max.max (2 * 1) (Max.max (1) (1 + 1))) (0))) (0 + Max.max (Max.max (Max.max (Max.max (2 * 1) (Max.max (1) (1 + 1))) (2 * 1)) (Max.max (1) (1 + 1))) (0))) (1 + Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (2 * 1) (1 + 1)) (0))) (0 + Max.max (Max.max (2 * 1) (1 + 1)) (0))) (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (2 * 1)) (1)) (0))) (Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (0)) (Max.max (Max.max (2 * 1) (1 + 1)) (0))) (0 + Max.max (Max.max (2 * 1) (1 + 1)) (0)))) (0 + Max.max (Max.max (Max.max (Max.max (1) (Max.max (2 * 1) (1 + 1))) (Max.max (2 * 1) (1))) (1 + 1)) (0))) (10 * 1)) (0 + Max.max (Max.max (Max.max (2 * 1) (1)) (1 + 1)) (0))) (Max.max (2 * 1) (Max.max (Max.max (1) (1 + 1)) (1 + 0))))) (0 + Max.max (Max.max (2 * 1) (Max.max (1) (1 + 1))) (0)))) (0 + Max.max (Max.max (2 * 1) (Max.max (1) (1 + 1))) (0))) (2 * 1) (Max.max (2 * 1) (1 + 1)) (1) polyH35 polyH156 polyH28 polyH1 polyH157;
  have polyH159 := Poly.add polyH34 polyH158;
  have polyH160 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (List.finRange (Sigma.fst x_1), Prod.snd (Prod.fst (Sigma.snd x_1), Sigma.snd x_1))) polyH28 polyH1;
  have polyH161 := Poly.add polyH160 polyH11;
  have polyH162 := Poly.mul polyH21 polyH161;
  have polyH163 := Poly.add polyH159 polyH162;
  have polyH164 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => List (Fin i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => List (Fin ((fun (n : ℕ) => n) i) → Bool)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (List.finRange i, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => List.map (fun (a : Fin i) (b : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (a, Prod.snd x_1), b), Prod.snd (Prod.snd (a, Prod.snd x_1)))) (Prod.fst x_1)) (@Uniform.onFst ℕ (fun (i : ℕ) => Universe i) (fun (i : ℕ) => List (Fin i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Universe i) => List.finRange i) (@Uniform.universeListAny ℕ fun (n : ℕ) => n)) (@Uniform.map ℕ (fun (i : ℕ) => Fin i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (b : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst x_1, b), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (v : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd (v, Prod.snd x_1)), Prod.fst (v, Prod.snd x_1)), Prod.snd (Prod.snd (v, Prod.snd x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)))) (@Uniform.vectorMapAny ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt)))) (Sigma.fst x_6) ((Prod.fst (Sigma.snd x_6), Sigma.snd x_6))))) polyH163;
  have polyH165 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_vectorMapAny (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (b : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst x_1, b), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (v : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd (v, Prod.snd x_1)), Prod.fst (v, Prod.snd x_1)), Prod.snd (Prod.snd (v, Prod.snd x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)))) (@Uniform.vectorMapAny ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt))) (Sigma.fst x_6) ((Prod.fst (Sigma.snd x_6), Sigma.snd x_6))))) polyH164;
  have polyH166 := Poly.add polyH15 polyH165;
  have polyH167 := Poly.add polyH16 polyH11;
  have polyH168 := Poly.mul polyH21 polyH167;
  have polyH169 := Poly.add polyH166 polyH168;
  have polyH170 := Poly.of_le (fun (x_6 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Fin ((fun (n : ℕ) => n) i) → Bool) _ _ _ (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, x_1)) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (v b : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (v, Prod.snd x_1), b), Prod.snd (Prod.snd (v, Prod.snd x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => x_1) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _) (@Uniform.id ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _)) (@Uniform.vectorMapAny ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (b : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst x_1, b), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) → Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1, Prod.snd (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Universe ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (v : Fin ((fun (n : ℕ) => n) i)) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd (v, Prod.snd x_1)), Prod.fst (v, Prod.snd x_1)), Prod.snd (Prod.snd (v, Prod.snd x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Universe ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)))) (@Uniform.vectorMapAny ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ (fun (n : ℕ) => n) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (fun (n : ℕ) (x_2 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) (Prod.fst (Prod.fst x_2)) (Prod.snd (Prod.fst x_2)))) i ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => (Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => ((Prod.fst (Prod.snd x_1), Prod.fst x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n × Fin n) × OAI.ThreeMachine.Instance n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) (Prod.fst (Prod.fst x_1)) (Prod.snd (Prod.fst x_1)))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.snd (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) (x_1 : Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) => Prod.fst (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _)) (@Uniform.comp ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i) × OAI.ThreeMachine.Instance i) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Fin ((fun (n : ℕ) => n) i)) OAI.ThreeMachine.Instance _ _))) Uniform.edgeAt)))) (Sigma.fst x_6) (Sigma.snd x_6)))) polyH169;
  exact Poly.lift polyH170 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs

theorem reachMatrix : Poly (fun x : Σ n, Universe n × Instance n => x.1+x.2.2.edges.length)
    (fun x => Uniform.reachMatrix.time x.1 x.2) 30 := by
  let J := Σ n, Universe n × Instance n
  let s (x : J) := x.1+x.2.2.edges.length
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hl : Poly s (fun x => x.2.2.edges.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have hv := Poly.volumeInstance (fun x => x.2.2) hn hl
  let a (x : J) : (Universe x.1 × Matrix x.1) × Matrix x.1 :=
    ((x.2.1,fun a b => decide (x.2.2.edge a b)),fun a b => decide (x.2.2.edge a b))
  let f (n : ℕ) (p : (Universe n × Matrix n) × Matrix n) :=
    (p.1,ThreeMachine.StackCompiler.nextMatrix p.1.2 p.2)
  have hN := hn.precomp (Sigma.fst : Poly.IterPool (fun x : J => x.1) → J)
  have hT : Poly (fun p : Poly.IterPool (fun x : J => x.1) => s p.1)
      (fun p => Uniform.closureMatrixStep.time p.1.1 ((f p.1.1)^[p.2.val] (a p.1))) 20 := by (
  have polyH0 := Poly.reparam (@Costs.closureMatrixStep) (fun (p_1 : Poly.IterPool fun (x : J) => Sigma.fst x) => Sigma.mk (Sigma.fst (Sigma.fst p_1)) ((f (Sigma.fst (Sigma.fst p_1)))^[Fin.val (Sigma.snd p_1)] (a (Sigma.fst p_1)))) (hN);
  exact Poly.lift polyH0 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hV : Poly (fun p : Poly.IterPool (fun x : J => x.1) => s p.1)
      (fun p => volume ((f p.1.1)^[p.2.val] (a p.1))) 2 := by (
  have polyH0 := Poly.volumeUniverse (hN) (fun (p_1 : Poly.IterPool fun (x : J) => Sigma.fst x) => ((f (Sigma.fst (Sigma.fst p_1)))^[Fin.val (Sigma.snd p_1)] (a (Sigma.fst p_1))).1.1);
  have polyH1 := Poly.volumeMatrix (hN) (fun (p_1 : Poly.IterPool fun (x : J) => Sigma.fst x) => ((f (Sigma.fst (Sigma.fst p_1)))^[Fin.val (Sigma.snd p_1)] (a (Sigma.fst p_1))).1.2);
  have polyH2 := Poly.volumeProd (fun (p_1 : Poly.IterPool fun (x : J) => Sigma.fst x) => ((f (Sigma.fst (Sigma.fst p_1)))^[Fin.val (Sigma.snd p_1)] (a (Sigma.fst p_1))).1) polyH0 polyH1;
  have polyH3 := Poly.volumeMatrix (hN) (fun (p_1 : Poly.IterPool fun (x : J) => Sigma.fst x) => ((f (Sigma.fst (Sigma.fst p_1)))^[Fin.val (Sigma.snd p_1)] (a (Sigma.fst p_1))).2);
  have polyH4 := Poly.volumeProd (fun (p_1 : Poly.IterPool fun (x : J) => Sigma.fst x) => (f (Sigma.fst (Sigma.fst p_1)))^[Fin.val (Sigma.snd p_1)] (a (Sigma.fst p_1))) polyH2 polyH3;
  exact Poly.lift polyH4 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hI := Poly.iterateTime Uniform.closureMatrixStep (fun x : J => x.1) (fun x => x.1) a hn hT hV
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => x_1.2.1);
  have polyH1 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => x_1.2) polyH0 (hv);
  have polyH2 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (2);
  have polyH3 := Poly.add polyH1 polyH2;
  have polyH4 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (OAI.ThreeMachine.Instance) _ _ (Sigma.fst x_13) (Sigma.snd x_13)))) polyH3;
  have polyH5 := Poly.volumeUniverse (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (Sigma.snd x_1).1);
  have polyH6 := Poly.add polyH5 polyH2;
  have polyH7 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (100000);
  have polyH8 := Poly.lengthFinRange (hn);
  have polyH9 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (1);
  have polyH10 := Poly.add polyH8 polyH9;
  have polyH11 := Poly.mul polyH7 polyH10;
  have polyH12 := Poly.volumeFinRange (hn);
  have polyH13 := Poly.add polyH12 polyH9;
  have polyH14 := Poly.mul polyH11 polyH13;
  have polyH15 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (@Uniform.time_length_le (ℕ) (Fin) _ (Sigma.fst x_13) (List.finRange (Sigma.fst x_13)))) polyH14;
  have polyH16 := Poly.add polyH6 polyH15;
  have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (10);
  have polyH18 := Poly.mul polyH17 polyH13;
  have polyH19 := Poly.add polyH16 polyH18;
  have polyH20 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (Universe) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => ℕ) _ _ _ (fun (n : ℕ) (x_1 : Universe n) => List.finRange n) (fun (i : ℕ) (xs : List (Fin i)) => List.length xs) (Uniform.universeList) (@Uniform.length ℕ Fin _) (Sigma.fst x_13) (Prod.fst (Sigma.snd x_13))))) polyH19;
  have polyH21 := Poly.add polyH4 polyH20;
  have polyH22 := Poly.add polyH5 polyH9;
  have polyH23 := Poly.mul polyH17 polyH22;
  have polyH24 := Poly.add polyH21 polyH23;
  have polyH25 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (Universe) (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => n) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) (Uniform.universeNumber) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH24;
  have polyH26 := Poly.size (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1))));
  have polyH27 := Poly.reparam (@Costs.edgeMatrix) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH26;
  have polyH28 := Poly.add polyH4 polyH27;
  have polyH29 := Poly.const (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => Sigma.fst x_1 + List.length (OAI.ThreeMachine.Instance.edges (Prod.snd (Sigma.snd x_1)))) (20);
  have polyH30 := Poly.add polyH1 polyH5;
  have polyH31 := Poly.volumeMatrix (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd (Sigma.snd x_1)) a_1 b));
  have polyH32 := Poly.add polyH30 polyH31;
  have polyH33 := Poly.add polyH32 polyH9;
  have polyH34 := Poly.mul polyH29 polyH33;
  have polyH35 := Poly.add polyH28 polyH34;
  have polyH36 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (Universe) (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) (Uniform.edgeMatrix) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH35;
  have polyH37 := Poly.add polyH36 polyH27;
  have polyH38 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (Prod.fst (Sigma.snd x_1), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd (Sigma.snd x_1)) a_1 b))) polyH5 polyH31;
  have polyH39 := Poly.add polyH1 polyH38;
  have polyH40 := Poly.add polyH39 polyH31;
  have polyH41 := Poly.add polyH40 polyH9;
  have polyH42 := Poly.mul polyH29 polyH41;
  have polyH43 := Poly.add polyH37 polyH42;
  have polyH44 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe i × (Fin i → Fin i → Bool)) (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.edgeMatrix) (Uniform.edgeMatrix) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH43;
  have polyH45 := Poly.add polyH25 polyH44;
  have polyH46 := Poly.volumeNat (hn);
  have polyH47 := Poly.add polyH1 polyH46;
  have polyH48 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => ((Prod.fst (Sigma.snd x_1), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd (Sigma.snd x_1)) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd (Sigma.snd x_1)) a_1 b))) polyH38 polyH31;
  have polyH49 := Poly.add polyH47 polyH48;
  have polyH50 := Poly.add polyH49 polyH9;
  have polyH51 := Poly.mul polyH29 polyH50;
  have polyH52 := Poly.add polyH45 polyH51;
  have polyH53 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n : ℕ) => ℕ) (fun (i : ℕ) => (Universe i × (Fin i → Fin i → Bool)) × (Fin i → Fin i → Bool)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (fun (x_2 : Universe i) => i) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => ((Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)), fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => n) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.universeNumber) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe i × (Fin i → Fin i → Bool)) (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.edgeMatrix) Uniform.edgeMatrix) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH52;
  have polyH54 := Poly.add polyH53 (hI);
  have polyH55 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => ((fun (x_2 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst (Sigma.snd x_1)), (Prod.fst (Sigma.snd x_1), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd (Sigma.snd x_1)) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd (Sigma.snd x_1)) a_1 b))) polyH46 polyH48;
  have polyH56 := Poly.add polyH55 polyH9;
  have polyH57 := Poly.mul polyH17 polyH56;
  have polyH58 := Poly.add polyH54 polyH57;
  have polyH59 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => ℕ × (Universe i × (Fin i → Fin i → Bool)) × (Fin i → Fin i → Bool)) (fun (n : ℕ) => (Universe n × Matrix n) × Matrix n) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => ((fun (x_2 : Universe i) => i) (Prod.fst x_1), (Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)), fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (fun (i : ℕ) (x_1 : ℕ × (Universe i × Matrix i) × Matrix i) => (fun (x_2 : (Universe i × Matrix i) × Matrix i) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst x_1] (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n : ℕ) => ℕ) (fun (i : ℕ) => (Universe i × (Fin i → Fin i → Bool)) × (Fin i → Fin i → Bool)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (fun (x_2 : Universe i) => i) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => ((Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)), fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => n) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.universeNumber) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe i × (Fin i → Fin i → Bool)) (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.edgeMatrix) Uniform.edgeMatrix)) (@Uniform.iterate ℕ (fun (n : ℕ) => (Universe n × Matrix n) × Matrix n) _ (fun (n : ℕ) (x_1 : (Universe n × Matrix n) × Matrix n) => (Prod.fst x_1, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_1)) (Prod.snd x_1))) Uniform.closureMatrixStep) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH58;
  have polyH60 := Poly.volumeUniverse (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => ((fun (x_2 : (Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) × Matrix (Sigma.fst x_1)) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1))] (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1)))).1.1);
  have polyH61 := Poly.volumeMatrix (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => ((fun (x_2 : (Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) × Matrix (Sigma.fst x_1)) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1))] (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1)))).1.2);
  have polyH62 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => ((fun (x_2 : (Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) × Matrix (Sigma.fst x_1)) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1))] (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1)))).1) polyH60 polyH61;
  have polyH63 := Poly.volumeMatrix (hn) (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => ((fun (x_2 : (Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) × Matrix (Sigma.fst x_1)) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1))] (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1)))).2);
  have polyH64 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (fun (x_2 : (Universe (Sigma.fst x_1) × Matrix (Sigma.fst x_1)) × Matrix (Sigma.fst x_1)) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1))] (Prod.snd ((fun (x_2 : Universe (Sigma.fst x_1) × OAI.ThreeMachine.Instance (Sigma.fst x_1)) => ((fun (x_3 : Universe (Sigma.fst x_1)) => Sigma.fst x_1) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_1)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) (Sigma.snd x_1)))) polyH62 polyH63;
  have polyH65 := Poly.add polyH64 polyH2;
  have polyH66 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Universe i × Matrix i) (Matrix) _ _ (Sigma.fst x_13) ((fun (x_1 : ℕ × (Universe (Sigma.fst x_13) × Matrix (Sigma.fst x_13)) × Matrix (Sigma.fst x_13)) => (fun (x_2 : (Universe (Sigma.fst x_13) × Matrix (Sigma.fst x_13)) × Matrix (Sigma.fst x_13)) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst x_1] (Prod.snd x_1)) ((fun (x_1 : Universe (Sigma.fst x_13) × OAI.ThreeMachine.Instance (Sigma.fst x_13)) => ((fun (x_2 : Universe (Sigma.fst x_13)) => Sigma.fst x_13) (Prod.fst x_1), (Prod.fst x_1, fun (a_1 b : Fin (Sigma.fst x_13)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)), fun (a_1 b : Fin (Sigma.fst x_13)) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (Sigma.snd x_13)))))) polyH65;
  have polyH67 := Poly.add polyH59 polyH66;
  have polyH68 := Poly.add polyH64 polyH9;
  have polyH69 := Poly.mul polyH17 polyH68;
  have polyH70 := Poly.add polyH67 polyH69;
  have polyH71 := Poly.of_le (fun (x_13 : (n : ℕ) × Universe n × OAI.ThreeMachine.Instance n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n : ℕ) => (Universe n × Matrix n) × Matrix n) (Matrix) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (fun (x_2 : ℕ × (Universe i × Matrix i) × Matrix i) => (fun (x_3 : (Universe i × Matrix i) × Matrix i) => (Prod.fst x_3, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_3)) (Prod.snd x_3)))^[Prod.fst x_2] (Prod.snd x_2)) ((fun (x_2 : Universe i × OAI.ThreeMachine.Instance i) => ((fun (x_3 : Universe i) => i) (Prod.fst x_2), (Prod.fst x_2, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b)), fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_2) a_1 b))) x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => ℕ × (Universe i × (Fin i → Fin i → Bool)) × (Fin i → Fin i → Bool)) (fun (n : ℕ) => (Universe n × Matrix n) × Matrix n) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => ((fun (x_2 : Universe i) => i) (Prod.fst x_1), (Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)), fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (fun (i : ℕ) (x_1 : ℕ × (Universe i × Matrix i) × Matrix i) => (fun (x_2 : (Universe i × Matrix i) × Matrix i) => (Prod.fst x_2, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_2)) (Prod.snd x_2)))^[Prod.fst x_1] (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n : ℕ) => ℕ) (fun (i : ℕ) => (Universe i × (Fin i → Fin i → Bool)) × (Fin i → Fin i → Bool)) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (fun (x_2 : Universe i) => i) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => ((Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)), fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n) => n) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.universeNumber) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (i : ℕ) => Universe i × (Fin i → Fin i → Bool)) (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) (x_1 : Universe i × OAI.ThreeMachine.Instance i) => (Prod.fst x_1, fun (a_1 b : Fin i) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b))) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) Universe (fun (n : ℕ) => Fin n → Fin n → Bool) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (x_1 : Universe n × OAI.ThreeMachine.Instance n) (a_1 b : Fin n) => Decidable.decide (OAI.ThreeMachine.Instance.edge (Prod.snd x_1) a_1 b)) (@Uniform.fst ℕ Universe OAI.ThreeMachine.Instance _ _) Uniform.edgeMatrix) Uniform.edgeMatrix)) (@Uniform.iterate ℕ (fun (n : ℕ) => (Universe n × Matrix n) × Matrix n) _ (fun (n : ℕ) (x_1 : (Universe n × Matrix n) × Matrix n) => (Prod.fst x_1, OAI.ThreeMachine.StackCompiler.nextMatrix (Prod.snd (Prod.fst x_1)) (Prod.snd x_1))) Uniform.closureMatrixStep)) (@Uniform.snd ℕ (fun (i : ℕ) => Universe i × Matrix i) Matrix _ _) (Sigma.fst x_13) (Sigma.snd x_13)))) polyH70;
  exact Poly.lift polyH71 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

theorem unaryAnswer (G : ∀ j, Instance (n j)) (d : J → Option ℕ)
    (hn : Poly s n 1) (he : Poly s (fun j => (G j).edges.length) 1)
    (hd : Poly s (fun j => (d j).getD 0) 1) :
    Poly s (fun j => Uniform.unaryAnswer.time (n j) (U j,(G j,d j))) 150011 := by
  have hD : Poly s (fun j => volume (d j)) 1 := by
    apply Poly.of_le (fun j : J => volume_option_le_getD (d j) 0)
    have hv := Poly.volumeNat hd
    (
  have polyH0 := Poly.const (s) (2);
  have polyH1 := Poly.add (hv) polyH0;
  exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
  have hG := Poly.volumeInstance G hn he
  have hA := answerMatrix s n U (fun j => closureMatrix (G j) (n j)) d hn hd
  (
  have polyH0 := Poly.volumeUniverse (hn) (fun (j_1 : J) => U j_1);
  have polyH1 := Poly.volumeProd (fun (j_1 : J) => (G j_1, d j_1)) (hG) (hD);
  have polyH2 := Poly.volumeProd (fun (j_1 : J) => (U j_1, G j_1, d j_1)) polyH0 polyH1;
  have polyH3 := Poly.const (s) (2);
  have polyH4 := Poly.add polyH2 polyH3;
  have polyH5 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (Universe) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ (n j_14) ((U j_14, G j_14, d j_14))))) polyH4;
  have polyH6 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (Universe) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _ (n j_14) ((U j_14, G j_14, d j_14))))) polyH4;
  have polyH7 := Poly.add polyH1 polyH3;
  have polyH8 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_fst (ℕ) (OAI.ThreeMachine.Instance) (fun (i : ℕ) => Option ℕ) _ _ (n j_14) (Prod.snd (U j_14, G j_14, d j_14))))) polyH7;
  have polyH9 := Poly.add polyH6 polyH8;
  have polyH10 := Poly.const (s) (10);
  have polyH11 := Poly.const (s) (1);
  have polyH12 := Poly.add polyH1 polyH11;
  have polyH13 := Poly.mul polyH10 polyH12;
  have polyH14 := Poly.add polyH9 polyH13;
  have polyH15 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) (OAI.ThreeMachine.Instance) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.fst ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _) (n j_14) ((U j_14, G j_14, d j_14))))) polyH14;
  have polyH16 := Poly.add polyH5 polyH15;
  have polyH17 := Poly.const (s) (20);
  have polyH18 := Poly.add polyH2 polyH0;
  have polyH19 := Poly.add polyH18 (hG);
  have polyH20 := Poly.add polyH19 polyH11;
  have polyH21 := Poly.mul polyH17 polyH20;
  have polyH22 := Poly.add polyH16 polyH21;
  have polyH23 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (Universe) (OAI.ThreeMachine.Instance) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.fst ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _)) (n j_14) ((U j_14, G j_14, d j_14))))) polyH22;
  have polyH24 := Poly.add (hn) (he);
  have polyH25 := Poly.reparam (@Costs.reachMatrix) (fun (j_1 : J) => Sigma.mk (n j_1) (Prod.fst (U j_1, G j_1, d j_1), Prod.fst (Prod.snd (U j_1, G j_1, d j_1)))) polyH24;
  have polyH26 := Poly.add polyH23 polyH25;
  have polyH27 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, G j_1, d j_1), Prod.fst (Prod.snd (U j_1, G j_1, d j_1)))) polyH0 (hG);
  have polyH28 := Poly.add polyH27 polyH11;
  have polyH29 := Poly.mul polyH10 polyH28;
  have polyH30 := Poly.add polyH26 polyH29;
  have polyH31 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n_1 : ℕ) => Matrix n_1) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × OAI.ThreeMachine.Instance n_1) => closureMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) Universe OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.fst ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _))) (Uniform.reachMatrix) (n j_14) ((U j_14, G j_14, d j_14))))) polyH30;
  have polyH32 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_snd (ℕ) (OAI.ThreeMachine.Instance) (fun (i : ℕ) => Option ℕ) _ _ (n j_14) (Prod.snd (U j_14, G j_14, d j_14))))) polyH7;
  have polyH33 := Poly.add polyH6 polyH32;
  have polyH34 := Poly.add polyH33 polyH13;
  have polyH35 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.snd ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _) (n j_14) ((U j_14, G j_14, d j_14))))) polyH34;
  have polyH36 := Poly.add polyH31 polyH35;
  have polyH37 := Poly.volumeMatrix (hn) (fun (j_1 : J) => closureMatrix (Prod.snd ((fun (x : Universe (n j_1) × OAI.ThreeMachine.Instance (n j_1) × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (U j_1, G j_1, d j_1))) (n j_1));
  have polyH38 := Poly.add polyH2 polyH37;
  have polyH39 := Poly.add polyH38 (hD);
  have polyH40 := Poly.add polyH39 polyH11;
  have polyH41 := Poly.mul polyH17 polyH40;
  have polyH42 := Poly.add polyH36 polyH41;
  have polyH43 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (n_1 : ℕ) => Matrix n_1) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (fun (x_1 : Universe i × OAI.ThreeMachine.Instance i) => closureMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.snd (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n_1 : ℕ) => Matrix n_1) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × OAI.ThreeMachine.Instance n_1) => closureMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) Universe OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.fst ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _))) Uniform.reachMatrix) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.snd ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _)) (n j_14) ((U j_14, G j_14, d j_14))))) polyH42;
  have polyH44 := Poly.add polyH5 polyH43;
  have polyH45 := Poly.volumeProd (fun (j_1 : J) => ((fun (x : Universe (n j_1) × OAI.ThreeMachine.Instance (n j_1)) => closureMatrix (Prod.snd x) (n j_1)) ((fun (x : Universe (n j_1) × OAI.ThreeMachine.Instance (n j_1) × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (U j_1, G j_1, d j_1)), Prod.snd (Prod.snd (U j_1, G j_1, d j_1)))) polyH37 (hD);
  have polyH46 := Poly.add polyH18 polyH45;
  have polyH47 := Poly.add polyH46 polyH11;
  have polyH48 := Poly.mul polyH17 polyH47;
  have polyH49 := Poly.add polyH44 polyH48;
  have polyH50 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (Universe) (fun (i : ℕ) => Matrix i × Option ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i) => closureMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x), Prod.snd (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (n_1 : ℕ) => Matrix n_1) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (fun (x_1 : Universe i × OAI.ThreeMachine.Instance i) => closureMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.snd (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n_1 : ℕ) => Matrix n_1) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × OAI.ThreeMachine.Instance n_1) => closureMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) Universe OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.fst ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _))) Uniform.reachMatrix) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.snd ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _))) (n j_14) ((U j_14, G j_14, d j_14))))) polyH49;
  have polyH51 := Poly.add polyH50 (hA);
  have polyH52 := Poly.volumeProd (fun (j_1 : J) => (Prod.fst (U j_1, G j_1, d j_1), (fun (x : Universe (n j_1) × OAI.ThreeMachine.Instance (n j_1)) => closureMatrix (Prod.snd x) (n j_1)) ((fun (x : Universe (n j_1) × OAI.ThreeMachine.Instance (n j_1) × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (U j_1, G j_1, d j_1)), Prod.snd (Prod.snd (U j_1, G j_1, d j_1)))) polyH0 polyH45;
  have polyH53 := Poly.add polyH52 polyH11;
  have polyH54 := Poly.mul polyH10 polyH53;
  have polyH55 := Poly.add polyH51 polyH54;
  have polyH56 := Poly.of_le (fun (j_14 : J) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × Matrix i × Option ℕ) (fun (n_1 : ℕ) => Option (List ℕ)) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x, (fun (x_1 : Universe i × OAI.ThreeMachine.Instance i) => closureMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x), Prod.snd (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × Matrix n_1 × Option ℕ) => OAI.ThreeMachine.StackCompiler.answerMatrix (Prod.fst (Prod.snd x)) (Prod.snd (Prod.snd x))) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) Universe (fun (i : ℕ) => Matrix i × Option ℕ) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i) => closureMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x), Prod.snd (Prod.snd x))) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (n_1 : ℕ) => Matrix n_1) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (fun (x_1 : Universe i × OAI.ThreeMachine.Instance i) => closureMatrix (Prod.snd x_1) i) ((fun (x_1 : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) x)) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.snd (Prod.snd x)) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i) (fun (n_1 : ℕ) => Matrix n_1) _ _ _ (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => (Prod.fst x, Prod.fst (Prod.snd x))) (fun (n_1 : ℕ) (x : Universe n_1 × OAI.ThreeMachine.Instance n_1) => closureMatrix (Prod.snd x) n_1) (@Uniform.pair ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) Universe OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x : Universe i × OAI.ThreeMachine.Instance i × Option ℕ) => Prod.fst (Prod.snd x)) (@Uniform.fst ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) OAI.ThreeMachine.Instance _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.fst ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _))) Uniform.reachMatrix) (@Uniform.comp ℕ (fun (i : ℕ) => Universe i × OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) (fun (i : ℕ) => Option ℕ) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ Universe (fun (i : ℕ) => OAI.ThreeMachine.Instance i × Option ℕ) _ _) (@Uniform.snd ℕ OAI.ThreeMachine.Instance (fun (i : ℕ) => Option ℕ) _ _)))) (Uniform.answerMatrix) (n j_14) ((U j_14, G j_14, d j_14))))) polyH55;
  exact Poly.lift polyH56 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
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

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.unaryAnswer := @OAI.ThreeMachine.StackCompiler.Costs.unaryAnswer
