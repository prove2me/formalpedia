-- Prove2me | solution 1 for OAI.ThreeMachine.StackCompiler.Costs.matrixGetFrame
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T06:36:15.913688+00:00
-- url     : https://prove2.me/submissions/f8a8114a-442b-4222-8706-0fede90cc1cd

import Mathlib
import Definitions.Def_ThreeMachine
import Definitions.Def_OAIThreeMachineSched02

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false


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

theorem volume_bool_vector_le {n : ℕ} (v : Fin n → Bool) : volume v ≤ 4*n+1 := by
  have h := volume_function_le v 3 (fun _ => volume_bool _)
  omega

theorem volume_matrix_le {n : ℕ} (M : Matrix n) : volume M ≤ 10*(n+1)^2 := by
  have h := volume_function_le M (4*n+1) (fun _ => volume_bool_vector_le _)
  nlinarith

namespace Poly
variable {I : Type u6} {s n f : I → ℕ} {d : ℕ}

theorem volumeBoolVector (hn : Poly s n d) (v : ∀ i, Fin (n i) → Bool) :
    Poly s (fun i => volume (v i)) d := by
  apply of_le (fun i => volume_bool_vector_le (v i))
  (have polyH0 := Poly.const (s) (4); have polyH1 := Poly.mul polyH0 (hn); have polyH2 := Poly.const (s) (1); have polyH3 := Poly.add polyH1 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | omega))

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
-- module StateCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u7} {α : I → Type u8} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
namespace Costs
theorem matrixGet : Poly (fun x : Σ n, Matrix n × (Fin n × Fin n) => x.1)
    (fun x => Uniform.matrixGet.time x.1 x.2) 3 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1); have polyH1 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.1); have polyH2 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2.1); have polyH3 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2.2); have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2) polyH2 polyH3; have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2) polyH1 polyH4; have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (2); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7; have polyH9 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7; have polyH10 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2.1); have polyH11 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2.2); have polyH12 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2) polyH10 polyH11; have polyH13 := Poly.add polyH12 polyH6; have polyH14 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH13; have polyH15 := Poly.add polyH9 polyH14; have polyH16 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (10); have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (1); have polyH18 := Poly.add polyH12 polyH17; have polyH19 := Poly.mul polyH16 polyH18; have polyH20 := Poly.add polyH15 polyH19; have polyH21 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH20; have polyH22 := Poly.add polyH8 polyH21; have polyH23 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (20); have polyH24 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).1); have polyH25 := Poly.add polyH5 polyH24; have polyH26 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).1); have polyH27 := Poly.add polyH25 polyH26; have polyH28 := Poly.add polyH27 polyH17; have polyH29 := Poly.mul polyH23 polyH28; have polyH30 := Poly.add polyH22 polyH29; have polyH31 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) (Fin) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH30; have polyH32 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (1000000000); have polyH33 := Poly.add polyH0 polyH17; have polyH34 := Poly.mul polyH32 polyH33; have polyH35 := Poly.add polyH24 polyH0; have polyH36 := Poly.add polyH35 polyH17; have polyH37 := Poly.mul polyH34 polyH36; have polyH38 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (@Uniform.time_functionGet_le (fun (i : ℕ) => Fin i → Bool) _ (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2)) (Prod.fst (Prod.snd (Sigma.snd x_2))))) polyH37; have polyH39 := Poly.add polyH31 polyH38; have polyH40 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.fst (Sigma.snd x_1), Prod.fst (Prod.snd (Sigma.snd x_1)))) polyH24 polyH26; have polyH41 := Poly.add polyH40 polyH17; have polyH42 := Poly.mul polyH16 polyH41; have polyH43 := Poly.add polyH39 polyH42; have polyH44 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i) (fun (i : ℕ) => Fin i → Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (i : ℕ) => Fin i → Bool) _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH43; have polyH45 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH13; have polyH46 := Poly.add polyH9 polyH45; have polyH47 := Poly.add polyH46 polyH19; have polyH48 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH47; have polyH49 := Poly.add polyH44 polyH48; have polyH50 := Poly.volumeBoolVector polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).1 (Prod.snd ((fun (x_2 : (Fin (Sigma.fst x_1) → Fin (Sigma.fst x_1) → Bool) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) (Sigma.snd x_1)))); have polyH51 := Poly.add polyH5 polyH50; have polyH52 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).2); have polyH53 := Poly.add polyH51 polyH52; have polyH54 := Poly.add polyH53 polyH17; have polyH55 := Poly.mul polyH23 polyH54; have polyH56 := Poly.add polyH49 polyH55; have polyH57 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Bool) (Fin) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (fun (x_3 : (Fin i → Fin i → Bool) × Fin i) => Prod.fst x_3 (Prod.snd x_3)) ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_3, Prod.fst (Prod.snd x_3))) x_1)) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i) (fun (i : ℕ) => Fin i → Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (i : ℕ) => Fin i → Bool) _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH56; have polyH58 := Poly.add polyH50 polyH0; have polyH59 := Poly.add polyH58 polyH17; have polyH60 := Poly.mul polyH34 polyH59; have polyH61 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (@Uniform.time_functionGet_le (fun (n : ℕ) => Bool) _ (Sigma.fst x_2) ((fun (x_1 : (Fin (Sigma.fst x_2) → Fin (Sigma.fst x_2) → Bool) × Fin (Sigma.fst x_2)) => Prod.fst x_1 (Prod.snd x_1)) ((fun (x_1 : (Fin (Sigma.fst x_2) → Fin (Sigma.fst x_2) → Bool) × Fin (Sigma.fst x_2) × Fin (Sigma.fst x_2)) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (Sigma.snd x_2))) (Prod.snd (Prod.snd (Sigma.snd x_2))))) polyH60; have polyH62 := Poly.add polyH57 polyH61; have polyH63 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => ((fun (x_2 : (Fin (Sigma.fst x_1) → Fin (Sigma.fst x_1) → Bool) × Fin (Sigma.fst x_1)) => Prod.fst x_2 (Prod.snd x_2)) ((fun (x_2 : (Fin (Sigma.fst x_1) → Fin (Sigma.fst x_1) → Bool) × Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (Prod.fst x_2, Prod.fst (Prod.snd x_2))) (Sigma.snd x_1)), Prod.snd (Prod.snd (Sigma.snd x_1)))) polyH50 polyH52; have polyH64 := Poly.add polyH63 polyH17; have polyH65 := Poly.mul polyH16 polyH64; have polyH66 := Poly.add polyH62 polyH65; have polyH67 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Bool) × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i) => Prod.fst x_3 (Prod.snd x_3)) ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_3, Prod.fst (Prod.snd x_3))) x_1), Prod.snd (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Bool) Fin _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (fun (x_3 : (Fin i → Fin i → Bool) × Fin i) => Prod.fst x_3 (Prod.snd x_3)) ((fun (x_3 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_3, Prod.fst (Prod.snd x_3))) x_1)) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.snd (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i) (fun (i : ℕ) => Fin i → Bool) _ _ _ (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => (Prod.fst x_1, Prod.fst (Prod.snd x_1))) (fun (n : ℕ) (x_1 : (Fin n → Fin n → Bool) × Fin n) => Prod.fst x_1 (Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i → Fin i → Bool) Fin _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : (Fin i → Fin i → Bool) × Fin i × Fin i) => Prod.fst (Prod.snd x_1)) (@Uniform.fst ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.fst ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (i : ℕ) => Fin i → Bool) _)) (@Uniform.comp ℕ (fun (i : ℕ) => (Fin i → Fin i → Bool) × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) Fin _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Fin i → Fin i → Bool) (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.snd ℕ Fin Fin _ _))) (@Uniform.functionGet (fun (n : ℕ) => Bool) _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH66; exact Poly.lift polyH67 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

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

theorem matrixGetFrame (frame : Bool) :
    Poly (fun x : Σ n, Matrix n × (Fin n × Fin n) => x.1)
      (fun x => (Uniform.matrixGetFrame frame).time x.1 x.2) 3 := by
  cases frame <;> [(have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.matrixGet) (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega)); (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1); have polyH1 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.1); have polyH2 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2.1); have polyH3 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2.2); have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2.2) polyH2 polyH3; have polyH5 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => x_1.2) polyH1 polyH4; have polyH6 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (2); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Matrix) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7; have polyH9 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Matrix) (fun (i : ℕ) => Fin i × Fin i) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH7; have polyH10 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2.1); have polyH11 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2.2); have polyH12 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).2) polyH10 polyH11; have polyH13 := Poly.add polyH12 polyH6; have polyH14 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH13; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (Fin) _ _ (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH13; have polyH16 := Poly.add polyH14 polyH15; have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (20); have polyH18 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).2); have polyH19 := Poly.add polyH12 polyH18; have polyH20 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Sigma.snd x_1)).1); have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (1); have polyH23 := Poly.add polyH21 polyH22; have polyH24 := Poly.mul polyH17 polyH23; have polyH25 := Poly.add polyH16 polyH24; have polyH26 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Fin i) (Fin) (Fin) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ Fin Fin _ _) (@Uniform.fst ℕ Fin Fin _ _) (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH25; have polyH27 := Poly.add polyH9 polyH26; have polyH28 := Poly.const (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.fst x_1) (10); have polyH29 := Poly.add polyH12 polyH22; have polyH30 := Poly.mul polyH28 polyH29; have polyH31 := Poly.add polyH27 polyH30; have polyH32 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Fin i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.swap ℕ Fin Fin _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH31; have polyH33 := Poly.add polyH8 polyH32; have polyH34 := Poly.volumeMatrix polyH0 (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Sigma.snd x_1).1); have polyH35 := Poly.add polyH5 polyH34; have polyH36 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.snd (Prod.snd (Sigma.snd x_1)), Prod.fst (Prod.snd (Sigma.snd x_1)))) polyH18 polyH20; have polyH37 := Poly.add polyH35 polyH36; have polyH38 := Poly.add polyH37 polyH22; have polyH39 := Poly.mul polyH17 polyH38; have polyH40 := Poly.add polyH33 polyH39; have polyH41 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Matrix i × Fin i × Fin i) (Matrix) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Matrix i × Fin i × Fin i) => (fun (x_3 : Fin i × Fin i) => (Prod.snd x_3, Prod.fst x_3)) (Prod.snd x_1)) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Fin i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.swap ℕ Fin Fin _ _)) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH40; have polyH42 := Poly.reparam (@Costs.matrixGet) (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => Sigma.mk (Sigma.fst x_1) (Prod.fst (Sigma.snd x_1), (fun (x_2 : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (Prod.snd x_2, Prod.fst x_2)) (Prod.snd (Sigma.snd x_1)))) polyH0; have polyH43 := Poly.add polyH41 polyH42; have polyH44 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Matrix n × Fin n × Fin n) => (Prod.fst (Sigma.snd x_1), (fun (x_2 : Fin (Sigma.fst x_1) × Fin (Sigma.fst x_1)) => (Prod.snd x_2, Prod.fst x_2)) (Prod.snd (Sigma.snd x_1)))) polyH34 polyH36; have polyH45 := Poly.add polyH44 polyH22; have polyH46 := Poly.mul polyH28 polyH45; have polyH47 := Poly.add polyH43 polyH46; have polyH48 := Poly.of_le (fun (x_2 : (n : ℕ) × Matrix n × Fin n × Fin n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Matrix i × Fin i × Fin i) (fun (i : ℕ) => Matrix i × Fin i × Fin i) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Matrix i × Fin i × Fin i) => (Prod.fst x_1, (fun (x_3 : Fin i × Fin i) => (Prod.snd x_3, Prod.fst x_3)) (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Matrix n × Fin n × Fin n) => Prod.fst x_1 (Prod.fst (Prod.snd x_1)) (Prod.snd (Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => Matrix i × Fin i × Fin i) Matrix (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (i : ℕ) (x_1 : Matrix i × Fin i × Fin i) => (fun (x_3 : Fin i × Fin i) => (Prod.snd x_3, Prod.fst x_3)) (Prod.snd x_1)) (@Uniform.fst ℕ Matrix (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.comp ℕ (fun (i : ℕ) => Matrix i × Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) (fun (i : ℕ) => Fin i × Fin i) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) (x_1 : Fin i × Fin i) => (Prod.snd x_1, Prod.fst x_1)) (@Uniform.snd ℕ Matrix (fun (i : ℕ) => Fin i × Fin i) _ _) (@Uniform.swap ℕ Fin Fin _ _))) (Uniform.matrixGet) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH47; exact Poly.lift polyH48 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))]

end ThreeMachine.StackCompiler.Costs
end

end OAI
end

theorem solution : type_of% @OAI.ThreeMachine.StackCompiler.Costs.matrixGetFrame := @OAI.ThreeMachine.StackCompiler.Costs.matrixGetFrame
