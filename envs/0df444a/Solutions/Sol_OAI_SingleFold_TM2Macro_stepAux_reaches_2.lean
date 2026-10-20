-- Prove2me | solution 2 for OAI.SingleFold.TM2Macro.stepAux_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:32:38.209215+00:00
-- url     : https://prove2.me/submissions/e733291c-4dce-412a-ace9-b74c3a83e4fc

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/TuringSimulation.lean:L96-L146
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.TM2Macro.stepAux_reaches. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
import Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_TuringSimulation

-- ---- from OAI.NumberTheory.SingleFold.TuringSimulation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace SingleFold.TM2Macro

section
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
lemma pack_div (l : List Symbol) : pack l/5=pack l.tail := by
  cases l with
  | nil => rfl
  | cons s l => simp [Nat.mul_add_div, Nat.div_eq_of_lt (digit s).isLt]
lemma pack_mod (l : List Symbol) : mod5 false (pack l)=l.head?.elim 0 digit := by
  cases l with
  | nil => rfl
  | cons s l => apply Fin.ext; simp [mod5,Macro.radix, Nat.mod_eq_of_lt (digit s).isLt]
lemma pack_symbol (l : List Symbol) : symbol (mod5 false (pack l))=l.head? := by
  rw [pack_mod]; cases l <;> simp
lemma pack_restore (l : List Symbol) :
    (if (mod5 false (pack l)).val=0 then pack l/5 else 5*(pack l/5)+(mod5 false (pack l)).val)=pack l := by
  cases l with
  | nil => rfl
  | cons s l => cases s <;> simp [pack,mod5,Macro.radix,digit,Nat.mul_add_div]

variable {n : ℕ} {Λ : Type}
lemma values_update (S : Stack → List Symbol) (x : Fin n → ℕ) (k : Stack) (l : List Symbol) :
    values (Function.update S k l) x=Function.update (values S x) (.inl k) (pack l) := by
  funext i
  rcases i with j|j
  · by_cases h : j=k <;> simp [values,Function.update_apply,h]
  · simp [values,Function.update_apply]

lemma stepAux_reaches (M : Λ → Stmt Λ) (initial : Λ) (q : Stmt Λ) (v : Store)
    (S : Stack → List Symbol) (x : Fin n → ℕ) :
    Reaches₁ (Macro.step (program M initial)) (codeCfg q v S x) (encode M (TM2.stepAux q v S) x) := by
  induction q generalizing v S with
  | halt => exact TransGen.single rfl
  | goto f => exact TransGen.single rfl
  | load f q ih => exact (ih (f v) S).head (r:=fun c d=>d∈Macro.step (program M initial) c) rfl
  | branch f q r ihq ihr =>
    cases h : f v
    · simpa only [Reaches₁,TM2.stepAux,h,Bool.false_eq_true,ite_false,Bool.cond_false] using
        (ihr v S).head (r:=fun c d=>d∈Macro.step (program M initial) c) (show Macro.step (program M initial) (codeCfg (.branch f q r) v S x)=some (codeCfg r v S x) by simp [Macro.step,Macro.next,program,codeCfg,h])
    · simpa only [Reaches₁,TM2.stepAux,h,ite_true,Bool.cond_true] using
        (ihq v S).head (r:=fun c d=>d∈Macro.step (program M initial) c) (show Macro.step (program M initial) (codeCfg (.branch f q r) v S x)=some (codeCfg q v S x) by simp [Macro.step,Macro.next,program,codeCfg,h])
  | push k f q ih =>
    apply (ih v (Function.update S k (f v::S k))).head (r:=fun c d=>d∈Macro.step (program M initial) c)
    change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.code q v)) (Function.update (values S x) (.inl k) (5*pack (S k)+(digit (f v)).val))) = some _
    rw [codeCfg,values_update,pack_cons]
  | pop k f q ih =>
    apply (ih (f v (S k).head?) (Function.update S k (S k).tail)).head (r:=fun c d=>d∈Macro.step (program M initial) c)
    change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.code q (f v (symbol (mod5 false (pack (S k))))))) (Function.update (values S x) (.inl k) (pack (S k)/5))) = some _
    rw [pack_symbol,pack_div,codeCfg,values_update]
  | peek k f q ih =>
    let d := mod5 false (pack (S k))
    let w := f v (S k).head?
    let V := Function.update (values S x) (.inl k) (pack (S k)/5)
    have h1 : Macro.step (program M initial) (codeCfg (.peek k f q) v S x)=
        some ⟨some (.restore k d q w),V⟩ := by
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.restore k d q (f v (symbol (mod5 false (pack (S k))))))) V)=some _
      rw [pack_symbol]
    have h2 : Macro.step (program M initial) ⟨some (.restore k d q w),V⟩=some (codeCfg q w S x) := by
      have hp : (if d.val=0 then pack (S k)/5 else 5*(pack (S k)/5)+d.val)=pack (S k) := pack_restore (S k)
      by_cases hd : d.val=0
      · rw [ite_eq_left hd] at hp
        have hv : V=values S x := by
          dsimp [V]; rw [hp]
          exact Function.update_eq_self _ _
        change some (Macro.next (program M initial) (.restore k d q w) V)=some _
        simp only [Macro.next,program,hd,ite_eq_left]
        rw [hv]; rfl
      · rw [ite_eq_right hd] at hp
        change some (Macro.next (program M initial) (.restore k d q w) V)=some _
        simp only [Macro.next,program,hd,ite_false]
        have hV : V (.inl k)=pack (S k)/5 := Function.update_self _ _ _
        rw [hV]
        dsimp only [V]
        rw [Function.update_idem,hp]
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.code q w)) (Function.update (values S x) (.inl k) (values S x (.inl k))))=some _
        rw [Function.update_eq_self]; rfl

    exact ((ih w S).head (r:=fun c d=>d∈Macro.step (program M initial) c) h2).head
      (r:=fun c d=>d∈Macro.step (program M initial) c) h1

end

section
open Turing Turing.PartrecToTM2 StateTransition Relation
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
variable {n : ℕ} {Λ : Type}
variable (M : Λ → Stmt Λ) (initial : Λ)
local notation "F" => Macro.step (program M initial)
end

open Turing Turing.PartrecToTM2 StateTransition Relation
variable {n : ℕ} {Λ : Type}
variable (M : Λ → Stmt Λ) (initial : Λ)
local notation "F" => Macro.step (program M initial)
end SingleFold.TM2Macro

namespace SingleFold.Macro
open StateTransition Relation
open scoped Classical
variable {Q Q' J : Type} [DecidableEq J]
end SingleFold.Macro

end

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.TM2Macro
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)


theorem solution : type_of% @_root_.OAI.SingleFold.TM2Macro.stepAux_reaches := @_root_.OAI.SingleFold.TM2Macro.stepAux_reaches
