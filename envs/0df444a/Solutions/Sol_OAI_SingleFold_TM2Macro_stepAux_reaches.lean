-- Prove2me | solution 1 for OAI.SingleFold.TM2Macro.stepAux_reaches
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:37:37.335051+00:00
-- url     : https://prove2.me/submissions/ee02231c-1e96-4951-bb0e-c477a800cc73

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

open OAI OAI.SingleFold OAI.SingleFold.TM2Macro
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
variable {n : ℕ} {Λ : Type}


theorem solution (M : Λ → Stmt Λ) (initial : Λ) (q : Stmt Λ) (v : Store)
    (S : Stack → List Symbol) (x : Fin n → ℕ) :
    Reaches₁ (Macro.step (program M initial)) (codeCfg q v S x) (encode M (TM2.stepAux q v S) x) := by
  classical
  have hvals : ∀ (S : Stack → List Symbol) (k : Stack) (l : List Symbol),
      values (Function.update S k l) x = Function.update (values S x) (.inl k) (pack l) := by
    intro S k l; funext r
    rcases r with r | r
    · by_cases h : r = k
      · subst h; simp
      · simp [Function.update_of_ne h, Function.update_of_ne (show (Sum.inl r : Reg n) ≠ .inl k by simpa using h)]
    · simp [Function.update_of_ne (show (Sum.inr r : Reg n) ≠ .inl k by simp)]
  have hst : ∀ (l : Label n Λ) (val : Reg n → ℕ),
      Macro.step (program M initial) ⟨some l, val⟩ = some (Macro.next (program M initial) l val) := fun _ _ => rfl
  induction q generalizing v S with
  | push k f q ih =>
    apply TransGen.head _ (ih v _)
    show _ ∈ Macro.step (program M initial) ⟨some (.code (.push k f q) v), values S x⟩
    rw [hst]
    simp only [Macro.next, program, codeCfg, hvals, pack_cons, values_inl]
    rfl
  | peek k f q ih =>
    have hmod : ∀ l : List Symbol, pack l % 5 = (match l with | [] => 0 | s :: _ => (digit s).val) := by
      intro l; cases l with
      | nil => rfl
      | cons s t => simp only [pack_cons]; have := (digit s).isLt; omega
    cases hS : S k with
    | nil =>
      have e : TM2.stepAux (.peek k f q) v S = TM2.stepAux q (f v none) S := by simp [TM2.stepAux, hS]
      rw [e]
      apply TransGen.head (b := ⟨some (.restore k 0 q (f v none)), values S x⟩)
      · show _ ∈ Macro.step (program M initial) ⟨some (.code (.peek k f q) v), values S x⟩
        rw [hst]
        simp only [Macro.next, program, values_inl, hS, pack_nil, Macro.radix]
        have hv : Function.update (values S x) (Sum.inl k) 0 = values S x :=
          Function.update_eq_self_iff.mpr (by simp [hS])
        simp only [Bool.false_eq_true, if_false, Nat.zero_mod, Nat.zero_div, Fin.mk_zero, symbol_zero, hv]
        rfl
      apply TransGen.head _ (ih (f v none) S)
      show _ ∈ Macro.step (program M initial) ⟨some (.restore k 0 q (f v none)), values S x⟩
      rw [hst]; rfl
    | cons s t =>
      have e : TM2.stepAux (.peek k f q) v S = TM2.stepAux q (f v (some s)) S := by simp [TM2.stepAux, hS]
      rw [e]
      have key : ∀ (h : (5 * pack t + (digit s).val) % 5 < 5),
          (⟨(5 * pack t + (digit s).val) % 5, h⟩ : Fin 5) = digit s := fun h => Fin.ext (by
            simp only; have := (digit s).isLt; omega)
      have hdiv : (5 * pack t + (digit s).val) / 5 = pack t := by have := (digit s).isLt; omega
      have hne : (digit s).val ≠ 0 := by cases s <;> decide
      apply TransGen.head (b := ⟨some (.restore k (digit s) q (f v (some s))),
        Function.update (values S x) (Sum.inl k) (pack t)⟩)
      · show _ ∈ Macro.step (program M initial) ⟨some (.code (.peek k f q) v), values S x⟩
        rw [hst]
        simp only [Macro.next, program, values_inl, hS, pack_cons, Macro.radix, Bool.false_eq_true,
          if_false, key, hdiv, symbol_digit]
        rfl
      apply TransGen.head (b := codeCfg q (f v (some s)) S x)
      · show _ ∈ Macro.step (program M initial) ⟨some (.restore k (digit s) q (f v (some s))), _⟩
        rw [hst]
        simp only [Macro.next, program, hne, if_false, Function.update_idem, codeCfg]
        have hv : Function.update (values S x) (Sum.inl k) (5 * pack t + (digit s).val) = values S x :=
          Function.update_eq_self_iff.mpr (by simp [hS])
        simp only [Function.update_self]
        rw [hv]; rfl
      exact ih _ S
  | pop k f q ih =>
    have hS' : values (Function.update S k (S k).tail) x =
        Function.update (values S x) (Sum.inl k) (pack (S k) / 5) := by
      rw [hvals]; congr 1
      cases S k with
      | nil => rfl
      | cons s t => simp only [List.tail_cons, pack_cons]; have := (digit s).isLt; omega
    apply TransGen.head (b := codeCfg q (f v (S k).head?) (Function.update S k (S k).tail) x)
    · show _ ∈ Macro.step (program M initial) ⟨some (.code (.pop k f q) v), values S x⟩
      rw [hst]
      simp only [Macro.next, program, values_inl, Macro.radix, Bool.false_eq_true, if_false, codeCfg, hS']
      have hsym : ∀ (l : List Symbol) (h : pack l % 5 < 5), symbol ⟨pack l % 5, h⟩ = l.head? := by
        intro l h
        cases l with
        | nil => rfl
        | cons s t =>
          have key : (⟨pack (s :: t) % 5, h⟩ : Fin 5) = digit s := Fin.ext (by
              simp only [pack_cons]; have := (digit s).isLt; omega)
          rw [key, symbol_digit]; rfl
      simp only [hsym]; rfl
    exact ih _ _
  | load a q ih =>
    apply TransGen.head _ (ih _ S)
    show _ ∈ Macro.step (program M initial) ⟨some (.code (.load a q) v), values S x⟩
    rw [hst]; rfl
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hf : f v
    · have e : TM2.stepAux (.branch f q₁ q₂) v S = TM2.stepAux q₂ v S := by simp [TM2.stepAux, hf]
      rw [e]
      apply TransGen.head _ (ih₂ v S)
      show _ ∈ Macro.step (program M initial) ⟨some (.code (.branch f q₁ q₂) v), values S x⟩
      rw [hst]; simp [Macro.next, program, hf, codeCfg]
    · have e : TM2.stepAux (.branch f q₁ q₂) v S = TM2.stepAux q₁ v S := by simp [TM2.stepAux, hf]
      rw [e]
      apply TransGen.head _ (ih₁ v S)
      show _ ∈ Macro.step (program M initial) ⟨some (.code (.branch f q₁ q₂) v), values S x⟩
      rw [hst]; simp [Macro.next, program, hf, codeCfg]
  | goto f =>
    apply TransGen.single
    show _ ∈ Macro.step (program M initial) ⟨some (.code (.goto f) v), values S x⟩
    rw [hst]; rfl
  | halt =>
    apply TransGen.single
    show _ ∈ Macro.step (program M initial) ⟨some (.code .halt v), values S x⟩
    rw [hst]; rfl

